use std::collections::VecDeque;

use rustc_hash::FxHashMap;

use super::{
    interpreter::Interpreter,
    io::IO,
    value::{RecordId, Value},
};
use crate::name_resolution::symbol::Symbol;

/// Unique identifier for a task in the executor
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TaskId(pub u64);

/// State of a task in the executor
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    /// Task is waiting to be polled
    Pending,
    /// Task is ready to be polled (in run queue)
    Runnable,
    /// Task has completed
    Complete,
}

/// A task represents a suspendable computation
#[derive(Debug)]
pub struct Task {
    pub id: TaskId,
    /// The poll function symbol for this state machine
    pub poll_func: Symbol,
    /// Current state index
    pub state: i64,
    /// State data record containing live variables
    pub state_data: Value,
    /// Current status
    pub status: TaskState,
    /// Result when complete
    pub result: Option<Value>,
}

impl Task {
    pub fn new(id: TaskId, poll_func: Symbol) -> Self {
        Self {
            id,
            poll_func,
            state: 0,
            state_data: Value::Record(RecordId::Anon, vec![]),
            status: TaskState::Runnable,
            result: None,
        }
    }
}

/// Waker allows a task to signal that it's ready to make progress
#[derive(Debug, Clone)]
pub struct Waker {
    pub task_id: TaskId,
}

impl Waker {
    pub fn new(task_id: TaskId) -> Self {
        Self { task_id }
    }

    /// Create a Value representation of this waker for passing to Talk code
    pub fn to_value(&self) -> Value {
        Value::Record(
            RecordId::Anon, // Will be Waker struct
            vec![Value::Int(self.task_id.0 as i64)],
        )
    }
}

/// Context passed to poll functions, containing the waker
#[derive(Debug, Clone)]
pub struct Context {
    pub waker: Waker,
}

impl Context {
    pub fn new(waker: Waker) -> Self {
        Self { waker }
    }

    /// Create a Value representation of this context for passing to Talk code
    pub fn to_value(&self) -> Value {
        Value::Record(
            RecordId::Anon, // Will be Context struct
            vec![self.waker.to_value()],
        )
    }
}

/// Result of polling a task
#[derive(Debug)]
pub enum PollResult {
    /// Task completed with a value
    Ready(Value),
    /// Task yielded, waiting for something
    Pending {
        /// New state index
        next_state: i64,
        /// Updated state data
        state_data: Value,
        /// Value that was yielded
        yielded: Value,
    },
}

/// Trait for executors that can run async tasks
pub trait Executor {
    /// Spawn a new task from a poll function
    fn spawn(&mut self, poll_func: Symbol) -> TaskId;

    /// Wake a task, marking it as ready to poll
    fn wake(&mut self, task_id: TaskId);

    /// Run all tasks to completion
    fn run<I: IO>(&mut self, interpreter: &mut Interpreter<I>) -> Value;
}

/// Runtime executor implementation with task queue
#[derive(Debug)]
pub struct RuntimeExecutor {
    /// All tasks
    tasks: FxHashMap<TaskId, Task>,
    /// Queue of tasks ready to be polled
    run_queue: VecDeque<TaskId>,
    /// Next task ID to assign
    next_task_id: u64,
    /// Root task (first spawned)
    root_task: Option<TaskId>,
    /// Map of file descriptors to waiting tasks
    io_interests: FxHashMap<i32, TaskId>,
}

impl Default for RuntimeExecutor {
    fn default() -> Self {
        Self::new()
    }
}

impl RuntimeExecutor {
    pub fn new() -> Self {
        Self {
            tasks: FxHashMap::default(),
            run_queue: VecDeque::new(),
            next_task_id: 0,
            root_task: None,
            io_interests: FxHashMap::default(),
        }
    }

    /// Register interest in a file descriptor for a task
    pub fn register_io(&mut self, fd: i32, task_id: TaskId) {
        self.io_interests.insert(fd, task_id);
    }

    /// Unregister interest in a file descriptor
    pub fn unregister_io(&mut self, fd: i32) {
        self.io_interests.remove(&fd);
    }

    /// Poll for IO events and wake waiting tasks
    pub fn poll_io<I: IO>(&mut self, io: &mut I, timeout_ms: i64) {
        if self.io_interests.is_empty() {
            return;
        }

        // Build pollfd array
        let mut poll_fds: Vec<(i32, i16, i16)> = self
            .io_interests
            .keys()
            .map(|&fd| (fd, libc::POLLIN as i16 | libc::POLLOUT as i16, 0))
            .collect();

        let result = io.io_poll(&mut poll_fds, timeout_ms);

        if result > 0 {
            // Wake tasks whose fds are ready
            for (fd, _, revents) in poll_fds {
                if revents != 0 {
                    if let Some(&task_id) = self.io_interests.get(&fd) {
                        self.wake(task_id);
                    }
                }
            }
        }
    }

    /// Check if all tasks are complete
    pub fn all_complete(&self) -> bool {
        self.tasks.values().all(|t| t.status == TaskState::Complete)
    }

    /// Get the result of the root task
    pub fn root_result(&self) -> Option<Value> {
        self.root_task
            .and_then(|id| self.tasks.get(&id))
            .and_then(|t| t.result.clone())
    }

    /// Parse a poll result value into a PollResult
    fn parse_poll_result(&self, result: Value) -> Option<PollResult> {
        // The poll function returns: (next_state: Int, state_data: Record, poll: Poll<T, Y>)
        let Value::Record(_, fields) = result else {
            return None;
        };

        if fields.len() < 3 {
            return None;
        }

        let Value::Int(next_state) = &fields[0] else {
            return None;
        };
        let state_data = fields[1].clone();
        let poll = &fields[2];

        // Poll<T, Y> is an enum: case ready(T), case pending(Y)
        // Represented as Record with tag as first field
        let Value::Record(_, poll_fields) = poll else {
            // If it's not a record, treat as ready (but warn - this may hide bugs)
            tracing::warn!(
                "parse_poll_result: expected Poll record, got {:?}; treating as Ready",
                poll
            );
            return Some(PollResult::Ready(poll.clone()));
        };

        if poll_fields.is_empty() {
            return Some(PollResult::Ready(Value::Void));
        }

        let Value::Int(tag) = &poll_fields[0] else {
            tracing::warn!(
                "parse_poll_result: Poll record first field should be Int tag, got {:?}; treating as Ready",
                poll_fields[0]
            );
            return Some(PollResult::Ready(poll.clone()));
        };

        match *tag {
            0 => {
                // ready(T) - tag 0
                let value = if poll_fields.len() > 1 {
                    poll_fields[1].clone()
                } else {
                    Value::Void
                };
                Some(PollResult::Ready(value))
            }
            1 => {
                // pending(Y) - tag 1
                let yielded = if poll_fields.len() > 1 {
                    poll_fields[1].clone()
                } else {
                    Value::Void
                };
                Some(PollResult::Pending {
                    next_state: *next_state,
                    state_data,
                    yielded,
                })
            }
            _ => Some(PollResult::Ready(poll.clone())),
        }
    }
}

impl Executor for RuntimeExecutor {
    fn spawn(&mut self, poll_func: Symbol) -> TaskId {
        let id = TaskId(self.next_task_id);
        self.next_task_id += 1;

        let task = Task::new(id, poll_func);
        self.tasks.insert(id, task);
        self.run_queue.push_back(id);

        if self.root_task.is_none() {
            self.root_task = Some(id);
        }

        id
    }

    fn wake(&mut self, task_id: TaskId) {
        if let Some(task) = self.tasks.get_mut(&task_id) {
            if task.status == TaskState::Pending {
                task.status = TaskState::Runnable;
                self.run_queue.push_back(task_id);
            }
        }
    }

    fn run<I: IO>(&mut self, interpreter: &mut Interpreter<I>) -> Value {
        use super::register::Register;

        loop {
            // Poll all runnable tasks
            while let Some(task_id) = self.run_queue.pop_front() {
                let Some(task) = self.tasks.get(&task_id) else {
                    continue;
                };

                // Skip if already complete
                if task.status == TaskState::Complete {
                    continue;
                }

                let poll_func = task.poll_func;
                let state = task.state;
                let state_data = task.state_data.clone();

                // Create context with waker
                let waker = Waker::new(task_id);
                let cx = Context::new(waker);

                // Build poll arguments: (state: Int, state_data: Record, resumed: R, cx: Context)
                // For now, resumed is Void
                let poll_args = vec![
                    Value::Int(state),
                    state_data,
                    Value::Void, // resumed value
                    cx.to_value(),
                ];

                // Call the poll function
                interpreter.call(poll_func, poll_args, Register::MAIN, None);

                // Run until the call returns
                while !interpreter.frames.is_empty() {
                    interpreter.next();
                }

                // Get the result
                let result = interpreter.main_result.take().unwrap_or(Value::Void);

                // Parse the poll result
                if let Some(poll_result) = self.parse_poll_result(result) {
                    match poll_result {
                        PollResult::Ready(value) => {
                            // For non-root tasks, we can remove them immediately to free memory.
                            // For the root task, we keep it to return the result at the end.
                            if Some(task_id) == self.root_task {
                                if let Some(task) = self.tasks.get_mut(&task_id) {
                                    task.status = TaskState::Complete;
                                    task.result = Some(value);
                                }
                            } else {
                                // Remove completed non-root task to prevent memory leak
                                self.tasks.remove(&task_id);
                            }
                        }
                        PollResult::Pending {
                            next_state,
                            state_data,
                            yielded: _,
                        } => {
                            if let Some(task) = self.tasks.get_mut(&task_id) {
                                task.state = next_state;
                                task.state_data = state_data;
                                task.status = TaskState::Pending;
                            }
                        }
                    }
                }
            }

            // Check if all tasks are done
            if self.all_complete() {
                return self.root_result().unwrap_or(Value::Void);
            }

            // If run queue is empty but tasks remain, wait for IO
            if self.run_queue.is_empty() && !self.io_interests.is_empty() {
                self.poll_io(&mut interpreter.io, 100); // 100ms timeout
            } else if self.run_queue.is_empty() {
                // No runnable tasks and no IO interests - deadlock
                // In a real system we'd want better handling here
                break;
            }
        }

        self.root_result().unwrap_or(Value::Void)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_waker_to_value() {
        let waker = Waker::new(TaskId(42));
        let value = waker.to_value();

        match value {
            Value::Record(_, fields) => {
                assert_eq!(fields.len(), 1);
                assert_eq!(fields[0], Value::Int(42));
            }
            _ => panic!("Expected record value"),
        }
    }

    #[test]
    fn test_context_to_value() {
        let waker = Waker::new(TaskId(123));
        let cx = Context::new(waker);
        let value = cx.to_value();

        match value {
            Value::Record(_, fields) => {
                assert_eq!(fields.len(), 1);
                match &fields[0] {
                    Value::Record(_, waker_fields) => {
                        assert_eq!(waker_fields[0], Value::Int(123));
                    }
                    _ => panic!("Expected waker record"),
                }
            }
            _ => panic!("Expected context record"),
        }
    }

    #[test]
    fn test_executor_spawn() {
        let mut executor = RuntimeExecutor::new();
        let id = executor.spawn(Symbol::Main);

        assert_eq!(id, TaskId(0));
        assert!(executor.tasks.contains_key(&id));
        assert_eq!(executor.root_task, Some(id));
    }

    #[test]
    fn test_executor_wake() {
        let mut executor = RuntimeExecutor::new();
        let id = executor.spawn(Symbol::Main);

        // Mark as pending
        executor.tasks.get_mut(&id).unwrap().status = TaskState::Pending;
        executor.run_queue.clear();

        // Wake it
        executor.wake(id);

        assert_eq!(executor.tasks[&id].status, TaskState::Runnable);
        assert!(executor.run_queue.contains(&id));
    }

    #[test]
    fn test_parse_poll_result_ready() {
        let executor = RuntimeExecutor::new();

        // Poll::ready(42) - tag 0, value 42
        let result = Value::Record(
            RecordId::Anon,
            vec![
                Value::Int(1),                         // next_state
                Value::Record(RecordId::Anon, vec![]), // state_data
                Value::Record(
                    RecordId::Anon,
                    vec![Value::Int(0), Value::Int(42)], // Poll::ready(42)
                ),
            ],
        );

        match executor.parse_poll_result(result) {
            Some(PollResult::Ready(Value::Int(42))) => {}
            other => panic!("Expected Ready(42), got {:?}", other),
        }
    }

    #[test]
    fn test_parse_poll_result_pending() {
        let executor = RuntimeExecutor::new();

        // Poll::pending(()) - tag 1
        let result = Value::Record(
            RecordId::Anon,
            vec![
                Value::Int(2),                                        // next_state
                Value::Record(RecordId::Anon, vec![Value::Int(100)]), // state_data with saved var
                Value::Record(
                    RecordId::Anon,
                    vec![Value::Int(1), Value::Void], // Poll::pending(())
                ),
            ],
        );

        match executor.parse_poll_result(result) {
            Some(PollResult::Pending {
                next_state,
                state_data,
                ..
            }) => {
                assert_eq!(next_state, 2);
                match state_data {
                    Value::Record(_, fields) => {
                        assert_eq!(fields[0], Value::Int(100));
                    }
                    _ => panic!("Expected state data record"),
                }
            }
            other => panic!("Expected Pending, got {:?}", other),
        }
    }
}
