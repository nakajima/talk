use std::{
    collections::VecDeque,
    io::{self, IsTerminal, Write},
    sync::{Arc, Condvar, Mutex},
    thread,
    time::Duration,
};

use crate::compiling::progress::{self, Phase, Reporter};

const FRAME_TEXT: [&str; 8] = [
    "0x74", "0x61", "0x6C", "0x6B", "0x74", "0x61", "0x6C", "0x6B",
];
const FRAME_COLOR: [u8; 8] = [15, 249, 242, 235, 235, 242, 249, 15];
const FRAME_INTERVAL: Duration = Duration::from_millis(80);

struct State {
    phase: Option<Phase>,
    pending: VecDeque<Phase>,
    stopped: bool,
}

struct Spinner {
    state: Arc<(Mutex<State>, Condvar)>,
    worker: Option<thread::JoinHandle<()>>,
}

impl Spinner {
    fn new(enabled: bool) -> Self {
        let state = Arc::new((
            Mutex::new(State {
                phase: None,
                pending: VecDeque::new(),
                stopped: false,
            }),
            Condvar::new(),
        ));
        let worker = enabled.then(|| {
            let state = state.clone();
            let color = std::env::var_os("NO_COLOR").is_none();
            thread::spawn(move || Self::animate(state, color))
        });
        Self { state, worker }
    }

    fn reporter(&self) -> Reporter {
        let state = self.state.clone();
        Arc::new(move |phase| {
            let (lock, changed) = &*state;
            let mut current = lock
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if current.pending.back().copied().or(current.phase) != Some(phase) {
                current.pending.push_back(phase);
                changed.notify_one();
            }
        })
    }

    fn animate(state: Arc<(Mutex<State>, Condvar)>, color: bool) {
        let mut frame = 0;
        loop {
            let phase = {
                let (lock, changed) = &*state;
                let mut current = lock
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner);
                while current.phase.is_none() && current.pending.is_empty() && !current.stopped {
                    current = changed
                        .wait(current)
                        .unwrap_or_else(std::sync::PoisonError::into_inner);
                }
                if let Some(phase) = current.pending.pop_front() {
                    current.phase = Some(phase);
                    Some(phase)
                } else if current.stopped {
                    break;
                } else {
                    current.phase
                }
            };

            if let Some(phase) = phase {
                let mut stderr = io::stderr().lock();
                let _ = Self::render_frame(&mut stderr, frame, phase, color);
                let _ = stderr.flush();
                frame = (frame + 1) % FRAME_TEXT.len();
            }

            let (lock, changed) = &*state;
            let current = lock
                .lock()
                .unwrap_or_else(std::sync::PoisonError::into_inner);
            if current.stopped || !current.pending.is_empty() {
                continue;
            }
            let _ = changed
                .wait_timeout(current, FRAME_INTERVAL)
                .unwrap_or_else(std::sync::PoisonError::into_inner);
        }
    }

    fn render_frame(
        output: &mut impl Write,
        frame: usize,
        phase: Phase,
        color: bool,
    ) -> io::Result<()> {
        write!(output, "\r\x1b[2K ")?;
        if color {
            write!(
                output,
                "\x1b[38;5;{}m{} \x1b[39m",
                FRAME_COLOR[frame], FRAME_TEXT[frame]
            )?;
        } else {
            write!(output, "{} ", FRAME_TEXT[frame])?;
        }
        write!(output, "{}", phase.label())
    }
}

impl Drop for Spinner {
    fn drop(&mut self) {
        let (lock, changed) = &*self.state;
        lock.lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .stopped = true;
        changed.notify_one();
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
            let mut stderr = io::stderr().lock();
            let _ = write!(stderr, "\r\x1b[2K");
            let _ = stderr.flush();
        }
    }
}

pub fn with_spinner<R>(enabled: bool, operation: impl FnOnce() -> R) -> R {
    let spinner = Spinner::new(enabled && io::stderr().is_terminal());
    progress::with_reporter(spinner.reporter(), operation)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colored_frames_match_the_talktalk_sequence() {
        let expected = [
            "\r\x1b[2K \x1b[38;5;15m0x74 \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;249m0x61 \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;242m0x6C \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;235m0x6B \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;235m0x74 \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;242m0x61 \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;249m0x6C \x1b[39mParsing",
            "\r\x1b[2K \x1b[38;5;15m0x6B \x1b[39mParsing",
        ];
        for (frame, expected) in expected.iter().enumerate() {
            let mut rendered = Vec::new();
            Spinner::render_frame(&mut rendered, frame, Phase::Parsing, true)
                .expect("render frame");
            assert_eq!(String::from_utf8(rendered).expect("ASCII frame"), *expected);
        }
    }

    #[test]
    fn no_color_keeps_the_ascii_animation() {
        let mut rendered = Vec::new();
        Spinner::render_frame(&mut rendered, 0, Phase::TypeChecking, false).expect("render frame");
        assert_eq!(
            String::from_utf8(rendered).expect("ASCII frame"),
            "\r\x1b[2K 0x74 Type checking"
        );
    }
}
