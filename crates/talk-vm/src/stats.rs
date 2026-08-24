use crate::{Insn, Module};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::time::{Duration, Instant};

/// Aggregate statistics for one bytecode module across one or more VM runs.
///
/// Static instruction counts come from the module. Dynamic counts are exact,
/// but elapsed time includes the cost of collecting those counts. A collector
/// binds to the first module layout it observes and rejects incompatible
/// layouts so `(chunk, pc)` identities remain meaningful.
#[derive(Debug, Default)]
pub struct VmStats {
    runs: u64,
    elapsed: Duration,
    chunks: Vec<VmChunkStats>,
    bound: bool,
    started_at: Option<Instant>,
}

/// Statistics for one bytecode chunk.
#[derive(Debug)]
pub struct VmChunkStats {
    name: String,
    opcodes: Vec<&'static str>,
    executions: Vec<u64>,
}

/// Aggregated static and dynamic counts for one opcode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VmOpcodeStats {
    pub opcode: &'static str,
    pub emitted: u64,
    pub executed: u64,
}

/// Dynamic count for one emitted instruction site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct VmInstructionStats<'a> {
    pub chunk_index: usize,
    pub chunk_name: &'a str,
    pub pc: usize,
    pub opcode: &'static str,
    pub executions: u64,
}

impl VmStats {
    /// Create a collector bound to `module`, making static counts available
    /// before the first run. [`VmStats::default`] instead binds on first use.
    pub fn for_module(module: &Module) -> Self {
        let mut stats = Self::default();
        stats.bind(module);
        stats
    }

    pub fn runs(&self) -> u64 {
        self.runs
    }

    pub fn elapsed(&self) -> Duration {
        self.elapsed
    }

    pub fn emitted_instructions(&self) -> u64 {
        self.chunks
            .iter()
            .map(|chunk| chunk.opcodes.len() as u64)
            .sum()
    }

    pub fn executed_instructions(&self) -> u64 {
        self.chunks.iter().map(VmChunkStats::executed).sum()
    }

    pub fn chunks(&self) -> &[VmChunkStats] {
        &self.chunks
    }

    /// Aggregate counts by opcode, ordered by opcode name.
    pub fn opcode_stats(&self) -> Vec<VmOpcodeStats> {
        let mut counts: BTreeMap<&'static str, (u64, u64)> = BTreeMap::new();
        for chunk in &self.chunks {
            for (&opcode, &executions) in chunk.opcodes.iter().zip(&chunk.executions) {
                let entry = counts.entry(opcode).or_default();
                entry.0 += 1;
                entry.1 += executions;
            }
        }
        counts
            .into_iter()
            .map(|(opcode, (emitted, executed))| VmOpcodeStats {
                opcode,
                emitted,
                executed,
            })
            .collect()
    }

    /// Return every emitted instruction site in module order.
    pub fn instruction_stats(&self) -> Vec<VmInstructionStats<'_>> {
        self.chunks
            .iter()
            .enumerate()
            .flat_map(|(chunk_index, chunk)| {
                chunk
                    .opcodes
                    .iter()
                    .copied()
                    .zip(chunk.executions.iter().copied())
                    .enumerate()
                    .map(move |(pc, (opcode, executions))| VmInstructionStats {
                        chunk_index,
                        chunk_name: &chunk.name,
                        pc,
                        opcode,
                        executions,
                    })
            })
            .collect()
    }

    /// Render totals, opcode counts, chunk counts, and the twenty hottest
    /// emitted instruction sites. Dynamic rows are ordered by executions.
    pub fn render(&self) -> String {
        let emitted = self.emitted_instructions();
        let executed = self.executed_instructions();
        let seconds = self.elapsed.as_secs_f64();
        let throughput = if seconds > 0.0 {
            executed as f64 / seconds
        } else {
            0.0
        };
        let average_ns = if executed > 0 {
            self.elapsed.as_nanos() as f64 / executed as f64
        } else {
            0.0
        };

        let mut out = String::new();
        let _ = writeln!(out, "VM instruction statistics");
        let _ = writeln!(out, "runs: {}", self.runs);
        let _ = writeln!(out, "elapsed: {:.6} s", seconds);
        let _ = writeln!(out, "emitted: {emitted}");
        let _ = writeln!(out, "executed: {executed}");
        let _ = writeln!(
            out,
            "throughput: {:.3} M instructions/s",
            throughput / 1_000_000.0
        );
        let _ = writeln!(
            out,
            "average: {average_ns:.2} ns/instruction (instrumented)"
        );

        let mut opcodes = self.opcode_stats();
        opcodes.sort_by_key(|stats| std::cmp::Reverse((stats.executed, stats.emitted)));
        let _ = writeln!(out, "\nopcodes:");
        let _ = writeln!(
            out,
            "  {:<22} {:>10} {:>14}",
            "opcode", "emitted", "executed"
        );
        for stats in opcodes {
            let _ = writeln!(
                out,
                "  {:<22} {:>10} {:>14}",
                stats.opcode, stats.emitted, stats.executed
            );
        }

        let mut chunks: Vec<(usize, &VmChunkStats)> = self.chunks.iter().enumerate().collect();
        chunks.sort_by_key(|(_, chunk)| std::cmp::Reverse(chunk.executed()));
        let _ = writeln!(out, "\nchunks:");
        let _ = writeln!(
            out,
            "  {:>6} {:<36} {:>10} {:>14}",
            "index", "name", "emitted", "executed"
        );
        for (index, chunk) in chunks {
            let _ = writeln!(
                out,
                "  {:>6} {:<36} {:>10} {:>14}",
                index,
                chunk.name,
                chunk.emitted(),
                chunk.executed()
            );
        }

        let mut instructions = self.instruction_stats();
        instructions.sort_by_key(|stats| std::cmp::Reverse(stats.executions));
        let _ = writeln!(out, "\nhottest instruction sites:");
        let _ = writeln!(
            out,
            "  {:>6} {:>6} {:<22} {:>14}  chunk",
            "chunk", "pc", "opcode", "executed"
        );
        for stats in instructions.into_iter().take(20) {
            let _ = writeln!(
                out,
                "  {:>6} {:>6} {:<22} {:>14}  {}",
                stats.chunk_index, stats.pc, stats.opcode, stats.executions, stats.chunk_name
            );
        }
        out
    }

    pub(crate) fn begin_run(&mut self, module: &Module) -> Result<(), String> {
        if self.started_at.is_some() {
            return Err("vm: statistics collector is already recording a run".into());
        }
        if !self.bound {
            self.bind(module);
        } else if !self.matches(module) {
            return Err("vm: statistics collector belongs to an incompatible module".into());
        }
        self.started_at = Some(Instant::now());
        Ok(())
    }

    pub(crate) fn record(&mut self, chunk: usize, pc: usize) {
        self.chunks[chunk].executions[pc] += 1;
    }

    pub(crate) fn finish_run(&mut self) {
        if let Some(started_at) = self.started_at.take() {
            self.elapsed += started_at.elapsed();
            self.runs += 1;
        }
    }

    fn bind(&mut self, module: &Module) {
        self.chunks = module
            .chunks
            .iter()
            .map(|chunk| VmChunkStats {
                name: chunk.name.clone(),
                opcodes: chunk.code.iter().map(opcode_name).collect(),
                executions: vec![0; chunk.code.len()],
            })
            .collect();
        self.bound = true;
    }

    fn matches(&self, module: &Module) -> bool {
        self.chunks.len() == module.chunks.len()
            && self
                .chunks
                .iter()
                .zip(&module.chunks)
                .all(|(stats, chunk)| {
                    stats.name == chunk.name
                        && stats.opcodes.len() == chunk.code.len()
                        && stats
                            .opcodes
                            .iter()
                            .copied()
                            .eq(chunk.code.iter().map(opcode_name))
                })
    }
}

impl VmChunkStats {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn emitted(&self) -> u64 {
        self.opcodes.len() as u64
    }

    pub fn executed(&self) -> u64 {
        self.executions.iter().sum()
    }

    /// Execution counts indexed by bytecode PC.
    pub fn instruction_executions(&self) -> &[u64] {
        &self.executions
    }
}

fn opcode_name(insn: &Insn) -> &'static str {
    match insn {
        Insn::Const { .. } => "Const",
        Insn::Move { .. } => "Move",
        Insn::Add { .. } => "Add",
        Insn::Sub { .. } => "Sub",
        Insn::Mul { .. } => "Mul",
        Insn::Div { .. } => "Div",
        Insn::And { .. } => "And",
        Insn::Or { .. } => "Or",
        Insn::Xor { .. } => "Xor",
        Insn::Shl { .. } => "Shl",
        Insn::Shr { .. } => "Shr",
        Insn::Not { .. } => "Not",
        Insn::Cmp { .. } => "Cmp",
        Insn::Trunc { .. } => "Trunc",
        Insn::IToF { .. } => "IToF",
        Insn::BToI { .. } => "BToI",
        Insn::IToB { .. } => "IToB",
        Insn::CellNew { .. } => "CellNew",
        Insn::CellGet { .. } => "CellGet",
        Insn::CellSet { .. } => "CellSet",
        Insn::AggNew { .. } => "AggNew",
        Insn::StringLit { .. } => "StringLit",
        Insn::Field { .. } => "Field",
        Insn::FieldIndex { .. } => "FieldIndex",
        Insn::GetElement { .. } => "GetElement",
        Insn::GetTag { .. } => "GetTag",
        Insn::ExistentialPack { .. } => "ExistentialPack",
        Insn::ExistentialWitness { .. } => "ExistentialWitness",
        Insn::ExistentialPayload { .. } => "ExistentialPayload",
        Insn::SetField { .. } => "SetField",
        Insn::SetFieldIndex { .. } => "SetFieldIndex",
        Insn::Alloc { .. } => "Alloc",
        Insn::Free { .. } => "Free",
        Insn::Retain { .. } => "Retain",
        Insn::IsUnique { .. } => "IsUnique",
        Insn::Load { .. } => "Load",
        Insn::CheckedIndexedLoad { .. } => "CheckedIndexedLoad",
        Insn::Store { .. } => "Store",
        Insn::Copy { .. } => "Copy",
        Insn::Swap { .. } => "Swap",
        Insn::Io { .. } => "Io",
        Insn::TaskSpawn { .. } => "TaskSpawn",
        Insn::TaskJoin { .. } => "TaskJoin",
        Insn::TaskWidth { .. } => "TaskWidth",
        Insn::ChanSend { .. } => "ChanSend",
        Insn::ChanTake { .. } => "ChanTake",
        Insn::ChanCtl { .. } => "ChanCtl",
        Insn::Suspend { .. } => "Suspend",
        Insn::Resume { .. } => "Resume",
        Insn::Cancel { .. } => "Cancel",
        Insn::Call { .. } => "Call",
        Insn::MakeClosure { .. } => "MakeClosure",
        Insn::EnvGet { .. } => "EnvGet",
        Insn::CallIndirect { .. } => "CallIndirect",
        Insn::Jump { .. } => "Jump",
        Insn::Branch { .. } => "Branch",
        Insn::Switch { .. } => "Switch",
        Insn::Ret { .. } => "Ret",
        Insn::ObjectNew { .. } => "ObjectNew",
        Insn::SetFinalizer { .. } => "SetFinalizer",
        Insn::ObjectGet { .. } => "ObjectGet",
        Insn::ObjectSet { .. } => "ObjectSet",
        Insn::RegionAcquire { .. } => "RegionAcquire",
        Insn::RegionRelease { .. } => "RegionRelease",
        Insn::MakeCont { .. } => "MakeCont",
        Insn::CallCont { .. } => "CallCont",
        Insn::UnwindRet => "UnwindRet",
        Insn::PushHandler { .. } => "PushHandler",
        Insn::FindHandler { .. } => "FindHandler",
        Insn::GetFloor { .. } => "GetFloor",
        Insn::SetFloor { .. } => "SetFloor",
        Insn::Trap { .. } => "Trap",
    }
}
