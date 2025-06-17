use crate::{analysis::cfg::ControlFlowGraph, lowering::lowerer::IRFunction};

pub trait FunctionAnalysisPass {
    type Output;
    type Error;

    fn run(
        &self,
        function: &IRFunction,
        cfg: &ControlFlowGraph,
    ) -> Result<Self::Output, Self::Error>;
}
