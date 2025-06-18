use std::collections::{HashMap, HashSet};

use crate::{
    analysis::{cfg::ControlFlowGraph, function_analysis_pass::FunctionAnalysisPass},
    environment::{Property, StructDef},
    lowering::{
        instr::Instr,
        ir_error::IRError,
        ir_value::IRValue,
        lowerer::{BasicBlockID, IRFunction},
        register::Register,
    },
};

pub struct DefiniteInitizationPass {
    struct_def: StructDef,
}

impl FunctionAnalysisPass for DefiniteInitizationPass {
    type Output = ();
    type Error = IRError;

    fn run(&self, func: &IRFunction, cfg: &ControlFlowGraph) -> Result<(), IRError> {
        if self.struct_def.properties.is_empty() {
            return Ok(());
        }

        let (_self_reg, property_pointers) = self.get_property_pointers(func);

        let mut out_sets: HashMap<BasicBlockID, HashSet<Property>> = HashMap::new();

        // Initialize all out_sets to empty
        for block in &func.blocks {
            out_sets.insert(block.id, HashSet::new());
        }

        let mut changed = true;
        while changed {
            changed = false;

            for &block_id in &cfg.reverse_postorder {
                let mut in_set = {
                    let predecessors = &cfg.predecessors[&block_id];
                    if let Some(&first_pred_id) = predecessors.first() {
                        let mut running_set = out_sets[&first_pred_id].clone();
                        for &pred_id in predecessors.iter().skip(1) {
                            running_set = running_set
                                .intersection(&out_sets[&pred_id])
                                .cloned()
                                .collect();
                        }
                        running_set
                    } else {
                        HashSet::new() // entry block
                    }
                };

                let block = &func.blocks[block_id.0 as usize];
                for instr in &block.instructions {
                    if let Instr::Store { location, .. } = instr
                        && let Some(property_symbol) = property_pointers.get(location)
                    {
                        in_set.insert(property_symbol.clone());
                    }
                }

                let out_set = in_set;
                if out_set != out_sets[&block_id] {
                    out_sets.insert(block_id, out_set);
                    changed = true;
                }
            }
        }

        let all_properties: HashSet<Property> =
            HashSet::from_iter(self.struct_def.properties.clone());
        let mut props_initialized_on_all_paths: Option<HashSet<Property>> = None;

        for block in &func.blocks {
            if let Some(Instr::Ret { .. }) = block.instructions.last() {
                let exit_set = &out_sets[&block.id];
                if let Some(ref mut intersection_set) = props_initialized_on_all_paths {
                    *intersection_set = intersection_set.intersection(exit_set).cloned().collect();
                } else {
                    props_initialized_on_all_paths = Some(exit_set.clone());
                }
            }
        }

        let initialized_set = props_initialized_on_all_paths.unwrap_or_default();
        let uninitialized_properties = all_properties
            .difference(&initialized_set)
            .collect::<Vec<_>>();

        if uninitialized_properties.is_empty() {
            Ok(())
        } else {
            Err(IRError::PartialInitialization(
                func.name.to_string(),
                uninitialized_properties.into_iter().cloned().collect(),
            ))
        }
    }
}

impl DefiniteInitizationPass {
    pub fn new(struct_def: StructDef) -> Self {
        Self { struct_def }
    }

    // Identifies which property a register points to.
    // A register points to a property if it's the result of a gep on self.
    fn get_property_pointers(&self, func: &IRFunction) -> (Register, HashMap<Register, Property>) {
        let mut property_pointers = HashMap::new();
        // The 'self' parameter is the first argument to an init method.
        let self_reg = func.env_reg;

        for block in &func.blocks {
            for instr in &block.instructions {
                if let Instr::GetElementPointer {
                    dest, base, index, ..
                } = instr
                    && *base == self_reg
                {
                    // The index of the gep corresponds to the property index.

                    let index = match index {
                        IRValue::ImmediateInt(index) => index,
                        IRValue::Register(_register) => todo!(),
                    };

                    if let Some(property) = self.struct_def.properties.iter().nth(*index as usize) {
                        property_pointers.insert(*dest, property.clone());
                    }
                }
            }
        }
        (self_reg, property_pointers)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        SourceFile, SymbolID,
        compiling::driver::Driver,
        environment::{Property, TypeDef},
        lowering::ir_module::IRModule,
        source_file,
        type_checker::Ty,
    };

    fn lower(code: &'static str) -> (IRModule, SourceFile<source_file::Lowered>) {
        let mut driver = Driver::with_str(code);

        let lowered = driver.lower().into_iter().next().unwrap();
        let file = lowered.source_file(&"-".into()).unwrap().clone();
        let module = lowered.module();
        (module, file)
    }

    #[test]
    fn does_nothing_when_its_fine() {
        let (module, file) = lower(
            "
      struct Person {
        let age: Int

        init(age: Int) {
          self.age = age
        }
      }
      ",
        );

        let person_id = SymbolID::resolved(1);
        let function = module
            .functions
            .iter()
            .find(|f| f.name == format!("@_{}_Person_init", person_id.0))
            .unwrap();

        let Some(TypeDef::Struct(struct_def)) = file.type_def(&person_id) else {
            panic!("didn't get struct def");
        };

        let cfg = ControlFlowGraph::new(&function);

        assert!(
            DefiniteInitizationPass::new(struct_def.clone())
                .run(function, &cfg)
                .is_ok()
        );
    }

    #[test]
    fn provides_error_with_missing_properties() {
        let (module, file) = lower(
            "
      struct Person {
        let age: Int

        init(age: Int) {}
      }
      ",
        );

        let person_id = SymbolID::resolved(1);
        let function = module
            .functions
            .iter()
            .find(|f| f.name == format!("@_{}_Person_init", person_id.0))
            .unwrap();

        let Some(TypeDef::Struct(struct_def)) = file.type_def(&person_id) else {
            panic!("didn't get struct def");
        };

        let cfg = ControlFlowGraph::new(&function);

        assert_eq!(
            Err(IRError::PartialInitialization(
                format!("@_{}_Person_init", person_id.0),
                vec![Property {
                    name: "age".into(),
                    ty: Ty::Int,
                    symbol: SymbolID::resolved(2)
                }]
            )),
            DefiniteInitizationPass::new(struct_def.clone()).run(function, &cfg)
        );
    }

    #[test]
    fn provides_error_with_conditional() {
        let (module, file) = lower(
            "
      struct Person {
        let age: Int

        init(age: Int) {
          if age > 1 {
            self.age = age
          }
        }
      }
      ",
        );

        let person_id = SymbolID::resolved(1);
        let function = module
            .functions
            .iter()
            .find(|f| f.name == format!("@_{}_Person_init", person_id.0))
            .unwrap();

        let Some(TypeDef::Struct(struct_def)) = file.type_def(&person_id) else {
            panic!("didn't get struct def");
        };

        let cfg = ControlFlowGraph::new(&function);

        assert_eq!(
            Err(IRError::PartialInitialization(
                format!("@_{}_Person_init", person_id.0),
                vec![Property {
                    name: "age".into(),
                    ty: Ty::Int,
                    symbol: SymbolID::resolved(2)
                }]
            )),
            DefiniteInitizationPass::new(struct_def.clone()).run(function, &cfg)
        );
    }

    #[test]
    fn provides_is_ok_with_else_conditional() {
        let (module, file) = lower(
            "
        struct Person {
          let age: Int

          init(age: Int) {
            if age > 1 {
              self.age = age
            } else {
              self.age = 123
            }
          }
        }
      ",
        );

        let person_id = SymbolID::resolved(1);
        let function = module
            .functions
            .iter()
            .find(|f| f.name == format!("@_{}_Person_init", person_id.0))
            .unwrap();

        let Some(TypeDef::Struct(struct_def)) = file.type_def(&person_id) else {
            panic!("didn't get struct def");
        };

        let cfg = ControlFlowGraph::new(&function);

        assert_eq!(
            Ok(()),
            DefiniteInitizationPass::new(struct_def.clone()).run(function, &cfg)
        );
    }
}
