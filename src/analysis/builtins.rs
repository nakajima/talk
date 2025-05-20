use super::type_checker::Ty;

pub fn match_builtin(name: &'static str) -> Option<Ty> {
    let res = match name {
        "Int" => Some(Ty::Int),
        "Float" => Some(Ty::Float),
        _ => None,
    };

    log::info!("Matching {}, res: {:?}", name, res);

    res
}
