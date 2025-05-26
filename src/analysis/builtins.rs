use super::type_checker::Ty;

pub fn match_builtin(name: String) -> Option<Ty> {
    let res = match name.as_str() {
        "Int" => Some(Ty::Int),
        "Float" => Some(Ty::Float),
        _ => None,
    };

    log::info!("Matching {}, res: {:?}", name, res);

    res
}
