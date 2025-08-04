use std::collections::BTreeMap;

use crate::{expr_id::ExprID, types::visitor::Scope};

pub struct Scopes {
    scopes: BTreeMap<ExprID, Scope>
}

