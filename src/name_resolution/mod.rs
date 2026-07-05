pub mod builtins;
pub mod decl_declarer;
pub mod name_resolver;
pub mod symbol;

#[cfg(test)]
pub mod name_resolver_tests;

#[macro_export]
macro_rules! on {
    ($expr: expr, $pattern: pat, $body: block) => {
      #[allow(irrefutable_let_patterns)]
      if let $pattern = $expr $body
    };
}
