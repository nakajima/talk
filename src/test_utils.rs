#[macro_export]
macro_rules! fxhashmap {
    ($($k:expr => $v:expr),* $(,)?) => {{
        let mut m = rustc_hash::FxHashMap::default();
        $( m.insert($k, $v); )*
        m
    }};
}

#[macro_export]
macro_rules! indexmap {
    ($($k:expr => $v:expr),* $(,)?) => {{
        let mut m = indexmap::IndexMap::new();
        $( m.insert($k, $v); )*
        m
    }};
}

#[macro_export]
macro_rules! any_expr {
    ($expr:expr) => {{
        $crate::parsing::node_kinds::expr::Expr {
            id: NodeID::ANY,
            span: $crate::parsing::span::Span::ANY,
            kind: $expr,
        }
    }};
}

#[macro_export]
macro_rules! any {
    // Pass an arbitrary list of fields
    ($ty:ident, { $($fields:tt)* }) => {{
        $ty {
            id: NodeID::ANY,
            span: Span::ANY,
            $($fields)*
        }
    }};

    // Convenience: pass just a kind expression
    ($ty:ident, $kind:expr) => {{
        $ty {
            id: NodeID::ANY,
            span: Span::ANY,
            kind: $kind,
        }
    }};
}

#[macro_export]
macro_rules! any_body {
    ($expr:expr) => {{
        $crate::node_kinds::body::Body {
            id: NodeID::ANY,
            span: $crate::parsing::span::Span::ANY,
            decls: $expr,
        }
    }};
}

#[macro_export]
macro_rules! any_block {
    ($expr:expr) => {{
        $crate::node_kinds::block::Block {
            id: NodeID::ANY,
            span: $crate::parsing::span::Span::ANY,
            args: vec![],
            body: $expr,
        }
    }};
}

#[macro_export]
macro_rules! assert_eq_diff_display {
    ($lhs:expr, $rhs:expr $(,)?) => {{
        if $lhs != $rhs {
            use prettydiff::diff_lines;
            panic!(
                "Assertion failed, {} != {}\nDiff:\n{}",
                $lhs,
                $rhs,
                diff_lines(format!("{}", $lhs).as_str(), format!("{}", $rhs).as_str())
            );
        }
    }};
}

#[macro_export]
macro_rules! assert_eq_diff {
    ($lhs:expr, $rhs:expr $(,)?) => {{
        if $lhs != $rhs {
            use prettydiff::diff_lines;
            panic!(
                "Assertion failed, {:?} != {:?}\nDiff:\n{}",
                $lhs,
                $rhs,
                diff_lines(
                    format!("{:#?}", $lhs).as_str(),
                    format!("{:#?}", $rhs).as_str()
                )
            );
        }
    }};
}

#[macro_export]
macro_rules! assert_match_capture {
    ($expr:expr, $pattern:pat, $capture_block:block) => {{
        let value = $expr;
        match value {
            $pattern => $capture_block,
            _ => panic!(
                "assertion failed: value `{:?}` did not match pattern `{}`",
                value,
                stringify!($pattern)
            ),
        }
    }};
}

pub mod trace {
    use tracing::{Metadata, Subscriber};
    use tracing_subscriber::{
        fmt::TestWriter,
        layer::Filter,
        registry::{LookupSpan, SpanRef},
    };

    #[derive(Debug)]
    struct PreludeMarker;
    struct MarkPreludeSpan;

    impl<S> tracing_subscriber::Layer<S> for MarkPreludeSpan
    where
        S: Subscriber + for<'a> LookupSpan<'a>,
    {
        fn on_new_span(
            &self,
            attrs: &tracing::span::Attributes<'_>,
            id: &tracing::span::Id,
            ctx: tracing_subscriber::layer::Context<'_, S>,
        ) {
            if let Some(span) = ctx.span(id) {
                let mut extensions = span.extensions_mut();
                let mut visitor = HasPreludeField(false);
                attrs.record(&mut visitor);
                if visitor.has_prelude_field() {
                    extensions.insert(PreludeMarker);
                }
            }
        }
    }

    struct HasPreludeField(bool);

    impl tracing::field::Visit for HasPreludeField {
        fn record_bool(&mut self, field: &tracing::field::Field, value: bool) {
            if field.name() == "prelude" && value {
                self.0 = true;
            }
        }

        fn record_debug(&mut self, _field: &tracing::field::Field, _value: &dyn std::fmt::Debug) {}
    }

    impl HasPreludeField {
        fn has_prelude_field(&self) -> bool {
            self.0
        }
    }

    struct SuppressPrelude;

    impl<S> Filter<S> for SuppressPrelude
    where
        S: Subscriber + for<'a> LookupSpan<'a>,
    {
        fn enabled(
            &self,
            _metadata: &Metadata<'_>,
            ctx: &tracing_subscriber::layer::Context<'_, S>,
        ) -> bool {
            if let Some(span) = ctx.lookup_current() {
                // Walk up the span tree to see if we're inside a prelude span
                let mut current: Option<SpanRef<S>> = Some(span);
                while let Some(span) = current {
                    if span.extensions().get::<PreludeMarker>().is_some() {
                        return false; // suppress this log
                    }
                    current = span.parent();
                }
            }
            true
        }
    }

    pub fn init() {
        color_eyre::install().unwrap();
        use tracing_subscriber::{EnvFilter, prelude::*, registry};

        if std::env::var("LOG_PRELUDE") == Ok("1".into()) {
            let tree = tracing_tree::HierarchicalLayer::new(2)
                .with_writer(TestWriter::new())
                .with_filter(EnvFilter::from_default_env()); // ordinary RUST_LOG filtering

            registry()
                .with(MarkPreludeSpan) // sets the PreludeMarker
                .with(tree)
                .init();
        } else {
            let tree = tracing_tree::HierarchicalLayer::new(2)
                .with_ansi(std::env::var("NO_COLOR").is_err())
                .with_writer(TestWriter::new())
                .with_filter(SuppressPrelude) // kills everything inside a prelude span
                .with_filter(EnvFilter::from_default_env()); // ordinary RUST_LOG filtering

            registry()
                .with(MarkPreludeSpan) // sets the PreludeMarker
                .with(tree)
                .init();
        };
    }
}
