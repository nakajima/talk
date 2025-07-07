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

#[macro_export]
macro_rules! assert_lowered_functions {
    ($left:expr, $right:expr $(,)?) => {
        match (&$left, &$right) {
            (left_val, right_val) => {
                use $crate::lowering::ir_module::IRModule;

                if !right_val.iter().all(|f| left_val.functions.contains(f)) {
                    let right_program = IRModule {
                        functions: right_val.clone(),
                    };

                    use prettydiff::{diff_chars, diff_lines};
                    use $crate::lowering::ir_printer::print;
                    tracing::error!(
                        "{}",
                        diff_chars(
                            &format!("{:?}", &left_val.functions),
                            &format!("{:?}", right_val)
                        )
                    );

                    panic!(
                        "{}\n{}",
                        diff_lines("Actual", "Expected"),
                        diff_lines(print(left_val).as_ref(), print(&right_program).as_ref())
                    )
                }
            }
        }
    };
}

// Check that two functions are the same. Ignores debug info.
#[macro_export]
macro_rules! assert_lowered_function {
    ($module:expr, $function_name:expr, $expected_function:expr $(,)?) => {
        match (&$module, &$function_name, $expected_function) {
            (module, function_name, expected_function) => {
                let function = module
                    .functions
                    .iter()
                    .find(|f| &f.name == function_name)
                    .unwrap_or_else(|| {
                        panic!(
                            "did not find function in compiled ir: {} in {:?}",
                            function_name,
                            module
                                .functions
                                .iter()
                                .map(|f| f.name.clone())
                                .collect::<Vec<String>>()
                        )
                    });

                let mut function = function.clone();
                let mut expected_function = expected_function.clone();
                function.debug_info = Default::default();
                expected_function.debug_info = Default::default();

                #[allow(clippy::print_with_newline)]
                if function != expected_function {
                    use prettydiff::{diff_chars, diff_lines};
                    use $crate::lowering::ir_printer::format_func;
                    print!(
                        "{}\n",
                        diff_chars(
                            &format!("{:?}", &function),
                            &format!("{:?}", expected_function)
                        )
                    );

                    panic!(
                        "{}\n{}",
                        diff_lines("Actual", "Expected"),
                        diff_lines(
                            format_func(&function).as_ref(),
                            format_func(&expected_function).as_ref()
                        )
                    )
                }
            }
        }
    };
}

pub mod trace {
    use tracing::{Metadata, Subscriber};
    use tracing_subscriber::{
        EnvFilter,
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
        use tracing_subscriber::prelude::*;
        use tracing_subscriber::{fmt, registry};

        // Build the fmt layer with filtering logic
        let fmt_layer = fmt::layer()
            .compact()
            .with_test_writer()
            // .with_span_events(FmtSpan::ENTER | FmtSpan::EXIT)
            .with_ansi(true)
            .without_time()
            .with_target(false)
            .with_file(true)
            .with_line_number(true)
            .with_filter(EnvFilter::from_default_env());
        // .with_filter(SuppressPrelude);

        registry().with(MarkPreludeSpan).with(fmt_layer).init();
    }
}
