// Use a procedural macro to generate bindings for the world we specified in
// `host.wit`
wit_bindgen::generate!({
    world: "host",
});

#[allow(warnings)]
mod bindings;

pub fn start() {
    console_error_panic_hook::set_once();
}

mod talk_ex {
    use crate::{
        bindings::{Guest, HighlightToken},
    };

    use talk::{
        compiling::driver::Driver, highlighter::Higlighter, interpret::{interpreter::IRInterpreter, io::test_io::TestIO},
        lowering::ir_printer::print, transforms::monomorphizer::Monomorphizer,
    };

    pub struct TalkEx;

    impl Guest for TalkEx {
        fn ir(code: String) -> String {
            let mut driver = Driver::with_str(&code);
            let lowered = driver.lower().into_iter().next().unwrap();
            print(&lowered.module())
        }

        fn run(code: String) {
            let mut driver = Driver::with_str(&code);
            let lowered = driver.lower().into_iter().next().unwrap();
            let mono = Monomorphizer::new(&lowered.env).run(lowered.module());
            let mut io = TestIO::default();
            IRInterpreter::new(mono, &mut io, &driver.symbol_table)
                .run()
                .unwrap();
        }

        fn highlight(code: String) -> Vec<HighlightToken> {
            Higlighter::new(&code)
                .highlight()
                .into_iter()
                .map(|tok| HighlightToken {
                    kind: tok.kind.to_string(),
                    start: tok.start,
                    end: tok.end,
                })
                .collect()
        }
    }
}

use talk_ex::TalkEx;
bindings::export!(TalkEx with_types_in bindings);
