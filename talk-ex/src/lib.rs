// Use a procedural macro to generate bindings for the world we specified in
// `host.wit`
wit_bindgen::generate!({
    // the name of the world in the `*.wit` input file
    world: "talk-ex",
});

#[allow(warnings)]
mod bindings;
mod console;
mod io;

pub fn start() {
    console_error_panic_hook::set_once();
}

mod talk_ex {
    use crate::{bindings::HighlightToken, io::WasmIO};

    use talk::{
        compiling::driver::Driver, highlighter::Higlighter, interpret::interpreter::IRInterpreter,
        lowering::ir_printer::print, transforms::monomorphizer::Monomorphizer,
    };

    use crate::bindings::Guest;

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
            let mut io = WasmIO::default();
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
