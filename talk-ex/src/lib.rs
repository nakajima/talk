use crate::talk_ex::Runtime;

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
    use std::{cell::RefCell, path::PathBuf};

    use talk::interpret::io::InterpreterIO;
    use talk::{
        compiling::driver::{Driver, DriverConfig},
        highlighter::Higlighter,
        interpret::{interpreter::IRInterpreter, io::test_io::TestIO},
        transforms::monomorphizer::Monomorphizer,
    };

    use crate::bindings::exports::talkex::host::types::{Guest, GuestRunner, HighlightToken};

    pub struct Runtime {
        pub io: TestIO,
        driver: RefCell<Driver>,
    }

    impl GuestRunner for Runtime {
        fn new() -> Self {
            Self {
                io: TestIO::default(),
                driver: RefCell::new(Driver::new(DriverConfig::default())),
            }
        }

        fn highlight(&self, code: String) -> Vec<HighlightToken> {
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

        fn ir(&self, code: String) -> String {
            let mut driver = self.driver.borrow_mut();
            driver.update_file(&PathBuf::from("-"), code);
            let lowered = driver.lower().into_iter().next().unwrap();
            talk::lowering::ir_printer::print(&lowered.module())
        }

        fn run(&self, code: String) -> () {
            let mut driver = self.driver.borrow_mut();
            driver.update_file(&PathBuf::from("-"), code);
            let lowered = driver.lower().into_iter().next().unwrap();
            let mono = Monomorphizer::new(&lowered.env).run(lowered.module());
            IRInterpreter::new(mono, &self.io, &driver.symbol_table)
                .run()
                .expect("Did not run.");
        }

        fn ping(&self) -> () {
            self.io.write_all("PONG".as_bytes());
        }
    }

    impl Guest for Runtime {
        type Runner = Runtime;
    }
}

bindings::export!(Runtime with_types_in bindings);
