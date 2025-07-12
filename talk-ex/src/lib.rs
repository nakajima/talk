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
    use std::path::PathBuf;
    use std::sync::Mutex;

    use talk::highlighter::Higlighter;
    use talk::interpret::interpreter::IRInterpreter;
    use talk::transforms::monomorphizer::Monomorphizer;
    use talk::{compiling::driver::Driver, interpret::io::test_io::TestIO};

    use crate::bindings::{Guest, HighlightToken, Io};

    lazy_static::lazy_static! {
        static ref DRIVER: Mutex<Driver> = Mutex::new(Driver::default());
    }

    pub struct Runtime;

    impl Guest for Runtime {
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

        fn ir(code: String) -> String {
            let mut driver = DRIVER.lock().expect("Unable to unlock driver");
            driver.update_file(&PathBuf::from("-"), code);
            let lowered = driver.lower().into_iter().next().unwrap();
            talk::lowering::ir_printer::print(&lowered.module())
        }

        fn run(code: String) -> Io {
            let mut driver = DRIVER.lock().expect("Unable to unlock driver");
            driver.update_file(&PathBuf::from("-"), code);
            let lowered = driver.lower().into_iter().next().unwrap();
            let mono = Monomorphizer::new(&lowered.env).run(lowered.module());
            let io = TestIO::new();
            IRInterpreter::new(mono, &io, &driver.symbol_table)
                .run()
                .expect("Did not run.");

            Io {
                stdout: io.stdout(),
                stderr: io.stderr(),
            }
        }

        fn ping() -> Io {
            Io {
                stdout: "PONG\n".as_bytes().to_vec(),
                stderr: vec![],
            }
        }
    }
}

use talk_ex::Runtime;
crate::export!(Runtime with_types_in bindings);
