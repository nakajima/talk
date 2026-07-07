#![feature(test)]

extern crate test;

use talk::compiling::driver::{compile_bytecode_from, Driver, DriverConfig, Lowered, Source};
use talk::vm::interp::Value;
use talk::vm::{interp, io::CaptureIO, Module};
use test::{black_box, Bencher};

#[derive(Clone, Copy)]
struct Program {
    name: &'static str,
    source: &'static str,
    expected_value: i64,
    expected_stdout: &'static str,
}

impl Program {
    fn lower(self) -> Driver<Lowered> {
        let typed = Driver::new(
            vec![Source::from(self.source)],
            DriverConfig::new(self.name),
        )
        .parse()
        .expect("parse benchmark program")
        .resolve_names()
        .expect("resolve benchmark program")
        .type_check();
        assert!(
            !typed.has_errors(),
            "{}: type errors: {:?}",
            self.name,
            typed.diagnostics()
        );

        let mut lowered = typed.lower();
        assert!(
            lowered.phase.diagnostics.is_empty(),
            "{}: lowering diagnostics: {:?}",
            self.name,
            lowered.phase.diagnostics
        );
        let verified = lowered.phase.program.verify();
        assert!(
            verified.is_ok(),
            "{}: verifier: {:?}",
            self.name,
            verified.err()
        );
        lowered
    }

    fn run_end_to_end(self) -> (Value, String) {
        let mut lowered = self.lower();
        lowered.run_vm_with_output().expect("run benchmark program")
    }

    fn compile_module(self) -> Module {
        let bytecode = compile_bytecode_from(self.name, Source::from(self.source))
            .expect("compile benchmark bytecode");
        Module::decode_bytecode(&bytecode).expect("decode benchmark bytecode")
    }

    fn run_scheduled(self, module: &Module) -> (Value, String) {
        let mut io = CaptureIO::default();
        let value = interp::run(module, &mut io).expect("run benchmark module");
        let stdout = String::from_utf8_lossy(&io.out).into_owned();
        (value, stdout)
    }

    fn assert_result(self, value: &Value, stdout: &str) {
        assert_eq!(
            value,
            &Value::I64(self.expected_value),
            "{}: value",
            self.name
        );
        assert_eq!(stdout, self.expected_stdout, "{}: stdout", self.name);
    }

    fn bench_end_to_end(self, b: &mut Bencher) {
        let (value, stdout) = self.run_end_to_end();
        self.assert_result(&value, &stdout);

        b.iter(|| {
            let (value, stdout) = self.run_end_to_end();
            black_box((value, stdout))
        });
    }

    fn bench_scheduled_vm(self, b: &mut Bencher) {
        let module = self.compile_module();
        let (value, stdout) = self.run_scheduled(&module);
        self.assert_result(&value, &stdout);

        b.iter(|| {
            let (value, stdout) = self.run_scheduled(black_box(&module));
            black_box((value, stdout))
        });
    }
}

const TIGHT_LOOP: Program = Program {
    name: "bench_tight_loop",
    source: r#"func sumTo(n: Int) -> Int {
    let total = 0
    let i = 0
    loop i < n {
        total = total + i
        i = i + 1
    }
    total
}

sumTo(20000)"#,
    expected_value: 199990000,
    expected_stdout: "",
};

const RECURSIVE_FIB: Program = Program {
    name: "bench_recursive_fib",
    source: r#"func fib(n: Int) -> Int {
    if n <= 1 {
        n
    } else {
        fib(n - 2) + fib(n - 1)
    }
}

fib(22)"#,
    expected_value: 17711,
    expected_stdout: "",
};

const CLOSURE_CALLS: Program = Program {
    name: "bench_closure_calls",
    source: r#"func apply(f: (Int) -> Int, n: Int) -> Int {
    let total = 0
    let i = 0
    loop i < n {
        total = total + f(i)
        i = i + 1
    }
    total
}

let offset = 1
apply(func(n) { n * 2 + offset }, 5000)"#,
    expected_value: 25000000,
    expected_stdout: "",
};

const EFFECT_RESUME: Program = Program {
    name: "bench_effect_resume",
    source: r#"effect 'step(n) -> Int

@handle 'step { n in
    continue n + 1
}

func go(n: Int) 'step -> Int {
    let total = 0
    let i = 0
    loop i < n {
        total = total + 'step(i)
        i = i + 1
    }
    total
}

go(1000)"#,
    expected_value: 500500,
    expected_stdout: "",
};

const STRING_CONCAT: Program = Program {
    name: "bench_string_concat",
    source: r#"func build(n: Int) -> Int {
    let text = ""
    let i = 0
    loop i < n {
        text = text + "x"
        i = i + 1
    }
    text.byte_count
}

build(128)"#,
    expected_value: 128,
    expected_stdout: "",
};

const ARRAY_FOR: Program = Program {
    name: "bench_array_for",
    source: r#"func sumArray(rounds: Int) -> Int {
    let values = [1, 2, 3, 4, 5, 6, 7, 8]
    let total = 0
    let i = 0
    loop i < rounds {
        for value in values {
            total = total + value
        }
        i = i + 1
    }
    total
}

sumArray(1000)"#,
    expected_value: 36000,
    expected_stdout: "",
};

macro_rules! bench_program {
    ($end_to_end:ident, $scheduled_vm:ident, $program:expr) => {
        #[bench]
        fn $end_to_end(b: &mut Bencher) {
            $program.bench_end_to_end(b);
        }

        #[bench]
        fn $scheduled_vm(b: &mut Bencher) {
            $program.bench_scheduled_vm(b);
        }
    };
}

bench_program!(e2e_tight_loop, scheduled_vm_tight_loop, TIGHT_LOOP);
bench_program!(e2e_recursive_fib, scheduled_vm_recursive_fib, RECURSIVE_FIB);
bench_program!(e2e_closure_calls, scheduled_vm_closure_calls, CLOSURE_CALLS);
bench_program!(e2e_effect_resume, scheduled_vm_effect_resume, EFFECT_RESUME);
bench_program!(e2e_string_concat, scheduled_vm_string_concat, STRING_CONCAT);
bench_program!(e2e_array_for, scheduled_vm_array_for, ARRAY_FOR);
