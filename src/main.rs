use std::env;
use std::fs;

use wasm_runner::decoder::Decoder;
use wasm_runner::executor::{instantiate, invoke, Context, ExecutionError};
use wasm_runner::instance::{Extarnval, Hostfunc};
use wasm_runner::module::Name;
use wasm_runner::types::{Functype, Resulttype, Valtype};
use wasm_runner::validator::validate;
use wasm_runner::value::{F32Bytes, F64Bytes, Value, ValueKind, WasmRunnerResult};

// test
use wast::parser::{self, ParseBuffer};
use wast::{
    AssertExpression, Expression, Instruction, NanPattern, Wast, WastDirective, WastExecute,
    WastInvoke,
};

fn main() {
    let base_dir_path = env::args().skip(1).next().expect("path to wast directory");
    run_test(&format!("{}/block.wast", base_dir_path));
    run_test(&format!("{}/br.wast", base_dir_path));
    run_test(&format!("{}/loop.wast", base_dir_path));
    run_test(&format!("{}/f32.wast", base_dir_path));
    run_test(&format!("{}/f32_cmp.wast", base_dir_path));
    run_test(&format!("{}/f64.wast", base_dir_path));
    run_test(&format!("{}/i32.wast", base_dir_path));
    run_test(&format!("{}/i64.wast", base_dir_path));
    run_test(&format!("{}/int_literals.wast", base_dir_path));
}

fn run_invoke_ation<'a>(
    ctx: &mut Context,
    name: &'a str,
    args: Vec<Expression<'a>>,
) -> Result<WasmRunnerResult, ExecutionError> {
    let arguments = args
        .into_iter()
        .map(|arg| {
            assert_eq!(arg.instrs.len(), 1);
            use Instruction::*;
            let value_kind = match arg.instrs[0] {
                I32Const(x) => ValueKind::I32(x as u32),
                I64Const(x) => ValueKind::I64(x as u64),
                F32Const(ref x) => {
                    ValueKind::F32(F32Bytes::new(f32::from_le_bytes(x.bits.to_le_bytes())))
                }
                F64Const(ref x) => {
                    ValueKind::F64(F64Bytes::new(f64::from_le_bytes(x.bits.to_le_bytes())))
                }
                _ => unimplemented!(),
            };
            Value::new(value_kind)
        })
        .collect::<Vec<Value>>();
    let funcaddr = ctx.find_funcaddr(&Name::new(name.to_string())).unwrap();
    invoke(ctx, funcaddr, arguments)
}

fn run_test(wast_file_path: &str) {
    println!("[[test]] {}", wast_file_path);
    let wast_text = fs::read_to_string(wast_file_path).unwrap();
    let buf = ParseBuffer::new(&wast_text).unwrap();
    let wast_ast = parser::parse::<Wast>(&buf).unwrap();
    let mut ctx = Context::new();
    register_spectest_hostfunc(&mut ctx);
    let mut last_moduleinst = None;
    for directive in wast_ast.directives {
        use WastDirective::*;
        match directive {
            Module(mut module) => {
                let name = module.id.map(|id| Name::new(id.name().to_string()));
                let mut reader = &module.encode().unwrap()[..];
                let mut decoder = Decoder::new(&mut reader);
                let mut module = decoder.run().expect("should success");
                if let Some(name) = name {
                    module.set_name(name);
                }
                validate(&module).unwrap();
                let moduleinst = instantiate(&mut ctx, &module).unwrap();
                last_moduleinst = Some(moduleinst);
            }
            Register { name, .. } => {
                let contents = last_moduleinst
                    .as_ref()
                    .unwrap()
                    .extract_exported_contents();
                for (content_name, content) in contents {
                    ctx.register_content(Some(Name::new(name.to_string())), content_name, content);
                }
            }
            Invoke(WastInvoke { name, args, .. }) => {
                run_invoke_ation(&mut ctx, name, args).unwrap();
            }
            AssertReturn { exec, results, .. } => {
                let (func_name, arguments) = match exec {
                    WastExecute::Invoke(WastInvoke { name, args, .. }) => (name, args),
                    _ => unimplemented!(),
                };
                let (expected_result, should_replace_nan): (Vec<Value>, Vec<bool>) = results
                    .into_iter()
                    .map(|res| {
                        use AssertExpression::*;
                        match res {
                            I32(x) => (Value::new(ValueKind::I32(x as u32)), false),
                            I64(x) => (Value::new(ValueKind::I64(x as u64)), false),
                            F32(NanPattern::Value(x)) => (
                                Value::new(ValueKind::F32(F32Bytes::new(f32::from_le_bytes(
                                    x.bits.to_le_bytes(),
                                )))),
                                false,
                            ),
                            // @todo fix to handle NaN correctly
                            F32(NanPattern::CanonicalNan) => {
                                (Value::new(ValueKind::F32(F32Bytes::new(f32::NAN))), true)
                            }
                            F32(NanPattern::ArithmeticNan) => {
                                (Value::new(ValueKind::F32(F32Bytes::new(f32::NAN))), true)
                            }
                            F64(NanPattern::Value(x)) => (
                                Value::new(ValueKind::F64(F64Bytes::new(f64::from_le_bytes(
                                    x.bits.to_le_bytes(),
                                )))),
                                false,
                            ),
                            // @todo fix to handle NaN correctly
                            F64(NanPattern::CanonicalNan) => {
                                (Value::new(ValueKind::F64(F64Bytes::new(f64::NAN))), true)
                            }
                            F64(NanPattern::ArithmeticNan) => {
                                (Value::new(ValueKind::F64(F64Bytes::new(f64::NAN))), true)
                            }
                            _ => unimplemented!(),
                        }
                    })
                    .unzip();

                let WasmRunnerResult::Values(res) =
                    run_invoke_ation(&mut ctx, func_name, arguments).unwrap();
                let res: Vec<Value> = if should_replace_nan.iter().any(|b| *b) {
                    res.iter()
                        .map(|v| match v.kind() {
                            ValueKind::F32(f) if f.is_nan() => {
                                Value::new(ValueKind::F32(F32Bytes::new(f32::NAN)))
                            }
                            ValueKind::F64(f) if f.is_nan() => {
                                Value::new(ValueKind::F64(F64Bytes::new(f64::NAN)))
                            }
                            _ => *v,
                        })
                        .collect()
                } else {
                    res
                };
                println!("{}: result = {:?}", func_name, res);
                assert_eq!(res, expected_result);
            }
            AssertTrap { exec, message, .. } => {
                let (func_name, arguments) = match exec {
                    WastExecute::Invoke(WastInvoke { name, args, .. }) => (
                        name,
                        args.into_iter()
                            .map(|arg| {
                                assert_eq!(arg.instrs.len(), 1);
                                use Instruction::*;
                                let value_kind = match arg.instrs[0] {
                                    I32Const(x) => ValueKind::I32(x as u32),
                                    I64Const(x) => ValueKind::I64(x as u64),
                                    F32Const(ref x) => {
                                        ValueKind::F32(F32Bytes::from_bytes(x.bits.to_le_bytes()))
                                    }
                                    F64Const(ref x) => {
                                        ValueKind::F64(F64Bytes::from_bytes(x.bits.to_le_bytes()))
                                    }
                                    _ => unimplemented!(),
                                };
                                Value::new(value_kind)
                            })
                            .collect::<Vec<Value>>(),
                    ),
                    _ => unimplemented!(),
                };
                let expected_trap = match message {
                    "integer divide by zero" => ExecutionError::ZeroDivision,
                    "integer overflow" => ExecutionError::IntegerOverflow,
                    "out of bounds memory access" => ExecutionError::OutOfBoundsMemoryAccess,
                    "undefined element" => ExecutionError::UndefinedElement,
                    "indirect call type mismatch" => ExecutionError::IndirectCallTypeMismatch,
                    "invalid conversion to integer" => ExecutionError::InvalidConversionToInteger,
                    "unreachable" => ExecutionError::ExplicitTrap,
                    _ => unimplemented!(),
                };

                let funcaddr = ctx
                    .find_funcaddr(&Name::new(func_name.to_string()))
                    .unwrap();
                let res = invoke(&mut ctx, funcaddr, arguments).unwrap_err();
                println!("{}: trap = {:?}", func_name, res);
                assert_eq!(res, expected_trap);
                ctx.reset();
            }
            _ => (),
        }
    }
}

fn hostfunc_print_i32(args: Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
    assert_eq!(args.len(), 1);
    let n = match args[0].kind() {
        ValueKind::I32(n) => n,
        _ => panic!(),
    };
    println!("hostfunc_print_i32: {}", n);
    Ok(WasmRunnerResult::Values(vec![]))
}

fn hostfunc_print_f32(args: Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
    assert_eq!(args.len(), 1);
    let n = match args[0].kind() {
        ValueKind::F32(n) => n,
        _ => panic!(),
    };
    println!("hostfunc_print_f32: {}", n.to_f32());
    Ok(WasmRunnerResult::Values(vec![]))
}

fn hostfunc_print_f64(args: Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
    assert_eq!(args.len(), 1);
    let n = match args[0].kind() {
        ValueKind::F64(n) => n,
        _ => panic!(),
    };
    println!("hostfunc_print_f64: {}", n.to_f64());
    Ok(WasmRunnerResult::Values(vec![]))
}

fn hostfunc_print_i32_f32(args: Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
    assert_eq!(args.len(), 2);
    let (n0, n1) = match (args[0].kind(), args[1].kind()) {
        (ValueKind::I32(n0), ValueKind::F32(n1)) => (n0, n1),
        _ => panic!(),
    };
    println!("hostfunc_print_i32_f32: {}, {}", n0, n1.to_f32());
    Ok(WasmRunnerResult::Values(vec![]))
}

fn hostfunc_print_f64_f64(args: Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
    assert_eq!(args.len(), 2);
    let (n0, n1) = match (args[0].kind(), args[1].kind()) {
        (ValueKind::F64(n0), ValueKind::F64(n1)) => (n0, n1),
        _ => panic!(),
    };
    println!("hostfunc_print_f64_f64: {}, {}", n0.to_f64(), n1.to_f64());
    Ok(WasmRunnerResult::Values(vec![]))
}

fn register_spectest_hostfunc(ctx: &mut Context) {
    let modulename = Name::new("spectest".to_string());
    let targets: Vec<(
        _,
        fn(Vec<Value>) -> Result<WasmRunnerResult, ExecutionError>,
        _,
    )> = vec![
        (
            "print_i32",
            hostfunc_print_i32,
            (vec![Valtype::I32], vec![]),
        ),
        (
            "print_f32",
            hostfunc_print_f32,
            (vec![Valtype::F32], vec![]),
        ),
        (
            "print_f64",
            hostfunc_print_f64,
            (vec![Valtype::F64], vec![]),
        ),
        (
            "print_i32_f32",
            hostfunc_print_i32_f32,
            (vec![Valtype::I32, Valtype::F32], vec![]),
        ),
        (
            "print_f64_f64",
            hostfunc_print_f64_f64,
            (vec![Valtype::F64, Valtype::F64], vec![]),
        ),
    ];
    for (name, code, (param_type, return_type)) in targets {
        let hostfunc = Hostfunc::new(code);
        let functype = Functype::new(Resulttype::new(param_type), Resulttype::new(return_type));
        let funcaddr = ctx.register_hostfunc(functype, hostfunc).unwrap();
        ctx.register_content(
            Some(modulename.make_clone()),
            Name::new(name.to_string()),
            Extarnval::Func(funcaddr),
        );
    }
}
