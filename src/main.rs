use std::env;
use std::fs;

use wasm_runner::decoder::Decoder;
use wasm_runner::executor::{instantiate, invoke, Context, ExecutionError};
use wasm_runner::instance::{Extarnval, Hostfunc, Moduleinst};
use wasm_runner::module::Name;
use wasm_runner::types::{
    Elemtype, Functype, Globaltype, Limit, Memtype, Mutability, Resulttype, Tabletype, Valtype,
};
use wasm_runner::validator::validate;
use wasm_runner::value::{F32Bytes, F64Bytes, Value, ValueKind, WasmRunnerResult};

// test
use wast::parser::{self, ParseBuffer};
use wast::{
    AssertExpression, Expression, Id, Instruction, Module, NanPattern, Wast, WastDirective,
    WastExecute, WastInvoke,
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
    module: Option<Id<'a>>,
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
    let module_name = module.map(|id| Name::new(id.name().to_string()));
    let content_name = Name::new(name.to_string());
    let funcaddr = ctx
        .find_funcaddr(module_name.as_ref(), &content_name)
        .unwrap();
    invoke(ctx, funcaddr, arguments)
}

fn run_instantiate_action<'a>(
    ctx: &mut Context,
    module: &mut Module<'a>,
) -> Result<Moduleinst, ExecutionError> {
    let name = module.id.map(|id| Name::new(id.name().to_string()));
    let mut reader = &module.encode().unwrap()[..];
    let mut decoder = Decoder::new(&mut reader);
    let mut module = decoder.run().expect("should success");
    if let Some(name) = name {
        module.set_name(name);
    }
    validate(&module).unwrap();
    instantiate(ctx, &module)
}

fn run_test(wast_file_path: &str) {
    println!("[[test]] {}", wast_file_path);
    let wast_text = fs::read_to_string(wast_file_path).unwrap();
    let buf = ParseBuffer::new(&wast_text).unwrap();
    let wast_ast = parser::parse::<Wast>(&buf).unwrap();
    let mut ctx = Context::new();
    register_spectest_hostfunc(&mut ctx);
    register_spectest_global(&mut ctx);
    register_spectest_table(&mut ctx);
    register_spectest_mem(&mut ctx);
    let mut last_moduleinst = None;
    for directive in wast_ast.directives {
        use WastDirective::*;
        match directive {
            Module(mut module) => {
                let moduleinst = run_instantiate_action(&mut ctx, &mut module).unwrap();
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
            Invoke(WastInvoke {
                name, args, module, ..
            }) => {
                run_invoke_ation(&mut ctx, module, name, args).unwrap();
            }
            AssertReturn { exec, results, .. } => {
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

                let (func_name, res) = match exec {
                    WastExecute::Invoke(WastInvoke {
                        module, name, args, ..
                    }) => {
                        let (func_name, arguments) = (name, args);

                        let WasmRunnerResult::Values(res) =
                            run_invoke_ation(&mut ctx, module, func_name, arguments).unwrap();
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
                        (func_name, res)
                    }
                    WastExecute::Get { module, global } => {
                        let module_name = module.map(|id| Name::new(id.name().to_string()));
                        let content_name = Name::new(global.to_string());
                        (
                            "get",
                            vec![ctx
                                .load_global(module_name.as_ref(), &content_name)
                                .unwrap()],
                        )
                    }
                    _ => unimplemented!(),
                };

                println!("{}: result = {:?}", func_name, res);
                assert_eq!(res, expected_result);
            }
            AssertTrap { exec, message, .. } => {
                let (func_name, result_err) = match exec {
                    WastExecute::Invoke(WastInvoke {
                        module, name, args, ..
                    }) => {
                        let func_name = name;
                        let arguments = args
                            .into_iter()
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
                            .collect::<Vec<Value>>();
                        let module_name = module.map(|id| Name::new(id.name().to_string()));
                        let funcaddr = ctx
                            .find_funcaddr(module_name.as_ref(), &Name::new(func_name.to_string()))
                            .unwrap();
                        (
                            func_name,
                            invoke(&mut ctx, funcaddr, arguments).unwrap_err(),
                        )
                    }
                    WastExecute::Module(mut module) => (
                        "trap_module",
                        run_instantiate_action(&mut ctx, &mut module).unwrap_err(),
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
                    "uninitialized element" => ExecutionError::UninitializedElement,
                    _ => unimplemented!(),
                };

                println!("{}: trap = {:?}", func_name, result_err);
                assert_eq!(result_err, expected_trap);
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

fn hostfunc_print(args: Vec<Value>) -> Result<WasmRunnerResult, ExecutionError> {
    assert_eq!(args.len(), 0);
    println!("hostfunc_print:");
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
        ("print", hostfunc_print, (vec![], vec![])),
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

fn register_spectest_global(ctx: &mut Context) {
    let modulename = Name::new("spectest".to_string());
    let targets = vec![
        ("global_i32", ValueKind::I32(666), Mutability::Var),
        (
            "global_f32",
            ValueKind::F32(F32Bytes::new(666.6)),
            Mutability::Var,
        ),
        (
            "global_f64",
            ValueKind::F64(F64Bytes::new(666.6)),
            Mutability::Var,
        ),
    ];
    for (name, valuekind, mutability) in targets {
        let val = Value::new(valuekind);
        let globaltype = Globaltype::new(val.typ(), mutability);
        let globaladdr = ctx.register_global(&globaltype, val).unwrap();
        ctx.register_content(
            Some(modulename.make_clone()),
            Name::new(name.to_string()),
            Extarnval::Global(globaladdr),
        );
    }
}

fn register_spectest_table(ctx: &mut Context) {
    let modulename = Name::new("spectest".to_string());
    let targets = vec![("table", Limit::new(10, Some(20)), Elemtype::Funcref)];
    for (name, limit, elemtype) in targets {
        let tabletype = Tabletype::new(limit, elemtype);
        let tableaddr = ctx.register_table(&tabletype).unwrap();
        ctx.register_content(
            Some(modulename.make_clone()),
            Name::new(name.to_string()),
            Extarnval::Table(tableaddr),
        );
    }
}

fn register_spectest_mem(ctx: &mut Context) {
    let modulename = Name::new("spectest".to_string());
    let targets = vec![("memory", Limit::new(1, Some(2)))];
    for (name, limit) in targets {
        let memtype = Memtype::new(limit);
        let memaddr = ctx.register_mem(&memtype).unwrap();
        ctx.register_content(
            Some(modulename.make_clone()),
            Name::new(name.to_string()),
            Extarnval::Mem(memaddr),
        );
    }
}
