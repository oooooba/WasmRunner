mod decoder;
mod executor;
mod instance;
mod instr;
mod module;
mod types;
mod validator;
mod value;

use std::env;
use std::fs;

use decoder::Decoder;
use executor::{instantiate, invoke, Context, ExecutionError};
use module::Name;
use validator::validate;
use value::{F32Bytes, F64Bytes, Value, ValueKind, WasmRunnerResult};

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
                instantiate(&mut ctx, &module).unwrap();
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
