mod decoder;
mod executor;
mod instance;
mod instr;
mod module;
mod types;
mod value;

use std::env;
use std::fs;

use decoder::Decoder;
use executor::{instantiate, invoke, ExecutionError};
use module::Name;
use value::{Value, ValueKind, WasmRunnerResult};

// test
use wast::parser::{self, ParseBuffer};
use wast::{AssertExpression, Instruction, Wast, WastDirective, WastExecute, WastInvoke};

fn main() {
    let base_dir_path = env::args().skip(1).next().expect("path to wast directory");
    run_test(&format!("{}/block.wast", base_dir_path));
    run_test(&format!("{}/loop.wast", base_dir_path));
    run_test(&format!("{}/br.wast", base_dir_path));
    run_test(&format!("{}/i32.wast", base_dir_path));
    run_test(&format!("{}/i64.wast", base_dir_path));
}

fn run_test(module_file_name: &str) {
    println!("[[test]] {}", module_file_name);
    let wast_text = fs::read_to_string(module_file_name).unwrap();
    let buf = ParseBuffer::new(&wast_text).unwrap();
    let wast_ast = parser::parse::<Wast>(&buf).unwrap();
    let mut current_module = None;
    let mut current_moduleinst = None;
    let mut current_context = None;
    for directive in wast_ast.directives {
        use WastDirective::*;
        match directive {
            Module(mut module) => {
                let mut reader = &module.encode().unwrap()[..];
                let mut decoder = Decoder::new(&mut reader);
                let module = decoder.run().expect("should success");
                let (moduleinst, ctx) = instantiate(&module).unwrap();
                current_module = Some(module);
                current_moduleinst = Some(moduleinst);
                current_context = Some(ctx);
            }
            AssertReturn { exec, results, .. } => {
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
                                    _ => unimplemented!(),
                                };
                                Value::new(value_kind)
                            })
                            .collect::<Vec<Value>>(),
                    ),
                    _ => unimplemented!(),
                };
                let expected_result = results
                    .into_iter()
                    .map(|res| {
                        use AssertExpression::*;
                        match res {
                            I32(x) => Value::new(ValueKind::I32(x as u32)),
                            I64(x) => Value::new(ValueKind::I64(x as u64)),
                            _ => unimplemented!(),
                        }
                    })
                    .collect::<Vec<Value>>();

                let moduleinst = current_moduleinst.as_ref().unwrap();
                let ctx = current_context.as_mut().unwrap();
                let funcaddr = moduleinst
                    .find_funcaddr(&Name::new(func_name.to_string()))
                    .unwrap();
                let res = invoke(ctx, funcaddr, arguments).unwrap();
                println!("{}: result = {:?}", func_name, res);
                assert_eq!(res, WasmRunnerResult::Values(expected_result));
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
                    _ => unimplemented!(),
                };

                let moduleinst = current_moduleinst.as_ref().unwrap();
                let ctx = current_context.as_mut().unwrap();
                let funcaddr = moduleinst
                    .find_funcaddr(&Name::new(func_name.to_string()))
                    .unwrap();
                let res = invoke(ctx, funcaddr, arguments).unwrap_err();
                println!("{}: trap = {:?}", func_name, res);
                assert_eq!(res, expected_trap);

                // recreate module instance and context
                let (new_moduleinst, new_context) =
                    instantiate(current_module.as_ref().unwrap()).unwrap();
                current_moduleinst = Some(new_moduleinst);
                current_context = Some(new_context);
            }
            _ => (),
        }
    }
}
