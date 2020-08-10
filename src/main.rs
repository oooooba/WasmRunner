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
use executor::{instantiate, invoke};
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
}

fn run_test(module_file_name: &str) {
    println!("[[test]] {}", module_file_name);
    let wast_text = fs::read_to_string(module_file_name).unwrap();
    let buf = ParseBuffer::new(&wast_text).unwrap();
    let wast_ast = parser::parse::<Wast>(&buf).unwrap();
    let mut current_module = None;
    for directive in wast_ast.directives {
        use WastDirective::*;
        match directive {
            Module(mut module) => {
                let mut reader = &module.encode().unwrap()[..];
                let mut decoder = Decoder::new(&mut reader);
                let module = decoder.run().expect("should success");
                current_module = Some(module);
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

                let module = current_module.as_ref().unwrap();
                let (moduleinst, mut ctx) = instantiate(module).unwrap();
                let funcaddr = moduleinst
                    .find_funcaddr(&Name::new(func_name.to_string()))
                    .unwrap();
                let res = invoke(&mut ctx, funcaddr, arguments).unwrap();
                println!("{}: result = {:?}", func_name, res);
                assert_eq!(res, WasmRunnerResult::Values(expected_result));
            }
            _ => (),
        }
    }
}
