use rulesxp::ast::Value;
use rulesxp::evaluator;
use rulesxp::jsonlogic::{ast_to_jsonlogic, parse_jsonlogic};
use rulesxp::scheme::parse_scheme;
use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;

fn main() {
    println!("RulesXP Multi-Language Rules Expression Evaluator");
    println!("Supports JSONLogic and Scheme with strict typing");
    println!("Enter S-expressions like: (+ 1 2)");
    println!("Enter JSONLogic like: {{\"and\": [true, {{\">\":[5,3]}}]}}");
    println!("Type :help for more commands, or Ctrl+C to exit.");
    println!();

    let mut rl = DefaultEditor::new().unwrap();
    let mut env = evaluator::create_global_env();
    let mut jsonlogic_mode = false;

    loop {
        match rl.readline("rulesxp> ") {
            Ok(line) => {
                let line = line.trim();
                if line.is_empty() {
                    continue;
                }

                // Add the line to history
                let _ = rl.add_history_entry(line);

                // Handle special commands
                match line {
                    ":help" => {
                        print_help();
                        continue;
                    }
                    ":env" => {
                        print_environment(&env);
                        continue;
                    }
                    ":jsonlogic" => {
                        jsonlogic_mode = !jsonlogic_mode;
                        if jsonlogic_mode {
                            println!("JSONLogic mode enabled:");
                            println!("  • Results shown as JSONLogic");
                            println!("  • Scheme inputs show JSONLogic translation (→)");
                        } else {
                            println!("Scheme mode enabled:");
                            println!("  • Results shown as S-expressions");
                            println!("  • JSONLogic inputs show Scheme translation (→)");
                        }
                        continue;
                    }
                    ":quit" | ":exit" => {
                        println!("Goodbye!");
                        break;
                    }
                    _ => {}
                }

                // Try to parse and evaluate the expression
                // First check if input looks like JSON (starts with { or [)
                let result =
                    if line.trim_start().starts_with('{') || line.trim_start().starts_with('[') {
                        // Try JSONLogic parsing
                        match parse_jsonlogic(line) {
                            Ok(expr) => {
                                // If in Scheme mode, show the parsed expression as Scheme
                                if !jsonlogic_mode {
                                    println!("→ {}", expr);
                                }
                                evaluator::eval(&expr, &mut env)
                            }
                            Err(e) => Err(e),
                        }
                    } else {
                        // Try Scheme parsing
                        match parse_scheme(line) {
                            Ok(expr) => {
                                // If in JSONLogic mode, show the parsed expression as JSONLogic
                                if jsonlogic_mode && let Ok(json_str) = ast_to_jsonlogic(&expr) {
                                    println!("→ {}", json_str);
                                } // Skip if conversion fails
                                evaluator::eval(&expr, &mut env)
                            }
                            Err(e) => Err(e),
                        }
                    };

                match result {
                    Ok(result) => {
                        // Don't print Unspecified values (e.g., from define)
                        if !matches!(result, Value::Unspecified) {
                            if jsonlogic_mode {
                                match ast_to_jsonlogic(&result) {
                                    Ok(json_str) => println!("{}", json_str),
                                    Err(_) => println!("{}", result), // Fallback to S-expression if conversion fails
                                }
                            } else {
                                println!("{}", result);
                            }
                        }
                    }
                    Err(e) => println!("Error: {}", e),
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("Interrupted. Use Ctrl+D or :quit to exit.");
            }
            Err(ReadlineError::Eof) => {
                println!("Goodbye!");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
}

fn print_help() {
    println!("Mini Scheme Interpreter with JSONLogic Support:");
    println!("  :help      - Show this help message");
    println!("  :env       - Show current environment bindings");
    println!("  :jsonlogic - Toggle JSONLogic output mode");
    println!(
        "               • Scheme mode: results as S-expressions, shows JSONLogic translation (→)"
    );
    println!("               • JSONLogic mode: results as JSONLogic, shows Scheme translation (→)");
    println!("  :quit      - Exit the interpreter");
    println!("  :exit      - Exit the interpreter");
    println!();
    println!("Supported languages:");
    println!("  S-expressions (Scheme): (+ 1 2), (and #t (> 5 3))");
    println!("  JSONLogic: {{\"and\": [true, {{\">\":[5,3]}}]}}");
    println!();
    println!("Supported operations (both languages):");
    println!("  Numbers: 42, -5");
    println!("  Booleans: #t/#f (Scheme) or true/false (JSON)");
    println!("  Arithmetic: +, -, *, /");
    println!("  Comparison: =, <, >, <=, >=, !=");
    println!("  Logic: and, or, not");
    println!("  Conditionals: if");
    println!("  Variables: var (JSONLogic)");
    println!();
    println!("Examples:");
    println!("  (+ 1 2 3)");
    println!("  {{\">\": [5, 3]}}");
    println!("  (and #t (> 5 3))");
    println!("  {{\"and\": [true, {{\">\":[5,3]}}]}}");
    println!();
}

fn print_environment(_env: &rulesxp::evaluator::Environment) {
    println!("TODO: Print environment");
}
