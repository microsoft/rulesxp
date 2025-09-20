use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use sexpr::{evaluator, parser};

fn main() {
    println!("Mini Scheme Interpreter v0.1.0");
    println!("Type expressions to evaluate them, or Ctrl+C to exit.");
    println!();

    let mut rl = DefaultEditor::new().unwrap();
    let mut env = evaluator::create_global_env();

    loop {
        match rl.readline("scheme> ") {
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
                    ":quit" | ":exit" => {
                        println!("Goodbye!");
                        break;
                    }
                    _ => {}
                }

                // Try to parse and evaluate the expression
                match parser::parse(line) {
                    Ok(expr) => match evaluator::eval(&expr, &mut env) {
                        Ok(result) => println!("{}", result),
                        Err(e) => println!("Error: {}", e),
                    },
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
    println!("Mini Scheme Interpreter Commands:");
    println!("  :help    - Show this help message");
    println!("  :env     - Show current environment bindings");
    println!("  :quit    - Exit the interpreter");
    println!("  :exit    - Exit the interpreter");
    println!();
    println!("Supported Scheme features:");
    println!("  Numbers: 42, 3.14, -5");
    println!("  Booleans: #t, #f");
    println!("  Strings: \"hello world\"");
    println!("  Lists: (1 2 3), (list 1 2 3)");
    println!("  Arithmetic: +, -, *, /");
    println!("  Comparison: =, <, >");
    println!("  List operations: car, cdr, cons, list, null?");
    println!("  Special forms: quote, define, if, lambda");
    println!();
    println!("Examples:");
    println!("  (+ 1 2 3)");
    println!("  (define x 42)");
    println!("  (if (> x 0) \"positive\" \"not positive\")");
    println!("  (define square (lambda (x) (* x x)))");
    println!("  (square 5)");
}

fn print_environment(_env: &sexpr::Environment) {
    println!("TODO: Print environment");
}
