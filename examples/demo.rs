use rulesxp::evaluator;

#[cfg(feature = "jsonlogic")]
use rulesxp::jsonlogic::parse_jsonlogic;

#[cfg(feature = "scheme")]
use rulesxp::scheme::parse_scheme;

fn main() {
    println!("=== RulesXP: Dual-Language Scheme/JSONLogic Demo ===\n");

    let env = evaluator::create_global_env();

    // Test cases comparing equivalent expressions
    let test_cases = vec![
        // Basic arithmetic
        ("(+ 1 2 3)", r#"{"+":[1,2,3]}"#, "Addition"),
        ("(* 4 5)", r#"{"*":[4,5]}"#, "Multiplication"),
        // Comparison
        ("(> 5 3)", r#"{">":[5,3]}"#, "Greater than"),
        ("(= 4 4)", r#"{"==":[4,4]}"#, "Equality"),
        // Logic
        ("(and #t #t)", r#"{"and":[true,true]}"#, "Logical AND"),
        ("(or #f #t)", r#"{"or":[false,true]}"#, "Logical OR"),
        ("(not #f)", r#"{"!":[false]}"#, "Logical NOT"),
        // Nested expressions
        (
            "(and #t (> 5 3))",
            r#"{"and":[true,{">":[5,3]}]}"#,
            "Nested logic",
        ),
        (
            "(if (> 10 5) 42 0)",
            r#"{"if":[{">":[10,5]},42,0]}"#,
            "Conditional",
        ),
    ];

    for (scheme_expr, jsonlogic_expr, description) in test_cases {
        println!("--- {} ---", description);
        println!("Scheme:    {}", scheme_expr);
        println!("JSONLogic: {}", jsonlogic_expr);

        // Parse and evaluate Scheme
        let scheme_result = match parse_scheme(scheme_expr) {
            Ok(expr) => match evaluator::eval(&expr, &mut env.clone()) {
                Ok(result) => format!("{}", result),
                Err(e) => format!("Error: {}", e),
            },
            Err(e) => format!("Parse Error: {}", e),
        };

        // Parse and evaluate JSONLogic
        let jsonlogic_result = match parse_jsonlogic(jsonlogic_expr) {
            Ok(expr) => match evaluator::eval(&expr, &mut env.clone()) {
                Ok(result) => format!("{}", result),
                Err(e) => format!("Error: {}", e),
            },
            Err(e) => format!("Parse Error: {}", e),
        };

        println!("Result:    {} (both languages)", scheme_result);

        // Verify they match
        if scheme_result == jsonlogic_result {
            println!("✓ Results match!");
        } else {
            println!(
                "✗ Results differ: Scheme={}, JSONLogic={}",
                scheme_result, jsonlogic_result
            );
        }
        println!();
    }

    println!("=== Demo Complete ===");
}
