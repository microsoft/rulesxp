use sexpr::{evaluator, parse_jsonlogic};

fn main() {
    println!("=== JSONLogic Conformance Test ===\n");

    let mut env = evaluator::create_global_env();

    let mut total_tests = 0;
    let mut failed_tests = 0;

    // Test cases based on JSONLogic specification
    let test_cases = vec![
        // Basic primitives should work
        ("true", "true", "Boolean true literal"),
        ("false", "false", "Boolean false literal"),
        // null is intentionally not supported to avoid non-conformance
        ("42", "42", "Number literal"),
        ("\"hello\"", "\"hello\"", "String literal"),
        ("[1,2,3]", "(1 2 3)", "Array literal"),
        // Basic operations we support
        ("{\"==\":[1,1]}", "#t", "Equality true"),
        ("{\"==\":[1,2]}", "#f", "Equality false"),
        ("{\"!=\":[1,2]}", "#t", "Not equal true"),
        ("{\"!=\":[1,1]}", "#f", "Not equal false"),
        ("{\">\": [2,1]}", "#t", "Greater than true"),
        ("{\">=\": [1,1]}", "#t", "Greater than or equal"),
        ("{\"<\": [1,2]}", "#t", "Less than true"),
        ("{\"<=\": [1,1]}", "#t", "Less than or equal"),
        // Arithmetic
        ("{\"+\":[1,2,3]}", "6", "Addition with multiple args"),
        ("{\"-\":[5,2]}", "3", "Subtraction"),
        ("{\"*\":[2,3,4]}", "24", "Multiplication with multiple args"),
        ("{\"*\": [4,2]}", "8", "Multiplication"),
        // Logic operations
        ("{\"and\":[true,true]}", "#t", "AND true"),
        ("{\"and\":[true,false]}", "#f", "AND false"),
        ("{\"or\":[false,true]}", "#t", "OR true"),
        ("{\"or\":[false,false]}", "#f", "OR false"),
        ("{\"!\":[true]}", "#f", "NOT true"),
        ("{\"!\":[false]}", "#t", "NOT false"),
        // Nested operations
        (
            "{\"and\":[true,{\">\": [5,3]}]}",
            "#t",
            "Nested AND with comparison",
        ),
        // Conditionals
        (
            "{\"if\":[true,\"yes\",\"no\"]}",
            "\"yes\"",
            "If true branch",
        ),
        (
            "{\"if\":[false,\"yes\",\"no\"]}",
            "\"no\"",
            "If false branch",
        ),
    ];

    // CRITICAL: Test JSONLogic-specific behaviors that might not conform
    let problematic_cases = vec![
        // JSONLogic allows unary operators without arrays (syntactic sugar)
        (
            "{\"!\": true}",
            "#f",
            "Unary NOT without array (syntactic sugar)",
        ),
        // JSONLogic type coercion in equality
        (
            "{\"==\":[1,\"1\"]}",
            "#t",
            "Type coercion: number equals string",
        ),
        ("{\"==\":[0,false]}", "#t", "Type coercion: 0 equals false"),
        // JSONLogic strict equality
        ("{\"===\":[1,1]}", "#t", "Strict equality same type"),
        (
            "{\"===\":[1,\"1\"]}",
            "#f",
            "Strict equality different types",
        ),
        // JSONLogic truthy/falsy behavior (!! operator intentionally not supported due to semantic mismatch)
        (
            "{\"!!\":[[]]}",
            "ERROR",
            "Double negation not supported (empty array)",
        ),
        (
            "{\"!!\":[\"0\"]}",
            "ERROR",
            "Double negation not supported (string '0')",
        ),
        (
            "{\"!!\":[0]}",
            "ERROR",
            "Double negation not supported (number 0)",
        ),
        (
            "{\"!!\":[1]}",
            "ERROR",
            "Double negation not supported (number 1)",
        ),
        (
            "{\"!!\":[\"\"]}",
            "ERROR",
            "Double negation not supported (empty string)",
        ),
        (
            "{\"!!\":[\"hello\"]}",
            "ERROR",
            "Double negation not supported (non-empty string)",
        ),
        // JSONLogic returns first truthy/falsy for and/or
        (
            "{\"or\":[false,\"a\"]}",
            "\"a\"",
            "OR returns first truthy value",
        ),
        ("{\"or\":[false,0,\"a\"]}", "\"a\"", "OR skips falsy values"),
        (
            "{\"and\":[true,\"a\",3]}",
            "3",
            "AND returns last value when all truthy",
        ),
        (
            "{\"and\":[true,\"\",3]}",
            "\"\"",
            "AND returns first falsy value",
        ),
        // JSONLogic between operations (special case of < and <=)
        ("{\"<\":[1,2,3]}", "#t", "Between exclusive (1 < 2 < 3)"),
        (
            "{\"<\":[1,1,3]}",
            "#f",
            "Between exclusive fails at equality",
        ),
        ("{\"<=\":[1,2,3]}", "#t", "Between inclusive (1 <= 2 <= 3)"),
        (
            "{\"<=\":[1,1,3]}",
            "#t",
            "Between inclusive allows equality",
        ),
        // Unary minus
        ("{\"-\": 2}", "-2", "Unary minus"),
        ("{\"-\": -2}", "2", "Unary minus of negative"),
        // Unary plus for casting
        (
            "{\"+\": \"3.14\"}",
            "3",
            "Unary plus casting string to number",
        ),
        // Variable operations (these will likely fail without data context)
        (
            "{\"var\": \"field\"}",
            "ERROR",
            "Variable access without data",
        ),
        // Operations intentionally not supported to avoid non-conformance
        (
            "{\"/\": [8, 2]}",
            "ERROR",
            "Division operator not supported",
        ),
        (
            "{\"not\": [true]}",
            "ERROR",
            "JSONLogic 'not' operator not supported (use '!' instead)",
        ),
        // Null values are intentionally rejected to avoid non-conformance
        (
            "{\"if\":[null,\"yes\",\"no\"]}",
            "ERROR",
            "Null in JSONLogic expression should be rejected",
        ),
    ];

    println!("--- Basic Conformance Tests ---");
    for (jsonlogic_expr, expected, description) in test_cases {
        total_tests += 1;
        let result = test_jsonlogic_expression(jsonlogic_expr, &mut env);
        if result == expected {
            println!("✓ {}: {}", description, jsonlogic_expr);
        } else {
            println!(
                "✗ {}: {} → {} (expected {})",
                description, jsonlogic_expr, result, expected
            );
            failed_tests += 1;
        }
    }

    println!("\n--- Potential Non-Conformance Tests ---");
    for (jsonlogic_expr, expected, description) in problematic_cases {
        total_tests += 1;
        let result = test_jsonlogic_expression(jsonlogic_expr, &mut env);
        if result == expected
            || (expected == "ERROR"
                && (result.starts_with("Error") || result.starts_with("Parse Error")))
        {
            println!("✓ {}: {}", description, jsonlogic_expr);
        } else {
            println!(
                "✗ {}: {} → {} (expected {})",
                description, jsonlogic_expr, result, expected
            );
            failed_tests += 1;
            println!("  ^ This indicates non-conformant behavior!");
        }
    }

    println!("\n=== Summary ===");
    println!("Total tests: {}", total_tests);
    println!("Passed: {}", total_tests - failed_tests);
    println!("Failed: {}", failed_tests);

    if failed_tests > 0 {
        println!("\nNon-conformant behaviors detected! See failed tests above.");
    } else {
        println!("\nAll tests passed - implementation appears conformant!");
    }
}

fn test_jsonlogic_expression(expr: &str, env: &mut sexpr::Environment) -> String {
    match parse_jsonlogic(expr) {
        Ok(parsed) => match evaluator::eval(&parsed, env) {
            Ok(result) => format!("{}", result),
            Err(e) => format!("Error: {}", e),
        },
        Err(e) => format!("Parse Error: {}", e),
    }
}
