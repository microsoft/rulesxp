// serde-json needs this set to be able to parse the huge JSONLogic official test list
#![recursion_limit = "1024"]
#![cfg(feature = "jsonlogic")]
#![expect(clippy::unwrap_used)] // test code OK

use rulesxp::evaluator;
use rulesxp::jsonlogic::{ast_to_jsonlogic, parse_jsonlogic};
use std::collections::HashMap;

#[test]
fn test_jsonlogic_conformance() {
    // Complete JSONLogic conformance test suite from https://jsonlogic.com/tests.json
    // Augmented with categorized non-conformance reasons where applicable
    //
    // (Note: File is stored as txt to bypass automatic reformatting of JSON so this file
    //        can cleanly diff in case of upstream additions)
    //
    // TEST FORMAT:
    // [rule, data, expected] - Original test case, fully supported
    // [rule, data, expected, "reason"] - Explicitly marked failure with reason
    //
    // CONFORMANCE CATEGORIES:
    // OK - Fully supported operations (3-column format, no explicit status needed)
    // BYDESIGN - Intentionally not supported (design choices - these operations FAIL by design):
    //   BYDESIGN-LITERAL-NULL: We reject null values for safety, and to avoid exposing Scheme nil/empty list semantics to JavaScript
    //   BYDESIGN-LITERAL-FLOAT: We only support integers, not floating point - our language has no numeric tower, only i64
    //   BYDESIGN-OPERATOR-TERNARY: We use 'if' instead of '?:' ternary operator - this operator is not documented in the official documentation!
    //   BYDESIGN-OPERATOR-DIVISION: Division and modulo operations (/, %) - since we are integer only, this makes limited sense
    //   BYDESIGN-COERCION: Type coercion behavior - we enforce strict typing - behaviors here are giant footguns, differ between languages, and between JSONLogic and JavaScript
    //   BYDESIGN-TRUTHINESS: Truthy/falsy behavior including double-negation (!!) - we require explicit booleans
    //   BYDESIGN-IF-CHAINED: Complex chained if conditions not supported - Scheme does not support this
    //   BYDESIGN-IF-MINIMAL: If without else clause not supported - Scheme does not support this, the value of this operation would possibly leak nulls into the system
    // NOTIMPL - Not yet implemented (could be added in the future - these operations FAIL for now):
    //   NOTIMPL-OPERATOR-STRING-*: String operations with specific suffixes (IN, SUBSTR)
    //   NOTIMPL-OPERATOR-LIST-*: List operations with specific suffixes (MAP, FILTER, REDUCE, ALL, NONE, SOME, MERGE)
    //   NOTIMPL-DATA-CONTEXT: Variable access operations (var, missing) & data context required
    let official_tests_json_str = include_str!("tests.txt");
    let official_tests_json: serde_json::Value =
        serde_json::from_str(official_tests_json_str).expect("Failed to parse tests.json");
    let official_tests = official_tests_json
        .as_array()
        .expect("Expected tests.json to contain an array");

    let mut stats: HashMap<&str, (usize, usize)> = HashMap::new(); // (total, passed)
    let mut failures = Vec::new();
    let mut test_number = 0;

    for test in official_tests {
        match test {
            // Skip comment/section header strings
            serde_json::Value::String(_comment) => {
                continue;
            }
            // Process test arrays: [rule, data, expected] (OK) or [rule, data, expected, reason] (failure)
            serde_json::Value::Array(test_array) => {
                let (rule, _data, expected, status) = match &test_array[..] {
                    // 3-element array: [rule, data, expected] - OK
                    [rule, data, expected] => (rule, data, expected, "OK"),
                    // 4-element array: [rule, data, expected, reason] - explicit failure reason
                    [rule, data, expected, status_value] => {
                        (rule, data, expected, status_value.as_str().unwrap())
                    }
                    _ => panic!(
                        "Expected 3-element (OK) or 4-element (reason) test array, got: {test_array:?}"
                    ),
                };

                test_number += 1;
                let status_key = status.split('-').next().unwrap_or(status);

                let rule_str = serde_json::to_string(rule).unwrap();
                let expected_str = serde_json::to_string(expected).unwrap();

                let entry = stats.entry(status_key).or_insert((0, 0)); // (total, passed)
                entry.0 += 1;

                println!("Running test #{test_number}: {rule_str} (expect {status})");

                let result = parse_jsonlogic(&rule_str)
                    .and_then(|parsed| {
                        evaluator::eval(&parsed, &mut evaluator::create_global_env())
                    })
                    .and_then(|result| ast_to_jsonlogic(&result));

                let (actual_status, passed) = match (status_key, &result) {
                    ("OK", Ok(result_str)) if result_str == &expected_str => ("OK", true),
                    ("OK", Ok(result_str)) => {
                        failures.push(format!(
                            "Test #{test_number}: {rule_str} - Expected OK with {expected_str}, got {result_str}"
                        ));
                        ("FAIL", false)
                    }
                    ("OK", Err(e)) => {
                        failures.push(format!(
                            "Test #{test_number}: {rule_str} - Expected OK, got error: {e}"
                        ));
                        ("FAIL", false)
                    }
                    ("BYDESIGN" | "NOTIMPL", Err(_)) => (status_key, true),
                    ("BYDESIGN" | "NOTIMPL", Ok(result_str)) => {
                        failures.push(format!(
                            "Test #{test_number}: {rule_str} - Expected {status_key}, got OK with {result_str}"
                        ));
                        ("FAIL", false)
                    }
                    _ => panic!("Unknown status: {status_key}"),
                };

                if passed {
                    entry.1 += 1;
                }

                if actual_status == "FAIL" {
                    println!("Test #{test_number}: Expected {status_key}, got {actual_status}");
                }
            }
            // Error: unexpected test data format
            invalid => {
                panic!(
                    "Expected string (comment) or 3/4-element test case array, got: {invalid:?}"
                );
            }
        }
    }

    let total_tests: usize = stats.values().map(|(total, _)| total).sum();
    println!("\nTest Results ({total_tests} total):");

    for (status, &(category_total, passed)) in &stats {
        let pct_of_total = 100.0 * category_total as f64 / total_tests as f64;
        println!("  {status}: {passed}/{category_total} ({pct_of_total:.1}% of total)");
    }

    if !failures.is_empty() {
        println!("\nFailures:");
        for failure in &failures {
            println!("  {failure}");
        }
    }

    assert!(
        failures.is_empty(),
        "Found {} test failures",
        failures.len()
    );
    println!("\nAll tests passed!");
}
