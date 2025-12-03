#![allow(clippy::unwrap_used)]

use criterion::{Criterion, black_box, criterion_group, criterion_main};
use rulesxp::{evaluator, jsonlogic, scheme};

const SCHEME_SIMPLE: &str = "(+ 1 2)";
const SCHEME_NESTED: &str = "(if (> (* 5 2) 8) (max 10 5 20) 0)";
const JSONLOGIC_SIMPLE: &str = r#"{"+":[1,2]}"#;
const JSONLOGIC_NESTED: &str = r#"{"if":[{">":[{"*":[5,2]},8]},{"max":[10,5,20]},0]}"#;

// Recursive Factorial (using inline self-application pattern)
const SCHEME_FACTORIAL: &str =
    "((lambda (f x) (f f x)) (lambda (self n) (if (<= n 1) 1 (* n (self self (- n 1))))) 10)";

fn bench_parsing(c: &mut Criterion) {
    let mut group = c.benchmark_group("Parsing");

    // Scheme Parsing
    group.bench_function("Scheme Simple", |b| {
        b.iter(|| scheme::parse_scheme(black_box(SCHEME_SIMPLE)))
    });

    group.bench_function("Scheme Nested", |b| {
        b.iter(|| scheme::parse_scheme(black_box(SCHEME_NESTED)))
    });

    group.bench_function("Scheme Factorial", |b| {
        b.iter(|| scheme::parse_scheme(black_box(SCHEME_FACTORIAL)))
    });

    // JSONLogic Parsing
    group.bench_function("JSONLogic Simple", |b| {
        b.iter(|| jsonlogic::parse_jsonlogic(black_box(JSONLOGIC_SIMPLE)))
    });

    group.bench_function("JSONLogic Nested", |b| {
        b.iter(|| jsonlogic::parse_jsonlogic(black_box(JSONLOGIC_NESTED)))
    });

    group.finish();
}

fn bench_evaluation(c: &mut Criterion) {
    let mut group = c.benchmark_group("Evaluation");

    let env = evaluator::create_global_env();
    let scheme_expr = scheme::parse_scheme(SCHEME_SIMPLE).unwrap();
    let json_expr = jsonlogic::parse_jsonlogic(JSONLOGIC_SIMPLE).unwrap();
    let scheme_nested = scheme::parse_scheme(SCHEME_NESTED).unwrap();
    let json_nested = jsonlogic::parse_jsonlogic(JSONLOGIC_NESTED).unwrap();
    let scheme_factorial = scheme::parse_scheme(SCHEME_FACTORIAL).unwrap();
    group.bench_function("Eval Scheme Simple", |b| {
        b.iter(|| evaluator::eval(black_box(&scheme_expr), &mut env.clone()))
    });

    group.bench_function("Eval JSONLogic Simple", |b| {
        b.iter(|| evaluator::eval(black_box(&json_expr), &mut env.clone()))
    });

    group.bench_function("Eval Scheme Nested", |b| {
        b.iter(|| evaluator::eval(black_box(&scheme_nested), &mut env.clone()))
    });

    group.bench_function("Eval JSONLogic Nested", |b| {
        b.iter(|| evaluator::eval(black_box(&json_nested), &mut env.clone()))
    });

    group.bench_function("Eval Scheme Factorial", |b| {
        b.iter(|| evaluator::eval(black_box(&scheme_factorial), &mut env.clone()))
    });

    group.finish();
}

criterion_group!(benches, bench_parsing, bench_evaluation);
criterion_main!(benches);
