#![no_main]

use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = std::str::from_utf8(data) {
        if let Ok(parsed) = rulesxp::scheme::parse_scheme(s) {
            let _ = rulesxp::evaluator::eval(&parsed, &mut rulesxp::evaluator::create_global_env());
        }
    }
});
