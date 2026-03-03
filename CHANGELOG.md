# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## 0.3.1

### Added

- Code coverage reporting in CI with Codecov integration
- Maintainer's guide (`docs/MAINTAINERS-GUIDE.md`)
- README facelift

### Changed

- Release process switched to OIDC
- Improved CI pipeline performance with cached tool binaries
- Simplified dependabot configuration
- Fuzzing runs carry over corpus data between runs
- Dependency updates
- Check for cargo minimum dependency versions

### Fixed

- Code coverage improved from 93% to 97%

## 0.3.0

### Added

- Performance benchmarks in CI with criterion with regression detection

### Changed

- **Breaking:** Simplified project module hierarchy
- Benchmark uploads and comments restricted to main branch and PRs
- Clippy clean when not all features are enabled
- Updated dependencies

## 0.2.1

### Added

- Type-safe custom operations registration API (`register_builtin_operation`, `register_variadic_builtin_operation`)
- Iterator-based signatures for list and variadic "rest" parameters
- Project fuzzing support with cargo-fuzz for both S-expression and JSONLogic parsing/evaluation
- Daily fuzzing CI workflow
- Release binary packaging as zip/tar.gz
- Release version verification against git tag
- `.gitattributes` for standardized newline handling

### Changed

- Builtin functions migrated to new type-safe mechanics
- Eliminated `.expect()` calls by construction

### Fixed

- Disabled release tasks on forks

## 0.1.2

### Added

- Official JSONLogic.com conformance test suite
- GitHub CI pipeline
- Dependabot configuration

## 0.1.1

### Changed

- Added docs.rs metadata to build documentation with all features enabled

## 0.1.0

### Added

- Mini Scheme interpreter with integer-only arithmetic and strict typing/booleans
- JSONLogic interpreter with integer-only arithmetic, no nulls, and strict typing/booleans
- Precompiled operations, parse-time arity validation, and stack overflow guards
- Registration of new builtins.
- Sample REPL

