# Maintainers Guide

## Issues and Pull Requests

Please triage incoming issues and review pull requests in a timely manner. Dependabot PRs,
community contributions, and bug reports all benefit from prompt attention — stale PRs discourage
contributors and stale issues accumulate. Aim to provide an initial response within a few business
days.

---

## Dependency Management

### Dependabot

[Dependabot](https://docs.github.com/en/code-security/dependabot) is configured in
[.github/dependabot.yml](../.github/dependabot.yml) to open pull requests **monthly** for:

- **Cargo dependencies** in `/` (the main crate)
- **Cargo dependencies** in `/fuzz` (the fuzz crate)
- **GitHub Actions** versions in workflows

PRs are labeled `dependencies` and prefixed with `deps` (or `ci` for Actions updates).

**Important limitation:** Dependabot only updates *direct* dependencies that have newer versions
available. It does **not** update transitive (indirect) dependencies in `Cargo.lock`. Over time the
lock file can drift, accumulating outdated transitive dependencies that Dependabot never touches.

Dependabot runs are typically fast (a few minutes) because it only checks the manifest files for
newer versions and opens PRs — it does not build or test the crate itself. The CI workflows
triggered by those PRs handle building and testing.

### Updating Dependencies Locally

To keep **all** dependencies current — including transitive ones that Dependabot misses —
periodically run the following locally.

#### 1. Update `Cargo.lock` (transitive dependencies)

```sh
cargo update
```

This resolves every dependency (direct and transitive) to the latest SemVer-compatible version and
rewrites `Cargo.lock`. It does **not** change version requirements in `Cargo.toml`, so it is always
safe to run. Review the diff, then build and test:

> **Note:** `Cargo.lock` is ignored by downstream consumers of a library crate — they resolve their
> own dependency versions. We check it in anyway so that our own example and test builds are
> deterministic. Keeping it fresh with `cargo update` is still valuable to ensure we're testing
> against current transitive dependencies. The version requirements in `Cargo.toml`, on the other
> hand, *are* inherited by callers and should be kept accurate.

```sh
cargo build --all-features --all-targets
cargo test --all-features --all-targets
cargo clippy --all-features --all-targets -- -D warnings
```

#### 2. Upgrade direct dependency versions (`Cargo.toml`)

For bumping the version *requirements* in `Cargo.toml` (e.g., `nom = "7.0"` → `nom = "8.0"`), use
[`cargo-edit`](https://github.com/killercup/cargo-edit):

```sh
# Install once
cargo install cargo-edit

# Interactively review and choose which direct dependencies to upgrade
cargo upgrade -i
```

> **Note:** Cargo itself is gaining a native `cargo update --breaking` command, but as of this
> writing it is still unstable and requires nightly
> (`cargo +nightly -Zunstable-options update --breaking`). Once stabilized, `cargo-edit` will no
> longer be needed.

`cargo upgrade -i` shows each available upgrade and lets you accept or skip it. After upgrading,
look for breakage:

```sh
cargo build --all-features --all-targets
cargo test --all-features --all-targets
cargo clippy --all-features --all-targets -- -D warnings
```

Fix any compilation errors or API changes before committing. Major-version bumps (e.g., `nom`
7.x → 8.x) are the most likely to require code changes. Before accepting an upgrade, check the
**CHANGELOG** or release notes of the updated crate, or review the commit history between the old
and new versions, to make a judgement call on how to adapt to upgrade-mandated changes and what
migration steps may be needed.

> **Note:** Always pass `--all-features --all-targets` to build, test, and clippy commands.
> `--all-features` enables optional features (e.g., `scheme`, `jsonlogic`) so that all code paths
> are compiled and checked. `--all-targets` includes examples, benchmarks, and tests — not just the
> library — ensuring nothing is missed.

#### Recommended workflow

1. `cargo update` — pick up all compatible transitive updates.
2. `cargo upgrade -i` — review and accept direct dependency bumps.
3. Build, test, and lint.
4. Commit `Cargo.toml` and `Cargo.lock` together.

---

## Publishing a New Version to crates.io

The crate is published automatically by the [release workflow](../.github/workflows/release.yml)
when a version tag is pushed. The workflow verifies that the tag matches the version in
`Cargo.toml`, publishes to crates.io, creates a GitHub Release, and uploads platform binaries.

### Step-by-step

1. **Decide the new version number.** Follow
   [Semantic Versioning (SemVer)](https://semver.org/) and Cargo's interpretation of it:

   **Pre-1.0** (current — `0.x.y`): the **minor** component signals breaking changes:
   - **Patch** (`0.3.0` → `0.3.1`) — backward-compatible bug fixes or internal changes.
   - **Minor** (`0.3.0` → `0.4.0`) — **breaking** API changes (or significant new
     functionality).

   **Post-1.0** (`≥ 1.0.0`): follows conventional SemVer:
   - **Patch** (`1.0.0` → `1.0.1`) — backward-compatible bug fixes.
   - **Minor** (`1.0.0` → `1.1.0`) — backward-compatible new functionality.
   - **Major** (`1.0.0` → `2.0.0`) — breaking API changes.

2. **Update `Cargo.toml`:**

   ```toml
   [package]
   version = "0.4.0"   # ← new version
   ```

3. **Commit and push to `main`:**

   ```sh
   git add Cargo.toml Cargo.lock
   git commit -m "release: v0.4.0"
   git push origin main
   ```

4. **Create and push an annotated tag:**

   ```sh
   git tag -a v0.4.0 -m "v0.4.0"
   git push origin v0.4.0
   ```

   The release workflow will:
   - Verify the tag version matches `Cargo.toml`.
   - Run `cargo publish --all-features --token $CRATES_IO_TOKEN`.
   - Create a GitHub Release with the tag.
   - Build and attach platform binaries (Linux x64, Windows x64, macOS ARM64).

5. **Verify** the release on [crates.io/crates/rulesxp](https://crates.io/crates/rulesxp) and
   the [GitHub Releases](https://github.com/microsoft/rulesxp/releases) page.

### Refreshing the crates.io Token

The release workflow authenticates to crates.io using the `CRATES_IO_TOKEN` repository secret.
Tokens expire or may need rotation; here is how to refresh it:

1. **Generate a new token** at <https://crates.io/settings/tokens>.
   - Give it a descriptive name (e.g., `rulesxp-github-actions`).
   - Scope it to `publish-update` for the `rulesxp` crate (if scoped tokens are available).

2. **Update the repository secret:**
   - Go to **Settings → Secrets and variables → Actions** in the
     [rulesxp repository](https://github.com/microsoft/rulesxp/settings/secrets/actions).
   - Edit the `CRATES_IO_TOKEN` secret and paste the new token value.

3. **Test** by triggering a release (or re-running a previous release workflow) to confirm the
   new token works.

> **Tip:** Set a calendar reminder to rotate the token before it expires. crates.io tokens
> currently have configurable expiration — choose a duration that balances security with
> convenience.
