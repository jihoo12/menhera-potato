# menhera-potato

A small Rust project (library + CLI/binary).

## Overview

- Library code: `src/`
- Binary entrypoint: `src/main.rs`
- Tests: `tests/`
- Canonical specification: [spec/formal_system.md](spec/formal_system.md)
- Proof obligations: [spec/proof_obligations.md](spec/proof_obligations.md)
- Development instructions: [AGENTS.md](AGENTS.md)

## Development

New features follow **specification → soundness proof → implementation → validation**. Update the formal system and discharge the affected proof obligations before changing kernel behavior. The current implementation is an audited baseline, not a fully proved kernel.

## Build

```bash
cargo build --release
```

## Run

```bash
cargo run --release
```

## Test

```bash
cargo test
```

## License

See the `LICENSE` file in the repository root.