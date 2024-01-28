#!/bin/sh
# cargo install cargo-pgo
cargo pgo build && ./target/x86_64-unknown-linux-gnu/release/weld >/dev/null && cargo pgo optimize
