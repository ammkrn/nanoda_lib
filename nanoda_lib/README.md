
There are three examples; `basic` just runs the type checker, `stdout` prints the export contents to standard out, and `to_file` takes an absolute path and records the information there. Right now it's set to panic in the event of an IO error, but user implementations of the `IsTracer` trait can change that behavior. 
LTO is curently enabled since that seems to have a larger impact on performance than usual, but you can disable it in Cargo.toml to reduce compile-times.

```
cargo run --release --example basic <path-to-lean-export>

cargo run --release --example stdout <path-to-lean-export>

cargo run --release --example to_file <path-to-lean-export> -o <path-to-logfile>
```

The grammar is split between `grammar.txt` and `step_grammar.txt` since the latter is machine-generated.

See the comment above `trace::mod::IsTracer` for notes on user-defined
implementations of `IsTracer`.

