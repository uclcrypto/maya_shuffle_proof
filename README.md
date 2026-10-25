# MAYA: A Short Shuffle Argument With Fast Verification

> **Research code.** This is a research prototypeonly -- for benchmarking and experimentation. Not audited, no correctness or security guarantees. Do NOT use in production or any deployed system.

This repository contains a Rust implementation of the MAYA shuffle argument, a shuffle argument with
`O(log n)` proof size and fast verification. Two curve instantiations are
provided: MAYA-Ristretto on curve25519-dalek (Ristretto255) and MAYA-P256 on
arkworks (NIST P-256).  The repository accompanies the MAYA paper accepted at CCS ’26.

- Paper: MAYA, ACM CCS 2026. Full version: <https://eprint.iacr.org/2026/941>
- Verifier-oriented specification and further material:
  <https://thaodoanvan.github.io/maya_website/>
- Archived artifact, with the full evaluation instructions and the Verificatum
  baseline scripts: <https://doi.org/10.5281/zenodo.22647683>



## Requirements

- **Hardware**: x86-64 CPU, minimum 8 GB RAM (16 GB is recommended)
- **Software**: Rust >= 1.81 (install via [rustup](https://rustup.rs))


## Repository structure

```
maya_ristretto/              # Primary instantiation (Ristretto255, curve25519-dalek)
  src/                       # Library source
  tests/                     # Integration tests
  benches/r1cs.rs            # Benchmark: prover and verifier timing
  docs/                      # Notes inherited from Bulletproofs                   
maya_p256/                   # Secondary instantiation (NIST P-256, arkworks)
  src/                       # Library source
  tests/  
  benches/r1cs.rs            # Benchmark: prover and verifier timing                        
LICENSE-MIT
README.md                      
```


## Quick start

```bash
cd maya_ristretto
cargo build --release --features yoloproofs,parallel
QUICK=1 RUSTFLAGS='-C target_cpu=native' \
  cargo bench --bench r1cs --features yoloproofs,parallel
```

**Notes**

- First benchmark run may take some minutes due to dependency compilation.
- Benchmark timings are more stable after the initial build.
- For stable numbers, run while plugged in and avoid background load.


## Tests

```bash
cd maya_ristretto && cargo test --release --features yoloproofs
cd ../maya_p256   && cargo test --release --features yoloproofs
```

## Reproducing Paper Results


### Tables 1 and 2 - Prover and Verifier Performance

Single-threaded:
```bash
cd maya_ristretto
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
```

Multi-threaded:
```bash
cd maya_ristretto
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel
```

For each of the 8 configurations (N in {10^3, 10^4, 10^5, 10^6}, k in {2, 4}), the output
shows a per-phase breakdown followed by totals. A summary table is printed at the end.

### Figure 3 - Sweet Spot Analysis

```bash
cd maya_ristretto
BENCH_FOLDING=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
```

Runs proof generation across k in {2, 3, 4, 5, 6, 8, 16} for N in {10^3,...,10^6}.
A table of normalized times (relative to k=2) is printed at the end.


### Tables 8-11 - MAYA-P256 (Appendices O, P)

```bash
cd maya_p256
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,asm          # single-threaded
RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel,asm  # multi-threaded
```

### Table 12 - Padding Comparison (Appendix R)

Iterative padding (default):
```bash
cd maya_ristretto
BENCH_PADDING=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
```

Global padding:
```bash
cd maya_ristretto
BENCH_PADDING=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,global_padding
```

### Multi-run averaging

An alternative averaging benchmark measures the complete prover and verifier pipelines over multiple runs, reporting the mean and standard deviation for each configuration.

The benchmarks used for Tables 1-2 above rely on Criterion's built-in averaging. Both approaches produce similar results. Criterion provides a more detailed per-phase timing breakdown, while  the multi-run averaging benchmark reports a single end-to-end runtime.

```bash
cd maya_ristretto
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel
```

```bash
cd maya_p256
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,asm
BENCH_FULL_AVG=1 RUSTFLAGS='-C target_cpu=native' cargo bench --bench r1cs --features yoloproofs,parallel,asm
```

Default is 10 runs/config to keep runtime manageable. Override with NUM_RUNS=100.


## Result Mapping

| Paper Results | Section | Command |
| --- | --- | --- |
| Prover (Single-Threaded) | Table 1 | `cargo bench --bench r1cs --features yoloproofs` |
| Prover (Multi-Threaded) | Table 1 | `cargo bench --bench r1cs --features yoloproofs,parallel` |
| Verifier (Single-Threaded) | Table 2 | Same as Table 1 (Single-Threaded) |
| Verifier (Multi-Threaded) | Table 2 | Same as Table 1 (Multi-Threaded) |
| Proof size | Section 4.3.3 | Any run with `N=10^6`, `k=4` |
| Sweet spot | Figure 3 | `BENCH_FOLDING=1 cargo bench ...` |
| Padding strategies | Table 12 | `BENCH_PADDING=1 cargo bench ...` |
| MAYA-P256 | Tables 8–11 | `cd maya_p256 && cargo bench ...` |
| Full averaging | Tables 1–2 | `BENCH_FULL_AVG=1 cargo bench ...` |


## Interpreting Results

The numbers in the paper were measured on an Intel Core i5-1245U (12 threads, 4.4 GHz), 16 GB RAM,
Ubuntu 22.04, rustc 1.88.0.


## License

MAYA is developed by the UCLouvain Crypto Group and released under the
MIT License (see `LICENSE-MIT`). It extends the Bulletproofs library of
dalek-cryptography, distributed under the MIT License,
Copyright (c) 2018 Chain, Inc.; this notice is kept in `LICENSE-MIT`.
