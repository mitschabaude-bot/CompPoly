# BF64 carry-less multiplication

The x86-64 measurements in [the raw samples](bench-bf64-clmul.jsonl) compare the frozen pure-Lean executable at `f2fab06`, the CLMUL implementation at `c1e783e`, and unchanged leanMultisig primitives at `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`. Rust uses `-C target-cpu=native`; Lean C uses `-march=native`. Three alternating rounds run single-threaded on CPU 5 of the Ryzen 7 3700X under the shared benchmark lock. Setup is excluded, dependent chains retain their output, and every cross-language sink agrees. Counts are medians of user instructions per operation. The host load was 67–70, so cycles and elapsed times in the raw samples are diagnostic.

| Kernel | Lean software | Lean CLMUL | Native Rust | Software / Rust | CLMUL / Rust |
|---|---:|---:|---:|---:|---:|
| K multiply, dependent | 234.01 | 17.01 | 9.00 | 25.99× | 1.89× |
| K multiply, throughput | 264.81 | 5.76 | 8.33 | 31.80× | 0.69× |
| E multiply | 1,516.01 | 81.01 | 53.00 | 28.60× | 1.53× |
| E × K | 459.09 | 48.10 | 41.02 | 11.19× | 1.17× |
| K square | 89.01 | 18.01 | 20.00 | 4.45× | 0.90× |
| K inverse | 8,131.98 | 1,217.94 | 747.20 | 10.88× | 1.63× |
| K Frobenius, eight squares | 738.08 | 167.08 | 139.02 | 5.31× | 1.20× |
| E square | 266.10 | 50.08 | 58.02 | 4.59× | 0.86× |
| E q-Frobenius | 27.01 | 27.01 | 9.00 | 3.00× | 3.00× |
| Deferred E dot, per product | 1,798.97 | 385.41 | 36.71 | 49.01× | 10.50× |
| Reduced E dot, per product | 1,675.19 | 249.24 | 66.25 | 25.28× | 3.76× |

The paired low/high calls compile to one live PCLMUL for each full product. The sparse base-field reduction uses the same three-product fold as Rust. Cubic multiplication combines six unreduced products before three reductions. Packed dot products retain unreduced accumulators until the end. The deferred packed dot remains above the five-times target: generated C retains general `Nat` address arithmetic and list traversal around its six carry-less products. The throughput test permits compiler scheduling across independent lanes; its ratio is specific to that workload.

The [A/B evidence](bench-bf64-clmul-ab.json) retains the raw suite samples and comparison text. Deferred cubic multiplication has throughput ratio 0.852 with stable controls and no suspect rows. CLMUL map construction has nibble/byte ratios 0.373/0.408 with stable controls and no suspect rows. The hardware reduction iteration improves dependent/throughput multiplication by 0.617/0.778, although that run's throughput control drift exceeded 10%. The initial primitive throughput improvement triggered the harness's below-0.1 suspect threshold; disassembly, live dependencies and the matched native counter run establish that the large improvement is real. These loaded-host timings do not replace the reference-machine best-time tables.

High-reuse additive-NTT twiddles retain their byte tables. Switching the prepared multiplier globally to direct CLMUL did not earn a faster verdict at medium or large size. Table construction uses the proved CLMUL factory; the existing direct masked multiplier also compiles through CLMUL. An unboxed-list dot-loop experiment did not earn a faster verdict and is excluded.

The kernel-safe refinement theorems retain pure Lean bodies for both primitive halves. The compiled smoke executable checks 8,273 pairs against an independent shift/XOR reference, reduction, cubic arithmetic, maps and packed storage. `lake build`, `lake test`, both BF64 and additive smoke executables, and `lake exe axiomsweep --check` pass; the sweep reports zero sorry-tainted or nonstandard-axiom-tainted declarations. AArch64's PMULL statement expression was cross-compiled but has not been executed on ARM. See the [compiled-code trust contract](wiki/serialization.md).

Reproduce with `python3 scripts/bench-bf64-native.py FROZEN_SOFTWARE_BINARY`. The driver builds Lean inside a 12 GiB systemd scope and builds its Rust harness against a clean checkout of the pinned source before taking counters.

## Scalar deferred-dot accumulation

[Three alternating native-counter runs](bench-bf64-scalar-dot.jsonl) compare the CLMUL baseline `50601b6`, the scalar machine-offset dot, and pinned native Rust `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`. Counts exclude setup and every sink agrees. The raw `software` engine key names the pre-change CLMUL executable in this record.

| Kernel | Lean before instructions/product | Lean scalar instructions/product | Native Rust instructions/product | Scalar / Rust |
| --- | ---: | ---: | ---: | ---: |
| K dependent multiply | 17.01 | 17.01 | 9.00 | 1.89× |
| K independent multiply | 5.76 | 5.76 | 8.33 | 0.69× |
| E multiply | 81.01 | 81.01 | 53.00 | 1.53× |
| K/E multiply | 48.09 | 48.10 | 41.02 | 1.17× |
| K square | 18.01 | 18.01 | 20.00 | 0.90× |
| K inverse | 1,217.94 | 1,217.94 | 747.20 | 1.63× |
| K Frobenius | 167.12 | 167.08 | 139.02 | 1.20× |
| E square | 50.09 | 50.09 | 58.02 | 0.86× |
| E q-Frobenius | 27.01 | 27.01 | 9.00 | 3.00× |
| E deferred dot | 385.41 | 64.61 | 36.70 | 1.76× |
| E reduced dot | 249.24 | 249.24 | 66.25 | 3.76× |

The packed dot passes ten `UInt64` accumulator arguments and a `USize` loop index. The generated C contains scalar updates and machine-offset loads, with one result allocation after the loop; no accumulator record or natural-number address arithmetic is allocated per product. `dot_code` proves equality for every buffer length, including empty buffers and lengths outside the native machine range. The [five-round A/B records](bench-bf64-scalar-dot-ab.json) give the deferred dot a 0.237 candidate/baseline ratio with matching digests and no suspect rows. Compiled smoke tests, group validation, the complete test library and the axiom sweep pass. Host load makes wall-time comparisons unsuitable.
