# Flat-basis additive encoder

The encoder implements the normalized novel-basis additive NTT on leanVM's polynomial-coordinate K field and cubic E extension. The bit-plane path stores each row as 64 `UInt64` planes, each carrying one bit of up to 64 K coordinates. Initial K rows use 56 coordinates; 16 E lanes use 48 coordinates in constant, linear, quadratic order. Physical rows are padded to 64 coordinates, independently of the logical output width. The output transpose restores little-endian row-major words without allocating another codeword.

`AdditiveNTT.Bitsliced.Plan.create` retains packed scalar twiddles and can be reused across messages and forward/inverse transforms. Each butterfly block builds the scalar's 64-by-64 binary matrix using 63 shift-reduce steps and one transpose. Every butterfly prepares sixteen groups of four-bit XOR combinations of its input planes in a reusable 2 KiB scratch buffer, then applies the matrix using sixteen lookups per output plane. No per-twiddle byte maps or multiplier closures are retained. Checked `USize` counters and addresses drive the row and stage sweeps. Native compilation disables loop and SLP vectorization for these kernels: Clang's vectorized scalar lookup expansion introduced unnecessary shuffles and repacking.

`Bitsliced.fromFn` fills and transposes each row directly into packed storage. `forward` and `inverse` operate on planes; `encode` and `decode` accept word rows and transpose at the boundaries. The Rust fixture adapter reverses live initial K lanes, places absent lanes first, tiles the message, and ignores the extra physical padding when digesting or dumping. Rust rounds initial logical width to a multiple of eight. Leading zeros belonging to a Merkle leaf's framing are outside this component. `BF64.Packed.zeros` uses `ByteArray.zeros` directly.

The word-oriented `AdditiveNTT.Packed` encoder remains the specification bridge. `encodeRows` accepts row-major novel coefficients; `encodeInitial` accepts lane-major K columns. `decodeRows` retains the first coset of the inverse. `monomialCoefficients` supplies a separate certified triangular conversion from monomial coefficients; this generic polynomial conversion is a correctness reference rather than a production-size kernel.

## Proof and execution checks

The six SWAR exchange passes are proved to transpose every bit. The register transpose is an involutive bijection, with an explicit equivalence; row materialization and output transposition have coordinate readback theorems. The block codec has a 512-byte round trip through `ByteCodec`.

`lane_applySpec` proves that each decoded matrix-product lane is multiplication by the shared field scalar. `applyScratch_eq_applySpec` certifies the four-bit lookup kernel. The native machine-address reads and writes refine the packed accessors, and their finite traversals refine the same disjoint row partition as the packed stage. `forwardStage_represents` and `inverseStage_represents` certify both stage directions; induction gives full-transform agreement and inverse recovery. `read_encode` and `read_decode` identify every materialized output word with the existing packed transform. That packed layer supplies the generic K encoder and cubic-extension coordinate refinement, including scalar embedding and ordered E limbs.

The linked bit-plane regression executable checks all 4096 transpose bits, multiplication by zero, one, two, the high bit and a seeded scalar, every stage count from zero to four against packed encoding, and inverse byte recovery. The packed regressions check generic K/E encoding, initial reversal and padding, both inverse orders, zero-domain, zero-stage, rate-zero and empty-lane cases, and monomial conversion. The implementations use approved ByteArray accessors and add no foreign arithmetic. Run:

```bash
systemd-run --user --scope -p MemoryMax=12G -- lake build
systemd-run --user --scope -p MemoryMax=12G -- lake test
systemd-run --user --scope -p MemoryMax=12G -- lake build CompPolyBitsliceSmoke CompPolyAdditiveSmoke
.lake/build/bin/CompPolyBitsliceSmoke
.lake/build/bin/CompPolyAdditiveSmoke
systemd-run --user --scope -p MemoryMax=12G -- lake exe axiomsweep --check
./scripts/check-imports.sh
./scripts/lint-style.sh
python3 scripts/check-docs-integrity.py
```

## Rust conformance and measurement

The reference is leanMultisig [`9d8bce818aa7c7e18e67026e522a9b1539d0a57d`](https://github.com/leanEthereum/leanMultisig/tree/9d8bce818aa7c7e18e67026e522a9b1539d0a57d). The build command makes a fresh temporary read-only source checkout, checks that tracked Rust sources remain unchanged and removes it on exit. The external harness calls Rust's public `AdditiveNttF64` production encoder with retained whole output and an empty row sink. Its scalar stage oracle uses Rust's own twiddles and F64 operations, and compares its full final array to the production encoder. It does not modify Rust arithmetic.

```bash
python3 scripts/bench-additive-ntt.py build
python3 scripts/bench-additive-ntt.py check > additive-conformance.jsonl
python3 scripts/bench-additive-ntt.py bench > additive-performance.jsonl
```

Conformance checks compare every small logical output byte, and stage/output digests plus word counts for larger arrays. The fixed inputs use raw words `0x0123456789abcdef XOR ((i+1)*0x9e3779b97f4a7c15)` with wrapping UInt64 arithmetic. The two-word diagnostic digest is FNV-style XOR/multiply together with an independent rotate/add accumulator; it is not a cryptographic hash. Small fixtures cover leading padding, a live count crossing the eight-lane boundary, differing rates, extension limb order and the no-stage case. K and E cases cover every domain logarithm 13–22, and all five production shapes are also checked stage by stage. The Lean checker additionally recovers the entire tiled input byte-for-byte with its inverse.

Measurements use three alternating Lean/Rust samples per shape, one worker pinned to CPU 5, native Rust CPU targeting, retained whole codewords and no hashing sink. Both include input transposition/tiling, allocation and all encoding stages in the timed phase. Lean materializes bit planes directly and transposes the final codeword back to words in place. Plans and input messages are prepared before the begin marker. The phase ends before output digesting; the parent snapshots `instructions:u` and `cycles:u` between begin/end handshakes and rejects multiplexed counts. Nanoseconds come from each implementation's monotonic clock. Plan setup nanoseconds and whole-process peak RSS are reported separately; RSS includes runtime, plan, message and codeword memory, not an allocation counter. The process prepares a new plan for each sample and performs no discarded warmup. This measures one transform using a reusable plan, without amortizing construction into its phase time.

All runs hold `/tmp/compstark-bench.lock`, which serializes cooperating benchmarks but does not make this shared server idle. Recorded 1/5/15-minute load averages bound the wall-time claims. CPU/toolchain versions, binary SHA-256s, input shapes, output digests and individual samples are retained in the JSON lines. These are single-threaded encoder measurements; they do not include Merkle hashing or establish end-to-end prover performance.

## Recorded bit-plane results, 2026-11-06

The [bit-plane conformance records](bench-additive-ntt-bitsliced-conformance.jsonl) contain 31 passing cases: six exact-byte small fixtures, K and E at every domain logarithm 13–22, and all five production shapes. Every stage and final digest agrees with Rust, and every Lean inverse recovers the complete padded input byte-for-byte. The [performance records](bench-additive-ntt-bitsliced-performance.jsonl) retain all 30 samples and five medians. Both files identify identical binaries by SHA-256. The full library build, `lake test`, linked bit-plane regressions, import/style/documentation checks and axiom sweep pass without warnings. The sweep covers 14,188 declarations across 541 modules, with zero sorry taint and zero non-standard axiom taint.

The machine is an AMD Ryzen 7 3700X; Lean is v4.35.0 and Rust is 1.99.1. These are loaded-host, single-worker medians. All output sinks match; all hardware samples have equal enabled/running counter time.

| Field / log domain / lanes / log rate | Lean seconds | Rust seconds | Time ratio | Lean instructions (billions) | Rust instructions (billions) | Instruction ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| K / 22 / 56 / 1 | 84.917 | 4.314 | 19.7× | 547.230 | 26.450 | 20.7× |
| E / 21 / 16 / 4 | 42.117 | 1.726 | 24.4× | 223.073 | 9.149 | 24.4× |
| E / 20 / 16 / 7 | 12.863 | 0.701 | 18.4× | 89.425 | 3.643 | 24.5× |
| E / 19 / 16 / 10 | 4.209 | 0.232 | 18.2× | 33.654 | 1.203 | 28.0× |
| E / 18 / 16 / 13 | 1.324 | 0.090 | 14.8× | 11.274 | 0.356 | 31.7× |

| Field / log domain | Lean plan seconds | Rust plan seconds | Lean peak RSS (GiB) | Rust peak RSS (GiB) | Physical / logical Lean codeword (GiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| K / 22 | 11.167 | 0.000130 | 2.976 | 2.628 | 2.000 / 1.750 |
| E / 21 | 7.030 | 0.000156 | 1.130 | 0.799 | 1.000 / 0.750 |
| E / 20 | 2.158 | 0.000152 | 0.573 | 0.380 | 0.500 / 0.375 |
| E / 19 | 1.001 | 0.000105 | 0.320 | 0.190 | 0.250 / 0.188 |
| E / 18 | 0.469 | 0.000099 | 0.195 | 0.097 | 0.125 / 0.094 |

Boundary load averages ranged from 5.54–8.82 / 7.51–11.10 / 9.31–11.34 (1/5/15 minutes). Phase seconds exclude plan and fixture generation, and end before output consumption. Peak RSS is the median of whole-process peaks. K/22 output RSS is 2.099 GiB; its 2.976 GiB peak includes overlap between the 2 GiB physical codeword and the 0.875 GiB original message during materialization, plus plan and runtime memory.

The [packed baseline records](bench-additive-ntt-performance.jsonl) use the same Rust binary. Instruction counts improve by 3.2–3.7× across these shapes. The initial K peak falls from 17.014 GiB to 2.976 GiB; the E/21 peak falls from 7.026 GiB to 1.130 GiB. Baseline wall seconds were measured under different host load, so the interleaved Rust comparisons above are the relevant wall-time ratios.

| Field / log domain | Packed Lean instructions (billions) | Bit-plane Lean instructions (billions) | Instruction reduction | Packed / bit-plane peak RSS (GiB) |
| --- | ---: | ---: | ---: | ---: |
| K / 22 | 2003.145 | 547.230 | 3.66× | 17.014 / 2.976 |
| E / 21 | 722.777 | 223.073 | 3.24× | 7.026 / 1.130 |
| E / 20 | 304.172 | 89.425 | 3.40× | 3.528 / 0.573 |
| E / 19 | 118.332 | 33.654 | 3.52× | 1.801 / 0.320 |
| E / 18 | 40.827 | 11.274 | 3.62× | 0.944 / 0.195 |

The measured instruction gap is 20.7–31.7× Rust, so the proposed 2–3× estimate is not achieved. The bit-plane implementation improves instruction counts and memory use while preserving the certified refinement chain; these results do not establish Rust-comparable encoder or prover speed.

## Performance limits

The register layout removes per-lane software multiplication from the stage sweep, but scratch preparation, matrix application, block construction and packed-buffer ownership checks still cost instructions. A short cycle profile during the log-22 inverse identified scratch preparation and dot products as the leading hot functions; it does not partition the complete forward benchmark. Native scratch preparation also contains lazy constant getters for computed offsets. Their individual contribution is not isolated by the production table.

The physical codeword uses 512 bytes per row: 64 K coordinates, including unused zero coordinates. Logical output widths remain 56 K words or 48 K words for the production E workloads. Whole-process peak RSS includes the runtime, plan, original input message, physical codeword and transient buffers. Instruction counts are the primary comparison on this loaded host; wall seconds do not establish quiet-host performance or end-to-end prover speed.
