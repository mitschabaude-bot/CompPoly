# Packed flat-basis additive encoder

The packed encoder implements the normalized novel-basis additive NTT on leanVM's polynomial-coordinate K field and cubic E extension. `FlatPlan` retains certified stage multipliers. Stages with fewer than eight block-index bits use prepared byte maps; other stages use the certified masked scalar product. Plans depend on domain logarithm, and can be reused across messages, lane counts and forward/inverse transforms. The physical codeword is a contiguous little-endian byte buffer, with eight bytes per K word and three consecutive K words per E element.

`AdditiveNTT.Packed.encodeRows` accepts row-major novel coefficients. `encodeInitial` accepts lane-major K columns, reverses the live lanes and puts absent lanes first; Rust rounds the physical initial width to a multiple of eight. A logical Merkle leaf's additional leading zeros belong to its framing adapter. `decodeRows` applies the ascending inverse stages and retains the first coset. It recovers novel coefficients. `monomialCoefficients` separately performs triangular monomial-to-novel conversion, with a reconstruction theorem; that generic polynomial conversion is suitable as a correctness reference rather than a production-size conversion kernel.

## Proof and execution checks

The flat basis independence theorem identifies raw `1 << i` words with `BF64.binaryBasisVector`. Each packed stage refines the generic array stage, then the generic function-backed `computableNTTStage`. The forward driver refines `computableAdditiveNTT`. The cubic-extension refinement proves that field embeddings preserve twiddles and scalar-linear coordinate projections commute with the generic encoder. Applying this to the ordered three E coordinates proves equality to the generic E encoder, in addition to the base-limb equality. Inverse butterflies cancel forward butterflies, disjoint stage sweeps preserve those equalities, and induction over stages proves inverse recovery at every coordinate. The first-coset decoding theorem recovers every input message word.

The linked native regression executable checks generic K/E encoders, reversed initial lanes and padding, inverse round trips in both orders, zero-domain, zero-stage, rate-zero and empty-lane cases, and monomial basis conversion. It uses the approved ByteArray accessors and adds no foreign arithmetic. Run:

```bash
systemd-run --user --scope -p MemoryMax=12G -- lake build
systemd-run --user --scope -p MemoryMax=12G -- lake test
systemd-run --user --scope -p MemoryMax=12G -- lake build CompPolyAdditiveSmoke
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

Conformance checks compare every small output byte, and stage/output digests plus word counts for larger arrays. The fixed inputs use raw words `0x0123456789abcdef XOR ((i+1)*0x9e3779b97f4a7c15)` with wrapping UInt64 arithmetic. The two-word diagnostic digest is FNV-style XOR/multiply together with an independent rotate/add accumulator; it is not a cryptographic hash. Small fixtures cover leading padding, a live count crossing the eight-lane boundary, differing rates, extension limb order and the no-stage case. K and E cases cover every domain logarithm 13–22, and all five production shapes are also checked stage by stage. The Lean checker additionally recovers the entire tiled input byte-for-byte with its inverse.

Measurements use three alternating Lean/Rust samples per shape, one worker pinned to CPU 5, native Rust CPU targeting, retained whole codewords and no hashing sink. Both include input transposition/tiling, allocation and all encoding stages in the timed phase. Plans and input messages are prepared before the begin marker. The phase ends before output digesting; the parent snapshots `instructions:u` and `cycles:u` between begin/end handshakes and rejects multiplexed counts. Nanoseconds come from each implementation's monotonic clock. Plan setup nanoseconds and whole-process peak RSS are reported separately; RSS includes runtime, plan, message and codeword memory, not an allocation counter. The process prepares a new plan for each sample and performs no discarded warmup. This measures one transform using a reusable plan, without amortizing construction into its phase time.

All runs hold `/tmp/compstark-bench.lock`, which serializes cooperating benchmarks but does not make this shared server idle. Recorded 1/5/15-minute load averages bound the wall-time claims. CPU/toolchain versions, binary SHA-256s, input shapes, output digests and individual samples are retained in the JSON lines. These are single-threaded encoder measurements; they do not include Merkle hashing or establish end-to-end prover performance.

## Recorded results, 2026-11-06

The [conformance records](bench-additive-ntt-conformance.jsonl) contain 31 passing cases: six exact-byte small fixtures, K and E at every domain logarithm 13–22, and all five production shapes. Every recorded stage and final digest agrees, and every Lean inverse recovers the tiled input exactly. The [performance records](bench-additive-ntt-performance.jsonl) retain all 30 samples and their five medians; both files identify the same binaries by SHA-256. The implementation passes the full library build, `lake test`, 11 linked native regressions, import/style/documentation checks and the axiom sweep (13,874 declarations, zero sorry taint and zero non-standard axiom taint).

The machine is an AMD Ryzen 7 3700X; Lean is v4.35.0 and Rust is 1.99.1. These are loaded-host single-worker observations, with the measurement procedure above. All output sinks match and all hardware samples have equal enabled/running counter time.

| Field / log domain / lanes / log rate | Lean seconds | Rust seconds | Time ratio | Lean instructions (billions) | Rust instructions (billions) | Instruction ratio |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| K / 22 / 56 / 1 | 220.042 | 4.512 | 48.8× | 2003.145 | 26.450 | 75.7× |
| E / 21 / 16 / 4 | 67.594 | 1.276 | 53.0× | 722.777 | 9.149 | 79.0× |
| E / 20 / 16 / 7 | 27.447 | 0.548 | 50.1× | 304.172 | 3.643 | 83.5× |
| E / 19 / 16 / 10 | 17.252 | 0.306 | 56.4× | 118.332 | 1.203 | 98.3× |
| E / 18 / 16 / 13 | 5.954 | 0.116 | 51.4× | 40.827 | 0.356 | 114.8× |

| Field / log domain | Lean plan seconds | Rust plan seconds | Lean peak RSS (GiB) | Rust peak RSS (GiB) | Codeword bytes (GiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| K / 22 | 9.494 | 0.000131 | 17.014 | 2.628 | 1.750 |
| E / 21 | 4.369 | 0.000106 | 7.026 | 0.799 | 0.750 |
| E / 20 | 2.083 | 0.000106 | 3.528 | 0.380 | 0.375 |
| E / 19 | 1.659 | 0.000142 | 1.801 | 0.190 | 0.188 |
| E / 18 | 0.826 | 0.000133 | 0.944 | 0.097 | 0.094 |

Boundary load averages ranged from 3.39–8.78 / 4.45–7.05 / 6.27–8.29 (1/5/15 minutes). Initial K wall samples were 264.3 s, 220.0 s, 210.9 s. Their instruction counts differ by less than 0.0001%; the wall variation does not change the large instruction gap. Plan setup is excluded from phase counters and phase seconds. Peak RSS covers the entire process, including setup and temporary allocation.

The encoder is not Rust-competitive: its instruction ratios are 75.7–114.8×, and it does not establish the survey's proposed comparable-speed goal. The packed allocator `BF64.Packed.zeros` materializes a boxed byte array before conversion to packed storage, contributing a large temporary memory cost. The compiled butterfly loops also retain Nat address arithmetic, shared-multiplier closure calls and the software masked products in later stages. These are concrete implementation costs; the measurements do not isolate their individual contributions. Prepared plans remove repeated setup across encodings, but do not remove the measured transform gap. No multithreaded or fused Merkle performance claim follows from these results.
