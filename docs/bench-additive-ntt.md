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

## Recorded bit-plane baseline, 2026-11-06

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

The baseline instruction gap is 20.7–31.7× Rust, so these measurements do not achieve the proposed 2–3× estimate. The bit-plane implementation improves instruction counts and memory use while preserving the certified refinement chain; these results do not establish Rust-comparable encoder or prover speed.

## Performance limits

The register layout removes per-lane software multiplication from the stage sweep, but scratch preparation, matrix application, block construction and packed-buffer ownership checks still cost instructions. The counter-marked decomposition below isolates scratch preparation, application and row movement. Runtime group bases and literal slot displacements keep offset expressions out of lazy constant getters; dot products are inlined into the matrix application.

The physical codeword uses 512 bytes per row: 64 K coordinates, including unused zero coordinates. Logical output widths remain 56 K words or 48 K words for the production E workloads. Whole-process peak RSS includes the runtime, plan, original input message, physical codeword and transient buffers. Instruction counts are the primary comparison on this loaded host; wall seconds do not establish quiet-host performance or end-to-end prover speed.

## Butterfly instruction decomposition

The [baseline decomposition records](bench-additive-ntt-breakdown-before.jsonl) measure the kernel at `cd2f0b12c7146160cad556f46e95900602cb53ea`. Every substep is inside begin/end counter markers, using the same inherited counters, CPU 5, one worker and shared lock as the production sampler. Setup, plans, input construction and output consumption are outside these microbenchmark markers. Three samples are recorded for each part. Independent chains use 100,000 iterations; the empty Nat-loop floor uses 1,000,000. Actual and identity stage sweeps use ten repetitions over 65,536 rows, or 327,680 butterfly groups per sample. Application chains feed their output back as the next matrix masks, so they measure the fixed instruction path without table preparation inside the interval. Transpose and XOR chains retain their dependencies through separate generated functions. Counts include constructors, reference counting and calls belonging to each substep; these are instruction counts, not arithmetic-operation counts.

| Isolated substep | Baseline instructions/iteration | Interpretation |
| --- | ---: | --- |
| Empty chain | 11.01 | Nat loop, decrement, increment and termination |
| Matrix construction | 2,845.34 | 63 shift/reduce steps plus the matrix transpose |
| Transpose | 2,265.06 | One complete 64×64 transpose |
| Prepare four-bit input tables | 4,495.08 | Sixteen groups of sixteen combinations |
| Apply prepared tables | 4,094.51 | 64 output planes, sixteen lookups each |
| Butterfly XORs | 875.08 | Both 64-plane XORs |
| Complete register butterfly | 9,402.52 | Preparation, application, XORs and state ownership |
| Packed row movement | 1,231.52 | Two row loads and two row stores |

The baseline actual stage costs 13,371.59 instructions/group with a different matrix for every butterfly (`i = 0`), 10,519.78 with 256 butterflies/matrix (`i = 8`), and 10,508.68 with 32,768 butterflies/matrix (`i = 15`). Identity stages cost 1,323.75, 1,255.02 and 1,254.75 respectively. The identity kernel's unused matrix construction is absent from generated C. These stage measurements capture the real machine-index loops and packed ownership path, whereas adding isolated function chains changes allocation and fusion opportunities. The long-span identity stage minus the isolated movement chain is only 23.23 instructions/group; this comparison includes differences in ownership/fusion, but rules out a multi-thousand-instruction indexing loop. The raw movement and identity measurements are retained separately rather than labeling their sum as pure indexing overhead.

K/22/56/rate-1 has `ell = 21`: 44,040,192 butterfly groups and 4,194,302 matrix constructions. The 547,230,309,290-instruction production baseline therefore costs 12,425.70 instructions/group. Matrix construction amortizes to 269.94 after subtracting the 11-instruction chain floor; two boundary transposes per row amortize to 429.34. Weighting actual stage costs by their block counts gives approximately 10,781 instructions/group in the stages. The following reconciliation uses directly measured preparation/application/XOR chains and assigns their difference from the actual stage measurement to movement and control. It is not a claim that independently compiled microbenchmarks are exactly additive.

| K/22 baseline component | Instructions/butterfly group |
| --- | ---: |
| Matrix building, amortized | 270 |
| Input XOR-table preparation | 4,495 |
| Matrix application | 4,095 |
| Both XOR additions | 875 |
| Packed movement, indexing, stage control and fusion residual | ≈1,046 |
| Boundary transposes | 429 |
| Remaining materialization, boundary movement and phase residual | ≈1,215 |
| Complete timed phase | 12,426 |

### Generated C and selected change

The baseline `Scratch.c` contains 512 `lean_usize_once` calls and one `lean_uint32_once` call in `prepareScratch`, with 512 approved 32-bit writes. Thus filling 256 words also repeatedly checks 512 lazily initialized offset values. The stage's generated C calls `matrix` in the outer block loop, then loads two rows, prepares the input tables, applies the matrix, XORs and stores inside the span loop. Matrix preparation is already amortized over the block. The specialized inner fold takes `size_t` base, stride, bound and index arguments; its addresses use `lean_usize_shift_left` and `lean_usize_add`, with no Nat address conversion or multiplier-closure call inside the butterfly. There is no dense masked 64×64 application loop.

The retained path passes a runtime group index and four scalar plane arguments to `prepareChunk`. Its table writes use immediate displacements from that base, eliminating the 512 lazy offset getters. One lazy UInt32 zero-value getter remains per group; it is included in the counters. `dotScratch` is inlined into `applyScratch`, allowing the native compiler to share extraction constants across output planes. The generated machine code uses nibble extraction and indexed loads/XORs; the two approved UInt32 reads combine into a machine-word load. No arithmetic extern, inline C, compiler-trusted proof or table of field products is introduced.

The [table screening records](bench-additive-ntt-table-screen.jsonl) compare the runtime-base four-bit path before dot-product inlining against the byte experiment. Byte tables use eight groups of 256 words in 16 KiB. Gray-code traversal builds each group with 255 XORs; application uses eight lookups per output plane. The byte candidate passes 320 lane-product comparisons against masked field multiplication, but its preparation dominates:

| Candidate | Prepare instructions | Apply instructions | Sum |
| --- | ---: | ---: | ---: |
| Runtime-base four-bit, separate dot calls | 1,952 | 4,095 | 6,047 |
| Eight-bit Gray-code tables | 10,507 | 1,605 | 12,112 |
| Runtime-base four-bit, inlined dots | 1,952 | 3,358 | 5,310 |

The arithmetic model counts the 2,040 table-building XORs but omits materializing 2,048 table words. With the approved accessors, the generated byte-table preparation performs 4,096 UInt32 stores and splits nonzero words into low/high halves, in addition to address calculation, XORs, calls and register traffic. This explains why its roughly 2.6K abstract operations do not become 2.6K machine instructions. The complete byte multiplication chain costs 12,085 instructions, consistent with that sum after chain/fusion differences. The retained complete register butterfly costs 6,123 instructions, versus 9,403 at baseline. The [inlined decomposition records](bench-additive-ntt-breakdown-inline.jsonl) show actual stage costs of 10,091.59, 7,239.78 and 7,228.68 instructions/group for stages 0, 8 and 15: a reduction of 3,280 instructions/group. The byte experiment is confined to its benchmark executable; production has one certified four-bit path.

`fillChunk_packed` proves the literal-address writes equal the mathematical packed table. `Scratch.packed_prepare`, `lookup_prepare` and `applyScratch_eq_applySpec` then certify the application against the matrix definition, preserving the stage, packed-transform and generic-encoder chain. Matrix reuse cannot also reuse these prepared tables across different inputs: every table word is an XOR combination of the current input planes. Under the retained path, matrix building averages about 270 instructions/group and an identity stage costs about 1,255. Even eliminating all movement/control through tile fusion would save at most about 17% of a long-span stage; this bound overstates what fusion can remove. Two- or three-stage fusion is therefore not implemented in this change. The remaining instruction gap is primarily table construction/application and Lean object/buffer traffic.

Reproduce the microbenchmarks after building the runners:

```bash
systemd-run --user --scope -p MemoryMax=12G -- lake build CompPolyBitsliceBreakdown CompPolyBitsliceByteBench
.lake/build/bin/CompPolyBitsliceByteBench check combined 0
python3 scripts/bench-additive-ntt-breakdown.py stages .lake/build/bin/CompPolyBitsliceBreakdown
python3 scripts/bench-additive-ntt-breakdown.py byte .lake/build/bin/CompPolyBitsliceByteBench
```

Generated-C inspection uses `.lake/build/ir/CompPoly/Fields/Binary/AdditiveNTT/Bitsliced/Scratch.c`, `Stage.c` and `Native.c`. The specialized `forwardStage` inner fold contains the hot butterfly, while its enclosing fold contains the `matrix` call. `objdump -d --disassemble=lp_CompPoly_AdditiveNTT_Bitsliced_applyScratch .lake/build/bin/CompPolyBitsliceBreakdown` shows the compiled extraction and indexed-load sequence; `lp_CompPoly_AdditiveNTT_Bitsliced_prepareChunk___redArg` shows literal displacements and paired UInt32 stores.

### Runtime-base production results

The [conformance records](bench-additive-ntt-cost-fix-conformance.jsonl) contain all 31 passing cases, including six exact-byte fixtures, K/E at every logarithm 13–22 and all production shapes. Every recorded stage and final output agrees with pinned Rust, and the Lean inverse recovers the complete padded input. The [production records](bench-additive-ntt-cost-fix-performance.jsonl) retain three alternating Lean/Rust samples per shape, with matching sinks and no multiplexed counters. Their binary hashes match the conformance run. Full `lake build`, `lake test`, linked regressions, import/style/documentation checks and axiom sweep pass without warnings; the sweep covers 14,191 declarations in 541 modules with zero sorry or non-standard-axiom taint.

| Field / log domain / lanes / log rate | Lean instructions (billions) | Rust instructions (billions) | Instruction ratio | Lean seconds | Rust seconds | Lean peak RSS (GiB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| K / 22 / 56 / 1 | 402.779 | 26.450 | 15.23× | 52.812 | 6.294 | 2.973 |
| E / 21 / 16 / 4 | 164.604 | 9.149 | 17.99× | 16.639 | 1.308 | 1.137 |
| E / 20 / 16 / 7 | 67.069 | 3.643 | 18.41× | 8.588 | 0.549 | 0.579 |
| E / 19 / 16 / 10 | 25.915 | 1.203 | 21.54× | 3.663 | 0.277 | 0.326 |
| E / 18 / 16 / 13 | 9.124 | 0.356 | 25.66× | 0.874 | 0.082 | 0.198 |

| Field / log domain | Instruction reduction from bit-plane baseline | Lean plan seconds | Rust plan seconds | Rust peak RSS (GiB) |
| --- | ---: | ---: | ---: | ---: |
| K / 22 | 1.36× | 11.483 | 0.000171 | 2.628 |
| E / 21 | 1.36× | 4.365 | 0.000108 | 0.799 |
| E / 20 | 1.33× | 2.051 | 0.000146 | 0.380 |
| E / 19 | 1.30× | 1.451 | 0.000130 | 0.190 |
| E / 18 | 1.24× | 0.447 | 0.000089 | 0.097 |

Boundary load averages span 4.30–6.62 / 5.69–7.15 / 7.05–7.90 (1/5/15 minutes). These are loaded-host single-worker wall times; instruction reductions compare against the recorded bit-plane baseline, while wall-time comparisons use the interleaved Rust samples. Phase timing includes allocation and input/output layout conversion, excludes plan/message setup, and ends before digesting. Whole-process peak RSS includes plans, message, physical codeword and runtime memory. K/22 costs 9,146 instructions/butterfly group, versus 12,426 at baseline; its output RSS is 2.102 GiB. The retained path reduces instructions and preserves the memory bound, but the 2–3× Rust target remains unachieved.
