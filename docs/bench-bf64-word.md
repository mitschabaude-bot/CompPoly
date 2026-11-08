# Polynomial-basis BF64 word kernels

The word carrier preserves leanVM's polynomial basis and byte encoding. General masked multiplication approaches the Rust hardware path within about 3.3 times on K, while E multiplication remains about nine times slower. A prepared shared-scalar byte map reaches roughly 3.3 ns per product with a warm 16 KiB table; this is a different use pattern from arbitrary multiplication. The complete bitslice screening workload is substantially slower and is not a certified library implementation.

## Method

Measurements use an AMD Ryzen 7 3700X, Linux x86-64, Lean 4.35.0, logical CPU 5, and one Lean worker. `CompPolyBF64Bench` is compiled Lean with no new foreign interface. Packed storage uses CompPoly's existing 32-bit little-endian byte-array accessors. `scripts/bench-bf64.py` measures `instructions:u`, `cycles:u`, and monotonic wall time over three alternating rounds, rejecting multiplexed counters. The marked interval excludes module initialization, fixture construction, and prepared-map construction; separate rows include map construction plus one lookup product. Each result contributes to a printed sink. Raw samples and executable identity are recorded in [the JSONL evidence](bench-bf64-word.jsonl).

Dependent multiplication chains use the survey's inputs `0x0123456789abcdef` and `0xfedcba9876543210`. Throughput uses ten changing operands in the existing harness's unrolled chain. Unary chains XOR a fixed perturbation before each operation. The K Frobenius row performs eight squarings; the extension Frobenius rows compute the `2^64` power. Dot rows read two 64-element packed buffers and report cost per extension product, including reads and accumulation. The bitslice row performs 64 independent products including two input transposes and the output transpose; its preflight compares every lane against scalar multiplication.

The Rust reference is the leanVM survey's native x86 PCLMULQDQ measurement on this host: 5.511 ns for dependent K multiplication and 11.025 ns for dependent E multiplication. These reference times were not remeasured alongside this change. No Rust throughput, lookup-map, square, inverse, Frobenius, or dot timing is inferred from them. Wall time is descriptive on the shared host; instruction counts determine the algorithm ranking.

## Results

| Operation | Lean ns/op | Instructions/op | Rust ns/op |
|---|---:|---:|---:|
| K specification, dependent | 22862.983 | 247643.9 | 5.511 |
| K shift/XOR, dependent | 45.849 | 730.0 | 5.511 |
| K shift/XOR, independent | 45.423 | 721.9 | — |
| K prepared nibble map, dependent | 5.373 | 72.0 | — |
| K prepared byte map, dependent | 3.347 | 37.0 | — |
| K masked, dependent | 17.978 | 234.0 | 5.511 |
| K masked, independent | 17.071 | 264.8 | — |
| K bitslice, complete batch / product | 2313.579 | 37251.7 | — |
| K masked square | 7.977 | 89.0 | — |
| K masked Frobenius, eight squarings | 61.289 | 738.1 | — |
| K masked inverse | 678.005 | 8132.0 | — |
| E Karatsuba, dependent | 99.381 | 1516.0 | 11.025 |
| E × shared K scalar | 34.159 | 459.1 | — |
| E square | 16.309 | 266.1 | — |
| E Frobenius, 64 squarings | 1064.317 | 16445.3 | — |
| E Frobenius, coordinate formula | 1.183 | 27.0 | — |
| E unreduced packed dot, per product | 113.100 | 1798.9 | — |
| E reduced packed dot, per product | 102.457 | 1675.2 | — |
| Nibble map setup plus one product | 19331.308 | 310309.1 | — |
| Byte map setup plus one product | 158364.573 | 2474281.9 | — |

The one-, five-, and fifteen-minute load averages ranged over 2.02–2.11 / 3.43–3.47 / 4.85–4.87. Scalar/masked K multiplication retired 730/234 instructions per dependent product. Nibble/byte maps retired 72/37. The bitslice screening candidate retired 37,252 instructions per product and lost decisively. Deferred dot reduction retired 1,799 instructions per product, versus 1,675 for the reduced loop, a 7.4% increase.

Masked K dependent multiplication was 3.26× the survey's Rust time; specialized E multiplication was 9.01×. Against the contemporaneous specification row, masked K multiplication was 1272× faster by wall time and 1058× cheaper by instruction count. These ratios describe the measured kernels, not a whole prover.

At the measured setup instruction counts, nibble maps need about 1,916 uses and byte maps about 12,560 uses to amortize preparation against masked multiplication. Cache contention can move this crossover.

The standard harness additionally measures independently evolving E products over 64 seeds. Its small-preset medians are shown separately because the chain shape differs from the marked runner. [Raw harness records](bench-bf64-harness.jsonl) include sample distributions and matching specification checksums.

| Standard harness row | ns/op |
|---|---:|
| E Karatsuba, latency | 107.801 |
| E Karatsuba, throughput | 116.150 |

Five alternating A/B invocations against the frozen scalar-loop baseline classified both K scalar rows faster: latency ratio 0.735 and throughput ratio 0.717. The specification and harness rows were unchanged; there were zero slower, mismatched, missing, or suspect rows. This A/B result concerns the scalar machine-counter loop. The instruction counts above rank the alternative algorithms independently of shared-host wall-clock variation.

## Refinements and storage

| Kernel | Kernel-checked theorem |
|---|---|
| Scalar shift/XOR K product | `BF64.Word.toField_mul` |
| Masked integer K product | `BF64.Word.toField_mulMasked` |
| Scalar square, Frobenius, inverse | `BF64.Word.toField_square`, `toField_frobenius`, `toField_inv` |
| Masked square, Frobenius, inverse | `BF64.Word.toField_squareMasked`, `toField_frobeniusMasked`, `toField_invMasked` |
| Prepared maps | `BF64.Word.NibbleMap.toField_mul`, `BF64.Word.ByteMap.toField_mul` |
| E Karatsuba, K scalar product, square | `BF64.WordExt3.toField_mul`, `toField_mulScalar`, `toField_square` |
| E repeated squaring, base-field Frobenius | `BF64.WordExt3.toField_frobenius`, `toField_frobeniusK` |
| Unreduced packed E dot | `BF64.WordExt3.toField_dot` |
| Packed storage | `BF64.Packed.get_set`, `read_write`, `read_ofFn`; `BF64.WordExt3.read_ofFn` |

The refinement proofs use named arithmetic and coefficient lemmas. `Word` has `CanonicalNat` and `ByteCodec`; `WordExt3` and fixed-length `Packed.Buffer n` have `ByteCodec`. Round trips and encoding injectivity are available through the class interfaces. `Word.toBytes_toField` and `WordExt3.toBytes_toField` identify the specification encodings: eight little-endian bytes for K, three ordered K coefficients for E.

## Decisions and limits

The masked implementation uses three 32-bit carry-less products, each recovered from four interleaved coefficient streams and ordinary integer multiplication, followed by two shift/XOR reduction folds. It is the general K multiplication choice. Squaring exposes equal operands to the compiler, which shares the repeated streams. The extension uses six masked products for Karatsuba multiplication and three for a K scalar product. Its `2^64` Frobenius uses the identity `Y^(2^64) = Y²` to permute coordinates and XOR once.

The nibble and byte maps exchange setup and cache footprint for a short lookup chain. Preparation costs about 19 µs for a nibble map and 158 µs for a byte map in this run. These measurements cover one reused scalar and a hot table, not many competing twiddle tables or a full transform.

The unreduced dot kernel accumulates five double-width polynomial coefficients, folds `Y³ = Y + 1`, and performs only three final K reductions. Its packed fold nevertheless uses more instructions than accumulating individually reduced Karatsuba products. Both figures are retained in the report; deferred reduction alone does not establish a speedup in compiled Lean.

The direct bitslice screening candidate uses an array-backed schoolbook Boolean circuit. Including transposes, it is far slower than scalar masked products. Following the test/measure/prove loop, it is retained only under `bench/` as a reproducible rejected experiment, with differential checks and no library API or claimed refinement theorem. These numbers reject this circuit and layout; they do not establish a lower bound for optimized bitsliced circuits or already-transposed workloads.

The K shared-scalar use pattern is competitive with the Rust scalar reference after sufficient reuse. General K multiplication improves the boxed specification by orders of magnitude but retains a hardware carry-less-multiply gap. E multiplication and dots remain a material cost for a prover. These kernel measurements do not establish whole-prover competitiveness.

## Validation and reproduction

The arithmetic regression checks all 4,096 monomial pairs and 1,024 generated word pairs against the existing BF64 specification. Native smoke checks cover maps, packed reads/writes, unary arithmetic including zero inversion, E Frobenius, codecs, and dots of lengths 0, 1, 7, and 64. The harness cross-checks result digests between specification and word implementations. The instruction runner cross-checks scalar/masked/map sinks, scalar/masked unary sinks, reduced/unreduced dot sinks, and repeat stability.

```bash
systemd-run --user --scope -p MemoryMax=12G -- lake build
systemd-run --user --scope -p MemoryMax=12G -- lake test
systemd-run --user --scope -p MemoryMax=12G -- lake exe axiomsweep --check
systemd-run --user --scope -p MemoryMax=12G -- lake build CompPolyBF64Smoke CompPolyBF64Bench CompPolyBench
.lake/build/bin/CompPolyBF64Smoke
.lake/build/bin/CompPolyBench --validate-only --groups fields-bf64-mul,fields-bf64-masked,fields-bf64-fixed,fields-bf64-ext3
python3 scripts/bench-bf64.py > bench/out/bf64-counts.jsonl
```

The axiom sweep must report zero `sorryAx` and zero nonstandard-axiom taint. These software-baseline measurements use kernel-safe Lean arithmetic. The compiled CLMUL implementation, its native Rust comparison and its explicit extern trust assumption are documented in [the CLMUL comparison](bench-bf64-clmul.md). See [the benchmark guide](wiki/benchmarking.md) for the general harness and [the binary-field guide](wiki/binary-fields-and-ntt.md#polynomial-basis-word-kernels) for the public modules.
