# Additive NTT function comparison

The structural reference is native leanMultisig `9d8bce818aa7c7e18e67026e522a9b1539d0a57d`, with `-C target-cpu=native`, on the Ryzen 7 3700X. Its `ntt/plan.rs` divides the transform into gathered far layers and contiguous deep layers. `ntt/layers.rs` fuses two or three layers per sweep through the radix-4 and radix-8 schedules in `ntt/kernels.rs`. `merkle.rs` consumes completed deep blocks through `RowSink`, hashes batches of leaves, and climbs cache-resident subtrees.

## Measured function map

Callgrind 3.22.0 counts user instructions in the existing matched additive-NTT harnesses, with one worker. The K workload has domain logarithm 14, 56 live lanes and log inverse rate 1. Both sinks are `6161288611265212461:15484524747797890496`. Collection is toggled at the encoder entry and ends at its return; plan construction, message construction and the output digest are outside the interval. Inclusive counts overlap and must not be added. Callgrind elapsed times on the heavily loaded host are not performance measurements.

The Lean executable is the retained `302359f6011bcab03ae4a76e363cef63b876a68f` bit-plane harness, SHA-256 `268aff921d4872545075459a30c1a42f1772399a0c0157b0f634e6121fc0682a`. Its bit-plane modules and harness source are byte-identical to `50601b6`; CLMUL does not change their arithmetic. The Rust executable SHA-256 is `46f424e98a61ae0321fcb481c5ff23b46507e63408c7b0f1e92f5cd15754120a`. These counts describe the retained encoder implementations, independently of the prover's dependency pins.

| Operation | Lean function | Rust function | Lean M instructions | Rust M instructions | Lean / Rust |
| --- | --- | --- | ---: | ---: | ---: |
| Complete encoding, including tiling and boundary materialization | harness `encode` | `AdditiveNttF64::encode_lane_major` | 1,097.447 | 68.165 | 16.10× |
| All transform layers | `Bitsliced.stageSweep` outer folds | `AdditiveNttF64::run_layers` | 820.481 | 58.576 | 14.01× |
| Butterfly arithmetic | `prepareScratch` and `applyScratch`, plus plane XORs | `butterfly_lanes` | see decomposition | 54.088 | different layout |
| Initial lane materialization | specialized `Bitsliced.fromFn` | fused into first `GatheredPass::run` | 229.348 | fused | different layout |
| Final row materialization | `Bitsliced.transposeRows` | word rows already materialized | 46.537 | no separate pass | different layout |
| Gathered far-layer pass, including its butterflies | no corresponding pass | `GatheredPass::run` task | no corresponding pass | 18.191 | different algorithm |
| Contiguous deep pass, including its butterflies | no corresponding pass | `DeepPass::in_place` task | no corresponding pass | 49.972 | different algorithm |

The Rust gathered and deep passes sum to 68.163 M instructions, almost the complete encode. The Lean stage sweeps, input materialization and output transpose sum to 1,096.366 M, almost its complete encode. The dominant differences are the butterfly representation and the input/output work. A gathered or deep pass cannot be assigned a Lean/Rust ratio before Lean implements that pass.

On this CPU Rust's multiplication uses scalar PCLMUL instructions, while the four-lane kernel uses AVX2 XORs and vector reduction. Native Rust therefore remains the denominator; a scalar Rust oracle is only a correctness check.

The [raw function records](bench-ntt-port-before.json) retain inclusive function counts and both complete output sinks. The E workload, with domain logarithm 14, 16 cubic-extension lanes and log inverse rate 4, costs 869.501 M Lean instructions versus 53.482 M native Rust instructions (16.26×). Its layer sweeps cost 641.931 M versus 40.110 M (16.00×). Rust uses a message-fed deep pass for this shape.

## Production phase baseline

The matched complete-prover hardware-counter medians at leanvm-security `a211ede`, CompPoly `50601b6`, and CompStark `2b79a572` are recorded in leanvm-security's `docs/prover-clmul.json`. Each run produces the complete Rust-identical proof and passes the certified byte verifier. These are production SET and Fibonacci fixtures, distinct from the matched encoder workload above.

| Fixture | Phase | Lean M instructions | Native Rust M instructions | Lean / Rust |
| --- | --- | ---: | ---: | ---: |
| SET | Initial commitment | 3,552.023 | 155.399 | 22.86× |
| SET | Extension commitments, summed | 2,045.848 | 101.020 | 20.25× |
| Fibonacci | Initial commitment | 3,622.974 | 155.464 | 23.30× |
| Fibonacci | Extension commitments, summed | 2,048.376 | 101.020 | 20.28× |

The initial phase includes plan setup and Merkle construction. The extension row sums every commitment within PCS opening. These counts do not establish multi-thread scaling or performance on the larger aggregation fixture.
