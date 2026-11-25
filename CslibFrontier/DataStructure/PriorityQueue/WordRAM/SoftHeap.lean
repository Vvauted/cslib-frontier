/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Params
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Program
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Model
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Defill
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Insert
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.ExtractMin
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Collect
public import CslibFrontier.DataStructure.PriorityQueue.WordRAM.SoftHeap.Standard

/-!
# Parametric Single-Heap Word-RAM Soft Heap

Unregistered single-heap Word-RAM soft-heap step following [Chazelle2000] and
[PettieRamachandran2002], Lemma 2.2. Supports `insert`, `extractMin`, and `collectCorrupted`
(without `meld` or arbitrary-handle `delete`) for arbitrary corruption rank threshold `r : ℕ` and
`rankThresholdForEps ε = Nat.log 2 (Nat.ceil (12 / ε)) + 1` (`0 < ε : ℚ`), exported both as
composable `Cslib.DataStructure.Memory.Prog` operations and as a standalone flat deterministic
width-blind `Cslib.WordRAM.Program .standard r` batch driver (`SoftHeap.Standard`).

## Cost model and scope

* **Composable `Memory.Prog` operations**: `allocPool`, `defill`, `shInsert`, `shExtractMin`, and
  `shCollectCorrupted` operate on caller-supplied bump-allocated pools (`SHHandle` with
  `rankThreshold`, `maxItems`, `maxNodes`), certifying `O(r + 1)` (`+ (240 * r + 520)`) amortized
  cost per insert, `O(1)` (`+ 250`) amortized cost per extract-min independently of `r`, and
  `≤ 8 * N` for corrupted-item collection alongside uniform `Realizes .exact` (`work := 0`)
  certificates.
* **Standalone `Program .standard r` driver**: `shBatchProg` hides `shFuelBound` and pool
  allocation internally and lowers via `exists_softHeap_standard_program` and
  `exists_softHeap_standard_program_eps` to a single fixed width-blind rand-free
  `Program .standard r` (`¬prog.ReadsWidth`, `prog.IsRandFree`) executing `N` insertions and `M`
  extract-mins from `State.init I.encode` under `Fits w I.wordBound` in
  `O(N * (r + 1) + M + 1)` (`O(N * (rankThresholdForEps ε + 1) + M + 1)`) native instructions with
  at most `12 * N / 2 ^ r` (`≤ ε * N`) surviving corrupted items.

## Main definitions

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.rankThresholdForEps`, `shFuelBound`:
  `ε`-derived corruption rank threshold and `shFuelBound r maxItems`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.targetSize`, `sizeCap`, `itemPhi`:
  parametric soft-heap rank parameters and exact closed-form item potential.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHHandle`, `SHExtractResult`, `SHInv`:
  handle, extraction result record, and full representation/amortized invariant.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.allocPool`, `defill`, `shInsert`,
  `shExtractMin`, `shCollectCorrupted`: memory-oracle Soft Heap operations with `Realizes .exact`
  certificates.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHOp`, `SHBatchInput`, `SHBatchResult`,
  `SHBatchExtract`, `SHBatchEntry`, `SHBatchTrace`, `shBatchProg`: flat batch I/O types, trace
  witness, and self-contained `Memory.Prog` driver.

## Main results

* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.corrupt_sum_bound`, `corrupt_sum_bound_eps`,
  `shInv_corrupted_le`, `shInv_corrupted_le_eps`: Chazelle's corruption bounds
  (`2 ^ r * #corrupted ≤ 12 * N` and rational `ε`-error specialization).
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.SHInv.origKey_le_ckey`: every surviving
  entry satisfies `origKey ≤ ckey`.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.realizes_allocPool`, `realizes_defill`,
  `realizes_shInsert`, `realizes_shExtractMin`, `realizes_shCollectCorrupted`,
  `realizes_shBatchProg`: uniform `Realizes .exact` native compilation certificates.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.allocPool_spec`, `shInit_inv`, `defill_spec`,
  `shInsert_spec`, `shExtractMin_spec`, `shCollectCorrupted_spec`, `shBatchProg_spec`: full
  correctness, permutation, key-monotonicity, pool framing, and amortized `memoryCost` specs.
* `Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.exists_softHeap_standard_program`,
  `exists_softHeap_standard_program_eps`: uniform width-blind rand-free `Program .standard r`
  lowered batch specifications.

## References

* [B. Chazelle, *The Soft Heap: An Approximate Priority Queue with Optimal Error Rate*,
  Journal of the ACM 47(6), 2000][Chazelle2000]
* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002], Lemma 2.2.
-/
