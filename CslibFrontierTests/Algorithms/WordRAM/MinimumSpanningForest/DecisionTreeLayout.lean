/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for DecisionTree.Layout and DecisionTree.PrecompKruskal)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompKruskal

/-!
# Tests for Word-RAM Decision-Tree Layouts and Kruskal Precomputation

Exercises `dtThreshold`, `dtPrecompCost`, `dtGraphMask`, `walkCompleteTree_eval`,
`skelToTree_isComplete`, and the `*_spec` / `realizes_*` interfaces of `dtFillAllPairsProg`,
`dtFillPowProg`, `dtDecodeMaskProg`, and `dtKruskalMaskProg` under `module` encapsulation,
including `numV = 0` / `len = 0` / `e = 0` empty-graph boundary witnesses.
-/

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreeLayout

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## `DecisionTree.Layout`: Threshold, Bitmask, and Complete-Tree Evaluation -/

-- Threshold lower/cost bounds and `dtGraphMask` bit/bound properties on a 3-vertex triangle.
example :
    1 ≤ dtThreshold 0 ∧
    dtPrecompCost (dtThreshold 128) ≤ 128 ∧
    (let es : List (Fin 3 × Fin 3) :=
      [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)]
     dtGraphMask es < 2 ^ Nat.choose 3 2 ∧
     (dtGraphMask es).testBit (edgePairIdx 1 2) = true) := by
  refine ⟨dtThreshold_ge_one 0, dtPrecompCost_dtThreshold_le (by decide), ?_⟩
  let es : List (Fin 3 × Fin 3) :=
    [(⟨0, by decide⟩, ⟨1, by decide⟩), (⟨1, by decide⟩, ⟨2, by decide⟩)]
  refine ⟨dtGraphMask_lt es (fun e he => by
    simp only [es, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide), ?_⟩
  rw [dtGraphMask_testBit, decide_eq_true_iff]
  exact ⟨(⟨1, by decide⟩, ⟨2, by decide⟩), by simp, rfl⟩

-- `skelToTree_isComplete` and `walkCompleteTree_eval` on a depth-1 tree over `2` edges.
example (p : Equiv.Perm (Fin 2)) (cmp : Fin 2 → Fin 2 → Bool)
    (hcmp : ∀ a b : Fin 2, cmp a b = true ↔ (p a).val < (p b).val) :
    (skelToTree 2 le_rfl 1 0 (fun k => k + 1) 1 1).IsComplete 1 ∧
    (let l0 : Finset (Fin 2) := {⟨0, by decide⟩}
     let l1 : Finset (Fin 2) := {⟨1, by decide⟩}
     let T : MSFDT 2 := .node ⟨0, by decide⟩ ⟨1, by decide⟩ (.leaf l0) (.leaf l1)
     let mem : ℕ → ℕ := fun a =>
       if a = 0 then 0 else if a = 1 then 1
       else if a = 10 then maskOfFinset l0 else if a = 11 then maskOfFinset l1 else 0
     let endNode := walkCompleteTree 0 10 mem cmp 1 1
     2 ≤ endNode ∧ endNode < 4 ∧
     mem (10 + (endNode - 2)) = maskOfFinset (T.eval p)) := by
  refine ⟨skelToTree_isComplete 2 le_rfl 1 0 (fun k => k + 1) 1 1, ?_⟩
  intro l0 l1 T mem endNode
  have hhold : HoldsCompleteTree 1 0 10 1 1 mem T := by
    refine holdsCompleteTree_node.mpr ⟨by decide, by decide, ?_, ?_, ?_, ?_⟩
    · simp [mem]
    · simp [mem]
    · exact holdsCompleteTree_leaf.mpr ⟨by decide, by decide, by simp [mem]⟩
    · exact holdsCompleteTree_leaf.mpr ⟨by decide, by decide, by simp [mem]⟩
  simpa using walkCompleteTree_eval p cmp hcmp hhold

/-! ## `DecisionTree.PrecompKruskal`: Enumeration, Power Table, Decoding, and Kruskal -/

-- `dtFillAllPairsProg_spec`, `realizes_dtFillAllPairsProg`, and empty `numV = 0` boundary.
example {w : ℕ} {d : DTPairsArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtFillAllPairsProgSafe w d s) :
    Memory.FramedTriple w s (dtFillAllPairsProg d) (d.numV * (1 + 2 * d.numV))
      (Set.Ico d.arrA (d.arrA + d.numV.choose 2) ∪
        Set.Ico d.arrB (d.arrB + d.numV.choose 2))
      (fun res s' =>
        res = d.numV.choose 2 ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k (hk : k < d.numV.choose 2),
          s'.mem (d.arrA + k) =
            ((allPairs d.numV)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
          s'.mem (d.arrB + k) =
            ((allPairs d.numV)[k]'(by rw [length_allPairs]; exact hk)).2.val) ∧
    Realizes .exact dtFillAllPairsProg dtPairsArgsWords WordEncoding.encode
      dtFillAllPairsProgSafe (fun _ _ => 0) :=
  ⟨dtFillAllPairsProg_spec hwf hsafe, realizes_dtFillAllPairsProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 0⟩
    let d0 : DTPairsArgs := ⟨0, 0, 0⟩
    Memory.FramedTriple 16 s0 (dtFillAllPairsProg d0) 0 ∅
      fun res s' => res = 0 ∧ s'.frontier = 0 ∧ Memory.WellFormed 16 s' := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨Nat.two_pow_pos 16, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtFillAllPairsProgSafe 16 d0 s0 :=
    (dtFillAllPairsProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by decide, fun h => by omega, by simp [d0, s0],
       by simp [d0, s0], Or.inl (by simp [d0])⟩
  have hft := dtFillAllPairsProg_spec hwf0 hsafe0
  simpa [d0, s0] using hft.mono le_rfl fun res s' ⟨hres, hfr, hwf', _⟩ => ⟨hres, hfr, hwf'⟩

-- `dtFillPowProg_spec`, `realizes_dtFillPowProg`, and `len = 0` boundary.
example {w : ℕ} {d : DTPowArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtFillPowProgSafe w d s) :
    Memory.FramedTriple w s (dtFillPowProg d) (1 + 2 * d.len)
      (Set.Ico d.powArr (d.powArr + d.len + 1))
      (fun res s' =>
        res = d.len ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ k ≤ d.len, s'.mem (d.powArr + k) = d.base ^ k) ∧
    Realizes .exact dtFillPowProg dtPowArgsWords WordEncoding.encode
      dtFillPowProgSafe (fun _ _ => 0) :=
  ⟨dtFillPowProg_spec hwf hsafe, realizes_dtFillPowProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 1⟩
    let d0 : DTPowArgs := ⟨0, 3, 0⟩
    Memory.FramedTriple 16 s0 (dtFillPowProg d0) 1 (Set.Ico 0 1)
      fun res s' => res = 0 ∧ s'.frontier = 1 ∧ s'.mem 0 = 1 := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨by decide, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtFillPowProgSafe 16 d0 s0 :=
    (dtFillPowProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by decide, by decide, by simp [d0, s0]⟩
  have hft := dtFillPowProg_spec hwf0 hsafe0
  refine hft.mono (by decide) fun res s' ⟨hres, hfr, _, hpow⟩ =>
    ⟨hres, hfr, by simpa [d0] using hpow 0 le_rfl⟩

-- `dtDecodeMaskProg_spec` + `realizes_dtDecodeMaskProg` (general and empty `r0 = 0` witness).
example {w r0 : ℕ} {d : DTDecodeMaskArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtDecodeMaskProgSafe w d s)
    (hmaxE : d.maxE = r0.choose 2)
    (hpairs : ∀ k (hk : k < r0.choose 2),
      s.mem (d.r0PairA + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).1.val ∧
      s.mem (d.r0PairB + k) = ((allPairs r0)[k]'(by rw [length_allPairs]; exact hk)).2.val)
    (hduv : d.edgeU + r0.choose 2 ≤ d.edgeV ∨ d.edgeV + r0.choose 2 ≤ d.edgeU)
    (hdup : d.edgeU + r0.choose 2 ≤ d.edgePair ∨ d.edgePair + r0.choose 2 ≤ d.edgeU)
    (hdvp : d.edgeV + r0.choose 2 ≤ d.edgePair ∨ d.edgePair + r0.choose 2 ≤ d.edgeV)
    (hdua : d.edgeU + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgeU)
    (hdub : d.edgeU + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgeU)
    (hdva : d.edgeV + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgeV)
    (hdvb : d.edgeV + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgeV)
    (hdpa : d.edgePair + r0.choose 2 ≤ d.r0PairA ∨ d.r0PairA + r0.choose 2 ≤ d.edgePair)
    (hdpb : d.edgePair + r0.choose 2 ≤ d.r0PairB ∨ d.r0PairB + r0.choose 2 ≤ d.edgePair) :
    Memory.FramedTriple w s (dtDecodeMaskProg d) (5 * d.maxE)
      (Set.Ico d.edgeU (d.edgeU + d.maxE) ∪ Set.Ico d.edgeV (d.edgeV + d.maxE) ∪
        Set.Ico d.edgePair (d.edgePair + d.maxE))
      (fun res s' =>
        res = (maskEdgePairs r0 d.mask).length ∧
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j (hj : j < (maskEdgePairs r0 d.mask).length),
          s'.mem (d.edgeU + j) = ((maskEdgePairs r0 d.mask)[j]).1.val ∧
          s'.mem (d.edgeV + j) = ((maskEdgePairs r0 d.mask)[j]).2.val ∧
          s'.mem (d.edgePair + j) =
            pairIdx ((maskEdgePairs r0 d.mask)[j]).1.val
              ((maskEdgePairs r0 d.mask)[j]).2.val) ∧
    Realizes .exact dtDecodeMaskProg dtDecodeMaskArgsWords WordEncoding.encode
      dtDecodeMaskProgSafe (fun _ _ => 0) :=
  ⟨dtDecodeMaskProg_spec hwf hsafe hmaxE hpairs hduv hdup hdvp hdua hdub hdva hdvb hdpa hdpb,
   realizes_dtDecodeMaskProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 0⟩
    let d0 : DTDecodeMaskArgs := ⟨0, 0, 0, 0, 0, 0, 0⟩
    Memory.FramedTriple 16 s0 (dtDecodeMaskProg d0) 0 ∅
      fun res s' => res = 0 ∧ s'.frontier = 0 := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨Nat.two_pow_pos 16, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtDecodeMaskProgSafe 16 d0 s0 :=
    (dtDecodeMaskProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by simp [d0, s0], by simp [d0, s0],
       by simp [d0, s0], by simp [d0, s0], by simp [d0, s0]⟩
  have hft := dtDecodeMaskProg_spec (r0 := 0) hwf0 hsafe0 rfl
    (fun k hk => absurd hk (Nat.not_lt_zero _))
    (Or.inl le_rfl) (Or.inl le_rfl) (Or.inl le_rfl)
    (Or.inl le_rfl) (Or.inl le_rfl) (Or.inl le_rfl)
    (Or.inl le_rfl) (Or.inl le_rfl) (Or.inl le_rfl)
  simpa [d0] using hft.mono (by decide) fun res s' ⟨hres, hfr, _, _⟩ =>
    ⟨hres.trans (by simp [d0, maskEdgePairs]), hfr⟩

-- `dtKruskalMaskProg_spec`, `realizes_dtKruskalMaskProg`, and `e = 0` boundary witness.
example {w : ℕ} {d : DTKruskalProgArgs} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hsafe : dtKruskalMaskProgSafe w d s)
    (p : Equiv.Perm (Fin d.e))
    (hord : ∀ rk (hrk : rk < d.e), s.mem (d.orderArr + rk) = (p.symm ⟨rk, hrk⟩).val)
    (ends : Fin d.e → Sym2 (Fin d.r0))
    (hends : ∀ i : Fin d.e, ∃ a b : Fin d.r0, ends i = s(a, b) ∧
      s.mem (d.edgeU + i.val) = a.val ∧ s.mem (d.edgeV + i.val) = b.val) :
    Memory.FramedTriple w s (dtKruskalMaskProg d) (d.r0 + d.e * (5 + 2 * d.r0))
      (Set.Ico d.compArr (d.compArr + d.r0))
      (fun res s' =>
        res = maskOfFinset (Cslib.Multigraph.msf ends p Finset.univ) ∧
        s'.frontier = s.frontier ∧ Memory.WellFormed w s') ∧
    Realizes .exact dtKruskalMaskProg dtKruskalProgArgsWords WordEncoding.encode
      dtKruskalMaskProgSafe (fun _ _ => 0) :=
  ⟨dtKruskalMaskProg_spec hwf hsafe p hord ends hends, realizes_dtKruskalMaskProg⟩

example :
    let s0 : Memory.State := ⟨fun _ => 0, 3⟩
    let d0 : DTKruskalProgArgs := ⟨3, 0, 0, 0, 0, 0⟩
    Memory.FramedTriple 16 s0 (dtKruskalMaskProg d0) 3 (Set.Ico 0 3)
      fun res s' =>
        res = maskOfFinset
          (Cslib.Multigraph.msf (fun i : Fin 0 => (Fin.elim0 i : Sym2 (Fin 3)))
            (Equiv.refl (Fin 0)) Finset.univ) ∧
        s'.frontier = 3 := by
  intro s0 d0
  have hwf0 : Memory.WellFormed 16 s0 := ⟨by decide, fun _ => Nat.two_pow_pos 16⟩
  have hsafe0 : dtKruskalMaskProgSafe 16 d0 s0 :=
    (dtKruskalMaskProgSafe_iff 16 d0 s0).mpr
      ⟨by decide, by decide, by decide, by decide,
       by simp [d0, s0], by simp [d0, s0], by simp [d0, s0], by simp [d0, s0],
       Or.inr (by simp [d0]), Or.inr (by simp [d0]), Or.inr (by simp [d0]),
       fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hft := dtKruskalMaskProg_spec hwf0 hsafe0 (Equiv.refl (Fin 0))
    (fun _ h => absurd h (Nat.not_lt_zero _))
    (fun i : Fin 0 => (Fin.elim0 i : Sym2 (Fin 3))) (fun i => Fin.elim0 i)
  exact hft.mono (by simp [d0]) fun res s' ⟨hres, hfr, _⟩ => ⟨hres, hfr⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreeLayout
