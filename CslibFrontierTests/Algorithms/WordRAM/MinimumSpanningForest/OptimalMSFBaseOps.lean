/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for OptimalMSF base combinatorial bounds and Word-RAM subroutines)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BaseOps
import CslibFrontier.Computability.WordRAM.Realization.NatLog
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-!
# Tests for Word-RAM Optimal MSF Base Bounds and Subroutines

Exercises Section 1 combinatorial/acyclicity bounds and all six Section 3 Word-RAM subroutines
from `CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BaseOps` across concrete
non-empty and empty (`m = 0`) witnesses, plus `module`-encapsulated composite `realize` pipelines
exercising all six `BaseOps` `realizes_*` certificates alongside `NatLog.natLog2Prog` and
`NatLog.iterLogProg 3`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFBaseOps

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## Private test setup and decode helpers -/

private def encodeLifts {nLoc nGlob : ℕ} (lift : Fin nLoc → Fin nGlob) : List ℕ :=
  (List.finRange nLoc).map fun k => (lift k).val

private theorem holdsList_get {base : ℕ} {xs : List ℕ} {mem : ℕ → ℕ}
    (h : Block.HoldsList base xs mem) :
    ∀ i (hi : i < xs.length), mem (base + i) = xs[i] := by
  induction xs generalizing base with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons x rest ih =>
    obtain ⟨hx, hrest⟩ := Block.holdsList_cons_iff.mp h
    intro i hi
    cases i with
    | zero => exact hx
    | succ k =>
      rw [show base + (k + 1) = base + 1 + k by omega]
      exact ih hrest k (Nat.lt_of_succ_lt_succ hi)

private theorem holdsIndexedEdges_of_holdsList {n : ℕ} (base : ℕ) (es : List (IndexedEdge n))
    {mem : ℕ → ℕ} (h : Block.HoldsList base (encodeIndexedEdges es) mem) :
    HoldsIndexedEdges base es mem := by
  induction es generalizing base with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons e rest ih =>
    simp only [encodeIndexedEdges, List.flatMap_cons, List.cons_append, List.nil_append] at h
    obtain ⟨hu, h₁⟩ := Block.holdsList_cons_iff.mp h
    obtain ⟨hv, h₂⟩ := Block.holdsList_cons_iff.mp h₁
    obtain ⟨hw, h₃⟩ := Block.holdsList_cons_iff.mp h₂
    obtain ⟨hid, hrest⟩ := Block.holdsList_cons_iff.mp h₃
    rw [show base + 1 + 1 + 1 + 1 = base + 4 by omega] at hrest
    have hrest' : HoldsIndexedEdges (base + 4) rest mem := ih (base + 4) hrest
    intro i hi
    cases i with
    | zero => exact ⟨hu, hv, hw, hid⟩
    | succ k =>
      rcases hrest' k (Nat.lt_of_succ_lt_succ hi) with ⟨h₁, h₂, h₃, h₄⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [show base + 4 * (k + 1) = base + 4 + 4 * k by omega]; exact h₁
      · rw [show base + 4 * (k + 1) + 1 = base + 4 + 4 * k + 1 by omega]; exact h₂
      · rw [show base + 4 * (k + 1) + 2 = base + 4 + 4 * k + 2 by omega]; exact h₃
      · rw [show base + 4 * (k + 1) + 3 = base + 4 + 4 * k + 3 by omega]; exact h₄

private theorem fits32_of_lt {v : ℕ} (hv : v < 256) : Fits 32 v :=
  Nat.lt_trans hv (by decide)

private theorem wf_empty_32 : Memory.WellFormed 32 ⟨fun _ => 0, 0⟩ :=
  ⟨fits32_of_lt (by decide), fun _ => fits32_of_lt (by dsimp only; decide)⟩

/-! ## Section 1: Combinatorial, `dtPrecompCost`, and Acyclicity Witnesses -/

example (k : ℕ) (hk : 24 ≤ k) :
    Nat.iterLog 3 (2 ^ 2 ^ 2 ^ k) = k ∧ dtPrecompCost k ≤ 2 ^ 2 ^ 2 ^ k := by
  have hlog : Nat.iterLog 3 (2 ^ 2 ^ 2 ^ k) = k := by
    rw [Nat.iterLog_succ, Nat.iterLog_succ, Nat.iterLog_succ, Nat.iterLog_zero,
      Nat.log_pow (by decide : 1 < 2), Nat.log_pow (by decide : 1 < 2),
      Nat.log_pow (by decide : 1 < 2)]
  have hle := dtPrecompCost_iterLog_le_of_ge_24 (by rw [hlog]; exact hk)
  rw [hlog] at hle
  exact ⟨hlog, hle⟩

example : (4 : ℕ) ≤ 2 * ([⟨0, 1, 5, 10⟩, ⟨2, 3, 7, 11⟩] : List (IndexedEdge 4)).length := by
  refine card_le_two_mul_of_noIsolated [⟨0, 1, 5, 10⟩, ⟨2, 3, 7, 11⟩] fun y => ?_
  fin_cases y
  · exact ⟨⟨0, 1, 5, 10⟩, by simp, Or.inl rfl⟩
  · exact ⟨⟨0, 1, 5, 10⟩, by simp, Or.inr rfl⟩
  · exact ⟨⟨2, 3, 7, 11⟩, by simp, Or.inl rfl⟩
  · exact ⟨⟨2, 3, 7, 11⟩, by simp, Or.inr rfl⟩

example : IsAcyclic ([(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩]) ∧
    ¬ IsAcyclic ([(⟨0, 2, 7⟩ : WeightedEdge 3 ℕ), ⟨0, 1, 3⟩, ⟨1, 2, 5⟩]) ∧
    [(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩].length ≤
      ({0, 1, 2} : Finset (Fin 3)).card - 1 := by
  have h2 : IsAcyclic ([(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩]) := by decide
  have hnot : ¬ IsAcyclic ([(⟨0, 2, 7⟩ : WeightedEdge 3 ℕ), ⟨0, 1, 3⟩, ⟨1, 2, 5⟩]) := by
    rw [isAcyclic_cons_iff]
    rintro ⟨hrel, _⟩
    have htrue : (edgePartition ([(⟨0, 1, 3⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 5⟩])).rel 0 2 = true := by
      decide
    simp [htrue] at hrel
  have hlen := isAcyclic_length_le_finset_sub_one ({0, 1, 2} : Finset (Fin 3))
    [⟨0, 1, 3⟩, ⟨1, 2, 5⟩] h2 fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> decide
  exact ⟨h2, hnot, hlen⟩

example : IsAcyclic ([(⟨0, 1, 4⟩ : WeightedEdge 3 ℕ), ⟨1, 2, 9⟩]) := by
  let lift : Fin 3 → Fin 5 := ![1, 3, 4]
  have hlift : Function.Injective lift := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [lift]
  have hlifted : IsAcyclic (contractEdgeList lift [⟨0, 1, 4⟩, ⟨1, 2, 9⟩]) := by decide
  exact isAcyclic_of_contractEdgeList_injective hlift _ hlifted

example : ([2, 2] : List ℕ).sum ≤ 5 ∧ ([] : List ℕ).sum ≤ 5 := by
  let verts : List (Finset (Fin 5)) := [{0, 1, 2}, {2, 3, 4}]
  have hnonempty : ([2, 2] : List ℕ).sum ≤ 5 := by
    refine sum_verts_sub_one_le verts [2, 2] rfl (fun i => ?_) (fun i => ?_)
    · fin_cases i <;> decide
    · fin_cases i <;> decide
  have hempty : ([] : List ℕ).sum ≤ 5 :=
    sum_verts_sub_one_le ([] : List (Finset (Fin 5))) [] rfl (fun i => Fin.elim0 i)
      (fun i => Fin.elim0 i)
  exact ⟨hnonempty, hempty⟩

/-! ## Section 2: Concrete Edge-Array Subroutines (Non-Empty and `m = 0`) -/

example :
    let es : List (IndexedEdge 4) := [⟨0, 1, 3, 7⟩, ⟨1, 2, 5, 13⟩, ⟨2, 3, 9, 29⟩]
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩
      (initFromWordsProg (encodeIndexedEdges es))
    let outBase := (Memory.spec 0).clientResult s₁ (retagIndexedProg (0, es.length))
    let s₂ := (Memory.spec 0).clientState s₁ (retagIndexedProg (0, es.length))
    outBase = 12 ∧ s₂.frontier = 24 ∧
    HoldsIndexedEdges outBase
      ([⟨0, 1, 3, 0⟩, ⟨1, 2, 5, 1⟩, ⟨2, 3, 9, 2⟩] : List (IndexedEdge 4)) s₂.mem ∧
    s₂.mem 3 = 7 ∧ s₂.mem 7 = 13 ∧ s₂.mem 11 = 29 ∧
    (Memory.spec 0).clientResult s₁ (retagIndexedProg (0, 0)) = 12 ∧
    ((Memory.spec 0).clientState s₁ (retagIndexedProg (0, 0))).frontier = 12 := by
  let es : List (IndexedEdge 4) := [⟨0, 1, 3, 7⟩, ⟨1, 2, 5, 13⟩, ⟨2, 3, 9, 29⟩]
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := encodeIndexedEdges es) wf_empty_32
      (fits32_of_lt (by simp [es, encodeIndexedEdges]))
      (fun v hv => fits32_of_lt (by simp [es, encodeIndexedEdges] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg (encodeIndexedEdges es))
  have hin : HoldsIndexedEdges 0 es s₁.mem := holdsIndexedEdges_of_holdsList 0 es hbl1
  have hr := framedTriple_iff_realization.mp
    (retagIndexedProg_spec (w := 32) (srcBase := 0) (es := es) (s := s₁)
      (fits32_of_lt (by decide)) hwf1 hin (by simp [hfr1, es, encodeIndexedEdges])
      (fits32_of_lt (by rw [hfr1]; simp [es, encodeIndexedEdges])))
  obtain ⟨_, _, hmod2, hout, hfr2, _, hret⟩ := hr
  have hk3 : s₁.mem 3 = 7 := (hin 0 (by decide)).2.2.2
  have hk7 : s₁.mem 7 = 13 := (hin 1 (by decide)).2.2.2
  have hk11 : s₁.mem 11 = 29 := (hin 2 (by decide)).2.2.2
  have hpres3 : ((Memory.spec 0).clientState s₁ (retagIndexedProg (0, es.length))).mem 3 = 7 :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; simp [es, encodeIndexedEdges])
      (Set.notMem_empty _)).trans hk3
  have hpres7 : ((Memory.spec 0).clientState s₁ (retagIndexedProg (0, es.length))).mem 7 = 13 :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; simp [es, encodeIndexedEdges])
      (Set.notMem_empty _)).trans hk7
  have hpres11 : ((Memory.spec 0).clientState s₁ (retagIndexedProg (0, es.length))).mem 11 = 29 :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; simp [es, encodeIndexedEdges])
      (Set.notMem_empty _)).trans hk11
  have hr0 := framedTriple_iff_realization.mp
    (retagIndexedProg_spec (w := 32) (srcBase := 0) (es := ([] : List (IndexedEdge 4))) (s := s₁)
      (fits32_of_lt (by decide)) hwf1 (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by simp [hfr1]) (fits32_of_lt (by rw [hfr1]; simp [es, encodeIndexedEdges])))
  simp only [List.length_nil] at hr0
  refine ⟨by rw [hout, hfr1]; simp [es, encodeIndexedEdges],
    by rw [hfr2, hfr1]; simp [es, encodeIndexedEdges], ?_, hpres3, hpres7, hpres11,
    by rw [hr0.2.2.2.1, hfr1]; simp [es, encodeIndexedEdges],
    by rw [hr0.2.2.2.2.1, hfr1]; simp [es, encodeIndexedEdges]⟩
  intro i hi
  rcases i with _ | _ | _ | k
  · simpa [es] using hret 0 (by decide)
  · simpa [es] using hret 1 (by decide)
  · simpa [es] using hret 2 (by decide)
  · simp at hi; omega

example :
    let es : List (IndexedEdge 3) := [⟨0, 1, 2, 5⟩, ⟨1, 2, 4, 9⟩]
    let words := encodeIndexedEdges es ++ [99, 0, 0]
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
    let res := (Memory.spec 0).clientResult s₁ (appendSelIdsProg (⟨0, 8⟩, 1, es.length))
    let s₂ := (Memory.spec 0).clientState s₁ (appendSelIdsProg (⟨0, 8⟩, 1, es.length))
    res = 3 ∧ s₂.frontier = 11 ∧ s₂.mem 8 = 99 ∧ s₂.mem 9 = 5 ∧ s₂.mem 10 = 9 ∧
    (Memory.spec 0).clientResult s₁ (appendSelIdsProg (⟨0, 8⟩, 2, 0)) = 2 ∧
    ((Memory.spec 0).clientState s₁ (appendSelIdsProg (⟨0, 8⟩, 2, 0))).mem 8 = 99 := by
  let es : List (IndexedEdge 3) := [⟨0, 1, 2, 5⟩, ⟨1, 2, 4, 9⟩]
  let words := encodeIndexedEdges es ++ [99, 0, 0]
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := words) wf_empty_32
      (fits32_of_lt (by simp [words, es, encodeIndexedEdges]))
      (fun v hv => fits32_of_lt (by simp [words, es, encodeIndexedEdges] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
  have hg := holdsList_get hbl1
  have hin : HoldsIndexedEdges 0 es s₁.mem := fun i hi => by
    rcases i with _ | _ | k
    · exact ⟨by simpa [words, es, encodeIndexedEdges] using hg 0 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 1 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 2 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 3 (by decide)⟩
    · exact ⟨by simpa [words, es, encodeIndexedEdges] using hg 4 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 5 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 6 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 7 (by decide)⟩
    · simp [es] at hi
  have h8 : s₁.mem 8 = 99 := by simpa [words, es, encodeIndexedEdges] using hg 8 (by decide)
  have hft := framedTriple_iff_realization.mp
    (appendSelIdsProg_spec (w := 32) (srcBase := 0) (dstBase := 8) (dstOff := 1) (srcEs := es)
      (s := s₁) (fits32_of_lt (by decide)) hwf1 hin
      (by rw [hfr1]; simp [words, es, encodeIndexedEdges])
      (by rw [hfr1]; simp [words, es, encodeIndexedEdges]) (by simp [es])
      (fits32_of_lt (by simp [es])))
  obtain ⟨_, _, hmod2, hres2, hfr2, _, hvals2⟩ := hft
  have hp8 : ((Memory.spec 0).clientState s₁ (appendSelIdsProg (⟨0, 8⟩, 1, es.length))).mem 8 =
      99 :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; simp [words, es, encodeIndexedEdges])
      (fun hm => by rw [Set.mem_Ico] at hm; omega)).trans h8
  have hft0 := framedTriple_iff_realization.mp
    (appendSelIdsProg_spec (w := 32) (srcBase := 0) (dstBase := 8) (dstOff := 2)
      (srcEs := ([] : List (IndexedEdge 3))) (s := s₁) (fits32_of_lt (by decide)) hwf1
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, es, encodeIndexedEdges])
      (by rw [hfr1]; simp [words, es, encodeIndexedEdges]) (by decide) (fits32_of_lt (by decide)))
  have hp08 : ((Memory.spec 0).clientState s₁ (appendSelIdsProg (⟨0, 8⟩, 2, 0))).mem 8 = 99 :=
    (hft0.2.2.1.mem_eq_of_not_mem (by rw [hfr1]; simp [words, es, encodeIndexedEdges])
      (fun hm => by rw [Set.mem_Ico] at hm; omega)).trans h8
  exact ⟨hres2, by rw [hfr2, hfr1]; simp [words, es, encodeIndexedEdges], hp8,
    hvals2 0 (by decide), hvals2 1 (by decide), hft0.2.2.2.1, hp08⟩

example :
    let es : List (IndexedEdge 4) := [⟨0, 2, 6, 3⟩, ⟨1, 3, 8, 5⟩]
    let pad : List (IndexedEdge 4) := [⟨3, 3, 77, 88⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
    let words := encodeIndexedEdges (es ++ pad)
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
    let res := (Memory.spec 0).clientResult s₁ (copyStride4Prog (⟨0, 8⟩, 1, es.length))
    let s₂ := (Memory.spec 0).clientState s₁ (copyStride4Prog (⟨0, 8⟩, 1, es.length))
    res = 3 ∧ s₂.frontier = 20 ∧
    HoldsIndexedEdges 12 es s₂.mem ∧ s₂.mem 10 = 77 ∧
    (Memory.spec 0).clientResult s₁ (copyStride4Prog (⟨0, 8⟩, 1, 0)) = 1 := by
  let es : List (IndexedEdge 4) := [⟨0, 2, 6, 3⟩, ⟨1, 3, 8, 5⟩]
  let pad : List (IndexedEdge 4) := [⟨3, 3, 77, 88⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  let words := encodeIndexedEdges (es ++ pad)
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := words) wf_empty_32
      (fits32_of_lt (by simp [words, es, pad, encodeIndexedEdges]))
      (fun v hv => fits32_of_lt (by simp [words, es, pad, encodeIndexedEdges] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
  have hg := holdsList_get hbl1
  have hin : HoldsIndexedEdges 0 es s₁.mem := fun i hi => by
    rcases i with _ | _ | k
    · exact ⟨by simpa [words, es, pad, encodeIndexedEdges] using hg 0 (by decide),
        by simpa [words, es, pad, encodeIndexedEdges] using hg 1 (by decide),
        by simpa [words, es, pad, encodeIndexedEdges] using hg 2 (by decide),
        by simpa [words, es, pad, encodeIndexedEdges] using hg 3 (by decide)⟩
    · exact ⟨by simpa [words, es, pad, encodeIndexedEdges] using hg 4 (by decide),
        by simpa [words, es, pad, encodeIndexedEdges] using hg 5 (by decide),
        by simpa [words, es, pad, encodeIndexedEdges] using hg 6 (by decide),
        by simpa [words, es, pad, encodeIndexedEdges] using hg 7 (by decide)⟩
    · simp [es] at hi
  have h10 : s₁.mem 10 = 77 := by
    simpa [words, es, pad, encodeIndexedEdges] using hg 10 (by decide)
  have hft := framedTriple_iff_realization.mp
    (copyStride4Prog_spec (w := 32) (srcBase := 0) (dstBase := 8) (dstOff := 1) (srcEs := es)
      (s := s₁) (fits32_of_lt (by decide)) hwf1 hin
      (by rw [hfr1]; simp [words, es, pad, encodeIndexedEdges])
      (by rw [hfr1]; simp [words, es, pad, encodeIndexedEdges])
      (by simp [es]) (fits32_of_lt (by simp [es])))
  obtain ⟨_, _, hmod2, hres2, hfr2, _, hcopy⟩ := hft
  have hp10 : ((Memory.spec 0).clientState s₁ (copyStride4Prog (⟨0, 8⟩, 1, es.length))).mem 10 =
      77 :=
    (hmod2.mem_eq_of_not_mem (by rw [hfr1]; simp [words, es, pad, encodeIndexedEdges])
      (fun hm => by simp [Set.mem_Ico] at hm)).trans h10
  have hft0 := framedTriple_iff_realization.mp
    (copyStride4Prog_spec (w := 32) (srcBase := 0) (dstBase := 8) (dstOff := 1)
      (srcEs := ([] : List (IndexedEdge 4))) (s := s₁) (fits32_of_lt (by decide)) hwf1
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, es, pad, encodeIndexedEdges])
      (by rw [hfr1]; simp [words, es, pad, encodeIndexedEdges]) (by decide)
      (fits32_of_lt (by decide)))
  exact ⟨hres2, by rw [hfr2, hfr1]; simp [words, es, pad, encodeIndexedEdges], hcopy, hp10,
    hft0.2.2.2.1⟩

example :
    let L1 : List (IndexedEdge 4) := [⟨0, 1, 2, 10⟩, ⟨1, 2, 4, 11⟩]
    let L2 : List (IndexedEdge 4) := [⟨2, 3, 6, 12⟩]
    let L3 : List (IndexedEdge 4) := [⟨0, 3, 8, 13⟩]
    let words := encodeIndexedEdges (L1 ++ L2 ++ L3)
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
    let res := (Memory.spec 0).clientResult s₁ (concatThreeProg ⟨0, 2, 8, 1, 12, 1⟩)
    let s₂ := (Memory.spec 0).clientState s₁ (concatThreeProg ⟨0, 2, 8, 1, 12, 1⟩)
    res = (16, 4) ∧ s₂.frontier = 32 ∧
    HoldsIndexedEdges res.1 (L1 ++ L2 ++ L3) s₂.mem ∧
    (Memory.spec 0).clientResult s₁ (concatThreeProg ⟨0, 0, 8, 0, 12, 0⟩) = (16, 0) := by
  let L1 : List (IndexedEdge 4) := [⟨0, 1, 2, 10⟩, ⟨1, 2, 4, 11⟩]
  let L2 : List (IndexedEdge 4) := [⟨2, 3, 6, 12⟩]
  let L3 : List (IndexedEdge 4) := [⟨0, 3, 8, 13⟩]
  let words := encodeIndexedEdges (L1 ++ L2 ++ L3)
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := words) wf_empty_32
      (fits32_of_lt (by simp [words, L1, L2, L3, encodeIndexedEdges]))
      (fun v hv => fits32_of_lt (by simp [words, L1, L2, L3, encodeIndexedEdges] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
  have hg := holdsList_get hbl1
  have h1 : HoldsIndexedEdges 0 L1 s₁.mem := fun i hi => by
    rcases i with _ | _ | k
    · exact ⟨by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 0 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 1 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 2 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 3 (by decide)⟩
    · exact ⟨by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 4 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 5 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 6 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 7 (by decide)⟩
    · simp [L1] at hi
  have h2 : HoldsIndexedEdges 8 L2 s₁.mem := fun i hi => by
    rcases i with _ | k
    · exact ⟨by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 8 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 9 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 10 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 11 (by decide)⟩
    · simp [L2] at hi
  have h3 : HoldsIndexedEdges 12 L3 s₁.mem := fun i hi => by
    rcases i with _ | k
    · exact ⟨by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 12 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 13 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 14 (by decide),
        by simpa [words, L1, L2, L3, encodeIndexedEdges] using hg 15 (by decide)⟩
    · simp [L3] at hi
  have hft := framedTriple_iff_realization.mp
    (concatThreeProg_spec (w := 32) (b1 := 0) (b2 := 8) (b3 := 12) hwf1
      h1 (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])
      h2 (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])
      h3 (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])
      (fits32_of_lt (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])))
  obtain ⟨_, _, _, hres, hfr2, _, hcat⟩ := hft
  have hft0 := framedTriple_iff_realization.mp
    (concatThreeProg_spec (w := 32) (n := 4) (b1 := 0) (b2 := 8) (b3 := 12)
      (L1 := []) (L2 := []) (L3 := []) hwf1
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])
      (fits32_of_lt (by rw [hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges])))
  simp only [List.length_nil] at hft0
  simp only [L1, L2, L3, List.length_cons, List.length_nil] at hres hfr2
  exact ⟨by rw [hres, hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges],
    by rw [hfr2, hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges], hcat,
    by rw [hft0.2.2.2.1, hfr1]; simp [words, L1, L2, L3, encodeIndexedEdges]⟩

example :
    let C : List (IndexedEdge 3) := [⟨0, 1, 10, 4⟩, ⟨1, 2, 20, 8⟩]
    let lift : Fin 3 → Fin 5 := ![1, 3, 4]
    let words := encodeIndexedEdges C ++ encodeLifts lift ++ [55, 0, 0, 0] ++ List.replicate 8 0
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
    let res := (Memory.spec 0).clientResult s₁ (liftEdgesProg (⟨0, 8, 11⟩, 1, C.length))
    let s₂ := (Memory.spec 0).clientState s₁ (liftEdgesProg (⟨0, 8, 11⟩, 1, C.length))
    res = 3 ∧ s₂.frontier = 23 ∧ s₂.mem 11 = 55 ∧
    HoldsIndexedEdges 15 ([⟨1, 3, 10, 4⟩, ⟨3, 4, 20, 8⟩] : List (IndexedEdge 5)) s₂.mem ∧
    (Memory.spec 0).clientResult s₁ (liftEdgesProg (⟨0, 8, 11⟩, 1, 0)) = 1 := by
  let C : List (IndexedEdge 3) := [⟨0, 1, 10, 4⟩, ⟨1, 2, 20, 8⟩]
  let lift : Fin 3 → Fin 5 := ![1, 3, 4]
  let words := encodeIndexedEdges C ++ encodeLifts lift ++ [55, 0, 0, 0] ++ List.replicate 8 0
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := words) wf_empty_32
      (fits32_of_lt (by simp [words, C, encodeIndexedEdges, encodeLifts]))
      (fun v hv => fits32_of_lt (by
        simp [words, C, encodeIndexedEdges, encodeLifts, lift] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
  have hg := holdsList_get hbl1
  have hin : HoldsIndexedEdges 0 C s₁.mem := fun i hi => by
    rcases i with _ | _ | k
    · exact ⟨by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 0 (by decide),
        by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 1 (by decide),
        by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 2 (by decide),
        by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 3 (by decide)⟩
    · exact ⟨by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 4 (by decide),
        by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 5 (by decide),
        by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 6 (by decide),
        by simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 7 (by decide)⟩
    · simp [C] at hi
  have hlift : ∀ k : Fin 3, s₁.mem (8 + k.val) = (lift k).val := fun k => by
    fin_cases k
    · simpa [words, C, encodeIndexedEdges, encodeLifts, lift] using hg 8 (by decide)
    · simpa [words, C, encodeIndexedEdges, encodeLifts, lift] using hg 9 (by decide)
    · simpa [words, C, encodeIndexedEdges, encodeLifts, lift] using hg 10 (by decide)
  have h11 : s₁.mem 11 = 55 := by
    simpa [words, C, encodeIndexedEdges, encodeLifts] using hg 11 (by decide)
  have hft := framedTriple_iff_realization.mp
    (liftEdgesProg_spec (w := 32) (edgeBase := 0) (liftBase := 8) (dstBase := 11) (dstOff := 1)
      (C := C) (lift := lift) (s := s₁) (fits32_of_lt (by decide)) hwf1 hin
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts]) hlift
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts])
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts])
      (by simp [C]) (by simp [C]) (fits32_of_lt (by simp [C])))
  obtain ⟨_, _, hmod2, hres2, hfr2, _, hlifted⟩ := hft
  have hp11 : ((Memory.spec 0).clientState s₁ (liftEdgesProg (⟨0, 8, 11⟩, 1, C.length))).mem 11 =
      55 :=
    (hmod2.mem_eq_of_not_mem
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts])
      (fun hm => by simp [Set.mem_Ico] at hm)).trans h11
  have hft0 := framedTriple_iff_realization.mp
    (liftEdgesProg_spec (w := 32) (edgeBase := 0) (liftBase := 8) (dstBase := 11) (dstOff := 1)
      (C := ([] : List (IndexedEdge 3))) (lift := lift) (s := s₁) (fits32_of_lt (by decide)) hwf1
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts]) hlift
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts])
      (by rw [hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts])
      (by decide) (by decide) (fits32_of_lt (by decide)))
  refine ⟨hres2, by rw [hfr2, hfr1]; simp [words, C, encodeIndexedEdges, encodeLifts], hp11, ?_,
    hft0.2.2.2.1⟩
  intro i hi
  have hv0 : (C.map fun x => (⟨lift x.u, lift x.v, x.weight, x.id⟩ : IndexedEdge 5))[0]'(by
      simp [C]) = ⟨1, 3, 10, 4⟩ := by
    dsimp only [C, lift]; rfl
  have hv1 : (C.map fun x => (⟨lift x.u, lift x.v, x.weight, x.id⟩ : IndexedEdge 5))[1]'(by
      simp [C]) = ⟨3, 4, 20, 8⟩ := by
    dsimp only [C, lift]; rfl
  rcases i with _ | _ | k
  · have h0 := hlifted 0 (by decide)
    rw [hv0] at h0; exact h0
  · have h1 := hlifted 1 (by decide)
    rw [hv1] at h1; exact h1
  · simp at hi

example :
    let H_rem : List (IndexedEdge 5) := [⟨0, 1, 10, 4⟩, ⟨2, 3, 20, 7⟩, ⟨3, 4, 30, 9⟩]
    let H_msf : List (IndexedEdge 3) := [⟨1, 2, 30, 2⟩, ⟨0, 1, 10, 0⟩]
    let words := encodeIndexedEdges H_rem ++ encodeIndexedEdges H_msf
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
    let outBase := (Memory.spec 0).clientResult s₁ (liftHRemProg (0, 12, H_msf.length))
    let s₂ := (Memory.spec 0).clientState s₁ (liftHRemProg (0, 12, H_msf.length))
    outBase = 20 ∧ s₂.frontier = 28 ∧
    HoldsIndexedEdges outBase ([⟨3, 4, 30, 9⟩, ⟨0, 1, 10, 4⟩] : List (IndexedEdge 5)) s₂.mem ∧
    (Memory.spec 0).clientResult s₁ (liftHRemProg (0, 12, 0)) = 20 := by
  let H_rem : List (IndexedEdge 5) := [⟨0, 1, 10, 4⟩, ⟨2, 3, 20, 7⟩, ⟨3, 4, 30, 9⟩]
  let H_msf : List (IndexedEdge 3) := [⟨1, 2, 30, 2⟩, ⟨0, 1, 10, 0⟩]
  let words := encodeIndexedEdges H_rem ++ encodeIndexedEdges H_msf
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := words) wf_empty_32
      (fits32_of_lt (by simp [words, H_rem, H_msf, encodeIndexedEdges]))
      (fun v hv => fits32_of_lt (by simp [words, H_rem, H_msf, encodeIndexedEdges] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
  have hg := holdsList_get hbl1
  have hrem : HoldsIndexedEdges 0 H_rem s₁.mem := fun i hi => by
    rcases i with _ | _ | _ | k
    · exact ⟨by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 0 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 1 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 2 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 3 (by decide)⟩
    · exact ⟨by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 4 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 5 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 6 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 7 (by decide)⟩
    · exact ⟨by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 8 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 9 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 10 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 11 (by decide)⟩
    · simp [H_rem] at hi; omega
  have hmsf : HoldsIndexedEdges 12 H_msf s₁.mem := fun i hi => by
    rcases i with _ | _ | k
    · exact ⟨by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 12 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 13 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 14 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 15 (by decide)⟩
    · exact ⟨by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 16 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 17 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 18 (by decide),
        by simpa [words, H_rem, H_msf, encodeIndexedEdges] using hg 19 (by decide)⟩
    · simp [H_msf] at hi
  have hids : ∀ e ∈ H_msf, e.id < H_rem.length := fun e he => by
    simp only [H_msf, H_rem, List.mem_cons, List.not_mem_nil, or_false,
      List.length_cons, List.length_nil] at he ⊢
    rcases he with rfl | rfl <;> decide
  have hft := framedTriple_iff_realization.mp
    (liftHRemProg_spec (w := 32) (hRemBase := 0) (msfBase := 12) (H_rem := H_rem)
      (H_msf := H_msf) (s := s₁) (fits32_of_lt (by decide)) hwf1 hrem
      (by rw [hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges]) hmsf
      (by rw [hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges]) hids
      (fits32_of_lt (by rw [hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges])))
  obtain ⟨_, _, _, hout, hfr2, _, hgath⟩ := hft
  have hft0 := framedTriple_iff_realization.mp
    (liftHRemProg_spec (w := 32) (hRemBase := 0) (msfBase := 12) (H_rem := H_rem)
      (H_msf := ([] : List (IndexedEdge 3))) (s := s₁) (fits32_of_lt (by decide)) hwf1 hrem
      (by rw [hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges])
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges]) (fun _ he => by simp at he)
      (fits32_of_lt (by rw [hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges])))
  simp only [List.length_nil] at hft0
  refine ⟨by rw [hout, hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges],
    by rw [hfr2, hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges], ?_,
    by rw [hft0.2.2.2.1, hfr1]; simp [words, H_rem, H_msf, encodeIndexedEdges]⟩
  intro i hi
  have hv0 : (H_msf.pmap (fun e he => H_rem[e.id]'(hids e he)) (fun _ he => he))[0]'(by
      simp [H_msf]) = ⟨3, 4, 30, 9⟩ := by
    simp only [H_rem, H_msf, List.getElem_pmap]; rfl
  have hv1 : (H_msf.pmap (fun e he => H_rem[e.id]'(hids e he)) (fun _ he => he))[1]'(by
      simp [H_msf]) = ⟨0, 1, 10, 4⟩ := by
    simp only [H_rem, H_msf, List.getElem_pmap]; rfl
  rcases i with _ | _ | k
  · have h0 := hgath 0 (by simp [H_msf])
    rw [hv0] at h0; exact h0
  · have h1 := hgath 1 (by simp [H_msf])
    rw [hv1] at h1; exact h1
  · simp at hi

/-! ## Section 3: Composite `realize` Pipelines Exercising All Six `BaseOps` + `NatLog` -/

private def prepPipelineProg (d : (ℕ × ℕ) × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ × ℕ × ℕ) := do
  let k1 ← natLog2Prog d.2.2
  let k3 ← iterLogProg 3 d.2.2
  let ob ← retagIndexedProg (d.1.1, d.1.2)
  let cat ← concatThreeProg ⟨d.1.1, d.1.2, ob, d.1.2, d.1.1, 0⟩
  let endOff ← appendSelIdsProg (⟨ob, d.2.1⟩, 0, d.1.2)
  pure (k1, k3, cat.1, endOff)

private def prepPipelineRawPre (w : ℕ) (d : (ℕ × ℕ) × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  let s1 := (Memory.spec 0).clientState s (natLog2Prog d.2.2)
  let s2 := (Memory.spec 0).clientState s1 (iterLogProg 3 d.2.2)
  let ob := (Memory.spec 0).clientResult s2 (retagIndexedProg (d.1.1, d.1.2))
  let s3 := (Memory.spec 0).clientState s2 (retagIndexedProg (d.1.1, d.1.2))
  let s4 := (Memory.spec 0).clientState s3
    (concatThreeProg ⟨d.1.1, d.1.2, ob, d.1.2, d.1.1, 0⟩)
  Fits w 16 ∧
    retagIndexedProgSafe w (d.1.1, d.1.2) s2 ∧
    concatThreeProgSafe w ⟨d.1.1, d.1.2, ob, d.1.2, d.1.1, 0⟩ s3 ∧
    appendSelIdsProgSafe w (⟨ob, d.2.1⟩, 0, d.1.2) s4

private theorem realizes_prepPipelineProg : Realizes .exact
    prepPipelineProg
    (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
    (fun w d s =>
      Fits w 16 ∧ d.1.1 + 4 * d.1.2 ≤ s.frontier ∧ d.2.1 + d.1.2 ≤ s.frontier ∧
      Fits w (s.frontier + 12 * d.1.2) ∧ Fits w (d.1.2 + 1))
    (fun d _ => 4 * Nat.log 2 d.2.2 + 20) := by
  have hraw : Realizes .exact prepPipelineProg
      (WordEncoding.encode (α := (ℕ × ℕ) × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ × ℕ × ℕ × ℕ))
      prepPipelineRawPre (fun d _ => 4 * Nat.log 2 d.2.2 + 20) := by
    unfold prepPipelineProg
    realize [realizes_natLog2Prog, realizes_iterLogProg, realizes_retagIndexedProg,
      realizes_concatThreeProg, realizes_appendSelIdsProg]
    all_goals
      rcases h with ⟨h16, h3, h4, h5⟩
      first
      | exact h3 | exact h4 | exact h5
      | (have h16' := h16; fits)
      | (dsimp only; omega)
  refine hraw.consequence
    (fun w d s _ hmem ⟨h16, hsrc, hdst, hfit12, hfitm⟩ => ?_) (fun _ _ => le_rfl)
  rcases d with ⟨⟨srcBase, count⟩, ⟨dstBase, n₀⟩⟩
  dsimp only [prepPipelineRawPre]
  dsimp only at hsrc hdst hfit12 hfitm ⊢
  obtain ⟨_, _, _, hs1, hk1⟩ := framedTriple_iff_realization.mp (natLog2Prog_spec w n₀ s)
  obtain ⟨_, _, _, hs2, hk3⟩ := framedTriple_iff_realization.mp
    (iterLogProg_spec w 3 n₀ ((Memory.spec 0).clientState s (natLog2Prog n₀)))
  set s2 := (Memory.spec 0).clientState ((Memory.spec 0).clientState s (natLog2Prog n₀))
    (iterLogProg 3 n₀)
  have hs2_eq : s2 = s := hs2.trans hs1
  let es : List (IndexedEdge (2 ^ w)) := List.ofFn fun i : Fin count =>
    ⟨⟨s.mem (srcBase + 4 * i.val), hmem.mem_fits _⟩,
      ⟨s.mem (srcBase + 4 * i.val + 1), hmem.mem_fits _⟩,
      s.mem (srcBase + 4 * i.val + 2), s.mem (srcBase + 4 * i.val + 3)⟩
  have hlen : es.length = count := List.length_ofFn
  have hes : HoldsIndexedEdges srcBase es s2.mem := fun i hi => by
    have hi' : i < count := hlen ▸ hi
    simp [es, hs2_eq]
  have h3 := framedTriple_iff_realization.mp
    (retagIndexedProg_spec (s := s2) h16 (hs2_eq ▸ hmem) hes
      (by rw [hs2_eq, hlen]; exact hsrc) (by rw [hs2_eq, hlen]; exact hfit12.of_le (by omega)))
  rw [hlen] at h3
  obtain ⟨_, _, hmod3, hob, hs3_fr, hwf3, hret3⟩ := h3
  set ob := (Memory.spec 0).clientResult s2 (retagIndexedProg (srcBase, count))
  set s3 := (Memory.spec 0).clientState s2 (retagIndexedProg (srcBase, count))
  have hes3 : HoldsIndexedEdges srcBase es s3.mem := hes.congr fun a ha1 ha2 => by
    have hlt : a < s2.frontier := by rw [hs2_eq]; rw [hlen] at ha2; omega
    exact hmod3.mem_eq_of_not_mem hlt (Set.notMem_empty _)
  let es' := es.mapIdx fun i e => (⟨e.u, e.v, e.weight, i⟩ : IndexedEdge (2 ^ w))
  have hlen' : es'.length = count := by simp [es', hlen]
  have h4 := framedTriple_iff_realization.mp
    (concatThreeProg_spec (b1 := srcBase) (b2 := ob) (b3 := srcBase)
      (L1 := es) (L2 := es') (L3 := ([] : List (IndexedEdge (2 ^ w))))
      hwf3 hes3 (by rw [hlen, hs3_fr, hs2_eq]; omega)
      hret3 (by rw [hlen', hob, hs3_fr])
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [List.length_nil, hs3_fr, hs2_eq]; omega)
      (by rw [hlen, hlen', List.length_nil, hs3_fr, hs2_eq]; exact hfit12.of_le (by omega)))
  rw [hlen, hlen', List.length_nil] at h4
  obtain ⟨_, _, hmod4, hcat, hs4_fr, hwf4, _⟩ := h4
  set s4 := (Memory.spec 0).clientState s3
    (concatThreeProg ⟨srcBase, count, ob, count, srcBase, 0⟩)
  have hret4 : HoldsIndexedEdges ob es' s4.mem := hret3.congr fun a ha1 ha2 => by
    have hlt : a < s3.frontier := by rw [hs3_fr]; rw [hlen'] at ha2; omega
    exact hmod4.mem_eq_of_not_mem hlt (Set.notMem_empty _)
  have h5 := framedTriple_iff_realization.mp
    (appendSelIdsProg_spec (srcBase := ob) (dstBase := dstBase) (dstOff := 0) (srcEs := es')
      (s := s4) h16 hwf4 hret4 (by rw [hlen', hs4_fr, hs3_fr, hob]; omega)
      (by rw [hlen', hs4_fr, hs3_fr, hs2_eq]; omega)
      (Or.inr (by rw [hlen', hob, hs2_eq]; omega))
      (by simpa [hlen'] using hfitm))
  obtain ⟨_, _, _, _, _, _, _⟩ := h5
  refine ⟨h16,
    ⟨h16, by rw [hs2_eq]; exact hsrc, by rw [hs2_eq]; exact hfit12.of_le (by omega)⟩,
    ⟨h16, by dsimp only; rw [hs3_fr, hs2_eq]; exact hfit12.of_le (by omega),
      by dsimp only; rw [hs3_fr, hs2_eq]; omega, by dsimp only; rw [hob, hs3_fr],
      by dsimp only; rw [hs3_fr, hs2_eq]; omega⟩,
    ⟨h16, by dsimp only; rw [hs4_fr, hob, hs3_fr]; omega,
      by dsimp only; rw [hs4_fr, hs3_fr, hs2_eq]; omega, by simpa using hfitm⟩⟩

private def liftPipelineProg (d : (CopyStride4Env × ℕ) × (LiftEdgesEnv × ℕ)) : Memory.Prog ℕ := do
  let _ ← copyStride4Prog (d.1.1, 0, d.1.2)
  let _ ← liftEdgesProg (d.2.1, 0, d.2.2)
  liftHRemProg (d.2.1.dstBase, d.1.1.dstBase, d.1.2)

private theorem realizes_liftPipelineProg : Realizes .exact
    liftPipelineProg
    (WordEncoding.encode (α := (CopyStride4Env × ℕ) × (LiftEdgesEnv × ℕ)))
    (WordEncoding.encode (α := ℕ))
    (fun w d s =>
      let s1 := (Memory.spec 0).clientState s (copyStride4Prog (d.1.1, 0, d.1.2))
      let s2 := (Memory.spec 0).clientState s1 (liftEdgesProg (d.2.1, 0, d.2.2))
      copyStride4ProgSafe w (d.1.1, 0, d.1.2) s ∧
      liftEdgesProgSafe w (d.2.1, 0, d.2.2) s1 ∧
      liftHRemProgSafe w (d.2.1.dstBase, d.1.1.dstBase, d.1.2) s2)
    (fun _ _ => 0) := by
  unfold liftPipelineProg
  realize [realizes_copyStride4Prog, realizes_liftEdgesProg, realizes_liftHRemProg]
  all_goals
    rcases h with ⟨h1, h2, h3⟩
    first | exact h1 | exact h2 | exact h3

example :
    let es : List (IndexedEdge 4) := [⟨0, 1, 5, 10⟩, ⟨1, 2, 7, 11⟩]
    let words := encodeIndexedEdges es ++ [0, 0]
    let s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
    let res := (Memory.spec 0).clientResult s₁ (prepPipelineProg ((0, 2), (8, 65536)))
    res = (16, 2, 18, 2) := by
  let es : List (IndexedEdge 4) := [⟨0, 1, 5, 10⟩, ⟨1, 2, 7, 11⟩]
  let words := encodeIndexedEdges es ++ [0, 0]
  have hinit := framedTriple_iff_realization.mp
    (initFromWordsProg_spec (w := 32) (words := words) wf_empty_32
      (fits32_of_lt (by simp [words, es, encodeIndexedEdges]))
      (fun v hv => fits32_of_lt (by simp [words, es, encodeIndexedEdges] at hv; omega)))
  obtain ⟨_, _, _, hb1, hfr1, hbl1, hwf1⟩ := hinit
  rw [hb1] at hbl1; dsimp only at hbl1
  set s₁ := (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)
  have hg := holdsList_get hbl1
  have hin : HoldsIndexedEdges 0 es s₁.mem := fun i hi => by
    rcases i with _ | _ | k
    · exact ⟨by simpa [words, es, encodeIndexedEdges] using hg 0 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 1 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 2 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 3 (by decide)⟩
    · exact ⟨by simpa [words, es, encodeIndexedEdges] using hg 4 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 5 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 6 (by decide),
        by simpa [words, es, encodeIndexedEdges] using hg 7 (by decide)⟩
    · simp [es] at hi
  obtain ⟨_, _, _, hs1, hk1⟩ := framedTriple_iff_realization.mp (natLog2Prog_spec 32 65536 s₁)
  obtain ⟨_, _, _, hs2, hk3⟩ := framedTriple_iff_realization.mp
    (iterLogProg_spec 32 3 65536 ((Memory.spec 0).clientState s₁ (natLog2Prog 65536)))
  set s2 := (Memory.spec 0).clientState ((Memory.spec 0).clientState s₁ (natLog2Prog 65536))
    (iterLogProg 3 65536)
  have hs2_eq : s2 = s₁ := hs2.trans hs1
  have h3 := framedTriple_iff_realization.mp
    (retagIndexedProg_spec (s := s2) (fits32_of_lt (by decide)) (hs2_eq ▸ hwf1) (hs2_eq ▸ hin)
      (by rw [hs2_eq, hfr1]; simp [words, es, encodeIndexedEdges])
      (fits32_of_lt (by rw [hs2_eq, hfr1]; simp [words, es, encodeIndexedEdges])))
  have hlen2 : es.length = 2 := rfl
  rw [hlen2] at h3
  obtain ⟨_, _, hmod3, hob, hs3_fr, hwf3, hret3⟩ := h3
  set ob := (Memory.spec 0).clientResult s2 (retagIndexedProg (0, 2))
  set s3 := (Memory.spec 0).clientState s2 (retagIndexedProg (0, 2))
  have hin3 : HoldsIndexedEdges 0 es s3.mem := hin.congr fun a ha1 ha2 =>
    (hmod3.mem_eq_of_not_mem (by
      rw [hs2_eq, hfr1]; simp [words, es, encodeIndexedEdges] at ha2 ⊢; omega)
      (Set.notMem_empty _)).trans (by rw [hs2_eq])
  let es' := es.mapIdx fun i e => (⟨e.u, e.v, e.weight, i⟩ : IndexedEdge 4)
  have hlen2' : es'.length = 2 := by simp [es', es]
  have h4 := framedTriple_iff_realization.mp
    (concatThreeProg_spec (b1 := 0) (b2 := ob) (b3 := 0)
      (L1 := es) (L2 := es') (L3 := ([] : List (IndexedEdge 4)))
      hwf3 hin3 (by rw [hs3_fr, hs2_eq, hfr1]; simp [words, es, encodeIndexedEdges])
      hret3 (by rw [hob, hs3_fr]; simp [es, es'])
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (by rw [hs3_fr, hs2_eq, hfr1]; simp [words, es, encodeIndexedEdges])
      (fits32_of_lt (by rw [hs3_fr, hs2_eq, hfr1]; simp [words, es, es', encodeIndexedEdges])))
  rw [hlen2, hlen2', List.length_nil] at h4
  obtain ⟨_, _, hmod4, hcat, hs4_fr, hwf4, _⟩ := h4
  set s4 := (Memory.spec 0).clientState s3 (concatThreeProg ⟨0, 2, ob, 2, 0, 0⟩)
  have hret4 : HoldsIndexedEdges ob es' s4.mem := hret3.congr fun a ha1 ha2 =>
    hmod4.mem_eq_of_not_mem (by rw [hs3_fr]; simp [es', es] at ha2; omega) (Set.notMem_empty _)
  have h5 := framedTriple_iff_realization.mp
    (appendSelIdsProg_spec (srcBase := ob) (dstBase := 8) (dstOff := 0) (srcEs := es')
      (s := s4) (fits32_of_lt (by decide)) hwf4 hret4
      (by rw [hs4_fr, hs3_fr, hob]; simp [es', es])
      (by rw [hs4_fr, hs3_fr, hs2_eq, hfr1]; simp [words, es, es', encodeIndexedEdges])
      (Or.inr (by rw [hob, hs2_eq, hfr1]; simp [words, es, es', encodeIndexedEdges]))
      (fits32_of_lt (by simp [es', es])))
  obtain ⟨_, _, _, hend, _, _, _⟩ := h5
  rw [hlen2'] at hend
  have hl1 : Nat.log 2 65536 = 16 := by decide
  have hl3 : Nat.iterLog 3 65536 = 2 := by
    have hp : (65536 : ℕ) = 2 ^ 16 := by decide
    have hd16 : (16 : ℕ) = 2 ^ 4 := by decide
    have hd4 : (4 : ℕ) = 2 ^ 2 := by decide
    simp only [Nat.iterLog_succ, Nat.iterLog_zero, hp, Nat.log_pow (by decide : 1 < 2),
      hd16, hd4]
  have hprog : (Memory.spec 0).clientResult s₁ (prepPipelineProg ((0, 2), (8, 65536))) =
      ((Memory.spec 0).clientResult s₁ (natLog2Prog 65536),
       (Memory.spec 0).clientResult ((Memory.spec 0).clientState s₁ (natLog2Prog 65536))
         (iterLogProg 3 65536),
       ((Memory.spec 0).clientResult s3 (concatThreeProg ⟨0, 2, ob, 2, 0, 0⟩)).1,
       (Memory.spec 0).clientResult s4 (appendSelIdsProg (⟨ob, 8⟩, 0, 2))) := by
    simp only [prepPipelineProg, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_pure]
    rfl
  change (Memory.spec 0).clientResult s₁ (prepPipelineProg ((0, 2), (8, 65536))) = (16, 2, 18, 2)
  rw [hprog, hk1, hk3, hcat, hs3_fr, hs2_eq, hfr1, hend, hl1, hl3]
  simp [words, es, encodeIndexedEdges]

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFBaseOps
