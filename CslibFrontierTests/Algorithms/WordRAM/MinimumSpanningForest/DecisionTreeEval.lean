/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Batch
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Client Tests for `DecisionTree.Eval` and `DecisionTree.Batch`

Exercises `evalDecisionTreeProg`, `evalDecisionTreeProg_spec`, `evalDecisionTreeBatchProg`,
`evalDecisionTreeBatchProg_spec`, `compactVertices_isSimple`, and
`compactVertices_isMinSpanningForest` across pure vertex lifting on `Fin 3 ↪ Fin 6`,
a concrete `r0 = 3` `HoldsDTTable` witness (`dtTable3`), and end-to-end single-component (`m = 0`,
`m = 1`, unsorted `K_3`) and 3-component `Fin 6` batch runs.
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreeEval

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.DisjointSet Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## 1. Pure Graph Lifting and Small-Graph Decision-Tree Helpers -/

private theorem small_simple_msf_univ {e : ℕ} {ends : Fin e → Sym2 (Fin 3)}
    (hsimp : IsSimple ends) (he : e ≤ 2) (p : Equiv.Perm (Fin e)) :
    Cslib.Multigraph.msf ends p Finset.univ = Finset.univ := by
  ext x; rw [iff_true_right (Finset.mem_univ x)]
  induction hx : ends x using Sym2.ind with
  | _ a b =>
    rw [Cslib.Multigraph.mem_msf_iff p hx]; refine ⟨Finset.mem_univ _, fun hc => ?_⟩
    have hne : a ≠ b := fun h => by
      subst h; exact (isSimple_iff _).mp hsimp |>.1 x (hx ▸ Sym2.mk_isDiag_iff.mpr rfl)
    by_cases h1 : e ≤ 1
    · have hemp : {f | f ∈ (Finset.univ : Finset (Fin e)) ∧ p f < p x} = ∅ := by
        ext f; simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and, Set.mem_empty_iff_false,
          iff_false, not_lt]; have : f = x := Fin.ext (by omega); subst this; exact le_rfl
      rw [hemp, Cslib.Multigraph.joins_empty_iff] at hc; exact hne hc
    · let x' : Fin e := ⟨1 - x.val, by omega⟩
      have hxx' : x' ≠ x := Fin.ne_of_val_ne (by dsimp [x']; omega)
      have hsub : {f | f ∈ (Finset.univ : Finset (Fin e)) ∧ p f < p x} ⊆ {x'} := fun f hf => by
        have hfx : f ≠ x := fun h => by subst h; exact lt_irrefl _ hf.2
        simp only [Set.mem_singleton_iff]; ext; dsimp [x']; have := Fin.val_ne_of_ne hfx; omega
      have hc' := hc.mono hsub
      rw [← Set.union_empty {x'}, ← Set.insert_eq, Cslib.Multigraph.joins_insert_iff] at hc'
      rcases hc' with h0 | ⟨c, d, hcd, hac, hdb⟩
      · rw [Cslib.Multigraph.joins_empty_iff] at h0; exact hne h0
      · rw [Cslib.Multigraph.joins_empty_iff] at hac hdb; subst hac hdb
        exact hxx' ((isSimple_iff _).mp hsimp |>.2 (hcd.trans hx.symm))

private theorem small_simple_optDepth_zero {e : ℕ} {ends : Fin e → Sym2 (Fin 3)}
    (hsimp : IsSimple ends) (he : e ≤ 2) :
    MSFDT.Correct ends (.leaf (Finset.univ : Finset (Fin e))) ∧ optDepth ends = 0 := by
  have hcorr : MSFDT.Correct ends (.leaf (Finset.univ : Finset (Fin e))) :=
    (MSFDT.correct_iff _ _).mpr fun p => (small_simple_msf_univ hsimp he p).symm
  exact ⟨hcorr, Nat.eq_zero_of_le_zero (optDepth_le_of_correct hcorr)⟩

private def k3Fin (i : Fin 3) : Fin (maskEdgePairs 3 7).length :=
  ⟨i.val, by have hi := i.isLt; interval_cases i.val <;> decide⟩

private theorem k3Fin_inj : Function.Injective k3Fin := fun _ _ h => Fin.ext (congrArg Fin.val h)

private def k3MaskTree : MSFDT (maskEdgePairs 3 7).length :=
  .node (k3Fin 0) (k3Fin 1)
    (.node (k3Fin 1) (k3Fin 2) (.leaf {k3Fin 0, k3Fin 1}) (.leaf {k3Fin 0, k3Fin 2}))
    (.node (k3Fin 0) (k3Fin 2) (.leaf {k3Fin 0, k3Fin 1}) (.leaf {k3Fin 1, k3Fin 2}))

private theorem fin3_cov {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (u : Fin (maskEdgePairs 3 7).length) : u = k3Fin a ∨ u = k3Fin b ∨ u = k3Fin c := by
  have hu : u.val < 3 := by
    have := u.isLt
    have : (maskEdgePairs 3 7).length = 3 := by decide
    omega
  have ha := Fin.val_ne_of_ne hab; have hb := Fin.val_ne_of_ne hac; have hc := Fin.val_ne_of_ne hbc
  have : u.val = a.val ∨ u.val = b.val ∨ u.val = c.val := by omega
  rcases this with h | h | h
  exacts [.inl (Fin.ext h), .inr (.inl (Fin.ext h)), .inr (.inr (Fin.ext h))]

private theorem k3_joins_other {x y z : Fin 3} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {S : Set (Fin (maskEdgePairs 3 7).length)} (hx : k3Fin x ∈ S) (hy : k3Fin y ∈ S) :
    ∃ a b : Fin 3, endsOfMask 3 7 (k3Fin z) = s(a, b) ∧
      Cslib.Multigraph.Joins (endsOfMask 3 7) S a b := by
  have he0 : endsOfMask 3 7 (k3Fin 0) = s(0, 1) := by decide
  have he1 : endsOfMask 3 7 (k3Fin 1) = s(0, 2) := by decide
  have he2 : endsOfMask 3 7 (k3Fin 2) = s(1, 2) := by decide
  fin_cases x <;> fin_cases y <;> fin_cases z <;> first
    | exact absurd rfl hxy | exact absurd rfl hxz | exact absurd rfl hyz
    | exact ⟨0, 1, by decide, (Cslib.Multigraph.Joins.of_mem hx he1).trans
        (Cslib.Multigraph.Joins.of_mem hy he2).symm⟩
    | exact ⟨0, 1, by decide, (Cslib.Multigraph.Joins.of_mem hy he1).trans
        (Cslib.Multigraph.Joins.of_mem hx he2).symm⟩
    | exact ⟨0, 2, by decide, (Cslib.Multigraph.Joins.of_mem hx he0).trans
        (Cslib.Multigraph.Joins.of_mem hy he2)⟩
    | exact ⟨0, 2, by decide, (Cslib.Multigraph.Joins.of_mem hy he0).trans
        (Cslib.Multigraph.Joins.of_mem hx he2)⟩
    | exact ⟨1, 2, by decide, (Cslib.Multigraph.Joins.of_mem hx he0).symm.trans
        (Cslib.Multigraph.Joins.of_mem hy he1)⟩
    | exact ⟨1, 2, by decide, (Cslib.Multigraph.Joins.of_mem hy he0).symm.trans
        (Cslib.Multigraph.Joins.of_mem hx he1)⟩

private theorem k3_msf_of_max (p : Equiv.Perm (Fin (maskEdgePairs 3 7).length))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : p (k3Fin i) < p (k3Fin k)) (hj : p (k3Fin j) < p (k3Fin k)) :
    Cslib.Multigraph.msf (endsOfMask 3 7) p Finset.univ = {k3Fin i, k3Fin j} := by
  have hsimp := (isSimple_iff _).mp (endsOfMask_isSimple 3 7)
  have hmem_of : ∀ {x y : Fin 3}, x ≠ y → x ≠ k → y ≠ k → p (k3Fin x) < p (k3Fin k) →
      k3Fin x ∈ Cslib.Multigraph.msf (endsOfMask 3 7) p Finset.univ :=
    fun {x y} hxy hxk hyk hxk_lt => by
      induction hx : endsOfMask 3 7 (k3Fin x) using Sym2.ind with
      | _ a b =>
        rw [Cslib.Multigraph.mem_msf_iff p hx]; refine ⟨Finset.mem_univ _, fun hc => ?_⟩
        have hne : a ≠ b := fun heq => by
          subst heq; exact hsimp.1 (k3Fin x) (hx ▸ Sym2.mk_isDiag_iff.mpr rfl)
        have hsub : {f | f ∈ (Finset.univ : Finset (Fin (maskEdgePairs 3 7).length)) ∧
            p f < p (k3Fin x)} ⊆ {k3Fin y} := fun f hf => by
          rcases fin3_cov hxy hxk hyk f with rfl | rfl | rfl
          · exact absurd hf.2 (lt_irrefl _)
          · rfl
          · exact absurd (lt_trans hxk_lt hf.2) (lt_irrefl _)
        have hc' := hc.mono hsub
        rw [← Set.union_empty {k3Fin y}, ← Set.insert_eq, Cslib.Multigraph.joins_insert_iff] at hc'
        rcases hc' with h0 | ⟨c, d, hcd, hac, hdb⟩
        · rw [Cslib.Multigraph.joins_empty_iff] at h0; exact hne h0
        · rw [Cslib.Multigraph.joins_empty_iff] at hac hdb; subst hac hdb
          exact (fun h => hxy (k3Fin_inj h)) (hsimp.2 (hx.trans hcd.symm))
  have hk_not : k3Fin k ∉ Cslib.Multigraph.msf (endsOfMask 3 7) p Finset.univ := by
    obtain ⟨a, b, hk_eq, hj_ab⟩ := k3_joins_other hij hik hjk
      (S := {f | f ∈ (Finset.univ : Finset (Fin (maskEdgePairs 3 7).length)) ∧
        p f < p (k3Fin k)})
      ⟨Finset.mem_univ _, hi⟩ ⟨Finset.mem_univ _, hj⟩
    rw [Cslib.Multigraph.mem_msf_iff p hk_eq]; exact fun h => h.2 hj_ab
  ext e; rw [Finset.mem_insert, Finset.mem_singleton]
  rcases fin3_cov hij hik hjk e with rfl | rfl | rfl
  · exact iff_of_true (hmem_of hij hik hjk hi) (.inl rfl)
  · exact iff_of_true (hmem_of hij.symm hjk hik hj) (.inr rfl)
  · exact iff_of_false hk_not
      (by rintro (h | h) <;> [exact hik (k3Fin_inj h).symm; exact hjk (k3Fin_inj h).symm])

private theorem k3MaskTree_correct : MSFDT.Correct (endsOfMask 3 7) k3MaskTree := by
  rw [MSFDT.correct_iff]; intro p; dsimp only [k3MaskTree, MSFTree.eval]
  have hflip : ∀ {a b : Fin 3}, a ≠ b → ¬ p (k3Fin a) < p (k3Fin b) →
      p (k3Fin b) < p (k3Fin a) := fun hab h =>
    lt_of_le_of_ne (Fin.le_def.mpr (not_lt.mp h)) fun eq =>
      absurd (k3Fin_inj (p.injective eq.symm)) hab
  split_ifs with h01 h12 h02
  · exact (k3_msf_of_max p (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
      (Fin.lt_def.mpr (lt_trans h01 h12)) (Fin.lt_def.mpr h12)).symm
  · exact (k3_msf_of_max p (i := 0) (j := 2) (k := 1) (by decide) (by decide) (by decide)
      (Fin.lt_def.mpr h01) (hflip (by decide) h12)).symm
  · exact (k3_msf_of_max p (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide)
      (Fin.lt_def.mpr h02) (lt_trans (hflip (by decide) h01) (Fin.lt_def.mpr h02))).symm
  · exact (k3_msf_of_max p (i := 1) (j := 2) (k := 0) (by decide) (by decide) (by decide)
      (hflip (by decide) h01) (hflip (by decide) h02)).symm

private theorem k3_optDepth_eq_two : optDepth (endsOfMask 3 7) = 2 := by
  refine le_antisymm (optDepth_le_of_correct k3MaskTree_correct) ?_
  by_contra hlt; have hle : optDepth (endsOfMask 3 7) ≤ 1 := by omega
  obtain ⟨T, hcorr, hd⟩ := exists_opt_msfDT (endsOfMask 3 7)
  rw [MSFDT.correct_iff] at hcorr; have hd1 : T.depth ≤ 1 := hd ▸ hle
  have htwo : ∃ a b : Finset (Fin (maskEdgePairs 3 7).length),
      ∀ p : Equiv.Perm (Fin (maskEdgePairs 3 7).length), T.eval p = a ∨ T.eval p = b := by
    cases T with
    | leaf ans => exact ⟨ans, ans, fun _ => .inl rfl⟩
    | node _ _ l r => cases l with
      | node _ _ _ _ => simp [MSFTree.depth] at hd1
      | leaf al => cases r with
        | node _ _ _ _ => simp [MSFTree.depth] at hd1
        | leaf ar => exact ⟨al, ar, fun p => by dsimp [MSFTree.eval]; split_ifs <;> simp⟩
  obtain ⟨a, b, hab⟩ := htwo
  let p1 : Equiv.Perm (Fin (maskEdgePairs 3 7).length) := Equiv.refl _
  let p2 : Equiv.Perm (Fin (maskEdgePairs 3 7).length) := Equiv.swap (k3Fin 1) (k3Fin 2)
  let p3 : Equiv.Perm (Fin (maskEdgePairs 3 7).length) := Equiv.swap (k3Fin 0) (k3Fin 2)
  have hv1 : T.eval p1 = {k3Fin 0, k3Fin 1} := (hcorr p1).trans (k3_msf_of_max p1 (i := 0)
    (j := 1) (k := 2) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hv2 : T.eval p2 = {k3Fin 0, k3Fin 2} := (hcorr p2).trans (k3_msf_of_max p2 (i := 0)
    (j := 2) (k := 1) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hv3 : T.eval p3 = {k3Fin 1, k3Fin 2} := (hcorr p3).trans (k3_msf_of_max p3 (i := 1)
    (j := 2) (k := 0) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hd12 : ({k3Fin 0, k3Fin 1} : Finset _) ≠ {k3Fin 0, k3Fin 2} := by decide
  have hd13 : ({k3Fin 0, k3Fin 1} : Finset _) ≠ {k3Fin 1, k3Fin 2} := by decide
  have hd23 : ({k3Fin 0, k3Fin 2} : Finset _) ≠ {k3Fin 1, k3Fin 2} := by decide
  rcases hab p1 with h1 | h1 <;> rcases hab p2 with h2 | h2 <;> rcases hab p3 with h3 | h3 <;>
    first | exact hd12 (hv1.symm.trans (h1.trans h2.symm |>.trans hv2))
          | exact hd13 (hv1.symm.trans (h1.trans h3.symm |>.trans hv3))
          | exact hd23 (hv2.symm.trans (h2.trans h3.symm |>.trans hv3))

/-! ## 2. Concrete `r0 = 3` Decision-Tree Table Witness -/

/-- Memory image of a complete optimal MSF decision-tree table for `r0 = 3` vertices. -/
@[expose] def dtTable3Mem : List ℕ :=
  [ 8, 11, 15, 19, 24, 28, 33, 38
  , 0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 2, 0, 0, 1, 3, 1, 0, 2, 1, 2, 0, 0, 2, 3, 2, 0, 1, 2, 3
  , 3, 2, 0, 1, 2, 0, 1, 1, 2, 0, 2, 3, 5, 3, 6 ]

/-- Word-RAM memory lookup function for the `r0 = 3` table (`dtTable3Mem`). -/
@[expose] def dtTable3 (a : ℕ) : ℕ := dtTable3Mem.getD a 0

/-- All entries of `dtTable3` lie strictly within address bound `53`. -/
theorem dtTable3_bounds : DTTableInBounds 3 0 53 dtTable3 := by
  rw [dtTableInBounds_iff]; refine ⟨by decide, fun mask hmask => ?_⟩
  have h8 : mask < 8 := by simpa using hmask
  interval_cases mask <;> decide

private theorem dtTable3_leaf_entry (mask : ℕ) (hlen : (maskEdgePairs 3 mask).length ≤ 2)
    (he : dtTable3 (dtTable3 (0 + mask)) = (maskEdgePairs 3 mask).length)
    (hd0 : dtTable3 (dtTable3 (0 + mask) + 1) = 0)
    (hsub : ∀ j : Fin (maskEdgePairs 3 mask).length,
      dtTable3 (dtTable3 (0 + mask) + 2 + j.val) =
        pairIdx (maskEdgePairs 3 mask)[j.val].1.val (maskEdgePairs 3 mask)[j.val].2.val)
    (hleaf : dtTable3 (dtTable3 (0 + mask) + 2 + (maskEdgePairs 3 mask).length +
        2 * (2 ^ 0 - 1) + (1 - 2 ^ 0)) =
      maskOfFinset (Finset.univ : Finset (Fin (maskEdgePairs 3 mask).length))) :
    let entryPtr := dtTable3 (0 + mask); let pairs := maskEdgePairs 3 mask
    let e := pairs.length; let d := dtTable3 (entryPtr + 1)
    dtTable3 entryPtr = e ∧ d = optDepth (endsOfMask 3 mask) ∧
    (∀ j (hj : j < e), dtTable3 (entryPtr + 2 + j) = pairIdx (pairs[j]).1.val (pairs[j]).2.val) ∧
    ∃ T : MSFDT e, T.IsComplete d ∧ T.Correct (endsOfMask 3 mask) ∧
      HoldsCompleteTree d (entryPtr + 2 + e)
        (entryPtr + 2 + e + 2 * (2 ^ d - 1)) d 1 dtTable3 T := by
  obtain ⟨hcorr, hopt⟩ := small_simple_optDepth_zero (endsOfMask_isSimple 3 mask) hlen
  refine ⟨he, hd0.trans hopt.symm, fun j hj => hsub ⟨j, hj⟩, .leaf Finset.univ,
    by rw [hd0]; exact MSFTree.isComplete_leaf, hcorr, ?_⟩
  rw [hd0, holdsCompleteTree_leaf]; exact ⟨by decide, by decide, hleaf⟩

/-- `dtTable3` satisfies `HoldsDTTable 3 0` across all 8 canonical graphs on `≤ 3` vertices. -/
theorem dtTable3_holds : HoldsDTTable 3 0 dtTable3 := by
  rw [holdsDTTable_iff]; intro mask hmask
  have h8 : mask < 8 := by simpa using hmask
  interval_cases mask <;> first
    | exact dtTable3_leaf_entry _ (by decide) (by decide) (by decide) (by decide) (by decide)
    | have hd2 : dtTable3 (dtTable3 (0 + 7) + 1) = 2 := by decide
      have hsub : ∀ j : Fin (maskEdgePairs 3 7).length,
          dtTable3 (dtTable3 (0 + 7) + 2 + j.val) =
            pairIdx (maskEdgePairs 3 7)[j.val].1.val (maskEdgePairs 3 7)[j.val].2.val := by decide
      refine ⟨by decide, hd2.trans k3_optDepth_eq_two.symm, fun j hj => hsub ⟨j, hj⟩,
        k3MaskTree, ?_, k3MaskTree_correct, ?_⟩
      · rw [hd2]
        simp only [k3MaskTree, MSFTree.isComplete_node, MSFTree.isComplete_leaf, k3Fin]; decide
      · rw [hd2]
        simp only [k3MaskTree, holdsCompleteTree_node, holdsCompleteTree_leaf, maskOfFinset, k3Fin]
        decide

private theorem dtTable3_fits (a : ℕ) : Fits 16 (dtTable3 a) := by
  by_cases ha : a < 53
  · interval_cases a <;> decide
  · have hlen : dtTable3Mem.length ≤ a := by
      simp only [dtTable3Mem, List.length_cons, List.length_nil]; omega
    rw [dtTable3, List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]; decide

/-! ## 3. Pure Vertex Compaction and MSF Lifting Bridges -/

private def lift3To6 : Fin 3 → Fin 6 | 0 => 1 | 1 => 4 | 2 => 5

private theorem lift3To6_inj : Function.Injective lift3To6 := fun a b h => by
  fin_cases a <;> fin_cases b <;> simp_all [lift3To6]

private theorem rel_edgePartition_contract_of_inj {n n' : ℕ} {f : Fin n → Fin n'}
    (hf : Function.Injective f) {M : List (WeightedEdge n ℕ)} {u v : Fin n}
    (h : (edgePartition (contractEdgeList f M)).rel (f u) (f v) = true) :
    (edgePartition M).rel u v = true := by
  rw [rel_edgePartition_iff_eqvGen] at h ⊢
  let R := fun a b : Fin n => ∃ e ∈ M, a = e.u ∧ b = e.v
  let R' := fun a' b' : Fin n' => ∃ e' ∈ contractEdgeList f M, a' = e'.u ∧ b' = e'.v
  have hinv : ∀ x' y' : Fin n', Relation.EqvGen R' x' y' →
      x' = y' ∨ ∃ a b : Fin n, f a = x' ∧ f b = y' ∧ Relation.EqvGen R a b := fun x' y' hxy => by
    induction hxy with
    | rel _ _ hr =>
      obtain ⟨_, he', rfl, rfl⟩ := hr; obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      exact .inr ⟨e.u, e.v, rfl, rfl, .rel _ _ ⟨e, he, rfl, rfl⟩⟩
    | refl _ => exact .inl rfl
    | symm _ _ _ ih =>
      rcases ih with rfl | ⟨a, b, rfl, rfl, hab⟩
      exacts [.inl rfl, .inr ⟨b, a, rfl, rfl, hab.symm⟩]
    | trans _ _ _ _ _ ih1 ih2 =>
      rcases ih1 with rfl | ⟨a1, b1, rfl, rfl, h1⟩; · exact ih2
      rcases ih2 with rfl | ⟨b2, c2, hbb, rfl, h2⟩; · exact .inr ⟨a1, b1, rfl, rfl, h1⟩
      cases hf hbb; exact .inr ⟨a1, c2, rfl, rfl, .trans _ _ _ h1 h2⟩
  rcases hinv (f u) (f v) h with heq | ⟨a, b, ha, hb, hab⟩
  · cases hf heq; exact .refl _
  · cases hf ha; cases hf hb; exact hab

private def k3Compact : List (IndexedEdge 3) := [⟨1, 0, 5, 10⟩, ⟨2, 1, 3, 11⟩, ⟨0, 2, 8, 12⟩]

private def k3Uncompacted : List (IndexedEdge 6) :=
  k3Compact.map fun e => ⟨lift3To6 e.u, lift3To6 e.v, e.weight, e.id⟩

private theorem k3_two_or_three_weight_le_8 {G' : List (WeightedEdge 3 ℕ)}
    (hsub : G'.Subperm (k3Compact.map IndexedEdge.toWeighted))
    (hrel01 : (edgePartition G').rel 0 1) (hrel12 : (edgePartition G').rel 1 2)
    (hw : totalWeight G' ≤ 8) : G'.length = 2 ∧ totalWeight G' = 8 := by
  obtain ⟨l, hp, hs⟩ := hsub
  have hnodup : G'.Nodup :=
    hp.nodup_iff.mp ((by decide : (k3Compact.map IndexedEdge.toWeighted).Nodup).sublist hs)
  have hmem : ∀ e ∈ G', e ∈ k3Compact.map IndexedEdge.toWeighted := fun _ he =>
    hs.subset (hp.mem_iff.mpr he)
  rcases G' with _ | ⟨e0, _ | ⟨e1, _ | ⟨e2, rest⟩⟩⟩
  · simp [edgePartition] at hrel01
  · have he0 := hmem e0 List.mem_cons_self
    simp only [k3Compact, IndexedEdge.toWeighted, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at he0
    rcases he0 with rfl | rfl | rfl <;> [revert hrel12; revert hrel01; revert hrel01] <;> decide
  · have he0 := hmem e0 List.mem_cons_self
    have he1 := hmem e1 (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [k3Compact, IndexedEdge.toWeighted, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at he0 he1
    have hne : e0 ≠ e1 := fun h => (List.nodup_cons.mp hnodup).1 (h ▸ List.mem_cons_self)
    rcases he0 with rfl | rfl | rfl <;> rcases he1 with rfl | rfl | rfl <;>
      first | exact absurd rfl hne | exact ⟨rfl, by decide⟩ | simp [totalWeight] at hw
  · have hw_each : ∀ x ∈ k3Compact.map IndexedEdge.toWeighted, 3 ≤ x.weight := by decide
    have hw0 := hw_each e0 (hmem e0 List.mem_cons_self)
    have hw1 := hw_each e1 (hmem e1 (List.mem_cons_of_mem _ List.mem_cons_self))
    have hw2 := hw_each e2 (hmem e2 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
    simp only [totalWeight, List.map_cons, List.sum_cons] at hw; omega

private theorem k3Compact_witness_msf :
    IsMinSpanningForest (k3Compact.map IndexedEdge.toWeighted)
      ([⟨1, 0, 5, 10⟩, ⟨2, 1, 3, 11⟩].map IndexedEdge.toWeighted) := by
  refine ⟨⟨by decide, by rw [isAcyclic_iff]; decide, ?_⟩, fun G' hG' => ?_⟩
  · have hpart : edgePartition ([⟨1, 0, 5, 10⟩, ⟨2, 1, 3, 11⟩].map IndexedEdge.toWeighted) =
        (Partition.discrete 3 |>.merge 1 0 |>.merge 2 1) := by
      simp [edgePartition, IndexedEdge.toWeighted]
    have hpartC : edgePartition (k3Compact.map IndexedEdge.toWeighted) =
        ((Partition.discrete 3 |>.merge 1 0 |>.merge 2 1).merge 0 2) := by
      simp [edgePartition, k3Compact, IndexedEdge.toWeighted]
    rw [hpart, hpartC]; exact (Partition.merge_of_rel (by decide)).symm
  · by_contra hlt
    have hw_lt : totalWeight G' < 8 := by
      have : totalWeight (([⟨1, 0, 5, 10⟩, ⟨2, 1, 3, 11⟩] : List (IndexedEdge 3)).map
          IndexedEdge.toWeighted) = 8 := by simp [totalWeight, IndexedEdge.toWeighted]
      omega
    have hrel01 : (edgePartition G').rel 0 1 := by rw [hG'.2.2]; decide
    have hrel12 : (edgePartition G').rel 1 2 := by rw [hG'.2.2]; decide
    have ⟨_, heq8⟩ := k3_two_or_three_weight_le_8 hG'.1 hrel01 hrel12 hw_lt.le; omega

example : IsSimple (edgeEnds (k3Compact.map IndexedEdge.toWeighted)) :=
  compactVertices_isSimple (lift := lift3To6) (es := k3Uncompacted) rfl
    ((isSimple_iff _).mpr ⟨fun i => by fin_cases i <;> decide,
      fun a b h => by fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)⟩)

example :
    let msf3 : List (IndexedEdge 3) := [⟨1, 0, 5, 10⟩, ⟨2, 1, 3, 11⟩]
    IsMinSpanningForest (k3Uncompacted.map IndexedEdge.toWeighted)
      (contractEdgeList lift3To6 (msf3.map IndexedEdge.toWeighted)) :=
  compactVertices_isMinSpanningForest lift3To6_inj rfl k3Compact_witness_msf

/-! ## 4. End-to-End `evalDecisionTreeProg_spec` Runs (`w = 16`) -/

private theorem k3_msf_sublist_summary {F : List (IndexedEdge 3)} (hsub : F.Subperm k3Compact)
    (hmsf : IsMinSpanningForest (k3Compact.map IndexedEdge.toWeighted)
      (F.map IndexedEdge.toWeighted)) :
    F.length = 2 ∧ (F.map IndexedEdge.weight).sum = 8 := by
  have hmin : totalWeight (F.map IndexedEdge.toWeighted) ≤ 8 := by
    simpa [totalWeight, IndexedEdge.toWeighted] using hmsf.2 _ k3Compact_witness_msf.1
  have hrel01 : (edgePartition (F.map IndexedEdge.toWeighted)).rel 0 1 := by
    rw [hmsf.1.2.2]; decide
  have hrel12 : (edgePartition (F.map IndexedEdge.toWeighted)).rel 1 2 := by
    rw [hmsf.1.2.2]; decide
  obtain ⟨l, hp, hs⟩ := hsub
  obtain ⟨hlen, htw⟩ := k3_two_or_three_weight_le_8 ⟨l.map _, hp.map _, hs.map _⟩
    hrel01 hrel12 hmin
  exact ⟨by simpa using hlen,
    by simpa [totalWeight, List.map_map, Function.comp_def, IndexedEdge.toWeighted] using htw⟩

private def testMem (xs : List ℕ) (a : ℕ) : ℕ :=
  if a < 53 then dtTable3 a else xs.getD (a - 53) 0

private theorem testMem_fits {xs : List ℕ} (hxs : ∀ x ∈ xs, Fits 16 x) (a : ℕ) :
    Fits 16 (testMem xs a) := by
  by_cases ha : a < 53
  · simp only [testMem, ha, ↓reduceIte]; exact dtTable3_fits a
  · simp only [testMem, ha, ↓reduceIte]
    by_cases hhi : a - 53 < xs.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hhi]
      exact hxs _ (List.getElem_mem hhi)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; decide

private theorem testMem_table (xs : List ℕ) :
    HoldsDTTable 3 0 (testMem xs) ∧ DTTableInBounds 3 0 53 (testMem xs) :=
  have hs : ∀ a < 53, testMem xs a = dtTable3 a := fun a ha => by simp [testMem, ha]
  ⟨dtTable3_holds.congr dtTable3_bounds hs, dtTable3_bounds.mono le_rfl hs⟩

private def edge1List : List ℕ := [2, 0, 7, 42]
private def k3List : List ℕ := [1, 0, 5, 10, 2, 1, 3, 11, 0, 2, 8, 12]

example :
    let s : Memory.State := ⟨dtTable3, 60⟩; let q : DTQuery := ⟨0, 3, 0, 53, 56⟩
    let res := (Memory.spec 0).clientResult s (evalDecisionTreeProg q)
    let s' := (Memory.spec 0).clientState s (evalDecisionTreeProg q)
    evalDecisionTreeProgSafe 16 q s ∧
    res = 0 ∧ s'.frontier ≤ 63 ∧ (∀ a < 60, s'.mem a = dtTable3 a) := by
  intro s q res s'
  have hspec := @evalDecisionTreeProg_spec 16 3 53 q [] s
    (by decide) ⟨by decide, dtTable3_fits⟩ (by decide) rfl
    ((isSimple_iff _).mpr ⟨fun i => Fin.elim0 i, fun a => Fin.elim0 a⟩)
    (fun _ hi => by simp at hi) (by decide) (by decide) (.inl (by decide))
    dtTable3_holds dtTable3_bounds (by decide) (fun a ha => by dsimp only [q]; omega) (by decide)
  obtain ⟨_, _, hmod, hsafe, _, hfr, _, F, hF_len, hF_sub, _, _⟩ :=
    framedTriple_iff_realization.mp hspec
  have hF_nil : F = [] := List.eq_nil_iff_forall_not_mem.mpr fun _ h => by
    have := hF_sub.subset h; simp at this
  exact ⟨hsafe, by dsimp only [res]; rw [← hF_len, hF_nil]; rfl, by simpa [s, q] using hfr,
    fun a ha => hmod.mem_eq_of_not_mem ha (by simp only [Set.mem_Ico, List.length_nil]; omega)⟩

example :
    let mem := testMem edge1List; let s : Memory.State := ⟨mem, 65⟩
    let q : DTQuery := ⟨0, 3, 1, 53, 57⟩
    let res := (Memory.spec 0).clientResult s (evalDecisionTreeProg q)
    let s' := (Memory.spec 0).clientState s (evalDecisionTreeProg q)
    evalDecisionTreeProgSafe 16 q s ∧ res = 1 ∧
    s'.mem 57 = 2 ∧ s'.mem 58 = 0 ∧ s'.mem 59 = 7 ∧ s'.mem 60 = 42 ∧
    (∀ a < 57, s'.mem a = mem a) := by
  intro mem s q res s'
  let e0 : IndexedEdge 3 := ⟨2, 0, 7, 42⟩; obtain ⟨htab, hbnd⟩ := testMem_table edge1List
  have hspec := @evalDecisionTreeProg_spec 16 3 53 q [e0] s
    (by decide) ⟨by decide, testMem_fits (by decide)⟩ (by decide) rfl
    ((isSimple_iff _).mpr ⟨fun i => by fin_cases i; decide,
      fun a b _ => by fin_cases a; fin_cases b; rfl⟩)
    (fun i hi => by
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp [mem, s, q, testMem, edge1List, e0])
    (by decide) (by decide) (.inl (by decide))
    htab hbnd (by decide) (fun a ha => by dsimp only [q]; omega) (by decide)
  obtain ⟨_, _, hmod, hsafe, _, _, _, F, hF_len, hF_sub, hF_holds, hF_msf⟩ :=
    framedTriple_iff_realization.mp hspec
  have hF_eq : F = [e0] := by
    have hm := hF_msf.1.2.2; rcases F with _ | ⟨x, rest⟩
    · simp only [edgePartition, List.map_nil, edgePartitionFrom_nil] at hm
      have hrel : (Partition.discrete 3).rel 2 0 = true := by rw [hm]; decide
      revert hrel; decide
    · have hlen := hF_sub.length_le; rw [List.length_cons, List.length_singleton] at hlen
      have hr : rest = [] := List.eq_nil_of_length_eq_zero (by omega); subst hr
      have hx := hF_sub.subset List.mem_cons_self; simp only [List.mem_singleton] at hx
      subst hx; rfl
  rw [hF_eq] at hF_len hF_holds; obtain ⟨h0, h1, h2, h3⟩ := hF_holds 0 (by simp)
  exact ⟨hsafe, hF_len.symm, h0, h1, h2, h3, fun a ha =>
    hmod.mem_eq_of_not_mem (by dsimp only [s]; omega) (by simp only [Set.mem_Ico, q]; omega)⟩

example :
    let mem := testMem k3List; let s : Memory.State := ⟨mem, 80⟩
    let q : DTQuery := ⟨0, 3, 3, 53, 65⟩
    let res := (Memory.spec 0).clientResult s (evalDecisionTreeProg q)
    let s' := (Memory.spec 0).clientState s (evalDecisionTreeProg q)
    evalDecisionTreeProgSafe 16 q s ∧ res = 2 ∧
    (∃ F : List (IndexedEdge 3),
      F.length = 2 ∧ (F.map IndexedEdge.weight).sum = 8 ∧ HoldsIndexedEdges 65 F s'.mem) ∧
    (∀ a < 65, s'.mem a = mem a) := by
  intro mem s q res s'; obtain ⟨htab, hbnd⟩ := testMem_table k3List
  have hsimp3 : IsSimple (edgeEnds (k3Compact.map IndexedEdge.toWeighted)) := (isSimple_iff _).mpr
    ⟨fun i => by fin_cases i <;> decide,
     fun a b h => by fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)⟩
  have hspec := @evalDecisionTreeProg_spec 16 3 53 q k3Compact s
    (by decide) ⟨by decide, testMem_fits (by decide)⟩ (by decide) rfl hsimp3
    (fun i hi => by
      have hi3 : i < 3 := by simpa [k3Compact] using hi
      interval_cases i <;> simp [mem, s, q, testMem, k3Compact, k3List])
    (by decide) (by decide) (.inl (by decide))
    htab hbnd (by decide) (fun a ha => by dsimp only [q]; omega) (by decide)
  obtain ⟨_, _, hmod, hsafe, _, _, _, F, hF_len, hF_sub, hF_holds, hF_msf⟩ :=
    framedTriple_iff_realization.mp hspec
  obtain ⟨hF2, hFw8⟩ := k3_msf_sublist_summary hF_sub hF_msf
  exact ⟨hsafe, hF_len.symm.trans hF2, ⟨F, hF2, hFw8, hF_holds⟩, fun a ha =>
    hmod.mem_eq_of_not_mem (by dsimp only [s]; omega) (by simp only [Set.mem_Ico, q]; omega)⟩

/-! ## 5. End-to-End `evalDecisionTreeBatchProg_spec` Runs (`w = 16`) -/

private def batchList : List ℕ :=
  [ 4, 1, 5, 10, 5, 4, 3, 11, 1, 5, 8, 12, 2, 0, 7, 20, 53, 3, 65, 0, 65, 1 ]
private def batchCs : List (List (IndexedEdge 6)) := [k3Uncompacted, [], [⟨2, 0, 7, 20⟩]]
private def batchEdgeBases : List ℕ := [53, 65, 65]

private theorem subperm_of_map {α β : Type*} (f : α → β) {xs : List β} {ys : List α}
    (hsub : xs.Subperm (ys.map f)) : ∃ zs : List α, zs.Subperm ys ∧ xs = zs.map f := by
  have hp : ∀ {as bs : List β} {l : List α}, as.Perm bs → as = l.map f →
      ∃ zs : List α, l.Perm zs ∧ bs = zs.map f := by
    intro as bs l h; induction h generalizing l with
    | nil =>
      cases l with
      | nil => intro _; exact ⟨[], .nil, rfl⟩
      | cons _ _ => simp_all
    | cons _ _ ih => cases l with | nil => simp | cons y l' =>
      simp only [List.map_cons, List.cons.injEq]; rintro ⟨rfl, rfl⟩
      obtain ⟨zs, hzp, rfl⟩ := ih rfl; exact ⟨y :: zs, hzp.cons y, rfl⟩
    | swap _ _ _ => cases l with | nil => simp | cons y₁ l'' => cases l'' with
      | nil => simp | cons y₂ l' =>
        simp only [List.map_cons, List.cons.injEq]; rintro ⟨rfl, rfl, rfl⟩
        exact ⟨y₂ :: y₁ :: l', .swap y₂ y₁ l', rfl⟩
    | trans _ _ ih1 ih2 =>
      intro hl; obtain ⟨zs, hzp, rfl⟩ := ih1 hl; obtain ⟨ws, hwp, rfl⟩ := ih2 rfl
      exact ⟨ws, hzp.trans hwp, rfl⟩
  obtain ⟨l, hpe, hs⟩ := hsub; obtain ⟨l', hs', hm⟩ := List.sublist_map_iff.mp hs
  obtain ⟨zs, hzp, rfl⟩ := hp hpe hm; exact ⟨zs, ⟨l', hzp, hs'⟩, rfl⟩

example :
    let s : Memory.State := ⟨dtTable3, 60⟩; let d : DTBatchArgs := ⟨0, 3, 4, 0, 53⟩
    let res := (Memory.spec 0).clientResult s (evalDecisionTreeBatchProg d)
    let s' := (Memory.spec 0).clientState s (evalDecisionTreeBatchProg d)
    evalDecisionTreeBatchProgSafe 16 d s ∧ res.2 = 0 ∧ (∀ a < 60, s'.mem a = dtTable3 a) := by
  intro s d res s'
  have hspec := @evalDecisionTreeBatchProg_spec 16 53 d [] [] s
    (by decide) ⟨by decide, dtTable3_fits⟩ rfl rfl (fun _ hi => by simp at hi) (by decide)
    (fun _ hi => by simp at hi) (fun _ hi => by simp at hi) (fun _ hi => by simp at hi)
    dtTable3_holds dtTable3_bounds (by decide) (by decide)
  obtain ⟨_, _, hmod, hsafe, _, _, _, Fs, hFs_len, _, hflat_len, _⟩ :=
    framedTriple_iff_realization.mp hspec
  have hFs_nil : Fs = [] := List.eq_nil_of_length_eq_zero hFs_len; subst hFs_nil
  exact ⟨hsafe, hflat_len.symm, fun a ha => hmod.mem_eq_of_not_mem ha (Set.notMem_empty a)⟩

example :
    let mem := testMem batchList; let s : Memory.State := ⟨mem, 80⟩
    let d : DTBatchArgs := ⟨0, 3, 6, 3, 69⟩
    let res := (Memory.spec 0).clientResult s (evalDecisionTreeBatchProg d)
    let s' := (Memory.spec 0).clientState s (evalDecisionTreeBatchProg d)
    evalDecisionTreeBatchProgSafe 16 d s ∧ res.2 = 3 ∧
    (∃ Fs : List (List (IndexedEdge 6)),
      Fs.length = 3 ∧ Fs.flatten.length = 3 ∧
      (Fs.flatten.map IndexedEdge.weight).sum = 15 ∧ HoldsIndexedEdges res.1 Fs.flatten s'.mem) ∧
    (∀ a < 80, s'.mem a = mem a) := by
  intro mem s d res s'; obtain ⟨htab, hbnd⟩ := testMem_table batchList
  have hsimp0 : IsSimple (edgeEnds (k3Uncompacted.map IndexedEdge.toWeighted)) :=
    (isSimple_iff _).mpr ⟨fun i => by fin_cases i <;> decide,
      fun a b h => by fin_cases a <;> fin_cases b <;> first | rfl | exact absurd h (by decide)⟩
  have hsimp2 : IsSimple (edgeEnds (([⟨2, 0, 7, 20⟩] : List (IndexedEdge 6)).map
      IndexedEdge.toWeighted)) := (isSimple_iff _).mpr
    ⟨fun i => by fin_cases i; decide, fun a b _ => by fin_cases a; fin_cases b; rfl⟩
  have hspec := @evalDecisionTreeBatchProg_spec 16 53 d batchCs batchEdgeBases s
    (by decide) ⟨by decide, testMem_fits (by decide)⟩ rfl rfl
    (fun i hi => by
      have : i < 3 := by simpa [batchCs] using hi
      interval_cases i <;> decide +revert)
    (by decide)
    (fun i hi => by
      have : i < 3 := by simpa [batchCs] using hi
      interval_cases i
      · exact ⟨fun j hj => by
          have : j < 3 := by simpa [batchCs, k3Uncompacted, k3Compact] using hj
          interval_cases j <;> decide +revert,
          by simp [s, batchEdgeBases, batchCs, k3Uncompacted, k3Compact]⟩
      · exact ⟨fun _ hj => by simp [batchCs] at hj, by simp [s, batchEdgeBases, batchCs]⟩
      · exact ⟨fun j hj => by
          have : j < 1 := by simpa [batchCs] using hj
          interval_cases j
          decide +revert, by simp [s, batchEdgeBases, batchCs]⟩)
    (fun i hi => by
      have : i < 3 := by simpa [batchCs] using hi
      interval_cases i
      · exact hsimp0
      · exact (isSimple_iff _).mpr ⟨fun j => Fin.elim0 j, fun a => Fin.elim0 a⟩
      · exact hsimp2)
    (fun i hi => by
      have : i < 3 := by simpa [batchCs] using hi
      interval_cases i
      · exact ⟨{1, 4, 5}, by decide, by decide +revert⟩
      · exact ⟨∅, by decide, fun _ h => by simp [batchCs] at h⟩
      · exact ⟨{0, 2}, by decide, by simp [batchCs]⟩)
    htab hbnd (by decide) (by decide)
  obtain ⟨_, _, hmod, hsafe, _, _, _, Fs, hFs_len, hflat_holds, hflat_len, hFs_msf⟩ :=
    framedTriple_iff_realization.mp hspec
  rcases Fs with _ | ⟨F0, _ | ⟨F1, _ | ⟨F2, rest⟩⟩⟩
  · simp [batchCs] at hFs_len
  · simp [batchCs] at hFs_len
  · simp [batchCs] at hFs_len
  have hrest : rest = [] := by simpa [batchCs] using hFs_len
  subst hrest
  obtain ⟨h0_sub, h0_msf⟩ := hFs_msf 0 (by decide) (by simp)
  obtain ⟨h1_sub, _⟩ := hFs_msf 1 (by decide) (by simp)
  obtain ⟨h2_sub, h2_msf⟩ := hFs_msf 2 (by decide) (by simp)
  have hF1_nil : F1 = [] := List.eq_nil_iff_forall_not_mem.mpr fun _ h => by
    have := h1_sub.subset h; simp [batchCs] at this
  have hF2_eq : F2 = [⟨2, 0, 7, 20⟩] := by
    have hm := h2_msf.1.2.2; rcases F2 with _ | ⟨x, r⟩
    · simp only [edgePartition, edgePartitionFrom, batchCs, List.getElem_cons_zero,
        List.getElem_cons_succ, List.map_nil, List.foldl_nil] at hm
      have hrel6 : (Partition.discrete 6).rel 2 0 = true := by rw [hm]; decide
      revert hrel6; decide
    · have hlen := h2_sub.length_le; simp only [batchCs, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_cons, List.length_nil] at hlen
      have hr : r = [] := List.eq_nil_of_length_eq_zero (by omega); subst hr
      have hx := h2_sub.subset List.mem_cons_self
      simp only [batchCs, List.getElem_cons_zero, List.getElem_cons_succ, List.mem_singleton] at hx
      subst hx; rfl
  have h0_sub' : F0.Subperm k3Uncompacted := by simpa [batchCs] using h0_sub
  obtain ⟨F0', hF0'_sub, rfl⟩ :=
    subperm_of_map (fun e : IndexedEdge 3 =>
      (⟨lift3To6 e.u, lift3To6 e.v, e.weight, e.id⟩ : IndexedEdge 6)) h0_sub'
  let F0 : List (IndexedEdge 6) := F0'.map fun e => ⟨lift3To6 e.u, lift3To6 e.v, e.weight, e.id⟩
  have hmsf_lift := compactVertices_isMinSpanningForest lift3To6_inj rfl
    k3Compact_witness_msf
  have hmin_w : totalWeight (F0'.map IndexedEdge.toWeighted) ≤ 8 := by
    simpa [totalWeight, contractEdgeList, contractEdge, List.map_map, Function.comp_def,
      IndexedEdge.toWeighted] using h0_msf.2 _ hmsf_lift.1
  have hpart0 := h0_msf.1.2.2
  have hrel_lift : ∀ {u v : Fin 3},
      (edgePartition (F0.map IndexedEdge.toWeighted)).rel (lift3To6 u) (lift3To6 v) = true →
      (edgePartition (F0'.map IndexedEdge.toWeighted)).rel u v = true := fun h =>
    rel_edgePartition_contract_of_inj lift3To6_inj (by
      simpa [F0, contractEdgeList, contractEdge, List.map_map, Function.comp_def,
        IndexedEdge.toWeighted] using h)
  have hrel01 : (edgePartition (F0'.map IndexedEdge.toWeighted)).rel 0 1 :=
    hrel_lift (by dsimp only [F0, lift3To6]; erw [hpart0]; decide)
  have hrel12 : (edgePartition (F0'.map IndexedEdge.toWeighted)).rel 1 2 :=
    hrel_lift (by dsimp only [F0, lift3To6]; erw [hpart0]; decide)
  obtain ⟨l0, hp0, hs0⟩ := hF0'_sub
  obtain ⟨hF0'_2, hF0'_tw⟩ := k3_two_or_three_weight_le_8
    ⟨l0.map _, hp0.map _, hs0.map _⟩ hrel01 hrel12 hmin_w
  have hF0'_2' : F0'.length = 2 := by simpa using hF0'_2
  have hF0'_sum : (F0'.map IndexedEdge.weight).sum = 8 := by
    simpa [totalWeight, List.map_map, Function.comp_def, IndexedEdge.toWeighted] using hF0'_tw
  have hflat_3 : ([F0, F1, F2].flatten).length = 3 := by simp [F0, hF1_nil, hF2_eq, hF0'_2']
  have hflat_w : (([F0, F1, F2].flatten).map IndexedEdge.weight).sum = 15 := by
    simp [F0, hF1_nil, hF2_eq, List.map_map, Function.comp_def, hF0'_sum]
  exact ⟨hsafe, hflat_len.symm.trans hflat_3, ⟨_, rfl, hflat_3, hflat_w, hflat_holds⟩,
    fun a ha => hmod.mem_eq_of_not_mem ha (Set.notMem_empty a)⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreeEval
