/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Base Combinatorial Bounds and Word-RAM Subroutines for Optimal MSF

Combinatorial and Word-RAM base helpers toward Theorem 5.8 of [PettieRamachandran2002] (`#8624`):

- Combinatorial bounds (`dtPrecompCost_iterLog_le_of_ge_24`, `card_le_two_mul_of_noIsolated`,
  `isAcyclic_cons_iff`, `edgePartition_contractEdgeList_rel_inj`,
  `isAcyclic_of_contractEdgeList_injective`, `isAcyclic_length_le_finset_sub_one`, and
  `sum_verts_sub_one_le`) bridging `Nat.iterLog 3`, `dtPrecompCost`, and `IsAcyclic`.
- Four faithfully word-encoded argument/environment structures (`AppendSelEnv`, `CopyStride4Env`,
  `ConcatThreeArgs`, `LiftEdgesEnv`).
- Six `Memory.Prog` subroutines with `Realizes .exact` (`work = 0`) and `Memory.FramedTriple`
  specifications: `appendSelIdsProg`, `retagIndexedProg`, `copyStride4Prog`, `concatThreeProg`
  (via `RecordOps.concatRecordsProg`), `liftEdgesProg`, and `liftHRemProg`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.AppendSelEnv`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.CopyStride4Env`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.ConcatThreeArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.LiftEdgesEnv`: word-encoded argument bundles.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.appendSelIdsProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.appendSelIdsProgSafe`: append selected edge IDs.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.retagIndexedProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.retagIndexedProgSafe`: retag edge IDs `0..m-1`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.copyStride4Prog`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.copyStride4ProgSafe`: stride-4 edge array copy.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.concatThreeProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.concatThreeProgSafe`: 3-way stride-4 concat.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftEdgesProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftEdgesProgSafe`: lift local edges to global.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftHRemProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftHRemProgSafe`: gather `H_rem` edges by ID.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.dtPrecompCost_iterLog_le_of_ge_24`: precomputation
  budget `dtPrecompCost (Nat.iterLog 3 n₀) ≤ n₀` when `24 ≤ Nat.iterLog 3 n₀`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.card_le_two_mul_of_noIsolated`: `n ≤ 2 * m` when
  no vertex is isolated.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.isAcyclic_cons_iff`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.edgePartition_contractEdgeList_rel_inj`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.isAcyclic_of_contractEdgeList_injective`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.isAcyclic_length_le_finset_sub_one`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.sum_verts_sub_one_le`: acyclicity bounds.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_appendSelIdsProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.appendSelIdsProg_spec`: certificates for
  `appendSelIdsProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_retagIndexedProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.retagIndexedProg_spec`: certificates for
  `retagIndexedProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_copyStride4Prog`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.copyStride4Prog_spec`: certificates for
  `copyStride4Prog`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_concatThreeProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.concatThreeProg_spec`: certificates for
  `concatThreeProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_liftEdgesProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftEdgesProg_spec`: certificates for
  `liftEdgesProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_liftHRemProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.liftHRemProg_spec`: certificates for
  `liftHRemProg`.

## References

* [Pettie and Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Complexity, Acyclicity, and Combinatorial Helpers -/

/-- When `24 ≤ Nat.iterLog 3 n₀`, the double-exponential decision-tree precomputation target
`dtPrecompCost (Nat.iterLog 3 n₀)` fits inside `n₀`. -/
theorem dtPrecompCost_iterLog_le_of_ge_24 {n₀ : ℕ} (hr : 24 ≤ Nat.iterLog 3 n₀) :
    dtPrecompCost (Nat.iterLog 3 n₀) ≤ n₀ := by
  set r := Nat.iterLog 3 n₀
  have hL2_pos : 0 < Nat.log 2 (Nat.log 2 n₀) := by
    by_contra h0
    have hz : Nat.log 2 (Nat.log 2 n₀) = 0 := by omega
    have hr0 : r = 0 := by simp [r, Nat.iterLog_succ, hz]
    omega
  have hL1_pos : 0 < Nat.log 2 n₀ := by
    by_contra h0
    have hz : Nat.log 2 n₀ = 0 := by omega
    simp [hz] at hL2_pos
  have hn₀_pos : 0 < n₀ := by
    by_contra h0
    have hz : n₀ = 0 := by omega
    simp [hz] at hL1_pos
  have hp1 : 2 ^ r ≤ Nat.log 2 (Nat.log 2 n₀) :=
    Nat.pow_log_le_self 2 (Nat.ne_of_gt hL2_pos)
  have hp2 : 2 ^ (2 ^ r) ≤ Nat.log 2 n₀ :=
    (Nat.pow_le_pow_right (by decide) hp1).trans (Nat.pow_log_le_self 2 (Nat.ne_of_gt hL1_pos))
  have hp3 : 2 ^ (2 ^ (2 ^ r)) ≤ n₀ :=
    (Nat.pow_le_pow_right (by decide) hp2).trans (Nat.pow_log_le_self 2 (Nat.ne_of_gt hn₀_pos))
  have hpoly : 4 * r ^ 4 + 16 ≤ 2 ^ r := by
    have hgen : ∀ k, 24 ≤ k → 4 * k ^ 4 + 16 ≤ 2 ^ k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => decide
      | succ m hm ih =>
        have h1 : 24 * m ^ 3 ≤ m ^ 4 :=
          calc 24 * m ^ 3 ≤ m * m ^ 3 := Nat.mul_le_mul_right _ hm
          _ = m ^ 4 := by ring
        have h2 : 24 * m ^ 2 ≤ m ^ 3 :=
          calc 24 * m ^ 2 ≤ m * m ^ 2 := Nat.mul_le_mul_right _ hm
          _ = m ^ 3 := by ring
        have h3 : 24 * m ≤ m ^ 2 :=
          calc 24 * m ≤ m * m := Nat.mul_le_mul_right _ hm
          _ = m ^ 2 := by ring
        have hexp : (m + 1) ^ 4 = m ^ 4 + 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1 := by ring
        have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
        omega
    exact hgen r hr
  have hr_gt1 : ¬ (r ≤ 1) := by omega
  simp only [dtPrecompCost, hr_gt1, ↓reduceIte]
  exact (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hpoly)).trans hp3

/-- If every vertex in `Fin n` is incident to at least one edge in `es`, then
`n ≤ 2 * es.length`. -/
theorem card_le_two_mul_of_noIsolated {n : ℕ} (es : List (IndexedEdge n))
    (hno : ∀ y : Fin n, ∃ e ∈ es, e.u = y ∨ e.v = y) : n ≤ 2 * es.length := by
  have hsub : (Finset.univ : Finset (Fin n)) ⊆
      es.foldr (fun e acc => insert e.u (insert e.v acc)) ∅ := by
    intro y _
    obtain ⟨e, he, hy⟩ := hno y
    clear hno
    induction es with
    | nil => simp at he
    | cons a rest ih =>
      simp only [List.foldr_cons, Finset.mem_insert]
      rcases List.mem_cons.mp he with rfl | hmem
      · rcases hy with rfl | rfl <;> simp
      · exact Or.inr (Or.inr (ih hmem))
  have hcard : ∀ l : List (IndexedEdge n),
      (l.foldr (fun e acc => insert e.u (insert e.v acc)) (∅ : Finset (Fin n))).card ≤
        2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih =>
      simp only [List.foldr_cons, List.length_cons]
      have h1 := Finset.card_insert_le a.u (insert a.v (rest.foldr
        (fun e acc => insert e.u (insert e.v acc)) ∅))
      have h2 := Finset.card_insert_le a.v (rest.foldr
        (fun e acc => insert e.u (insert e.v acc)) ∅)
      omega
  simpa [Fintype.card_fin] using (Finset.card_le_card hsub).trans (hcard es)

/-- `e :: L` is acyclic iff `e`'s endpoints lie in distinct components of `L` and `L` is
acyclic. -/
theorem isAcyclic_cons_iff {n : ℕ} {W : Type} (e : WeightedEdge n W)
    (L : List (WeightedEdge n W)) :
    IsAcyclic (e :: L) ↔ (edgePartition L).rel e.u e.v = false ∧ IsAcyclic L := by
  have hperm : (e :: L).Perm (L ++ [e]) := by
    simpa using (List.perm_append_singleton e L).symm
  rw [Perm.isAcyclic_iff hperm, isAcyclic_iff, isAcyclic_iff, edgePartition,
    edgePartitionFrom_append, edgePartitionFrom_cons, edgePartitionFrom_nil, List.length_append,
    List.length_singleton]
  change ((edgePartition L).merge e.u e.v).numComponents + (L.length + 1) = n ↔
    (edgePartition L).rel e.u e.v = false ∧ (edgePartition L).numComponents + L.length = n
  cases hrel : (edgePartition L).rel e.u e.v
  · have hm := DisjointSet.Partition.numComponents_merge_of_not_rel hrel
    simp only [true_and]
    omega
  · rw [DisjointSet.Partition.merge_of_rel hrel]
    have hle := numComponents_le_edgePartitionFrom_add_length (DisjointSet.Partition.discrete n) L
    simp only [DisjointSet.Partition.numComponents_discrete] at hle
    change n ≤ (edgePartition L).numComponents + L.length at hle
    simp only [Bool.true_eq_false, false_and, iff_false]
    omega

/-- Injective contraction `lift : Fin k → Fin n` preserves connected-component equivalence
classes exactly. -/
theorem edgePartition_contractEdgeList_rel_inj {k n : ℕ}
    {lift : Fin k → Fin n} (hlift : Function.Injective lift)
    (L : List (WeightedEdge k ℕ)) (u v : Fin k) :
    (edgePartition (contractEdgeList lift L)).rel (lift u) (lift v) =
      (edgePartition L).rel u v := by
  rw [Bool.eq_iff_iff, rel_edgePartition_iff_eqvGen, rel_edgePartition_iff_eqvGen]
  constructor
  · intro h
    let RL : Fin k → Fin k → Prop := fun x y => ∃ e ∈ L, x = e.u ∧ y = e.v
    let R : Fin n → Fin n → Prop := fun a b =>
      a = b ∨ ∃ u' v' : Fin k, a = lift u' ∧ b = lift v' ∧ Relation.EqvGen RL u' v'
    have hgen : ∀ a b : Fin n,
        Relation.EqvGen (fun x y => ∃ e ∈ contractEdgeList lift L, x = e.u ∧ y = e.v) a b →
          R a b := by
      intro a b hab
      induction hab with
      | rel _ _ hab =>
        obtain ⟨e, he, rfl, rfl⟩ := hab
        simp only [contractEdgeList, List.mem_map] at he
        obtain ⟨f, hf, rfl⟩ := he
        exact Or.inr ⟨f.u, f.v, rfl, rfl, .rel _ _ ⟨f, hf, rfl, rfl⟩⟩
      | refl _ => exact Or.inl rfl
      | symm _ _ _ ih =>
        rcases ih with rfl | ⟨u', v', ha, hb, huv⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨v', u', hb, ha, .symm _ _ huv⟩
      | trans _ _ _ _ _ ih1 ih2 =>
        rcases ih1 with rfl | ⟨u1, v1, ha, hb1, h1⟩
        · exact ih2
        · rcases ih2 with rfl | ⟨u2, v2, hb2, hc, h2⟩
          · exact Or.inr ⟨u1, v1, ha, hb1, h1⟩
          · have hv_eq : v1 = u2 := hlift (hb1.symm.trans hb2)
            subst hv_eq
            exact Or.inr ⟨u1, v2, ha, hc, .trans _ _ _ h1 h2⟩
    rcases hgen (lift u) (lift v) h with heq | ⟨u', v', hu, hv, huv⟩
    · have : u = v := hlift heq
      subst this
      exact .refl _
    · have hu' : u = u' := hlift hu
      have hv' : v = v' := hlift hv
      subst hu'; subst hv'
      exact huv
  · intro h
    induction h with
    | rel _ _ hxy =>
      obtain ⟨e, he, rfl, rfl⟩ := hxy
      exact .rel _ _ ⟨contractEdge lift e, List.mem_map.mpr ⟨e, he, rfl⟩, rfl, rfl⟩
    | refl _ => exact .refl _
    | symm _ _ _ ih => exact .symm _ _ ih
    | trans _ _ _ _ _ ih1 ih2 => exact .trans _ _ _ ih1 ih2

/-- If `contractEdgeList lift L` is acyclic along an injective embedding `lift`, then `L` is
acyclic. -/
theorem isAcyclic_of_contractEdgeList_injective {k n : ℕ}
    {lift : Fin k → Fin n} (hlift : Function.Injective lift)
    (L : List (WeightedEdge k ℕ)) (hL : IsAcyclic (contractEdgeList lift L)) :
    IsAcyclic L := by
  induction L with
  | nil => exact isAcyclic_nil
  | cons e rest ih =>
    change IsAcyclic (contractEdge lift e :: contractEdgeList lift rest) at hL
    obtain ⟨hrel, hrest⟩ := (isAcyclic_cons_iff _ _).mp hL
    refine (isAcyclic_cons_iff e rest).mpr ⟨?_, ih hrest⟩
    have hrel_iff := edgePartition_contractEdgeList_rel_inj hlift rest e.u e.v
    change (edgePartition (contractEdgeList lift rest)).rel (lift e.u) (lift e.v) = false at hrel
    rw [hrel] at hrel_iff
    exact hrel_iff.symm

/-- Any acyclic edge list supported on a vertex subset `S : Finset (Fin n)` has length at most
`S.card - 1`. -/
theorem isAcyclic_length_le_finset_sub_one {n : ℕ} (S : Finset (Fin n))
    (F : List (WeightedEdge n ℕ)) (hF : IsAcyclic F)
    (hmem : ∀ e ∈ F, e.u ∈ S ∧ e.v ∈ S) : F.length ≤ S.card - 1 := by
  by_cases hS : S.card = 0
  · have hnil : F = [] := by
      rw [List.eq_nil_iff_forall_not_mem]
      intro e he
      have hu := (hmem e he).1
      rw [Finset.card_eq_zero.mp hS] at hu
      simp at hu
    simp [hnil]
  · have hpos : 0 < S.card := Nat.pos_of_ne_zero hS
    let eS := S.equivFin
    let ι : Fin S.card → Fin n := fun i => (eS.symm i).1
    have hι : Function.Injective ι := fun a b hab =>
      eS.symm.injective (Subtype.ext hab)
    let F' : List (WeightedEdge S.card ℕ) := F.pmap
      (fun e he => ⟨eS ⟨e.u, (hmem e he).1⟩, eS ⟨e.v, (hmem e he).2⟩, e.weight⟩)
      (fun _ he => he)
    have hmk : ∀ (u1 : Fin n) (v1 : Fin n) (w1 : ℕ) (e : WeightedEdge n ℕ),
        u1 = e.u → v1 = e.v → w1 = e.weight →
        (⟨u1, v1, w1⟩ : WeightedEdge n ℕ) = e := by
      rintro u1 v1 w1 ⟨u, v, w⟩ rfl rfl rfl; rfl
    have hcon : contractEdgeList ι F' = F := by
      apply List.ext_getElem
      · simp [contractEdgeList, F']
      · intro i hi1 hi2
        simp only [contractEdgeList, F', List.getElem_map, List.getElem_pmap, contractEdge, ι]
        exact hmk _ _ _ F[i] (by simp [eS]) (by simp [eS]) rfl
    have hF' : IsAcyclic F' := isAcyclic_of_contractEdgeList_injective hι F' (hcon ▸ hF)
    have hlen := IsAcyclic.length_le_pred hpos hF'
    have hF_len : F'.length = F.length := by simp [F']
    omega

/-- Total-length bound over vertex sets overlapping earlier rounds in at most one vertex:
if `lens[i] ≤ verts[i].card - 1` and each `verts[i]` shares at most one vertex with the union of
earlier sets `verts[j]` (`j < i`), then `lens.sum ≤ n`. -/
theorem sum_verts_sub_one_le {n : ℕ} (verts : List (Finset (Fin n)))
    (lens : List ℕ) (hlen : lens.length = verts.length)
    (hle : ∀ i : Fin verts.length,
      lens[i.val]'(by omega) ≤ (verts[i.val]'i.isLt).card - 1)
    (hinter : ∀ i : Fin verts.length,
      ((verts[i.val]'i.isLt) ∩ (Finset.univ.filter fun j : Fin verts.length =>
        j.val < i.val).biUnion (fun j => verts[j.val]'j.isLt)).card ≤ 1) :
    lens.sum ≤ n := by
  have haux : ∀ k ≤ verts.length,
      (lens.take k).sum ≤ ((Finset.univ.filter fun j : Fin verts.length =>
        j.val < k).biUnion (fun j => verts[j.val]'j.isLt)).card := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk_lt : k < verts.length := by omega
      have htake : lens.take (k + 1) = lens.take k ++ [lens[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
      rw [htake, List.sum_append, List.sum_singleton]
      let U : Finset (Fin n) := (Finset.univ.filter fun j : Fin verts.length =>
        j.val < k).biUnion (fun j => verts[j.val]'j.isLt)
      have hU_succ : (Finset.univ.filter fun j : Fin verts.length =>
          j.val < k + 1).biUnion (fun j => verts[j.val]'j.isLt) =
          U ∪ verts[k]'hk_lt := by
        ext x
        simp only [U, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨j, hj, hxj⟩
          by_cases hjk : j.val < k
          · exact Or.inl ⟨j, hjk, hxj⟩
          · rcases j with ⟨jv, hjv⟩
            have hjk_eq : jv = k := by simp only at hj hjk; omega
            subst hjk_eq
            exact Or.inr hxj
        · rintro (⟨j, hj, hxj⟩ | hxk)
          · exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
          · exact ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hxk⟩
      rw [hU_succ]
      have hcap := Finset.card_union_add_card_inter U (verts[k]'hk_lt)
      have hk_val : (⟨k, hk_lt⟩ : Fin verts.length).val = k := rfl
      have hi1 : (verts[k]'hk_lt ∩ U).card ≤ 1 := by
        simpa only [hk_val] using hinter ⟨k, hk_lt⟩
      have hcard_pos : (verts[k]'hk_lt ∩ U).card ≤ (verts[k]'hk_lt).card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [Finset.inter_comm] at hcap
      have hl : lens[k]'(by omega) ≤ (verts[k]'hk_lt).card - 1 := by
        simpa only [hk_val] using hle ⟨k, hk_lt⟩
      have ih' := ih (by omega)
      dsimp only [U] at *
      omega
  have hfin := haux verts.length le_rfl
  rw [List.take_of_length_le (by omega)] at hfin
  have huniv : ((Finset.univ.filter fun j : Fin verts.length =>
      j.val < verts.length).biUnion (fun j => verts[j.val]'j.isLt)).card ≤ n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  exact hfin.trans huniv

/-! ## Section 2: Faithfully Encoded Argument and Environment Structures -/

/-- Environment for `appendSelIdsProg`: source edge array `srcBase` and destination ID array
`dstBase`. -/
structure AppendSelEnv where
  /-- Base address of stride-4 source edges. -/
  srcBase : ℕ
  /-- Base address of destination edge-ID array. -/
  dstBase : ℕ
  deriving DecidableEq

/-- Faithful two-word encoding of `AppendSelEnv` as `[srcBase, dstBase]`. -/
word_enc_structure encAppendSelEnv : AppendSelEnv where
  srcBase : wordWords,
  dstBase : wordWords

instance : WordEncoding AppendSelEnv := ⟨2, encAppendSelEnv⟩

/-- Environment for `copyStride4Prog`: source and destination base addresses of stride-4
edge arrays. -/
structure CopyStride4Env where
  /-- Base address of stride-4 source edges. -/
  srcBase : ℕ
  /-- Base address of stride-4 destination array. -/
  dstBase : ℕ
  deriving DecidableEq

/-- Faithful two-word encoding of `CopyStride4Env` as `[srcBase, dstBase]`. -/
word_enc_structure encCopyStride4Env : CopyStride4Env where
  srcBase : wordWords,
  dstBase : wordWords

instance : WordEncoding CopyStride4Env := ⟨2, encCopyStride4Env⟩

/-- Arguments for `concatThreeProg`: base addresses and lengths of three stride-4 edge arrays. -/
structure ConcatThreeArgs where
  /-- Base of first stride-4 array. -/
  b1 : ℕ
  /-- Length of first array. -/
  l1 : ℕ
  /-- Base of second stride-4 array. -/
  b2 : ℕ
  /-- Length of second array. -/
  l2 : ℕ
  /-- Base of third stride-4 array. -/
  b3 : ℕ
  /-- Length of third array. -/
  l3 : ℕ
  deriving DecidableEq

/-- Faithful six-word encoding of `ConcatThreeArgs` as `[b1, l1, b2, l2, b3, l3]`. -/
word_enc_structure encConcatThreeArgs : ConcatThreeArgs where
  b1 : wordWords,
  l1 : wordWords,
  b2 : wordWords,
  l2 : wordWords,
  b3 : wordWords,
  l3 : wordWords

instance : WordEncoding ConcatThreeArgs := ⟨6, encConcatThreeArgs⟩

/-- Environment for `liftEdgesProg`: local edge base, vertex lift map, and global destination
array base. -/
structure LiftEdgesEnv where
  /-- Base address of local stride-4 edges. -/
  edgeBase : ℕ
  /-- Base address of vertex lift table. -/
  liftBase : ℕ
  /-- Base address of global destination stride-4 array. -/
  dstBase : ℕ
  deriving DecidableEq

/-- Faithful three-word encoding of `LiftEdgesEnv` as `[edgeBase, liftBase, dstBase]`. -/
word_enc_structure encLiftEdgesEnv : LiftEdgesEnv where
  edgeBase : wordWords,
  liftBase : wordWords,
  dstBase : wordWords

instance : WordEncoding LiftEdgesEnv := ⟨3, encLiftEdgesEnv⟩

private structure Stride4Words where
  u : ℕ
  v : ℕ
  wt : ℕ
  eid : ℕ

private word_enc_structure encStride4Words : Stride4Words where
  u : wordWords,
  v : wordWords,
  wt : wordWords,
  eid : wordWords

private instance : WordEncoding Stride4Words := ⟨4, encStride4Words⟩

/-! ## Section 3: Base `Memory.Prog` Subroutines and Specifications -/

private theorem iterate_bind_snd_ft {w C : ℕ} {S : Set ℕ} {s : Memory.State}
    {p : Memory.Prog (ℕ × ℕ)}
    (hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p))
    (hm : memoryCost p s ≤ C)
    (hmod : Memory.Modifies S s ((Memory.spec 0).clientState s p))
    {Q : ℕ → Memory.State → Prop}
    (hq : Q ((Memory.spec 0).clientResult s p).2 ((Memory.spec 0).clientState s p)) :
    Memory.FramedTriple w s (p >>= fun st => pure st.2) C S Q := by
  refine framedTriple_iff_realization.mpr ⟨validHistory_bind_step hv (validHistory_pure w _ _),
    ?_, ?_, ?_⟩
  · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]; exact hm
  · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]; exact hmod
  · rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]; exact hq

private theorem allocDirty4_bind_pure_ft {w count C : ℕ} {S : Set ℕ} {s : Memory.State}
    {f : ℕ → Memory.Prog ℕ}
    (hfit : Fits w (s.frontier + 4 * count)) (hS : ∀ a ∈ S, s.frontier ≤ a)
    (hv : (Memory.spec w).ValidHistory ⟨s.mem, s.frontier + 4 * count⟩
      ((Memory.spec w).clientHistory ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier)))
    (hm : memoryCost (f s.frontier) ⟨s.mem, s.frontier + 4 * count⟩ ≤ C)
    (hmod : Memory.Modifies S ⟨s.mem, s.frontier + 4 * count⟩
      ((Memory.spec 0).clientState ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier)))
    {Q : ℕ → Memory.State → Prop}
    (hq : Q s.frontier
      ((Memory.spec 0).clientState ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier))) :
    Memory.FramedTriple w s (Memory.allocDirty (4 * count) >>= fun ob =>
      f ob >>= fun _ => pure ob) (C + 1) ∅ Q := by
  have hft : Memory.FramedTriple w ⟨s.mem, s.frontier + 4 * count⟩ (f s.frontier) C S
      fun _ s' => Memory.FramedTriple w s' (pure s.frontier) 0 S Q :=
    framedTriple_iff_realization.mpr ⟨hv, hm, hmod, Memory.FramedTriple.pure hq⟩
  exact ((Memory.FramedTriple.allocDirty_bind hfit
    ((Memory.FramedTriple.bind_same hft).mono (Nat.add_zero _).le
      fun _ _ h => h)).frame_empty_of_ge_frontier hS).mono (by omega : C + 0 + 1 ≤ C + 1)
    fun _ _ h => h

/-! ### `appendSelIdsProg`: Append Edge IDs from Stride-4 Array -/

private def appendSelIdStep (d : AppendSelEnv × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let eid ← Memory.read (d.1.srcBase + 4 * d.2.1 + 3)
  Memory.write (d.1.dstBase + d.2.2) eid
  pure (d.2.1 + 1, d.2.2 + 1)

private def appendSelIdStepSafe (w : ℕ) (d : AppendSelEnv × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2.1 + 1) ∧ Fits w (d.2.2 + 1) ∧
    d.1.srcBase + 4 * d.2.1 + 3 < s.frontier ∧ d.1.dstBase + d.2.2 < s.frontier

private theorem realizes_appendSelIdStep_history : Realizes .exact
    appendSelIdStep
    (appendWords (WordEncoding.encode (α := AppendSelEnv)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ))
    (fun w d s => appendSelIdStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (appendSelIdStep d)))
    (fun _ _ => 0) := by
  unfold appendSelIdStep
  realize
  all_goals
    obtain ⟨⟨h16, hfit1, hfit2, h1, h2⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_appendSelIdStep : Realizes .exact
    appendSelIdStep
    (appendWords (WordEncoding.encode (α := AppendSelEnv)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ)) appendSelIdStepSafe (fun _ _ => 0) :=
  realizes_appendSelIdStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Append `count` original edge IDs (`e.id`) from stride-4 source array `e.srcBase` into
`e.dstBase` starting at offset `dstOff`, returning `dstOff + count`. -/
def appendSelIdsProg : AppendSelEnv × ℕ × ℕ → Memory.Prog ℕ
  | (e, dstOff, count) => do
    let st ← iterate appendSelIdStep e count (0, dstOff)
    pure st.2

/-- Safety domain for `appendSelIdsProg`. -/
@[expose] def appendSelIdsProgSafe (w : ℕ) : AppendSelEnv × ℕ × ℕ → Memory.State → Prop
  | (e, dstOff, count), s =>
    Fits w 16 ∧ e.srcBase + 4 * count ≤ s.frontier ∧
      e.dstBase + dstOff + count ≤ s.frontier ∧ Fits w (dstOff + count + 1)

private theorem appendSelIdsProg_word_spec {w srcBase dstBase dstOff count : ℕ}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsrc_lt : srcBase + 4 * count ≤ s.frontier)
    (hdst_lt : dstBase + dstOff + count ≤ s.frontier)
    (hfit_off : Fits w (dstOff + count + 1)) :
    let e : AppendSelEnv := ⟨srcBase, dstBase⟩
    let S := Set.Ico (dstBase + dstOff) (dstBase + dstOff + count)
    iterationSafe appendSelIdStep appendSelIdStepSafe w e count (0, dstOff) s ∧
    Memory.FramedTriple w s (appendSelIdsProg (e, dstOff, count)) (2 * count) S
      fun res s' =>
        res = dstOff + count ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ((srcBase + 4 * count ≤ dstBase + dstOff ∨ dstBase + dstOff + count ≤ srcBase) →
          ∀ j < count, s'.mem (dstBase + dstOff + j) = s.mem (srcBase + 4 * j + 3)) := by
  let e : AppendSelEnv := ⟨srcBase, dstBase⟩
  let S : Set ℕ := Set.Ico (dstBase + dstOff) (dstBase + dstOff + count)
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a = (k, dstOff + k) ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ((srcBase + 4 * count ≤ dstBase + dstOff ∨ dstBase + dstOff + count ≤ srcBase) →
      ∀ j < k, t.mem (dstBase + dstOff + j) = s.mem (srcBase + 4 * j + 3))
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      appendSelIdStepSafe w (e, a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (appendSelIdStep (e, a))) ∧
      let a' := (Memory.spec 0).clientResult t (appendSelIdStep (e, a))
      let t' := (Memory.spec 0).clientState t (appendSelIdStep (e, a))
      memoryCost (appendSelIdStep (e, a)) t + 0 ≤ 0 + 2 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hfit_k1 : Fits w (k + 1) := hfit_off.of_le (by omega)
    have hfit_ok1 : Fits w (dstOff + k + 1) := hfit_off.of_le (by omega)
    have hmem_t : ∀ x, Fits w (t.mem x) := hwt.mem_fits
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (appendSelIdStep (e, (k, dstOff + k)))) := by
      dsimp only [appendSelIdStep, e]
      valid_prog
      all_goals first | exact hmem_t _ | omega
    have hcost : memoryCost (appendSelIdStep (e, (k, dstOff + k))) t ≤ 2 := by
      dsimp only [appendSelIdStep, e]
      prog_cost
    have hres : (Memory.spec 0).clientResult t (appendSelIdStep (e, (k, dstOff + k))) =
        (k + 1, dstOff + (k + 1)) := by
      dsimp only [appendSelIdStep, e]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure, Nat.add_assoc]
    have hst : (Memory.spec 0).clientState t (appendSelIdStep (e, (k, dstOff + k))) =
        ⟨Function.update t.mem (dstBase + (dstOff + k)) (t.mem (srcBase + 4 * k + 3)),
          t.frontier⟩ := by
      dsimp only [appendSelIdStep, e]
      rw [clientState_bind_read, clientState_bind_write, StateTransitionSpec.clientState_pure]
    have hupd_out : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (appendSelIdStep (e, (k, dstOff + k)))).mem x =
          t.mem x := by
      intro x hx
      rw [hst]
      simp only [S, Set.mem_Ico, not_and_or, not_le, not_lt] at hx
      update_simp
    refine ⟨⟨h16, hfit_k1, hfit_ok1, by dsimp only [e]; omega, by dsimp only [e]; omega⟩,
      hvh, by omega, ⟨by rw [hst], fun x _ hx => hupd_out x hx⟩,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh,
      fun x hx => (hupd_out x hx).trans (hframe x hx), fun hd j hj => ?_⟩
    rw [hst]; dsimp only
    by_cases hjk : j = k
    · subst j
      have hin_src : t.mem (srcBase + 4 * k + 3) = s.mem (srcBase + 4 * k + 3) :=
        hframe _ (by simp only [S, Set.mem_Ico]; rcases hd with hdl | hdr <;> omega)
      rw [show dstBase + (dstOff + k) = dstBase + dstOff + k by omega, Function.update_self,
        hin_src]
    · update_simp; exact hpref hd j (by omega)
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, hres_it, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec appendSelIdStep appendSelIdStepSafe w e 2 count inv (fun _ _ _ => 0)
      S hstep (0, dstOff) s
      ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, iterate_bind_snd_ft hv_it (by simpa using hm_it) hmod_it
    ⟨congrArg Prod.snd hres_it, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `appendSelIdsProg`. -/
theorem realizes_appendSelIdsProg : Realizes .exact
    appendSelIdsProg
    (WordEncoding.encode (α := AppendSelEnv × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    appendSelIdsProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : AppendSelEnv × ℕ × ℕ => do
        let st ← iterate appendSelIdStep d.1 d.2.2 (0, d.2.1)
        pure st.2)
      (WordEncoding.encode (α := AppendSelEnv × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => Fits w 16 ∧
        iterationSafe appendSelIdStep appendSelIdStepSafe w d.1 d.2.2 (0, d.2.1) s)
      (fun _ _ => 0) := by
    realize [realizes_appendSelIdStep]
    exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine (hraw.congr fun ⟨_, _, _⟩ => rfl).consequence (fun w d s _ hmem h => ?_)
    (fun _ _ => le_rfl)
  rcases d with ⟨e, dstOff, count⟩
  obtain ⟨h16, hsrc, hdst, hfit⟩ := h
  exact ⟨h16, (appendSelIdsProg_word_spec h16 hmem hsrc hdst hfit).1⟩

/-- Framed specification for `appendSelIdsProg`: copies `srcEs[j].id` into
`dstBase + dstOff + j` for `j < srcEs.length`, modifying only
`Set.Ico (dstBase + dstOff) (dstBase + dstOff + srcEs.length)`, in at most `2 * srcEs.length`
memory operations. -/
theorem appendSelIdsProg_spec {w n srcBase dstBase dstOff : ℕ}
    {srcEs : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase srcEs s.mem)
    (hin_lt : srcBase + 4 * srcEs.length ≤ s.frontier)
    (hdst_lt : dstBase + dstOff + srcEs.length ≤ s.frontier)
    (hdisj : srcBase + 4 * srcEs.length ≤ dstBase + dstOff ∨
      dstBase + dstOff + srcEs.length ≤ srcBase)
    (hfit_off : Fits w (dstOff + srcEs.length + 1)) :
    Memory.FramedTriple w s (appendSelIdsProg (⟨srcBase, dstBase⟩, dstOff, srcEs.length))
      (2 * srcEs.length) (Set.Ico (dstBase + dstOff) (dstBase + dstOff + srcEs.length))
      fun res s' =>
        res = dstOff + srcEs.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j (hj : j < srcEs.length), s'.mem (dstBase + dstOff + j) = srcEs[j].id := by
  refine (appendSelIdsProg_word_spec h16 hwf hin_lt hdst_lt hfit_off).2.mono le_rfl
    fun res s' ⟨hres, hfr, hwf', hvals⟩ =>
      ⟨hres, hfr, hwf', fun j hj => (hvals hdisj j hj).trans (hin j hj).2.2.2⟩

/-! ### Private Stride-4 Read/Write Helpers -/

private def stride4At (base idx : ℕ) (ew : Stride4Words) (mem : ℕ → ℕ) : Prop :=
  mem (base + 4 * idx) = ew.u ∧ mem (base + 4 * idx + 1) = ew.v ∧
    mem (base + 4 * idx + 2) = ew.wt ∧ mem (base + 4 * idx + 3) = ew.eid

private theorem stride4At_congr {base idx : ℕ} {ew : Stride4Words} {m₁ m₂ : ℕ → ℕ}
    (heq : ∀ q < 4, m₂ (base + 4 * idx + q) = m₁ (base + 4 * idx + q))
    (h : stride4At base idx ew m₁) : stride4At base idx ew m₂ :=
  ⟨(heq 0 (by decide)).trans h.1, (heq 1 (by decide)).trans h.2.1,
    (heq 2 (by decide)).trans h.2.2.1, (heq 3 (by decide)).trans h.2.2.2⟩

private def writeStride4 (d : (ℕ × ℕ) × Stride4Words) : Memory.Prog ℕ := do
  Memory.write (d.1.1 + 4 * d.1.2) d.2.u
  Memory.write (d.1.1 + 4 * d.1.2 + 1) d.2.v
  Memory.write (d.1.1 + 4 * d.1.2 + 2) d.2.wt
  Memory.write (d.1.1 + 4 * d.1.2 + 3) d.2.eid
  pure (d.1.2 + 1)

private def writeStride4Safe (w : ℕ) (d : (ℕ × ℕ) × Stride4Words) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.2 + 1) ∧ Fits w d.2.u ∧ Fits w d.2.v ∧ Fits w d.2.wt ∧
    Fits w d.2.eid ∧ d.1.1 + 4 * d.1.2 + 3 < s.frontier

private theorem realizes_writeStride4_history : Realizes .exact
    writeStride4
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words)))
    (WordEncoding.encode (α := ℕ))
    (fun w d s => writeStride4Safe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeStride4 d)))
    (fun _ _ => 0) := by
  unfold writeStride4
  realize
  all_goals
    obtain ⟨⟨h16, hfit, hu, hv1, hw1, hid, hlt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.write,
      Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_writeStride4 : Realizes .exact
    writeStride4
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words)))
    (WordEncoding.encode (α := ℕ)) writeStride4Safe (fun _ _ => 0) :=
  realizes_writeStride4_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem writeStride4_spec {w dst idx : ℕ} {ew : Stride4Words} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hu : Fits w ew.u) (hv : Fits w ew.v) (hwt : Fits w ew.wt) (heid : Fits w ew.eid)
    (hlt : dst + 4 * idx + 3 < s.frontier) :
    let S := Set.Ico (dst + 4 * idx) (dst + 4 * idx + 4)
    Memory.FramedTriple w s (writeStride4 ((dst, idx), ew)) 4 S fun res s' =>
      res = idx + 1 ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
      stride4At dst idx ew s'.mem := by
  have hprog : writeStride4 ((dst, idx), ew) =
      (Memory.write (dst + 4 * idx) ew.u >>= fun _ =>
        Memory.write (dst + 4 * idx + 1) ew.v >>= fun _ =>
          Memory.write (dst + 4 * idx + 2) ew.wt >>= fun _ =>
            Memory.write (dst + 4 * idx + 3) ew.eid >>= fun _ => pure (idx + 1)) := rfl
  have hvh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (writeStride4 ((dst, idx), ew))) := by
    rw [hprog]; valid_prog; all_goals (try dsimp only); omega
  have hst : (Memory.spec 0).clientState s (writeStride4 ((dst, idx), ew)) =
      ⟨Function.update (Function.update (Function.update (Function.update s.mem
        (dst + 4 * idx) ew.u) (dst + 4 * idx + 1) ew.v) (dst + 4 * idx + 2) ew.wt)
        (dst + 4 * idx + 3) ew.eid, s.frontier⟩ := by
    rw [hprog]; repeat rw [clientState_bind_write]; rfl
  have hmod : Memory.Modifies (Set.Ico (dst + 4 * idx) (dst + 4 * idx + 4)) s
      ((Memory.spec 0).clientState s (writeStride4 ((dst, idx), ew))) := by
    refine ⟨by rw [hst], fun x _ hx => ?_⟩
    rw [hst]
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hx
    update_simp
  refine framedTriple_iff_realization.mpr ⟨hvh, ?_, hmod, ?_, by rw [hst],
    wellFormed_clientState hwf hvh, ?_⟩
  · rw [hprog]; prog_cost
  · rw [hprog]; simp only [clientResult_bind_write, StateTransitionSpec.clientResult_pure]
  · rw [hst]; dsimp only [stride4At]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp

private def readStride4 (d : ℕ × ℕ) : Memory.Prog Stride4Words := do
  let u ← Memory.read (d.1 + 4 * d.2)
  let v ← Memory.read (d.1 + 4 * d.2 + 1)
  let wt ← Memory.read (d.1 + 4 * d.2 + 2)
  let eid ← Memory.read (d.1 + 4 * d.2 + 3)
  pure ⟨u, v, wt, eid⟩

private def readStride4Safe (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1 + 4 * d.2 + 3 < s.frontier

private theorem realizes_readStride4_history : Realizes .exact
    readStride4 (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words))
    (fun w d s => readStride4Safe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (readStride4 d)))
    (fun _ _ => 0) := by
  unfold readStride4
  realize
  all_goals
    obtain ⟨⟨h16, hlt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals fits

private theorem realizes_readStride4 : Realizes .exact
    readStride4 (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := Stride4Words))
    readStride4Safe (fun _ _ => 0) :=
  realizes_readStride4_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem readStride4_spec {w base idx : ℕ} {s : Memory.State}
    (hlt : base + 4 * idx + 3 < s.frontier) :
    Memory.FramedTriple w s (readStride4 (base, idx)) 4 ∅ fun res s' =>
      res = ⟨s.mem (base + 4 * idx), s.mem (base + 4 * idx + 1),
        s.mem (base + 4 * idx + 2), s.mem (base + 4 * idx + 3)⟩ ∧ s' = s := by
  have hprog : readStride4 (base, idx) =
      (Memory.read (base + 4 * idx) >>= fun u =>
        Memory.read (base + 4 * idx + 1) >>= fun v =>
          Memory.read (base + 4 * idx + 2) >>= fun wt =>
            Memory.read (base + 4 * idx + 3) >>= fun eid => pure ⟨u, v, wt, eid⟩) := rfl
  have hvh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (readStride4 (base, idx))) := by
    rw [hprog]; valid_prog; all_goals omega
  have hst : (Memory.spec 0).clientState s (readStride4 (base, idx)) = s := by
    rw [hprog]; repeat rw [clientState_bind_read]; rfl
  refine framedTriple_iff_realization.mpr ⟨hvh, ?_, ?_, ?_, hst⟩
  · rw [hprog]; prog_cost
  · rw [hst]; exact Memory.Modifies.refl ∅ s
  · rw [hprog]; simp only [clientResult_bind_read, StateTransitionSpec.clientResult_pure]

/-! ### `retagIndexedProg`: Retag Edge IDs `0..m-1` -/

private def retagStep (d : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let ew ← readStride4 (d.1.1, d.2)
  writeStride4 ((d.1.2, d.2), ⟨ew.u, ew.v, ew.wt, d.2⟩)

private def retagStepSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ readStride4Safe w (d.1.1, d.2) s ∧
    let ew := (Memory.spec 0).clientResult s (readStride4 (d.1.1, d.2))
    let s1 := (Memory.spec 0).clientState s (readStride4 (d.1.1, d.2))
    writeStride4Safe w ((d.1.2, d.2), ⟨ew.u, ew.v, ew.wt, d.2⟩) s1

private theorem realizes_retagStep : Realizes .exact
    retagStep
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ)) retagStepSafe (fun _ _ => 0) := by
  unfold retagStep
  realize [realizes_readStride4, realizes_writeStride4]
  · exact h.2.1
  · exact h.2.2

/-- Copy `count` stride-4 edges from `d.1` into a newly allocated dirty block while rewriting each
edge's identifier to its array index `0 .. count - 1`, returning the allocated base address. -/
def retagIndexedProg (d : ℕ × ℕ) : Memory.Prog ℕ := do
  let outBase ← Memory.allocDirty (4 * d.2)
  let _ ← iterate retagStep (d.1, outBase) d.2 0
  pure outBase

/-- Safety domain for `retagIndexedProg`. -/
@[expose] def retagIndexedProgSafe (w : ℕ) (d : ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1 + 4 * d.2 ≤ s.frontier ∧ Fits w (s.frontier + 4 * d.2)

private theorem retagIndexedProg_word_spec {w srcBase count : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : srcBase + 4 * count ≤ s.frontier) (hfit : Fits w (s.frontier + 4 * count)) :
    let prog := retagIndexedProg (srcBase, count)
    iterationSafe retagStep retagStepSafe w (srcBase, s.frontier) count 0
      ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s prog (8 * count + 1) ∅ fun outBase s' =>
      outBase = s.frontier ∧ s'.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s' ∧
      ∀ i < count, stride4At outBase i
        ⟨s.mem (srcBase + 4 * i), s.mem (srcBase + 4 * i + 1),
          s.mem (srcBase + 4 * i + 2), i⟩ s'.mem := by
  let outBase := s.frontier
  let s₀ : Memory.State := ⟨s.mem, s.frontier + 4 * count⟩
  have hs₀_fr : s₀.frontier = s.frontier + 4 * count := rfl
  let S : Set ℕ := Set.Ico outBase (outBase + 4 * count)
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hfit, hwf.mem_fits⟩
  have hfit_m1 : Fits w (count + 1) := by
    rcases count with _ | m
    · exact h16.of_le (by omega)
    · exact hfit.of_le (by omega)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s₀.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ∀ i < k, stride4At outBase i
      ⟨s.mem (srcBase + 4 * i), s.mem (srcBase + 4 * i + 1), s.mem (srcBase + 4 * i + 2), i⟩ t.mem
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      retagStepSafe w ((srcBase, outBase), a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (retagStep ((srcBase, outBase), a))) ∧
      let a' := (Memory.spec 0).clientResult t (retagStep ((srcBase, outBase), a))
      let t' := (Memory.spec 0).clientState t (retagStep ((srcBase, outBase), a))
      memoryCost (retagStep ((srcBase, outBase), a)) t + 0 ≤ 0 + 8 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hr := readStride4_spec (w := w) (base := srcBase) (idx := k) (s := t)
      (by rw [htfr, hs₀_fr]; omega)
    have hmem_t := hwt.mem_fits
    have hfit_k1 : Fits w (k + 1) := hfit_m1.of_le (by omega)
    have hsrc_mem : ∀ q < 4, t.mem (srcBase + 4 * k + q) = s.mem (srcBase + 4 * k + q) :=
      fun q hq => hframe _ (by simp only [S, Set.mem_Ico, outBase]; omega)
    let Sk := Set.Ico (outBase + 4 * k) (outBase + 4 * k + 4)
    have hft_s : Memory.FramedTriple w t (retagStep ((srcBase, outBase), k)) 8 Sk fun a' t' =>
        a' = k + 1 ∧ t'.frontier = s₀.frontier ∧ Memory.WellFormed w t' ∧
        stride4At outBase k ⟨s.mem (srcBase + 4 * k), s.mem (srcBase + 4 * k + 1),
          s.mem (srcBase + 4 * k + 2), k⟩ t'.mem := by
      have hsub : Memory.FramedTriple w t (readStride4 (srcBase, k)) 4 Sk fun ew t₁ =>
          Memory.FramedTriple w t₁ (writeStride4 ((outBase, k), ⟨ew.u, ew.v, ew.wt, k⟩)) 4 Sk
            fun a' t' =>
              a' = k + 1 ∧ t'.frontier = s₀.frontier ∧ Memory.WellFormed w t' ∧
              stride4At outBase k ⟨s.mem (srcBase + 4 * k), s.mem (srcBase + 4 * k + 1),
                s.mem (srcBase + 4 * k + 2), k⟩ t'.mem := by
        refine (hr.frame_mono (Set.empty_subset Sk)).mono le_rfl fun ew t₁ ⟨hew, ht₁⟩ => ?_
        rw [ht₁, hew]
        have hw := writeStride4_spec (w := w) (dst := outBase) (idx := k)
          (ew := ⟨t.mem (srcBase + 4 * k), t.mem (srcBase + 4 * k + 1),
            t.mem (srcBase + 4 * k + 2), k⟩)
          hwt (hmem_t _) (hmem_t _) (hmem_t _) (hfit_k1.of_le (Nat.le_succ k))
          (by rw [htfr, hs₀_fr]; dsimp only [outBase]; omega)
        refine hw.mono le_rfl fun res t' ⟨hres, hfr', hwt', hstr⟩ =>
          ⟨hres, hfr'.trans htfr, hwt', ?_⟩
        have hu0 : t.mem (srcBase + 4 * k) = s.mem (srcBase + 4 * k) := by
          simpa using hsrc_mem 0 (by decide)
        simpa only [hu0, hsrc_mem 1 (by decide), hsrc_mem 2 (by decide)] using hstr
      exact hsub.bind_same.mono (by omega) fun _ _ h => h
    obtain ⟨hv_s, hc_s, hmod_s, hres_s, ht'_fr, hwt', hstr_k⟩ :=
      framedTriple_iff_realization.mp hft_s
    have hr_spec := framedTriple_iff_realization.mp hr
    obtain ⟨hr_ew, hr_st⟩ := hr_spec.2.2.2
    have hsafe_s : retagStepSafe w ((srcBase, outBase), k) t := by
      refine ⟨h16, ⟨h16, by dsimp only; rw [htfr, hs₀_fr]; omega⟩, ?_⟩
      rw [hr_st, hr_ew]
      exact ⟨h16, hfit_k1, hmem_t _, hmem_t _, hmem_t _, hfit_k1.of_le (Nat.le_succ k),
        by dsimp only; rw [htfr, hs₀_fr]; dsimp only [outBase]; omega⟩
    have hmod_S : Memory.Modifies S t
        ((Memory.spec 0).clientState t (retagStep ((srcBase, outBase), k))) :=
      hmod_s.mono fun x hx => by
        simp only [Sk, S, Set.mem_Ico] at hx ⊢; dsimp only [outBase] at *; omega
    have hmem_keep : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (retagStep ((srcBase, outBase), k))).mem x = t.mem x :=
      fun x hx => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) x fun hxk => by
        simp only [Sk, S, Set.mem_Ico] at hx hxk; dsimp only [outBase] at *; omega
    refine ⟨hsafe_s, hv_s, by omega, hmod_S, ?_⟩
    dsimp only [inv]
    refine ⟨hres_s, ht'_fr, hwt', fun x hx => (hmem_keep x hx).trans (hframe x hx),
      fun i hi => ?_⟩
    by_cases hik : i = k
    · subst i; exact hstr_k
    · exact stride4At_congr (fun q hq => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) _
        (by simp only [Sk, Set.mem_Ico]; omega)) (hpref i (by omega))
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, _, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec retagStep retagStepSafe w (srcBase, outBase) 8 count
      inv (fun _ _ _ => 0) S hstep 0 s₀
      ⟨rfl, rfl, hwf₀, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, allocDirty4_bind_pure_ft (S := S)
    (f := fun ob => iterate retagStep (srcBase, ob) count 0)
    hfit (fun _ ha => ha.1) hv_it (by simpa using hm_it) hmod_it ⟨rfl, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `retagIndexedProg`. -/
theorem realizes_retagIndexedProg : Realizes .exact
    retagIndexedProg (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    retagIndexedProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact retagIndexedProg (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun w d s => Fits w 16 ∧ Fits w (s.frontier + 4 * d.2) ∧
        iterationSafe retagStep retagStepSafe w (d.1, s.frontier) d.2 0
          ⟨s.mem, s.frontier + 4 * d.2⟩)
      (fun _ _ => 0) := by
    unfold retagIndexedProg
    realize [realizes_retagStep]
    all_goals first
      | exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
      | (have h16 := h.1; have hf := h.2.1; have hfront := hmem.frontier_fits; fits)
  refine hraw.consequence (fun w d s _ hmem ⟨h16, hsrc, hfit⟩ => ?_) (fun _ _ => le_rfl)
  exact ⟨h16, hfit, (retagIndexedProg_word_spec h16 hmem hsrc hfit).1⟩

/-- Framed specification for `retagIndexedProg`: allocates `4 * es.length` dirty words at
`s.frontier`, copies `es` with edge IDs retagged `0 .. es.length - 1`, leaving all cells below
`s.frontier` untouched (`Modifies ∅`), in at most `8 * es.length + 1` memory operations. -/
theorem retagIndexedProg_spec {w n srcBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase es s.mem)
    (hin_lt : srcBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * es.length)) :
    Memory.FramedTriple w s (retagIndexedProg (srcBase, es.length)) (8 * es.length + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * es.length ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase (es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩) s'.mem := by
  refine (retagIndexedProg_word_spec h16 hwf hin_lt hfit).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun i hi => ?_⟩
  have hi_len : i < es.length := by simpa using hi
  obtain ⟨hu, hv, hw, _⟩ := hin i hi_len
  obtain ⟨h0, h1, h2, h3⟩ := hvals i hi_len
  simp only [List.getElem_mapIdx]
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3⟩

/-! ### `copyStride4Prog`: Copy Stride-4 Edge Array -/

private def copyStride4Step (d : CopyStride4Env × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let ew ← readStride4 (d.1.srcBase, d.2.1)
  let nextOff ← writeStride4 ((d.1.dstBase, d.2.2), ew)
  pure (d.2.1 + 1, nextOff)

private def copyStride4StepSafe (w : ℕ) (d : CopyStride4Env × (ℕ × ℕ))
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2.1 + 1) ∧ readStride4Safe w (d.1.srcBase, d.2.1) s ∧
    let ew := (Memory.spec 0).clientResult s (readStride4 (d.1.srcBase, d.2.1))
    let s1 := (Memory.spec 0).clientState s (readStride4 (d.1.srcBase, d.2.1))
    writeStride4Safe w ((d.1.dstBase, d.2.2), ew) s1

private theorem realizes_copyStride4Step : Realizes .exact
    copyStride4Step
    (appendWords (WordEncoding.encode (α := CopyStride4Env)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ)) copyStride4StepSafe (fun _ _ => 0) := by
  unfold copyStride4Step
  realize [realizes_readStride4, realizes_writeStride4]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2
    | (have h16 := h.1; have hfit1 := h.2.1; fits)

/-- Copy `count` stride-4 edges from `e.srcBase` to `e.dstBase` starting at edge offset
`dstOff`, returning `dstOff + count`. -/
def copyStride4Prog : CopyStride4Env × ℕ × ℕ → Memory.Prog ℕ
  | (e, dstOff, count) => do
    let st ← iterate copyStride4Step e count (0, dstOff)
    pure st.2

/-- Safety domain for `copyStride4Prog`. -/
@[expose] def copyStride4ProgSafe (w : ℕ) : CopyStride4Env × ℕ × ℕ → Memory.State → Prop
  | (e, dstOff, count), s =>
    Fits w 16 ∧ e.srcBase + 4 * count ≤ s.frontier ∧
      e.dstBase + 4 * (dstOff + count) ≤ s.frontier ∧ Fits w (dstOff + count + 1)

private theorem copyStride4Prog_word_spec {w srcBase dstBase dstOff count : ℕ}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsrc_lt : srcBase + 4 * count ≤ s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + count) ≤ s.frontier)
    (hfit_off : Fits w (dstOff + count + 1)) :
    let e : CopyStride4Env := ⟨srcBase, dstBase⟩
    let S := Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + count))
    iterationSafe copyStride4Step copyStride4StepSafe w e count (0, dstOff) s ∧
    Memory.FramedTriple w s (copyStride4Prog (e, dstOff, count)) (8 * count) S
      fun res s' =>
        res = dstOff + count ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ((srcBase + 4 * count ≤ dstBase + 4 * dstOff ∨
          dstBase + 4 * (dstOff + count) ≤ srcBase) →
          ∀ i < count, stride4At (dstBase + 4 * dstOff) i
            ⟨s.mem (srcBase + 4 * i), s.mem (srcBase + 4 * i + 1),
              s.mem (srcBase + 4 * i + 2), s.mem (srcBase + 4 * i + 3)⟩ s'.mem) := by
  let e : CopyStride4Env := ⟨srcBase, dstBase⟩
  let S : Set ℕ := Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + count))
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a = (k, dstOff + k) ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ((srcBase + 4 * count ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + count) ≤ srcBase) →
      ∀ i < k, stride4At (dstBase + 4 * dstOff) i
        ⟨s.mem (srcBase + 4 * i), s.mem (srcBase + 4 * i + 1),
          s.mem (srcBase + 4 * i + 2), s.mem (srcBase + 4 * i + 3)⟩ t.mem)
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      copyStride4StepSafe w (e, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (copyStride4Step (e, a))) ∧
      let a' := (Memory.spec 0).clientResult t (copyStride4Step (e, a))
      let t' := (Memory.spec 0).clientState t (copyStride4Step (e, a))
      memoryCost (copyStride4Step (e, a)) t + 0 ≤ 0 + 8 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hr := readStride4_spec (w := w) (base := srcBase) (idx := k) (s := t)
      (by rw [htfr]; omega)
    have hmem_t := hwt.mem_fits
    have hfit_k1 : Fits w (k + 1) := hfit_off.of_le (by omega)
    have hfit_ok1 : Fits w (dstOff + k + 1) := hfit_off.of_le (by omega)
    let Sk := Set.Ico (dstBase + 4 * (dstOff + k)) (dstBase + 4 * (dstOff + k) + 4)
    have hft_s : Memory.FramedTriple w t (copyStride4Step (e, (k, dstOff + k))) 8 Sk
        fun a' t' =>
          a' = (k + 1, dstOff + (k + 1)) ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
          stride4At dstBase (dstOff + k)
            ⟨t.mem (srcBase + 4 * k), t.mem (srcBase + 4 * k + 1),
              t.mem (srcBase + 4 * k + 2), t.mem (srcBase + 4 * k + 3)⟩ t'.mem := by
      have hsub : Memory.FramedTriple w t (readStride4 (srcBase, k)) 4 Sk fun ew t₁ =>
          Memory.FramedTriple w t₁ (writeStride4 ((dstBase, dstOff + k), ew) >>= fun nextOff =>
            pure (k + 1, nextOff)) 4 Sk fun a' t' =>
              a' = (k + 1, dstOff + (k + 1)) ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
              stride4At dstBase (dstOff + k)
                ⟨t.mem (srcBase + 4 * k), t.mem (srcBase + 4 * k + 1),
                  t.mem (srcBase + 4 * k + 2), t.mem (srcBase + 4 * k + 3)⟩ t'.mem := by
        refine (hr.frame_mono (Set.empty_subset Sk)).mono le_rfl fun ew t₁ ⟨hew, ht₁⟩ => ?_
        rw [ht₁, hew]
        have hw := writeStride4_spec (w := w) (dst := dstBase) (idx := dstOff + k)
          (ew := ⟨t.mem (srcBase + 4 * k), t.mem (srcBase + 4 * k + 1),
            t.mem (srcBase + 4 * k + 2), t.mem (srcBase + 4 * k + 3)⟩)
          hwt (hmem_t _) (hmem_t _) (hmem_t _) (hmem_t _) (by rw [htfr]; omega)
        exact ((hw.mono le_rfl fun nextOff t' ⟨hnext, hfr', hwt', hstr⟩ =>
          Memory.FramedTriple.pure (c := 0) (a := (k + 1, nextOff))
            ⟨by rw [hnext, Nat.add_assoc], hfr'.trans htfr, hwt', hstr⟩).bind_same).mono
          (Nat.add_zero 4).le fun _ _ h => h
      exact hsub.bind_same.mono (by omega) fun _ _ h => h
    obtain ⟨hv_s, hc_s, hmod_s, hres_s, ht'_fr, hwt', hstr_k⟩ :=
      framedTriple_iff_realization.mp hft_s
    have hr_spec := framedTriple_iff_realization.mp hr
    obtain ⟨hr_ew, hr_st⟩ := hr_spec.2.2.2
    have hsafe_s : copyStride4StepSafe w (e, (k, dstOff + k)) t := by
      refine ⟨h16, hfit_k1, ⟨h16, by dsimp only [e]; rw [htfr]; omega⟩, ?_⟩
      rw [hr_st, hr_ew]
      exact ⟨h16, hfit_ok1, hmem_t _, hmem_t _, hmem_t _, hmem_t _,
        by dsimp only [e]; rw [htfr]; omega⟩
    have hmod_S : Memory.Modifies S t
        ((Memory.spec 0).clientState t (copyStride4Step (e, (k, dstOff + k)))) :=
      hmod_s.mono fun x hx => by simp only [Sk, S, Set.mem_Ico] at hx ⊢; omega
    have hmem_keep : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (copyStride4Step (e, (k, dstOff + k)))).mem x =
          t.mem x :=
      fun x hx => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) x fun hxk => by
        simp only [Sk, S, Set.mem_Ico] at hx hxk; omega
    refine ⟨hsafe_s, hv_s, by omega, hmod_S, ?_⟩
    dsimp only [inv]
    refine ⟨hres_s, ht'_fr, hwt', fun x hx => (hmem_keep x hx).trans (hframe x hx),
      fun hd i hi => ?_⟩
    by_cases hik : i = k
    · subst i
      have hsrc_mem : ∀ q < 4, t.mem (srcBase + 4 * k + q) = s.mem (srcBase + 4 * k + q) :=
        fun q hq => hframe _ (by simp only [S, Set.mem_Ico]; rcases hd with hdl | hdr <;> omega)
      have ha0 : dstBase + 4 * (dstOff + k) = dstBase + 4 * dstOff + 4 * k := by omega
      have h0 : t.mem (srcBase + 4 * k) = s.mem (srcBase + 4 * k) := by
        simpa using hsrc_mem 0 (by decide)
      dsimp only [stride4At] at hstr_k ⊢
      rw [ha0, h0, hsrc_mem 1 (by decide), hsrc_mem 2 (by decide),
        hsrc_mem 3 (by decide)] at hstr_k
      exact hstr_k
    · exact stride4At_congr (fun q hq => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) _
        (by simp only [Sk, Set.mem_Ico]; omega)) (hpref hd i (by omega))
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, hres_it, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec copyStride4Step copyStride4StepSafe w e 8 count inv (fun _ _ _ => 0)
      S hstep (0, dstOff) s
      ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, iterate_bind_snd_ft hv_it (by simpa using hm_it) hmod_it
    ⟨congrArg Prod.snd hres_it, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `copyStride4Prog`. -/
theorem realizes_copyStride4Prog : Realizes .exact
    copyStride4Prog
    (WordEncoding.encode (α := CopyStride4Env × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    copyStride4ProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : CopyStride4Env × ℕ × ℕ => do
        let st ← iterate copyStride4Step d.1 d.2.2 (0, d.2.1)
        pure st.2)
      (WordEncoding.encode (α := CopyStride4Env × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => Fits w 16 ∧
        iterationSafe copyStride4Step copyStride4StepSafe w d.1 d.2.2 (0, d.2.1) s)
      (fun _ _ => 0) := by
    realize [realizes_copyStride4Step]
    exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine (hraw.congr fun ⟨_, _, _⟩ => rfl).consequence (fun w d s _ hmem h => ?_)
    (fun _ _ => le_rfl)
  rcases d with ⟨e, dstOff, count⟩
  obtain ⟨h16, hsrc, hdst, hfit⟩ := h
  exact ⟨h16, (copyStride4Prog_word_spec h16 hmem hsrc hdst hfit).1⟩

/-- Framed specification for `copyStride4Prog`: copies `srcEs` into `dstBase + 4 * dstOff`,
modifying only `Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + srcEs.length))`, in at
most `8 * srcEs.length` memory operations. -/
theorem copyStride4Prog_spec {w n srcBase dstBase dstOff : ℕ}
    {srcEs : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges srcBase srcEs s.mem)
    (hin_lt : srcBase + 4 * srcEs.length ≤ s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + srcEs.length) ≤ s.frontier)
    (hdisj : srcBase + 4 * srcEs.length ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + srcEs.length) ≤ srcBase)
    (hfit_off : Fits w (dstOff + srcEs.length + 1)) :
    Memory.FramedTriple w s (copyStride4Prog (⟨srcBase, dstBase⟩, dstOff, srcEs.length))
      (8 * srcEs.length) (Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + srcEs.length)))
      fun res s' =>
        res = dstOff + srcEs.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges (dstBase + 4 * dstOff) srcEs s'.mem := by
  refine (copyStride4Prog_word_spec h16 hwf hin_lt hdst_lt hfit_off).2.mono le_rfl
    fun res s' ⟨hres, hfr, hwf', hvals⟩ => ⟨hres, hfr, hwf', fun i hi => ?_⟩
  obtain ⟨hu, hv, hw, hid⟩ := hin i hi
  obtain ⟨h0, h1, h2, h3⟩ := hvals hdisj i hi
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3.trans hid⟩

/-! ### `concatThreeProg`: Concatenate Three Stride-4 Edge Arrays via `RecordOps` -/

private def edgeToRecord {n : ℕ} (e : IndexedEdge n) : Fin 4 → ℕ
  | 0 => e.u.val
  | 1 => e.v.val
  | 2 => e.weight
  | 3 => e.id

private theorem holdsIndexedEdges_iff_holdsRecords {n : ℕ} (base : ℕ)
    (es : List (IndexedEdge n)) (mem : ℕ → ℕ) :
    HoldsIndexedEdges base es mem ↔ HoldsRecords 4 base (es.map edgeToRecord) mem := by
  constructor
  · intro h i hi j
    have hi' : i < es.length := by simpa using hi
    obtain ⟨hu, hv, hw, hid⟩ := h i hi'
    rcases j with ⟨_ | _ | _ | _ | k, hj⟩
    · simp only [List.getElem_map, edgeToRecord, Nat.add_zero]; exact hu
    · simp only [List.getElem_map, edgeToRecord]; exact hv
    · simp only [List.getElem_map, edgeToRecord]; exact hw
    · simp only [List.getElem_map, edgeToRecord]; exact hid
    · omega
  · intro h i hi
    have hi' : i < (es.map edgeToRecord).length := by simpa using hi
    have h0 := h i hi' 0
    have h1 := h i hi' 1
    have h2 := h i hi' 2
    have h3 := h i hi' 3
    simp only [List.getElem_map, edgeToRecord] at h0 h1 h2 h3
    exact ⟨h0, h1, h2, h3⟩

/-- Concatenate three stride-4 edge arrays into a newly dirty-allocated block via
`RecordOps.concatRecordsProg`, returning `(outBase, a.l1 + a.l2 + a.l3)`. -/
def concatThreeProg (a : ConcatThreeArgs) : Memory.Prog (ℕ × ℕ) := do
  let blk ← concatRecordsProg ⟨4, a.b1, a.l1, a.b2, a.l2, a.b3, a.l3⟩
  pure (blk.base, a.l1 + a.l2 + a.l3)

/-- Safety domain for `concatThreeProg`. -/
@[expose] def concatThreeProgSafe (w : ℕ) (a : ConcatThreeArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (s.frontier + 4 * (a.l1 + a.l2 + a.l3)) ∧
    a.b1 + 4 * a.l1 ≤ s.frontier ∧ a.b2 + 4 * a.l2 ≤ s.frontier ∧ a.b3 + 4 * a.l3 ≤ s.frontier

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `concatThreeProg`. -/
theorem realizes_concatThreeProg : Realizes .exact
    concatThreeProg (WordEncoding.encode (α := ConcatThreeArgs)) (WordEncoding.encode (α := ℕ × ℕ))
    concatThreeProgSafe (fun _ _ => 0) := by
  unfold concatThreeProg
  realize [realizes_concatRecordsProg]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2.1
    | exact h.2.2.2.2
    | (have h16 := h.1; have hfit := h.2.1; fits)

/-- Framed specification for `concatThreeProg`: concatenates `L1`, `L2`, and `L3` into a freshly
dirty-allocated stride-4 array at `s.frontier`, leaving all cells below `s.frontier` untouched
(`Modifies ∅`), in at most `8 * (L1.length + L2.length + L3.length) + 1` memory operations. -/
theorem concatThreeProg_spec {w n b1 b2 b3 : ℕ}
    {L1 L2 L3 : List (IndexedEdge n)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (h1 : HoldsIndexedEdges b1 L1 s.mem) (h1_lt : b1 + 4 * L1.length ≤ s.frontier)
    (h2 : HoldsIndexedEdges b2 L2 s.mem) (h2_lt : b2 + 4 * L2.length ≤ s.frontier)
    (h3 : HoldsIndexedEdges b3 L3 s.mem) (h3_lt : b3 + 4 * L3.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * (L1.length + L2.length + L3.length))) :
    Memory.FramedTriple w s
      (concatThreeProg ⟨b1, L1.length, b2, L2.length, b3, L3.length⟩)
      (8 * (L1.length + L2.length + L3.length) + 1) ∅
      fun res s' =>
        res = (s.frontier, L1.length + L2.length + L3.length) ∧
        s'.frontier = s.frontier + 4 * (L1.length + L2.length + L3.length) ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges res.1 (L1 ++ L2 ++ L3) s'.mem := by
  have hR1 := (holdsIndexedEdges_iff_holdsRecords b1 L1 s.mem).mp h1
  have hR2 := (holdsIndexedEdges_iff_holdsRecords b2 L2 s.mem).mp h2
  have hR3 := (holdsIndexedEdges_iff_holdsRecords b3 L3 s.mem).mp h3
  have hc := concatRecordsProg_spec (w := w) (stride := 4)
    (srcA := b1) (srcB := b2) (srcC := b3)
    (rowsA := L1.map edgeToRecord) (rowsB := L2.map edgeToRecord)
    (rowsC := L3.map edgeToRecord) hwf
    hR1 (by simpa using h1_lt) hR2 (by simpa using h2_lt) hR3 (by simpa using h3_lt)
    (by simpa using hfit)
  simp only [List.length_map] at hc
  have hprog : concatThreeProg ⟨b1, L1.length, b2, L2.length, b3, L3.length⟩ =
      (concatRecordsProg ⟨4, b1, L1.length, b2, L2.length, b3, L3.length⟩ >>= fun blk =>
        pure (blk.base, L1.length + L2.length + L3.length)) := rfl
  rw [hprog]
  refine (Memory.FramedTriple.bind_same (hc.mono le_rfl fun blk s' ⟨hblk, _, hfr, hwf', hrows⟩ =>
    Memory.FramedTriple.pure (c := 0) (a := (blk.base, L1.length + L2.length + L3.length))
      ⟨by rw [hblk], hfr, hwf', ?_⟩)).mono (by omega) fun _ _ h => h
  dsimp only
  rw [holdsIndexedEdges_iff_holdsRecords, List.map_append, List.map_append]
  exact hrows

/-! ### `liftEdgesProg`: Lift Local Stride-4 Edges to Global Vertices -/

private def liftEdgeRead (d : LiftEdgesEnv × ℕ) : Memory.Prog Stride4Words := do
  let u ← Memory.read (d.1.edgeBase + 4 * d.2)
  let v ← Memory.read (d.1.edgeBase + 4 * d.2 + 1)
  let u' ← Memory.read (d.1.liftBase + u)
  let v' ← Memory.read (d.1.liftBase + v)
  let wt ← Memory.read (d.1.edgeBase + 4 * d.2 + 2)
  let eid ← Memory.read (d.1.edgeBase + 4 * d.2 + 3)
  pure ⟨u', v', wt, eid⟩

private def liftEdgeReadSafe (w : ℕ) (d : LiftEdgesEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1.edgeBase + 4 * d.2 + 3 < s.frontier ∧
    let u := s.mem (d.1.edgeBase + 4 * d.2)
    let v := s.mem (d.1.edgeBase + 4 * d.2 + 1)
    d.1.liftBase + u < s.frontier ∧ d.1.liftBase + v < s.frontier

private theorem realizes_liftEdgeRead_history : Realizes .exact
    liftEdgeRead
    (appendWords (WordEncoding.encode (α := LiftEdgesEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := Stride4Words))
    (fun w d s => liftEdgeReadSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (liftEdgeRead d)))
    (fun _ _ => 0) := by
  unfold liftEdgeRead
  realize
  all_goals
    obtain ⟨⟨h16, h1, h2, h3⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.step_read, Memory.valid]
  all_goals fits

private theorem realizes_liftEdgeRead : Realizes .exact
    liftEdgeRead
    (appendWords (WordEncoding.encode (α := LiftEdgesEnv)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := Stride4Words)) liftEdgeReadSafe (fun _ _ => 0) :=
  realizes_liftEdgeRead_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private theorem liftEdgeRead_spec {w edgeBase liftBase dstBase idx : ℕ} {s : Memory.State}
    (hlt : edgeBase + 4 * idx + 3 < s.frontier)
    (hu_lt : liftBase + s.mem (edgeBase + 4 * idx) < s.frontier)
    (hv_lt : liftBase + s.mem (edgeBase + 4 * idx + 1) < s.frontier) :
    let e : LiftEdgesEnv := ⟨edgeBase, liftBase, dstBase⟩
    Memory.FramedTriple w s (liftEdgeRead (e, idx)) 6 ∅ fun res s' =>
      res = ⟨s.mem (liftBase + s.mem (edgeBase + 4 * idx)),
        s.mem (liftBase + s.mem (edgeBase + 4 * idx + 1)),
        s.mem (edgeBase + 4 * idx + 2), s.mem (edgeBase + 4 * idx + 3)⟩ ∧ s' = s := by
  let e : LiftEdgesEnv := ⟨edgeBase, liftBase, dstBase⟩
  have hprog : liftEdgeRead (e, idx) =
      (Memory.read (edgeBase + 4 * idx) >>= fun u =>
        Memory.read (edgeBase + 4 * idx + 1) >>= fun v =>
          Memory.read (liftBase + u) >>= fun u' =>
            Memory.read (liftBase + v) >>= fun v' =>
              Memory.read (edgeBase + 4 * idx + 2) >>= fun wt =>
                Memory.read (edgeBase + 4 * idx + 3) >>= fun eid => pure ⟨u', v', wt, eid⟩) := rfl
  have hvh : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (liftEdgeRead (e, idx))) := by
    rw [hprog]; valid_prog; all_goals omega
  have hst : (Memory.spec 0).clientState s (liftEdgeRead (e, idx)) = s := by
    rw [hprog]; repeat rw [clientState_bind_read]; rfl
  refine framedTriple_iff_realization.mpr ⟨hvh, ?_, ?_, ?_, hst⟩
  · rw [hprog]; prog_cost
  · rw [hst]; exact Memory.Modifies.refl ∅ s
  · rw [hprog]; simp only [clientResult_bind_read, StateTransitionSpec.clientResult_pure]

private def liftEdgeStep (d : LiftEdgesEnv × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let ew ← liftEdgeRead (d.1, d.2.1)
  let nextOff ← writeStride4 ((d.1.dstBase, d.2.2), ew)
  pure (d.2.1 + 1, nextOff)

private def liftEdgeStepSafe (w : ℕ) (d : LiftEdgesEnv × (ℕ × ℕ)) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2.1 + 1) ∧ liftEdgeReadSafe w (d.1, d.2.1) s ∧
    let ew := (Memory.spec 0).clientResult s (liftEdgeRead (d.1, d.2.1))
    let s1 := (Memory.spec 0).clientState s (liftEdgeRead (d.1, d.2.1))
    writeStride4Safe w ((d.1.dstBase, d.2.2), ew) s1

private theorem realizes_liftEdgeStep : Realizes .exact
    liftEdgeStep
    (appendWords (WordEncoding.encode (α := LiftEdgesEnv)) (WordEncoding.encode (α := ℕ × ℕ)))
    (WordEncoding.encode (α := ℕ × ℕ)) liftEdgeStepSafe (fun _ _ => 0) := by
  unfold liftEdgeStep
  realize [realizes_liftEdgeRead, realizes_writeStride4]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2
    | (have h16 := h.1; have hfit1 := h.2.1; fits)

/-- Lift `count` local stride-4 edges at `e.edgeBase` through vertex table `e.liftBase` into
`e.dstBase` starting at offset `dstOff`, returning `dstOff + count`. -/
def liftEdgesProg : LiftEdgesEnv × ℕ × ℕ → Memory.Prog ℕ
  | (e, dstOff, count) => do
    let st ← iterate liftEdgeStep e count (0, dstOff)
    pure st.2

/-- Safety domain for `liftEdgesProg`. -/
@[expose] def liftEdgesProgSafe (w : ℕ) : LiftEdgesEnv × ℕ × ℕ → Memory.State → Prop
  | (e, dstOff, count), s =>
    Fits w 16 ∧ e.edgeBase + 4 * count ≤ s.frontier ∧
      (e.edgeBase + 4 * count ≤ e.dstBase + 4 * dstOff ∨
        e.dstBase + 4 * (dstOff + count) ≤ e.edgeBase) ∧
      (∀ k < count,
        e.liftBase + s.mem (e.edgeBase + 4 * k) < s.frontier ∧
        e.liftBase + s.mem (e.edgeBase + 4 * k + 1) < s.frontier) ∧
      e.dstBase + 4 * (dstOff + count) ≤ s.frontier ∧ Fits w (dstOff + count + 1)

private theorem liftEdgesProg_word_spec {w edgeBase liftBase dstBase dstOff count : ℕ}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsrc_lt : edgeBase + 4 * count ≤ s.frontier)
    (hdisj_e : edgeBase + 4 * count ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + count) ≤ edgeBase)
    (hlb : ∀ k < count, liftBase + s.mem (edgeBase + 4 * k) < s.frontier ∧
      liftBase + s.mem (edgeBase + 4 * k + 1) < s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + count) ≤ s.frontier)
    (hfit_off : Fits w (dstOff + count + 1)) :
    let e : LiftEdgesEnv := ⟨edgeBase, liftBase, dstBase⟩
    let S := Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + count))
    iterationSafe liftEdgeStep liftEdgeStepSafe w e count (0, dstOff) s ∧
    Memory.FramedTriple w s (liftEdgesProg (e, dstOff, count)) (10 * count) S
      fun res s' =>
        res = dstOff + count ∧ s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ((∀ k < count, liftBase + s.mem (edgeBase + 4 * k) ∉ S ∧
          liftBase + s.mem (edgeBase + 4 * k + 1) ∉ S) →
          ∀ i < count, stride4At (dstBase + 4 * dstOff) i
            ⟨s.mem (liftBase + s.mem (edgeBase + 4 * i)),
              s.mem (liftBase + s.mem (edgeBase + 4 * i + 1)),
              s.mem (edgeBase + 4 * i + 2), s.mem (edgeBase + 4 * i + 3)⟩ s'.mem) := by
  let e : LiftEdgesEnv := ⟨edgeBase, liftBase, dstBase⟩
  let S : Set ℕ := Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + count))
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a = (k, dstOff + k) ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ((∀ j < count, liftBase + s.mem (edgeBase + 4 * j) ∉ S ∧
      liftBase + s.mem (edgeBase + 4 * j + 1) ∉ S) →
      ∀ i < k, stride4At (dstBase + 4 * dstOff) i
        ⟨s.mem (liftBase + s.mem (edgeBase + 4 * i)),
          s.mem (liftBase + s.mem (edgeBase + 4 * i + 1)),
          s.mem (edgeBase + 4 * i + 2), s.mem (edgeBase + 4 * i + 3)⟩ t.mem)
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      liftEdgeStepSafe w (e, a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (liftEdgeStep (e, a))) ∧
      let a' := (Memory.spec 0).clientResult t (liftEdgeStep (e, a))
      let t' := (Memory.spec 0).clientState t (liftEdgeStep (e, a))
      memoryCost (liftEdgeStep (e, a)) t + 0 ≤ 0 + 10 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hsrc_mem : ∀ q < 4, t.mem (edgeBase + 4 * k + q) = s.mem (edgeBase + 4 * k + q) :=
      fun q hq => hframe _ (by simp only [S, Set.mem_Ico]; rcases hdisj_e with hd | hd <;> omega)
    have hlu_eq : t.mem (edgeBase + 4 * k) = s.mem (edgeBase + 4 * k) := by
      simpa using hsrc_mem 0 (by decide)
    have hlv_eq : t.mem (edgeBase + 4 * k + 1) = s.mem (edgeBase + 4 * k + 1) :=
      hsrc_mem 1 (by decide)
    have hu_lt : liftBase + t.mem (edgeBase + 4 * k) < t.frontier := by
      rw [hlu_eq, htfr]; exact (hlb k hk).1
    have hv_lt : liftBase + t.mem (edgeBase + 4 * k + 1) < t.frontier := by
      rw [hlv_eq, htfr]; exact (hlb k hk).2
    have hr := liftEdgeRead_spec (w := w) (edgeBase := edgeBase) (liftBase := liftBase)
      (dstBase := dstBase) (idx := k) (s := t) (by omega) hu_lt hv_lt
    have hmem_t := hwt.mem_fits
    have hfit_k1 : Fits w (k + 1) := hfit_off.of_le (by omega)
    have hfit_ok1 : Fits w (dstOff + k + 1) := hfit_off.of_le (by omega)
    let ew_t : Stride4Words :=
      ⟨t.mem (liftBase + t.mem (edgeBase + 4 * k)),
        t.mem (liftBase + t.mem (edgeBase + 4 * k + 1)),
        t.mem (edgeBase + 4 * k + 2), t.mem (edgeBase + 4 * k + 3)⟩
    let Sk := Set.Ico (dstBase + 4 * (dstOff + k)) (dstBase + 4 * (dstOff + k) + 4)
    have hft_s : Memory.FramedTriple w t (liftEdgeStep (e, (k, dstOff + k))) 10 Sk fun a' t' =>
        a' = (k + 1, dstOff + (k + 1)) ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
        stride4At dstBase (dstOff + k) ew_t t'.mem := by
      have hsub : Memory.FramedTriple w t (liftEdgeRead (e, k)) 6 Sk fun ew t₁ =>
          Memory.FramedTriple w t₁ (writeStride4 ((dstBase, dstOff + k), ew) >>= fun nextOff =>
            pure (k + 1, nextOff)) 4 Sk fun a' t' =>
              a' = (k + 1, dstOff + (k + 1)) ∧ t'.frontier = s.frontier ∧ Memory.WellFormed w t' ∧
              stride4At dstBase (dstOff + k) ew_t t'.mem := by
        refine (hr.frame_mono (Set.empty_subset Sk)).mono le_rfl fun ew t₁ ⟨hew, ht₁⟩ => ?_
        subst ht₁; rw [hew]
        have hw := writeStride4_spec (w := w) (dst := dstBase) (idx := dstOff + k) (ew := ew_t)
          hwt (hmem_t _) (hmem_t _) (hmem_t _) (hmem_t _) (by rw [htfr]; omega)
        exact ((hw.mono le_rfl fun nextOff t' ⟨hnext, hfr', hwt', hstr⟩ =>
          Memory.FramedTriple.pure (c := 0) (a := (k + 1, nextOff))
            ⟨by rw [hnext, Nat.add_assoc], hfr'.trans htfr, hwt', hstr⟩).bind_same).mono
          (Nat.add_zero 4).le fun _ _ h => h
      exact hsub.bind_same.mono (by omega) fun _ _ h => h
    obtain ⟨hv_s, hc_s, hmod_s, hres_s, ht'_fr, hwt', hstr_k⟩ :=
      framedTriple_iff_realization.mp hft_s
    have hr_spec := framedTriple_iff_realization.mp hr
    obtain ⟨hr_ew, hr_st⟩ := hr_spec.2.2.2
    have hsafe_s : liftEdgeStepSafe w (e, (k, dstOff + k)) t := by
      refine ⟨h16, hfit_k1, ⟨h16, by rw [htfr]; dsimp only [e]; omega, hu_lt, hv_lt⟩, ?_⟩
      rw [hr_st, hr_ew]
      exact ⟨h16, hfit_ok1, hmem_t _, hmem_t _, hmem_t _, hmem_t _,
        by rw [htfr]; dsimp only [e]; omega⟩
    have hmod_S : Memory.Modifies S t
        ((Memory.spec 0).clientState t (liftEdgeStep (e, (k, dstOff + k)))) :=
      hmod_s.mono fun x hx => by simp only [Sk, S, Set.mem_Ico] at hx ⊢; omega
    have hmem_keep : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (liftEdgeStep (e, (k, dstOff + k)))).mem x = t.mem x :=
      fun x hx => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) x fun hxk => by
        simp only [Sk, S, Set.mem_Ico] at hx hxk; omega
    refine ⟨hsafe_s, hv_s, by omega, hmod_S, ?_⟩
    dsimp only [inv]
    refine ⟨hres_s, ht'_fr, hwt', fun x hx => (hmem_keep x hx).trans (hframe x hx),
      fun hl i hi => ?_⟩
    by_cases hik : i = k
    · subst i
      have ha0 : dstBase + 4 * (dstOff + k) = dstBase + 4 * dstOff + 4 * k := by omega
      have hl0 : t.mem (liftBase + s.mem (edgeBase + 4 * k)) =
          s.mem (liftBase + s.mem (edgeBase + 4 * k)) := hframe _ (hl k hk).1
      have hl1 : t.mem (liftBase + s.mem (edgeBase + 4 * k + 1)) =
          s.mem (liftBase + s.mem (edgeBase + 4 * k + 1)) := hframe _ (hl k hk).2
      dsimp only [stride4At, ew_t] at hstr_k ⊢
      rw [ha0, hlu_eq, hlv_eq, hl0, hl1, hsrc_mem 2 (by decide),
        hsrc_mem 3 (by decide)] at hstr_k
      exact hstr_k
    · exact stride4At_congr (fun q hq => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) _
        (by simp only [Sk, Set.mem_Ico]; omega)) (hpref hl i (by omega))
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, hres_it, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec liftEdgeStep liftEdgeStepSafe w e 10 count inv (fun _ _ _ => 0)
      S hstep (0, dstOff) s
      ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, iterate_bind_snd_ft hv_it (by simpa using hm_it) hmod_it
    ⟨congrArg Prod.snd hres_it, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `liftEdgesProg`. -/
theorem realizes_liftEdgesProg : Realizes .exact
    liftEdgesProg
    (WordEncoding.encode (α := LiftEdgesEnv × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    liftEdgesProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : LiftEdgesEnv × ℕ × ℕ => do
        let st ← iterate liftEdgeStep d.1 d.2.2 (0, d.2.1)
        pure st.2)
      (WordEncoding.encode (α := LiftEdgesEnv × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => Fits w 16 ∧
        iterationSafe liftEdgeStep liftEdgeStepSafe w d.1 d.2.2 (0, d.2.1) s)
      (fun _ _ => 0) := by
    realize [realizes_liftEdgeStep]
    exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine (hraw.congr fun ⟨_, _, _⟩ => rfl).consequence (fun w d s _ hmem h => ?_)
    (fun _ _ => le_rfl)
  rcases d with ⟨e, dstOff, count⟩
  obtain ⟨h16, hsrc, hde, hlb, hdst, hfit⟩ := h
  exact ⟨h16, (liftEdgesProg_word_spec h16 hmem hsrc hde hlb hdst hfit).1⟩

/-- Framed specification for `liftEdgesProg`: writes `C` with endpoints lifted through `lift`
into `dstBase + 4 * dstOff`, modifying only
`Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length))`, in at most `10 * C.length`
memory operations. -/
theorem liftEdgesProg_spec {w nLoc nGlob edgeBase liftBase dstBase dstOff : ℕ}
    {C : List (IndexedEdge nLoc)} {lift : Fin nLoc → Fin nGlob} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase C s.mem)
    (hin_lt : edgeBase + 4 * C.length ≤ s.frontier)
    (hlift : ∀ k : Fin nLoc, s.mem (liftBase + k.val) = (lift k).val)
    (hlift_lt : liftBase + nLoc ≤ s.frontier)
    (hdst_lt : dstBase + 4 * (dstOff + C.length) ≤ s.frontier)
    (hdisj_e : edgeBase + 4 * C.length ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + C.length) ≤ edgeBase)
    (hdisj_l : liftBase + nLoc ≤ dstBase + 4 * dstOff ∨
      dstBase + 4 * (dstOff + C.length) ≤ liftBase)
    (hfit_off : Fits w (dstOff + C.length + 1)) :
    Memory.FramedTriple w s
      (liftEdgesProg (⟨edgeBase, liftBase, dstBase⟩, dstOff, C.length))
      (10 * C.length) (Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length)))
      fun res s' =>
        res = dstOff + C.length ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges (dstBase + 4 * dstOff)
          (C.map fun x => (⟨lift x.u, lift x.v, x.weight, x.id⟩ : IndexedEdge nGlob)) s'.mem := by
  have hlb : ∀ k < C.length, liftBase + s.mem (edgeBase + 4 * k) < s.frontier ∧
      liftBase + s.mem (edgeBase + 4 * k + 1) < s.frontier := fun k hk => by
    obtain ⟨hu, hv, _, _⟩ := hin k hk
    rw [hu, hv]
    exact ⟨by have := C[k].u.isLt; omega, by have := C[k].v.isLt; omega⟩
  have hnl : ∀ k < C.length,
      liftBase + s.mem (edgeBase + 4 * k) ∉
        Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length)) ∧
      liftBase + s.mem (edgeBase + 4 * k + 1) ∉
        Set.Ico (dstBase + 4 * dstOff) (dstBase + 4 * (dstOff + C.length)) := fun k hk => by
    obtain ⟨hu, hv, _, _⟩ := hin k hk
    rw [hu, hv]
    simp only [Set.mem_Ico]
    have h1 := C[k].u.isLt
    have h2 := C[k].v.isLt
    rcases hdisj_l with hdl | hdr <;> exact ⟨by omega, by omega⟩
  refine (liftEdgesProg_word_spec h16 hwf hin_lt hdisj_e hlb hdst_lt hfit_off).2.mono le_rfl
    fun res s' ⟨hres, hfr, hwf', hvals⟩ => ⟨hres, hfr, hwf', fun i hi => ?_⟩
  have hi' : i < C.length := by simpa using hi
  obtain ⟨hu, hv, hw, hid⟩ := hin i hi'
  obtain ⟨h0, h1, h2, h3⟩ := hvals hnl i hi'
  simp only [List.getElem_map]
  rw [hu, hlift C[i].u] at h0
  rw [hv, hlift C[i].v] at h1
  exact ⟨h0, h1, h2.trans hw, h3.trans hid⟩

/-! ### `liftHRemProg`: Gather Selected `H_rem` Edges by Original Identifier -/

private def liftHRemRead (d : (ℕ × ℕ) × ℕ) : Memory.Prog Stride4Words := do
  let idx ← Memory.read (d.1.2 + 4 * d.2 + 3)
  readStride4 (d.1.1, idx)

private def liftHRemReadSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.1.2 + 4 * d.2 + 3 < s.frontier ∧
    readStride4Safe w (d.1.1, s.mem (d.1.2 + 4 * d.2 + 3)) s

private theorem realizes_liftHRemRead : Realizes .exact
    liftHRemRead
    (appendWords (WordEncoding.encode (α := ℕ × ℕ)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := Stride4Words)) liftHRemReadSafe (fun _ _ => 0) := by
  unfold liftHRemRead
  realize [realizes_readStride4]
  all_goals first
    | exact h.2.2
    | (have h16 := h.1; have hlt := h.2.1; have hfront := hmem.frontier_fits; fits)

private theorem liftHRemRead_spec {w hRemBase msfBase idx : ℕ} {s : Memory.State}
    (hmsf_lt : msfBase + 4 * idx + 3 < s.frontier)
    (hrem_lt : hRemBase + 4 * s.mem (msfBase + 4 * idx + 3) + 3 < s.frontier) :
    let eIdx := s.mem (msfBase + 4 * idx + 3)
    Memory.FramedTriple w s (liftHRemRead ((hRemBase, msfBase), idx)) 5 ∅ fun res s' =>
      res = ⟨s.mem (hRemBase + 4 * eIdx), s.mem (hRemBase + 4 * eIdx + 1),
        s.mem (hRemBase + 4 * eIdx + 2), s.mem (hRemBase + 4 * eIdx + 3)⟩ ∧ s' = s :=
  Memory.FramedTriple.read_bind hmsf_lt (readStride4_spec hrem_lt)

private def liftHRemStep (d : (ℕ × ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let ew ← liftHRemRead ((d.1.1, d.1.2.1), d.2)
  writeStride4 ((d.1.2.2, d.2), ew)

private def liftHRemStepSafe (w : ℕ) (d : (ℕ × ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.2 + 1) ∧ liftHRemReadSafe w ((d.1.1, d.1.2.1), d.2) s ∧
    let ew := (Memory.spec 0).clientResult s (liftHRemRead ((d.1.1, d.1.2.1), d.2))
    let s1 := (Memory.spec 0).clientState s (liftHRemRead ((d.1.1, d.1.2.1), d.2))
    writeStride4Safe w ((d.1.2.2, d.2), ew) s1

private theorem realizes_liftHRemStep : Realizes .exact
    liftHRemStep
    (appendWords (WordEncoding.encode (α := ℕ × ℕ × ℕ)) (WordEncoding.encode (α := ℕ)))
    (WordEncoding.encode (α := ℕ)) liftHRemStepSafe (fun _ _ => 0) := by
  unfold liftHRemStep
  realize [realizes_liftHRemRead, realizes_writeStride4]
  · exact h.2.2.1
  · exact h.2.2.2

/-- Gather `count` edges from `hRemBase` indexed by the `.id` fields of stride-4 records at
`msfBase`, returning the base address of a newly allocated dirty stride-4 edge array. -/
def liftHRemProg : ℕ × ℕ × ℕ → Memory.Prog ℕ
  | (hRemBase, msfBase, count) => do
    let outBase ← Memory.allocDirty (4 * count)
    let _ ← iterate liftHRemStep (hRemBase, msfBase, outBase) count 0
    pure outBase

/-- Safety domain for `liftHRemProg`. -/
@[expose] def liftHRemProgSafe (w : ℕ) : ℕ × ℕ × ℕ → Memory.State → Prop
  | (hRemBase, msfBase, count), s =>
    Fits w 16 ∧ msfBase + 4 * count ≤ s.frontier ∧
      (∀ k < count, hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 4 ≤ s.frontier) ∧
      Fits w (s.frontier + 4 * count)

private theorem liftHRemProg_word_spec {w hRemBase msfBase count : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hmsf_lt : msfBase + 4 * count ≤ s.frontier)
    (hids_lt : ∀ k < count, hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 4 ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * count)) :
    let prog := liftHRemProg (hRemBase, msfBase, count)
    iterationSafe liftHRemStep liftHRemStepSafe w (hRemBase, msfBase, s.frontier) count 0
      ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s prog (9 * count + 1) ∅ fun outBase s' =>
      outBase = s.frontier ∧ s'.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s' ∧
      ∀ i < count,
        let eIdx := s.mem (msfBase + 4 * i + 3)
        stride4At outBase i ⟨s.mem (hRemBase + 4 * eIdx), s.mem (hRemBase + 4 * eIdx + 1),
          s.mem (hRemBase + 4 * eIdx + 2), s.mem (hRemBase + 4 * eIdx + 3)⟩ s'.mem := by
  let outBase := s.frontier
  let s₀ : Memory.State := ⟨s.mem, s.frontier + 4 * count⟩
  have hs₀_fr : s₀.frontier = s.frontier + 4 * count := rfl
  let S : Set ℕ := Set.Ico outBase (outBase + 4 * count)
  have hwf₀ : Memory.WellFormed w s₀ := ⟨hfit, hwf.mem_fits⟩
  have hfit_m1 : Fits w (count + 1) := by
    rcases count with _ | m
    · exact h16.of_le (by omega)
    · exact hfit.of_le (by omega)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s₀.frontier ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ∀ i < k,
      let eIdx := s.mem (msfBase + 4 * i + 3)
      stride4At outBase i ⟨s.mem (hRemBase + 4 * eIdx), s.mem (hRemBase + 4 * eIdx + 1),
        s.mem (hRemBase + 4 * eIdx + 2), s.mem (hRemBase + 4 * eIdx + 3)⟩ t.mem
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      liftHRemStepSafe w ((hRemBase, msfBase, outBase), a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (liftHRemStep ((hRemBase, msfBase, outBase), a))) ∧
      let a' := (Memory.spec 0).clientResult t (liftHRemStep ((hRemBase, msfBase, outBase), a))
      let t' := (Memory.spec 0).clientState t (liftHRemStep ((hRemBase, msfBase, outBase), a))
      memoryCost (liftHRemStep ((hRemBase, msfBase, outBase), a)) t + 0 ≤ 0 + 9 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hidx_eq : t.mem (msfBase + 4 * k + 3) = s.mem (msfBase + 4 * k + 3) :=
      hframe _ (by simp only [S, Set.mem_Ico, outBase]; omega)
    have hrem_bound := hids_lt k hk
    have hrem_mem : ∀ q < 4, t.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + q) =
        s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + q) := fun q hq =>
      hframe _ (by simp only [S, Set.mem_Ico, outBase]; omega)
    have hr := liftHRemRead_spec (w := w) (hRemBase := hRemBase) (msfBase := msfBase)
      (idx := k) (s := t) (by rw [htfr, hs₀_fr]; omega)
      (by rw [htfr, hs₀_fr, hidx_eq]; omega)
    have hmem_t := hwt.mem_fits
    have hfit_k1 : Fits w (k + 1) := hfit_m1.of_le (by omega)
    let ew_s : Stride4Words :=
      ⟨s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3)),
        s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 1),
        s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 2),
        s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 3)⟩
    let Sk := Set.Ico (outBase + 4 * k) (outBase + 4 * k + 4)
    have hft_s : Memory.FramedTriple w t (liftHRemStep ((hRemBase, msfBase, outBase), k)) 9 Sk
        fun a' t' =>
          a' = k + 1 ∧ t'.frontier = s₀.frontier ∧ Memory.WellFormed w t' ∧
          stride4At outBase k ew_s t'.mem := by
      have hsub : Memory.FramedTriple w t (liftHRemRead ((hRemBase, msfBase), k)) 5 Sk
          fun ew t₁ =>
            Memory.FramedTriple w t₁ (writeStride4 ((outBase, k), ew)) 4 Sk fun a' t' =>
              a' = k + 1 ∧ t'.frontier = s₀.frontier ∧ Memory.WellFormed w t' ∧
              stride4At outBase k ew_s t'.mem := by
        refine (hr.frame_mono (Set.empty_subset Sk)).mono le_rfl fun ew t₁ ⟨hew, ht₁⟩ => ?_
        rw [ht₁, hew]
        have hw := writeStride4_spec (w := w) (dst := outBase) (idx := k)
          (ew := ⟨t.mem (hRemBase + 4 * t.mem (msfBase + 4 * k + 3)),
            t.mem (hRemBase + 4 * t.mem (msfBase + 4 * k + 3) + 1),
            t.mem (hRemBase + 4 * t.mem (msfBase + 4 * k + 3) + 2),
            t.mem (hRemBase + 4 * t.mem (msfBase + 4 * k + 3) + 3)⟩)
          hwt (hmem_t _) (hmem_t _) (hmem_t _) (hmem_t _)
          (by rw [htfr, hs₀_fr]; dsimp only [outBase]; omega)
        refine hw.mono le_rfl fun res t' ⟨hres, hfr', hwt', hstr⟩ =>
          ⟨hres, hfr'.trans htfr, hwt', ?_⟩
        have hrem0 : t.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3)) =
            s.mem (hRemBase + 4 * s.mem (msfBase + 4 * k + 3)) := by
          simpa using hrem_mem 0 (by decide)
        simpa only [hidx_eq, hrem0, hrem_mem 1 (by decide), hrem_mem 2 (by decide),
          hrem_mem 3 (by decide)] using hstr
      exact hsub.bind_same.mono (by omega) fun _ _ h => h
    obtain ⟨hv_s, hc_s, hmod_s, hres_s, ht'_fr, hwt', hstr_k⟩ :=
      framedTriple_iff_realization.mp hft_s
    have hr_spec := framedTriple_iff_realization.mp hr
    obtain ⟨hr_ew, hr_st⟩ := hr_spec.2.2.2
    have hsafe_s : liftHRemStepSafe w ((hRemBase, msfBase, outBase), k) t := by
      refine ⟨h16, hfit_k1, ⟨h16, by dsimp only; rw [htfr, hs₀_fr]; omega,
        ⟨h16, by dsimp only; rw [htfr, hs₀_fr, hidx_eq]; omega⟩⟩, ?_⟩
      rw [hr_st, hr_ew]
      exact ⟨h16, hfit_k1, hmem_t _, hmem_t _, hmem_t _, hmem_t _,
        by dsimp only; rw [htfr, hs₀_fr]; dsimp only [outBase]; omega⟩
    have hmod_S : Memory.Modifies S t
        ((Memory.spec 0).clientState t (liftHRemStep ((hRemBase, msfBase, outBase), k))) :=
      hmod_s.mono fun x hx => by
        simp only [Sk, S, Set.mem_Ico] at hx ⊢; dsimp only [outBase] at *; omega
    have hmem_keep : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (liftHRemStep ((hRemBase, msfBase, outBase), k))).mem x =
          t.mem x :=
      fun x hx => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) x fun hxk => by
        simp only [Sk, S, Set.mem_Ico] at hx hxk; dsimp only [outBase] at *; omega
    refine ⟨hsafe_s, hv_s, by omega, hmod_S, ?_⟩
    dsimp only [inv]
    refine ⟨hres_s, ht'_fr, hwt', fun x hx => (hmem_keep x hx).trans (hframe x hx),
      fun i hi => ?_⟩
    by_cases hik : i = k
    · subst i; exact hstr_k
    · exact stride4At_congr (fun q hq => hft_s.mem_eq_of_frontier_eq (ht'_fr.trans htfr.symm) _
        (by simp only [Sk, Set.mem_Ico]; omega)) (hpref i (by omega))
  obtain ⟨hsafe_it, hv_it, hm_it, hmod_it, _, hfr_it, hwf_it, _, hvals_it⟩ :=
    iterate_potential_spec liftHRemStep liftHRemStepSafe w (hRemBase, msfBase, outBase) 9 count
      inv (fun _ _ _ => 0) S hstep 0 s₀
      ⟨rfl, rfl, hwf₀, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  exact ⟨hsafe_it, allocDirty4_bind_pure_ft (S := S)
    (f := fun ob => iterate liftHRemStep (hRemBase, msfBase, ob) count 0)
    hfit (fun _ ha => ha.1) hv_it (by simpa using hm_it) hmod_it ⟨rfl, hfr_it, hwf_it, hvals_it⟩⟩

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `liftHRemProg`. -/
theorem realizes_liftHRemProg : Realizes .exact
    liftHRemProg (WordEncoding.encode (α := ℕ × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
    liftHRemProgSafe (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : ℕ × ℕ × ℕ => do
        let outBase ← Memory.allocDirty (4 * d.2.2)
        let _ ← iterate liftHRemStep (d.1, d.2.1, outBase) d.2.2 0
        pure outBase)
      (WordEncoding.encode (α := ℕ × ℕ × ℕ)) (WordEncoding.encode (α := ℕ))
      (fun w d s => Fits w 16 ∧ Fits w (s.frontier + 4 * d.2.2) ∧
        iterationSafe liftHRemStep liftHRemStepSafe w (d.1, d.2.1, s.frontier) d.2.2 0
          ⟨s.mem, s.frontier + 4 * d.2.2⟩)
      (fun _ _ => 0) := by
    realize [realizes_liftHRemStep]
    all_goals first
      | exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
      | (have h16 := h.1; have hf := h.2.1; have hfront := hmem.frontier_fits; fits)
  refine (hraw.congr fun ⟨_, _, _⟩ => rfl).consequence (fun w d s _ hmem h => ?_)
    (fun _ _ => le_rfl)
  rcases d with ⟨hRemBase, msfBase, count⟩
  obtain ⟨h16, hmsf, hids, hfit⟩ := h
  exact ⟨h16, hfit, (liftHRemProg_word_spec h16 hmem hmsf hids hfit).1⟩

/-- Framed specification for `liftHRemProg`: allocates `4 * H_msf.length` dirty words at
`s.frontier` and gathers `H_rem[e.id]` for each `e ∈ H_msf`, leaving all cells below `s.frontier`
untouched (`Modifies ∅`), in at most `9 * H_msf.length + 1` memory operations. -/
theorem liftHRemProg_spec {w n nA hRemBase msfBase : ℕ}
    {H_rem : List (IndexedEdge n)} {H_msf : List (IndexedEdge nA)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hrem : HoldsIndexedEdges hRemBase H_rem s.mem)
    (hrem_lt : hRemBase + 4 * H_rem.length ≤ s.frontier)
    (hmsf : HoldsIndexedEdges msfBase H_msf s.mem)
    (hmsf_lt : msfBase + 4 * H_msf.length ≤ s.frontier)
    (hids : ∀ e ∈ H_msf, e.id < H_rem.length)
    (hfit : Fits w (s.frontier + 4 * H_msf.length)) :
    Memory.FramedTriple w s (liftHRemProg (hRemBase, msfBase, H_msf.length))
      (9 * H_msf.length + 1) ∅ fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * H_msf.length ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase
          (H_msf.pmap (fun e he => H_rem[e.id]'(hids e he)) (fun _ he => he)) s'.mem := by
  have hids_lt : ∀ k < H_msf.length,
      hRemBase + 4 * s.mem (msfBase + 4 * k + 3) + 4 ≤ s.frontier := fun k hk => by
    have hid_eq := (hmsf k hk).2.2.2
    have hlt := hids H_msf[k] (List.getElem_mem hk)
    omega
  refine (liftHRemProg_word_spec h16 hwf hmsf_lt hids_lt hfit).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun i hi => ?_⟩
  have hi_len : i < H_msf.length := by simpa using hi
  have hid_eq := (hmsf i hi_len).2.2.2
  have hlt := hids H_msf[i] (List.getElem_mem hi_len)
  obtain ⟨hu, hv, hw, hid⟩ := hrem H_msf[i].id hlt
  obtain ⟨h0, h1, h2, h3⟩ := hvals i hi_len
  simp only [List.getElem_pmap]
  rw [hid_eq] at h0 h1 h2 h3
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3.trans hid⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
