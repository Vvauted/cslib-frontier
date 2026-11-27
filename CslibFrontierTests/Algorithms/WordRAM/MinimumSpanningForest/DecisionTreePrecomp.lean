/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for DecisionTree.PrecompSearch)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompSearch
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Tests for Word-RAM Optimal Decision-Tree Search and Precomputation

Exercises `precomputeDTProg`, `precomputeDTProgSafe`, `precomputeDTProgSafe_iff`,
`precomputeDTProg_spec`, and `realizes_precomputeDTProg` on concrete `r0 = 1`, `r0 = 2`, and
non-trivial `r0 = 3` triangle (`mask = 7`, `dtTestSkelProg` + `dtWriteFoundEntry`) witnesses
(via `holdsDTTable_for_le`, `DTTableInBounds`, `HoldsCompleteTree`, and a
`module`-encapsulated `realize [realizes_precomputeDTProg]` client).
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreePrecomp

open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.DataStructure
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

-- Concrete `r0 = 1, w = 8` witness exercising `precomputeDTProg_spec`, frame preservation,
-- `DTTableInBounds`, and `holdsDTTable_for_le` on the trivial `0`-edge graph.
example :
    let s0 : Memory.State := ⟨fun a => if a = 3 then 42 else 0, 10⟩
    Memory.FramedTriple 8 s0 (precomputeDTProg 1) 64 ∅ fun res s' =>
      Memory.WellFormed 8 s' ∧ s'.frontier ≤ 74 ∧ s'.mem 3 = 42 ∧
      HoldsDTTable 1 res s'.mem ∧ DTTableInBounds 1 res s'.frontier s'.mem := by
  intro s0
  have hwf0 : Memory.WellFormed 8 s0 :=
    ⟨by decide, fun a => by dsimp only [s0]; split_ifs <;> decide⟩
  have hcost : dtPrecompCost 1 = 64 := by
    simp only [dtPrecompCost, Nat.le_refl, ↓reduceIte]
  have hsafe0 : precomputeDTProgSafe 8 1 s0 := by
    rw [precomputeDTProgSafe_iff, hcost]; exact (by decide : Fits 8 (10 + 64))
  obtain ⟨hval, hc, hmod, hwf', hfr', htab, hbnd⟩ :=
    framedTriple_iff_realization.mp (precomputeDTProg_spec hwf0 hsafe0)
  rw [hcost] at hc hfr'
  have hmem3 := hmod.mem_eq_of_not_mem (a := 3) (by decide) (Set.notMem_empty 3)
  have hcheck := holdsDTTable_for_le htab le_rfl (by decide : 0 < 2 ^ Nat.choose 1 2)
  have _ := hcheck.1
  exact framedTriple_iff_realization.mpr
    ⟨hval, hc, hmod, hwf', hfr', by simpa [s0] using hmem3, htab, hbnd⟩

private theorem dtPrecompCost_of_two_le {r0 : ℕ} (hr : 2 ≤ r0) :
    dtPrecompCost r0 = 2 ^ (2 ^ (4 * r0 ^ 4 + 16)) := by
  have hnot1 : ¬(r0 ≤ 1) := by omega
  dsimp only [dtPrecompCost]; simp only [hnot1, ↓reduceIte]

private theorem add_lt_pow_succ {s k w : ℕ} (hs : s < 2 ^ k) (hw : w = k + 1) :
    s + 2 ^ k < 2 ^ w := by
  rw [hw, Nat.pow_succ', two_mul]; exact Nat.add_lt_add_right hs _

private theorem add_cost_lt_two_pow_succ {r0 s w : ℕ} (hr : 2 ≤ r0) (hs : s < 64)
    (hw : w = 2 ^ (4 * r0 ^ 4 + 16) + 1) : s + dtPrecompCost r0 < 2 ^ w := by
  have hge : 64 ≤ 2 ^ (2 ^ (4 * r0 ^ 4 + 16)) := by
    rw [← dtPrecompCost_of_two_le hr]; exact dtPrecompCost_ge_64 r0
  rw [dtPrecompCost_of_two_le hr]
  exact add_lt_pow_succ (hs.trans_le hge) hw

-- Concrete non-empty `r0 = 2, w = 2 ^ 80 + 1` witness exercising `precomputeDTProg_spec`,
-- frame preservation, `DTTableInBounds`, and `holdsDTTable_for_le` at both the non-empty 1-edge
-- graph `mask = 1` (`Fin 2`) and the smaller `v = 1` sub-table (`mask = 0`).
example :
    let w := 2 ^ 80 + 1
    let s0 : Memory.State := ⟨fun a => if a = 0 then 99 else 0, 4⟩
    precomputeDTProgSafe w 2 s0 ∧
    (Memory.FramedTriple w s0 (precomputeDTProg 2) (dtPrecompCost 2) ∅ fun res s' =>
        Memory.WellFormed w s' ∧ s'.frontier ≤ 4 + dtPrecompCost 2 ∧ s'.mem 0 = 99 ∧
        HoldsDTTable 2 res s'.mem ∧ DTTableInBounds 2 res s'.frontier s'.mem) ∧
      let res := (Memory.spec 0).clientResult s0 (precomputeDTProg 2)
      let s' := (Memory.spec 0).clientState s0 (precomputeDTProg 2)
      let entryPtr := s'.mem (res + 1)
      let e := (maskEdgePairs 2 1).length
      e = 1 ∧ s'.mem entryPtr = 1 ∧ s'.mem (entryPtr + 1) = optDepth (endsOfMask 2 1) ∧
      s'.mem (entryPtr + 2) = pairIdx 0 1 ∧
      (∃ T : MSFDT 1, T.IsComplete (s'.mem (entryPtr + 1)) ∧ T.Correct (endsOfMask 2 1)) := by
  intro w s0
  have h128_w : 2 ^ 7 < 2 ^ w :=
    Nat.pow_lt_pow_right (by decide) ((by decide : 7 < 2 ^ 6 + 1).trans
      (Nat.add_lt_add_right (Nat.pow_lt_pow_right (by decide) (by decide)) 1))
  have h4 : Fits w 4 := (by decide : 4 < 2 ^ 7).trans h128_w
  have h99 : Fits w 99 := (by decide : 99 < 2 ^ 7).trans h128_w
  have h0 : Fits w 0 := (by decide : 0 < 2 ^ 7).trans h128_w
  have hwf0 : Memory.WellFormed w s0 := ⟨h4, fun a => by dsimp only [s0]; split_ifs <;> assumption⟩
  have hsafe0 : precomputeDTProgSafe w 2 s0 := by
    rw [precomputeDTProgSafe_iff]
    exact add_cost_lt_two_pow_succ le_rfl (by decide : 4 < 64) (by decide)
  have hspec := precomputeDTProg_spec hwf0 hsafe0
  obtain ⟨hval, hc, hmod, hwf', hfr', htab, hbnd⟩ := framedTriple_iff_realization.mp hspec
  have hmem0 := hmod.mem_eq_of_not_mem (a := 0) (by decide) (Set.notMem_empty 0)
  have hle_v1 := holdsDTTable_for_le htab (by decide : 1 ≤ 2) (by decide : 0 < 2 ^ Nat.choose 1 2)
  have _ := hle_v1.1
  have h1 := holdsDTTable_for_le htab le_rfl (by decide : 1 < 2 ^ Nat.choose 2 2)
  have hlen1 : (maskEdgePairs 2 1).length = 1 := by decide
  obtain ⟨_, he_mem, hd_mem, _, hpairs_mem, T, hcomp, hcorr, _⟩ := h1
  refine ⟨hsafe0, framedTriple_iff_realization.mpr
    ⟨hval, hc, hmod, hwf', hfr', hmem0.trans (by simp only [s0, ↓reduceIte]), htab, hbnd⟩,
    hlen1, ?_, hd_mem, ?_, ⟨T, hcomp, hcorr⟩⟩
  · simpa only [hlen1] using he_mem
  · have hp0 := hpairs_mem 0 (by decide)
    have hpair0 :
        (maskEdgePairs 2 1)[0]'(by decide : 0 < (maskEdgePairs 2 1).length) =
          (⟨0, by decide⟩, ⟨1, by decide⟩) := by decide
    simpa only [hpair0] using hp0

-- Module-encapsulated client composing `precomputeDTProg` via
-- `realize [realizes_precomputeDTProg]`.
private def precomputeLookupClient (p : ℕ × ℕ) : Memory.Prog ℕ := do
  let tbl ← precomputeDTProg p.1
  Memory.read (tbl + p.2)

private def precomputeLookupClientSafe (w : ℕ) (p : ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w 2 ∧ precomputeDTProgSafe w p.1 s ∧ p.2 < 2 ^ p.1.choose 2

private theorem realizes_precomputeLookupClient : Realizes .exact
    precomputeLookupClient (appendWords wordWords wordWords) WordEncoding.encode
    precomputeLookupClientSafe (fun _ _ => 0) := by
  unfold precomputeLookupClient
  realize [realizes_precomputeDTProg]
  all_goals
    obtain ⟨h2, hsafe, hmask⟩ := h
    have hfit := (precomputeDTProgSafe_iff _ _ _).mp hsafe
    obtain ⟨_, _, _, _, hfr_le, _, hbd⟩ :=
      framedTriple_iff_realization.mp (precomputeDTProg_spec hmem hsafe)
    have htb := ((dtTableInBounds_iff _ _ _ _).mp hbd).1
    first | exact hsafe | omega | fits

private theorem fin3_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  rcases x with ⟨_ | _ | _ | k, hk⟩
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)
  · omega

private theorem k3Len : (maskEdgePairs 3 7).length = 3 := by decide

private def k3Cast : Fin (maskEdgePairs 3 7).length ≃ Fin 3 :=
  (Fin.castOrderIso k3Len).toEquiv

private theorem not_joins_of_inv {E V : Type*} (ends : E → Sym2 V) (S : Set E) (P : V → Prop)
    (hS : ∀ e ∈ S, ∀ a b, ends e = s(a, b) → (P a ↔ P b)) {u v : V} (hu : P u) (hv : ¬ P v) :
    ¬ Cslib.Multigraph.Joins ends S u v := fun hj => by
  obtain ⟨e, heS, hcut⟩ := hj.exists_mem_edgeCut (P := {x | P x}) hu hv
  obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.1 hcut
  exact hb ((hS e heS a b hab).mp ha)

private theorem k3_mem_msf (p : Equiv.Perm (Fin (maskEdgePairs 3 7).length))
    {x y k : Fin 3} (hxy : x ≠ y) (hxk : x ≠ k) (hyk : y ≠ k)
    (hlt : p (k3Cast.symm x) < p (k3Cast.symm k)) :
    k3Cast.symm x ∈ Cslib.Multigraph.msf (endsOfMask 3 7) p Finset.univ := by
  have he0 : endsOfMask 3 7 (k3Cast.symm 0) = s(0, 1) := by decide
  have he1 : endsOfMask 3 7 (k3Cast.symm 1) = s(0, 2) := by decide
  have he2 : endsOfMask 3 7 (k3Cast.symm 2) = s(1, 2) := by decide
  let S : Set (Fin (maskEdgePairs 3 7).length) :=
    {f | f ∈ Finset.univ ∧ p f < p (k3Cast.symm x)}
  have hS_eq : ∀ f ∈ S, f = k3Cast.symm y := fun f hf => by
    have hlt_f : p f < p (k3Cast.symm x) := hf.2
    have hfx : f ≠ k3Cast.symm x := fun h => by rw [h] at hlt_f; exact lt_irrefl _ hlt_f
    have hfk : f ≠ k3Cast.symm k := fun h => by
      rw [h] at hlt_f; exact absurd (lt_trans hlt hlt_f) (lt_irrefl _)
    have hcf : k3Cast f ≠ x := fun h =>
      hfx (k3Cast.injective (h.trans (k3Cast.apply_symm_apply _).symm))
    have hck : k3Cast f ≠ k := fun h =>
      hfk (k3Cast.injective (h.trans (k3Cast.apply_symm_apply _).symm))
    rcases fin3_cases (k3Cast f) with h0 | h1 | h2 <;>
      rcases fin3_cases x with rfl | rfl | rfl <;>
      rcases fin3_cases y with rfl | rfl | rfl <;>
      rcases fin3_cases k with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hxy | exact absurd rfl hxk | exact absurd rfl hyk
        | exact absurd h0 hcf | exact absurd h0 hck
        | exact absurd h1 hcf | exact absurd h1 hck
        | exact absurd h2 hcf | exact absurd h2 hck
        | exact k3Cast.injective (h0.trans (k3Cast.apply_symm_apply _).symm)
        | exact k3Cast.injective (h1.trans (k3Cast.apply_symm_apply _).symm)
        | exact k3Cast.injective (h2.trans (k3Cast.apply_symm_apply _).symm)
  have hstep {c d u v : Fin 3} (P : Fin 3 → Prop)
      (hey : endsOfMask 3 7 (k3Cast.symm y) = s(c, d))
      (hP : ∀ a b, s(a, b) = s(c, d) → (P a ↔ P b))
      (hu : P u) (hv : ¬ P v) : ¬ Cslib.Multigraph.Joins (endsOfMask 3 7) S u v :=
    not_joins_of_inv (endsOfMask 3 7) S P (fun f hf a b hab => by
      rw [hS_eq f hf, hey] at hab; exact hP a b hab.symm) hu hv
  rcases fin3_cases x with rfl | rfl | rfl <;> rcases fin3_cases y with rfl | rfl | rfl
  · exact absurd rfl hxy
  · rw [Cslib.Multigraph.mem_msf_iff p he0]
    exact ⟨Finset.mem_univ _, fun h => hstep (· = 1) he1 (fun a b hab => by
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
      (by decide) (by decide) h.symm⟩
  · rw [Cslib.Multigraph.mem_msf_iff p he0]
    exact ⟨Finset.mem_univ _, hstep (· = 0) he2 (fun a b hab => by
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) rfl (by decide)⟩
  · rw [Cslib.Multigraph.mem_msf_iff p he1]
    exact ⟨Finset.mem_univ _, fun h => hstep (· = 2) he0 (fun a b hab => by
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
      (by decide) (by decide) h.symm⟩
  · exact absurd rfl hxy
  · rw [Cslib.Multigraph.mem_msf_iff p he1]
    exact ⟨Finset.mem_univ _, hstep (· = 0) he2 (fun a b hab => by
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) rfl (by decide)⟩
  · rw [Cslib.Multigraph.mem_msf_iff p he2]
    exact ⟨Finset.mem_univ _, fun h => hstep (· = 2) he0 (fun a b hab => by
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
      (by decide) (by decide) h.symm⟩
  · rw [Cslib.Multigraph.mem_msf_iff p he2]
    exact ⟨Finset.mem_univ _, hstep (· = 1) he1 (fun a b hab => by
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide) rfl (by decide)⟩
  · exact absurd rfl hxy

private theorem k3_msf_of_order (p : Equiv.Perm (Fin (maskEdgePairs 3 7).length))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : p (k3Cast.symm i) < p (k3Cast.symm k))
    (hj : p (k3Cast.symm j) < p (k3Cast.symm k)) :
    Cslib.Multigraph.msf (endsOfMask 3 7) p Finset.univ =
      ({k3Cast.symm i, k3Cast.symm j} : Finset (Fin (maskEdgePairs 3 7).length)) := by
  have he0 : endsOfMask 3 7 (k3Cast.symm 0) = s(0, 1) := by decide
  have he1 : endsOfMask 3 7 (k3Cast.symm 1) = s(0, 2) := by decide
  have he2 : endsOfMask 3 7 (k3Cast.symm 2) = s(1, 2) := by decide
  have hk_not : k3Cast.symm k ∉ Cslib.Multigraph.msf (endsOfMask 3 7) p Finset.univ := by
    let S : Set (Fin (maskEdgePairs 3 7).length) :=
      {f | f ∈ Finset.univ ∧ p f < p (k3Cast.symm k)}
    have hiS : k3Cast.symm i ∈ S := ⟨Finset.mem_univ _, hi⟩
    have hjS : k3Cast.symm j ∈ S := ⟨Finset.mem_univ _, hj⟩
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      rcases fin3_cases k with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hij | exact absurd rfl hik | exact absurd rfl hjk
        | (rw [Cslib.Multigraph.mem_msf_iff p he2]; exact fun h => h.2
            ((Cslib.Multigraph.Joins.of_mem hiS he0).symm.trans
              (Cslib.Multigraph.Joins.of_mem hjS he1)))
        | (rw [Cslib.Multigraph.mem_msf_iff p he2]; exact fun h => h.2
            ((Cslib.Multigraph.Joins.of_mem hjS he0).symm.trans
              (Cslib.Multigraph.Joins.of_mem hiS he1)))
        | (rw [Cslib.Multigraph.mem_msf_iff p he1]; exact fun h => h.2
            ((Cslib.Multigraph.Joins.of_mem hiS he0).trans
              (Cslib.Multigraph.Joins.of_mem hjS he2)))
        | (rw [Cslib.Multigraph.mem_msf_iff p he1]; exact fun h => h.2
            ((Cslib.Multigraph.Joins.of_mem hjS he0).trans
              (Cslib.Multigraph.Joins.of_mem hiS he2)))
        | (rw [Cslib.Multigraph.mem_msf_iff p he0]; exact fun h => h.2
            ((Cslib.Multigraph.Joins.of_mem hiS he1).trans
              (Cslib.Multigraph.Joins.of_mem hjS he2).symm))
        | (rw [Cslib.Multigraph.mem_msf_iff p he0]; exact fun h => h.2
            ((Cslib.Multigraph.Joins.of_mem hjS he1).trans
              (Cslib.Multigraph.Joins.of_mem hiS he2).symm))
  ext f
  rw [Finset.mem_insert, Finset.mem_singleton]
  have hf_case : f = k3Cast.symm i ∨ f = k3Cast.symm j ∨ f = k3Cast.symm k := by
    have hci : k3Cast f = i ∨ k3Cast f = j ∨ k3Cast f = k := by
      have hi1 := (k3Cast f).isLt; have hfi := Fin.val_ne_of_ne hij
      have hfj := Fin.val_ne_of_ne hik; have hfk := Fin.val_ne_of_ne hjk
      have : (k3Cast f).val = i.val ∨ (k3Cast f).val = j.val ∨ (k3Cast f).val = k.val := by
        have := i.isLt; have := j.isLt; have := k.isLt; omega
      rcases this with h | h | h
      · exact .inl (Fin.ext h)
      · exact .inr (.inl (Fin.ext h))
      · exact .inr (.inr (Fin.ext h))
    rcases hci with h | h | h
    · exact .inl (k3Cast.injective (h.trans (k3Cast.apply_symm_apply i).symm))
    · exact .inr (.inl (k3Cast.injective (h.trans (k3Cast.apply_symm_apply j).symm)))
    · exact .inr (.inr (k3Cast.injective (h.trans (k3Cast.apply_symm_apply k).symm)))
  rcases hf_case with rfl | rfl | rfl
  · exact iff_of_true (k3_mem_msf p hij hik hjk hi) (.inl rfl)
  · exact iff_of_true (k3_mem_msf p hij.symm hjk hik hj) (.inr rfl)
  · refine iff_of_false hk_not ?_
    rintro (h | h)
    · exact hik (k3Cast.symm.injective h).symm
    · exact hjk (k3Cast.symm.injective h).symm

-- Non-trivial `r0 = 3, w = 2 ^ (4 * 3 ^ 4 + 16) + 1` (= `2 ^ 340 + 1`) witness exercising
-- `precomputeDTProg_spec` and `holdsDTTable_for_le` on the triangle `mask = 7` (`e = 3` search
-- branch: `dtTestSkelProg` + `dtWriteFoundEntry`), verifying positive stored depth (`0 < d`,
-- `2 ≤ d`), `HoldsCompleteTree`, and distinct 2-edge `T.eval` MSF leaves on two permutations.
example (w : ℕ) (hw : w = 2 ^ (4 * 3 ^ 4 + 16) + 1) :
    let s0 : Memory.State := ⟨fun a => if a = 1 then 77 else 0, 5⟩
    precomputeDTProgSafe w 3 s0 ∧
    (Memory.FramedTriple w s0 (precomputeDTProg 3) (dtPrecompCost 3) ∅ fun res s' =>
        Memory.WellFormed w s' ∧ s'.frontier ≤ 5 + dtPrecompCost 3 ∧ s'.mem 1 = 77 ∧
        HoldsDTTable 3 res s'.mem ∧ DTTableInBounds 3 res s'.frontier s'.mem) ∧
      let res := (Memory.spec 0).clientResult s0 (precomputeDTProg 3)
      let s' := (Memory.spec 0).clientState s0 (precomputeDTProg 3)
      let entryPtr := s'.mem (res + 7)
      let pairs := maskEdgePairs 3 7
      let e := pairs.length
      let d := s'.mem (entryPtr + 1)
      let intBase := entryPtr + 2 + e
      let leafBase := intBase + 2 * (2 ^ d - 1)
      let p1 : Equiv.Perm (Fin e) := Equiv.refl _
      let p2 : Equiv.Perm (Fin e) := k3Cast.symm.trans ((Equiv.swap (0 : Fin 3) 2).trans k3Cast)
      e = 3 ∧ s'.mem entryPtr = 3 ∧ d = optDepth (endsOfMask 3 7) ∧ 0 < d ∧ 2 ≤ d ∧
      ∃ T : MSFDT e,
        T.IsComplete d ∧
        T.Correct (endsOfMask 3 7) ∧
        HoldsCompleteTree d intBase leafBase d 1 s'.mem T ∧
        (T.eval p1).map k3Cast.toEmbedding = ({0, 1} : Finset (Fin 3)) ∧
        (T.eval p2).map k3Cast.toEmbedding = ({1, 2} : Finset (Fin 3)) ∧
        maskOfFinset (T.eval p1) = 3 ∧
        maskOfFinset (T.eval p2) = 6 ∧
        maskOfFinset (T.eval p1) ≠ maskOfFinset (T.eval p2) := by
  intro s0
  have h128_w : 2 ^ 7 < 2 ^ w :=
    Nat.pow_lt_pow_right (by decide) (hw ▸ ((by decide : 7 < 2 ^ 6 + 1).trans
      (Nat.add_lt_add_right (Nat.pow_lt_pow_right (by decide)
        (by decide : 6 < 4 * 3 ^ 4 + 16)) 1)))
  have hwf0 : Memory.WellFormed w s0 := ⟨(by decide : 5 < 2 ^ 7).trans h128_w, fun a => by
    dsimp only [s0]; split_ifs <;> [exact (by decide : 77 < 2 ^ 7).trans h128_w;
      exact (by decide : 0 < 2 ^ 7).trans h128_w]⟩
  have hsafe0 : precomputeDTProgSafe w 3 s0 := by
    rw [precomputeDTProgSafe_iff]
    exact add_cost_lt_two_pow_succ (by decide) (by decide : 5 < 64) hw
  have hspec := precomputeDTProg_spec hwf0 hsafe0
  obtain ⟨hval, hc, hmod, hwf', hfr', htab, hbnd⟩ := framedTriple_iff_realization.mp hspec
  have hmem1 := hmod.mem_eq_of_not_mem (a := 1) (by decide) (Set.notMem_empty 1)
  have h7 := holdsDTTable_for_le htab le_rfl (by decide : 7 < 2 ^ Nat.choose 3 2)
  obtain ⟨_, he_mem, hd_mem, _, _, T, hcomp, hcorr, hhold⟩ := h7
  have hcorr' := (MSFDT.correct_iff _ _).mp hcorr
  let p1 : Equiv.Perm (Fin (maskEdgePairs 3 7).length) := Equiv.refl _
  let p2 : Equiv.Perm (Fin (maskEdgePairs 3 7).length) :=
    k3Cast.symm.trans ((Equiv.swap (0 : Fin 3) 2).trans k3Cast)
  let p3 : Equiv.Perm (Fin (maskEdgePairs 3 7).length) :=
    k3Cast.symm.trans ((Equiv.swap (1 : Fin 3) 2).trans k3Cast)
  have hp1 : T.eval p1 = {k3Cast.symm 0, k3Cast.symm 1} :=
    (hcorr' p1).trans (k3_msf_of_order p1 (k := 2) (by decide) (by decide) (by decide)
      (by decide) (by decide))
  have hp2 : T.eval p2 = {k3Cast.symm 1, k3Cast.symm 2} :=
    (hcorr' p2).trans (k3_msf_of_order p2 (k := 0) (by decide) (by decide) (by decide)
      (by dsimp only [p2]; decide) (by dsimp only [p2]; decide))
  have hp3 : T.eval p3 = {k3Cast.symm 0, k3Cast.symm 2} :=
    (hcorr' p3).trans (k3_msf_of_order p3 (k := 1) (by decide) (by decide) (by decide)
      (by dsimp only [p3]; decide) (by dsimp only [p3]; decide))
  rw [hd_mem] at hcomp
  have hd_opt_ge2 : 2 ≤ optDepth (endsOfMask 3 7) := by
    by_contra hlt2
    rcases (by omega :
        optDepth (endsOfMask 3 7) = 0 ∨ optDepth (endsOfMask 3 7) = 1) with hd0 | hd1
    · rw [hd0] at hcomp
      cases T with
      | node _ _ _ _ => exact absurd hcomp MSFTree.isComplete_zero_node
      | leaf ans =>
        have h12 : ({k3Cast.symm 0, k3Cast.symm 1} :
            Finset (Fin (maskEdgePairs 3 7).length)) = {k3Cast.symm 1, k3Cast.symm 2} := by
          rw [← hp1, ← hp2]; rfl
        have hmem0 : k3Cast.symm 0 ∈ ({k3Cast.symm 1, k3Cast.symm 2} :
            Finset (Fin (maskEdgePairs 3 7).length)) := h12 ▸ Finset.mem_insert_self _ _
        exact absurd hmem0 (by decide)
    · rw [hd1] at hcomp
      cases T with
      | leaf _ => exact absurd hcomp MSFTree.isComplete_succ_leaf
      | node i j l r =>
        obtain ⟨_, hl, hr⟩ := MSFTree.isComplete_node.mp hcomp
        cases l with
        | node _ _ _ _ => exact absurd hl MSFTree.isComplete_zero_node
        | leaf a =>
          cases r with
          | node _ _ _ _ => exact absurd hr MSFTree.isComplete_zero_node
          | leaf b =>
            have hval_or (q : Equiv.Perm (Fin (maskEdgePairs 3 7).length)) :
                (MSFTree.node i j (.leaf a) (.leaf b)).eval q = a ∨
                  (MSFTree.node i j (.leaf a) (.leaf b)).eval q = b := by
              dsimp only [MSFTree.eval]; split_ifs <;> [exact .inl rfl; exact .inr rfl]
            rcases hval_or p1 with h1 | h1 <;> rcases hval_or p2 with h2 | h2 <;>
              rcases hval_or p3 with h3 | h3
            all_goals
              first
                | (have heq := (hp1.symm.trans h1).trans (h2.symm.trans hp2)
                   exact absurd (heq ▸ Finset.mem_insert_self (k3Cast.symm 0) _) (by decide))
                | (have heq := (hp1.symm.trans h1).trans (h3.symm.trans hp3)
                   exact absurd (heq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self
                     (k3Cast.symm 1))) (by decide))
                | (have heq := (hp2.symm.trans h2).trans (h3.symm.trans hp3)
                   exact absurd (heq ▸ Finset.mem_insert_self (k3Cast.symm 1) _) (by decide))
  have hd_ge2 := hd_mem ▸ hd_opt_ge2
  rw [← hd_mem] at hcomp
  have hmask1 : maskOfFinset (T.eval p1) = 3 := by
    rw [hp1, maskOfFinset, Finset.sum_pair (by decide)]; rfl
  have hmask2 : maskOfFinset (T.eval p2) = 6 := by
    rw [hp2, maskOfFinset, Finset.sum_pair (by decide)]; rfl
  refine ⟨hsafe0, framedTriple_iff_realization.mpr
    ⟨hval, hc, hmod, hwf', hfr', hmem1.trans (by simp only [s0, ↓reduceIte]), htab, hbnd⟩,
    k3Len, he_mem.trans k3Len, hd_mem, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd_ge2, hd_ge2,
    T, hcomp, hcorr, hhold, ?_, ?_, hmask1, hmask2, by rw [hmask1, hmask2]; decide⟩
  · rw [hp1]; simp [Finset.map_insert, Finset.map_singleton]
  · rw [hp2]; simp [Finset.map_insert, Finset.map_singleton]

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreePrecomp
