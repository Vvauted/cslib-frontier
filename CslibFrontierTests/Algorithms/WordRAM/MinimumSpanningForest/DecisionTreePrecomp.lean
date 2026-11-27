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
`precomputeDTProg_spec`, and `realizes_precomputeDTProg` on concrete `r0 = 1` and non-empty
`r0 = 2` witnesses (via `holdsDTTable_for_le`, `DTTableInBounds`, and a `module`-encapsulated
`realize [realizes_precomputeDTProg]` client).
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

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.DecisionTreePrecomp
