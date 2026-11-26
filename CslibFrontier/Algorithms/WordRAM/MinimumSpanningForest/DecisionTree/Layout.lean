/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical
-- `import all` exposes the unexposed `MSFTree.IsComplete` cases across the module boundary.
import all CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Decision-Tree Memory Layout, Threshold Bounds, and Canonical Bridges

Defines the lookup-table memory layout (`HoldsCompleteTree`, `HoldsDTTable`, `DTTableInBounds`),
pure decision-tree evaluation (`walkCompleteTree`) and skeleton decoding (`skelToTree`), the
vertex threshold `dtThreshold` (`O(log log log n₀)`) with its `dtPrecompCost` bound, and canonical
bitmask reindexing (`dtGraphMask`) over `#8768`'s `Cslib.Query.MinimumSpanningForest` primitives.

## Main definitions

* `log3Nat`, `dtPrecompCost`, `dtThreshold`: triple-log vertex threshold and exponential table
  precomputation budget.
* `HoldsCompleteTree`, `HoldsDTTable`, `DTTableInBounds`: Word-RAM memory predicates for
  optimal MSF decision trees indexed by canonical simple-graph bitmasks.
* `walkCompleteTree`, `skelToTree`: pure complete-tree walk and base-`choose e 2` skeleton
  decoder, together with `walkSkelNode` and `exists_skelCode_of_complete_correct`.
* `edgePairIdx`, `dtGraphMask`: canonical bitmask encoding of unordered edge-pair lists.

## References

* [Pettie and Ramachandran, *An Optimal Minimum Spanning Tree Algorithm*,
  Journal of the ACM 49(1), 2002][PettieRamachandran2002]
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Decision-Tree Threshold and Precomputation Cost Bounds -/

/-- Triple iterated binary logarithm `⌊log₂ ⌊log₂ ⌊log₂ n⌋⌋⌋`. -/
@[expose] def log3Nat (n : ℕ) : ℕ :=
  Nat.log 2 (Nat.log 2 (Nat.log 2 n))

/-- Closed-form upper bound on the memory cost and space usage of `precomputeDTProg r0`. -/
@[expose] def dtPrecompCost (r0 : ℕ) : ℕ :=
  if r0 ≤ 1 then 64 else 2 ^ (2 ^ (4 * r0 ^ 4 + 16))

/-- Every precomputation cost bound is at least `64`. -/
theorem dtPrecompCost_ge_64 (r0 : ℕ) : 64 ≤ dtPrecompCost r0 := by
  dsimp only [dtPrecompCost]
  split_ifs with h
  · exact le_rfl
  · have h1 : 6 ≤ 2 ^ (4 * r0 ^ 4 + 16) :=
      (by decide : 6 ≤ 2 ^ 16).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by decide : 64 ≤ 2 ^ 6).trans (Nat.pow_le_pow_right (by decide) h1)

/-- Decision-tree vertex threshold `r0 ∈ [1, max 1 (log3Nat n₀)]` maximizing `r0`
subject to `dtPrecompCost r0 ≤ n₀`, falling back to `1` for small `n₀`. -/
@[expose] def dtThreshold (n₀ : ℕ) : ℕ :=
  ((List.range (max 1 (log3Nat n₀) + 1)).filter fun r =>
    decide (1 ≤ r ∧ dtPrecompCost r ≤ n₀)).foldl max 1

private theorem foldl_max_spec (xs : List ℕ) (init : ℕ) :
    init ≤ xs.foldl max init ∧
    (∀ x ∈ xs, x ≤ xs.foldl max init) ∧
    (∀ (P : ℕ → Prop), P init → (∀ x ∈ xs, P x) → P (xs.foldl max init)) := by
  induction xs generalizing init with
  | nil => exact ⟨le_rfl, fun _ hx => by simp at hx, fun _ hi _ => hi⟩
  | cons y rest ih =>
    obtain ⟨hinit, hmem, hprop⟩ := ih (max init y)
    refine ⟨(le_max_left init y).trans hinit, fun x hx => ?_, fun P hi hxs => ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hrest
      · exact (le_max_right init x).trans hinit
      · exact hmem x hrest
    · refine hprop P ?_ (fun z hz => hxs z (List.mem_cons_of_mem y hz))
      rcases le_total init y with h | h
      · rw [max_eq_right h]; exact hxs y List.mem_cons_self
      · rw [max_eq_left h]; exact hi

/-- `dtThreshold n₀` is always at least `1`. -/
theorem dtThreshold_ge_one (n₀ : ℕ) : 1 ≤ dtThreshold n₀ :=
  (foldl_max_spec _ 1).1

/-- `dtThreshold n₀` never exceeds `max 1 (log3Nat n₀)`. -/
theorem dtThreshold_le_max_one_log3 (n₀ : ℕ) :
    dtThreshold n₀ ≤ max 1 (log3Nat n₀) := by
  refine (foldl_max_spec _ 1).2.2 (· ≤ max 1 (log3Nat n₀)) (le_max_left 1 (log3Nat n₀)) ?_
  intro r hr
  rw [List.mem_filter, List.mem_range] at hr
  omega

/-- For `n₀ ≥ 64`, `dtPrecompCost (dtThreshold n₀) ≤ n₀`. -/
theorem dtPrecompCost_dtThreshold_le {n₀ : ℕ} (h : 64 ≤ n₀) :
    dtPrecompCost (dtThreshold n₀) ≤ n₀ := by
  refine (foldl_max_spec _ 1).2.2 (fun r => dtPrecompCost r ≤ n₀) ?_ fun r hr => ?_
  · simp [dtPrecompCost, h]
  · rw [List.mem_filter, decide_eq_true_eq] at hr
    exact hr.2.2

/-- Unconditional precomputation cost bound `dtPrecompCost (dtThreshold n₀) ≤ n₀ + 64`. -/
theorem dtPrecompCost_dtThreshold_le_add (n₀ : ℕ) :
    dtPrecompCost (dtThreshold n₀) ≤ n₀ + 64 := by
  by_cases h : 64 ≤ n₀
  · exact (dtPrecompCost_dtThreshold_le h).trans (Nat.le_add_right n₀ 64)
  · have hempty : ((List.range (max 1 (log3Nat n₀) + 1)).filter fun r =>
        decide (1 ≤ r ∧ dtPrecompCost r ≤ n₀)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r _
      simp only [decide_eq_true_eq, not_and]
      intro _ hc
      have hge := dtPrecompCost_ge_64 r
      omega
    rw [dtThreshold, hempty, List.foldl_nil]
    simp [dtPrecompCost]

private theorem poly_le_two_pow_of_ge_24 {r : ℕ} (hr : 24 ≤ r) :
    4 * r ^ 4 + 16 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have hk4 : (k + 1) ^ 4 ≤ 2 * k ^ 4 := by
      have h1 : 24 * k ^ 3 ≤ k ^ 4 := by
        calc 24 * k ^ 3 ≤ k * k ^ 3 := Nat.mul_le_mul_right _ hk
          _ = k ^ 4 := by ring
      have h2 : 24 * k ^ 2 ≤ k ^ 3 := by
        calc 24 * k ^ 2 ≤ k * k ^ 2 := Nat.mul_le_mul_right _ hk
          _ = k ^ 3 := by ring
      have h3 : 24 * k ≤ k ^ 2 := by
        calc 24 * k ≤ k * k := Nat.mul_le_mul_right _ hk
          _ = k ^ 2 := by ring
      have hexp : (k + 1) ^ 4 = k ^ 4 + 4 * k ^ 3 + 6 * k ^ 2 + 4 * k + 1 := by ring
      omega
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega

/-- For all sufficiently large `n₀`, `dtThreshold n₀` equals `log3Nat n₀`. -/
theorem dtThreshold_eq_log3_of_large :
    ∃ R₀ : ℕ, ∀ n₀ : ℕ, R₀ ≤ log3Nat n₀ → dtThreshold n₀ = log3Nat n₀ := by
  refine ⟨24, fun n₀ hr => ?_⟩
  set r := log3Nat n₀
  have hL2_pos : 0 < Nat.log 2 (Nat.log 2 n₀) := by
    by_contra h0
    have hz : Nat.log 2 (Nat.log 2 n₀) = 0 := by omega
    have hr0 : r = 0 := by simp [r, log3Nat, hz]
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
  have hpoly : 4 * r ^ 4 + 16 ≤ 2 ^ r := poly_le_two_pow_of_ge_24 hr
  have hcost : dtPrecompCost r ≤ n₀ := by
    have hr_gt1 : ¬ (r ≤ 1) := by omega
    simp only [dtPrecompCost, hr_gt1, ↓reduceIte]
    exact (Nat.pow_le_pow_right (by decide)
      (Nat.pow_le_pow_right (by decide) hpoly)).trans hp3
  have hmax : max 1 r = r := max_eq_right (by omega)
  have hmem : r ∈ (List.range (max 1 r + 1)).filter fun k =>
      decide (1 ≤ k ∧ dtPrecompCost k ≤ n₀) := by
    rw [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by omega, by omega, hcost⟩
  exact le_antisymm (hmax ▸ dtThreshold_le_max_one_log3 n₀) ((foldl_max_spec _ 1).2.1 r hmem)

/-! ## Section 2: Table Layouts and Canonical Decision-Tree Bridges -/

/-- Memory `mem` holds complete binary tree `T` of uniform depth `dInit` at subtree `(d, node)`
(`1`-indexed internal nodes at `intBase + 2 * (node - 1)`, leaves at
`leafBase + (node - 2 ^ dInit)`). -/
def HoldsCompleteTree {e : ℕ} (dInit intBase leafBase : ℕ) :
    ℕ → ℕ → (ℕ → ℕ) → MSFDT e → Prop
  | 0, node, mem, .leaf ans =>
    2 ^ dInit ≤ node ∧ node < 2 ^ (dInit + 1) ∧
    mem (leafBase + (node - 2 ^ dInit)) = maskOfFinset ans
  | d + 1, node, mem, .node i j l r =>
    1 ≤ node ∧ i.val < j.val ∧
    mem (intBase + 2 * (node - 1)) = i.val ∧
    mem (intBase + 2 * (node - 1) + 1) = j.val ∧
    HoldsCompleteTree dInit intBase leafBase d (2 * node) mem l ∧
    HoldsCompleteTree dInit intBase leafBase d (2 * node + 1) mem r
  | _, _, _, _ => False

/-- Unfolding equation for `HoldsCompleteTree` at depth `0` on a leaf. -/
@[simp] theorem holdsCompleteTree_leaf {e dInit intBase leafBase node : ℕ}
    {mem : ℕ → ℕ} {ans : Finset (Fin e)} :
    HoldsCompleteTree dInit intBase leafBase 0 node mem (.leaf ans) ↔
      2 ^ dInit ≤ node ∧ node < 2 ^ (dInit + 1) ∧
      mem (leafBase + (node - 2 ^ dInit)) = maskOfFinset ans := Iff.rfl

/-- Unfolding equation for `HoldsCompleteTree` at depth `d + 1` on an internal node. -/
@[simp] theorem holdsCompleteTree_node {e dInit intBase leafBase d node : ℕ}
    {mem : ℕ → ℕ} {i j : Fin e} {l r : MSFDT e} :
    HoldsCompleteTree dInit intBase leafBase (d + 1) node mem (.node i j l r) ↔
      1 ≤ node ∧ i.val < j.val ∧
      mem (intBase + 2 * (node - 1)) = i.val ∧
      mem (intBase + 2 * (node - 1) + 1) = j.val ∧
      HoldsCompleteTree dInit intBase leafBase d (2 * node) mem l ∧
      HoldsCompleteTree dInit intBase leafBase d (2 * node + 1) mem r := Iff.rfl

/-- `HoldsCompleteTree` is false at depth `0` on an internal node. -/
@[simp] theorem holdsCompleteTree_zero_node {e dInit intBase leafBase node : ℕ}
    {mem : ℕ → ℕ} {i j : Fin e} {l r : MSFDT e} :
    ¬ HoldsCompleteTree dInit intBase leafBase 0 node mem (.node i j l r) := by
  simp [HoldsCompleteTree]

/-- `HoldsCompleteTree` is false at positive depth on a leaf. -/
@[simp] theorem holdsCompleteTree_succ_leaf {e dInit intBase leafBase d node : ℕ}
    {mem : ℕ → ℕ} {ans : Finset (Fin e)} :
    ¬ HoldsCompleteTree dInit intBase leafBase (d + 1) node mem (.leaf ans) := by
  simp [HoldsCompleteTree]

/-- Framing lemma for `HoldsCompleteTree`. -/
theorem HoldsCompleteTree.congr {e dInit intBase leafBase : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hint : ∀ a, intBase ≤ a → a < intBase + 2 * (2 ^ dInit - 1) → m₂ a = m₁ a)
    (hleaf : ∀ a, leafBase ≤ a → a < leafBase + 2 ^ dInit → m₂ a = m₁ a) :
    ∀ {d node : ℕ} {T : MSFDT e},
      d ≤ dInit → 1 ≤ node → node < 2 ^ (dInit - d + 1) →
      HoldsCompleteTree dInit intBase leafBase d node m₁ T →
      HoldsCompleteTree dInit intBase leafBase d node m₂ T := by
  intro d
  induction d with
  | zero =>
    intro node T _ _ _ h
    cases T with
    | node _ _ _ _ => exact absurd h holdsCompleteTree_zero_node
    | leaf ans =>
      obtain ⟨hlo, hhi, hmem⟩ := holdsCompleteTree_leaf.mp h
      have hpow : 2 ^ (dInit + 1) = 2 ^ dInit + 2 ^ dInit := by ring
      refine holdsCompleteTree_leaf.mpr ⟨hlo, hhi, ?_⟩
      rw [hleaf _ (by omega) (by omega), hmem]
  | succ d ih =>
    intro node T hd _ hnode h
    cases T with
    | leaf _ => exact absurd h holdsCompleteTree_succ_leaf
    | node i j l r =>
      obtain ⟨h1, hij, h0, h1m, hl, hr⟩ := holdsCompleteTree_node.mp h
      have hpow_le : 2 ^ (dInit - (d + 1) + 1) ≤ 2 ^ dInit :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hnode_lt : node < 2 ^ dInit := hnode.trans_le hpow_le
      have h2pow : 2 * 2 ^ (dInit - (d + 1) + 1) = 2 ^ (dInit - d + 1) := by
        rw [show dInit - d + 1 = (dInit - (d + 1) + 1) + 1 by omega, Nat.pow_succ']
        ring
      have h2node : 2 * node < 2 ^ (dInit - d + 1) := by linarith
      refine holdsCompleteTree_node.mpr ⟨h1, hij, ?_, ?_,
        ih (by omega) (by omega) h2node hl,
        ih (by omega) (by omega) (by omega) hr⟩
      · rw [hint _ (by omega) (by omega), h0]
      · rw [hint _ (by omega) (by omega), h1m]

/-- Memory `mem` holds a valid optimal-`MSFDT` lookup table at `tableBase` for all simple graphs
on at most `r0` vertices (`mask < 2 ^ r0.choose 2`). -/
def HoldsDTTable (r0 tableBase : ℕ) (mem : ℕ → ℕ) : Prop :=
  ∀ mask < 2 ^ r0.choose 2,
    let entryPtr := mem (tableBase + mask)
    let pairs := maskEdgePairs r0 mask
    let e := pairs.length
    let d := mem (entryPtr + 1)
    let intBase := entryPtr + 2 + e
    let leafBase := intBase + 2 * (2 ^ d - 1)
    mem entryPtr = e ∧
    d = optDepth (endsOfMask r0 mask) ∧
    (∀ j (hj : j < e),
      mem (entryPtr + 2 + j) = pairIdx (pairs[j]).1.val (pairs[j]).2.val) ∧
    ∃ T : MSFDT e,
      T.IsComplete d ∧
      T.Correct (endsOfMask r0 mask) ∧
      HoldsCompleteTree d intBase leafBase d 1 mem T

/-- Equivalence exposing the definition of `HoldsDTTable`. -/
theorem holdsDTTable_iff (r0 tableBase : ℕ) (mem : ℕ → ℕ) :
    HoldsDTTable r0 tableBase mem ↔
      ∀ mask < 2 ^ r0.choose 2,
        let entryPtr := mem (tableBase + mask)
        let pairs := maskEdgePairs r0 mask
        let e := pairs.length
        let d := mem (entryPtr + 1)
        let intBase := entryPtr + 2 + e
        let leafBase := intBase + 2 * (2 ^ d - 1)
        mem entryPtr = e ∧
        d = optDepth (endsOfMask r0 mask) ∧
        (∀ j (hj : j < e),
          mem (entryPtr + 2 + j) = pairIdx (pairs[j]).1.val (pairs[j]).2.val) ∧
        ∃ T : MSFDT e,
          T.IsComplete d ∧
          T.Correct (endsOfMask r0 mask) ∧
          HoldsCompleteTree d intBase leafBase d 1 mem T :=
  Iff.rfl

/-- Frontier-bounds predicate for a `HoldsDTTable` at `tableBase`. -/
def DTTableInBounds (r0 tableBase frontier : ℕ) (mem : ℕ → ℕ) : Prop :=
  tableBase + 2 ^ r0.choose 2 ≤ frontier ∧
  ∀ mask < 2 ^ r0.choose 2,
    let entryPtr := mem (tableBase + mask)
    let e := (maskEdgePairs r0 mask).length
    let d := mem (entryPtr + 1)
    entryPtr + 2 + e + 2 * (2 ^ d - 1) + 2 ^ d ≤ frontier

/-- Equivalence exposing the definition of `DTTableInBounds`. -/
theorem dtTableInBounds_iff (r0 tableBase frontier : ℕ) (mem : ℕ → ℕ) :
    DTTableInBounds r0 tableBase frontier mem ↔
      tableBase + 2 ^ r0.choose 2 ≤ frontier ∧
      ∀ mask < 2 ^ r0.choose 2,
        let entryPtr := mem (tableBase + mask)
        let e := (maskEdgePairs r0 mask).length
        let d := mem (entryPtr + 1)
        entryPtr + 2 + e + 2 * (2 ^ d - 1) + 2 ^ d ≤ frontier :=
  Iff.rfl

private theorem dtTable_entry_eq {r0 tableBase frontier mask : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hbnd : DTTableInBounds r0 tableBase frontier m₁)
    (heq : ∀ a < frontier, m₂ a = m₁ a) (hmask : mask < 2 ^ r0.choose 2) :
    m₂ (tableBase + mask) = m₁ (tableBase + mask) ∧
    m₂ (m₁ (tableBase + mask) + 1) = m₁ (m₁ (tableBase + mask) + 1) ∧
    1 ≤ 2 ^ m₁ (m₁ (tableBase + mask) + 1) ∧
    m₁ (tableBase + mask) + 2 + (maskEdgePairs r0 mask).length +
      2 * (2 ^ m₁ (m₁ (tableBase + mask) + 1) - 1) + 2 ^ m₁ (m₁ (tableBase + mask) + 1) ≤
        frontier := by
  have htb := hbnd.1
  have hent := hbnd.2 mask hmask
  dsimp only at hent
  have h2d : 1 ≤ 2 ^ m₁ (m₁ (tableBase + mask) + 1) := Nat.one_le_two_pow
  exact ⟨heq _ (by omega), heq _ (by omega), h2d, hent⟩

/-- Framing lemma for `HoldsDTTable`. -/
theorem HoldsDTTable.congr {r0 tableBase frontier : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hbnd : DTTableInBounds r0 tableBase frontier m₁)
    (heq : ∀ a < frontier, m₂ a = m₁ a)
    (htab : HoldsDTTable r0 tableBase m₁) : HoldsDTTable r0 tableBase m₂ := by
  intro mask hmask
  obtain ⟨hptr, hd_eq, h2d, hent⟩ := dtTable_entry_eq hbnd heq hmask
  have h1 := htab mask hmask
  dsimp only at hent h1 ⊢
  rw [hptr, hd_eq]
  refine ⟨(heq _ (by omega)).trans h1.1, h1.2.1, fun j hj => ?_, ?_⟩
  · exact (heq _ (by omega)).trans (h1.2.2.1 j hj)
  · obtain ⟨T, hcomp, hcorr, hhold⟩ := h1.2.2.2
    refine ⟨T, hcomp, hcorr, HoldsCompleteTree.congr (fun a ha1 ha2 => heq a (by omega))
      (fun a ha1 ha2 => heq a (by omega)) (le_refl _) (le_refl 1) (by simp) hhold⟩

/-- Monotonicity of `DTTableInBounds` under frontier growth and preservation below `frontier`. -/
theorem DTTableInBounds.mono {r0 tableBase f₁ f₂ : ℕ} {m₁ m₂ : ℕ → ℕ}
    (hbnd : DTTableInBounds r0 tableBase f₁ m₁) (hf : f₁ ≤ f₂)
    (heq : ∀ a < f₁, m₂ a = m₁ a) : DTTableInBounds r0 tableBase f₂ m₂ := by
  refine ⟨hbnd.1.trans hf, fun mask hmask => ?_⟩
  obtain ⟨hptr, hd_eq, _, hent⟩ := dtTable_entry_eq hbnd heq hmask
  dsimp only at hent ⊢
  rw [hptr, hd_eq]
  exact hent.trans hf

private theorem holdsDTTable_cast_aux (e₁ e₂ dInit entryPtr : ℕ) (he : e₁ = e₂)
    {mem : ℕ → ℕ} (T₁ : MSFDT e₁)
    (hcomp : T₁.IsComplete dInit)
    (hhold : HoldsCompleteTree dInit (entryPtr + 2 + e₁)
      (entryPtr + 2 + e₁ + 2 * (2 ^ dInit - 1)) dInit 1 mem T₁) :
    let σ : Fin e₁ ≃ Fin e₂ := (Fin.castOrderIso he).toEquiv
    let T₂ : MSFDT e₂ := (T₁.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ
    T₂.IsComplete dInit ∧
    HoldsCompleteTree dInit (entryPtr + 2 + e₂)
      (entryPtr + 2 + e₂ + 2 * (2 ^ dInit - 1)) dInit 1 mem T₂ := by
  subst he
  have hσ : (Fin.castOrderIso (rfl : e₁ = e₁)).toEquiv = Equiv.refl (Fin e₁) := by
    ext x; rfl
  have hmap_id : ∀ (T : MSFDT e₁),
      (T.mapLeaves (Finset.map (Equiv.refl (Fin e₁)).toEmbedding)).liftEmb
        (Equiv.refl (Fin e₁)) = T := by
    intro T
    induction T with
    | leaf ans =>
      simp only [MSFTree.mapLeaves, MSFTree.liftEmb]
      congr 1; ext x; simp
    | node i j l r ihl ihr =>
      simp only [MSFTree.mapLeaves, MSFTree.liftEmb]
      exact congrArg₂ (MSFTree.node i j) ihl ihr
  dsimp only
  rw [hσ, hmap_id T₁]
  exact ⟨hcomp, hhold⟩

private theorem msf_reindex_perm {e₁ e₂ n₁ n₂ : ℕ}
    (ends₁ : Fin e₁ → Sym2 (Fin n₁)) (ends₂ : Fin e₂ → Sym2 (Fin n₂))
    (σ : Fin e₁ ≃ Fin e₂) (φ : Fin n₁ ↪ Fin n₂)
    (hEnds : ∀ i : Fin e₁, Sym2.map φ (ends₁ i) = ends₂ (σ i))
    (p₁ : Equiv.Perm (Fin e₁)) (p₂ : Equiv.Perm (Fin e₂))
    (hp : ∀ a b : Fin e₁, (p₁ a).val < (p₁ b).val ↔ (p₂ (σ a)).val < (p₂ (σ b)).val) :
    Cslib.Multigraph.msf ends₂ p₂ Finset.univ =
      (Cslib.Multigraph.msf ends₁ p₁ Finset.univ).map σ.toEmbedding := by
  have hj_iff : ∀ (i : Fin e₁) (a₁ b₁ : Fin n₁),
      Cslib.Multigraph.Joins ends₁
          {f | f ∈ (Finset.univ : Finset (Fin e₁)) ∧ p₁ f < p₁ i} a₁ b₁ ↔
        Cslib.Multigraph.Joins ends₂
          {f | f ∈ (Finset.univ : Finset (Fin e₂)) ∧ p₂ f < p₂ (σ i)} (φ a₁) (φ b₁) := by
    intro i a₁ b₁
    have hflt : ((Finset.univ.filter fun e => (p₁ e).val < (p₁ i).val).map
        σ.toEmbedding : Finset (Fin e₂)) =
        Finset.univ.filter fun f => (p₂ f).val < (p₂ (σ i)).val := by
      ext f
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.coe_toEmbedding]
      exact ⟨fun ⟨e, he, hfe⟩ => hfe ▸ (hp e i).mp he,
        fun hf => ⟨σ.symm f, (hp _ _).mpr (by simpa using hf), σ.apply_symm_apply f⟩⟩
    have hs1 : {f | f ∈ (Finset.univ : Finset (Fin e₁)) ∧ p₁ f < p₁ i} =
        ↑(Finset.univ.filter fun e => (p₁ e).val < (p₁ i).val) := by
      ext e
      simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and, Finset.mem_coe, Finset.mem_filter,
        Fin.lt_def]
    have hs2 : {f | f ∈ (Finset.univ : Finset (Fin e₂)) ∧ p₂ f < p₂ (σ i)} =
        ↑(Finset.univ.filter fun f => (p₂ f).val < (p₂ (σ i)).val) := by
      ext f
      simp only [Set.mem_ofPred_eq, Finset.mem_univ, true_and, Finset.mem_coe, Finset.mem_filter,
        Fin.lt_def]
    rw [hs1, hs2, ← hflt]
    exact joins_reindex ends₁ ends₂ σ.toEmbedding φ hEnds _ a₁ b₁
  ext g
  rw [Finset.mem_map]
  constructor
  · intro hg
    let i := σ.symm g
    have hgi : σ i = g := σ.apply_symm_apply g
    refine ⟨i, ?_, hgi⟩
    obtain ⟨a₁, b₁, hab₁⟩ : ∃ a₁ b₁, ends₁ i = s(a₁, b₁) :=
      Sym2.ind (fun x y => ⟨x, y, rfl⟩) (ends₁ i)
    have hab₂ : ends₂ g = s(φ a₁, φ b₁) := by rw [← hgi, ← hEnds i, hab₁]; rfl
    rw [Cslib.Multigraph.mem_msf_iff p₂ hab₂] at hg
    rw [Cslib.Multigraph.mem_msf_iff p₁ hab₁]
    exact ⟨Finset.mem_univ _, fun hj => hg.2 (hgi ▸ (hj_iff i a₁ b₁).mp hj)⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨a₁, b₁, hab₁⟩ : ∃ a₁ b₁, ends₁ i = s(a₁, b₁) :=
      Sym2.ind (fun x y => ⟨x, y, rfl⟩) (ends₁ i)
    have hab₂ : ends₂ (σ.toEmbedding i) = s(φ a₁, φ b₁) := by
      change ends₂ (σ i) = s(φ a₁, φ b₁)
      rw [← hEnds i, hab₁]
      rfl
    rw [Cslib.Multigraph.mem_msf_iff p₁ hab₁] at hi
    rw [Cslib.Multigraph.mem_msf_iff p₂ hab₂]
    exact ⟨Finset.mem_univ _, fun hj => hi.2 ((hj_iff i a₁ b₁).mpr hj)⟩

/-- Specialize a `HoldsDTTable r0` entry at `mask < 2 ^ v.choose 2` to `v ≤ r0`. -/
theorem holdsDTTable_for_le {r0 v tableBase mask : ℕ} {mem : ℕ → ℕ}
    (htab : HoldsDTTable r0 tableBase mem) (hvr : v ≤ r0)
    (hmask : mask < 2 ^ v.choose 2) :
    let entryPtr := mem (tableBase + mask)
    let pairs := maskEdgePairs v mask
    let e := pairs.length
    let d := mem (entryPtr + 1)
    let intBase := entryPtr + 2 + e
    let leafBase := intBase + 2 * (2 ^ d - 1)
    mask < 2 ^ r0.choose 2 ∧
    mem entryPtr = e ∧
    d = optDepth (endsOfMask v mask) ∧
    d ≤ optDepthMN e v ∧
    (∀ j (hj : j < e),
      mem (entryPtr + 2 + j) = pairIdx (pairs[j]).1.val (pairs[j]).2.val) ∧
    ∃ T : MSFDT e,
      T.IsComplete d ∧
      T.Correct (endsOfMask v mask) ∧
      HoldsCompleteTree d intBase leafBase d 1 mem T := by
  have hch : v.choose 2 ≤ r0.choose 2 := by
    rw [Nat.choose_two_right, Nat.choose_two_right]
    exact Nat.div_le_div_right (Nat.mul_le_mul hvr (Nat.sub_le_sub_right hvr 1))
  have hmask_r0 : mask < 2 ^ r0.choose 2 :=
    hmask.trans_le (Nat.pow_le_pow_right (by decide) hch)
  obtain ⟨he_r0, hd_r0, hpairs_r0, T_r0, hcomp_r0, hcorr_r0, hhold_r0⟩ := htab mask hmask_r0
  have hcast := maskEdgePairs_cast hvr hmask
  have hlen : (maskEdgePairs r0 mask).length = (maskEdgePairs v mask).length := by
    rw [hcast, List.length_map]
  let σ : Fin (maskEdgePairs v mask).length ≃ Fin (maskEdgePairs r0 mask).length :=
    (Fin.castOrderIso hlen.symm).toEquiv
  let σinv : Fin (maskEdgePairs r0 mask).length ≃ Fin (maskEdgePairs v mask).length :=
    (Fin.castOrderIso hlen).toEquiv
  let T : MSFDT (maskEdgePairs v mask).length :=
    (T_r0.mapLeaves (Finset.map σinv.toEmbedding)).liftEmb σinv
  have haux := holdsDTTable_cast_aux _ _ _ _ hlen T_r0 hcomp_r0 hhold_r0
  have hd_v : mem (mem (tableBase + mask) + 1) = optDepth (endsOfMask v mask) := by
    rw [hd_r0, optDepth_endsOfMask_le hvr hmask]
  refine ⟨hmask_r0, he_r0.trans hlen, hd_v, ?_, fun j hj => ?_, T, haux.1, fun p => ?_, haux.2⟩
  · rw [hd_v]
    exact optDepth_endsOfMask_le_optDepthMN hmask le_rfl
  · have hj_r0 : j < (maskEdgePairs r0 mask).length := hlen.symm ▸ hj
    have hget : (maskEdgePairs r0 mask)[j] =
        Prod.map (Fin.castLE hvr) (Fin.castLE hvr) (maskEdgePairs v mask)[j] := by
      have hc := congrArg (fun l => l[j]?) hcast
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj_r0,
        List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at hc
      exact hc
    rw [hpairs_r0 j hj_r0, hget]
    rfl
  · let p' : Equiv.Perm (Fin (maskEdgePairs r0 mask).length) := σinv.trans (p.trans σ)
    have heval : T.eval p = (T_r0.eval p').map σinv.toEmbedding := by
      rw [← MSFTree.mapLeaves_eval (Finset.map σinv.toEmbedding) T_r0 p']
      exact MSFTree.liftEmb_eval σinv (T_r0.mapLeaves _) p' p fun _ _ => Iff.rfl
    have hmsf : Cslib.Multigraph.msf (endsOfMask r0 mask) p' Finset.univ =
        (Cslib.Multigraph.msf (endsOfMask v mask) p Finset.univ).map σ.toEmbedding := by
      refine msf_reindex_perm (endsOfMask v mask) (endsOfMask r0 mask)
        σ (Fin.castLEEmb hvr) (fun i => ?_) p p' (fun _ _ => Iff.rfl)
      have hget : (maskEdgePairs r0 mask)[(σ i).val] =
          Prod.map (Fin.castLE hvr) (Fin.castLE hvr) (maskEdgePairs v mask)[i.val] := by
        have hi_r0 : (σ i).val < (maskEdgePairs r0 mask).length := (σ i).isLt
        have hi_v : (σ i).val < (maskEdgePairs v mask).length := Nat.lt_of_lt_of_eq hi_r0 hlen
        have hc := congrArg (fun l => l[(σ i).val]?) hcast
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi_r0,
          List.getElem?_eq_getElem hi_v, Option.map_some, Option.some.injEq] at hc
        exact hc
      dsimp only [endsOfMask]
      simp only [Fin.getElem_fin, hget]
      rfl
    rw [heval, hcorr_r0 p', hmsf, Finset.map_map]
    ext x
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩
      convert ha
      exact σ.left_inv a
    · intro hx
      exact ⟨x, hx, σ.left_inv x⟩

/-- Canonical pair index `pairIdx (min u v) (max u v)` of an undirected endpoint pair `(u, v)`. -/
@[expose] def edgePairIdx (u v : ℕ) : ℕ :=
  if u < v then pairIdx u v else pairIdx v u

/-- Bitmask encoding the unordered edge set of `es : List (Fin v × Fin v)` over `allPairs v`. -/
@[expose] def dtGraphMask {v : ℕ} (es : List (Fin v × Fin v)) : ℕ :=
  es.foldl (fun acc e => acc ||| (1 <<< edgePairIdx e.1.val e.2.val)) 0

private theorem foldl_or_testBit {α : Type*} (f : α → ℕ) (xs : List α) (init k : ℕ) :
    (xs.foldl (fun acc x => acc ||| (1 <<< f x)) init).testBit k =
      (init.testBit k || decide (∃ x ∈ xs, f x = k)) := by
  induction xs generalizing init with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]
    by_cases hfx : f x = k
    · subst hfx; simp
    · have h1 : (decide (f x ≤ k) && Nat.testBit 1 (k - f x)) = false := by
        cases hle : decide (f x ≤ k)
        · rfl
        · rw [decide_eq_true_eq] at hle
          have hnz : 1 < 2 ^ (k - f x) := Nat.one_lt_two_pow (by omega)
          have htb : Nat.testBit 1 (k - f x) = false := by
            rw [Nat.testBit_eq_decide_div_mod_eq]
            have hdiv : 1 / 2 ^ (k - f x) = 0 := Nat.div_eq_of_lt hnz
            simp [hdiv]
          simp [htb]
      simp [h1, hfx]

/-- Characterizes bit `k` of `dtGraphMask es` as existence of an edge with `edgePairIdx = k`. -/
theorem dtGraphMask_testBit {v : ℕ} (es : List (Fin v × Fin v)) (k : ℕ) :
    (dtGraphMask es).testBit k = decide (∃ e ∈ es, edgePairIdx e.1.val e.2.val = k) := by
  dsimp only [dtGraphMask]
  rw [foldl_or_testBit]
  simp

private theorem foldl_or_lt_two_pow {α : Type*} (f : α → ℕ) (xs : List α) (M init : ℕ)
    (hi : init < 2 ^ M) (hxs : ∀ x ∈ xs, f x < M) :
    xs.foldl (fun acc x => acc ||| (1 <<< f x)) init < 2 ^ M := by
  induction xs generalizing init with
  | nil => exact hi
  | cons x rest ih =>
    simp only [List.foldl_cons]
    refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem x hy))
    have hfx : 1 <<< f x < 2 ^ M := by
      rw [Nat.shiftLeft_eq, one_mul]
      exact Nat.pow_lt_pow_right (by decide) (hxs x List.mem_cons_self)
    exact Nat.or_lt_two_pow hi hfx

/-- `dtGraphMask es` is strictly below `2 ^ v.choose 2` for any loopless edge list `es`. -/
theorem dtGraphMask_lt {v : ℕ} (es : List (Fin v × Fin v))
    (hno : ∀ e ∈ es, e.1 ≠ e.2) : dtGraphMask es < 2 ^ v.choose 2 := by
  refine foldl_or_lt_two_pow (fun e : Fin v × Fin v => edgePairIdx e.1.val e.2.val)
    es (v.choose 2) 0 (Nat.two_pow_pos _) fun e he => ?_
  dsimp only [edgePairIdx]
  have hne : e.1.val ≠ e.2.val := fun h => hno e he (Fin.ext h)
  split_ifs with huv
  · exact pairIdx_lt_choose_two huv e.2.isLt
  · exact pairIdx_lt_choose_two (by omega) e.1.isLt

private def canonPair {v : ℕ} (p : Fin v × Fin v) : Fin v × Fin v :=
  if p.1.val < p.2.val then p else (p.2, p.1)

/-- Canonical reindexing from a simple edge list `es : List (Fin v × Fin v)` to
`endsOfMask v (dtGraphMask es)`, preserving `pairIdx`, `Sym2` endpoints, length, and
`optDepth`. -/
theorem endsOfMask_reindex_dtGraphMask {v : ℕ} (es : List (Fin v × Fin v))
    (hsimp : IsSimple (fun i : Fin es.length => s(es[i.val].1, es[i.val].2))) :
    let mask := dtGraphMask es
    mask < 2 ^ v.choose 2 ∧
    (maskEdgePairs v mask).length = es.length ∧
    optDepth (fun i : Fin es.length => s(es[i.val].1, es[i.val].2)) =
      optDepth (endsOfMask v mask) ∧
    ∃ σ : Fin es.length ≃ Fin (maskEdgePairs v mask).length,
      (∀ k : Fin es.length,
        pairIdx ((maskEdgePairs v mask)[(σ k).val]).1.val
          ((maskEdgePairs v mask)[(σ k).val]).2.val =
          edgePairIdx es[k.val].1.val es[k.val].2.val) ∧
      (∀ k : Fin es.length,
        s(es[k.val].1, es[k.val].2) = endsOfMask v mask (σ k)) := by
  have hsimp' := (isSimple_iff _).mp hsimp
  have hno : ∀ e ∈ es, e.1 ≠ e.2 := fun e he heq => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp he
    exact hsimp'.1 ⟨k, hk⟩ (Sym2.mk_isDiag_iff.mpr heq)
  have hmask_lt : dtGraphMask es < 2 ^ v.choose 2 := dtGraphMask_lt es hno
  have hcp_lt : ∀ i : Fin es.length, (canonPair es[i.val]).1.val < (canonPair es[i.val]).2.val :=
    fun i => by
      have hne : es[i.val].1.val ≠ es[i.val].2.val :=
        fun h => hno es[i.val] (List.getElem_mem i.isLt) (Fin.ext h)
      by_cases h : es[i.val].1.val < es[i.val].2.val
      · simp [canonPair, h]
      · simp [canonPair, h]; omega
  have hcp_pidx : ∀ i : Fin es.length,
      pairIdx (canonPair es[i.val]).1.val (canonPair es[i.val]).2.val =
        edgePairIdx es[i.val].1.val es[i.val].2.val := fun i => by
    dsimp only [canonPair, edgePairIdx]; split_ifs <;> rfl
  have hcp_sym2 : ∀ i : Fin es.length,
      s((canonPair es[i.val]).1, (canonPair es[i.val]).2) = s(es[i.val].1, es[i.val].2) :=
    fun i => by
      dsimp only [canonPair]; split_ifs
      · rfl
      · exact Sym2.eq_swap
  have hmem : ∀ i : Fin es.length, canonPair es[i.val] ∈ maskEdgePairs v (dtGraphMask es) :=
    fun i => by
      rw [mem_maskEdgePairs_iff]
      refine ⟨hcp_lt i, ?_⟩
      rw [hcp_pidx i, dtGraphMask_testBit, decide_eq_true_iff]
      exact ⟨es[i.val], List.getElem_mem i.isLt, rfl⟩
  have hback : ∀ p ∈ maskEdgePairs v (dtGraphMask es),
      ∃ i : Fin es.length, canonPair es[i.val] = p := by
    intro p hp
    obtain ⟨hlt, htb⟩ := mem_maskEdgePairs_iff.mp hp
    rw [dtGraphMask_testBit, decide_eq_true_iff] at htb
    obtain ⟨e, he, hpe⟩ := htb
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    refine ⟨⟨i, hi⟩, ?_⟩
    have hpi : pairIdx (canonPair es[i]).1.val (canonPair es[i]).2.val =
        pairIdx p.1.val p.2.val := (hcp_pidx ⟨i, hi⟩).trans hpe
    have h1 := getElem_allPairs_pairIdx (hcp_lt ⟨i, hi⟩)
    have h2 := getElem_allPairs_pairIdx hlt
    have h12 : canonPair es[i] = p := by
      have hlen1 : pairIdx (canonPair es[i]).1.val (canonPair es[i]).2.val <
          (allPairs v).length := by
        rw [length_allPairs]; exact pairIdx_lt_choose_two (hcp_lt ⟨i, hi⟩) (canonPair es[i]).2.isLt
      have hlen2 : pairIdx p.1.val p.2.val < (allPairs v).length := by
        rw [length_allPairs]; exact pairIdx_lt_choose_two hlt p.2.isLt
      calc canonPair es[i]
          = (allPairs v)[pairIdx (canonPair es[i]).1.val (canonPair es[i]).2.val]'hlen1 := h1.symm
        _ = (allPairs v)[pairIdx p.1.val p.2.val]'hlen2 := by simp only [hpi]
        _ = p := h2
    exact h12
  let f : Fin es.length → Fin (maskEdgePairs v (dtGraphMask es)).length := fun i =>
    ⟨(maskEdgePairs v (dtGraphMask es)).idxOf (canonPair es[i.val]),
      List.idxOf_lt_length_of_mem (hmem i)⟩
  have hf_get : ∀ i : Fin es.length,
      (maskEdgePairs v (dtGraphMask es))[(f i).val] = canonPair es[i.val] := fun i =>
    List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem i))
  have hf_bij : Function.Bijective f := by
    constructor
    · intro i₁ i₂ he
      apply hsimp'.2
      have h1 : s(es[i₁.val].1, es[i₁.val].2) =
          s((maskEdgePairs v (dtGraphMask es))[(f i₁).val].1,
            (maskEdgePairs v (dtGraphMask es))[(f i₁).val].2) := by
        rw [hf_get i₁, hcp_sym2 i₁]
      have h2 : s(es[i₂.val].1, es[i₂.val].2) =
          s((maskEdgePairs v (dtGraphMask es))[(f i₂).val].1,
            (maskEdgePairs v (dtGraphMask es))[(f i₂).val].2) := by
        rw [hf_get i₂, hcp_sym2 i₂]
      change s(es[i₁.val].1, es[i₁.val].2) = s(es[i₂.val].1, es[i₂.val].2)
      rw [h1, h2, he]
    · intro k
      obtain ⟨i, hi⟩ := hback _ (List.getElem_mem k.isLt)
      refine ⟨i, Fin.ext ?_⟩
      exact (maskEdgePairs_nodup v (dtGraphMask es)).getElem_inj_iff.mp ((hf_get i).trans hi)
  let σ : Fin es.length ≃ Fin (maskEdgePairs v (dtGraphMask es)).length :=
    Equiv.ofBijective f hf_bij
  have hσ_get : ∀ i : Fin es.length,
      (maskEdgePairs v (dtGraphMask es))[(σ i).val] = canonPair es[i.val] := hf_get
  have hlen : (maskEdgePairs v (dtGraphMask es)).length = es.length := by
    simpa using Fintype.card_congr σ.symm
  have hopt : optDepth (fun i : Fin es.length => s(es[i.val].1, es[i.val].2)) =
      optDepth (endsOfMask v (dtGraphMask es)) := by
    refine optDepth_reindex _ (endsOfMask v (dtGraphMask es))
      σ (Equiv.refl (Fin v)).toEmbedding fun i => ?_
    change Sym2.map id s(es[i.val].1, es[i.val].2) =
      s((maskEdgePairs v (dtGraphMask es))[(σ i).val].1,
        (maskEdgePairs v (dtGraphMask es))[(σ i).val].2)
    rw [Sym2.map_id, hσ_get i, hcp_sym2 i]
    rfl
  refine ⟨hmask_lt, hlen, hopt, σ, fun k => ?_, fun k => ?_⟩
  · rw [hσ_get k, hcp_pidx k]
  · change s(es[k.val].1, es[k.val].2) =
      s((maskEdgePairs v (dtGraphMask es))[(σ k).val].1,
        (maskEdgePairs v (dtGraphMask es))[(σ k).val].2)
    rw [hσ_get k, hcp_sym2 k]

/-- Pure complete-tree walk matching edge comparison order `cmp : Fin e → Fin e → Bool`. -/
@[expose] def walkCompleteTree {e : ℕ} (intBase leafBase : ℕ) (mem : ℕ → ℕ)
    (cmp : Fin e → Fin e → Bool) : ℕ → ℕ → ℕ
  | 0, node => node
  | d + 1, node =>
    let a := mem (intBase + 2 * (node - 1))
    let b := mem (intBase + 2 * (node - 1) + 1)
    if h : a < e ∧ b < e then
      if cmp ⟨a, h.1⟩ ⟨b, h.2⟩ then
        walkCompleteTree intBase leafBase mem cmp d (2 * node)
      else
        walkCompleteTree intBase leafBase mem cmp d (2 * node + 1)
    else
      walkCompleteTree intBase leafBase mem cmp d (2 * node + 1)

/-- Evaluates `walkCompleteTree` on a complete decision tree stored in memory, proving leaf bounds
and agreement with `T.eval p`. -/
theorem walkCompleteTree_eval {e dInit intBase leafBase : ℕ} {mem : ℕ → ℕ}
    (p : Equiv.Perm (Fin e)) (cmp : Fin e → Fin e → Bool)
    (hcmp : ∀ a b : Fin e, cmp a b = true ↔ (p a).val < (p b).val) :
    ∀ {d node : ℕ} {T : MSFDT e},
      HoldsCompleteTree dInit intBase leafBase d node mem T →
      let endNode := walkCompleteTree intBase leafBase mem cmp d node
      2 ^ dInit ≤ endNode ∧ endNode < 2 ^ (dInit + 1) ∧
      mem (leafBase + (endNode - 2 ^ dInit)) = maskOfFinset (T.eval p) := by
  intro d
  induction d with
  | zero =>
    intro node T hhold
    cases T with
    | node _ _ _ _ => exact absurd hhold holdsCompleteTree_zero_node
    | leaf ans => exact holdsCompleteTree_leaf.mp hhold
  | succ d ih =>
    intro node T hhold
    cases T with
    | leaf _ => exact absurd hhold holdsCompleteTree_succ_leaf
    | node i j l r =>
      obtain ⟨_, _, h0, h1, hl, hr⟩ := holdsCompleteTree_node.mp hhold
      dsimp only [walkCompleteTree, MSFTree.eval]
      have ha : mem (intBase + 2 * (node - 1)) < e := by rw [h0]; exact i.isLt
      have hb : mem (intBase + 2 * (node - 1) + 1) < e := by rw [h1]; exact j.isLt
      simp only [ha, hb, and_self, ↓reduceDIte]
      have hi_eq : (⟨mem (intBase + 2 * (node - 1)), ha⟩ : Fin e) = i := Fin.ext h0
      have hj_eq : (⟨mem (intBase + 2 * (node - 1) + 1), hb⟩ : Fin e) = j := Fin.ext h1
      rw [hi_eq, hj_eq]
      by_cases hlt : (p i).val < (p j).val
      · have hc : cmp i j = true := (hcmp i j).mpr hlt
        simp only [hc, ↓reduceIte, hlt]
        exact ih hl
      · have hc : cmp i j = false := by
          cases hcv : cmp i j
          · rfl
          · exact absurd ((hcmp i j).mp hcv) hlt
        simp only [hc, Bool.false_eq_true, ↓reduceIte, hlt]
        exact ih hr

private theorem sum_range_shift_mul (B N : ℕ) (g : ℕ → ℕ) :
    ∑ k ∈ Finset.range N, g k * B ^ (k + 1) = B * ∑ k ∈ Finset.range N, g k * B ^ k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- Base-`B` digit decoding of `∑ k < N, f k * B^k` when `∀ k < N, f k < B`. -/
theorem baseB_digit_decode (B N : ℕ) (f : ℕ → ℕ) (hf : ∀ k < N, f k < B) :
    ∀ m < N, ((∑ k ∈ Finset.range N, f k * B ^ k) / B ^ m) % B = f m := by
  induction N generalizing f with
  | zero => intro m hm; omega
  | succ N ih =>
    intro m hm
    have hB : 0 < B := by have := hf 0 (Nat.zero_lt_succ N); omega
    rw [Finset.sum_range_succ', sum_range_shift_mul]
    cases m with
    | zero =>
      simp only [pow_zero, mul_one, Nat.div_one]
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (hf 0 (Nat.zero_lt_succ N))]
    | succ m =>
      simp only [pow_zero, mul_one]
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.mul_add_div hB, Nat.div_eq_of_lt (hf 0 (Nat.zero_lt_succ N))]
      simpa only [Nat.add_zero] using
        ih (fun k => f (k + 1)) (fun k hk => hf (k + 1) (Nat.succ_lt_succ hk))
          m (Nat.lt_of_succ_lt_succ hm)

/-- Total sum `∑ k < N, f k * B^k` is strictly below `B^N` when `∀ k < N, f k < B`. -/
theorem baseB_sum_lt (B N : ℕ) (f : ℕ → ℕ) (hf : ∀ k < N, f k < B) :
    ∑ k ∈ Finset.range N, f k * B ^ k < B ^ N := by
  induction N generalizing f with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ', pow_succ', sum_range_shift_mul]
    have hrec := ih (fun k => f (k + 1)) (fun k hk => hf (k + 1) (Nat.succ_lt_succ hk))
    have hf0 := hf 0 (Nat.zero_lt_succ N)
    simp only [pow_zero, mul_one]
    nlinarith

/-- Characterization of `MSFTree.IsComplete` at a leaf of depth `0`. -/
@[simp] theorem msfTree_isComplete_leaf {e : ℕ} {α : Type} {ans : α} :
    (MSFTree.leaf ans : MSFTree e α).IsComplete 0 :=
  trivial

/-- Characterization of `MSFTree.IsComplete` at depth `0` on an internal node. -/
@[simp] theorem msfTree_isComplete_zero_node {e : ℕ} {α : Type} {i j : Fin e}
    {l r : MSFTree e α} :
    ¬ (MSFTree.node i j l r).IsComplete 0 := by
  simp [MSFTree.IsComplete]

/-- Characterization of `MSFTree.IsComplete` at positive depth on a leaf. -/
@[simp] theorem msfTree_isComplete_succ_leaf {e d : ℕ} {α : Type} {ans : α} :
    ¬ (MSFTree.leaf ans : MSFTree e α).IsComplete (d + 1) := by
  simp [MSFTree.IsComplete]

/-- Characterization of `MSFTree.IsComplete` at depth `d + 1` on an internal node. -/
@[simp] theorem msfTree_isComplete_node {e d : ℕ} {α : Type} {i j : Fin e}
    {l r : MSFTree e α} :
    (MSFTree.node i j l r).IsComplete (d + 1) ↔
      i.val < j.val ∧ l.IsComplete d ∧ r.IsComplete d :=
  Iff.rfl

/-- Decode a base-`e.choose 2` skeleton integer `skelCode` and leaf bitmask table
`leafMask` into a complete `MSFDT e` of uniform depth `d`, rooted at `node`. -/
@[expose] def skelToTree (e : ℕ) (he : 2 ≤ e) (dInit skelCode : ℕ)
    (leafMask : ℕ → ℕ) : ℕ → ℕ → MSFDT e
  | 0, node =>
    let m := leafMask (node - 2 ^ dInit)
    .leaf (Finset.univ.filter fun i : Fin e => m.testBit i.val)
  | d + 1, node =>
    let numPairs := e.choose 2
    let pk := (skelCode / numPairs ^ (node - 1)) % numPairs
    let p := if h : pk < (allPairs e).length then (allPairs e)[pk]'h
             else (⟨0, by omega⟩, ⟨1, by omega⟩)
    .node p.1 p.2
      (skelToTree e he dInit skelCode leafMask d (2 * node))
      (skelToTree e he dInit skelCode leafMask d (2 * node + 1))

/-- Every tree constructed by `skelToTree` at depth `d` is complete of depth `d`. -/
theorem skelToTree_isComplete (e : ℕ) (he : 2 ≤ e) (dInit skelCode : ℕ)
    (leafMask : ℕ → ℕ) :
    ∀ d node, (skelToTree e he dInit skelCode leafMask d node).IsComplete d := by
  intro d
  induction d with
  | zero => intro node; simp [skelToTree]
  | succ d ih =>
    intro node
    dsimp only [skelToTree]
    split_ifs with h
    · exact msfTree_isComplete_node.mpr
        ⟨allPairs_lt (List.getElem_mem h), ih (2 * node), ih (2 * node + 1)⟩
    · exact msfTree_isComplete_node.mpr ⟨Nat.zero_lt_one, ih (2 * node), ih (2 * node + 1)⟩

/-! ## Section 3: Pure Skeleton Walk, Permutation Coding, and Arithmetic Bounds -/

private theorem choose_two_eq_div (n : ℕ) : n.choose 2 = n * (n - 1) / 2 :=
  Nat.choose_two_right n

private def pathFromRoot : ℕ → List Bool
  | 0 => []
  | 1 => []
  | q + 2 => pathFromRoot ((q + 2) / 2) ++ [decide ((q + 2) % 2 = 1)]
termination_by q => q

private theorem pathFromRoot_two_mul {q : ℕ} (hq : 1 ≤ q) :
    pathFromRoot (2 * q) = pathFromRoot q ++ [false] := by
  cases q with
  | zero => omega
  | succ n =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega]
    conv_lhs => unfold pathFromRoot
    rw [show (2 * n + 2) / 2 = n + 1 by omega, show (2 * n + 2) % 2 = 0 by omega]
    simp

private theorem pathFromRoot_two_mul_add_one {q : ℕ} (hq : 1 ≤ q) :
    pathFromRoot (2 * q + 1) = pathFromRoot q ++ [true] := by
  cases q with
  | zero => omega
  | succ n =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega]
    conv_lhs => unfold pathFromRoot
    rw [show (2 * n + 1 + 2) / 2 = n + 1 by omega, show (2 * n + 1 + 2) % 2 = 1 by omega]
    simp

private def subtreeAtPath {e : ℕ} : MSFDT e → List Bool → MSFDT e
  | T, [] => T
  | .leaf ans, _ :: _ => .leaf ans
  | .node _ _ l r, b :: bs => if b then subtreeAtPath r bs else subtreeAtPath l bs

private theorem subtreeAtPath_nil {e : ℕ} (T : MSFDT e) : subtreeAtPath T [] = T := by
  cases T <;> rfl

private theorem subtreeAtPath_append {e : ℕ} (T : MSFDT e) (bs₁ bs₂ : List Bool) :
    subtreeAtPath T (bs₁ ++ bs₂) = subtreeAtPath (subtreeAtPath T bs₁) bs₂ := by
  induction bs₁ generalizing T with
  | nil => cases T <;> cases bs₂ <;> rfl
  | cons b bs₁ ih =>
    cases T with
    | leaf ans => cases bs₂ <;> simp [subtreeAtPath]
    | node _ _ l r =>
      dsimp only [List.cons_append, subtreeAtPath]
      split_ifs <;> exact ih _

private theorem subtreeAtPath_isComplete {e d k : ℕ} {T : MSFDT e}
    (hcomp : T.IsComplete (k + d)) (bs : List Bool) (hbs : bs.length = k) :
    (subtreeAtPath T bs).IsComplete d := by
  induction k generalizing T bs with
  | zero =>
    cases bs with
    | nil => simpa [Nat.zero_add, subtreeAtPath] using hcomp
    | cons _ _ => simp at hbs
  | succ k ih =>
    cases bs with
    | nil => simp at hbs
    | cons b bs =>
      cases T with
      | leaf _ =>
        rw [show k + 1 + d = (k + d) + 1 by omega] at hcomp
        exact absurd hcomp msfTree_isComplete_succ_leaf
      | node i j l r =>
        rw [show k + 1 + d = (k + d) + 1 by omega] at hcomp
        obtain ⟨_, hl, hr⟩ := msfTree_isComplete_node.mp hcomp
        dsimp only [subtreeAtPath]
        split_ifs
        · exact ih hr bs (by simpa using hbs)
        · exact ih hl bs (by simpa using hbs)

private theorem length_pathFromRoot_lt {k d : ℕ} (hk1 : 1 ≤ k) (hk2 : k < 2 ^ d) :
    (pathFromRoot k).length < d := by
  induction k using Nat.strongRecOn generalizing d with
  | ind k ih =>
    rcases k with _ | _ | q
    · omega
    · cases d with
      | zero => simp at hk2
      | succ d => simp [pathFromRoot]
    · cases d with
      | zero => simp at hk2
      | succ d =>
        have hq2 : (q + 2) / 2 < 2 ^ d := by rw [Nat.pow_succ'] at hk2; omega
        have hih := ih ((q + 2) / 2) (by omega) (by omega) hq2
        conv_lhs => unfold pathFromRoot
        simp only [List.length_append, List.length_singleton]
        omega

private theorem lt_two_pow_of_length_pathFromRoot :
    ∀ q, 1 ≤ q → q < 2 ^ ((pathFromRoot q).length + 1) := by
  intro q hq
  induction q using Nat.strongRecOn with
  | ind q ih =>
    rcases q with _ | _ | q
    · omega
    · simp [pathFromRoot]
    · have hih := ih ((q + 2) / 2) (by omega) (by omega)
      conv_rhs => unfold pathFromRoot
      simp only [List.length_append, List.length_singleton]
      rw [show (pathFromRoot ((q + 2) / 2)).length + 1 + 1 =
        ((pathFromRoot ((q + 2) / 2)).length + 1) + 1 by omega, Nat.pow_succ']
      omega

/-- Walks internal comparisons of encoded skeleton `skelCode` for `d` levels starting at `node`
under comparison permutation `p`, returning the final `1`-indexed tree node. -/
@[expose] def walkSkelNode (e : ℕ) (he : 2 ≤ e) (skelCode : ℕ) :
    ℕ → ℕ → Equiv.Perm (Fin e) → ℕ
  | 0, node, _ => node
  | d + 1, node, p =>
    let numPairs := e.choose 2
    let pk := (skelCode / numPairs ^ (node - 1)) % numPairs
    let pr := if h : pk < (allPairs e).length then (allPairs e)[pk]'h
              else (⟨0, by omega⟩, ⟨1, by omega⟩)
    if (p pr.1).val < (p pr.2).val then
      walkSkelNode e he skelCode d (2 * node) p
    else
      walkSkelNode e he skelCode d (2 * node + 1) p

/-- Node-index range bounds `[node * 2^d, (node + 1) * 2^d)` after `d` skeleton steps. -/
theorem walkSkelNode_bounds (e : ℕ) (he : 2 ≤ e) (skelCode : ℕ)
    (p : Equiv.Perm (Fin e)) :
    ∀ d node, 1 ≤ node →
      node * 2 ^ d ≤ walkSkelNode e he skelCode d node p ∧
      walkSkelNode e he skelCode d node p < (node + 1) * 2 ^ d := by
  intro d
  induction d with
  | zero => intro node h1; dsimp only [walkSkelNode]; simp
  | succ d ih =>
    intro node h1
    dsimp only [walkSkelNode]
    split_ifs <;>
    · first
      | (obtain ⟨hl, hr⟩ := ih (2 * node) (by omega)
         rw [Nat.pow_succ']; exact ⟨by nlinarith, by nlinarith⟩)
      | (obtain ⟨hl, hr⟩ := ih (2 * node + 1) (by omega)
         rw [Nat.pow_succ']; exact ⟨by nlinarith, by nlinarith⟩)

/-- Evaluates `skelToTree` along `walkSkelNode` for any leaf bitmask assignment `leafMask`. -/
theorem skelToTree_eval_eq_leafMask (e : ℕ) (he : 2 ≤ e) (dInit skelCode : ℕ)
    (leafMask : ℕ → ℕ) (p : Equiv.Perm (Fin e)) :
    ∀ d node,
      (skelToTree e he dInit skelCode leafMask d node).eval p =
        Finset.univ.filter (fun i : Fin e =>
          (leafMask (walkSkelNode e he skelCode d node p - 2 ^ dInit)).testBit i.val) := by
  intro d
  induction d with
  | zero => intro node; rfl
  | succ d ih =>
    intro node
    dsimp only [skelToTree, walkSkelNode, MSFTree.eval]
    split_ifs <;> exact ih _

/-- Memory realization bridge for `skelToTree` when internal pairs and leaves match memory. -/
theorem holdsCompleteTree_skelToTree {e dInit intBase leafBase allPairA allPairB
    skelCode : ℕ} (he : 2 ≤ e) (leafMask : ℕ → ℕ) {mem : ℕ → ℕ}
    (hleaf_lt : ∀ l < 2 ^ dInit, leafMask l < 2 ^ e)
    (hpairs : ∀ (pk : ℕ) (hpk : pk < e.choose 2),
      mem (allPairA + pk) = ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).1.val ∧
      mem (allPairB + pk) = ((allPairs e)[pk]'(by rw [length_allPairs]; exact hpk)).2.val)
    (hint : ∀ k < 2 ^ dInit - 1,
      let pk := (skelCode / (e.choose 2) ^ k) % e.choose 2
      mem (intBase + 2 * k) = mem (allPairA + pk) ∧
      mem (intBase + 2 * k + 1) = mem (allPairB + pk))
    (hleaf : ∀ l < 2 ^ dInit, mem (leafBase + l) = leafMask l) :
    ∀ d node, d ≤ dInit → 2 ^ (dInit - d) ≤ node → node < 2 ^ (dInit - d + 1) →
      HoldsCompleteTree dInit intBase leafBase d node mem
        (skelToTree e he dInit skelCode leafMask d node) := by
  intro d
  induction d with
  | zero =>
    intro node hd hlo hhi
    rw [Nat.sub_zero] at hlo hhi
    dsimp only [skelToTree, HoldsCompleteTree]
    have hsub : node - 2 ^ dInit < 2 ^ dInit := by
      have : 2 ^ (dInit + 1) = 2 ^ dInit + 2 ^ dInit := by rw [Nat.pow_succ']; ring
      omega
    have hmask : maskOfFinset
        (Finset.univ.filter fun i : Fin e => (leafMask (node - 2 ^ dInit)).testBit i.val) =
        leafMask (node - 2 ^ dInit) := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [testBit_maskOfFinset]
      by_cases hk : k < e
      · simp [hk]
      · simp only [hk]
        symm
        exact Nat.testBit_eq_false_of_lt ((hleaf_lt _ hsub).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.not_lt.mp hk)))
    refine ⟨hlo, hhi, ?_⟩
    rw [hleaf _ hsub, hmask]
  | succ d ih =>
    intro node hd hlo hhi
    have h1_le : 1 ≤ node := (Nat.two_pow_pos _).trans_le hlo
    have hpow_le : 2 ^ (dInit - (d + 1) + 1) ≤ 2 ^ dInit :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hnode_lt : node < 2 ^ dInit := hhi.trans_le hpow_le
    have hk_lt : node - 1 < 2 ^ dInit - 1 := by omega
    have hnp_pos : 0 < e.choose 2 := by
      rw [choose_two_eq_div]
      exact Nat.div_pos (Nat.mul_le_mul he (Nat.sub_le_sub_right he 1)) (by decide)
    have hpk_lt :
        (skelCode / (e.choose 2) ^ (node - 1)) % e.choose 2 < (allPairs e).length := by
      rw [length_allPairs]
      exact Nat.mod_lt _ hnp_pos
    dsimp only [skelToTree]
    simp only [hpk_lt, ↓reduceDIte]
    dsimp only [HoldsCompleteTree]
    have hlt_pair :
        ((allPairs e)[(skelCode / (e.choose 2) ^ (node - 1)) % e.choose 2]'hpk_lt).1.val <
        ((allPairs e)[(skelCode / (e.choose 2) ^ (node - 1)) % e.choose 2]'hpk_lt).2.val :=
      allPairs_lt (List.getElem_mem hpk_lt)
    have hpk_lt' : (skelCode / (e.choose 2) ^ (node - 1)) % e.choose 2 < e.choose 2 :=
      Nat.mod_lt _ hnp_pos
    obtain ⟨ha_mem, hb_mem⟩ := hpairs _ hpk_lt'
    obtain ⟨hi_a, hi_b⟩ := hint (node - 1) hk_lt
    have h2lo : 2 ^ (dInit - d) ≤ 2 * node := by
      rw [show dInit - d = (dInit - (d + 1)) + 1 by omega, Nat.pow_succ']
      omega
    have h2hi : 2 * node + 1 < 2 ^ (dInit - d + 1) := by
      rw [show dInit - d + 1 = (dInit - (d + 1) + 1) + 1 by omega, Nat.pow_succ']
      omega
    refine ⟨h1_le, hlt_pair, hi_a.trans ha_mem, hi_b.trans hb_mem,
      ih (2 * node) (by omega) h2lo (by omega),
      ih (2 * node + 1) (by omega) (by omega) h2hi⟩

/-- Existence of a separating skeleton code `< (e.choose 2) ^ (2 ^ d - 1)` whenever
`optDepth ends ≤ d`. -/
theorem exists_skelCode_of_complete_correct {e n d : ℕ} (he : 2 ≤ e)
    (ends : Fin e → Sym2 (Fin n)) (hopt : optDepth ends ≤ d) :
    ∃ skelCode < (e.choose 2) ^ (2 ^ d - 1),
      ∀ p q : Equiv.Perm (Fin e),
        walkSkelNode e he skelCode d 1 p = walkSkelNode e he skelCode d 1 q →
        Cslib.Multigraph.msf ends p Finset.univ = Cslib.Multigraph.msf ends q Finset.univ := by
  obtain ⟨T, hcomp, hcorr⟩ := (exists_complete_correct_iff he ends d).mpr hopt
  let numPairs := e.choose 2
  have hnp_pos : 0 < numPairs := by
    dsimp only [numPairs]; rw [choose_two_eq_div]
    exact Nat.div_pos (Nat.mul_le_mul he (Nat.sub_le_sub_right he 1)) (by decide)
  let f : ℕ → ℕ := fun k =>
    if _ : k < 2 ^ d - 1 then
      match subtreeAtPath T (pathFromRoot (k + 1)) with
      | .leaf _ => 0
      | .node i j _ _ => pairIdx i.val j.val
    else 0
  have hf_lt : ∀ k < 2 ^ d - 1, f k < numPairs := by
    intro k hk
    dsimp only [f]
    simp only [hk, ↓reduceDIte]
    have hlen_lt := length_pathFromRoot_lt (k := k + 1) (d := d) (by omega) (by omega)
    have hsub := subtreeAtPath_isComplete (k := (pathFromRoot (k + 1)).length)
      (d := d - (pathFromRoot (k + 1)).length)
      (by rw [Nat.add_sub_cancel' hlen_lt.le]; exact hcomp)
      (pathFromRoot (k + 1)) rfl
    cases hst : subtreeAtPath T (pathFromRoot (k + 1)) with
    | leaf _ => exact hnp_pos
    | node i j _ _ =>
      rw [hst] at hsub
      rcases hdp : d - (pathFromRoot (k + 1)).length with _ | d'
      · omega
      · rw [hdp] at hsub
        obtain ⟨hij, _, _⟩ := msfTree_isComplete_node.mp hsub
        exact pairIdx_lt_choose_two hij j.isLt
  let skelCode := ∑ k ∈ Finset.range (2 ^ d - 1), f k * numPairs ^ k
  have hcode_lt : skelCode < numPairs ^ (2 ^ d - 1) :=
    baseB_sum_lt numPairs (2 ^ d - 1) f hf_lt
  have hwalk_eval : ∀ rem node (p : Equiv.Perm (Fin e)),
      1 ≤ node → (pathFromRoot node).length + rem = d →
      ∃ ans, subtreeAtPath T (pathFromRoot (walkSkelNode e he skelCode rem node p)) = .leaf ans ∧
        ans = (subtreeAtPath T (pathFromRoot node)).eval p := by
    intro rem
    induction rem with
    | zero =>
      intro node p h1 hsum
      rw [Nat.add_zero] at hsum
      have hsub := subtreeAtPath_isComplete (k := (pathFromRoot node).length) (d := 0)
        (by rwa [hsum, Nat.add_zero]) (pathFromRoot node) rfl
      cases heq : subtreeAtPath T (pathFromRoot node) with
      | node _ _ _ _ => rw [heq] at hsub; exact absurd hsub msfTree_isComplete_zero_node
      | leaf ans => exact ⟨ans, heq, rfl⟩
    | succ rem ih =>
      intro node p h1 hsum
      have hlen : (pathFromRoot node).length < d := by omega
      have hnode_lt : node < 2 ^ d :=
        (lt_two_pow_of_length_pathFromRoot node h1).trans_le
          (Nat.pow_le_pow_right (by decide) (by omega))
      have hsub := subtreeAtPath_isComplete (k := (pathFromRoot node).length) (d := rem + 1)
        (hsum ▸ hcomp) (pathFromRoot node) rfl
      cases heq : subtreeAtPath T (pathFromRoot node) with
      | leaf _ => rw [heq] at hsub; exact absurd hsub msfTree_isComplete_succ_leaf
      | node i j l r =>
        rw [heq] at hsub
        obtain ⟨hij, _, _⟩ := msfTree_isComplete_node.mp hsub
        have hdec : (skelCode / numPairs ^ (node - 1)) % numPairs = f (node - 1) :=
          baseB_digit_decode numPairs (2 ^ d - 1) f hf_lt (node - 1) (by omega)
        have hf_eq : f (node - 1) = pairIdx i.val j.val := by
          have hkb : node - 1 < 2 ^ d - 1 := by omega
          dsimp only [f]
          simp only [hkb, show node - 1 + 1 = node by omega, ↓reduceDIte, heq]
        have hpk_lt : (skelCode / numPairs ^ (node - 1)) % numPairs < (allPairs e).length := by
          rw [length_allPairs]
          exact Nat.mod_lt _ hnp_pos
        have hpr : (allPairs e)[(skelCode / numPairs ^ (node - 1)) % numPairs]'hpk_lt =
            (i, j) := by
          simpa only [hdec, hf_eq] using getElem_allPairs_pairIdx hij
        dsimp only [walkSkelNode]
        split_ifs with hpk_lt' hlt
        · dsimp only [numPairs] at hpr; rw [hpr] at hlt
          have hsum' : (pathFromRoot (2 * node)).length + rem = d := by
            rw [pathFromRoot_two_mul h1, List.length_append, List.length_singleton]; omega
          obtain ⟨ans, hl, ha⟩ := ih (2 * node) p (by omega) hsum'
          rw [pathFromRoot_two_mul h1, subtreeAtPath_append, heq] at ha
          dsimp only [subtreeAtPath] at ha
          simp only [Bool.false_eq_true, ↓reduceIte, subtreeAtPath_nil] at ha
          dsimp only [MSFTree.eval]
          simp only [hlt, ↓reduceIte]
          exact ⟨ans, hl, ha⟩
        · dsimp only [numPairs] at hpr; rw [hpr] at hlt
          have hsum' : (pathFromRoot (2 * node + 1)).length + rem = d := by
            rw [pathFromRoot_two_mul_add_one h1, List.length_append, List.length_singleton]; omega
          obtain ⟨ans, hl, ha⟩ := ih (2 * node + 1) p (by omega) hsum'
          rw [pathFromRoot_two_mul_add_one h1, subtreeAtPath_append, heq] at ha
          dsimp only [subtreeAtPath] at ha
          simp only [↓reduceIte, subtreeAtPath_nil] at ha
          dsimp only [MSFTree.eval]
          simp only [hlt, ↓reduceIte]
          exact ⟨ans, hl, ha⟩
        · exact absurd hpk_lt hpk_lt'
        · exact absurd hpk_lt hpk_lt'
  refine ⟨skelCode, hcode_lt, fun p q heq => ?_⟩
  obtain ⟨ansP, hlp, hap⟩ := hwalk_eval d 1 p le_rfl (by simp [pathFromRoot])
  obtain ⟨ansQ, hlq, haq⟩ := hwalk_eval d 1 q le_rfl (by simp [pathFromRoot])
  rw [← hcorr p, ← hcorr q]
  simp only [pathFromRoot, subtreeAtPath] at hap haq
  rw [← hap, ← haq]
  rw [← heq, hlp] at hlq
  cases hlq
  rfl

/-- Casted separating-skeleton existence lemma specialized to `maskEdgePairs r0 mask`. -/
theorem dtExistsGoodSkel {r0 mask e d : ℕ} (he2 : 2 ≤ e)
    (he_eq : e = (maskEdgePairs r0 mask).length) (hopt : optDepth (endsOfMask r0 mask) ≤ d) :
    ∃ skelCode < (e.choose 2) ^ (2 ^ d - 1),
      ∀ p q : Equiv.Perm (Fin e),
        walkSkelNode e he2 skelCode d 1 p = walkSkelNode e he2 skelCode d 1 q →
        let σ : Fin e ≃ Fin (maskEdgePairs r0 mask).length := (Fin.castOrderIso he_eq).toEquiv
        Cslib.Multigraph.msf (endsOfMask r0 mask) (σ.symm.trans (p.trans σ)) Finset.univ =
          Cslib.Multigraph.msf (endsOfMask r0 mask) (σ.symm.trans (q.trans σ)) Finset.univ := by
  subst e
  obtain ⟨sc, hsc_lt, hgood⟩ := exists_skelCode_of_complete_correct he2 (endsOfMask r0 mask) hopt
  refine ⟨sc, hsc_lt, fun p q hwalk => ?_⟩
  have hid : ∀ r : Equiv.Perm (Fin (maskEdgePairs r0 mask).length),
      ((Fin.castOrderIso rfl).toEquiv.symm.trans (Equiv.trans r (Fin.castOrderIso rfl).toEquiv)) =
        r := fun r => by ext x; rfl
  dsimp only
  rw [hid p, hid q]
  exact hgood p q hwalk

/-- Casted `HoldsCompleteTree` and `MSFDT.IsComplete` helper along `Equiv.Perm`/`Fin` cast. -/
theorem dtHoldsCompleteTreeCast {e₁ e₂ d intBase leafBase : ℕ} {mem : ℕ → ℕ}
    (heq : e₁ = e₂) (T : MSFDT e₁) (hcomp : T.IsComplete d)
    (hhold : HoldsCompleteTree d intBase leafBase d 1 mem T) :
    let σ : Fin e₁ ≃ Fin e₂ := (Fin.castOrderIso heq).toEquiv
    let T' := (T.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ
    T'.IsComplete d ∧ HoldsCompleteTree d intBase leafBase d 1 mem T' := by
  subst e₁
  have hid : (Fin.castOrderIso rfl).toEquiv = Equiv.refl (Fin e₂) := by ext x; rfl
  have hmap : ∀ {α : Type} (f : α → α) (hf : ∀ x, f x = x) (t : MSFTree e₂ α),
      t.mapLeaves f = t := fun f hf t => by
    induction t with
    | leaf a => simp [MSFTree.mapLeaves, hf a]
    | node i j l r ihl ihr => simp [MSFTree.mapLeaves, ihl, ihr]
  have hlift : ∀ {α : Type} (g : Fin e₂ → Fin e₂) (hg : ∀ x, g x = x) (t : MSFTree e₂ α),
      t.liftEmb g = t := fun g hg t => by
    induction t with
    | leaf _ => rfl
    | node i j l r ihl ihr => simp [MSFTree.liftEmb, hg i, hg j, ihl, ihr]
  dsimp only
  rw [hid, hmap _ (fun s => by ext x; simp), hlift (⇑(Equiv.refl (Fin e₂))) (fun _ => rfl)]
  exact ⟨hcomp, hhold⟩

private theorem pow_two_pow_add_le {a b m : ℕ}
    (ha : a ≤ 2 ^ (2 ^ m)) (hb : b ≤ 2 ^ (2 ^ m)) :
    a + b ≤ 2 ^ (2 ^ (m + 1)) := by
  calc a + b ≤ 2 ^ (2 ^ m) + 2 ^ (2 ^ m) := Nat.add_le_add ha hb
    _ = 2 ^ (2 ^ m + 1) := by rw [Nat.pow_succ']; ring
    _ ≤ 2 ^ (2 ^ (m + 1)) := by
      refine Nat.pow_le_pow_right (by decide) ?_
      have h1 : 1 ≤ 2 ^ m := Nat.two_pow_pos m
      rw [Nat.pow_succ']
      omega

private theorem pow_two_pow_mul_le {a b m : ℕ}
    (ha : a ≤ 2 ^ (2 ^ m)) (hb : b ≤ 2 ^ (2 ^ m)) :
    a * b ≤ 2 ^ (2 ^ (m + 1)) := by
  calc a * b ≤ 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := Nat.mul_le_mul ha hb
    _ = 2 ^ (2 ^ m + 2 ^ m) := (Nat.pow_add 2 (2 ^ m) (2 ^ m)).symm
    _ = 2 ^ (2 ^ (m + 1)) := by rw [Nat.pow_succ', two_mul]

private theorem pow_two_pow_mono {x m₁ m₂ : ℕ}
    (hx : x ≤ 2 ^ (2 ^ m₁)) (hm : m₁ ≤ m₂) :
    x ≤ 2 ^ (2 ^ m₂) :=
  hx.trans (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide) hm))

private theorem choose_two_le_sq (r : ℕ) : r.choose 2 ≤ r ^ 2 := by
  rw [choose_two_eq_div]
  calc r * (r - 1) / 2 ≤ r * (r - 1) := Nat.div_le_self _ 2
    _ ≤ r * r := Nat.mul_le_mul_left r (Nat.sub_le r 1)
    _ = r ^ 2 := (sq r).symm

private theorem maxD_le_pow_four (r0 : ℕ) : (r0.choose 2).choose 2 ≤ r0 ^ 4 := by
  calc (r0.choose 2).choose 2 ≤ (r0.choose 2) ^ 2 := choose_two_le_sq _
    _ ≤ (r0 ^ 2) ^ 2 := Nat.pow_le_pow_left (choose_two_le_sq r0) 2
    _ = r0 ^ 4 := by ring

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := Nat.lt_two_pow_self.le

private theorem pow_self_le_two_pow_four {e r0 : ℕ} (he : e ≤ r0.choose 2) :
    e ^ e ≤ 2 ^ (r0 ^ 4) := by
  rcases Nat.eq_zero_or_pos r0 with rfl | hr
  · have he0 : e = 0 := by rw [Nat.choose_zero_succ] at he; omega
    subst he0; decide
  · have he2 : e ≤ r0 ^ 2 := he.trans (choose_two_le_sq r0)
    calc e ^ e ≤ (r0 ^ 2) ^ e := Nat.pow_le_pow_left he2 e
      _ ≤ (r0 ^ 2) ^ (r0 ^ 2) := Nat.pow_le_pow_right (Nat.pow_pos hr) he2
      _ ≤ (2 ^ (r0 ^ 2)) ^ (r0 ^ 2) := Nat.pow_le_pow_left (nat_le_two_pow _) _
      _ = 2 ^ (r0 ^ 2 * r0 ^ 2) := (Nat.pow_mul 2 _ _).symm
      _ = 2 ^ (r0 ^ 4) := by ring_nf

private theorem numSkels_le_two_pow_two_pow {e d r0 : ℕ}
    (he : e ≤ r0.choose 2) (hd : d ≤ (r0.choose 2).choose 2) :
    (e.choose 2) ^ (2 ^ d - 1) ≤ 2 ^ (2 ^ (2 * r0 ^ 4)) := by
  have hnp : e.choose 2 ≤ r0 ^ 4 := (Nat.choose_le_choose 2 he).trans (maxD_le_pow_four r0)
  have h2d : 2 ^ d - 1 ≤ 2 ^ (r0 ^ 4) :=
    (Nat.sub_le _ 1).trans (Nat.pow_le_pow_right (by decide) (hd.trans (maxD_le_pow_four r0)))
  calc (e.choose 2) ^ (2 ^ d - 1)
      ≤ (2 ^ (r0 ^ 4)) ^ (2 ^ d - 1) :=
        Nat.pow_le_pow_left (hnp.trans (nat_le_two_pow _)) _
    _ ≤ (2 ^ (r0 ^ 4)) ^ (2 ^ (r0 ^ 4)) :=
        Nat.pow_le_pow_right (Nat.two_pow_pos _) h2d
    _ = 2 ^ (r0 ^ 4 * 2 ^ (r0 ^ 4)) := (Nat.pow_mul 2 _ _).symm
    _ ≤ 2 ^ (2 ^ (r0 ^ 4) * 2 ^ (r0 ^ 4)) :=
        Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (nat_le_two_pow _))
    _ = 2 ^ (2 ^ (2 * r0 ^ 4)) := by rw [← Nat.pow_add, two_mul]

/-- Double-exponential containment lemma proving any tower below `2^(2^(2*r0^4 + 40))` fits inside
`dtPrecompCost r0` for `2 ≤ r0`. -/
theorem le_dtPrecompCost_of_exp_le {r0 k x : ℕ} (hr2 : 2 ≤ r0)
    (hk : k ≤ 2 * r0 ^ 4 + 40) (hx : x ≤ 2 ^ (2 ^ k)) :
    x ≤ dtPrecompCost r0 := by
  have hnot : ¬ r0 ≤ 1 := by omega
  dsimp only [dtPrecompCost]
  simp only [hnot, ↓reduceIte]
  have hr4 : 16 ≤ r0 ^ 4 := by
    have h2 : 4 ≤ r0 * r0 := Nat.mul_le_mul hr2 hr2
    calc 16 = 4 * 4 := rfl
      _ ≤ (r0 * r0) * (r0 * r0) := Nat.mul_le_mul h2 h2
      _ = r0 ^ 4 := by ring
  exact pow_two_pow_mono hx (by omega)

/-- Tower-of-two bounds showing per-mask space and time budgets for `precomputeDTProg` are
strictly dominated by `dtPrecompCost r0`. -/
theorem dtPrecompArithBounds {r0 e : ℕ} (hr2 : 2 ≤ r0) (he_le : e ≤ r0.choose 2) :
    let maxE := r0.choose 2
    let numMasks := 2 ^ maxE
    let maxD := maxE.choose 2
    let maxNumSkels := (e.choose 2) ^ (2 ^ maxD - 1)
    e ^ e + (2 + e + 2 * (2 ^ maxD - 1) + 2 ^ maxD) ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) ∧
    e ^ e + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 2)) ∧
    maxNumSkels + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 2)) ∧
    1 + 5 * maxE + 1 + 2 * e + (2 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) +
      e * (1 + 2 * e) + (maxD + 1) * (2 * 2 ^ maxD + 1 +
        maxNumSkels * (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD)))) ≤
      2 ^ (2 ^ (2 * r0 ^ 4 + 11)) ∧
    9 + 5 * maxE ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 11)) ∧
    numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) ∧
    numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1 +
      numMasks * 2 ^ (2 ^ (2 * r0 ^ 4 + 5)) ≤ dtPrecompCost r0 ∧
    16 + r0 * (1 + 2 * r0) + numMasks * 2 ^ (2 ^ (2 * r0 ^ 4 + 11)) ≤ dtPrecompCost r0 := by
  intro maxE numMasks maxD maxNumSkels
  let m0 := 2 * r0 ^ 4 + 1
  have hr4 : 16 ≤ r0 ^ 4 := by
    have h2 : 4 ≤ r0 * r0 := Nat.mul_le_mul hr2 hr2
    calc 16 = 4 * 4 := rfl
      _ ≤ (r0 * r0) * (r0 * r0) := Nat.mul_le_mul h2 h2
      _ = r0 ^ 4 := by ring
  have hm0_le : 2 ^ (r0 ^ 4) ≤ 2 ^ (2 ^ m0) :=
    Nat.pow_le_pow_right (by decide) ((nat_le_two_pow _).trans
      (Nat.pow_le_pow_right (by decide) (by dsimp only [m0]; omega)))
  have h16_le : 16 ≤ 2 ^ (2 ^ m0) := by
    calc (16 : ℕ) = 2 ^ 4 := rfl
      _ ≤ 2 ^ (2 ^ m0) := Nat.pow_le_pow_right (by decide)
          ((by dsimp only [m0]; omega : 4 ≤ m0).trans (nat_le_two_pow m0))
  have hr02_le4 : r0 ^ 2 ≤ r0 ^ 4 := by
    calc r0 ^ 2 = r0 ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ r0 ^ 2 * r0 ^ 2 := Nat.mul_le_mul_left _ (by nlinarith)
      _ = r0 ^ 4 := by ring
  have hr0_le4 : r0 ≤ r0 ^ 4 := (by nlinarith : r0 ≤ r0 ^ 2).trans hr02_le4
  have hr0_le : r0 ≤ 2 ^ (2 ^ m0) := (nat_le_two_pow r0).trans
    ((Nat.pow_le_pow_right (by decide) hr0_le4).trans hm0_le)
  have hmaxE_le : maxE ≤ 2 ^ (2 ^ m0) :=
    ((choose_two_le_sq r0).trans hr02_le4).trans ((nat_le_two_pow (r0 ^ 4)).trans hm0_le)
  have hnm_le : numMasks ≤ 2 ^ (2 ^ m0) := by
    calc numMasks = 2 ^ maxE := rfl
      _ ≤ 2 ^ (r0 ^ 2) := Nat.pow_le_pow_right (by decide) (choose_two_le_sq r0)
      _ ≤ 2 ^ (r0 ^ 4) := Nat.pow_le_pow_right (by decide) hr02_le4
      _ ≤ 2 ^ (2 ^ m0) := hm0_le
  have hmaxD_le : maxD ≤ 2 ^ (2 ^ m0) :=
    (maxD_le_pow_four r0).trans ((nat_le_two_pow _).trans hm0_le)
  have h2mD_le : 2 ^ maxD ≤ 2 ^ (2 ^ m0) :=
    (Nat.pow_le_pow_right (by decide) (maxD_le_pow_four r0)).trans hm0_le
  have he_le' : e ≤ 2 ^ (2 ^ m0) := he_le.trans hmaxE_le
  have hee_le : e ^ e ≤ 2 ^ (2 ^ m0) := (pow_self_le_two_pow_four he_le).trans hm0_le
  have hns_le : maxNumSkels ≤ 2 ^ (2 ^ m0) :=
    (numSkels_le_two_pow_two_pow he_le le_rfl).trans
      (Nat.pow_le_pow_right (by decide) (Nat.pow_le_pow_right (by decide)
        (by dsimp only [m0]; omega)))
  have h2_le : 2 ≤ 2 ^ (2 ^ m0) := (by decide : 2 ≤ 16).trans h16_le
  have h_one : 1 ≤ 2 ^ (2 ^ m0) := (by decide : 1 ≤ 16).trans h16_le
  have h_4 : 4 ≤ 2 ^ (2 ^ m0) := (by decide : 4 ≤ 16).trans h16_le
  have h_5 : 5 ≤ 2 ^ (2 ^ m0) := (by decide : 5 ≤ 16).trans h16_le
  have h_7 : 7 ≤ 2 ^ (2 ^ m0) := (by decide : 7 ≤ 16).trans h16_le
  have h_9 : 9 ≤ 2 ^ (2 ^ m0) := (by decide : 9 ≤ 16).trans h16_le
  have hee1 : e ^ e + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 2)) :=
    pow_two_pow_add_le hee_le h_one
  have hns1 : maxNumSkels + 1 ≤ 2 ^ (2 ^ (2 * r0 ^ 4 + 2)) :=
    pow_two_pow_add_le hns_le h_one
  have hfr_d : e ^ e + (2 + e + 2 * (2 ^ maxD - 1) + 2 ^ maxD) ≤ 2 ^ (2 ^ (m0 + 4)) := by
    have h2e : 2 + e ≤ 2 ^ (2 ^ (m0 + 1)) := pow_two_pow_add_le h2_le he_le'
    have h2d : 2 * (2 ^ maxD - 1) ≤ 2 ^ (2 ^ (m0 + 1)) :=
      (Nat.mul_le_mul_left 2 (Nat.sub_le _ 1)).trans (pow_two_pow_mul_le h2_le h2mD_le)
    have h3 : 2 + e + 2 * (2 ^ maxD - 1) ≤ 2 ^ (2 ^ (m0 + 2)) := pow_two_pow_add_le h2e h2d
    have h4 : 2 + e + 2 * (2 ^ maxD - 1) + 2 ^ maxD ≤ 2 ^ (2 ^ (m0 + 3)) :=
      pow_two_pow_add_le h3 (pow_two_pow_mono h2mD_le (by omega))
    exact pow_two_pow_add_le (pow_two_pow_mono hee_le (by omega)) h4
  have h_all : numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1 ≤
      2 ^ (2 ^ (m0 + 4)) := by
    have ha1 : numMasks + 9 * maxE ≤ 2 ^ (2 ^ (m0 + 2)) :=
      pow_two_pow_add_le (pow_two_pow_mono hnm_le (by omega)) (pow_two_pow_mul_le h_9 hmaxE_le)
    have ha2 : 2 * maxD + 3 * 2 ^ maxD ≤ 2 ^ (2 ^ (m0 + 2)) :=
      pow_two_pow_add_le (pow_two_pow_mul_le h2_le hmaxD_le)
        (pow_two_pow_mul_le ((by decide : 3 ≤ 16).trans h16_le) h2mD_le)
    have ha3 : numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD ≤ 2 ^ (2 ^ (m0 + 3)) :=
      (by omega : numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD ≤
        (numMasks + 9 * maxE) + (2 * maxD + 3 * 2 ^ maxD)).trans (pow_two_pow_add_le ha1 ha2)
    have ha4 : r0 + 1 ≤ 2 ^ (2 ^ (m0 + 3)) :=
      pow_two_pow_mono (pow_two_pow_add_le hr0_le h_one) (by omega)
    exact (by omega : numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1 ≤
      (numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD) + (r0 + 1)).trans
      (pow_two_pow_add_le ha3 ha4)
  have h_step : 1 + 5 * maxE + 1 + 2 * e +
      (2 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) + e * (1 + 2 * e) +
        (maxD + 1) * (2 * 2 ^ maxD + 1 +
          maxNumSkels * (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD)))) ≤
      2 ^ (2 ^ (m0 + 10)) := by
    have hc_1 : 1 + 5 * maxE + 1 + 2 * e ≤ 2 ^ (2 ^ (m0 + 3)) := by
      have s1 : 1 + 5 * maxE ≤ 2 ^ (2 ^ (m0 + 2)) :=
        pow_two_pow_add_le (pow_two_pow_mono h_one (by omega)) (pow_two_pow_mul_le h_5 hmaxE_le)
      have s2 : 1 + 2 * e ≤ 2 ^ (2 ^ (m0 + 2)) :=
        pow_two_pow_add_le (pow_two_pow_mono h_one (by omega)) (pow_two_pow_mul_le h2_le he_le')
      exact (by omega : 1 + 5 * maxE + 1 + 2 * e ≤ (1 + 5 * maxE) + (1 + 2 * e)).trans
        (pow_two_pow_add_le s1 s2)
    have hc_pa : 2 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) + e * (1 + 2 * e) ≤
        2 ^ (2 ^ (m0 + 7)) := by
      have p1 : 5 + 2 * r0 ≤ 2 ^ (2 ^ (m0 + 2)) :=
        pow_two_pow_add_le (pow_two_pow_mono h_5 (by omega)) (pow_two_pow_mul_le h2_le hr0_le)
      have p2 : e * (5 + 2 * r0) ≤ 2 ^ (2 ^ (m0 + 3)) :=
        pow_two_pow_mul_le (pow_two_pow_mono he_le' (by omega)) p1
      have p3 : 2 + 7 * e + r0 ≤ 2 ^ (2 ^ (m0 + 3)) :=
        pow_two_pow_add_le (pow_two_pow_add_le (pow_two_pow_mono h2_le (by omega))
          (pow_two_pow_mul_le h_7 he_le')) (pow_two_pow_mono hr0_le (by omega))
      have p4 : 2 + 7 * e + r0 + e * (5 + 2 * r0) ≤ 2 ^ (2 ^ (m0 + 4)) :=
        pow_two_pow_add_le p3 p2
      have p5 : 2 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) ≤ 2 ^ (2 ^ (m0 + 6)) :=
        pow_two_pow_add_le (pow_two_pow_mono h2_le (by omega))
          (pow_two_pow_mul_le (pow_two_pow_mono hee_le (by omega)) p4)
      have p6 : e * (1 + 2 * e) ≤ 2 ^ (2 ^ (m0 + 6)) :=
        pow_two_pow_mono (pow_two_pow_mul_le (pow_two_pow_mono he_le' (by omega))
          (pow_two_pow_add_le (pow_two_pow_mono h_one (by omega))
            (pow_two_pow_mul_le h2_le he_le'))) (by omega)
      exact pow_two_pow_add_le p5 p6
    have hc_try : (maxD + 1) * (2 * 2 ^ maxD + 1 +
        maxNumSkels * (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD))) ≤
        2 ^ (2 ^ (m0 + 8)) := by
      have t1 : 4 + 5 * maxD ≤ 2 ^ (2 ^ (m0 + 2)) :=
        pow_two_pow_add_le (pow_two_pow_mono h_4 (by omega)) (pow_two_pow_mul_le h_5 hmaxD_le)
      have t2 : e ^ e * (4 + 5 * maxD) ≤ 2 ^ (2 ^ (m0 + 3)) :=
        pow_two_pow_mul_le (pow_two_pow_mono hee_le (by omega)) t1
      have t3 : 5 + 2 * e + 9 * 2 ^ maxD ≤ 2 ^ (2 ^ (m0 + 3)) :=
        pow_two_pow_add_le (pow_two_pow_add_le (pow_two_pow_mono h_5 (by omega))
          (pow_two_pow_mul_le h2_le he_le'))
          (pow_two_pow_mono (pow_two_pow_mul_le h_9 h2mD_le) (by omega))
      have t4 : 5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD) ≤ 2 ^ (2 ^ (m0 + 4)) :=
        pow_two_pow_add_le t3 t2
      have t5 : maxNumSkels * (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD)) ≤
          2 ^ (2 ^ (m0 + 5)) :=
        pow_two_pow_mul_le (pow_two_pow_mono hns_le (by omega)) t4
      have t6 : 2 * 2 ^ maxD + 1 ≤ 2 ^ (2 ^ (m0 + 5)) :=
        pow_two_pow_mono (pow_two_pow_add_le (pow_two_pow_mul_le h2_le h2mD_le)
          (pow_two_pow_mono h_one (by omega))) (by omega)
      have t7 : 2 * 2 ^ maxD + 1 +
          maxNumSkels * (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD)) ≤
          2 ^ (2 ^ (m0 + 6)) := pow_two_pow_add_le t6 t5
      have t8 : maxD + 1 ≤ 2 ^ (2 ^ (m0 + 6)) :=
        pow_two_pow_mono (pow_two_pow_add_le hmaxD_le h_one) (by omega)
      exact pow_two_pow_mono (pow_two_pow_mul_le t8 t7) (by omega)
    have hc_body : 2 + e ^ e * (2 + 7 * e + r0 + e * (5 + 2 * r0)) + e * (1 + 2 * e) +
        (maxD + 1) * (2 * 2 ^ maxD + 1 +
          maxNumSkels * (5 + 2 * e + 9 * 2 ^ maxD + e ^ e * (4 + 5 * maxD))) ≤
        2 ^ (2 ^ (m0 + 9)) :=
      pow_two_pow_add_le (pow_two_pow_mono hc_pa (by omega)) (pow_two_pow_mono hc_try (by omega))
    exact pow_two_pow_add_le (pow_two_pow_mono hc_1 (by omega)) hc_body
  have h_triv : 9 + 5 * maxE ≤ 2 ^ (2 ^ (m0 + 10)) :=
    pow_two_pow_mono (pow_two_pow_add_le (pow_two_pow_mono h_9 (by omega))
      (pow_two_pow_mul_le h_5 hmaxE_le)) (by omega)
  have h_tot_fr : numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1 +
      numMasks * 2 ^ (2 ^ (m0 + 4)) ≤ dtPrecompCost r0 := by
    have hmul : numMasks * 2 ^ (2 ^ (m0 + 4)) ≤ 2 ^ (2 ^ (m0 + 5)) :=
      pow_two_pow_mul_le (pow_two_pow_mono hnm_le (by omega)) le_rfl
    have hsum : numMasks + 9 * maxE + 2 * maxD + 3 * 2 ^ maxD + r0 + 1 +
        numMasks * 2 ^ (2 ^ (m0 + 4)) ≤ 2 ^ (2 ^ (m0 + 6)) :=
      pow_two_pow_add_le (pow_two_pow_mono h_all (by omega)) hmul
    exact le_dtPrecompCost_of_exp_le hr2 (by dsimp only [m0]; omega) hsum
  have h_tot_cost : 16 + r0 * (1 + 2 * r0) + numMasks * 2 ^ (2 ^ (m0 + 10)) ≤
      dtPrecompCost r0 := by
    have hpre : 16 + r0 * (1 + 2 * r0) ≤ 2 ^ (2 ^ (m0 + 11)) := by
      have hp1 : 1 + 2 * r0 ≤ 2 ^ (2 ^ (m0 + 2)) :=
        pow_two_pow_add_le (pow_two_pow_mono h_one (by omega)) (pow_two_pow_mul_le h2_le hr0_le)
      have hp2 : r0 * (1 + 2 * r0) ≤ 2 ^ (2 ^ (m0 + 3)) :=
        pow_two_pow_mul_le (pow_two_pow_mono hr0_le (by omega)) hp1
      exact pow_two_pow_mono (pow_two_pow_add_le (pow_two_pow_mono h16_le (by omega)) hp2)
        (by omega)
    have hmul : numMasks * 2 ^ (2 ^ (m0 + 10)) ≤ 2 ^ (2 ^ (m0 + 11)) :=
      pow_two_pow_mul_le (pow_two_pow_mono hnm_le (by omega)) le_rfl
    exact le_dtPrecompCost_of_exp_le hr2 (by dsimp only [m0]; omega) (pow_two_pow_add_le hpre hmul)
  exact ⟨hfr_d, hee1, hns1, h_step, h_triv, h_all, h_tot_fr, h_tot_cost⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest

end
