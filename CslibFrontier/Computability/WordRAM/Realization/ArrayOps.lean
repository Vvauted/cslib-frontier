/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
public import CslibFrontier.Computability.WordRAM.Realization.Structure
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Reusable verified Word-RAM array primitives over `Memory.Prog`

This module provides four reusable verified array primitives (plus a dirty-allocation zero-cost
variant under `Memory.ZeroAbove`), each equipped with:

1. a concrete executable `Memory.Prog` implementation,
2. a uniform `Realizes .exact` certificate with `work := 0`, and
3. a `FramedTriple` / `SameFrontierTriple` specification with `iterationSafe` and `WellFormed`
   preservation.

## Main definitions

* `fillConstStep`, `fillConstProg`: fill `[base, base + count)` with a constant `val`.
* `copySliceProg`: non-overlapping slice copy `[src, src + count)` to
  `[dst, dst + count)`.
* `prefixSumStep`, `prefixSumProg`: in-place exclusive prefix sum over `[base, base + count)`
  storing `[0, a₀, a₀ + a₁, ...]` and returning the total sum.
* `allocZeroBlockProg`: allocate a zeroed `Block` of size `size` at cost `size + 1`.
* `allocZeroBlockDirtyProg`: allocate a zeroed `Block` of size `size` at cost `1` when
  `Memory.ZeroAbove s` holds.
-/

public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

/-! ## Constant fill (`fillConstProg`) -/

/-- Single step of filling a contiguous slice: write `val` at `base + idx` and increment
the index `idx`. -/
@[expose] def fillConstStep : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((base, val), idx) => do
    Memory.write (base + idx) val
    pure (idx + 1)

/-- Native safety domain for `fillConstStep`. -/
@[expose] def fillConstStepSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (_ : Memory.State) : Prop :=
  Fits w (d.2 + 1)

private theorem realizes_fillConstStep_history : Realizes .exact
    fillConstStep WordEncoding.encode WordEncoding.encode
    (fun w d s => fillConstStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillConstStep d)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : (ℕ × ℕ) × ℕ => do
        Memory.write (d.1.1 + d.2) d.1.2
        pure (d.2 + 1))
      WordEncoding.encode WordEncoding.encode
      (fun w d s => fillConstStepSafe w d s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillConstStep d)))
      (fun _ _ => 0) := by
    realize
    all_goals
      rcases d with ⟨⟨_, _⟩, _⟩
      obtain ⟨hfit, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory, fillConstStep] at hv
      simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.stepFn, Memory.write, Memory.step_write, Memory.valid] at hv
      dsimp only
      fits
  exact hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)

/-- Uniform `Realizes .exact` certificate for `fillConstStep` with `work = 0`. -/
theorem realizes_fillConstStep :
    Realizes .exact fillConstStep WordEncoding.encode WordEncoding.encode fillConstStepSafe
      (fun _ _ => 0) :=
  realizes_fillConstStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Fill `count` consecutive cells `[base, base + count)` with `val`. -/
@[expose] def fillConstProg (base val count : ℕ) : Memory.Prog Unit := do
  let _ ← iterate fillConstStep (base, val) count 0
  pure ()

/-- Specification for `fillConstProg`: fills `[base, base + count)` with `val`, preserves
frontier and all cells outside `[base, base + count)`, costs at most `count`, and satisfies
`iterationSafe` and `WellFormed`. -/
theorem fillConstProg_spec {w base val count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hval : Fits w val) (hcount : Fits w count)
    (hbound : base + count ≤ s.frontier) :
    iterationSafe fillConstStep fillConstStepSafe w (base, val) count 0 s ∧
    Memory.SameFrontierTriple w s (fillConstProg base val count) count
      (Set.Ico base (base + count)) fun _ s' =>
        Memory.WellFormed w s' ∧ ∀ j < count, s'.mem (base + j) = val := by
  let S : Set ℕ := Set.Ico base (base + count)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    ∀ j < k, t.mem (base + j) = val
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      fillConstStepSafe w ((base, val), a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (fillConstStep ((base, val), a))) ∧
      let a' := (Memory.spec 0).clientResult t (fillConstStep ((base, val), a))
      let t' := (Memory.spec 0).clientState t (fillConstStep ((base, val), a))
      memoryCost (fillConstStep ((base, val), a)) t + 0 ≤ 0 + 1 ∧
      Memory.SameFrontierModifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hfill⟩
    subst a
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (fillConstStep ((base, val), k))) := by
      dsimp only [fillConstStep]
      exact validHistory_write_bind (by rw [htfr]; omega) hval (validHistory_pure w _ _)
    have hcost : memoryCost (fillConstStep ((base, val), k)) t ≤ 1 := by
      dsimp only [fillConstStep]
      simp only [memoryCost_bind', memoryCost_write, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult t (fillConstStep ((base, val), k)) = k + 1 := by
      dsimp only [fillConstStep]
      simp only [clientResult_bind_write, StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (fillConstStep ((base, val), k)) =
        ⟨Function.update t.mem (base + k) val, t.frontier⟩ := rfl
    have hmod : Memory.SameFrontierModifies S t
        ⟨Function.update t.mem (base + k) val, t.frontier⟩ :=
      (Memory.SameFrontierModifies.write t (base + k) val).mono fun x hx => by
        have heq : x = base + k := hx
        subst heq
        exact ⟨Nat.le_add_right _ _, by omega⟩
    refine ⟨hcount.of_le (by omega), hvh, by omega, by rw [hst]; exact hmod,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh, fun j hj => ?_⟩
    rw [hst]
    dsimp only
    by_cases hjk : j = k
    · rw [hjk, Function.update_self]
    · rw [Function.update_of_ne (by omega)]
      exact hfill j (by omega)
  obtain ⟨hsafe, hv, hcost, hmod, _, _, hwf', hvals⟩ :=
    iterate_potential_sameFrontier_spec fillConstStep fillConstStepSafe w (base, val) 1 count
      inv (fun _ _ _ => 0) S hstep 0 s ⟨rfl, rfl, hwf, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have hloop : Memory.SameFrontierTriple w s (iterate fillConstStep (base, val) count 0) count S
      fun _ s' => Memory.WellFormed w s' ∧ ∀ j < count, s'.mem (base + j) = val :=
    sameFrontierTriple_iff_realization.mpr ⟨hv, by simpa using hcost, hmod, hwf', hvals⟩
  have hres : Memory.SameFrontierTriple w s (fillConstProg base val count) count S
      fun _ s' => Memory.WellFormed w s' ∧ ∀ j < count, s'.mem (base + j) = val :=
    ((hloop.mono le_rfl fun _ _ h =>
      Memory.SameFrontierTriple.pure (c := 0) (a := ()) h).bind_same).mono
      (Nat.add_zero count).le fun _ _ h => h
  exact ⟨hsafe, hres⟩

/-- General `FramedTriple` wrapper for `fillConstProg`. -/
theorem fillConstProg_framedTriple {w base val count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hval : Fits w val) (hcount : Fits w count)
    (hbound : base + count ≤ s.frontier) :
    Memory.FramedTriple w s (fillConstProg base val count) count (Set.Ico base (base + count))
      fun _ s' => s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = val :=
  Memory.Triple.mono (fillConstProg_spec hwf hval hcount hbound).2 le_rfl
    fun _ _ ⟨hm, hwf', hvals⟩ => ⟨Memory.Modifies.of_sameFrontier hm, hm.1, hwf', hvals⟩

/-- Uniform `Realizes .exact` certificate for `fillConstProg` with `work = 0`. -/
theorem realizes_fillConstProg :
    Realizes .exact (fun ((base, val), count) => fillConstProg base val count)
      WordEncoding.encode WordEncoding.encode
      (fun _ ((base, _), count) s => base + count ≤ s.frontier) (fun _ _ => 0) := by
  have hraw : Realizes .exact (fun d : (ℕ × ℕ) × ℕ => fillConstProg d.1.1 d.1.2 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe (fun x : ((ℕ × ℕ) × ℕ) × ℕ =>
          fillConstStep ((x.1.1.1, x.1.1.2), x.2))
        (fun w d s => fillConstStepSafe w ((d.1.1.1, d.1.1.2), d.2) s) w d d.2 0 s)
      (fun _ _ => 0) := by
    unfold fillConstProg
    realize [realizes_fillConstStep]
    exact h
  refine (hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)).consequence (fun w d s hwords hmem hbound => ?_)
    (fun _ _ => le_rfl)
  rcases d with ⟨⟨base, val⟩, count⟩
  have hval : Fits w val := hwords 1
  have hcnt : Fits w count := hwords 2
  exact iterationSafe_map (fun x : (ℕ × ℕ) × ℕ => (x.1.1, x.1.2)) fillConstStep
    fillConstStepSafe _ (fun _ _ _ hs => hs)
    (fillConstProg_spec hmem hval hcnt hbound).1

/-! ## Non-overlapping slice copy (`copySliceProg`) -/

/-- Single step of copying `[src, src + count)` to `[dst, dst + count)` at index `idx`. -/
private def copySliceStep : (ℕ × ℕ) × ℕ → Memory.Prog ℕ
  | ((src, dst), idx) => do
    let v ← Memory.read (src + idx)
    Memory.write (dst + idx) v
    pure (idx + 1)

private def copySliceStepSafe (w : ℕ) (d : (ℕ × ℕ) × ℕ) (_ : Memory.State) : Prop :=
  Fits w (d.2 + 1)

private theorem realizes_copySliceStep_history : Realizes .exact
    copySliceStep WordEncoding.encode WordEncoding.encode
    (fun w d s => copySliceStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copySliceStep d)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : (ℕ × ℕ) × ℕ => do
        let v ← Memory.read (d.1.1 + d.2)
        Memory.write (d.1.2 + d.2) v
        pure (d.2 + 1))
      WordEncoding.encode WordEncoding.encode
      (fun w d s => copySliceStepSafe w d s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copySliceStep d)))
      (fun _ _ => 0) := by
    realize
    all_goals
      rcases d with ⟨⟨_, _⟩, _⟩
      obtain ⟨hfit, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory, copySliceStep] at hv
      simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
        Memory.valid] at hv
      dsimp only
      fits
  exact hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)

private theorem realizes_copySliceStep :
    Realizes .exact copySliceStep WordEncoding.encode WordEncoding.encode copySliceStepSafe
      (fun _ _ => 0) :=
  realizes_copySliceStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Copy `count` words from `[src, src + count)` to `[dst, dst + count)`. -/
def copySliceProg (src dst count : ℕ) : Memory.Prog Unit := do
  let _ ← iterate copySliceStep (src, dst) count 0
  pure ()

private theorem copySlice_iterationSafe {w src dst count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count)
    (hsrc : src + count ≤ s.frontier) (hdst : dst + count ≤ s.frontier) :
    iterationSafe copySliceStep copySliceStepSafe w (src, dst) count 0 s := by
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t
  refine (iterate_potential_sameFrontier_spec copySliceStep copySliceStepSafe w (src, dst) 2
    count inv (fun _ _ _ => 0) Set.univ (fun k hk a t ⟨ha, htfr, hwt⟩ => by
      subst a
      have hvh : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (copySliceStep ((src, dst), k))) := by
        dsimp only [copySliceStep]
        exact validHistory_read_bind (by rw [htfr]; omega)
          (validHistory_write_bind (by rw [htfr]; omega) (hwt.mem_fits _)
            (validHistory_pure w _ _))
      have hcost : memoryCost (copySliceStep ((src, dst), k)) t ≤ 2 := by
        dsimp only [copySliceStep]
        simp only [memoryCost_bind', memoryCost_read, memoryCost_write, memoryCost_pure]
        decide
      have hres : (Memory.spec 0).clientResult t (copySliceStep ((src, dst), k)) = k + 1 := by
        dsimp only [copySliceStep]
        simp only [clientResult_bind_read, clientResult_bind_write,
          StateTransitionSpec.clientResult_pure]
      have hst : (Memory.spec 0).clientState t (copySliceStep ((src, dst), k)) =
          ⟨Function.update t.mem (dst + k) (t.mem (src + k)), t.frontier⟩ := rfl
      refine ⟨hcnt.of_le (by omega), hvh, by omega,
        ⟨by rw [hst], fun _ hx => absurd (Set.mem_univ _) hx⟩,
        hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh⟩)
    0 s ⟨rfl, rfl, hwf⟩).1

/-- Specification for `copySliceProg`: for non-overlapping `[src, src + count)` and
`[dst, dst + count)`, copies `s.mem (src + j)` to `s'.mem (dst + j)`, modifies at most
`Set.Ico dst (dst + count)` with fixed frontier, costs at most `2 * count`, and preserves
`WellFormed`. -/
theorem copySliceProg_spec {w src dst count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count)
    (hdisj : src + count ≤ dst ∨ dst + count ≤ src)
    (hsrc : src + count ≤ s.frontier) (hdst : dst + count ≤ s.frontier) :
    Memory.SameFrontierTriple w s (copySliceProg src dst count) (2 * count)
      (Set.Ico dst (dst + count)) fun _ s' =>
        Memory.WellFormed w s' ∧ ∀ j < count, s'.mem (dst + j) = s.mem (src + j) := by
  let S : Set ℕ := Set.Ico dst (dst + count)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ j < k, t.mem (dst + j) = s.mem (src + j)) ∧
    (∀ i, k ≤ i → i < count → t.mem (src + i) = s.mem (src + i))
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      copySliceStepSafe w ((src, dst), a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (copySliceStep ((src, dst), a))) ∧
      let a' := (Memory.spec 0).clientResult t (copySliceStep ((src, dst), a))
      let t' := (Memory.spec 0).clientState t (copySliceStep ((src, dst), a))
      memoryCost (copySliceStep ((src, dst), a)) t + 0 ≤ 0 + 2 ∧
      Memory.SameFrontierModifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hcopied, hsrcRest⟩
    subst a
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (copySliceStep ((src, dst), k))) := by
      dsimp only [copySliceStep]
      exact validHistory_read_bind (by rw [htfr]; omega)
        (validHistory_write_bind (by rw [htfr]; omega) (hwt.mem_fits _)
          (validHistory_pure w _ _))
    have hcost : memoryCost (copySliceStep ((src, dst), k)) t ≤ 2 := by
      dsimp only [copySliceStep]
      simp only [memoryCost_bind', memoryCost_read, memoryCost_write, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult t (copySliceStep ((src, dst), k)) = k + 1 := by
      dsimp only [copySliceStep]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (copySliceStep ((src, dst), k)) =
        ⟨Function.update t.mem (dst + k) (t.mem (src + k)), t.frontier⟩ := rfl
    have hmod : Memory.SameFrontierModifies S t
        ⟨Function.update t.mem (dst + k) (t.mem (src + k)), t.frontier⟩ :=
      (Memory.SameFrontierModifies.write t (dst + k) (t.mem (src + k))).mono fun x hx => by
        have heq : x = dst + k := hx
        subst heq
        exact ⟨Nat.le_add_right _ _, by omega⟩
    refine ⟨hcnt.of_le (by omega), hvh, by omega, by rw [hst]; exact hmod,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh, fun j hj => ?_,
      fun i hik hic => ?_⟩
    · rw [hst]
      dsimp only
      by_cases hjk : j = k
      · rw [hjk, Function.update_self, hsrcRest k (le_refl k) hk]
      · rw [Function.update_of_ne (by omega)]
        exact hcopied j (by omega)
    · rw [hst]
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hsrcRest i (by omega) hic
  obtain ⟨hsafe, hv, hcost, hmod, _, _, hwf', hcopied, _⟩ :=
    iterate_potential_sameFrontier_spec copySliceStep copySliceStepSafe w (src, dst) 2 count
      inv (fun _ _ _ => 0) S hstep 0 s ⟨rfl, rfl, hwf, fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ _ => rfl⟩
  have hloop : Memory.SameFrontierTriple w s (iterate copySliceStep (src, dst) count 0)
      (2 * count) S fun _ s' =>
        Memory.WellFormed w s' ∧ ∀ j < count, s'.mem (dst + j) = s.mem (src + j) :=
    sameFrontierTriple_iff_realization.mpr ⟨hv, by simpa using hcost, hmod, hwf', hcopied⟩
  have hres : Memory.SameFrontierTriple w s (copySliceProg src dst count) (2 * count) S
      fun _ s' => Memory.WellFormed w s' ∧ ∀ j < count, s'.mem (dst + j) = s.mem (src + j) :=
    ((hloop.mono le_rfl fun _ _ h =>
      Memory.SameFrontierTriple.pure (c := 0) (a := ()) h).bind_same).mono
      (Nat.add_zero _).le fun _ _ h => h
  exact hres

/-- General `FramedTriple` wrapper for `copySliceProg`. -/
theorem copySliceProg_framedTriple {w src dst count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count)
    (hdisj : src + count ≤ dst ∨ dst + count ≤ src)
    (hsrc : src + count ≤ s.frontier) (hdst : dst + count ≤ s.frontier) :
    Memory.FramedTriple w s (copySliceProg src dst count) (2 * count)
      (Set.Ico dst (dst + count)) fun _ s' =>
        s'.frontier = s.frontier ∧ Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (dst + j) = s.mem (src + j) :=
  Memory.Triple.mono (copySliceProg_spec hwf hcnt hdisj hsrc hdst) le_rfl
    fun _ _ ⟨hm, hwf', hvals⟩ => ⟨Memory.Modifies.of_sameFrontier hm, hm.1, hwf', hvals⟩

/-- Uniform `Realizes .exact` certificate for `copySliceProg` with `work = 0`. -/
theorem realizes_copySliceProg :
    Realizes .exact (fun ((src, dst), count) => copySliceProg src dst count)
      WordEncoding.encode WordEncoding.encode
      (fun _ ((src, dst), count) s => src + count ≤ s.frontier ∧ dst + count ≤ s.frontier)
      (fun _ _ => 0) := by
  have hraw : Realizes .exact (fun d : (ℕ × ℕ) × ℕ => copySliceProg d.1.1 d.1.2 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe (fun x : ((ℕ × ℕ) × ℕ) × ℕ =>
          copySliceStep ((x.1.1.1, x.1.1.2), x.2))
        (fun w d s => copySliceStepSafe w ((d.1.1.1, d.1.1.2), d.2) s) w d d.2 0 s)
      (fun _ _ => 0) := by
    unfold copySliceProg
    realize [realizes_copySliceStep]
    exact h
  refine (hraw.congr (fun ⟨⟨_, _⟩, _⟩ => rfl)).consequence
    (fun w d s hwords hmem hbound => ?_) (fun _ _ => le_rfl)
  rcases d with ⟨⟨src, dst⟩, count⟩
  exact iterationSafe_map (fun x : (ℕ × ℕ) × ℕ => (x.1.1, x.1.2)) copySliceStep
    copySliceStepSafe _ (fun _ _ _ hs => hs)
    (copySlice_iterationSafe hmem (hwords 2) hbound.1 hbound.2)

/-! ## In-place exclusive prefix sum (`prefixSumProg`) -/

/-- Single step of the in-place exclusive prefix sum: read `x` at `base + idx`, overwrite
`base + idx` with the running accumulator `acc`, and return `(idx + 1, acc + x)`. -/
@[expose] def prefixSumStep : ℕ × ℕ × ℕ → Memory.Prog (ℕ × ℕ)
  | (base, idx, acc) => do
    let x ← Memory.read (base + idx)
    Memory.write (base + idx) acc
    pure (idx + 1, acc + x)

/-- Native safety domain for `prefixSumStep`. -/
@[expose] def prefixSumStepSafe (w : ℕ) : ℕ × ℕ × ℕ → Memory.State → Prop
  | (base, idx, acc), s => Fits w (idx + 1) ∧ Fits w (acc + s.mem (base + idx))

private theorem realizes_prefixSumStep_history : Realizes .exact
    prefixSumStep WordEncoding.encode WordEncoding.encode
    (fun w d s => prefixSumStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (prefixSumStep d)))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact
      (fun d : ℕ × ℕ × ℕ => do
        let x ← Memory.read (d.1 + d.2.1)
        Memory.write (d.1 + d.2.1) d.2.2
        pure (d.2.1 + 1, d.2.2 + x))
      WordEncoding.encode WordEncoding.encode
      (fun w d s => prefixSumStepSafe w d s ∧
        (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (prefixSumStep d)))
      (fun _ _ => 0) := by
    realize
    all_goals
      rcases d with ⟨_, _, _⟩
      obtain ⟨⟨hfit1, hfit2⟩, hv⟩ := h
      have hfront := hmem.frontier_fits
      dsimp only [StateTransitionSpec.clientHistory, prefixSumStep] at hv
      simp only [StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.stepFn, Memory.read, Memory.write, Memory.step_read, Memory.step_write,
        Memory.valid] at hv
      dsimp only
      fits
  exact hraw.congr (fun ⟨_, _, _⟩ => rfl)

/-- Uniform `Realizes .exact` certificate for `prefixSumStep` with `work = 0`. -/
theorem realizes_prefixSumStep :
    Realizes .exact prefixSumStep WordEncoding.encode WordEncoding.encode prefixSumStepSafe
      (fun _ _ => 0) :=
  realizes_prefixSumStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- In-place exclusive prefix sum over `[base, base + count)`: overwrites `mem (base + j)` with
`∑ i ∈ Finset.range j, mem (base + i)` for `j < count`, and returns the total sum
`∑ i ∈ Finset.range count, mem (base + i)`. -/
@[expose] def prefixSumProg (base count : ℕ) : Memory.Prog ℕ := do
  let res ← iterate prefixSumStep base count (0, 0)
  pure res.2

/-- Specification for `prefixSumProg`: computes the in-place exclusive prefix sum over
`[base, base + count)`, returns the total sum `∑ i ∈ Finset.range count, s.mem (base + i)`,
modifies only `Set.Ico base (base + count)` with fixed frontier, costs at most `2 * count`, and
satisfies `iterationSafe` and `WellFormed`. -/
theorem prefixSumProg_spec {w base count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count) (hbound : base + count ≤ s.frontier)
    (hsum : Fits w (∑ i ∈ Finset.range count, s.mem (base + i))) :
    iterationSafe prefixSumStep prefixSumStepSafe w base count (0, 0) s ∧
    Memory.SameFrontierTriple w s (prefixSumProg base count) (2 * count)
      (Set.Ico base (base + count)) fun res s' =>
        res = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) := by
  let S : Set ℕ := Set.Ico base (base + count)
  let inv (k : ℕ) (a : ℕ × ℕ) (t : Memory.State) : Prop :=
    a.1 = k ∧
    a.2 = (∑ i ∈ Finset.range k, s.mem (base + i)) ∧
    t.frontier = s.frontier ∧
    Memory.WellFormed w t ∧
    (∀ j < k, t.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i)) ∧
    (∀ i, k ≤ i → i < count → t.mem (base + i) = s.mem (base + i))
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      prefixSumStepSafe w (base, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (prefixSumStep (base, a))) ∧
      let a' := (Memory.spec 0).clientResult t (prefixSumStep (base, a))
      let t' := (Memory.spec 0).clientState t (prefixSumStep (base, a))
      memoryCost (prefixSumStep (base, a)) t + 0 ≤ 0 + 2 ∧
      Memory.SameFrontierModifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk ⟨idx, acc⟩ t ⟨hidx, hacc, htfr, hwt, hpref, hrest⟩
    dsimp only at hidx hacc
    subst idx
    have hcur : t.mem (base + k) = s.mem (base + k) := hrest k (le_refl k) hk
    have hacc_next : acc + t.mem (base + k) = ∑ i ∈ Finset.range (k + 1), s.mem (base + i) := by
      rw [hacc, hcur, Finset.sum_range_succ]
    have hfit_acc : Fits w acc :=
      hsum.of_le (hacc ▸ Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    have hfit_next : Fits w (acc + t.mem (base + k)) :=
      hsum.of_le (hacc_next ▸ Finset.sum_le_sum_of_subset (Finset.range_mono (by omega)))
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (prefixSumStep (base, (k, acc)))) := by
      dsimp only [prefixSumStep]
      exact validHistory_read_bind (by rw [htfr]; omega)
        (validHistory_write_bind (by rw [htfr]; omega) hfit_acc (validHistory_pure w _ _))
    have hcost : memoryCost (prefixSumStep (base, (k, acc))) t ≤ 2 := by
      dsimp only [prefixSumStep]
      simp only [memoryCost_bind', memoryCost_read, memoryCost_write, memoryCost_pure]
      decide
    have hres : (Memory.spec 0).clientResult t (prefixSumStep (base, (k, acc))) =
        (k + 1, acc + t.mem (base + k)) := by
      dsimp only [prefixSumStep]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (prefixSumStep (base, (k, acc))) =
        ⟨Function.update t.mem (base + k) acc, t.frontier⟩ := rfl
    have hmod : Memory.SameFrontierModifies S t
        ⟨Function.update t.mem (base + k) acc, t.frontier⟩ :=
      (Memory.SameFrontierModifies.write t (base + k) acc).mono fun x hx => by
        have heq : x = base + k := hx
        subst heq
        exact ⟨Nat.le_add_right _ _, by omega⟩
    have hfit_k1 : Fits w (k + 1) := hcnt.of_le (by omega)
    refine ⟨⟨hfit_k1, hfit_next⟩, hvh, by omega, by rw [hst]; exact hmod, ?_⟩
    rw [hres, hst]
    refine ⟨rfl, hacc_next, htfr, wellFormed_clientState hwt hvh, fun j hj => ?_,
      fun i hik hic => ?_⟩
    · dsimp only
      by_cases hjk : j = k
      · rw [hjk, Function.update_self, hacc]
      · rw [Function.update_of_ne (by omega)]
        exact hpref j (by omega)
    · dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hrest i (by omega) hic
  obtain ⟨hsafe, hv, hcost, hmod, _, hres, _, hwf', hpref, _⟩ :=
    iterate_potential_sameFrontier_spec prefixSumStep prefixSumStepSafe w base 2 count
      inv (fun _ _ _ => 0) S hstep (0, 0) s
      ⟨rfl, by simp, rfl, hwf, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩
  have hloop : Memory.SameFrontierTriple w s (iterate prefixSumStep base count (0, 0))
      (2 * count) S fun res s' =>
        res.2 = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) :=
    sameFrontierTriple_iff_realization.mpr ⟨hv, by simpa using hcost, hmod, hres, hwf', hpref⟩
  have hret : Memory.SameFrontierTriple w s (prefixSumProg base count) (2 * count) S
      fun res s' =>
        res = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) :=
    ((hloop.mono le_rfl fun res _ h =>
      Memory.SameFrontierTriple.pure (c := 0) (a := res.2) h).bind_same).mono
      (Nat.add_zero _).le fun _ _ h => h
  exact ⟨hsafe, hret⟩

/-- General `FramedTriple` wrapper for `prefixSumProg`. -/
theorem prefixSumProg_framedTriple {w base count : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hcnt : Fits w count) (hbound : base + count ≤ s.frontier)
    (hsum : Fits w (∑ i ∈ Finset.range count, s.mem (base + i))) :
    Memory.FramedTriple w s (prefixSumProg base count) (2 * count) (Set.Ico base (base + count))
      fun res s' =>
        res = ∑ i ∈ Finset.range count, s.mem (base + i) ∧
        s'.frontier = s.frontier ∧
        Memory.WellFormed w s' ∧
        ∀ j < count, s'.mem (base + j) = ∑ i ∈ Finset.range j, s.mem (base + i) :=
  Memory.Triple.mono (prefixSumProg_spec hwf hcnt hbound hsum).2 le_rfl
    fun _ _ ⟨hm, hres, hwf', hpref⟩ =>
      ⟨Memory.Modifies.of_sameFrontier hm, hres, hm.1, hwf', hpref⟩

/-- Uniform `Realizes .exact` certificate for `prefixSumProg` with `work = 0`. -/
theorem realizes_prefixSumProg :
    Realizes .exact (fun d : ℕ × ℕ => prefixSumProg d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => d.1 + d.2 ≤ s.frontier ∧
        Fits w (∑ i ∈ Finset.range d.2, s.mem (d.1 + i)))
      (fun _ _ => 0) := by
  have hraw : Realizes .exact (fun d : ℕ × ℕ => prefixSumProg d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => iterationSafe (fun x : (ℕ × ℕ) × ℕ × ℕ => prefixSumStep (x.1.1, x.2))
        (fun w d s => prefixSumStepSafe w (d.1.1, d.2.1, d.2.2) s) w d d.2 (0, 0) s)
      (fun _ _ => 0) := by
    unfold prefixSumProg
    realize [realizes_prefixSumStep]
    exact h
  exact hraw.consequence (fun w d s hwords hmem ⟨hbound, hsum⟩ =>
    iterationSafe_map Prod.fst prefixSumStep prefixSumStepSafe _ (fun _ _ _ hs => hs)
      (prefixSumProg_spec hmem (hwords 1) hbound hsum).1) (fun _ _ => le_rfl)

/-! ## Zeroed block allocation (`allocZeroBlockProg`, `allocZeroBlockDirtyProg`) -/

/-- Allocate a zeroed block of `size` words at the frontier, returning `Block.mk base size`. -/
@[expose] def allocZeroBlockProg (size : ℕ) : Memory.Prog Block := do
  let base ← Memory.alloc size
  pure ⟨base, size⟩

/-- Uniform `Realizes .exact` certificate for `allocZeroBlockProg` with `work = 0`. -/
theorem realizes_allocZeroBlockProg :
    Realizes .exact allocZeroBlockProg WordEncoding.encode WordEncoding.encode
      (fun _ _ _ => True) (fun _ _ => 0) := by
  unfold allocZeroBlockProg
  realize

/-- Framed specification for `allocZeroBlockProg`: costs `size + 1`, preserves all cells below
`s.frontier` (`Modifies ∅`), returns `⟨s.frontier, size⟩` allocated and zeroed, preserves
`WellFormed`, and guarantees disjointness from every block previously allocated in `s`. -/
theorem allocZeroBlockProg_spec {w size : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfit : Fits w (s.frontier + size)) :
    Memory.FramedTriple w s (allocZeroBlockProg size) (size + 1) ∅ fun b s' =>
      b = ⟨s.frontier, size⟩ ∧
      b.Allocated s' ∧
      Memory.WellFormed w s' ∧
      (∀ j < size, s'.mem (b.base + j) = 0) ∧
      ∀ b' : Block, b'.Allocated s → b'.Disjoint b := by
  have ht : Memory.Triple w s (allocZeroBlockProg size) (size + 1) fun b s' =>
      Memory.Modifies ∅ s s' ∧
      b = ⟨s.frontier, size⟩ ∧
      b.Allocated s' ∧
      Memory.WellFormed w s' ∧
      (∀ j < size, s'.mem (b.base + j) = 0) ∧
      ∀ b' : Block, b'.Allocated s → b'.Disjoint b := by
    refine Memory.Triple.mono (Memory.Triple.alloc_bind (c := 0) hfit (Memory.Triple.pure ?_))
      (Nat.zero_add _).le fun _ _ h => h
    refine ⟨Memory.Modifies.alloc s size, rfl, le_rfl, ?_, fun j hj => ?_, fun b' hb' => ?_⟩
    · exact hwf.step (o := .alloc size) hfit
    · exact clear_of_owns (Block.owns_add (b := ⟨s.frontier, size⟩) hj)
    · exact Block.disjoint_of_allocated_frontier hb' size
  exact ht

/-- Allocate a zeroed block of `size` words in `O(1)` time (`cost = 1`) via `Memory.allocDirty`
when memory is known to satisfy `Memory.ZeroAbove s`. -/
@[expose] def allocZeroBlockDirtyProg (size : ℕ) : Memory.Prog Block := do
  let base ← Memory.allocDirty size
  pure ⟨base, size⟩

/-- Uniform `Realizes .exact` certificate for `allocZeroBlockDirtyProg` with `work = 0`. -/
theorem realizes_allocZeroBlockDirtyProg :
    Realizes .exact allocZeroBlockDirtyProg WordEncoding.encode WordEncoding.encode
      (fun _ _ _ => True) (fun _ _ => 0) := by
  unfold allocZeroBlockDirtyProg
  realize

/-- Framed specification for `allocZeroBlockDirtyProg` under `Memory.ZeroAbove s`: costs `1`,
modifies nothing below `s.frontier` (`Modifies ∅`), returns `⟨s.frontier, size⟩` allocated and
zeroed, preserves `WellFormed` and `ZeroAbove`, and guarantees disjointness from every block
previously allocated in `s`. -/
theorem allocZeroBlockDirtyProg_spec {w size : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hz : Memory.ZeroAbove s) (hfit : Fits w (s.frontier + size)) :
    Memory.FramedTriple w s (allocZeroBlockDirtyProg size) 1 ∅ fun b s' =>
      b = ⟨s.frontier, size⟩ ∧
      b.Allocated s' ∧
      Memory.WellFormed w s' ∧
      Memory.ZeroAbove s' ∧
      (∀ j < size, s'.mem (b.base + j) = 0) ∧
      ∀ b' : Block, b'.Allocated s → b'.Disjoint b := by
  refine Memory.Triple.allocDirty_bind (c := 0) hfit (Memory.Triple.pure ?_)
  refine ⟨Memory.Modifies.allocDirty s size, rfl, le_rfl, ?_, hz.allocDirty size,
    fun j hj => ?_, fun b' hb' => ?_⟩
  · exact hwf.step (o := .allocDirty size) hfit
  · exact hz (s.frontier + j) (by omega)
  · exact Block.disjoint_of_allocated_frontier hb' size

end Cslib.WordRAM.Realization
