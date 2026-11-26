/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Layout
import CslibFrontier.DataStructure.Memory.Frame
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Dynamic Soft-Heap Partition Subroutines on the Word RAM

Implements the `Memory.Prog` subroutines, native safety domains, and uniform `Realizes .exact`
(`work = 0`) certificates for the `ε = 1 / 16` dynamic Soft-Heap DJP partition algorithm of
[PettieRamachandran2002], Section 3.2:

* Setup and outer/remaining edge loops (`partSetup`, `partRunOuterLoop`, `partRunRemLoop`),
  directly consuming `buildUndirCSR`, `SoftHeap.allocPool`, and `ArrayOps.fillConstProg`.
* Dynamic DJP round growth (`partRoundInit`, `partDjpLoop`, `partDjpStep`, `partDjpDispatch`,
  `partDjpAddVert`, `partDjpMaybeExpand`, `partExpandVertex`, `partExpandStep`,
  `partTryInsertEdge`), directly consuming `SoftHeap.{shInsert, shExtractMin}`.
* Per-round emission (`partRoundFinish`, `partEmitComp`, `partEmitCorrLoop`, `partMarkDeadLoop`,
  `partReadLocalPair`, `partWriteStride4`, `partCopyIndexedEdge`, `partWriteLocalEdge`,
  `partMaybeEmitLocal`, `partWriteRoundMeta`), consuming `SoftHeap.shCollectCorrupted`.

All interfaces use named `word_enc_structure` types from `Partition.Layout` with zero positional
tuple projection chains.

## Main definitions

* `partTryInsertEdge`, `partExpandVertex`, `partDjpAddVert`, `partDjpDispatch`, `partDjpStep`,
  `partDjpLoop`: dynamic Soft-Heap DJP growth loop.
* `partReadLocalPair`, `partWriteStride4`, `partCopyIndexedEdge`, `partWriteLocalEdge`,
  `partMaybeEmitLocal`, `partRoundFinish`: component/corrupted/dead emission helpers.
* `partSetup`, `partRoundInit`, `partRunRound`, `partOuterStep`, `partRunOuterLoop`,
  `partRunRemLoop`: setup, round execution, and outer/post-loop scanners.

## Main results

* `realizes_partSetup`, `realizes_partDjpLoop`, `realizes_partRunRound`,
  `realizes_partRunOuterLoop`, `realizes_partRunRemLoop` (and component `realizes_*` lemmas):
  uniform `Realizes .exact` certificates with `work = 0`.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap

/-! ## Dynamic Soft-Heap DJP Growth Subroutines -/

/-- Conditionally inserts edge `d.eIdx` into the Soft Heap when active (`edgeState = 0`) and
neighbor `d.nb` is not yet in the current component (`inCur ≠ d.cid`). -/
def partTryInsertEdge (d : PartTryInsertArgs) : Memory.Prog SHHandle := do
  let st ← Memory.read (d.bufBase + 14 * d.n + d.eIdx)
  if st = 0 then
    let inNb ← Memory.read (d.bufBase + d.n + d.nb)
    if inNb ≠ d.cid then
      let wt ← Memory.read (d.edgeBase + 4 * d.eIdx + 2)
      shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))
    else pure d.sh
  else pure d.sh

/-- Native safety domain for `partTryInsertEdge`. -/
def partTryInsertEdgeSafe (w : ℕ) (d : PartTryInsertArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (500 * (2 * d.m + 1)) ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
    d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧
    (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 →
      d.bufBase + d.n + d.nb < s.frontier ∧
      (s.mem (d.bufBase + d.n + d.nb) ≠ d.cid →
        d.edgeBase + 4 * d.eIdx + 2 < s.frontier ∧
        shInsertSafe w (d.sh, d.eIdx, s.mem (d.edgeBase + 4 * d.eIdx + 2),
          500 * (2 * d.m + 1)) s))

private theorem realizes_partTryInsertEdge_history : Realizes .exact
    partTryInsertEdge WordEncoding.encode WordEncoding.encode
    (fun w d s => partTryInsertEdgeSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partTryInsertEdge d)))
    (fun _ _ => 0) := by
  unfold partTryInsertEdge
  realize [realizes_shInsert]
  all_goals
    obtain ⟨⟨h16, hfuel, hbuf_fit, hst_lt, hbr⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ne_eq, ite_true, not_false_eq_true,
      StateTransitionSpec.runClient_lift_bind', StateTransitionSpec.validHistory_cons,
      StateTransitionSpec.stepFn, Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | (have := (hbr trivial).1; fits)
    | (have := ((hbr trivial).2 trivial).1; fits)
    | fits

/-- `partTryInsertEdge` is uniformly realized with `work = 0`. -/
theorem realizes_partTryInsertEdge : Realizes .exact
    partTryInsertEdge WordEncoding.encode WordEncoding.encode
    partTryInsertEdgeSafe (fun _ _ => 0) :=
  realizes_partTryInsertEdge_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partTryInsertEdge`. -/
theorem partTryInsertEdge_def (d : PartTryInsertArgs) : partTryInsertEdge d =
    (Memory.read (d.bufBase + 14 * d.n + d.eIdx) >>= fun st =>
      if st = 0 then
        Memory.read (d.bufBase + d.n + d.nb) >>= fun inNb =>
          if inNb ≠ d.cid then
            Memory.read (d.edgeBase + 4 * d.eIdx + 2) >>= fun wt =>
              shInsert (d.sh, d.eIdx, wt, 500 * (2 * d.m + 1))
          else pure d.sh
      else pure d.sh) := by
  unfold partTryInsertEdge
  rfl

/-- Unfolding equation for `partTryInsertEdgeSafe`. -/
theorem partTryInsertEdgeSafe_def (w : ℕ) (d : PartTryInsertArgs) (s : Memory.State) :
    partTryInsertEdgeSafe w d s =
      (Fits w 16 ∧ Fits w (500 * (2 * d.m + 1)) ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
        d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧
        (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 →
          d.bufBase + d.n + d.nb < s.frontier ∧
          (s.mem (d.bufBase + d.n + d.nb) ≠ d.cid →
            d.edgeBase + 4 * d.eIdx + 2 < s.frontier ∧
            shInsertSafe w (d.sh, d.eIdx, s.mem (d.edgeBase + 4 * d.eIdx + 2),
              500 * (2 * d.m + 1)) s))) := by
  unfold partTryInsertEdgeSafe
  rfl

/-- Single CSR half-edge expansion step during dynamic DJP growth. -/
def partExpandStep (d : PartAdjEnv × PartExpandState) : Memory.Prog PartExpandState := do
  let env := d.1
  let st := d.2
  let nb ← Memory.read (env.adjBase + 2 * st.idx)
  let eIdx ← Memory.read (env.adjBase + 2 * st.idx + 1)
  let h' ← partTryInsertEdge ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid, nb, eIdx, st.sh⟩
  pure ⟨st.idx + 1, h'⟩

/-- Native safety domain for `partExpandStep`. -/
def partExpandStepSafe (w : ℕ) (d : PartAdjEnv × PartExpandState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  Fits w 16 ∧ Fits w (st.idx + 1) ∧ env.adjBase + 2 * st.idx + 1 < s.frontier ∧
    partTryInsertEdgeSafe w
      ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid,
        s.mem (env.adjBase + 2 * st.idx), s.mem (env.adjBase + 2 * st.idx + 1), st.sh⟩ s

private theorem realizes_partExpandStep_history : Realizes .exact
    partExpandStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partExpandStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partExpandStep d)))
    (fun _ _ => 0) := by
  unfold partExpandStep
  realize [realizes_partTryInsertEdge]
  all_goals
    obtain ⟨⟨h16, hj1, hadj_lt, htry⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partExpandStep` is uniformly realized with `work = 0`. -/
theorem realizes_partExpandStep : Realizes .exact
    partExpandStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partExpandStepSafe (fun _ _ => 0) :=
  realizes_partExpandStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partExpandStep`. -/
theorem partExpandStep_def (d : PartAdjEnv × PartExpandState) : partExpandStep d =
    (Memory.read (d.1.adjBase + 2 * d.2.idx) >>= fun nb =>
      Memory.read (d.1.adjBase + 2 * d.2.idx + 1) >>= fun eIdx =>
        partTryInsertEdge
          ⟨d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid, nb, eIdx, d.2.sh⟩ >>= fun h' =>
          pure ⟨d.2.idx + 1, h'⟩) := by
  unfold partExpandStep
  rfl

/-- Unfolding equation for `partExpandStepSafe`. -/
theorem partExpandStepSafe_def (w : ℕ) (d : PartAdjEnv × PartExpandState) (s : Memory.State) :
    partExpandStepSafe w d s =
      (Fits w 16 ∧ Fits w (d.2.idx + 1) ∧ d.1.adjBase + 2 * d.2.idx + 1 < s.frontier ∧
        partTryInsertEdgeSafe w
          ⟨d.1.edgeBase, d.1.bufBase, d.1.n, d.1.m, d.1.cid,
            s.mem (d.1.adjBase + 2 * d.2.idx),
            s.mem (d.1.adjBase + 2 * d.2.idx + 1), d.2.sh⟩ s) := by
  unfold partExpandStepSafe
  rfl

/-- Expands all active CSR edges incident to vertex `d.u` into the Soft Heap. -/
def partExpandVertex (d : PartExpandVertexArgs) : Memory.Prog SHHandle := do
  let startJ ← Memory.read (d.env.offBase + d.u)
  let endJ ← Memory.read (d.env.offBase + d.u + 1)
  let res ← iterate partExpandStep
    ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
    (endJ - startJ) ⟨startJ, d.sh⟩
  pure res.sh

/-- Native safety domain for `partExpandVertex`. -/
def partExpandVertexSafe (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) : Prop :=
  let startJ := s.mem (d.env.offBase + d.u)
  let endJ := s.mem (d.env.offBase + d.u + 1)
  Fits w 16 ∧ d.env.offBase + d.u + 1 < s.frontier ∧ startJ ≤ endJ ∧
    iterationSafe partExpandStep partExpandStepSafe w
      ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
      (endJ - startJ) ⟨startJ, d.sh⟩ s

private theorem realizes_partExpandVertex_history : Realizes .exact
    partExpandVertex WordEncoding.encode WordEncoding.encode
    (fun w d s => partExpandVertexSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partExpandVertex d)))
    (fun _ _ => 0) := by
  unfold partExpandVertex
  realize [realizes_partExpandStep]
  all_goals
    obtain ⟨⟨h16, hoff_lt, hle, hiter⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-- `partExpandVertex` is uniformly realized with `work = 0`. -/
theorem realizes_partExpandVertex : Realizes .exact
    partExpandVertex WordEncoding.encode WordEncoding.encode
    partExpandVertexSafe (fun _ _ => 0) :=
  realizes_partExpandVertex_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partExpandVertex`. -/
theorem partExpandVertex_def (d : PartExpandVertexArgs) : partExpandVertex d =
    (Memory.read (d.env.offBase + d.u) >>= fun startJ =>
      Memory.read (d.env.offBase + d.u + 1) >>= fun endJ =>
        iterate partExpandStep
          ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
          (endJ - startJ) ⟨startJ, d.sh⟩ >>= fun res =>
          pure res.sh) := by
  unfold partExpandVertex
  rfl

/-- Unfolding equation for `partExpandVertexSafe`. -/
theorem partExpandVertexSafe_def (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) :
    partExpandVertexSafe w d s =
      (Fits w 16 ∧ d.env.offBase + d.u + 1 < s.frontier ∧
        s.mem (d.env.offBase + d.u) ≤ s.mem (d.env.offBase + d.u + 1) ∧
        iterationSafe partExpandStep partExpandStepSafe w
          ⟨d.env.adjBase, d.env.edgeBase, d.env.bufBase, d.env.n, d.env.m, d.cid⟩
          (s.mem (d.env.offBase + d.u + 1) - s.mem (d.env.offBase + d.u))
          ⟨s.mem (d.env.offBase + d.u), d.sh⟩ s) := by
  unfold partExpandVertexSafe
  rfl

/-- Writes four words `(u, v, weight, id)` in stride-4 layout at `d.dstBase + 4 * d.idx`. -/
def partWriteStride4 (d : PartWriteStride4Args) : Memory.Prog Unit := do
  Memory.write (d.dstBase + 4 * d.idx) d.u
  Memory.write (d.dstBase + 4 * d.idx + 1) d.v
  Memory.write (d.dstBase + 4 * d.idx + 2) d.weight
  Memory.write (d.dstBase + 4 * d.idx + 3) d.id

/-- Native safety domain for `partWriteStride4`. -/
def partWriteStride4Safe (w : ℕ) (d : PartWriteStride4Args) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.dstBase + 4 * d.idx + 3 < s.frontier

/-- `partWriteStride4` is uniformly realized with `work = 0`. -/
theorem realizes_partWriteStride4 : Realizes .exact
    partWriteStride4 WordEncoding.encode WordEncoding.encode
    partWriteStride4Safe (fun _ _ => 0) := by
  unfold partWriteStride4
  realize
  all_goals
    have h16 := h.1
    have hlt := h.2
    have hfront := hmem.frontier_fits
    fits

/-- Unfolding equation for `partWriteStride4`. -/
theorem partWriteStride4_def (d : PartWriteStride4Args) : partWriteStride4 d =
    (Memory.write (d.dstBase + 4 * d.idx) d.u >>= fun _ =>
      Memory.write (d.dstBase + 4 * d.idx + 1) d.v >>= fun _ =>
        Memory.write (d.dstBase + 4 * d.idx + 2) d.weight >>= fun _ =>
          Memory.write (d.dstBase + 4 * d.idx + 3) d.id) := by
  unfold partWriteStride4
  rfl

/-- Unfolding equation for `partWriteStride4Safe`. -/
theorem partWriteStride4Safe_def (w : ℕ) (d : PartWriteStride4Args) (s : Memory.State) :
    partWriteStride4Safe w d s = (Fits w 16 ∧ d.dstBase + 4 * d.idx + 3 < s.frontier) := by
  unfold partWriteStride4Safe
  rfl

/-- Copies stride-4 indexed edge `d.srcIdx` from `d.srcBase` to `d.dstBase + 4 * d.dstIdx`. -/
def partCopyIndexedEdge (d : PartCopyEdgeArgs) : Memory.Prog Unit := do
  let u ← Memory.read (d.srcBase + 4 * d.srcIdx)
  let v ← Memory.read (d.srcBase + 4 * d.srcIdx + 1)
  let wt ← Memory.read (d.srcBase + 4 * d.srcIdx + 2)
  let eid ← Memory.read (d.srcBase + 4 * d.srcIdx + 3)
  partWriteStride4 ⟨d.dstBase, d.dstIdx, u, v, wt, eid⟩

/-- Native safety domain for `partCopyIndexedEdge`. -/
def partCopyIndexedEdgeSafe (w : ℕ) (d : PartCopyEdgeArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.srcBase + 4 * d.srcIdx + 3 < s.frontier ∧
    d.dstBase + 4 * d.dstIdx + 3 < s.frontier

/-- `partCopyIndexedEdge` is uniformly realized with `work = 0`. -/
theorem realizes_partCopyIndexedEdge : Realizes .exact
    partCopyIndexedEdge WordEncoding.encode WordEncoding.encode
    partCopyIndexedEdgeSafe (fun _ _ => 0) := by
  unfold partCopyIndexedEdge
  realize [realizes_partWriteStride4]
  all_goals
    have h16 := h.1
    have hs := h.2.1
    have hd := h.2.2
    have hfront := hmem.frontier_fits
    first | exact ⟨h16, hd⟩ | fits

/-- Unfolding equation for `partCopyIndexedEdge`. -/
theorem partCopyIndexedEdge_def (d : PartCopyEdgeArgs) : partCopyIndexedEdge d =
    (Memory.read (d.srcBase + 4 * d.srcIdx) >>= fun u =>
      Memory.read (d.srcBase + 4 * d.srcIdx + 1) >>= fun v =>
        Memory.read (d.srcBase + 4 * d.srcIdx + 2) >>= fun wt =>
          Memory.read (d.srcBase + 4 * d.srcIdx + 3) >>= fun eid =>
            partWriteStride4 ⟨d.dstBase, d.dstIdx, u, v, wt, eid⟩) := by
  unfold partCopyIndexedEdge
  rfl

/-- Unfolding equation for `partCopyIndexedEdgeSafe`. -/
theorem partCopyIndexedEdgeSafe_def (w : ℕ) (d : PartCopyEdgeArgs) (s : Memory.State) :
    partCopyIndexedEdgeSafe w d s =
      (Fits w 16 ∧ d.srcBase + 4 * d.srcIdx + 3 < s.frontier ∧
        d.dstBase + 4 * d.dstIdx + 3 < s.frontier) := by
  unfold partCopyIndexedEdgeSafe
  rfl

/-- Checks stopping criteria after adding `d.vOut` (`d.dOut ≠ 0` or `d.env.maxsize ≤ d.size`),
expanding `d.vOut` only if continuing. -/
def partDjpMaybeExpand (d : PartDjpMaybeExpandArgs) : Memory.Prog PartDjpState := do
  if d.dOut ≠ 0 then
    pure ⟨0, 1, d.size, d.tLen, d.sh⟩
  else if d.env.maxsize ≤ d.size then
    pure ⟨0, 0, d.size, d.tLen, d.sh⟩
  else
    let h' ← partExpandVertex ⟨d.env, d.cid, d.vOut, d.sh⟩
    pure ⟨1, 0, d.size, d.tLen, h'⟩

/-- Native safety domain for `partDjpMaybeExpand`. -/
def partDjpMaybeExpandSafe (w : ℕ) (d : PartDjpMaybeExpandArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (d.dOut = 0 → ¬(d.env.maxsize ≤ d.size) →
      partExpandVertexSafe w ⟨d.env, d.cid, d.vOut, d.sh⟩ s)

/-- `partDjpMaybeExpand` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpMaybeExpand : Realizes .exact
    partDjpMaybeExpand WordEncoding.encode WordEncoding.encode
    partDjpMaybeExpandSafe (fun _ _ => 0) := by
  unfold partDjpMaybeExpand
  realize [realizes_partExpandVertex]
  · exact h.2 (by omega) (by omega)
  · have h16 := h.1; fits
  · have h16 := h.1; fits

/-- Unfolding equation for `partDjpMaybeExpand`. -/
theorem partDjpMaybeExpand_def (d : PartDjpMaybeExpandArgs) : partDjpMaybeExpand d =
    (if d.dOut ≠ 0 then pure ⟨0, 1, d.size, d.tLen, d.sh⟩
    else if d.env.maxsize ≤ d.size then pure ⟨0, 0, d.size, d.tLen, d.sh⟩
    else partExpandVertex ⟨d.env, d.cid, d.vOut, d.sh⟩ >>= fun h' =>
      pure ⟨1, 0, d.size, d.tLen, h'⟩) := by
  unfold partDjpMaybeExpand
  rfl

/-- Unfolding equation for `partDjpMaybeExpandSafe`. -/
theorem partDjpMaybeExpandSafe_def (w : ℕ) (d : PartDjpMaybeExpandArgs) (s : Memory.State) :
    partDjpMaybeExpandSafe w d s =
      (Fits w 16 ∧ (d.dOut = 0 → ¬(d.env.maxsize ≤ d.size) →
        partExpandVertexSafe w ⟨d.env, d.cid, d.vOut, d.sh⟩ s)) := by
  unfold partDjpMaybeExpandSafe
  rfl

/-- Adds newly discovered vertex `d.vOut` and DJP tree edge `d.eIdx` to the current round. -/
def partDjpAddVert (d : PartDjpAddVertArgs) : Memory.Prog PartDjpState := do
  let bufBase := d.env.bufBase
  let n := d.env.n
  partCopyIndexedEdge ⟨d.env.edgeBase, bufBase + 10 * n, d.eIdx, d.tLen⟩
  let dOut ← Memory.read (bufBase + d.vOut)
  Memory.write (bufBase + 3 * n + d.size) d.vOut
  Memory.write (bufBase + n + d.vOut) d.cid
  Memory.write (bufBase + 2 * n + d.vOut) d.size
  partDjpMaybeExpand ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩

/-- Native safety domain for `partDjpAddVert`. -/
def partDjpAddVertSafe (w : ℕ) (d : PartDjpAddVertArgs) (s : Memory.State) : Prop :=
  let bufBase := d.env.bufBase
  let n := d.env.n
  let m := d.env.m
  Fits w 16 ∧ Fits w (d.size + 1) ∧ Fits w (d.tLen + 1) ∧ Fits w (bufBase + 14 * n + 14 * m) ∧
    partCopyIndexedEdgeSafe w ⟨d.env.edgeBase, bufBase + 10 * n, d.eIdx, d.tLen⟩ s ∧
    bufBase + d.vOut < s.frontier ∧ bufBase + 3 * n + d.size < s.frontier ∧
    bufBase + n + d.vOut < s.frontier ∧ bufBase + 2 * n + d.vOut < s.frontier ∧
    let s₁ := (Memory.spec 0).clientState s
      (partCopyIndexedEdge ⟨d.env.edgeBase, bufBase + 10 * n, d.eIdx, d.tLen⟩)
    let dOut := s₁.mem (bufBase + d.vOut)
    let s₂ : Memory.State := ⟨Function.update (Function.update (Function.update s₁.mem
      (bufBase + 3 * n + d.size) d.vOut) (bufBase + n + d.vOut) d.cid)
      (bufBase + 2 * n + d.vOut) d.size, s₁.frontier⟩
    partDjpMaybeExpandSafe w ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩ s₂

private theorem realizes_partDjpAddVert_history : Realizes .exact
    partDjpAddVert WordEncoding.encode WordEncoding.encode
    (fun w d s => partDjpAddVertSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partDjpAddVert d)))
    (fun _ _ => 0) := by
  unfold partDjpAddVert
  realize [realizes_partCopyIndexedEdge, realizes_partDjpMaybeExpand]
  all_goals
    obtain ⟨⟨h16, hsz, htl, _, hcopy, hlt1, hlt2, hlt3, hlt4, hme⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [Memory.write]
  all_goals fits

/-- `partDjpAddVert` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpAddVert : Realizes .exact
    partDjpAddVert WordEncoding.encode WordEncoding.encode
    partDjpAddVertSafe (fun _ _ => 0) :=
  realizes_partDjpAddVert_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partDjpAddVert`. -/
theorem partDjpAddVert_def (d : PartDjpAddVertArgs) : partDjpAddVert d =
    (partCopyIndexedEdge ⟨d.env.edgeBase, d.env.bufBase + 10 * d.env.n, d.eIdx, d.tLen⟩ >>=
      fun _ =>
        Memory.read (d.env.bufBase + d.vOut) >>= fun dOut =>
          Memory.write (d.env.bufBase + 3 * d.env.n + d.size) d.vOut >>= fun _ =>
            Memory.write (d.env.bufBase + d.env.n + d.vOut) d.cid >>= fun _ =>
            Memory.write (d.env.bufBase + 2 * d.env.n + d.vOut) d.size >>= fun _ =>
              partDjpMaybeExpand
                ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩) := by
  unfold partDjpAddVert
  rfl

/-- Unfolding equation for `partDjpAddVertSafe`. -/
theorem partDjpAddVertSafe_def (w : ℕ) (d : PartDjpAddVertArgs) (s : Memory.State) :
    partDjpAddVertSafe w d s =
      (Fits w 16 ∧ Fits w (d.size + 1) ∧ Fits w (d.tLen + 1) ∧
        Fits w (d.env.bufBase + 14 * d.env.n + 14 * d.env.m) ∧
        partCopyIndexedEdgeSafe w
          ⟨d.env.edgeBase, d.env.bufBase + 10 * d.env.n, d.eIdx, d.tLen⟩ s ∧
        d.env.bufBase + d.vOut < s.frontier ∧
        d.env.bufBase + 3 * d.env.n + d.size < s.frontier ∧
        d.env.bufBase + d.env.n + d.vOut < s.frontier ∧
        d.env.bufBase + 2 * d.env.n + d.vOut < s.frontier ∧
        let s₁ := (Memory.spec 0).clientState s
          (partCopyIndexedEdge ⟨d.env.edgeBase, d.env.bufBase + 10 * d.env.n, d.eIdx, d.tLen⟩)
        let dOut := s₁.mem (d.env.bufBase + d.vOut)
        let s₂ : Memory.State := ⟨Function.update (Function.update (Function.update s₁.mem
          (d.env.bufBase + 3 * d.env.n + d.size) d.vOut)
          (d.env.bufBase + d.env.n + d.vOut) d.cid)
          (d.env.bufBase + 2 * d.env.n + d.vOut) d.size, s₁.frontier⟩
        partDjpMaybeExpandSafe w
          ⟨d.env, d.cid, d.sh, d.vOut, dOut, d.size + 1, d.tLen + 1⟩ s₂) := by
  unfold partDjpAddVertSafe
  rfl

/-- Processes an extracted edge `d.eIdx`, skipping internal edges and otherwise adding `vOut`. -/
def partDjpDispatch (d : PartDjpDispatchArgs) : Memory.Prog PartDjpState := do
  let edgeBase := d.env.edgeBase
  let inCurBase := d.env.bufBase + d.env.n
  let u ← Memory.read (edgeBase + 4 * d.eIdx)
  let v ← Memory.read (edgeBase + 4 * d.eIdx + 1)
  let cu ← Memory.read (inCurBase + u)
  let cv ← Memory.read (inCurBase + v)
  if cu = d.cid ∧ cv = d.cid then
    pure ⟨1, d.hitPrev, d.size, d.tLen, d.sh⟩
  else
    let vOut := if cu = d.cid then v else u
    partDjpAddVert ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩

/-- Native safety domain for `partDjpDispatch`. -/
def partDjpDispatchSafe (w : ℕ) (d : PartDjpDispatchArgs) (s : Memory.State) : Prop :=
  let edgeBase := d.env.edgeBase
  let inCurBase := d.env.bufBase + d.env.n
  let u := s.mem (edgeBase + 4 * d.eIdx)
  let v := s.mem (edgeBase + 4 * d.eIdx + 1)
  let cu := s.mem (inCurBase + u)
  let cv := s.mem (inCurBase + v)
  Fits w 16 ∧ edgeBase + 4 * d.eIdx + 1 < s.frontier ∧
    inCurBase + u < s.frontier ∧ inCurBase + v < s.frontier ∧
    (¬(cu = d.cid ∧ cv = d.cid) →
      let vOut := if cu = d.cid then v else u
      partDjpAddVertSafe w ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩ s)

private theorem realizes_partDjpDispatch_history : Realizes .exact
    partDjpDispatch WordEncoding.encode WordEncoding.encode
    (fun w d s => partDjpDispatchSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partDjpDispatch d)))
    (fun _ _ => 0) := by
  unfold partDjpDispatch
  realize [realizes_partDjpAddVert]
  all_goals
    obtain ⟨⟨h16, he_lt, hu_lt, hv_lt, hadd⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ite_true, ite_false, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first | exact hadd (by simp_all) | fits

/-- `partDjpDispatch` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpDispatch : Realizes .exact
    partDjpDispatch WordEncoding.encode WordEncoding.encode
    partDjpDispatchSafe (fun _ _ => 0) :=
  realizes_partDjpDispatch_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partDjpDispatch`. -/
theorem partDjpDispatch_def (d : PartDjpDispatchArgs) : partDjpDispatch d =
    (Memory.read (d.env.edgeBase + 4 * d.eIdx) >>= fun u =>
      Memory.read (d.env.edgeBase + 4 * d.eIdx + 1) >>= fun v =>
        Memory.read (d.env.bufBase + d.env.n + u) >>= fun cu =>
          Memory.read (d.env.bufBase + d.env.n + v) >>= fun cv =>
            if cu = d.cid ∧ cv = d.cid then pure ⟨1, d.hitPrev, d.size, d.tLen, d.sh⟩
            else
              let vOut := if cu = d.cid then v else u
              partDjpAddVert ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩) := by
  unfold partDjpDispatch
  rfl

/-- Unfolding equation for `partDjpDispatchSafe`. -/
theorem partDjpDispatchSafe_def (w : ℕ) (d : PartDjpDispatchArgs) (s : Memory.State) :
    partDjpDispatchSafe w d s =
      (Fits w 16 ∧ d.env.edgeBase + 4 * d.eIdx + 1 < s.frontier ∧
        d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx) < s.frontier ∧
        d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx + 1) < s.frontier ∧
        (¬(s.mem (d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx)) = d.cid ∧
            s.mem (d.env.bufBase + d.env.n + s.mem (d.env.edgeBase + 4 * d.eIdx + 1)) = d.cid) →
          let u := s.mem (d.env.edgeBase + 4 * d.eIdx)
          let v := s.mem (d.env.edgeBase + 4 * d.eIdx + 1)
          let vOut := if s.mem (d.env.bufBase + d.env.n + u) = d.cid then v else u
          partDjpAddVertSafe w ⟨d.env, d.cid, d.sh, d.eIdx, vOut, d.size, d.tLen⟩ s)) := by
  unfold partDjpDispatchSafe
  rfl

/-- Single `boundedWhile` step of the dynamic Soft-Heap DJP loop. The initial `Memory.read`
of `bufBase` ensures `1 ≤ memoryCost (partDjpStep d) s` even when `shExtractMin` returns early
on an empty heap (`firstRoot = 0`, `memoryCost = 0`), allowing `Realizes.while₀` (`work = 0`). -/
def partDjpStep (d : PartDjpEnv × PartDjpState) : Memory.Prog PartDjpState := do
  let _ ← Memory.read d.1.env.bufBase
  let ext ← shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1))
  if ext.found = 0 then
    pure ⟨0, 0, d.2.size, d.2.tLen, ext.handle⟩
  else
    partDjpDispatch ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩

/-- Native safety domain for `partDjpStep`. -/
def partDjpStepSafe (w : ℕ) (d : PartDjpEnv × PartDjpState) (s : Memory.State) : Prop :=
  let m := d.1.env.m
  Fits w 16 ∧ Fits w (500 * (2 * m + 1)) ∧ d.1.env.bufBase < s.frontier ∧
    shExtractMinSafe w (d.2.sh, 500 * (2 * m + 1)) s ∧
    let ext := (Memory.spec 0).clientResult s (shExtractMin (d.2.sh, 500 * (2 * m + 1)))
    let s₁ := (Memory.spec 0).clientState s (shExtractMin (d.2.sh, 500 * (2 * m + 1)))
    (ext.found ≠ 0 →
      partDjpDispatchSafe w
        ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩ s₁)

private theorem realizes_partDjpStep_history : Realizes .exact
    partDjpStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partDjpStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partDjpStep d)))
    (fun _ _ => 0) := by
  unfold partDjpStep
  realize [realizes_shExtractMin, realizes_partDjpDispatch]
  all_goals
    obtain ⟨⟨h16, hfuel, hbuf_lt, hext, hdisp⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | exact hdisp (by assumption)
    | fits

/-- `partDjpStep` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpStep : Realizes .exact
    partDjpStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partDjpStepSafe (fun _ _ => 0) :=
  realizes_partDjpStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partDjpStep`. -/
theorem partDjpStep_def (d : PartDjpEnv × PartDjpState) : partDjpStep d =
    (Memory.read d.1.env.bufBase >>= fun _ =>
      shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1)) >>= fun ext =>
        if ext.found = 0 then pure ⟨0, 0, d.2.size, d.2.tLen, ext.handle⟩
        else partDjpDispatch
          ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩) := by
  unfold partDjpStep
  rfl

/-- Unfolding equation for `partDjpStepSafe`. -/
theorem partDjpStepSafe_def (w : ℕ) (d : PartDjpEnv × PartDjpState) (s : Memory.State) :
    partDjpStepSafe w d s =
      (Fits w 16 ∧ Fits w (500 * (2 * d.1.env.m + 1)) ∧ d.1.env.bufBase < s.frontier ∧
        shExtractMinSafe w (d.2.sh, 500 * (2 * d.1.env.m + 1)) s ∧
        let ext := (Memory.spec 0).clientResult s
          (shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1)))
        let s₁ := (Memory.spec 0).clientState s
          (shExtractMin (d.2.sh, 500 * (2 * d.1.env.m + 1)))
        (ext.found ≠ 0 → partDjpDispatchSafe w
          ⟨d.1.env, d.1.cid, ext.handle, ext.val, d.2.hitPrev, d.2.size, d.2.tLen⟩ s₁)) := by
  unfold partDjpStepSafe
  rfl

/-! ## Component, Corrupted, and Remaining Edge Emission Helpers -/

/-- Reads compacted local endpoint indices `(localIdx[u], localIdx[v])` for edge `d.eIdx`. -/
def partReadLocalPair (d : PartReadLocalPairArgs) : Memory.Prog (ℕ × ℕ) := do
  let u ← Memory.read (d.edgeBase + 4 * d.eIdx)
  let v ← Memory.read (d.edgeBase + 4 * d.eIdx + 1)
  let lu ← Memory.read (d.localBase + u)
  let lv ← Memory.read (d.localBase + v)
  pure (lu, lv)

/-- Native safety domain for `partReadLocalPair`. -/
def partReadLocalPairSafe (w : ℕ) (d : PartReadLocalPairArgs) (s : Memory.State) : Prop :=
  let u := s.mem (d.edgeBase + 4 * d.eIdx)
  let v := s.mem (d.edgeBase + 4 * d.eIdx + 1)
  Fits w 16 ∧ d.edgeBase + 4 * d.eIdx + 1 < s.frontier ∧
    d.localBase + u < s.frontier ∧ d.localBase + v < s.frontier

private theorem realizes_partReadLocalPair_history : Realizes .exact
    partReadLocalPair WordEncoding.encode WordEncoding.encode
    (fun w d s => partReadLocalPairSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partReadLocalPair d)))
    (fun _ _ => 0) := by
  unfold partReadLocalPair
  realize
  all_goals
    obtain ⟨⟨h16, he_lt, hu_lt, hv_lt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partReadLocalPair` is uniformly realized with `work = 0`. -/
theorem realizes_partReadLocalPair : Realizes .exact
    partReadLocalPair WordEncoding.encode WordEncoding.encode
    partReadLocalPairSafe (fun _ _ => 0) :=
  realizes_partReadLocalPair_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Emits one compacted local `IndexedEdge` at `d.dstBase + 4 * d.cEdgeLen`. -/
def partWriteLocalEdge (d : PartWriteLocalEdgeArgs) : Memory.Prog ℕ := do
  let lp ← partReadLocalPair ⟨d.edgeBase, d.localBase, d.eIdx⟩
  let wt ← Memory.read (d.edgeBase + 4 * d.eIdx + 2)
  let eid ← Memory.read (d.edgeBase + 4 * d.eIdx + 3)
  partWriteStride4 ⟨d.dstBase, d.cEdgeLen, lp.1, lp.2, wt, eid⟩
  pure (d.cEdgeLen + 1)

/-- Native safety domain for `partWriteLocalEdge`. -/
def partWriteLocalEdgeSafe (w : ℕ) (d : PartWriteLocalEdgeArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.cEdgeLen + 1) ∧
    partReadLocalPairSafe w ⟨d.edgeBase, d.localBase, d.eIdx⟩ s ∧
    d.edgeBase + 4 * d.eIdx + 3 < s.frontier ∧
    d.dstBase + 4 * d.cEdgeLen + 3 < s.frontier

private theorem realizes_partWriteLocalEdge_history : Realizes .exact
    partWriteLocalEdge WordEncoding.encode WordEncoding.encode
    (fun w d s => partWriteLocalEdgeSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partWriteLocalEdge d)))
    (fun _ _ => 0) := by
  unfold partWriteLocalEdge
  realize [realizes_partReadLocalPair, realizes_partWriteStride4]
  all_goals
    obtain ⟨⟨h16, hc1, hlp, he_lt, hd_lt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [Memory.read]
  all_goals first | exact ⟨h16, hd_lt⟩ | fits

/-- `partWriteLocalEdge` is uniformly realized with `work = 0`. -/
theorem realizes_partWriteLocalEdge : Realizes .exact
    partWriteLocalEdge WordEncoding.encode WordEncoding.encode
    partWriteLocalEdgeSafe (fun _ _ => 0) :=
  realizes_partWriteLocalEdge_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Conditionally claims edge `d.eIdx` for component `d.cid` when active and `inCur[d.nb] =
d.cid`. -/
def partMaybeEmitLocal (d : PartMaybeEmitLocalArgs) : Memory.Prog ℕ := do
  let st ← Memory.read (d.bufBase + 14 * d.n + d.eIdx)
  let inNb ← Memory.read (d.bufBase + d.n + d.nb)
  if st = 0 ∧ inNb = d.cid then
    Memory.write (d.bufBase + 14 * d.n + d.eIdx) 1
    partWriteLocalEdge
      ⟨d.edgeBase, d.bufBase + 2 * d.n, d.bufBase + 14 * d.n + 2 * d.m, d.eIdx, d.cEdgeLen⟩
  else
    pure d.cEdgeLen

/-- Native safety domain for `partMaybeEmitLocal`. -/
def partMaybeEmitLocalSafe (w : ℕ) (d : PartMaybeEmitLocalArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.bufBase + 14 * d.n + 14 * d.m) ∧
    d.bufBase + 14 * d.n + d.eIdx < s.frontier ∧ d.bufBase + d.n + d.nb < s.frontier ∧
    (s.mem (d.bufBase + 14 * d.n + d.eIdx) = 0 → s.mem (d.bufBase + d.n + d.nb) = d.cid →
      partWriteLocalEdgeSafe w
        ⟨d.edgeBase, d.bufBase + 2 * d.n, d.bufBase + 14 * d.n + 2 * d.m, d.eIdx, d.cEdgeLen⟩
        ⟨Function.update s.mem (d.bufBase + 14 * d.n + d.eIdx) 1, s.frontier⟩)

private theorem realizes_partMaybeEmitLocal_history : Realizes .exact
    partMaybeEmitLocal WordEncoding.encode WordEncoding.encode
    (fun w d s => partMaybeEmitLocalSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partMaybeEmitLocal d)))
    (fun _ _ => 0) := by
  unfold partMaybeEmitLocal
  realize [realizes_partWriteLocalEdge]
  all_goals
    obtain ⟨⟨h16, _, hst_lt, hnb_lt, hwle⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.write, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partMaybeEmitLocal` is uniformly realized with `work = 0`. -/
theorem realizes_partMaybeEmitLocal : Realizes .exact
    partMaybeEmitLocal WordEncoding.encode WordEncoding.encode
    partMaybeEmitLocalSafe (fun _ _ => 0) :=
  realizes_partMaybeEmitLocal_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Single CSR half-edge scan step emitting internal edges of `V_i` into `C_i`. -/
def partEmitEdgeStep (d : PartAdjEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let nb ← Memory.read (env.adjBase + 2 * cur.idx)
  let eIdx ← Memory.read (env.adjBase + 2 * cur.idx + 1)
  let c' ← partMaybeEmitLocal
    ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid, nb, eIdx, cur.count⟩
  pure ⟨cur.idx + 1, c'⟩

/-- Native safety domain for `partEmitEdgeStep`. -/
def partEmitEdgeStepSafe (w : ℕ) (d : PartAdjEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ env.adjBase + 2 * cur.idx + 1 < s.frontier ∧
    partMaybeEmitLocalSafe w
      ⟨env.edgeBase, env.bufBase, env.n, env.m, env.cid,
        s.mem (env.adjBase + 2 * cur.idx), s.mem (env.adjBase + 2 * cur.idx + 1), cur.count⟩ s

private theorem realizes_partEmitEdgeStep_history : Realizes .exact
    partEmitEdgeStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitEdgeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitEdgeStep d)))
    (fun _ _ => 0) := by
  unfold partEmitEdgeStep
  realize [realizes_partMaybeEmitLocal]
  all_goals
    obtain ⟨⟨h16, hj1, hadj_lt, hme⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partEmitEdgeStep` is uniformly realized with `work = 0`. -/
theorem realizes_partEmitEdgeStep : Realizes .exact
    partEmitEdgeStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitEdgeStepSafe (fun _ _ => 0) :=
  realizes_partEmitEdgeStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Scans one live vertex `compVerts[d.2.idx]`'s CSR slice to emit internal edges of `C_i`. -/
def partEmitVertStep (d : PartEmitVertEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let u ← Memory.read (env.bufBase + 3 * env.n + cur.idx)
  let startJ ← Memory.read (env.offBase + u)
  let endJ ← Memory.read (env.offBase + u + 1)
  let res ← iterate partEmitEdgeStep
    ⟨env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, env.cid⟩
    (endJ - startJ) ⟨startJ, cur.count⟩
  pure ⟨cur.idx + 1, res.count⟩

/-- Native safety domain for `partEmitVertStep`. -/
def partEmitVertStepSafe (w : ℕ) (d : PartEmitVertEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  let u := s.mem (env.bufBase + 3 * env.n + cur.idx)
  let startJ := s.mem (env.offBase + u)
  let endJ := s.mem (env.offBase + u + 1)
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ env.bufBase + 3 * env.n + cur.idx < s.frontier ∧
    env.offBase + u + 1 < s.frontier ∧ startJ ≤ endJ ∧
    iterationSafe partEmitEdgeStep partEmitEdgeStepSafe w
      ⟨env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, env.cid⟩
      (endJ - startJ) ⟨startJ, cur.count⟩ s

private theorem realizes_partEmitVertStep_history : Realizes .exact
    partEmitVertStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitVertStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitVertStep d)))
    (fun _ _ => 0) := by
  unfold partEmitVertStep
  realize [realizes_partEmitEdgeStep]
  all_goals
    obtain ⟨⟨h16, ht1, hcv_lt, hoff_lt, hle, hiter⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals first
    | exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-- `partEmitVertStep` is uniformly realized with `work = 0`. -/
theorem realizes_partEmitVertStep : Realizes .exact
    partEmitVertStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitVertStepSafe (fun _ _ => 0) :=
  realizes_partEmitVertStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Processes one corrupted edge index from `corrBuf[d.2.idx]`, copying to `M_C` if
`edgeState = 0`. -/
def partEmitCorrStep (d : PartEdgeBufEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let eIdx ← Memory.read (env.bufBase + 14 * env.n + env.m + cur.idx)
  let st ← Memory.read (env.bufBase + 14 * env.n + eIdx)
  if st = 0 then
    Memory.write (env.bufBase + 14 * env.n + eIdx) 2
    partCopyIndexedEdge ⟨env.edgeBase, env.bufBase + 14 * env.n + 6 * env.m, eIdx, cur.count⟩
    pure ⟨cur.idx + 1, cur.count + 1⟩
  else
    pure ⟨cur.idx + 1, cur.count⟩

/-- Native safety domain for `partEmitCorrStep`. -/
def partEmitCorrStepSafe (w : ℕ) (d : PartEdgeBufEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  let eIdx := s.mem (env.bufBase + 14 * env.n + env.m + cur.idx)
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ Fits w (cur.count + 1) ∧
    Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
    env.bufBase + 14 * env.n + env.m + cur.idx < s.frontier ∧
    env.bufBase + 14 * env.n + eIdx < s.frontier ∧
    (s.mem (env.bufBase + 14 * env.n + eIdx) = 0 →
      partCopyIndexedEdgeSafe w
        ⟨env.edgeBase, env.bufBase + 14 * env.n + 6 * env.m, eIdx, cur.count⟩
        ⟨Function.update s.mem (env.bufBase + 14 * env.n + eIdx) 2, s.frontier⟩)

private theorem realizes_partEmitCorrStep_history : Realizes .exact
    partEmitCorrStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitCorrStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitCorrStep d)))
    (fun _ _ => 0) := by
  unfold partEmitCorrStep
  realize [realizes_partCopyIndexedEdge]
  all_goals
    obtain ⟨⟨h16, ht1, hmc1, _, hcb_lt, hst_lt, hcopy⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partEmitCorrStep` is uniformly realized with `work = 0`. -/
theorem realizes_partEmitCorrStep : Realizes .exact
    partEmitCorrStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitCorrStepSafe (fun _ _ => 0) :=
  realizes_partEmitCorrStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Copies `compVerts[d.2.idx]` to `cLiftAll[d.2.count]` and marks `dead[v] := 1`. -/
def partMarkDeadStep (d : PartMarkDeadEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let v ← Memory.read (env.bufBase + 3 * env.n + cur.idx)
  Memory.write (env.bufBase + 4 * env.n + cur.count) v
  Memory.write (env.bufBase + v) 1
  pure ⟨cur.idx + 1, cur.count + 1⟩

/-- Native safety domain for `partMarkDeadStep`. -/
def partMarkDeadStepSafe (w : ℕ) (d : PartMarkDeadEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  let v := s.mem (env.bufBase + 3 * env.n + cur.idx)
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ Fits w (cur.count + 1) ∧
    env.bufBase + 3 * env.n + cur.idx < s.frontier ∧
    env.bufBase + 4 * env.n + cur.count < s.frontier ∧
    env.bufBase + v < s.frontier

private theorem realizes_partMarkDeadStep_history : Realizes .exact
    partMarkDeadStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partMarkDeadStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partMarkDeadStep d)))
    (fun _ _ => 0) := by
  unfold partMarkDeadStep
  realize
  all_goals
    obtain ⟨⟨h16, ht1, hl1, hcv_lt, hcl_lt, hd_lt⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

/-- `partMarkDeadStep` is uniformly realized with `work = 0`. -/
theorem realizes_partMarkDeadStep : Realizes .exact
    partMarkDeadStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partMarkDeadStepSafe (fun _ _ => 0) :=
  realizes_partMarkDeadStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Writes stride-3 component metadata and stride-1 lift pointer for round `d.numComps`. -/
def partWriteRoundMeta (d : PartWriteRoundMetaArgs) : Memory.Prog Unit := do
  Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps) d.numVerts
  Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps + 1) d.numLocalEdges
  Memory.write (d.bufBase + 6 * d.n + 3 * d.numComps + 2) d.cEdgeBase
  Memory.write (d.bufBase + 9 * d.n + d.numComps) d.cLiftBase

/-- Native safety domain for `partWriteRoundMeta`. -/
def partWriteRoundMetaSafe (w : ℕ) (d : PartWriteRoundMetaArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.bufBase + 6 * d.n + 3 * d.numComps + 2 < s.frontier ∧
    d.bufBase + 9 * d.n + d.numComps < s.frontier

/-- `partWriteRoundMeta` is uniformly realized with `work = 0`. -/
theorem realizes_partWriteRoundMeta : Realizes .exact
    partWriteRoundMeta WordEncoding.encode WordEncoding.encode
    partWriteRoundMetaSafe (fun _ _ => 0) := by
  unfold partWriteRoundMeta
  realize
  all_goals
    have h16 := h.1
    have hcm_lt := h.2.1
    have hlm_lt := h.2.2
    have hfront := hmem.frontier_fits
    fits

/-- Emits component `C_i` edges from `liveCount` live vertices (`d.size` or `d.size - 1`). -/
def partEmitComp (d : PartEmitCompArgs) : Memory.Prog PartCursor := do
  if d.hitPrev = 0 then
    iterate partEmitVertStep d.env d.size ⟨0, d.cEdgeLen⟩
  else
    iterate partEmitVertStep d.env (d.size - 1) ⟨0, d.cEdgeLen⟩

/-- Native safety domain for `partEmitComp`. -/
def partEmitCompSafe (w : ℕ) (d : PartEmitCompArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ (d.hitPrev ≠ 0 → 1 ≤ d.size) ∧
    iterationSafe partEmitVertStep partEmitVertStepSafe w d.env
      (if d.hitPrev = 0 then d.size else d.size - 1) ⟨0, d.cEdgeLen⟩ s

/-- `partEmitComp` is uniformly realized with `work = 0`. -/
theorem realizes_partEmitComp : Realizes .exact
    partEmitComp WordEncoding.encode WordEncoding.encode
    partEmitCompSafe (fun _ _ => 0) := by
  unfold partEmitComp
  realize [realizes_partEmitVertStep]
  all_goals
    obtain ⟨h16, hsub, hiter⟩ := h
    have hfront := hmem.frontier_fits
    first
    | (simp only [hc, ↓reduceIte] at hiter
       exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs))
    | exact hsub hc

/-- Runs `partEmitCorrStep` over `d.numCorr` collected corrupted edges. -/
def partEmitCorrLoop (d : PartEmitCorrLoopArgs) : Memory.Prog PartCursor :=
  iterate partEmitCorrStep d.env d.numCorr ⟨0, d.mcLen⟩

/-- Native safety domain for `partEmitCorrLoop`. -/
def partEmitCorrLoopSafe (w : ℕ) (d : PartEmitCorrLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    iterationSafe partEmitCorrStep partEmitCorrStepSafe w d.env d.numCorr ⟨0, d.mcLen⟩ s

/-- `partEmitCorrLoop` is uniformly realized with `work = 0`. -/
theorem realizes_partEmitCorrLoop : Realizes .exact
    partEmitCorrLoop WordEncoding.encode WordEncoding.encode
    partEmitCorrLoopSafe (fun _ _ => 0) := by
  unfold partEmitCorrLoop
  realize [realizes_partEmitCorrStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Runs `partMarkDeadStep` over `d.size` round vertices. -/
def partMarkDeadLoop (d : PartMarkDeadLoopArgs) : Memory.Prog PartCursor :=
  iterate partMarkDeadStep d.env d.size ⟨0, d.cLiftLen⟩

/-- Native safety domain for `partMarkDeadLoop`. -/
def partMarkDeadLoopSafe (w : ℕ) (d : PartMarkDeadLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    iterationSafe partMarkDeadStep partMarkDeadStepSafe w d.env d.size ⟨0, d.cLiftLen⟩ s

/-- `partMarkDeadLoop` is uniformly realized with `work = 0`. -/
theorem realizes_partMarkDeadLoop : Realizes .exact
    partMarkDeadLoop WordEncoding.encode WordEncoding.encode
    partMarkDeadLoopSafe (fun _ _ => 0) := by
  unfold partMarkDeadLoop
  realize [realizes_partMarkDeadStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Finalizes one dynamic-DJP round: emits `C_i`, collects/emits `M_i`, records `lift_i` and
dead vertices, writes round metadata, and resets `firstRoot := 0` for the next round. -/
def partRoundFinish (d : PartRoundFinishArgs) : Memory.Prog PartOuterState := do
  let env := d.env
  let outer := d.outer
  let djp := d.djp
  let cRes ← partEmitComp
    ⟨⟨env.offBase, env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, outer.numComps + 1⟩,
      djp.hitPrev, djp.size, outer.cEdgeLen⟩
  let numCorr ← shCollectCorrupted (djp.sh, d.nc0, env.corrBufBase, 0, 2 * env.m)
  let mRes ← partEmitCorrLoop
    ⟨⟨env.edgeBase, env.bufBase, env.n, env.m⟩, numCorr, outer.mcLen⟩
  let lRes ← partMarkDeadLoop ⟨⟨env.bufBase, env.n⟩, djp.size, outer.cLiftLen⟩
  partWriteRoundMeta
    ⟨env.bufBase, env.n, outer.numComps, djp.size, cRes.count - outer.cEdgeLen,
      env.cEdgesBase + 4 * outer.cEdgeLen, env.cLiftBase + outer.cLiftLen⟩
  pure ⟨outer.u + 1, outer.numComps + 1, cRes.count, lRes.count, mRes.count, djp.tLen,
    ⟨djp.sh.itemBase, djp.sh.nodeBase, 0, djp.sh.itemCount, djp.sh.nodeCount,
      djp.sh.rankThreshold⟩⟩

/-- Native safety domain for `partRoundFinish`. -/
def partRoundFinishSafe (w : ℕ) (d : PartRoundFinishArgs) (s : Memory.State) : Prop :=
  let env := d.env
  let outer := d.outer
  let djp := d.djp
  let emitArgs : PartEmitCompArgs :=
    ⟨⟨env.offBase, env.adjBase, env.edgeBase, env.bufBase, env.n, env.m, outer.numComps + 1⟩,
      djp.hitPrev, djp.size, outer.cEdgeLen⟩
  let s₁ := (Memory.spec 0).clientState s (partEmitComp emitArgs)
  let cRes := (Memory.spec 0).clientResult s (partEmitComp emitArgs)
  let corrArgs := (djp.sh, d.nc0, env.corrBufBase, 0, 2 * env.m)
  let numCorr := (Memory.spec 0).clientResult s₁ (shCollectCorrupted corrArgs)
  let s₂ := (Memory.spec 0).clientState s₁ (shCollectCorrupted corrArgs)
  let mcArgs : PartEmitCorrLoopArgs :=
    ⟨⟨env.edgeBase, env.bufBase, env.n, env.m⟩, numCorr, outer.mcLen⟩
  let s₃ := (Memory.spec 0).clientState s₂ (partEmitCorrLoop mcArgs)
  let deadArgs : PartMarkDeadLoopArgs := ⟨⟨env.bufBase, env.n⟩, djp.size, outer.cLiftLen⟩
  let s₄ := (Memory.spec 0).clientState s₃ (partMarkDeadLoop deadArgs)
  Fits w 16 ∧ Fits w (outer.u + 1) ∧ Fits w (outer.numComps + 1) ∧ Fits w (2 * env.m) ∧
    outer.cEdgeLen ≤ cRes.count ∧
    Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
    Fits w (env.cEdgesBase + 4 * outer.cEdgeLen) ∧
    Fits w (env.cLiftBase + outer.cLiftLen) ∧
    partEmitCompSafe w emitArgs s ∧
    shCollectCorruptedSafe w corrArgs s₁ ∧
    partEmitCorrLoopSafe w mcArgs s₂ ∧
    partMarkDeadLoopSafe w deadArgs s₃ ∧
    partWriteRoundMetaSafe w
      ⟨env.bufBase, env.n, outer.numComps, djp.size, cRes.count - outer.cEdgeLen,
        env.cEdgesBase + 4 * outer.cEdgeLen, env.cLiftBase + outer.cLiftLen⟩ s₄

/-- `partRoundFinish` is uniformly realized with `work = 0`. -/
theorem realizes_partRoundFinish : Realizes .exact
    partRoundFinish WordEncoding.encode WordEncoding.encode
    partRoundFinishSafe (fun _ _ => 0) := by
  unfold partRoundFinish
  realize [realizes_partEmitComp, realizes_shCollectCorrupted,
    realizes_partEmitCorrLoop, realizes_partMarkDeadLoop, realizes_partWriteRoundMeta]
  all_goals first
    | exact h.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.2.2.1
    | exact h.2.2.2.2.1
    | exact h.2.2.2.2.2.2.2.2.2.2.2.2
    | (have h16 := h.1; have hu1 := h.2.1; have hnc1 := h.2.2.1;
       have h2m := h.2.2.2.1; have hce := h.2.2.2.2.1;
       have hbuf := h.2.2.2.2.2.1; have hcep := h.2.2.2.2.2.2.1;
       have hclp := h.2.2.2.2.2.2.2.1; have hfront := hmem.frontier_fits; fits)

/-! ## Round Initialization, DJP While Loop, Outer Loop, and Setup -/

/-- Initializes a new dynamic-DJP round at root `d.u` and expands `d.u` when
`1 < d.env.maxsize`. -/
def partRoundInit (d : PartExpandVertexArgs) : Memory.Prog SHHandle := do
  let n := d.env.n
  let bufBase := d.env.bufBase
  Memory.write (bufBase + 3 * n) d.u
  Memory.write (bufBase + n + d.u) d.cid
  Memory.write (bufBase + 2 * n + d.u) 0
  if d.env.maxsize ≤ 1 then pure d.sh
  else partExpandVertex d

/-- Native safety domain for `partRoundInit`. -/
def partRoundInitSafe (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) : Prop :=
  let n := d.env.n
  let bufBase := d.env.bufBase
  let s₁ : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
    (bufBase + 3 * n) d.u) (bufBase + n + d.u) d.cid) (bufBase + 2 * n + d.u) 0, s.frontier⟩
  Fits w 16 ∧ bufBase + 3 * n < s.frontier ∧ bufBase + n + d.u < s.frontier ∧
    bufBase + 2 * n + d.u < s.frontier ∧
    (¬(d.env.maxsize ≤ 1) → partExpandVertexSafe w d s₁)

private theorem realizes_partRoundInit_history : Realizes .exact
    partRoundInit WordEncoding.encode WordEncoding.encode
    (fun w d s => partRoundInitSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partRoundInit d)))
    (fun _ _ => 0) := by
  unfold partRoundInit
  realize [realizes_partExpandVertex]
  all_goals
    obtain ⟨⟨h16, h1, h2, h3, hexp⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.write, Memory.step_write, Memory.valid]
  all_goals first | exact hexp (by omega) | fits

/-- `partRoundInit` is uniformly realized with `work = 0`. -/
theorem realizes_partRoundInit : Realizes .exact
    partRoundInit WordEncoding.encode WordEncoding.encode
    partRoundInitSafe (fun _ _ => 0) :=
  realizes_partRoundInit_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Unfolding equation for `partRoundInit`. -/
theorem partRoundInit_def (d : PartExpandVertexArgs) : partRoundInit d =
    (Memory.write (d.env.bufBase + 3 * d.env.n) d.u >>= fun _ =>
      Memory.write (d.env.bufBase + d.env.n + d.u) d.cid >>= fun _ =>
        Memory.write (d.env.bufBase + 2 * d.env.n + d.u) 0 >>= fun _ =>
          if d.env.maxsize ≤ 1 then pure d.sh else partExpandVertex d) := by
  unfold partRoundInit
  rfl

/-- Unfolding equation for `partRoundInitSafe`. -/
theorem partRoundInitSafe_def (w : ℕ) (d : PartExpandVertexArgs) (s : Memory.State) :
    partRoundInitSafe w d s =
      (let s₁ : Memory.State := ⟨Function.update (Function.update (Function.update s.mem
        (d.env.bufBase + 3 * d.env.n) d.u) (d.env.bufBase + d.env.n + d.u) d.cid)
        (d.env.bufBase + 2 * d.env.n + d.u) 0, s.frontier⟩
      Fits w 16 ∧ d.env.bufBase + 3 * d.env.n < s.frontier ∧
        d.env.bufBase + d.env.n + d.u < s.frontier ∧
        d.env.bufBase + 2 * d.env.n + d.u < s.frontier ∧
        (¬(d.env.maxsize ≤ 1) → partExpandVertexSafe w d s₁)) := by
  unfold partRoundInitSafe
  rfl

/-- Bounded while loop growing one dynamic-DJP component starting from expanded root `u`. -/
def partDjpLoop (d : PartDjpLoopArgs) : Memory.Prog PartDjpState := do
  if d.env.maxsize ≤ 1 then pure ⟨0, 0, 1, d.tLen, d.sh⟩
  else boundedWhile (fun _ (s : PartDjpState) => s.cont ≠ 0)
         partDjpStep ⟨d.env, d.cid⟩ (2 * d.env.m + 1) ⟨1, 0, 1, d.tLen, d.sh⟩

/-- Native safety domain for `partDjpLoop`. -/
def partDjpLoopSafe (w : ℕ) (d : PartDjpLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    (¬(d.env.maxsize ≤ 1) →
      whileSafe (fun _ (s : PartDjpState) => s.cont ≠ 0)
        partDjpStep partDjpStepSafe w ⟨d.env, d.cid⟩ (2 * d.env.m + 1)
        ⟨1, 0, 1, d.tLen, d.sh⟩ s)

/-- `partDjpLoop` is uniformly realized with `work = 0`. -/
theorem realizes_partDjpLoop : Realizes .exact
    partDjpLoop WordEncoding.encode WordEncoding.encode
    partDjpLoopSafe (fun _ _ => 0) := by
  unfold partDjpLoop
  realize [realizes_partDjpStep]
  all_goals first
    | (have h16 := h.1; fits)
    | (intro _; exact whileSafe_imp (fun _ (s : PartDjpState) => s.cont ≠ 0)
        (fun _ (s : PartDjpState) => s.cont ≠ 0)
        (safe := partDjpStepSafe)
        (safe' := fun w x s => partDjpStepSafe w (⟨d.env, d.cid⟩, x.2) s)
        (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs => hs) (h.2 (by omega)))

/-- Unfolding equation for `partDjpLoop`. -/
theorem partDjpLoop_def (d : PartDjpLoopArgs) : partDjpLoop d =
    (if d.env.maxsize ≤ 1 then pure ⟨0, 0, 1, d.tLen, d.sh⟩
    else boundedWhile (fun _ (s : PartDjpState) => s.cont ≠ 0)
      partDjpStep ⟨d.env, d.cid⟩ (2 * d.env.m + 1) ⟨1, 0, 1, d.tLen, d.sh⟩) := by
  unfold partDjpLoop
  rfl

/-- Unfolding equation for `partDjpLoopSafe`. -/
theorem partDjpLoopSafe_def (w : ℕ) (d : PartDjpLoopArgs) (s : Memory.State) :
    partDjpLoopSafe w d s =
      (Fits w 16 ∧ (¬(d.env.maxsize ≤ 1) →
        whileSafe (fun _ (s : PartDjpState) => s.cont ≠ 0)
          partDjpStep partDjpStepSafe w ⟨d.env, d.cid⟩ (2 * d.env.m + 1)
          ⟨1, 0, 1, d.tLen, d.sh⟩ s)) := by
  unfold partDjpLoopSafe
  rfl

/-- Executes one full dynamic-DJP round starting from live root `d.2.u`. -/
def partRunRound (d : PartEnv × PartOuterState) : Memory.Prog PartOuterState := do
  let env := d.1
  let st := d.2
  let h0 ← partRoundInit ⟨env, st.numComps + 1, st.u, st.sh⟩
  let st1 ← partDjpLoop ⟨env, st.numComps + 1, st.tLen, h0⟩
  partRoundFinish ⟨env, st, st.sh.nodeCount, st1⟩

/-- Native safety domain for `partRunRound`. -/
def partRunRoundSafe (w : ℕ) (d : PartEnv × PartOuterState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  let initArgs : PartExpandVertexArgs := ⟨env, st.numComps + 1, st.u, st.sh⟩
  let h0 := (Memory.spec 0).clientResult s (partRoundInit initArgs)
  let s₁ := (Memory.spec 0).clientState s (partRoundInit initArgs)
  let loopArgs : PartDjpLoopArgs := ⟨env, st.numComps + 1, st.tLen, h0⟩
  let st1 := (Memory.spec 0).clientResult s₁ (partDjpLoop loopArgs)
  let s₂ := (Memory.spec 0).clientState s₁ (partDjpLoop loopArgs)
  Fits w 16 ∧ Fits w (st.numComps + 1) ∧ partRoundInitSafe w initArgs s ∧
    partDjpLoopSafe w loopArgs s₁ ∧
    partRoundFinishSafe w ⟨env, st, st.sh.nodeCount, st1⟩ s₂

/-- `partRunRound` is uniformly realized with `work = 0`. -/
theorem realizes_partRunRound : Realizes .exact
    partRunRound (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partRunRoundSafe (fun _ _ => 0) := by
  unfold partRunRound
  realize [realizes_partRoundInit, realizes_partDjpLoop, realizes_partRoundFinish]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2.1
    | exact h.2.2.2.2
    | (have h16 := h.1; have hnc1 := h.2.1; fits)

/-- Outer vertex scan step: skips already-claimed vertices (`dead[u] ≠ 0`), otherwise runs a
dynamic-DJP round starting at `u`. -/
def partOuterStep (d : PartEnv × PartOuterState) : Memory.Prog PartOuterState := do
  let env := d.1
  let st := d.2
  let dead ← Memory.read (env.bufBase + st.u)
  if dead ≠ 0 then
    pure ⟨st.u + 1, st.numComps, st.cEdgeLen, st.cLiftLen, st.mcLen, st.tLen, st.sh⟩
  else
    partRunRound d

/-- Native safety domain for `partOuterStep`. -/
def partOuterStepSafe (w : ℕ) (d : PartEnv × PartOuterState) (s : Memory.State) : Prop :=
  let env := d.1
  let st := d.2
  Fits w 16 ∧ Fits w (st.u + 1) ∧ env.bufBase + st.u < s.frontier ∧
    (s.mem (env.bufBase + st.u) = 0 → partRunRoundSafe w d s)

private theorem realizes_partOuterStep_history : Realizes .exact
    partOuterStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partOuterStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partOuterStep d)))
    (fun _ _ => 0) := by
  unfold partOuterStep
  realize [realizes_partRunRound]
  all_goals
    obtain ⟨⟨h16, hu1, hd_lt, hrun⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [ne_eq, StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  fits

/-- `partOuterStep` is uniformly realized with `work = 0`. -/
theorem realizes_partOuterStep : Realizes .exact
    partOuterStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partOuterStepSafe (fun _ _ => 0) :=
  realizes_partOuterStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Scans edge `d.2.idx`, copying it to `hRemBase` if still active (`edgeState[idx] = 0`). -/
def partEmitRemStep (d : PartEdgeBufEnv × PartCursor) : Memory.Prog PartCursor := do
  let env := d.1
  let cur := d.2
  let st ← Memory.read (env.bufBase + 14 * env.n + cur.idx)
  if st = 0 then
    partCopyIndexedEdge ⟨env.edgeBase, env.bufBase + 14 * env.n + 10 * env.m, cur.idx, cur.count⟩
    pure ⟨cur.idx + 1, cur.count + 1⟩
  else
    pure ⟨cur.idx + 1, cur.count⟩

/-- Native safety domain for `partEmitRemStep`. -/
def partEmitRemStepSafe (w : ℕ) (d : PartEdgeBufEnv × PartCursor) (s : Memory.State) : Prop :=
  let env := d.1
  let cur := d.2
  Fits w 16 ∧ Fits w (cur.idx + 1) ∧ Fits w (cur.count + 1) ∧
    Fits w (env.bufBase + 14 * env.n + 14 * env.m) ∧
    env.bufBase + 14 * env.n + cur.idx < s.frontier ∧
    (s.mem (env.bufBase + 14 * env.n + cur.idx) = 0 →
      partCopyIndexedEdgeSafe w
        ⟨env.edgeBase, env.bufBase + 14 * env.n + 10 * env.m, cur.idx, cur.count⟩ s)

private theorem realizes_partEmitRemStep_history : Realizes .exact
    partEmitRemStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    (fun w d s => partEmitRemStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partEmitRemStep d)))
    (fun _ _ => 0) := by
  unfold partEmitRemStep
  realize [realizes_partCopyIndexedEdge]
  all_goals
    obtain ⟨⟨h16, he1, hr1, _, hst_lt, hcopy⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn,
      Memory.read, Memory.step_read, Memory.valid]
  all_goals fits

/-- `partEmitRemStep` is uniformly realized with `work = 0`. -/
theorem realizes_partEmitRemStep : Realizes .exact
    partEmitRemStep (appendWords WordEncoding.encode WordEncoding.encode) WordEncoding.encode
    partEmitRemStepSafe (fun _ _ => 0) :=
  realizes_partEmitRemStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

/-- Allocates and zero-initializes CSR, Soft-Heap pool (`rankThreshold = 8`), and partition
workspace arrays using `buildUndirCSR`, `allocPool`, and `fillConstProg`. -/
def partSetup (d : PartSetupArgs) : Memory.Prog PartSetupResult := do
  let csr ← buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩
  let pool ← allocPool (2 * d.m) (4 * d.m)
  let bufBase ← Memory.allocDirty (14 * d.n + 14 * d.m)
  fillConstProg bufBase 0 (2 * d.n)
  fillConstProg (bufBase + 14 * d.n) 0 d.m
  pure ⟨⟨d.n, d.m, d.edgeBase, d.maxsize, csr.offBase, csr.adjBase, bufBase⟩,
    ⟨pool.1, pool.2, 0, 0, 0, partRankThreshold⟩⟩

/-- Native safety domain for `partSetup`. -/
def partSetupSafe (w : ℕ) (d : PartSetupArgs) (s : Memory.State) : Prop :=
  let s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩)
  let s₂ := (Memory.spec 0).clientState s₁ (allocPool (2 * d.m) (4 * d.m))
  let bufBase := s₂.frontier
  Fits w 16 ∧
    d.edgeBase + 4 * d.m ≤ s.frontier ∧
    Fits w (s.frontier + (2 * d.n + 4 * d.m + 1)) ∧
    (∀ j < d.m,
      s.mem (d.edgeBase + 4 * j) < d.n ∧ s.mem (d.edgeBase + 4 * j + 1) < d.n) ∧
    Fits w (s₁.frontier + 3 * (2 * d.m + 1) + 12 * (4 * d.m + 1) + 16) ∧
    Fits w (bufBase + (14 * d.n + 14 * d.m)) ∧
    Fits w (2 * d.n) ∧ Fits w d.m

/-- `partSetup` is uniformly realized with `work = 0`. -/
theorem realizes_partSetup : Realizes .exact
    partSetup WordEncoding.encode WordEncoding.encode
    partSetupSafe (fun _ _ => 0) := by
  unfold partSetup
  realize [realizes_buildUndirCSR, realizes_allocPool, realizes_fillConstProg]
  all_goals
    obtain ⟨h16, hin_lt, hfit_csr, hedges, hfit_pool, hfit_buf, h2n, hm⟩ := h
    have hfront := hmem.frontier_fits
    have hrt : partRankThreshold = 8 := rfl
    let s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩)
    let s₂ := (Memory.spec 0).clientState s₁ (allocPool (2 * d.m) (4 * d.m))
    let s₃ : Memory.State := ⟨s₂.mem, s₂.frontier + (14 * d.n + 14 * d.m)⟩
    have hfr_z1 : s₂.frontier + (14 * d.n + 14 * d.m) ≤
        ((Memory.spec 0).clientState s₃ (fillConstProg s₂.frontier 0 (2 * d.n))).frontier :=
      Memory.frontier_le_clientState s₃ (fillConstProg s₂.frontier 0 (2 * d.n))
    first
    | exact h16
    | exact hin_lt
    | exact hfit_csr
    | exact hedges
    | exact hfit_pool
    | exact h16.of_le (by omega)
    | exact h2n
    | (dsimp only [s₁, s₂, s₃] at hfr_z1 ⊢; omega)
    | fits

/-- Unfolding equation for `partSetup`. -/
theorem partSetup_def (d : PartSetupArgs) : partSetup d =
    (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩ >>= fun csr =>
      allocPool (2 * d.m) (4 * d.m) >>= fun pool =>
        Memory.allocDirty (14 * d.n + 14 * d.m) >>= fun bufBase =>
          fillConstProg bufBase 0 (2 * d.n) >>= fun _ =>
            fillConstProg (bufBase + 14 * d.n) 0 d.m >>= fun _ =>
              pure ⟨⟨d.n, d.m, d.edgeBase, d.maxsize, csr.offBase, csr.adjBase, bufBase⟩,
                ⟨pool.1, pool.2, 0, 0, 0, partRankThreshold⟩⟩) := by
  unfold partSetup
  rfl

/-- Unfolding equation for `partSetupSafe`. -/
theorem partSetupSafe_def (w : ℕ) (d : PartSetupArgs) (s : Memory.State) :
    partSetupSafe w d s =
      (let s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨d.n, d.m, d.edgeBase⟩)
      let s₂ := (Memory.spec 0).clientState s₁ (allocPool (2 * d.m) (4 * d.m))
      Fits w 16 ∧ d.edgeBase + 4 * d.m ≤ s.frontier ∧
        Fits w (s.frontier + (2 * d.n + 4 * d.m + 1)) ∧
        (∀ j < d.m,
          s.mem (d.edgeBase + 4 * j) < d.n ∧ s.mem (d.edgeBase + 4 * j + 1) < d.n) ∧
        Fits w (s₁.frontier + 3 * (2 * d.m + 1) + 12 * (4 * d.m + 1) + 16) ∧
        Fits w (s₂.frontier + (14 * d.n + 14 * d.m)) ∧ Fits w (2 * d.n) ∧ Fits w d.m) := by
  unfold partSetupSafe
  rfl

/-- Runs the outer vertex scan across `0 .. d.env.n - 1`. -/
def partRunOuterLoop (d : PartSetupResult) : Memory.Prog PartOuterState :=
  iterate partOuterStep d.env d.env.n ⟨0, 0, 0, 0, 0, 0, d.sh⟩

/-- Native safety domain for `partRunOuterLoop`. -/
def partRunOuterLoopSafe (w : ℕ) (d : PartSetupResult) (s : Memory.State) : Prop :=
  Fits w 16 ∧
    iterationSafe partOuterStep partOuterStepSafe w d.env d.env.n ⟨0, 0, 0, 0, 0, 0, d.sh⟩ s

/-- `partRunOuterLoop` is uniformly realized with `work = 0`. -/
theorem realizes_partRunOuterLoop : Realizes .exact
    partRunOuterLoop WordEncoding.encode WordEncoding.encode
    partRunOuterLoopSafe (fun _ _ => 0) := by
  unfold partRunOuterLoop
  realize [realizes_partOuterStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Runs the post-loop scan collecting remaining active edges into `hRemBase`. -/
def partRunRemLoop (d : PartEdgeBufEnv) : Memory.Prog PartCursor :=
  iterate partEmitRemStep d d.m ⟨0, 0⟩

/-- Native safety domain for `partRunRemLoop`. -/
def partRunRemLoopSafe (w : ℕ) (d : PartEdgeBufEnv) (s : Memory.State) : Prop :=
  Fits w 16 ∧ iterationSafe partEmitRemStep partEmitRemStepSafe w d d.m ⟨0, 0⟩ s

/-- `partRunRemLoop` is uniformly realized with `work = 0`. -/
theorem realizes_partRunRemLoop : Realizes .exact
    partRunRemLoop WordEncoding.encode WordEncoding.encode
    partRunRemLoopSafe (fun _ _ => 0) := by
  unfold partRunRemLoop
  realize [realizes_partEmitRemStep]
  exact h.2

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
