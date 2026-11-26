/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test suite for Word-RAM MSF indexed edges and CSR)

import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.Common

/-!
# Tests for Word-RAM Minimum Spanning Forest Indexed Edges and CSR

Exercises the public `*_spec` and `realizes_*` interfaces of `initIndexedEdges`, `emitMSFEdges`,
`emitIndexedEdgesFromIdxs`, and `buildUndirCSR` under `module` encapsulation on concrete
graphs, disconnected components, isolated vertices, and `m = 0` boundary witnesses.
-/

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsCSR

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest

/-! ## `IndexedEdges`: Raw-to-Indexed Initialization and Selected Emission -/

-- `initIndexedEdges` on a 3-edge triangle: output base, frontier, cost, `ValidHistory`,
-- preserved raw prefix, decoded stride-4 edges, and `realizes_initIndexedEdges`.
example :
    let rawEdges3 : List (WeightedEdge 3 ℕ) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 10⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 20⟩,
       ⟨⟨2, by decide⟩, ⟨0, by decide⟩, 5⟩]
    let s0 := mkInitRawState rawEdges3
    let r := execWordRAM s0 (initIndexedEdges 0 3)
    r.1 = 9 ∧ r.2.1.frontier = 21 ∧ r.2.2 ≤ 8 * 3 + 1 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (initIndexedEdges 0 3)) ∧
    readRawEdges 0 3 r.2.1.mem = [(0, 1, 10), (1, 2, 20), (2, 0, 5)] ∧
    readIndexedEdges r.1 3 r.2.1.mem = [(0, 1, 10, 0), (1, 2, 20, 1), (2, 0, 5, 2)] ∧
    Realizes .exact (fun d : ℕ × ℕ => initIndexedEdges d.1 d.2)
      WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ d.1 + 3 * d.2 ≤ s.frontier ∧ Fits w (s.frontier + 4 * d.2))
      (fun _ _ => 0) := by
  intro rawEdges3 s0 r
  dsimp only [r, s0, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitRawState_spec (w := 16) rawEdges3 (by decide) (by decide)
    (fun e he => by simp only [rawEdges3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> decide)
  have hft := initIndexedEdges_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hrawLen : rawEdges3.length = 3 := rfl
  rw [hrawLen] at hft
  obtain ⟨hv, hcost, hmod, hout, hfr, _, hidx⟩ := framedTriple_iff_realization.mp hft
  have hpres : readRawEdges 0 3 r.2.1.mem = [(0, 1, 10), (1, 2, 20), (2, 0, 5)] := by
    dsimp only [r, s0, execWordRAM]
    have hraw' : HoldsRawEdges 0 rawEdges3 r.2.1.mem :=
      hinit.2.2.congr fun a _ ha => hmod.mem_eq_of_not_mem (by rw [hinit.2.1]; omega)
        (Set.notMem_empty _)
    rcases hraw' 0 (by decide) with ⟨h0u, h0v, h0w⟩
    rcases hraw' 1 (by decide) with ⟨h1u, h1v, h1w⟩
    rcases hraw' 2 (by decide) with ⟨h2u, h2v, h2w⟩
    dsimp only [r, s0, execWordRAM] at h0u h0v h0w h1u h1v h1w h2u h2v h2w
    simp only [readRawEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [h0u, h0v, h0w, h1u, h1v, h1w, h2u, h2v, h2w]
    rfl
  have hdec : readIndexedEdges r.1 3 r.2.1.mem = [(0, 1, 10, 0), (1, 2, 20, 1), (2, 0, 5, 2)] := by
    dsimp only [r, s0, execWordRAM]
    rcases hidx 0 (by decide) with ⟨h0u, h0v, h0w, h0i⟩
    rcases hidx 1 (by decide) with ⟨h1u, h1v, h1w, h1i⟩
    rcases hidx 2 (by decide) with ⟨h2u, h2v, h2w, h2i⟩
    simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [h0u, h0v, h0w, h0i, h1u, h1v, h1w, h1i, h2u, h2v, h2w, h2i]
    rfl
  exact ⟨by rw [hout, hinit.2.1]; rfl, by rw [hfr, hinit.2.1]; rfl, hcost, hv, hpres, hdec,
    realizes_initIndexedEdges⟩

-- `initIndexedEdges` on the empty `m = 0` graph boundary.
example :
    let s0 := mkInitRawState ([] : List (WeightedEdge 3 ℕ))
    let r := execWordRAM s0 (initIndexedEdges 0 0)
    r.1 = 0 ∧ r.2.1.frontier = 0 ∧ r.2.2 ≤ 1 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (initIndexedEdges 0 0)) := by
  intro s0 r
  dsimp only [r, s0, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitRawState_spec (w := 16) ([] : List (WeightedEdge 3 ℕ))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := initIndexedEdges_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, hcost, _, hout, hfr, _, _⟩ := framedTriple_iff_realization.mp hft
  exact ⟨by rw [hout, hinit.2.1]; rfl, by rw [hfr, hinit.2.1]; rfl, hcost, hv⟩

-- `emitMSFEdges` emitting selected edges `[2, 0]` from `rawEdges3` and `realizes_emitMSFEdges`.
example :
    let rawEdges3 : List (WeightedEdge 3 ℕ) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 10⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 20⟩,
       ⟨⟨2, by decide⟩, ⟨0, by decide⟩, 5⟩]
    let s0 := mkInitRawState rawEdges3
    let prog : Memory.Prog ℕ := do
      let selBase ← initFromWordsProg [2, 0]
      emitMSFEdges ⟨0, selBase, 2⟩
    let r := execWordRAM s0 prog
    r.1 = 11 ∧ r.2.1.frontier = 18 ∧ r.2.2 ≤ 23 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 prog) ∧
    outputList r.2.1.mem r.1 = [2, 0, 5, 0, 1, 10] ∧
    Realizes .exact emitMSFEdges WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ d.selBase + d.count ≤ s.frontier ∧
        Fits w (s.frontier + (3 * d.count + 1)) ∧
        ∀ j < d.count, d.srcBase + 3 * s.mem (d.selBase + j) + 3 ≤ s.frontier)
      (fun _ _ => 0) := by
  intro rawEdges3 s0 prog r
  dsimp only [r, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitRawState_spec (w := 16) rawEdges3 (by decide) (by decide)
    (fun e he => by simp only [rawEdges3, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> decide)
  have hsel_ft := initFromWordsProg_spec (words := [2, 0]) hinit.1 (by rw [hinit.2.1]; decide)
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl <;> decide)
  have hft : Memory.FramedTriple 16 s0 prog 23 ∅ fun outBase s' =>
      outBase = 11 ∧ s'.frontier = 18 ∧ outputList s'.mem outBase = [2, 0, 5, 0, 1, 10] := by
    have hbind : Memory.FramedTriple 16 s0 prog ([2, 0].length + 1 + 20) ∅ fun outBase s' =>
        outBase = 11 ∧ s'.frontier = 18 ∧ outputList s'.mem outBase = [2, 0, 5, 0, 1, 10] := by
      refine Memory.FramedTriple.bind_same
        (Memory.Triple.mono hsel_ft le_rfl fun selBase t ⟨hm, hb, hfr, hhold, hwf'⟩ => ?_)
      refine ⟨hm, ?_⟩
      have hin' : HoldsRawEdges 0 rawEdges3 t.mem :=
        hinit.2.2.congr fun a _ ha => hm.mem_eq_of_not_mem (by rw [hinit.2.1]; omega)
          (Set.notMem_empty _)
      have hsel_mem : ∀ j (hj : j < ([⟨2, by decide⟩, ⟨0, by decide⟩] :
          List (Fin rawEdges3.length)).length),
          t.mem (selBase + j) = ([⟨2, by decide⟩, ⟨0, by decide⟩] :
            List (Fin rawEdges3.length))[j].val := by
        obtain ⟨h0, h1⟩ := Block.holdsList_cons_iff.mp hhold
        intro j hj
        match j with
        | 0 => exact h0
        | 1 => exact (Block.holdsList_cons_iff.mp h1).1
      have hemit := emitMSFEdges_spec (d := ⟨0, selBase, 2⟩) h16 hwf' hin'
        (by
          have hrawLen : rawEdges3.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hrawLen]; decide)
        hsel_mem
        (by
          have hrawLen : rawEdges3.length = 3 := rfl
          dsimp only; rw [hb, hfr, hinit.2.1, hrawLen]; decide)
        rfl
        (by
          have hrawLen : rawEdges3.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hrawLen]; decide)
      refine Memory.Triple.mono hemit (by dsimp only; omega)
        fun outBase s' ⟨hm2, hout, hfr2, _, hlist⟩ => ?_
      have hrawLen : rawEdges3.length = 3 := rfl
      refine ⟨hm2, by rw [hout, hfr, hinit.2.1, hrawLen]; rfl, ?_, ?_⟩
      · rw [hfr2, hfr, hinit.2.1, hrawLen]
        simp only [List.length_cons, List.length_nil]
      · simpa [rawEdges3, encodeEdges] using hlist
    exact hbind.mono (by decide) fun _ _ hq => hq
  obtain ⟨hv, hcost, _, hout, hfr, hlist⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hout, hfr, hcost, hv, hlist, realizes_emitMSFEdges⟩

-- `emitIndexedEdgesFromIdxs` on `disconnEdges` (`[2, 0]`) and `m = 0` boundaries.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let prog : Memory.Prog ℕ := do
      let selBase ← initFromWordsProg [2, 0]
      emitIndexedEdgesFromIdxs ⟨0, selBase, 2⟩
    let r := execWordRAM s0 prog
    r.1 = 14 ∧ r.2.1.frontier = 22 ∧ r.2.2 ≤ 22 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 prog) ∧
    readIndexedEdges r.1 2 r.2.1.mem = [(3, 4, 2, 102), (0, 1, 3, 100)] ∧
    (let sE := mkInitState ([] : List (IndexedEdge 4))
     let rE := execWordRAM sE (emitIndexedEdgesFromIdxs ⟨0, 0, 0⟩)
     rE.1 = 0 ∧ rE.2.1.frontier = 0 ∧ rE.2.2 ≤ 1 ∧
     (Memory.spec 16).ValidHistory sE
       ((Memory.spec 16).clientHistory sE (emitIndexedEdgesFromIdxs ⟨0, 0, 0⟩))) := by
  intro disconnEdges s0 prog r
  dsimp only [r, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hsel_ft := initFromWordsProg_spec (words := [2, 0]) hinit.1 (by rw [hinit.2.1]; decide)
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl <;> decide)
  have hft : Memory.FramedTriple 16 s0 prog 22 ∅ fun outBase s' =>
      outBase = 14 ∧ s'.frontier = 22 ∧
      HoldsIndexedEdges outBase [disconnEdges[2], disconnEdges[0]] s'.mem := by
    have hbind : Memory.FramedTriple 16 s0 prog ([2, 0].length + 1 + 19) ∅ fun outBase s' =>
        outBase = 14 ∧ s'.frontier = 22 ∧
        HoldsIndexedEdges outBase [disconnEdges[2], disconnEdges[0]] s'.mem := by
      refine Memory.FramedTriple.bind_same
        (Memory.Triple.mono hsel_ft le_rfl fun selBase t ⟨hm, hb, hfr, hhold, hwf'⟩ => ?_)
      refine ⟨hm, ?_⟩
      have hin' : HoldsIndexedEdges 0 disconnEdges t.mem :=
        hinit.2.2.congr fun a _ ha => hm.mem_eq_of_not_mem (by rw [hinit.2.1]; omega)
          (Set.notMem_empty _)
      have hsel_mem : ∀ j (hj : j < ([⟨2, by decide⟩, ⟨0, by decide⟩] :
          List (Fin disconnEdges.length)).length),
          t.mem (selBase + j) = ([⟨2, by decide⟩, ⟨0, by decide⟩] :
            List (Fin disconnEdges.length))[j].val := by
        obtain ⟨h0, h1⟩ := Block.holdsList_cons_iff.mp hhold
        intro j hj
        match j with
        | 0 => exact h0
        | 1 => exact (Block.holdsList_cons_iff.mp h1).1
      have hemit := emitIndexedEdgesFromIdxs_spec (d := ⟨0, selBase, 2⟩) h16 hwf' hin'
        (by
          have hdisLen : disconnEdges.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hdisLen]; omega)
        hsel_mem
        (by
          have hdisLen : disconnEdges.length = 3 := rfl
          dsimp only; rw [hb, hfr, hinit.2.1, hdisLen]
          simp only [List.length_cons, List.length_nil]; omega)
        rfl
        (by
          have hdisLen : disconnEdges.length = 3 := rfl
          dsimp only; rw [hfr, hinit.2.1, hdisLen]; decide)
      refine Memory.Triple.mono hemit (by dsimp only; omega)
        fun outBase s' ⟨hm2, hout, hfr2, _, hedges⟩ => ?_
      have hdisLen : disconnEdges.length = 3 := rfl
      refine ⟨hm2, by rw [hout, hfr, hinit.2.1, hdisLen]; rfl, ?_, ?_⟩
      · rw [hfr2, hfr, hinit.2.1, hdisLen]
        simp only [List.length_cons, List.length_nil]
      · simpa using hedges
    exact hbind.mono (by decide) fun _ _ hq => hq
  obtain ⟨hv, hcost, _, hout, hfr, hedges⟩ := framedTriple_iff_realization.mp hft
  have hdec : readIndexedEdges r.1 2 r.2.1.mem = [(3, 4, 2, 102), (0, 1, 3, 100)] := by
    dsimp only [r, execWordRAM]
    rcases hedges 0 (by decide) with ⟨h0u, h0v, h0w, h0i⟩
    rcases hedges 1 (by decide) with ⟨h1u, h1v, h1w, h1i⟩
    simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [h0u, h0v, h0w, h0i, h1u, h1v, h1w, h1i]
    rfl
  have hinitE := mkInitState_spec (w := 16) ([] : List (IndexedEdge 4))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hftE := emitIndexedEdgesFromIdxs_spec (d := ⟨0, 0, 0⟩)
    (idxs := ([] : List (Fin ([] : List (IndexedEdge 4)).length)))
    h16 hinitE.1 hinitE.2.2 (by rw [hinitE.2.1]; decide) (fun _ hj => by simp at hj)
    (by rw [hinitE.2.1]; decide) rfl (by rw [hinitE.2.1]; decide)
  obtain ⟨hvE, hcostE, _, houtE, hfrE, _, _⟩ := framedTriple_iff_realization.mp hftE
  exact ⟨hout, hfr, hcost, hv, hdec, by simp [houtE, hinitE.2.1], by simp [hfrE, hinitE.2.1],
    hcostE, hvE⟩

/-! ## `CSR`: Undirected Offsets, Half-Edge Slices, and `m = 0` -/

-- `buildUndirCSR` on disconnected 6-vertex graph `disconnEdges` (including isolated vertex `5`),
-- checking `offBase`, `adjBase`, frontier, cost, `ValidHistory`, and `mem_slice_iff`.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let g : GraphSlice := ⟨6, 3, 0⟩
    let r := execWordRAM s0 (buildUndirCSR g)
    r.1.offBase = 12 ∧ r.1.adjBase = 19 ∧ r.2.1.frontier = 37 ∧
    r.2.2 ≤ 16 * 3 + 5 * 6 + 6 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (buildUndirCSR g)) ∧
    HoldsUndirCSR r.1.offBase r.1.adjBase disconnEdges r.2.1.mem ∧
    (0, 0) ∈ (List.range (r.2.1.mem (r.1.offBase + 2) - r.2.1.mem (r.1.offBase + 1))).map
      (fun k =>
        let p := r.2.1.mem (r.1.offBase + 1) + k
        (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))) ∧
    (2, 1) ∈ (List.range (r.2.1.mem (r.1.offBase + 2) - r.2.1.mem (r.1.offBase + 1))).map
      (fun k =>
        let p := r.2.1.mem (r.1.offBase + 1) + k
        (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))) ∧
    ∀ nb eIdx, ¬ (nb, eIdx) ∈
      (List.range (r.2.1.mem (r.1.offBase + 6) - r.2.1.mem (r.1.offBase + 5))).map
        (fun k =>
          let p := r.2.1.mem (r.1.offBase + 5) + k
          (r.2.1.mem (r.1.adjBase + 2 * p), r.2.1.mem (r.1.adjBase + 2 * p + 1))) := by
  intro disconnEdges s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := buildUndirCSR_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen3 : disconnEdges.length = 3 := rfl
  rw [hlen3] at hft
  obtain ⟨hv, hcost, _, hoff, hadj, hfr, _, hcsr⟩ := framedTriple_iff_realization.mp hft
  refine ⟨by rw [hoff, hinit.2.1]; rfl, by rw [hadj, hinit.2.1]; rfl,
    by rw [hfr, hinit.2.1]; rfl, hcost, hv, hcsr, ?_, ?_, ?_⟩
  · exact (hcsr.mem_slice_iff ⟨1, by decide⟩ 0 0).mpr ⟨⟨0, by decide⟩, rfl, .inr ⟨rfl, rfl⟩⟩
  · exact (hcsr.mem_slice_iff ⟨1, by decide⟩ 2 1).mpr ⟨⟨1, by decide⟩, rfl, .inl ⟨rfl, rfl⟩⟩
  · intro nb eIdx hm
    obtain ⟨i, _, h_uv⟩ := (hcsr.mem_slice_iff ⟨5, by decide⟩ nb eIdx).mp hm
    fin_cases i <;> simp [disconnEdges] at h_uv

-- `buildUndirCSR` on empty `m = 0` (`3` isolated vertices) and `realizes_buildUndirCSR`.
example :
    let s0 := mkInitState ([] : List (IndexedEdge 3))
    let g : GraphSlice := ⟨3, 0, 0⟩
    let r := execWordRAM s0 (buildUndirCSR g)
    r.2.1.frontier = 7 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (buildUndirCSR g)) ∧
    (∀ k ≤ 3, r.2.1.mem (r.1.offBase + k) = 0) ∧
    Realizes .exact buildUndirCSR WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (2 * g.numVertices + 4 * g.numEdges + 1)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
  intro s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) ([] : List (IndexedEdge 3))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := buildUndirCSR_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, _, _, _, _, hfr, _, hcsr⟩ := framedTriple_iff_realization.mp hft
  refine ⟨by rw [hfr, hinit.2.1]; rfl, hv, fun k hk => ?_, realizes_buildUndirCSR⟩
  have hle := hcsr.offset_le_end k hk
  simp only [List.length_nil, Nat.mul_zero, Nat.le_zero] at hle
  exact hle

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsCSR
