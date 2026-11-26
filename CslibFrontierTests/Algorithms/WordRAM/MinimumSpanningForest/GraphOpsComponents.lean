/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components

/-!
# Tests for Word-RAM Minimum Spanning Forest Component Operations

Exercises the public `*_spec`, `realizes_*`, and graph-theory bridge interfaces of
`connectedComponentsProg`, `contractEdgesProg`, and `compactVerticesProg` under `module`
encapsulation on disconnected components, isolated vertices, and `m = 0` boundary witnesses.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsComponents

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

private def encodeIndexedEdges {n : ℕ} (es : List (IndexedEdge n)) : List ℕ :=
  es.flatMap fun e => [e.u.val, e.v.val, e.weight, e.id]

private def initFromWordsProg (words : List ℕ) : Memory.Prog ℕ := do
  let blk ← Memory.allocBlockDirty words.length
  Block.writeList blk.base words
  pure blk.base

private theorem initFromWordsProg_spec {w : ℕ} {words : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfit : Fits w (s.frontier + words.length))
    (hwords : ∀ v ∈ words, Fits w v) :
    Memory.FramedTriple w s (initFromWordsProg words) (words.length + 1) ∅ fun base s' =>
      base = s.frontier ∧ s'.frontier = s.frontier + words.length ∧
      Block.HoldsList base words s'.mem ∧ Memory.WellFormed w s' := by
  let s₁ : Memory.State := ⟨s.mem, s.frontier + words.length⟩
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit, hwf.mem_fits⟩
  have hpost : Memory.FramedTriple w s₁
      (Block.writeList s.frontier words >>= fun _ => pure s.frontier) words.length
      (Set.Ico s.frontier (s.frontier + words.length)) fun base s' =>
        base = s.frontier ∧ s'.frontier = s.frontier + words.length ∧
        Block.HoldsList base words s'.mem ∧ Memory.WellFormed w s' := by
    refine ((Block.framedTriple_writeList hwf₁ le_rfl hwords).mono le_rfl
      fun _ _ ⟨hfr, hhold, hwf'⟩ =>
        Memory.FramedTriple.pure (c := 0) ⟨rfl, hfr, hhold, hwf'⟩).bind_same
      |>.mono (Nat.add_zero _).le fun _ _ h => h
  refine Memory.Triple.mono (Memory.FramedTriple.allocBlockDirty_bind hfit hpost)
    (by omega) fun _ _ ⟨hm, hq⟩ => ⟨⟨hm.1, fun a ha _ => hm.2 a ha
      (by simp only [Set.mem_Ico, not_and, not_lt]; omega)⟩, hq⟩

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

private def mkInitStateFromWords (words : List ℕ) : Memory.State :=
  (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)

private def mkInitState {n : ℕ} (es : List (IndexedEdge n)) : Memory.State :=
  mkInitStateFromWords (encodeIndexedEdges es)

private theorem mkInitState_spec {w n : ℕ} (es : List (IndexedEdge n))
    (hn : Fits w n) (h4m : Fits w (4 * es.length))
    (hwts : ∀ e ∈ es, Fits w e.weight ∧ Fits w e.id) :
    Memory.WellFormed w (mkInitState es) ∧
    (mkInitState es).frontier = 4 * es.length ∧
    HoldsIndexedEdges 0 es (mkInitState es).mem := by
  have hwf0 : Memory.WellFormed w ⟨fun _ => 0, 0⟩ :=
    ⟨Nat.two_pow_pos w, fun _ => Nat.two_pow_pos w⟩
  have hlen : (encodeIndexedEdges es).length = 4 * es.length := by
    clear hwf0 h4m hwts
    induction es with
    | nil => rfl
    | cons e t ih =>
      have hs : (encodeIndexedEdges (e :: t)).length = 4 + (encodeIndexedEdges t).length := by
        dsimp only [encodeIndexedEdges]
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      rw [hs, ih, List.length_cons]
      omega
  have hfit : Fits w ((⟨fun _ => 0, 0⟩ : Memory.State).frontier +
      (encodeIndexedEdges es).length) := by
    simpa [hlen] using h4m
  have hwords : ∀ v ∈ encodeIndexedEdges es, Fits w v := by
    intro v hv
    simp only [encodeIndexedEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    obtain ⟨e, he, rfl | rfl | rfl | rfl⟩ := hv
    · exact hn.of_le (le_of_lt e.u.isLt)
    · exact hn.of_le (le_of_lt e.v.isLt)
    · exact (hwts e he).1
    · exact (hwts e he).2
  have hft := initFromWordsProg_spec hwf0 hfit hwords
  obtain ⟨_, _, _, hb, hfr, hhold, hwf'⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hwf', ?_, ?_⟩
  · simpa [mkInitState, mkInitStateFromWords, hlen] using hfr
  · rw [hb] at hhold
    exact holdsIndexedEdges_of_holdsList 0 es hhold

private def readIndexedEdges (base count : ℕ) (mem : ℕ → ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range count).map fun i =>
    (mem (base + 4 * i), mem (base + 4 * i + 1), mem (base + 4 * i + 2), mem (base + 4 * i + 3))

private def execWordRAM {α : Type} (s : Memory.State) (prog : Memory.Prog α) :
    α × Memory.State × ℕ :=
  ((Memory.spec 0).clientResult s prog, (Memory.spec 0).clientState s prog, memoryCost prog s)

/-! ## `Components`: BFS Component Count, Edge Contraction, and Vertex Compaction -/

-- `connectedComponentsProg` on `disconnEdges` (`{0,1,2}`, `{3,4}`, `{5}`): `numComps = 3`.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let g : GraphSlice := ⟨6, 3, 0⟩
    let r := execWordRAM s0 (connectedComponentsProg g)
    r.1.compBase = 37 ∧ r.1.numComps = 3 ∧ r.2.1.frontier = 49 ∧
    r.2.2 ≤ 24 * 3 + 13 * 6 + 8 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (connectedComponentsProg g)) ∧
    r.2.1.mem (r.1.compBase + 0) = r.2.1.mem (r.1.compBase + 1) ∧
    r.2.1.mem (r.1.compBase + 1) = r.2.1.mem (r.1.compBase + 2) ∧
    r.2.1.mem (r.1.compBase + 3) = r.2.1.mem (r.1.compBase + 4) ∧
    r.2.1.mem (r.1.compBase + 0) ≠ r.2.1.mem (r.1.compBase + 3) ∧
    r.2.1.mem (r.1.compBase + 0) ≠ r.2.1.mem (r.1.compBase + 5) ∧
    r.2.1.mem (r.1.compBase + 3) ≠ r.2.1.mem (r.1.compBase + 5) := by
  intro disconnEdges s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := connectedComponentsProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen3 : disconnEdges.length = 3 := rfl
  rw [hlen3] at hft
  obtain ⟨hv, hcost, _, hcb, _, hfr, _, _, _, hconn, hnum⟩ := framedTriple_iff_realization.mp hft
  have hnum3 : (edgePartition (disconnEdges.map IndexedEdge.toWeighted)).numComponents = 3 := by
    decide
  refine ⟨by rw [hcb, hinit.2.1]; rfl, hnum.trans hnum3, by rw [hfr, hinit.2.1]; rfl,
    hcost, hv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hconn ⟨0, by decide⟩ ⟨1, by decide⟩).mpr (by decide)
  · exact (hconn ⟨1, by decide⟩ ⟨2, by decide⟩).mpr (by decide)
  · exact (hconn ⟨3, by decide⟩ ⟨4, by decide⟩).mpr (by decide)
  · intro heq; exact absurd ((hconn ⟨0, by decide⟩ ⟨3, by decide⟩).mp heq) (by decide)
  · intro heq; exact absurd ((hconn ⟨0, by decide⟩ ⟨5, by decide⟩).mp heq) (by decide)
  · intro heq; exact absurd ((hconn ⟨3, by decide⟩ ⟨5, by decide⟩).mp heq) (by decide)

-- `connectedComponentsProg` on empty `m = 0` (`4` isolated vertices -> `4` components)
-- plus `realizes_connectedComponentsProg`.
example :
    let s0 := mkInitState ([] : List (IndexedEdge 4))
    let g : GraphSlice := ⟨4, 0, 0⟩
    let r := execWordRAM s0 (connectedComponentsProg g)
    r.1.numComps = 4 ∧ r.2.1.frontier = 17 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (connectedComponentsProg g)) ∧
    (∀ x y : Fin 4, r.2.1.mem (r.1.compBase + x.val) = r.2.1.mem (r.1.compBase + y.val) ↔
      x = y) ∧
    Realizes .exact connectedComponentsProg WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (4 * g.numVertices + 4 * g.numEdges + 1)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
  intro s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) ([] : List (IndexedEdge 4))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := connectedComponentsProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, _, _, _, _, hfr, _, _, _, hconn, hnum⟩ := framedTriple_iff_realization.mp hft
  have hnum4 :
      (edgePartition (([] : List (IndexedEdge 4)).map IndexedEdge.toWeighted)).numComponents =
        4 := by decide
  refine ⟨hnum.trans hnum4, by rw [hfr, hinit.2.1]; rfl, hv, fun x y => ?_,
    realizes_connectedComponentsProg⟩
  rw [hconn x y]
  fin_cases x <;> fin_cases y <;> decide

-- `contractEdgesProg` on `disconnEdges` along `[0, 0, 0, 1, 1, 2]` and
-- `realizes_contractEdgesProg`.
example :
    let disconnEdges : List (IndexedEdge 6) :=
      [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 100⟩,
       ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 101⟩,
       ⟨⟨3, by decide⟩, ⟨4, by decide⟩, 2, 102⟩]
    let s0 := mkInitState disconnEdges
    let prog : Memory.Prog ℕ := do
      let compBase ← initFromWordsProg [0, 0, 0, 1, 1, 2]
      contractEdgesProg ⟨6, 3, 0, compBase⟩
    let r := execWordRAM s0 prog
    r.1 = 18 ∧ r.2.1.frontier = 30 ∧ r.2.2 ≤ 38 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 prog) ∧
    readIndexedEdges r.1 3 r.2.1.mem = [(0, 0, 3, 100), (0, 0, 4, 101), (1, 1, 2, 102)] ∧
    Realizes .exact contractEdgesProg WordEncoding.encode WordEncoding.encode
      (fun w d s => Fits w 16 ∧ Fits w (4 * d.numEdges) ∧ Fits w (s.frontier + 4 * d.numEdges) ∧
        d.numEdges + 1 ≤ 2 ^ w ∧
        (∀ j < d.numEdges, d.edgeBase + 4 * j + 3 < s.frontier ∧
          d.compBase + s.mem (d.edgeBase + 4 * j) < s.frontier ∧
          d.compBase + s.mem (d.edgeBase + 4 * j + 1) < s.frontier))
      (fun _ _ => 0) := by
  intro disconnEdges s0 prog r
  dsimp only [r, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) disconnEdges (by decide) (by decide)
    (fun e he => by simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hcomp_ft := initFromWordsProg_spec (words := [0, 0, 0, 1, 1, 2])
    hinit.1 (by rw [hinit.2.1]; decide)
    (fun v hv => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  let compFn : Fin 6 → ℕ := fun u => [0, 0, 0, 1, 1, 2][u.val]!
  have hft : Memory.FramedTriple 16 s0 prog 38 ∅ fun out s' =>
      out = 18 ∧ s'.frontier = 30 ∧
      ∃ esOut : List (IndexedEdge 3),
        esOut.length = 3 ∧ HoldsIndexedEdges out esOut s'.mem ∧
        (∀ i (hi : i < 3) (hi' : i < esOut.length),
          (esOut[i]'hi').u.val = compFn (disconnEdges[i]'hi).u ∧
          (esOut[i]'hi').v.val = compFn (disconnEdges[i]'hi).v ∧
          (esOut[i]'hi').weight = (disconnEdges[i]'hi).weight ∧
          (esOut[i]'hi').id = (disconnEdges[i]'hi).id) := by
    have hbind : Memory.FramedTriple 16 s0 prog
        ([0, 0, 0, 1, 1, 2].length + 1 + 31) ∅ fun out s' =>
        out = 18 ∧ s'.frontier = 30 ∧
        ∃ esOut : List (IndexedEdge 3),
          esOut.length = 3 ∧ HoldsIndexedEdges out esOut s'.mem ∧
          (∀ i (hi : i < 3) (hi' : i < esOut.length),
            (esOut[i]'hi').u.val = compFn (disconnEdges[i]'hi).u ∧
            (esOut[i]'hi').v.val = compFn (disconnEdges[i]'hi).v ∧
            (esOut[i]'hi').weight = (disconnEdges[i]'hi).weight ∧
            (esOut[i]'hi').id = (disconnEdges[i]'hi).id) := by
      refine Memory.FramedTriple.bind_same
        (Memory.Triple.mono hcomp_ft le_rfl fun compB t ⟨hm, hb, hfr, hhold, hwf'⟩ => ?_)
      refine ⟨hm, ?_⟩
      have hin' : HoldsIndexedEdges 0 disconnEdges t.mem :=
        hinit.2.2.congr fun a _ ha => hm.mem_eq_of_not_mem (by rw [hinit.2.1]; omega)
          (Set.notMem_empty _)
      have hcomp_mem : ∀ u : Fin 6, t.mem (compB + u.val) = compFn u := by
        obtain ⟨h0, h1⟩ := Block.holdsList_cons_iff.mp hhold
        obtain ⟨hv1, h2⟩ := Block.holdsList_cons_iff.mp h1
        obtain ⟨hv2, h3⟩ := Block.holdsList_cons_iff.mp h2
        obtain ⟨hv3, h4⟩ := Block.holdsList_cons_iff.mp h3
        obtain ⟨hv4, h5⟩ := Block.holdsList_cons_iff.mp h4
        obtain ⟨hv5, _⟩ := Block.holdsList_cons_iff.mp h5
        intro u
        fin_cases u
        · exact h0
        · exact hv1
        · exact hv2
        · exact hv3
        · exact hv4
        · exact hv5
      have hcomp_lt : ∀ e ∈ disconnEdges, compFn e.u < 3 ∧ compFn e.v < 3 := by
        intro e he
        simp only [disconnEdges, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
      have hdisLen : disconnEdges.length = 3 := rfl
      have hcon := contractEdgesProg_spec (edgeBase := 0) (compBase := compB) (n' := 3)
        h16 hwf' hin'
        (by rw [hfr, hinit.2.1, hdisLen]; omega)
        hcomp_mem
        (by
          rw [hb, hfr, hinit.2.1, hdisLen]
          simp only [List.length_cons, List.length_nil]
          omega)
        hcomp_lt
        (by rw [hfr, hinit.2.1, hdisLen]; decide)
      refine Memory.Triple.mono hcon (by rw [hdisLen])
        fun out s' ⟨hm2, hout, hfr2, _, esOut, hlen, hedges, hel⟩ => ?_
      refine ⟨hm2, by rw [hout, hfr, hinit.2.1, hdisLen]; rfl, ?_, esOut, hlen, hedges, hel⟩
      rw [hfr2, hfr, hinit.2.1, hdisLen]
      simp only [List.length_cons, List.length_nil]
    exact hbind.mono (by decide) fun _ _ hq => hq
  obtain ⟨hv, hcost, _, hout, hfr, esOut, hlen, hedges, hel⟩ :=
    framedTriple_iff_realization.mp hft
  have hdec : readIndexedEdges r.1 3 r.2.1.mem =
      [(0, 0, 3, 100), (0, 0, 4, 101), (1, 1, 2, 102)] := by
    dsimp only [r, execWordRAM]
    have h0' : 0 < esOut.length := by omega
    have h1' : 1 < esOut.length := by omega
    have h2' : 2 < esOut.length := by omega
    rcases hedges 0 h0' with ⟨m0u, m0v, m0w, m0i⟩
    rcases hedges 1 h1' with ⟨m1u, m1v, m1w, m1i⟩
    rcases hedges 2 h2' with ⟨m2u, m2v, m2w, m2i⟩
    rcases hel 0 (by decide) h0' with ⟨e0u, e0v, e0w, e0i⟩
    rcases hel 1 (by decide) h1' with ⟨e1u, e1v, e1w, e1i⟩
    rcases hel 2 (by decide) h2' with ⟨e2u, e2v, e2w, e2i⟩
    simp only [readIndexedEdges, List.range_succ, List.range_zero, List.nil_append,
      List.map_append, List.map_cons, List.map_nil]
    rw [m0u, m0v, m0w, m0i, m1u, m1v, m1w, m1i, m2u, m2v, m2w, m2i,
      e0u, e0v, e0w, e0i, e1u, e1v, e1w, e1i, e2u, e2v, e2w, e2i]
    rfl
  exact ⟨hout, hfr, hcost, hv, hdec, realizes_contractEdgesProg⟩

-- `compactVerticesProg` on `isolatedEdges` (`6` vertices, isolated `0, 2, 3`):
-- `numVertices = 3`, simplicity, MSF transport, cost bound, and `realizes_compactVerticesProg`.
example :
    let isolatedEdges : List (IndexedEdge 6) :=
      [⟨⟨1, by decide⟩, ⟨4, by decide⟩, 7, 10⟩,
       ⟨⟨4, by decide⟩, ⟨5, by decide⟩, 2, 20⟩]
    let s0 := mkInitState isolatedEdges
    let g : GraphSlice := ⟨6, 2, 0⟩
    let r := execWordRAM s0 (compactVerticesProg g)
    r.1.numVertices = 3 ∧ r.1.liftBase = 8 ∧ r.1.edgeBase = 14 ∧ r.2.1.frontier = 22 ∧
    r.2.2 ≤ 14 * 2 + 3 * 6 + 2 ∧
    (Memory.spec 16).ValidHistory s0 ((Memory.spec 16).clientHistory s0 (compactVerticesProg g)) ∧
    Realizes .exact compactVerticesProg WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (g.numVertices + 4 * g.numEdges + 1)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
  intro isolatedEdges s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) isolatedEdges (by decide) (by decide)
    (fun e he => by simp only [isolatedEdges, List.mem_cons, List.not_mem_nil, or_false] at he
                    rcases he with rfl | rfl <;> exact ⟨by decide, by decide⟩)
  have hft := compactVerticesProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  have hlen2 : isolatedEdges.length = 2 := rfl
  rw [hlen2] at hft
  obtain ⟨hv, hcost, _, hlift, hedge, _, hfr, _, lift, esOut, hinj, hlen, _, _, hact, hmap⟩ :=
    framedTriple_iff_realization.mp hft
  have hnv : r.1.numVertices = 3 := by
    dsimp only [r, s0, g, execWordRAM]
    let S : Finset (Fin 6) := {⟨1, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩}
    have hScard : S.card = 3 := by decide
    have himg : Finset.univ.image lift = S := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨y, rfl⟩
        obtain ⟨e, he, hy⟩ := hact y
        have he' :
            (⟨lift e.u, lift e.v, e.weight, e.id⟩ : IndexedEdge 6) ∈ isolatedEdges := by
          have hmem := List.mem_map_of_mem
            (f := fun e => (⟨lift e.u, lift e.v, e.weight, e.id⟩ : IndexedEdge 6)) he
          rw [hmap] at hmem
          exact hmem
        simp only [isolatedEdges, List.mem_cons, List.not_mem_nil, or_false] at he'
        rcases he' with h0 | h1
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨1, by decide⟩ := congrArg IndexedEdge.u h0
            rw [this]; simp [S]
          · have : lift e.v = ⟨4, by decide⟩ := congrArg IndexedEdge.v h0
            rw [this]; simp [S]
        · rcases hy with rfl | rfl
          · have : lift e.u = ⟨4, by decide⟩ := congrArg IndexedEdge.u h1
            rw [this]; simp [S]
          · have : lift e.v = ⟨5, by decide⟩ := congrArg IndexedEdge.v h1
            rw [this]; simp [S]
      · intro hx
        have hiso : isolatedEdges.length = 2 := rfl
        have hlen0 : 0 < esOut.length := by omega
        have hlen1 : 1 < esOut.length := by omega
        have h0_eq : (⟨lift (esOut[0]'hlen0).u, lift (esOut[0]'hlen0).v,
            (esOut[0]'hlen0).weight, (esOut[0]'hlen0).id⟩ :
            IndexedEdge 6) = isolatedEdges[0] := by
          have := congrArg (fun l => l[0]?) hmap
          simp only [List.getElem?_map, List.getElem?_eq_getElem hlen0,
            List.getElem?_eq_getElem (by decide : 0 < isolatedEdges.length),
            Option.map_some, Option.some.injEq] at this
          exact this
        have h1_eq : (⟨lift (esOut[1]'hlen1).u, lift (esOut[1]'hlen1).v,
            (esOut[1]'hlen1).weight, (esOut[1]'hlen1).id⟩ :
            IndexedEdge 6) = isolatedEdges[1] := by
          have := congrArg (fun l => l[1]?) hmap
          simp only [List.getElem?_map, List.getElem?_eq_getElem hlen1,
            List.getElem?_eq_getElem (by decide : 1 < isolatedEdges.length),
            Option.map_some, Option.some.injEq] at this
          exact this
        simp only [S, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact ⟨_, congrArg IndexedEdge.u h0_eq⟩
        · exact ⟨_, congrArg IndexedEdge.v h0_eq⟩
        · exact ⟨_, congrArg IndexedEdge.v h1_eq⟩
    have hcard := (Finset.card_image_of_injective Finset.univ hinj).trans (Finset.card_fin _)
    exact hcard.symm.trans ((congrArg Finset.card himg).trans hScard)
  have _hsimp_out : IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) := by
    refine compactVertices_isSimple hmap ?_
    rw [isSimple_iff]
    refine ⟨fun i => by fin_cases i <;> decide, fun i₁ i₂ h => ?_⟩
    fin_cases i₁ <;> fin_cases i₂ <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.zero_eq_one_iff,
        Fin.one_eq_zero_iff, Fin.reduceFinMk, List.map_cons, List.map_nil, List.length_cons,
        List.length_nil, zero_add, Nat.reduceAdd, OfNat.ofNat_ne_one] at h ⊢
    all_goals revert h; decide
  have _hmsf_lift : ∀ L_out : List (WeightedEdge r.1.numVertices ℕ),
      IsMinSpanningForest (esOut.map IndexedEdge.toWeighted) L_out →
      IsMinSpanningForest (isolatedEdges.map IndexedEdge.toWeighted)
        (contractEdgeList lift L_out) :=
    fun _ hL => compactVertices_isMinSpanningForest_of_subperm hinj hmap hL
  exact ⟨hnv, by rw [hlift, hinit.2.1]; rfl, by rw [hedge, hinit.2.1]; rfl,
    by rw [hfr, hinit.2.1]; rfl, hcost, hv, realizes_compactVerticesProg⟩

-- `compactVerticesProg` on empty `m = 0` (`4` isolated vertices -> `0` active vertices).
example :
    let s0 := mkInitState ([] : List (IndexedEdge 4))
    let g : GraphSlice := ⟨4, 0, 0⟩
    let r := execWordRAM s0 (compactVerticesProg g)
    r.1.numVertices = 0 ∧ r.2.1.frontier = 4 ∧ r.2.2 ≤ 3 * 4 + 2 ∧
    (Memory.spec 16).ValidHistory s0
      ((Memory.spec 16).clientHistory s0 (compactVerticesProg g)) := by
  intro s0 g r
  dsimp only [r, s0, g, execWordRAM]
  have h16 : Fits 16 16 := by decide
  have hinit := mkInitState_spec (w := 16) ([] : List (IndexedEdge 4))
    (by decide) (by decide) (fun _ h => by simp at h)
  have hft := compactVerticesProg_spec h16 hinit.1 hinit.2.2 (by rw [hinit.2.1]; decide)
    (by rw [hinit.2.1]; decide)
  simp only [List.length_nil, Nat.mul_zero] at hft
  obtain ⟨hv, hcost, _, _, _, _, hfr, _, _, esOut, _, hlen, _, _, hact, _⟩ :=
    framedTriple_iff_realization.mp hft
  have hnv0 : r.1.numVertices = 0 := by
    dsimp only [r, s0, g, execWordRAM]
    by_contra hne
    have hpos : 0 < r.1.numVertices := Nat.pos_of_ne_zero hne
    obtain ⟨e, he, _⟩ := hact ⟨0, hpos⟩
    have hnil : esOut = [] := List.eq_nil_of_length_eq_zero hlen
    rw [hnil] at he
    exact List.not_mem_nil he
  exact ⟨hnv0, by rw [hfr, hinit.2.1]; rfl, hcost, hv⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsComponents
