/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (shared test harness for Word-RAM MSF graph operations)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.CSR

/-!
# Shared Word-RAM Minimum Spanning Forest Test Helpers

Provides reusable test state constructors built on `Block.writeList` and `Memory.allocBlockDirty`,
layout bridges from `Block.HoldsList` to `HoldsIndexedEdges` and `HoldsRawEdges`, memory-slice
decoders (`readIndexedEdges`, `readRawEdges`, `readNatSlice`), and deterministic execution helpers
(`execWordRAM`) shared across Word-RAM MSF test suites.
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-- Flatten `es : List (IndexedEdge n)` into stride-4 words `[u, v, weight, id, ...]`. -/
@[expose] def encodeIndexedEdges {n : ℕ} (es : List (IndexedEdge n)) : List ℕ :=
  es.flatMap fun e => [e.u.val, e.v.val, e.weight, e.id]

/-- Flatten `es : List (WeightedEdge n ℕ)` into stride-3 words `[u, v, weight, ...]`. -/
@[expose] def encodeRawEdges {n : ℕ} (es : List (WeightedEdge n ℕ)) : List ℕ :=
  es.flatMap fun e => [e.u.val, e.v.val, e.weight]

/-- Allocate `words.length` cells and write `words` consecutively via `Block.writeList`. -/
def initFromWordsProg (words : List ℕ) : Memory.Prog ℕ := do
  let blk ← Memory.allocBlockDirty words.length
  Block.writeList blk.base words
  pure blk.base

/-- Framed specification for `initFromWordsProg` allocating and initializing `words`. -/
theorem initFromWordsProg_spec {w : ℕ} {words : List ℕ} {s : Memory.State}
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

private theorem holdsRawEdges_of_holdsList {n : ℕ} (base : ℕ) (es : List (WeightedEdge n ℕ))
    {mem : ℕ → ℕ} (h : Block.HoldsList base (encodeRawEdges es) mem) :
    HoldsRawEdges base es mem := by
  induction es generalizing base with
  | nil => intro i hi; exact absurd hi (Nat.not_lt_zero _)
  | cons e rest ih =>
    simp only [encodeRawEdges, List.flatMap_cons, List.cons_append, List.nil_append] at h
    obtain ⟨hu, h₁⟩ := Block.holdsList_cons_iff.mp h
    obtain ⟨hv, h₂⟩ := Block.holdsList_cons_iff.mp h₁
    obtain ⟨hw, hrest⟩ := Block.holdsList_cons_iff.mp h₂
    rw [show base + 1 + 1 + 1 = base + 3 by omega] at hrest
    have hrest' : HoldsRawEdges (base + 3) rest mem := ih (base + 3) hrest
    intro i hi
    cases i with
    | zero => exact ⟨hu, hv, hw⟩
    | succ k =>
      rcases hrest' k (Nat.lt_of_succ_lt_succ hi) with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [show base + 3 * (k + 1) = base + 3 + 3 * k by omega]; exact h₁
      · rw [show base + 3 * (k + 1) + 1 = base + 3 + 3 * k + 1 by omega]; exact h₂
      · rw [show base + 3 * (k + 1) + 2 = base + 3 + 3 * k + 2 by omega]; exact h₃

/-- Build an initial `Memory.State` containing `words` at `[0, words.length)`,
constructed via `Block.writeList`. -/
def mkInitStateFromWords (words : List ℕ) : Memory.State :=
  (Memory.spec 0).clientState ⟨fun _ => 0, 0⟩ (initFromWordsProg words)

/-- Build an initial `Memory.State` holding `es : List (IndexedEdge n)` at address `0`,
constructed via `Block.writeList`. -/
def mkInitState {n : ℕ} (es : List (IndexedEdge n)) : Memory.State :=
  mkInitStateFromWords (encodeIndexedEdges es)

/-- Build an initial `Memory.State` holding stride-3 `es : List (WeightedEdge n ℕ)` at address `0`,
constructed via `Block.writeList`. -/
def mkInitRawState {n : ℕ} (es : List (WeightedEdge n ℕ)) : Memory.State :=
  mkInitStateFromWords (encodeRawEdges es)

/-- Specification of `mkInitState`: produces a well-formed state at frontier `4 * es.length`
holding `es` at address `0`. -/
theorem mkInitState_spec {w n : ℕ} (es : List (IndexedEdge n))
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

/-- Specification of `mkInitRawState`: produces a well-formed state at frontier `3 * es.length`
holding `es` at address `0`. -/
theorem mkInitRawState_spec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hn : Fits w n) (h3m : Fits w (3 * es.length))
    (hwts : ∀ e ∈ es, Fits w e.weight) :
    Memory.WellFormed w (mkInitRawState es) ∧
    (mkInitRawState es).frontier = 3 * es.length ∧
    HoldsRawEdges 0 es (mkInitRawState es).mem := by
  have hwf0 : Memory.WellFormed w ⟨fun _ => 0, 0⟩ :=
    ⟨Nat.two_pow_pos w, fun _ => Nat.two_pow_pos w⟩
  have hlen : (encodeRawEdges es).length = 3 * es.length := by
    clear hwf0 h3m hwts
    induction es with
    | nil => rfl
    | cons e t ih =>
      have hs : (encodeRawEdges (e :: t)).length = 3 + (encodeRawEdges t).length := by
        dsimp only [encodeRawEdges]
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
      rw [hs, ih, List.length_cons]
      omega
  have hfit : Fits w ((⟨fun _ => 0, 0⟩ : Memory.State).frontier +
      (encodeRawEdges es).length) := by
    simpa [hlen] using h3m
  have hwords : ∀ v ∈ encodeRawEdges es, Fits w v := by
    intro v hv
    simp only [encodeRawEdges, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hv
    obtain ⟨e, he, rfl | rfl | rfl⟩ := hv
    · exact hn.of_le (le_of_lt e.u.isLt)
    · exact hn.of_le (le_of_lt e.v.isLt)
    · exact hwts e he
  have hft := initFromWordsProg_spec hwf0 hfit hwords
  obtain ⟨_, _, _, hb, hfr, hhold, hwf'⟩ := framedTriple_iff_realization.mp hft
  refine ⟨hwf', ?_, ?_⟩
  · simpa [mkInitRawState, mkInitStateFromWords, hlen] using hfr
  · rw [hb] at hhold
    exact holdsRawEdges_of_holdsList 0 es hhold

/-- Decode `count` consecutive stride-4 `(u, v, weight, id)` edge records from `mem` at `base`. -/
@[expose] def readIndexedEdges (base count : ℕ) (mem : ℕ → ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  (List.range count).map fun i =>
    (mem (base + 4 * i), mem (base + 4 * i + 1), mem (base + 4 * i + 2), mem (base + 4 * i + 3))

/-- Decode `count` consecutive stride-3 `(u, v, weight)` edge records from `mem` at `base`. -/
@[expose] def readRawEdges (base count : ℕ) (mem : ℕ → ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range count).map fun i =>
    (mem (base + 3 * i), mem (base + 3 * i + 1), mem (base + 3 * i + 2))

/-- Decode `count` consecutive single words from `mem` starting at `base`. -/
@[expose] def readNatSlice (base count : ℕ) (mem : ℕ → ℕ) : List ℕ :=
  (List.range count).map fun i => mem (base + i)

/-- Execute `prog` from `s` with unbounded client semantics, returning
`(result, finalState, totalCost)`. -/
@[expose] def execWordRAM {α : Type} (s : Memory.State) (prog : Memory.Prog α) :
    α × Memory.State × ℕ :=
  ((Memory.spec 0).clientResult s prog, (Memory.spec 0).clientState s prog, memoryCost prog s)

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest
