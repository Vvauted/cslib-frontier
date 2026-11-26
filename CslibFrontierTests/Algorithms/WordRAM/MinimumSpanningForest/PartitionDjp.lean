/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpLoop
import Mathlib.Tactic.Linarith

/-!
# Tests for Dynamic Soft-Heap Partition DJP Subroutines

Verifies under Lean 4 `module` encapsulation:
1. All `Realizes .exact` synthesis certificates (`partSetup`, `partRoundInit`, `partDjpStep`,
   `partDjpLoop`, `partRunRound`, `partRunOuterLoop`, `partRunRemLoop`) and Soft-Heap
   `ε = 1 / 16` specialization (`partRankThreshold_eq_eps`, `partSHFuel_eq`).
2. Boundary cases: empty edge list (`m = 0`), single vertex (`n = 1`), and `maxsize = 1` early
   stop.
3. End-to-end symbolic/concrete execution of `partSetup_spec`, `partRoundInit_spec`, and
   `partDjpLoop_spec` on a small connected component (`n = 3`, `m = 2`).
-/

public section

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionDjp

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## Module-Encapsulated Realizes Certificate Checks -/

example : Realizes .exact partSetup WordEncoding.encode WordEncoding.encode
    partSetupSafe (fun _ _ => 0) :=
  realizes_partSetup

example : Realizes .exact partRoundInit WordEncoding.encode WordEncoding.encode
    partRoundInitSafe (fun _ _ => 0) :=
  realizes_partRoundInit

example : Realizes .exact partDjpStep (appendWords WordEncoding.encode WordEncoding.encode)
    WordEncoding.encode partDjpStepSafe (fun _ _ => 0) :=
  realizes_partDjpStep

example : Realizes .exact partDjpLoop WordEncoding.encode WordEncoding.encode
    partDjpLoopSafe (fun _ _ => 0) :=
  realizes_partDjpLoop

example : Realizes .exact partRunRound (appendWords WordEncoding.encode WordEncoding.encode)
    WordEncoding.encode partRunRoundSafe (fun _ _ => 0) :=
  realizes_partRunRound

example : Realizes .exact partRunOuterLoop WordEncoding.encode WordEncoding.encode
    partRunOuterLoopSafe (fun _ _ => 0) :=
  realizes_partRunOuterLoop

example : Realizes .exact partRunRemLoop WordEncoding.encode WordEncoding.encode
    partRunRemLoopSafe (fun _ _ => 0) :=
  realizes_partRunRemLoop

example : partRankThreshold = rankThresholdForEps (1 / 16 : ℚ) :=
  partRankThreshold_eq_eps

example (m : ℕ) : partSHFuel m = shFuelBound partRankThreshold (2 * m) :=
  partSHFuel_eq m

/-! ## Generic Component Execution Helper (Local) -/

private theorem run_single_round_test {w n edgeBase maxsize : ℕ}
    {es : List (IndexedEdge n)} {s₀ : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s₀)
    (hn_pos : 1 ≤ n) (hmax_pos : 1 ≤ maxsize)
    (hin : HoldsIndexedEdges edgeBase es s₀.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s₀.frontier)
    (hfit : Fits w (s₀.frontier + 1100 * (es.length + n + 1)))
    (hsimp : ∀ e : Fin es.length, es[e.val].u ≠ es[e.val].v)
    (u : Fin n) :
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨n, es.length, edgeBase, maxsize⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨n, es.length, edgeBase, maxsize⟩)
    let hInit := (Memory.spec 0).clientResult s1
      (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    let s3 := (Memory.spec 0).clientState s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ maxsize ∧ loopRes.tLen + 1 = loopRes.size ∧
    (memoryCost (partRoundInit ⟨setupRes.env, 1, u.val, setupRes.sh⟩) s1 : ℚ) +
      (memoryCost (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩) s2 : ℚ) ≤
      5450 * (es.length : ℚ) + 15 ∧
    (s3.mem (setupRes.env.bufBase + 3 * n) = u.val) := by
  have hs := partSetup_spec h16 hwf hn_pos hmax_pos hin hin_lt hfit
  rcases hs with ⟨_, _, _, hn_eq, hm_eq, heb_eq, hmax_eq, _, hsh_eq, hs1_fr, hwf1, _,
    hin1, hcsr1, hinv1, hzero_buf, hedge1, L, hL_env, hL_es, hL_eb, hL_max, _, _, hL_ib, hL_nb,
    hL_buf, _⟩
  set setupProg := partSetup ⟨n, es.length, edgeBase, maxsize⟩
  set setupRes := (Memory.spec 0).clientResult s₀ setupProg
  set s1 := (Memory.spec 0).clientState s₀ setupProg
  have hL_env_eq : setupRes.env = L.toEnv := hL_env.symm
  have hib0 : setupRes.sh.itemBase = L.itemBase := hL_ib.symm
  have hnb0 : setupRes.sh.nodeBase = L.nodeBase := hL_nb.symm
  have hrt0 : setupRes.sh.rankThreshold = partRankThreshold := by rw [hsh_eq]
  have hic0 : setupRes.sh.itemCount = 0 := by rw [hsh_eq]
  have hnc0 : setupRes.sh.nodeCount = 0 := by rw [hsh_eq]
  have hs1_fr' : s1.frontier = L.bufBase + (14 * n + 14 * L.es.length) := by
    rw [hs1_fr, hL_buf, hL_es]
  have hinv1' :
      SHInv w 0 0 (2 * L.es.length) (4 * L.es.length) setupRes.sh [] (fun _ => 0) s1 := by
    simpa only [hL_es] using hinv1
  have hcsr1' : HoldsUndirCSR L.offBase L.adjBase L.es s1.mem := by
    simpa only [hL_env_eq, PartLayout.toEnv, hL_es] using hcsr1
  have hin1' : HoldsIndexedEdges L.edgeBase L.es s1.mem := by
    rw [hL_eb, hL_es]; exact hin1
  have hdead1 : ∀ x < n, s1.mem (L.bufBase + x) = 0 := fun x hx => by
    rw [hL_buf]; exact hzero_buf x (by omega)
  have hincur1 : ∀ x < n, s1.mem (L.bufBase + n + x) = 0 := fun x hx => by
    rw [hL_buf, Nat.add_assoc]; exact hzero_buf (n + x) (by omega)
  have hedge1' : ∀ i < L.es.length, s1.mem (L.bufBase + 14 * n + i) = 0 := fun i hi => by
    rw [hL_buf]; exact hedge1 i (by simpa only [hL_es] using hi)
  have hsimp' : ∀ e : Fin L.es.length, L.es[e.val].u ≠ L.es[e.val].v := by
    subst hL_es; exact hsimp
  have hrem0 : remDeg n L.offBase s1.mem (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) =
      2 * L.es.length := by
    have heq : (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) = ∅ := by ext; simp
    rw [heq]; exact remDeg_empty hcsr1'
  have hcap0 : 0 + remDeg n L.offBase s1.mem
      (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) ≤ 2 * L.es.length := by
    rw [hrem0]; omega
  have hinit := partRoundInit_spec L (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0 u
    setupRes.sh s1 hs1_fr' hib0 hnb0 hrt0 hic0 hnc0 hinv1' hcsr1' hin1' hdead1 hincur1
    (fun _ _ => by omega) (h16.of_le (by omega)) rfl hedge1' hsimp' (by simp) hcap0
  rcases hinit with ⟨_, _, _, _, W₀, hinit_pot⟩
  let hInitL := (Memory.spec 0).clientResult s1 (partRoundInit ⟨L.toEnv, 1, u.val, setupRes.sh⟩)
  let s2L := (Memory.spec 0).clientState s1 (partRoundInit ⟨L.toEnv, 1, u.val, setupRes.sh⟩)
  have hloop := partDjpLoop_spec L s1 (fun _ => 0) (fun _ => 0) (fun _ => 0) 1 0 0 0 u
    hcsr1' hin1' hdead1 hedge1' (fun _ _ => by omega) (h16.of_le (by omega)) hsimp' hInitL s2L W₀
  rcases hloop with ⟨_, _, hcont0, _, _, W', hloop_pot⟩
  dsimp only
  rw [← hL_env]
  refine ⟨hcont0, ?_, ?_, ?_, ?_⟩
  · have hsz := W'.hsize_le; rw [hL_max] at hsz; exact hsz
  · have h1 := W'.hsize; have h2 := W'.htlen; dsimp only [hInitL, s2L] at h1 h2; omega
  · have hpot_nonneg : (0 : ℚ) ≤ djpPot W' := by
      dsimp only [djpPot]
      have hphi := Cslib.DataStructure.PriorityQueue.WordRAM.SoftHeap.totalPhi_nonneg
        partRankThreshold W'.roots
      positivity
    have hrem_q : (remDeg n L.offBase s1.mem
        (Finset.univ.filter (fun x : Fin n => (0 : ℕ) ≠ 0)) : ℚ) =
        2 * (es.length : ℚ) := by
      rw [hrem0, hL_es]; push_cast; ring
    have hesq : ((2 * L.es.length - 0 : ℕ) : ℚ) = 2 * (es.length : ℚ) := by
      rw [hL_es, Nat.sub_zero]; push_cast; ring
    rw [hrem_q, hesq] at hinit_pot
    linarith
  · have hv0 := W'.hverts_mem 0 (by have := W'.hsize; omega)
    have hr0 : ((djpVertsList W'.D)[0]'(by rw [djpVertsList_length]; omega)).val = u.val := by
      simp [djpVertsList, W'.hroot]
    dsimp only [PartLayout.toEnv]
    dsimp only [hInitL, s2L] at hv0
    rw [Nat.add_zero] at hv0
    exact hv0.trans hr0

/-! ## Concrete Boundary and Connected-Component Scenarios -/

/-- Boundary test 1: empty edge list (`m = 0`) on `n = 3` vertices. -/
theorem empty_graph_test :
    let s₀ : Memory.State := ⟨fun _ => 0, 0⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 0, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 0, 0, 3⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 3 ∧ loopRes.tLen + 1 = loopRes.size := by
  have h16 : Fits 20 16 := by decide
  have hwf : Memory.WellFormed 20 ⟨fun _ => 0, 0⟩ :=
    ⟨by decide, fun _ => h16.of_le (by simp)⟩
  have hfit : Fits 20 (0 + 1100 * (0 + 3 + 1)) := by decide
  have hres := run_single_round_test (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
    (es := []) h16 hwf (by decide) (by decide) (fun _ hi => by simp at hi) (by decide) hfit
    (fun e => Fin.elim0 e) ⟨0, by decide⟩
  exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

/-- Boundary test 2: single vertex (`n = 1, m = 0`). -/
theorem single_vertex_test :
    let s₀ : Memory.State := ⟨fun _ => 0, 0⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨1, 0, 0, 2⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨1, 0, 0, 2⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 2 ∧ loopRes.tLen + 1 = loopRes.size := by
  have h16 : Fits 20 16 := by decide
  have hres := run_single_round_test (w := 20) (n := 1) (edgeBase := 0) (maxsize := 2)
    (es := []) (s₀ := ⟨fun _ => 0, 0⟩) h16 ⟨by decide, fun _ => h16.of_le (by simp)⟩
    (by decide) (by decide) (fun _ hi => by simp at hi) (by decide) (by decide)
    (fun e => Fin.elim0 e) ⟨0, by decide⟩
  exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

/-- Sample RAM memory holding the encoded `n = 3`, `m = 2` path graph (`0 -5- 1 -2- 2`). -/
@[expose] def pathMem : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 5
  | 3 => 0
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 1
  | _ => 0

/-- Sample indexed edge list (`0 -5- 1 -2- 2`) on `3` vertices. -/
@[expose] def pathEdges : List (IndexedEdge 3) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 0⟩, ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 2, 1⟩]

private theorem path_holds : HoldsIndexedEdges 0 pathEdges pathMem := by
  intro i hi
  simp only [pathEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
    simp [pathEdges, pathMem]

private theorem path_simp (e : Fin pathEdges.length) :
    pathEdges[e.val].u ≠ pathEdges[e.val].v := by
  rcases e with ⟨i, hi⟩
  simp only [pathEdges, List.length_cons, List.length_nil] at hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [pathEdges]

private theorem pathMem_wf : Memory.WellFormed 20 ⟨pathMem, 8⟩ := by
  have h16 : Fits 20 16 := by decide
  refine ⟨by decide, fun a => h16.of_le ?_⟩
  rcases a with _ | _ | _ | _ | _ | _ | _ | _ | k <;> simp [pathMem]

/-- Boundary test 3: connected component (`n = 3`, path `0 -5- 1 -2- 2`) with `maxsize = 3`. -/
theorem connected_component_test :
    let s₀ : Memory.State := ⟨pathMem, 8⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 2, 0, 3⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 2, 0, 3⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 3 ∧ loopRes.tLen + 1 = loopRes.size := by
  have hres := run_single_round_test (w := 20) (n := 3) (edgeBase := 0) (maxsize := 3)
    (es := pathEdges) (s₀ := ⟨pathMem, 8⟩) (by decide) pathMem_wf (by decide) (by decide)
    path_holds (by decide) (by decide) path_simp ⟨0, by decide⟩
  exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

/-- Boundary test 4: `maxsize = 1` early stop on `n = 3`, `m = 2`. -/
theorem maxsize_one_boundary_test :
    let s₀ : Memory.State := ⟨pathMem, 8⟩
    let setupRes := (Memory.spec 0).clientResult s₀ (partSetup ⟨3, 2, 0, 1⟩)
    let s1 := (Memory.spec 0).clientState s₀ (partSetup ⟨3, 2, 0, 1⟩)
    let hInit := (Memory.spec 0).clientResult s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let s2 := (Memory.spec 0).clientState s1 (partRoundInit ⟨setupRes.env, 1, 0, setupRes.sh⟩)
    let loopRes := (Memory.spec 0).clientResult s2 (partDjpLoop ⟨setupRes.env, 1, 0, hInit⟩)
    loopRes.cont = 0 ∧ loopRes.size ≤ 1 ∧ loopRes.tLen + 1 = loopRes.size := by
  have hres := run_single_round_test (w := 20) (n := 3) (edgeBase := 0) (maxsize := 1)
    (es := pathEdges) (s₀ := ⟨pathMem, 8⟩) (by decide) pathMem_wf (by decide) (by decide)
    path_holds (by decide) (by decide) path_simp ⟨0, by decide⟩
  exact ⟨hres.1, hres.2.1, hres.2.2.1⟩

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionDjp
