/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests for Word-RAM Boruvka contraction step)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Boruvka
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-!
# Tests for Word-RAM Linear-Time Borůvka Contraction Step

Exercises `boruvkaMinProg`, `boruvkaSelectProg`, `boruvkaPartitionProg`, `boruvkaShrinkProg`,
`boruvkaStepProg`, and `boruvkaStepProg_lift_msf` across:

1. Empty-edge boundaries (`m = 0` with `n = 0` and `n = 3`).
2. Non-empty connected (`n = 4, m = 4`, halving to `outVertices = 2, outEdges = 1`) and
   disconnected (`n = 5` with isolated vertex and parallel edges) graph witnesses, including
   concrete `L_out` lifting along `boruvkaStepProg_lift_msf`.
3. Multigraph boundary (`m > n`, self-loops lighter than non-loop edges, parallel edges, cycle,
   and isolated vertex) confirming safe contraction and `2 * outVertices ≤ n`.
4. Composite `Realizes .exact` pipeline (`initAndBoruvkaStepProg` via `realize`) and lowering to a
   width-blind deterministic `Program .standard` via
   `exists_standard_basis_init_program_state_from_words`.
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsBoruvka

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest
open CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsTestSupport

/-! ## Private MSF base witnesses for concrete `L_out` checks -/

private theorem isMinSpanningForest_nil {n : ℕ} :
    IsMinSpanningForest (n := n) ([] : List (WeightedEdge n ℕ)) [] := by
  refine ⟨⟨List.Subperm.refl _, isAcyclic_nil, rfl⟩, fun F' hF' => ?_⟩
  rw [List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hF'.1.length_le)]

private theorem isMinSpanningForest_singleton {n : ℕ} (e : WeightedEdge n ℕ) (hne : e.u ≠ e.v) :
    IsMinSpanningForest [e] [e] := by
  have hrel_false : (DisjointSet.Partition.discrete n).rel e.u e.v = false :=
    Bool.eq_false_iff.mpr fun h => hne (DisjointSet.Partition.rel_discrete_eq_true.mp h)
  have hacyc : IsAcyclic [e] := isAcyclicFrom_cons.mpr ⟨hrel_false, isAcyclicFrom_nil _⟩
  refine ⟨⟨List.Subperm.refl _, hacyc, rfl⟩, fun F' hF' => ?_⟩
  have hlen : F'.length ≤ 1 := hF'.1.length_le
  cases F' with
  | nil =>
    have hrel := congrArg (fun p : DisjointSet.Partition n => p.rel e.u e.v) hF'.2.2
    have hl : (edgePartition ([] : List (WeightedEdge n ℕ))).rel e.u e.v = false := hrel_false
    have hr : (edgePartition [e]).rel e.u e.v = true := by
      simp [edgePartition]
    rw [hl, hr] at hrel
    cases hrel
  | cons f rest =>
    simp only [List.length_cons] at hlen
    obtain rfl : rest = [] := List.length_eq_zero_iff.mp (by omega)
    obtain rfl : f = e := List.mem_singleton.mp (hF'.1.subset List.mem_cons_self)
    exact le_rfl

/-! ## 1. Empty edge array (`m = 0`) boundary witnesses -/

example :
    let es : List (IndexedEdge 0) := []
    let s₀ := mkInitState es
    let r := execWordRAM s₀ (boruvkaStepProg ⟨0, 0, 0⟩)
    2 * r.1.outVertices ≤ 0 ∧ r.1.outEdges = 0 ∧ r.1.selCount = 0 ∧ r.2.2 ≤ 34 := by
  intro es s₀ r
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 16) es (by decide) (by decide)
    (fun _ h => absurd h List.not_mem_nil)
  have hft := boruvkaStepProg_spec (by decide) hwf hin (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, hcost, _, _, _, _, hout_v, hout_e, hsel_cn, _⟩ :=
    framedTriple_iff_realization.mp hft
  exact ⟨hout_v, Nat.eq_zero_of_le_zero hout_e, Nat.eq_zero_of_le_zero hsel_cn, hcost⟩

example :
    let es : List (IndexedEdge 3) := []
    let s₀ := mkInitState es
    let r := execWordRAM s₀ (boruvkaStepProg ⟨3, 0, 0⟩)
    2 * r.1.outVertices ≤ 3 ∧ r.1.outEdges = 0 ∧ r.1.selCount = 0 ∧ r.2.2 ≤ 217 := by
  intro es s₀ r
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 16) es (by decide) (by decide)
    (fun _ h => absurd h List.not_mem_nil)
  have hft := boruvkaStepProg_spec (by decide) hwf hin (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, hcost, _, _, _, _, hout_v, hout_e, _, hsel_cm, _⟩ :=
    framedTriple_iff_realization.mp hft
  exact ⟨hout_v, Nat.eq_zero_of_le_zero hout_e, Nat.eq_zero_of_le_zero hsel_cm, hcost⟩

/-! ## 2. Connected & disconnected witnesses and concrete `L_out` lifting -/

private def conn4E0 : IndexedEdge 4 := ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 1, 0⟩
private def conn4E1 : IndexedEdge 4 := ⟨⟨2, by decide⟩, ⟨3, by decide⟩, 2, 1⟩
private def conn4E2 : IndexedEdge 4 := ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 10, 2⟩
private def conn4E3 : IndexedEdge 4 := ⟨⟨0, by decide⟩, ⟨3, by decide⟩, 20, 3⟩
private def conn4Edges : List (IndexedEdge 4) := [conn4E0, conn4E1, conn4E2, conn4E3]

example :
    let s₀ := mkInitState conn4Edges
    let r := execWordRAM s₀ (boruvkaStepProg ⟨4, 4, 0⟩)
    2 * r.1.outVertices ≤ 4 ∧ r.1.outEdges ≤ 4 ∧ r.1.selCount ≤ 4 ∧ r.2.2 ≤ 582 := by
  intro s₀ r
  have hwts : ∀ e ∈ conn4Edges, Fits 16 e.weight ∧ Fits 16 e.id := by
    intro e he
    simp only [conn4Edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 16) conn4Edges (by decide) (by decide) hwts
  have hft := boruvkaStepProg_spec (by decide) hwf hin (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, hcost, _, _, _, _, hout_v, hout_e, hsel_cn, _⟩ :=
    framedTriple_iff_realization.mp hft
  exact ⟨hout_v, hout_e, hsel_cn, hcost⟩

example :
    let selEs : List (IndexedEdge 4) := [conn4E0, conn4E1]
    let eOut : IndexedEdge 2 := ⟨0, 1, 10, 2⟩
    let L_out : List (IndexedEdge 2) := [eOut]
    ∃ L_orig : List (IndexedEdge 4),
      (selEs ++ L_orig).Subperm conn4Edges ∧
      L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
      IsMinSpanningForest (conn4Edges.map IndexedEdge.toWeighted)
        ((selEs ++ L_orig).map IndexedEdge.toWeighted) := by
  intro selEs eOut L_out
  let compFn : Fin 4 → Fin 2 := fun u => if u.val < 2 then 0 else 1
  let remapper (e : IndexedEdge 4) : IndexedEdge 2 :=
    ⟨compFn e.u, compFn e.v, e.weight, e.id⟩
  let esCon := conn4Edges.map remapper
  have hsel_sub : selEs.Subperm conn4Edges :=
    (List.prefix_append selEs [conn4E2, conn4E3]).sublist.subperm
  have hcomp_surj : Function.Surjective compFn := by
    intro y
    fin_cases y
    · exact ⟨0, rfl⟩
    · exact ⟨2, rfl⟩
  have hcomp_rel : ∀ x y : Fin 4, compFn x = compFn y ↔
      (edgePartition (selEs.map IndexedEdge.toWeighted)).rel x y = true := by
    intro x y
    simp only [selEs, conn4E0, conn4E1, compFn]
    fin_cases x <;> fin_cases y <;> decide
  have hsel_ext : ∃ F_ext : List (WeightedEdge 4 ℕ),
      IsMinSpanningForest (conn4Edges.map IndexedEdge.toWeighted)
        (selEs.map IndexedEdge.toWeighted ++ F_ext) := by
    let F := selEs.map IndexedEdge.toWeighted ++ [conn4E2.toWeighted]
    let G := conn4Edges.map IndexedEdge.toWeighted
    have hF_sub : F.Subperm G :=
      (List.prefix_append F [conn4E3.toWeighted]).sublist.subperm
    have hF_all : ∀ x y : Fin 4, (edgePartition F).rel x y = true := by
      intro x y
      simp only [F, selEs, conn4E0, conn4E1, conn4E2, IndexedEdge.toWeighted, edgePartition,
        edgePartitionFrom]
      fin_cases x <;> fin_cases y <;> decide
    have hG_all : ∀ x y : Fin 4, (edgePartition G).rel x y = true := by
      intro x y
      simp only [G, conn4Edges, conn4E0, conn4E1, conn4E2, conn4E3, edgePartition,
        edgePartitionFrom]
      fin_cases x <;> fin_cases y <;> decide
    have hpart_FG : edgePartition F = edgePartition G :=
      DisjointSet.Partition.ext fun x y => (hF_all x y).trans (hG_all x y).symm
    have hF_nc : (edgePartition F).numComponents = 1 :=
      Finset.card_eq_one.mpr ⟨(edgePartition F).classOf 0,
        Finset.eq_singleton_iff_unique_mem.mpr ⟨(edgePartition F).classOf_mem_components 0,
          fun c hc => let ⟨x, hx⟩ := DisjointSet.Partition.mem_components.mp hc
            hx ▸ DisjointSet.Partition.classOf_eq_iff.mpr (hF_all x 0)⟩⟩
    have hF_acyc : IsAcyclic F := by
      rw [isAcyclic_iff, hF_nc]; decide
    refine ⟨[conn4E2.toWeighted], ⟨hF_sub, hF_acyc, hpart_FG⟩, fun F' hF' => ?_⟩
    obtain ⟨l, hl_perm, hl_sub⟩ := hF'.1
    have hl_len : l.length = 3 := by
      have hacyc' := hF'.2.1
      rw [isAcyclic_iff, hF'.2.2, ← hpart_FG, hF_nc, ← hl_perm.length_eq] at hacyc'
      omega
    rw [← Perm.totalWeight_eq hl_perm]
    obtain ⟨c, hc⟩ := hl_sub.exists_perm_append
    have hc_len : c.length = 1 := by
      have hlen := hc.length_eq
      simp only [List.length_append, conn4Edges, List.length_map, List.length_cons,
        List.length_nil] at hlen
      omega
    obtain ⟨e, rfl⟩ : ∃ e, c = [e] := List.length_eq_one_iff.mp hc_len
    have he_mem : e ∈ G := hc.symm.subset (List.mem_append_right l List.mem_cons_self)
    have he_wt : e.weight ≤ 20 := by
      simp only [G, conn4Edges, conn4E0, conn4E1, conn4E2, conn4E3, IndexedEdge.toWeighted,
        List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at he_mem
      rcases he_mem with rfl | rfl | rfl | rfl <;> decide
    have hsum := Perm.totalWeight_eq hc
    have hsum_F : totalWeight (List.map IndexedEdge.toWeighted selEs ++ [conn4E2.toWeighted]) =
        13 := by
      simp only [totalWeight, selEs, conn4E0, conn4E1, conn4E2, IndexedEdge.toWeighted,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.sum_cons,
        List.sum_nil]
      decide
    have hsum_G : totalWeight (List.map IndexedEdge.toWeighted conn4Edges) = 33 := by
      simp only [totalWeight, conn4Edges, conn4E0, conn4E1, conn4E2, conn4E3,
        IndexedEdge.toWeighted, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      decide
    have hsum_app : totalWeight (l ++ [e]) = totalWeight l + e.weight := by
      simp only [totalWeight, List.map_append, List.map_cons, List.map_nil, List.sum_append,
        List.sum_cons, List.sum_nil, add_zero]
    omega
  have hdedup_sub : [eOut].Subperm esCon :=
    (List.Sublist.cons _ (List.Sublist.cons _
      (List.Sublist.cons_cons eOut (List.nil_sublist _)))).subperm
  have hdedup_eq : ([eOut].map IndexedEdge.toWeighted) =
      dedupSimpleEdges (esCon.map IndexedEdge.toWeighted) := by
    simp only [esCon, remapper, compFn, eOut, conn4Edges, conn4E0, conn4E1, conn4E2, conn4E3]
    decide
  have hdedup_simp : IsSimple (edgeEnds ([eOut].map IndexedEdge.toWeighted)) := by
    rw [isSimple_iff]
    refine ⟨fun i => by fin_cases i; simp only [edgeEnds, List.getElem_map,
      IndexedEdge.toWeighted, eOut, List.getElem_cons_zero]; decide,
      fun i j => by fin_cases i; fin_cases j; simp⟩
  have hL_msf : IsMinSpanningForest ([eOut].map IndexedEdge.toWeighted)
      (L_out.map IndexedEdge.toWeighted) :=
    isMinSpanningForest_singleton eOut.toWeighted (by decide)
  exact boruvkaStepProg_lift_msf hsel_sub hsel_ext hcomp_surj hcomp_rel rfl
    hdedup_sub hdedup_eq hdedup_simp Function.injective_id rfl
    (List.Subperm.refl _) hL_msf

private def disc5Edges : List (IndexedEdge 5) :=
  [⟨⟨0, by decide⟩, ⟨1, by decide⟩, 3, 0⟩,
   ⟨⟨2, by decide⟩, ⟨3, by decide⟩, 5, 1⟩,
   ⟨⟨2, by decide⟩, ⟨3, by decide⟩, 8, 2⟩]

example :
    let s₀ := mkInitState disc5Edges
    let r := execWordRAM s₀ (boruvkaStepProg ⟨5, 3, 0⟩)
    2 * r.1.outVertices ≤ 5 ∧ r.1.outEdges ≤ 3 ∧ r.1.selCount ≤ 3 ∧
    (∀ L_out : List (IndexedEdge r.1.outVertices),
      L_out = [] → IsMinSpanningForest ([] : List (WeightedEdge r.1.outVertices ℕ))
        (L_out.map IndexedEdge.toWeighted)) := by
  intro s₀ r
  have hwts : ∀ e ∈ disc5Edges, Fits 16 e.weight ∧ Fits 16 e.id := by
    intro e he
    simp only [disc5Edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 16) disc5Edges (by decide) (by decide) hwts
  have hft := boruvkaStepProg_spec (by decide) hwf hin (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, _, _, _, _, _, hout_v, hout_e, _, hsel_cm, _⟩ :=
    framedTriple_iff_realization.mp hft
  exact ⟨hout_v, hout_e, hsel_cm, fun L_out hL => by subst hL; exact isMinSpanningForest_nil⟩

/-! ## 3. Multigraph boundary witness (`m > n`, loops, parallel edges, cycle, isolated vertex) -/

private def multi4Edges : List (IndexedEdge 4) :=
  [⟨⟨0, by decide⟩, ⟨0, by decide⟩, 1, 0⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 5, 1⟩,
   ⟨⟨0, by decide⟩, ⟨1, by decide⟩, 9, 2⟩,
   ⟨⟨1, by decide⟩, ⟨2, by decide⟩, 4, 3⟩,
   ⟨⟨0, by decide⟩, ⟨2, by decide⟩, 7, 4⟩,
   ⟨⟨2, by decide⟩, ⟨2, by decide⟩, 2, 5⟩]

example :
    4 < multi4Edges.length ∧
    let s₀ := mkInitState multi4Edges
    let r := execWordRAM s₀ (boruvkaStepProg ⟨4, multi4Edges.length, 0⟩)
    2 * r.1.outVertices ≤ 4 ∧ r.1.outEdges ≤ 6 ∧ r.1.selCount ≤ 4 ∧ r.2.2 ≤ 734 := by
  refine ⟨by decide, ?_⟩
  intro s₀ r
  have hwts : ∀ e ∈ multi4Edges, Fits 16 e.weight ∧ Fits 16 e.id := by
    intro e he
    simp only [multi4Edges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by decide⟩
  obtain ⟨hwf, hfr, hin⟩ := mkInitState_spec (w := 16) multi4Edges (by decide) (by decide) hwts
  have hft := boruvkaStepProg_spec (by decide) hwf hin (by rw [hfr]; decide)
    (by rw [hfr]; decide)
  obtain ⟨_, hcost, _, _, _, _, hout_v, hout_e, hsel_cn, _⟩ :=
    framedTriple_iff_realization.mp hft
  exact ⟨hout_v, hout_e, hsel_cn, hcost⟩

/-! ## 4. Composite `realize` pipeline and lowered `Program .standard` execution -/

private def initAndBoruvkaStepProg (g : GraphSlice) : Memory.Prog BoruvkaStepResult := do
  let edgeBase ← initIndexedEdges g.edgeBase g.numEdges
  boruvkaStepProg ⟨g.numVertices, g.numEdges, edgeBase⟩

private theorem initAndBoruvkaStepProg_spec {w n inBase : ℕ}
    {es : List (WeightedEdge n ℕ)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsEdges inBase es s.mem)
    (hin_lt : inBase + 3 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * es.length + (22 * es.length + 16 * n + 4))) :
    Memory.FramedTriple w s (initAndBoruvkaStepProg ⟨n, es.length, inBase⟩)
      (8 * es.length + 1 + (76 * es.length + 61 * n + 34)) ∅ fun res _ =>
        2 * res.outVertices ≤ n ∧ res.outEdges ≤ es.length := by
  dsimp only [initAndBoruvkaStepProg]
  refine (Memory.FramedTriple.bind_same (c₁ := 8 * es.length + 1)
    (c₂ := 76 * es.length + 61 * n + 34) ?_).mono le_rfl fun _ _ h => h
  refine (initIndexedEdges_spec h16 hwf hin hin_lt (hfit.of_le (by omega))).mono le_rfl
    fun edgeBase s₁ ⟨hbase, hfr₁, hwf₁, hidx⟩ => ?_
  let ies : List (IndexedEdge n) := es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩
  have hlen_ies : ies.length = es.length := List.length_mapIdx
  rw [← hlen_ies]
  exact (boruvkaStepProg_spec (es := ies) h16 hwf₁ hidx (by rw [hbase, hfr₁, hlen_ies])
    (by rw [hfr₁, hlen_ies]; exact hfit.of_le (by omega))).mono le_rfl
    fun _ _ ⟨_, _, _, hout_v, hout_e, _⟩ => ⟨hout_v, hout_e⟩

private theorem realizes_initAndBoruvkaStepProg : Realizes .exact initAndBoruvkaStepProg
    WordEncoding.encode WordEncoding.encode
    (fun w g s =>
      Fits w 16 ∧
      g.edgeBase + 3 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + 4 * g.numEdges + (22 * g.numEdges + 16 * g.numVertices + 4)) ∧
      ∀ j < g.numEdges,
        s.mem (g.edgeBase + 3 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 3 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact initAndBoruvkaStepProg WordEncoding.encode WordEncoding.encode
      (fun w g s =>
        let edgeBase := (Memory.spec 0).clientResult s (initIndexedEdges g.edgeBase g.numEdges)
        let s₁ := (Memory.spec 0).clientState s (initIndexedEdges g.edgeBase g.numEdges)
        Fits w 16 ∧ g.edgeBase + 3 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + 4 * g.numEdges) ∧
        edgeBase + 4 * g.numEdges ≤ s₁.frontier ∧
        Fits w (s₁.frontier + (22 * g.numEdges + 16 * g.numVertices + 4)) ∧
        ∀ j < g.numEdges,
          s₁.mem (edgeBase + 4 * j) < g.numVertices ∧
          s₁.mem (edgeBase + 4 * j + 1) < g.numVertices)
      (fun _ _ => 0) := by
    unfold initAndBoruvkaStepProg
    realize [realizes_initIndexedEdges, realizes_boruvkaStepProg]
    all_goals
      obtain ⟨h16, hin_lt, hfit_init, hedge_base, hfit_step, hedges⟩ := h
      first
      | exact h16 | exact hin_lt | exact hfit_init | exact hedge_base
      | exact hfit_step | exact hedges
  refine hraw.consequence (fun w g s _ hmem ⟨h16, hin_lt, hfit, hedges⟩ => ?_)
    (fun _ _ => le_rfl)
  let rawEs : List (WeightedEdge g.numVertices ℕ) :=
    List.ofFn fun i : Fin g.numEdges =>
      ⟨⟨s.mem (g.edgeBase + 3 * i.val), (hedges i.val i.isLt).1⟩,
       ⟨s.mem (g.edgeBase + 3 * i.val + 1), (hedges i.val i.isLt).2⟩,
       s.mem (g.edgeBase + 3 * i.val + 2)⟩
  have hlen : rawEs.length = g.numEdges := List.length_ofFn
  have hraw_holds : HoldsEdges g.edgeBase rawEs s.mem := fun i hi => by simp [rawEs]
  have hft := initIndexedEdges_spec h16 hmem hraw_holds (by simpa [hlen] using hin_lt)
    (by simpa [hlen] using hfit.of_le (by omega))
  rw [hlen] at hft
  obtain ⟨_, _, _, hbase, hfr₁, _, hidx⟩ := framedTriple_iff_realization.mp hft
  refine ⟨h16, hin_lt, hfit.of_le (by omega), by rw [hbase, hfr₁],
    by rw [hfr₁]; exact hfit.of_le (by omega), fun j hj => ?_⟩
  let ies := rawEs.mapIdx fun i e => (⟨e.u, e.v, e.weight, i⟩ : IndexedEdge g.numVertices)
  have hj' : j < ies.length := by simpa [ies, hlen] using hj
  obtain ⟨hu, hv, _⟩ := hidx j hj'
  exact ⟨hu ▸ ies[j].u.isLt, hv ▸ ies[j].v.isLt⟩

example :
    let words : List ℕ := [4, 4, 4, 0, 1, 1, 2, 3, 2, 1, 2, 10, 0, 3, 20]
    let g : GraphSlice := ⟨4, 4, 4⟩
    ∃ r C pc : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∃ frontier : Fin r, ∃ y n,
        Runs 16 prog (State.init words) ⟨pc, y⟩ n ∧
        step 16 prog ⟨pc, y⟩ =
          .halt ((Memory.spec 16).clientResult (Memory.State.init words)
            (initAndBoruvkaStepProg g)).outVertices ∧
        (memoryState frontier y).frontier =
          ((Memory.spec 16).clientState (Memory.State.init words)
            (initAndBoruvkaStepProg g)).frontier ∧
        n + 1 ≤ C * (memoryCost (initAndBoruvkaStepProg g) (Memory.State.init words) + 1) + 1 := by
  intro words g
  obtain ⟨r, C, pc, prog, hnw, frontier, _, hrun⟩ :=
    realizes_initAndBoruvkaStepProg.exists_standard_basis_init_program_state_from_words (2 : Fin 5)
  have hwf : Memory.WellFormed 16 (Memory.State.init words) :=
    Memory.wellFormed_init (by decide) (by decide)
  have hlayout : ∀ j : Fin 3, words.getD j.val 0 = WordEncoding.encode g j := by
    intro j; fin_cases j <;> rfl
  have hedges : ∀ j < g.numEdges,
      (Memory.State.init words).mem (g.edgeBase + 3 * j) < g.numVertices ∧
      (Memory.State.init words).mem (g.edgeBase + 3 * j + 1) < g.numVertices := by
    intro j hj
    dsimp only [g] at hj ⊢
    rcases j with _ | _ | _ | _ | j
    · decide
    · decide
    · decide
    · decide
    · omega
  have hpre : Fits 16 16 ∧ g.edgeBase + 3 * g.numEdges ≤ (Memory.State.init words).frontier ∧
      Fits 16 ((Memory.State.init words).frontier + 4 * g.numEdges +
        (22 * g.numEdges + 16 * g.numVertices + 4)) ∧
      ∀ j < g.numEdges,
        (Memory.State.init words).mem (g.edgeBase + 3 * j) < g.numVertices ∧
        (Memory.State.init words).mem (g.edgeBase + 3 * j + 1) < g.numVertices :=
    ⟨by decide, by decide, by decide, hedges⟩
  let rawEs : List (WeightedEdge 4 ℕ) :=
    [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨1, 2, 10⟩, ⟨0, 3, 20⟩]
  have hraw : HoldsEdges 4 rawEs (Memory.State.init words).mem := by
    intro i hi
    rcases i with _ | _ | _ | _ | i
    · simp only [words, rawEs, List.getElem_cons_zero]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · simp only [words, rawEs, List.getElem_cons_zero, List.getElem_cons_succ]; decide
    · dsimp only [rawEs] at hi; simp only [List.length_cons, List.length_nil] at hi; omega
  have hv := (framedTriple_iff_realization.mp (initAndBoruvkaStepProg_spec (by decide) hwf hraw
    (by decide) (by decide))).1
  obtain ⟨y, n, hruns, hhalt, hmem_eq, _, hsteps⟩ :=
    hrun 16 g words hlayout (by decide) (by decide) (by decide) hpre hv
  refine ⟨r, C, pc, stripRand prog, not_readsWidth_stripRand hnw, isRandFree_stripRand prog,
    frontier, y, n, runs_stripRand hruns, step_stripRand_of_halt hhalt, ?_, ?_⟩
  · rw [hmem_eq]
  · simpa only [Nat.add_zero] using hsteps

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.GraphOpsBoruvka
