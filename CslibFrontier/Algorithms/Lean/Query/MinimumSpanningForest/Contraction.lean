/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust

/-!
# Threshold-Rank Contraction and Dynamic Soft-Heap Robust Contraction

Umbrella module re-exporting the contraction and threshold-rank MSF theory of
[PettieRamachandran2002], Sections 2–3:

* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Threshold`: `edgeEnds`
  and lexicographic weight bridge to `Cslib.Multigraph.msf`, `WeaklySupported`, threshold-rank
  characterization `isMinSpanningForest_iff_threshold_partition`, and contraction preservation
  (`exists_extend_isMinSpanningForest_of_cutStep`, `isMinSpanningForest_append_of_contract`).
* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust`:
  `DynamicDJPTree`, Lemma 2.1 (`lemma_2_1_dynamic`), Robust Contraction Lemma 3.2
  (`lemma_3_2_dynamic`), Lemma 3.3 (`lemma_3_3_optDepth_sum_le`, `lemma_3_3_conglomerate_size`),
  and simple-graph deduplication (`dedupSimpleEdges`, `dedupSimpleEdges_isSimple`,
  `isMinSpanningForest_of_dedupSimpleEdges`).
-/
