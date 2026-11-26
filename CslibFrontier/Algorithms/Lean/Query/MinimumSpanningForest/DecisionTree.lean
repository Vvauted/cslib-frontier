/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical
public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Decomp

/-!
# MSF Decision Trees and Optimality Structural Lemmas

Umbrella module re-exporting the Pettie–Ramachandran minimum spanning forest comparison decision
tree development ([PettieRamachandran2002], Section 5.1) built over `Cslib.Multigraph.msf`:

* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic`: binary comparison
  decision trees `MSFTree`/`MSFDT`, `optDepth`, bitmask encodings `endsOfMask`, complete padded
  trees `MSFDT.padTo`, and compilation from `FreeM (LEQuery (Fin e))`.
* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical`:
  isomorphism invariance (`optDepth_reindex`), `optDepthMN` (`T*(m, n)`), Proposition 5.1
  (`le_two_mul_optDepthMN`), and Proposition 5.2 monotonicity bounds.
* `CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Decomp`: Property 5.3
  cut-vertex sufficiency (`property53Pair_of_inter_le_one`), Lemma 5.5 additivity
  (`optDepth_edgeUnionList_eq_sum`), Corollary 5.6 (`sum_optDepth_le_optDepthMN`), and
  Corollary 5.7 doubling (`two_mul_optDepthMN_le`).
-/
