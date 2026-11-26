/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Linarith

/-!
# Canonical MSF Decision-Tree Complexity `T*(m, n)` and Lower Bound

This module proves graph-isomorphism invariance of optimal decision-tree depth
(`optDepth_reindex`), reduces arbitrary simple graphs to canonical bitmask representations
(`endsOfMask`), defines worst-case optimal decision-tree complexity `optDepthMN m n` (`T*(m, n)`
of [PettieRamachandran2002]), and proves monotonicity (`optDepthMN_mono_m`, `optDepthMN_mono_n`),
the generic query-program upper bound (`optDepthMN_le_of_freeM`), and the cycle-cover lower bound
`m ≤ 2 * optDepthMN m n` ([PettieRamachandran2002], Propositions 5.1–5.2).

## Main definitions

* `Cslib.Query.MinimumSpanningForest.optDepthMN`: worst-case optimal comparison depth `T*(m, n)`
  over simple graphs on `n` vertices with at most `m` edges.
* `Cslib.Query.MinimumSpanningForest.MSFTree.traceVars`: edge indices inspected along a tree
  execution path.

## Main results

* `Cslib.Query.MinimumSpanningForest.optDepth_reindex`: isomorphism invariance of `optDepth`.
* `Cslib.Query.MinimumSpanningForest.optDepth_le_optDepthMN_of_isSimple`: any `e`-edge `n`-vertex
  simple graph with `e ≤ m` satisfies `optDepth ends ≤ optDepthMN m n`.
* `Cslib.Query.MinimumSpanningForest.optDepthMN_le_of_freeM`: uniform upper bound from any
  monotone comparison-query MSF family.
* `Cslib.Query.MinimumSpanningForest.le_two_mul_optDepthMN`: Proposition 5.1 of
  [PettieRamachandran2002], `m ≤ 2 * optDepthMN m n` for `3 ≤ m`, `3 ≤ n`, `m ≤ maxSimpleEdges n`.
* `Cslib.Query.MinimumSpanningForest.optDepthMN_mono_m`,
  `Cslib.Query.MinimumSpanningForest.optDepthMN_mono_n`: Proposition 5.2 monotonicity bounds.
-/

public section

namespace Cslib.Query.MinimumSpanningForest

/-! ## Reindexing and Canonical Reduction of Simple Graphs -/

theorem joins_reindex {E₁ E₂ V₁ V₂ : Type*} (ends₁ : E₁ → Sym2 V₁) (ends₂ : E₂ → Sym2 V₂)
    (σ : E₁ ≃ E₂) (φ : V₁ ↪ V₂)
    (hEnds : ∀ i : E₁, Sym2.map φ (ends₁ i) = ends₂ (σ i))
    (S : Finset E₁) (u v : V₁) :
    Cslib.Multigraph.Joins ends₁ (S : Set E₁) u v ↔
      Cslib.Multigraph.Joins ends₂ ((S.map σ.toEmbedding : Finset E₂) : Set E₂) (φ u) (φ v) := by
  constructor
  · refine Cslib.Multigraph.Joins.lift φ fun e he a b hab => ?_
    exact Cslib.Multigraph.Joins.of_mem (Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨e, he, rfl⟩))
      (by simpa [hab] using (hEnds e).symm)
  · intro hc
    classical
    let pull : V₂ → V₁ := fun x => if hx : ∃ a, φ a = x then hx.choose else u
    have hpull : ∀ a : V₁, pull (φ a) = a := fun a => by
      dsimp only [pull]
      have hx : ∃ a', φ a' = φ a := ⟨a, rfl⟩
      rw [dite_eq_left_of_eq_true (eq_true hx)]
      exact φ.injective hx.choose_spec
    have hmap : Cslib.Multigraph.Joins ends₁ (S : Set E₁) (pull (φ u)) (pull (φ v)) := by
      refine Cslib.Multigraph.Joins.lift pull (fun g hg a b hab => ?_) hc
      rw [Finset.mem_coe, Finset.mem_map] at hg
      obtain ⟨e, heS, rfl⟩ := hg
      induction he : ends₁ e using Sym2.ind with
      | _ a₁ b₁ =>
        have hsym : s(φ a₁, φ b₁) = s(a, b) := by
          rw [← Sym2.map_mk (f := φ), ← he, hEnds e]
          simpa using hab
        rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hp1 : pull a = a₁ := by rw [← h1, hpull]
          have hp2 : pull b = b₁ := by rw [← h2, hpull]
          rw [hp1, hp2]
          exact Cslib.Multigraph.Joins.of_mem heS he
        · have hp1 : pull a = b₁ := by rw [← h2, hpull]
          have hp2 : pull b = a₁ := by rw [← h1, hpull]
          rw [hp1, hp2]
          exact (Cslib.Multigraph.Joins.of_mem heS he).symm
    rwa [hpull u, hpull v] at hmap

theorem optDepth_reindex {e₁ e₂ n₁ n₂ : ℕ}
    (ends₁ : Fin e₁ → Sym2 (Fin n₁)) (ends₂ : Fin e₂ → Sym2 (Fin n₂))
    (σ : Fin e₁ ≃ Fin e₂) (φ : Fin n₁ ↪ Fin n₂)
    (hEnds : ∀ i : Fin e₁, Sym2.map φ (ends₁ i) = ends₂ (σ i)) :
    optDepth ends₁ = optDepth ends₂ := by
  have heq : e₁ = e₂ := by simpa using Fintype.card_congr σ
  have hunique : ∀ p : Equiv.Perm (Fin e₂),
      let c : Equiv.Perm (Fin e₁) := σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv)
      Cslib.Multigraph.msf ends₂ p Finset.univ =
        (Cslib.Multigraph.msf ends₁ c Finset.univ).map σ.toEmbedding := by
    intro p c
    ext g
    rw [Finset.mem_map]
    let i := σ.symm g
    have hperm_iff : ∀ a b : Fin e₁, c a < c b ↔ p (σ a) < p (σ b) := fun a b => by
      change (c a).val < (c b).val ↔ (p (σ a)).val < (p (σ b)).val
      simp [c, Fin.castOrderIso]
    induction hi : ends₁ i using Sym2.ind with
    | _ a₁ b₁ =>
      have hg_ends : ends₂ g = s(φ a₁, φ b₁) := by
        have hsi : σ i = g := σ.apply_symm_apply g
        rw [← hsi, ← hEnds i, hi]
        rfl
      have hflt : ((Finset.univ.filter fun e' : Fin e₁ => c e' < c i).map
          σ.toEmbedding : Finset (Fin e₂)) = Finset.univ.filter fun f => p f < p g := by
        ext f
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨e', he', rfl⟩
          exact (σ.apply_symm_apply g).symm ▸ (hperm_iff e' i).mp he'
        · intro hf
          refine ⟨σ.symm f, (hperm_iff (σ.symm f) i).mpr ?_, σ.apply_symm_apply f⟩
          simpa [i] using hf
      have hset₁ : {e' | e' ∈ (Finset.univ : Finset (Fin e₁)) ∧ c e' < c i} =
          ((Finset.univ.filter fun e' => c e' < c i : Finset (Fin e₁)) : Set (Fin e₁)) := by
        ext e'; simp
      have hset₂ : {f | f ∈ (Finset.univ : Finset (Fin e₂)) ∧ p f < p g} =
          ((Finset.univ.filter fun f => p f < p g : Finset (Fin e₂)) : Set (Fin e₂)) := by
        ext f; simp
      have hj_iff : Cslib.Multigraph.Joins ends₁
          {e' | e' ∈ (Finset.univ : Finset (Fin e₁)) ∧ c e' < c i} a₁ b₁ ↔
          Cslib.Multigraph.Joins ends₂
            {f | f ∈ (Finset.univ : Finset (Fin e₂)) ∧ p f < p g} (φ a₁) (φ b₁) := by
        rw [hset₁, hset₂, ← hflt]
        exact joins_reindex ends₁ ends₂ σ φ hEnds _ a₁ b₁
      constructor
      · intro hg
        refine ⟨i, ?_, σ.apply_symm_apply g⟩
        rw [Cslib.Multigraph.mem_msf_iff p hg_ends] at hg
        rw [Cslib.Multigraph.mem_msf_iff c hi]
        exact ⟨Finset.mem_univ _, fun hc => hg.2 (hj_iff.mp hc)⟩
      · rintro ⟨e, he, hge⟩
        have hei : e = i := σ.injective (hge.trans (σ.apply_symm_apply g).symm)
        rw [hei] at he
        rw [Cslib.Multigraph.mem_msf_iff c hi] at he
        rw [Cslib.Multigraph.mem_msf_iff p hg_ends]
        exact ⟨Finset.mem_univ _, fun hc => he.2 (hj_iff.mpr hc)⟩
  have hle1 : optDepth ends₂ ≤ optDepth ends₁ := by
    obtain ⟨T₁, hcorr₁, hd₁⟩ := exists_opt_msfDT ends₁
    let T₂ : MSFDT e₂ := (T₁.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ
    refine (optDepth_le_of_correct (T := T₂) fun p => ?_).trans ?_
    · let c : Equiv.Perm (Fin e₁) := σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv)
      have heval : T₂.eval p = (T₁.eval c).map σ.toEmbedding := by
        rw [← MSFTree.mapLeaves_eval (Finset.map σ.toEmbedding) T₁ c]
        refine MSFTree.liftEmb_eval σ (T₁.mapLeaves _) c p fun a b => ?_
        dsimp only [c]
        simp [Fin.castOrderIso]
      rw [heval, hcorr₁ c, hunique p]
    · simp [T₂, hd₁]
  have hle2 : optDepth ends₁ ≤ optDepth ends₂ := by
    obtain ⟨T₂, hcorr₂, hd₂⟩ := exists_opt_msfDT ends₂
    let T₁ : MSFDT e₁ := (T₂.mapLeaves (Finset.map σ.symm.toEmbedding)).liftEmb σ.symm
    refine (optDepth_le_of_correct (T := T₁) fun q => ?_).trans ?_
    · let p : Equiv.Perm (Fin e₂) :=
        σ.symm.trans (q.trans (Fin.castOrderIso heq).toEquiv)
      have hqp : σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv) = q := by
        ext x; simp [p, Fin.castOrderIso]
      have heval : T₁.eval q = (T₂.eval p).map σ.symm.toEmbedding := by
        rw [← MSFTree.mapLeaves_eval (Finset.map σ.symm.toEmbedding) T₂ p]
        refine MSFTree.liftEmb_eval σ.symm (T₂.mapLeaves _) p q fun a b => ?_
        dsimp only [p]
        simp [Fin.castOrderIso]
      have hu := hunique p
      dsimp only at hu
      rw [hqp] at hu
      have hinv : Cslib.Multigraph.msf ends₁ q Finset.univ =
          (Cslib.Multigraph.msf ends₂ p Finset.univ).map σ.symm.toEmbedding := by
        rw [hu, Finset.map_map]
        ext x
        simp
      rw [heval, hcorr₂ p, hinv]
    · simp [T₁, hd₂]
  exact le_antisymm hle2 hle1

theorem maskEdgePairs_cast {r₁ r₂ mask : ℕ} (hrr : r₁ ≤ r₂)
    (hmask : mask < 2 ^ maxSimpleEdges r₁) :
    maskEdgePairs r₂ mask =
      (maskEdgePairs r₁ mask).map (Prod.map (Fin.castLE hrr) (Fin.castLE hrr)) := by
  have hlen : maxSimpleEdges r₁ ≤ (allPairs r₂).length := by
    rw [length_allPairs]
    dsimp only [maxSimpleEdges]
    exact Nat.div_le_div_right (Nat.mul_le_mul hrr (Nat.sub_le_sub_right hrr 1))
  have htake : (allPairs r₂).take (maxSimpleEdges r₁) =
      (allPairs r₁).map (Prod.map (Fin.castLE hrr) (Fin.castLE hrr)) := by
    refine List.ext_getElem ?_ fun k hk1 hk2 => ?_
    · simp only [List.length_take, List.length_map, length_allPairs]
      rw [length_allPairs] at hlen
      exact Nat.min_eq_left hlen
    · have hk_lt : k < (allPairs r₁).length := by simpa [List.length_map] using hk2
      let p := (allPairs r₁)[k]'hk_lt
      have hplt : p.1.val < p.2.val := allPairs_lt (List.getElem_mem hk_lt)
      have hpidx : pairIdx p.1.val p.2.val = k := pairIdx_getElem_allPairs hk_lt
      rw [List.getElem_take, List.getElem_map]
      have hget₂ := getElem_allPairs_pairIdx (r := r₂)
        (a := Fin.castLE hrr p.1) (b := Fin.castLE hrr p.2) (by simpa using hplt)
      dsimp only [p] at hget₂ hpidx
      simpa [hpidx, Prod.map] using hget₂
  have hsplit : allPairs r₂ =
      (allPairs r₁).map (Prod.map (Fin.castLE hrr) (Fin.castLE hrr)) ++
        (allPairs r₂).drop (maxSimpleEdges r₁) := by
    rw [← htake, List.take_append_drop]
  dsimp only [maskEdgePairs]
  rw [hsplit]
  refine filterMaskAux_map_append _ mask (allPairs r₁) _ 0 fun k hk => ?_
  rw [length_allPairs] at hk
  exact Nat.testBit_eq_false_of_lt
    (hmask.trans_le (Nat.pow_le_pow_right (by omega) (by simpa using hk)))

theorem optDepth_endsOfMask_le {r₁ r₂ mask : ℕ} (hrr : r₁ ≤ r₂)
    (hmask : mask < 2 ^ maxSimpleEdges r₁) :
    optDepth (endsOfMask r₁ mask) = optDepth (endsOfMask r₂ mask) := by
  have hmap := maskEdgePairs_cast hrr hmask
  have hlen : (maskEdgePairs r₂ mask).length = (maskEdgePairs r₁ mask).length := by
    rw [hmap, List.length_map]
  let σ : Fin (maskEdgePairs r₁ mask).length ≃ Fin (maskEdgePairs r₂ mask).length :=
    (Fin.castOrderIso hlen.symm).toEquiv
  let φ : Fin r₁ ↪ Fin r₂ := Fin.castLEEmb hrr
  refine optDepth_reindex (endsOfMask r₁ mask) (endsOfMask r₂ mask) σ φ fun i => ?_
  have hget : (maskEdgePairs r₂ mask)[(σ i).val] =
      Prod.map (Fin.castLE hrr) (Fin.castLE hrr) (maskEdgePairs r₁ mask)[i.val] := by
    rw [List.getElem_of_eq hmap, List.getElem_map]
    rfl
  dsimp only [endsOfMask, φ]
  simp only [Fin.getElem_fin] at *
  rw [hget]
  rfl

private theorem mask_of_edgeFun_testBit {e R : ℕ} (idxFun : Fin e ↪ Fin R) (k : ℕ) :
    (∑ i : Fin e, 2 ^ (idxFun i).val).testBit k =
      decide (∃ i : Fin e, (idxFun i).val = k) := by
  let S : Finset (Fin R) := Finset.univ.map idxFun
  have hsum : (∑ i : Fin e, (2 : ℕ) ^ (idxFun i).val) = maskOfFinset S := by
    rw [maskOfFinset, Finset.sum_map]
  rw [hsum, testBit_maskOfFinset]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨hk, hmem⟩
    rw [Finset.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    exact ⟨i, congrArg Fin.val hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(idxFun i).isLt, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, Fin.ext rfl⟩⟩

private theorem exists_ordered_pair_of_not_isDiag {n : ℕ} {s : Sym2 (Fin n)} (hnd : ¬ s.IsDiag) :
    ∃ p : Fin n × Fin n, p.1.val < p.2.val ∧ s = s(p.1, p.2) := by
  induction s using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hnd
    have hne : a.val ≠ b.val := fun h => hnd (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(a, b), hlt, rfl⟩
    · exact ⟨(b, a), hgt, Sym2.eq_swap⟩

theorem optDepth_eq_endsOfMask_of_isSimple {e n : ℕ} (ends : Fin e → Sym2 (Fin n))
    (hG : IsSimple ends) :
    ∃ mask < 2 ^ maxSimpleEdges n, (maskEdgePairs n mask).length = e ∧
      optDepth ends = optDepth (endsOfMask n mask) := by
  classical
  let pairOf : Fin e → Fin n × Fin n := fun i =>
    Classical.choose (exists_ordered_pair_of_not_isDiag (hG.1 i))
  have hpair_lt : ∀ i : Fin e, (pairOf i).1.val < (pairOf i).2.val := fun i =>
    (Classical.choose_spec (exists_ordered_pair_of_not_isDiag (hG.1 i))).1
  have hpair_sym2 : ∀ i : Fin e, ends i = s((pairOf i).1, (pairOf i).2) := fun i =>
    (Classical.choose_spec (exists_ordered_pair_of_not_isDiag (hG.1 i))).2
  let idxFun : Fin e ↪ Fin (maxSimpleEdges n) :=
    ⟨fun i => ⟨pairIdx (pairOf i).1.val (pairOf i).2.val,
        pairIdx_lt_maxSimpleEdges (hpair_lt i) (pairOf i).2.isLt⟩,
     fun i₁ i₂ heq => by
       have heqv : pairIdx (pairOf i₁).1.val (pairOf i₁).2.val =
           pairIdx (pairOf i₂).1.val (pairOf i₂).2.val := congrArg Fin.val heq
       have hg₁ := getElem_allPairs_pairIdx (hpair_lt i₁)
       have hg₂ := getElem_allPairs_pairIdx (hpair_lt i₂)
       have hpeq : pairOf i₁ = pairOf i₂ := by
         rw [← Prod.mk.eta (p := pairOf i₁), ← Prod.mk.eta (p := pairOf i₂), ← hg₁, ← hg₂]
         simp only [heqv]
       refine hG.2 ?_
       rw [hpair_sym2 i₁, hpair_sym2 i₂, hpeq]⟩
  let mask := ∑ i : Fin e, 2 ^ (idxFun i).val
  have hmask_lt : mask < 2 ^ maxSimpleEdges n := by
    have hsum : mask = maskOfFinset (Finset.univ.map idxFun) := by
      simp [mask, maskOfFinset, Finset.sum_map]
    rw [hsum]
    exact maskOfFinset_lt _
  have hmem_iff : ∀ k : ℕ, (mask.testBit k = true) ↔ ∃ i : Fin e, (idxFun i).val = k := fun k => by
    rw [mask_of_edgeFun_testBit idxFun k, decide_eq_true_iff]
  have hspec := filterMaskAux_bij mask (allPairs n) (nodup_allPairs n) 0
  have hmem_pairs : ∀ i : Fin e, pairOf i ∈ maskEdgePairs n mask := fun i => by
    have hget := getElem_allPairs_pairIdx (hpair_lt i)
    have hmem := hspec.2 (pairIdx (pairOf i).1.val (pairOf i).2.val)
      (by rw [length_allPairs]; exact (idxFun i).isLt)
      (by rw [Nat.zero_add]; exact (hmem_iff _).mpr ⟨i, rfl⟩)
    rw [hget] at hmem
    exact hmem
  have hpairs_mem : ∀ p ∈ maskEdgePairs n mask, ∃ i : Fin e, pairOf i = p := by
    intro p hp
    obtain ⟨j, hj, rfl, htb⟩ := hspec.1 p hp
    rw [Nat.zero_add] at htb
    obtain ⟨i, hi⟩ := (hmem_iff j).mp htb
    refine ⟨i, ?_⟩
    have hget := getElem_allPairs_pairIdx (hpair_lt i)
    have hji : j = pairIdx (pairOf i).1.val (pairOf i).2.val := hi.symm
    simpa [hji] using hget.symm
  let f : Fin e → Fin (maskEdgePairs n mask).length := fun i =>
    ⟨(maskEdgePairs n mask).idxOf (pairOf i), List.idxOf_lt_length_of_mem (hmem_pairs i)⟩
  have hf_get : ∀ i : Fin e, (maskEdgePairs n mask)[(f i).val] = pairOf i := fun i =>
    List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem_pairs i))
  have hf_inj : Function.Injective f := fun i₁ i₂ he => by
    have h1 := hf_get i₁
    have h2 := hf_get i₂
    have hpeq : pairOf i₁ = pairOf i₂ := by
      rw [← h1, ← h2]
      exact congrArg
        (fun k : Fin (maskEdgePairs n mask).length => (maskEdgePairs n mask)[k.val]) he
    refine hG.2 ?_
    rw [hpair_sym2 i₁, hpair_sym2 i₂, hpeq]
  have hf_surj : Function.Surjective f := fun k => by
    obtain ⟨i, hi⟩ := hpairs_mem _ (List.getElem_mem k.isLt)
    refine ⟨i, Fin.ext ?_⟩
    have hn : (maskEdgePairs n mask).Nodup := filterMaskAux_nodup mask (nodup_allPairs n) 0
    have hg := hf_get i
    rw [hi] at hg
    exact hn.getElem_inj_iff.mp hg
  let σ : Fin e ≃ Fin (maskEdgePairs n mask).length := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hlen : (maskEdgePairs n mask).length = e := by
    simpa using (Fintype.card_congr σ.symm)
  refine ⟨mask, hmask_lt, hlen, ?_⟩
  refine optDepth_reindex ends (endsOfMask n mask) σ (Equiv.refl (Fin n)).toEmbedding fun i => ?_
  have hget : (maskEdgePairs n mask)[(σ i).val] = pairOf i := hf_get i
  change Sym2.map id (ends i) = endsOfMask n mask (σ i)
  rw [Sym2.map_id, hpair_sym2 i]
  dsimp only [endsOfMask]
  simp only [Fin.getElem_fin, hget]
  rfl

/-! ## Worst-Case Optimal Depth `T*(m, n)` -/

/-- Worst-case optimal decision-tree depth `T*(m, n)` over all simple graphs on `n` vertices with
at most `m` edges. -/
@[expose] noncomputable def optDepthMN (m n : ℕ) : ℕ :=
  ((Finset.range (2 ^ maxSimpleEdges n)).filter fun mask =>
    (maskEdgePairs n mask).length ≤ m).sup fun mask => optDepth (endsOfMask n mask)

theorem optDepth_endsOfMask_le_optDepthMN {m n mask : ℕ}
    (hmask : mask < 2 ^ maxSimpleEdges n) (hlen : (maskEdgePairs n mask).length ≤ m) :
    optDepth (endsOfMask n mask) ≤ optDepthMN m n := by
  refine Finset.le_sup (f := fun k => optDepth (endsOfMask n k)) ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmask, hlen⟩

theorem exists_endsOfMask_eq_optDepthMN (m n : ℕ) :
    ∃ mask < 2 ^ maxSimpleEdges n, (maskEdgePairs n mask).length ≤ m ∧
      optDepth (endsOfMask n mask) = optDepthMN m n := by
  let S := (Finset.range (2 ^ maxSimpleEdges n)).filter fun mask =>
    (maskEdgePairs n mask).length ≤ m
  have hne : S.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.two_pow_pos _), by simp [maskEdgePairs_zero]⟩⟩
  obtain ⟨mask, hmem, hsup⟩ := Finset.exists_mem_eq_sup S hne (fun k => optDepth (endsOfMask n k))
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  exact ⟨mask, hmem.1, hmem.2, hsup.symm⟩

theorem optDepth_le_optDepthMN_of_isSimple {e n m : ℕ} (ends : Fin e → Sym2 (Fin n))
    (hG : IsSimple ends) (hle : e ≤ m) :
    optDepth ends ≤ optDepthMN m n := by
  obtain ⟨mask, hmask, hlen, heq⟩ := optDepth_eq_endsOfMask_of_isSimple ends hG
  rw [heq]
  exact optDepth_endsOfMask_le_optDepthMN hmask (hlen ▸ hle)

/-- Uniform decision-tree upper bound `T*(m, n) ≤ f m` from any monotone comparison-query MSF
algorithm family solving simple graphs on `r` vertices with `e` edges in at most `f e` queries. -/
theorem optDepthMN_le_of_freeM (m n : ℕ) (f : ℕ → ℕ) (hf_mono : Monotone f)
    (alg : ∀ {e r : ℕ}, (Fin e → Sym2 (Fin r)) → FreeM (LEQuery (Fin e)) (Finset (Fin e)))
    (hcorr : ∀ {e r : ℕ} (ends : Fin e → Sym2 (Fin r)), IsSimple ends →
      ∀ p : Equiv.Perm (Fin e),
        (alg ends).eval (LEQuery.keyOracle p) = Cslib.Multigraph.msf ends p Finset.univ)
    (hdepth : ∀ {e r : ℕ} (ends : Fin e → Sym2 (Fin r)), IsSimple ends →
      ∀ p : Equiv.Perm (Fin e),
        (alg ends).countQueries (LEQuery.keyOracle p) ≤ f e) :
    optDepthMN m n ≤ f m := by
  obtain ⟨mask, _, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m n
  rw [← heq]
  have hs := endsOfMask_isSimple n mask
  exact (optDepth_le_of_freeM (endsOfMask n mask) (alg (endsOfMask n mask))
    (f (maskEdgePairs n mask).length) (hcorr _ hs) (hdepth _ hs)).trans (hf_mono hlen)

/-! ## Propositions 5.1 and 5.2 ([PettieRamachandran2002]) -/

/-- Path variables inspected along decision tree `T` when following permutation `p`. -/
@[expose] def MSFTree.traceVars {e : ℕ} {α : Type} :
    MSFTree e α → Equiv.Perm (Fin e) → Finset (Fin e)
  | .leaf _, _ => ∅
  | .node i j l r, p => {i, j} ∪ if (p i).val < (p j).val then l.traceVars p else r.traceVars p

theorem MSFTree.card_traceVars_le {e : ℕ} {α : Type} (T : MSFTree e α)
    (p : Equiv.Perm (Fin e)) : (T.traceVars p).card ≤ 2 * T.depth := by
  induction T with
  | leaf _ => simp [MSFTree.traceVars, MSFTree.depth]
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.traceVars, MSFTree.depth]
    have hpair : ({i, j} : Finset (Fin e)).card ≤ 2 := Finset.card_insert_le _ _
    have hu := Finset.card_union_le ({i, j} : Finset (Fin e))
      (if (p i).val < (p j).val then l.traceVars p else r.traceVars p)
    split_ifs at hu ⊢
    · omega
    · omega

theorem MSFTree.eval_eq_of_not_mem_traceVars {e : ℕ} {α : Type} (T : MSFTree e α)
    (p q : Equiv.Perm (Fin e)) (iStar : Fin e) (hnot : iStar ∉ T.traceVars p)
    (hagree : ∀ a b : Fin e, a ≠ iStar → b ≠ iStar →
      ((q a).val < (q b).val ↔ (p a).val < (p b).val)) :
    T.eval q = T.eval p := by
  induction T with
  | leaf _ => rfl
  | node a b l r ihl ihr =>
    dsimp only [MSFTree.traceVars] at hnot
    have han : a ≠ iStar := fun h => hnot (Finset.mem_union_left _ (by simp [h]))
    have hbn : b ≠ iStar := fun h => hnot (Finset.mem_union_left _ (by simp [h]))
    have hsub : iStar ∉ if (p a).val < (p b).val then l.traceVars p else r.traceVars p :=
      fun h => hnot (Finset.mem_union_right _ h)
    dsimp only [MSFTree.eval]
    by_cases hlt : (p a).val < (p b).val
    · have hltq : (q a).val < (q b).val := (hagree a b han hbn).mpr hlt
      simp only [hlt, ↓reduceIte] at hsub ⊢
      simp only [hltq, ↓reduceIte]
      exact ihl hsub
    · have hltq : ¬ ((q a).val < (q b).val) := fun h => hlt ((hagree a b han hbn).mp h)
      simp only [hlt, ↓reduceIte] at hsub ⊢
      simp only [hltq, ↓reduceIte]
      exact ihr hsub

private theorem joins_empty_iff {E V : Type*} (ends : E → Sym2 V) (u v : V) :
    Cslib.Multigraph.Joins ends (∅ : Set E) u v ↔ u = v := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      obtain ⟨_, hmem, _⟩ := hstep
      exact False.elim (Set.notMem_empty _ hmem)
  · intro h
    subst h
    exact Cslib.Multigraph.Joins.refl _

private theorem exists_perm_min_and_max {e : ℕ} (iStar : Fin e) :
    (∃ pMin : Equiv.Perm (Fin e), pMin iStar = ⟨0, Nat.zero_lt_of_lt iStar.isLt⟩ ∧
      ∀ a b : Fin e, a ≠ iStar → b ≠ iStar → ((pMin a).val < (pMin b).val ↔ a.val < b.val)) ∧
    (∃ pMax : Equiv.Perm (Fin e),
      pMax iStar = ⟨e - 1, Nat.sub_lt (Nat.zero_lt_of_lt iStar.isLt) Nat.one_pos⟩ ∧
      ∀ a b : Fin e, a ≠ iStar → b ≠ iStar → ((pMax a).val < (pMax b).val ↔ a.val < b.val)) := by
  have hepos : 0 < e := Nat.zero_lt_of_lt iStar.isLt
  let fMin : Fin e → Fin e := fun j =>
    if j = iStar then ⟨0, hepos⟩
    else if hlt : j.val < iStar.val then ⟨j.val + 1, by have := iStar.isLt; omega⟩
    else j
  have hfMin_pos : ∀ x : Fin e, x ≠ iStar → 0 < (fMin x).val := fun x hx => by
    dsimp only [fMin]
    simp only [hx, ↓reduceIte]
    split_ifs with hlt
    · simp
    · have hxne : x.val ≠ iStar.val := fun h => hx (Fin.ext h)
      omega
  have hfMin_inj : Function.Injective fMin := fun a b hab => by
    by_cases ha : a = iStar <;> by_cases hb : b = iStar
    · exact ha.trans hb.symm
    · have h0 : (fMin a).val = 0 := by simp [fMin, ha]
      have hpos := hfMin_pos b hb
      rw [← hab, h0] at hpos
      omega
    · have h0 : (fMin b).val = 0 := by simp [fMin, hb]
      have hpos := hfMin_pos a ha
      rw [hab, h0] at hpos
      omega
    dsimp only [fMin] at hab
    simp only [ha, hb, ↓reduceIte] at hab
    split_ifs at hab with h1 h2
    · exact Fin.ext (by have := congrArg Fin.val hab; simp at this; omega)
    · have hne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
      have := congrArg Fin.val hab; simp at this; omega
    · have hne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
      have := congrArg Fin.val hab; simp at this; omega
    · exact hab
  let pMin := Equiv.ofBijective fMin
    ((Fintype.bijective_iff_injective_and_card fMin).mpr ⟨hfMin_inj, rfl⟩)
  let fMax : Fin e → Fin e := fun j =>
    if j = iStar then ⟨e - 1, Nat.sub_lt hepos Nat.one_pos⟩
    else if hlt : j.val < iStar.val then j
    else ⟨j.val - 1, by have := j.isLt; omega⟩
  have hfMax_lt : ∀ x : Fin e, x ≠ iStar → (fMax x).val < e - 1 := fun x hx => by
    dsimp only [fMax]
    simp only [hx, ↓reduceIte]
    split_ifs with hlt
    · have hxlt := x.isLt; have := iStar.isLt; omega
    · have hxlt := x.isLt
      have hxne : x.val ≠ iStar.val := fun h => hx (Fin.ext h)
      dsimp only
      omega
  have hfMax_inj : Function.Injective fMax := fun a b hab => by
    by_cases ha : a = iStar <;> by_cases hb : b = iStar
    · exact ha.trans hb.symm
    · have he1 : (fMax a).val = e - 1 := by simp [fMax, ha]
      have hlt := hfMax_lt b hb
      rw [← hab, he1] at hlt
      omega
    · have he1 : (fMax b).val = e - 1 := by simp [fMax, hb]
      have hlt := hfMax_lt a ha
      rw [hab, he1] at hlt
      omega
    dsimp only [fMax] at hab
    simp only [ha, hb, ↓reduceIte] at hab
    split_ifs at hab with h1 h2
    · exact hab
    · have hne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
      have hb_lt := b.isLt
      have := congrArg Fin.val hab; dsimp only at this; omega
    · have hne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
      have ha_lt := a.isLt
      have := congrArg Fin.val hab; dsimp only at this; omega
    · exact Fin.ext (by
        have ha_ne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
        have hb_ne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
        have := congrArg Fin.val hab; simp at this; omega)
  let pMax := Equiv.ofBijective fMax
    ((Fintype.bijective_iff_injective_and_card fMax).mpr ⟨hfMax_inj, rfl⟩)
  refine ⟨⟨pMin, ?_, ?_⟩, ⟨pMax, ?_, ?_⟩⟩
  · simp [pMin, fMin]
  · intro a b ha hb
    simp only [pMin, Equiv.ofBijective_apply, fMin, ha, hb, ↓reduceIte]
    have ha_ne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
    have hb_ne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
    split_ifs <;> simp <;> omega
  · simp [pMax, fMax]
  · intro a b ha hb
    simp only [pMax, Equiv.ofBijective_apply, fMax, ha, hb, ↓reduceIte]
    have ha_ne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
    have hb_ne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
    split_ifs <;> simp <;> omega

/-- General cycle-cover lower bound: if every edge of `ends : Fin e → Sym2 (Fin n)` has
distinct endpoints and lies on a simple cycle, then `e ≤ 2 * optDepth ends`. -/
theorem edges_le_two_mul_optDepth_of_all_on_cycle {e n : ℕ}
    (ends : Fin e → Sym2 (Fin n)) (hnoloop : ∀ i : Fin e, ¬ (ends i).IsDiag)
    (hcyc : ∀ i : Fin e, ∀ a b : Fin n, ends i = s(a, b) →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e)) a b) :
    e ≤ 2 * optDepth ends := by
  by_contra hlt
  have hcard : 2 * optDepth ends < e := by omega
  obtain ⟨T, hcorr, hd⟩ := exists_opt_msfDT ends
  let p0 : Equiv.Perm (Fin e) := Equiv.refl _
  have htv_lt : (T.traceVars p0).card < Finset.univ.card (α := Fin e) := by
    have := T.card_traceVars_le p0
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨iStar, _, hiStar⟩ := Finset.exists_mem_notMem_of_card_lt_card htv_lt
  obtain ⟨⟨pMin, hpMin0, hpMin_ord⟩, ⟨pMax, hpMaxE, hpMax_ord⟩⟩ :=
    exists_perm_min_and_max iStar
  have hevMin : T.eval pMin = T.eval p0 :=
    T.eval_eq_of_not_mem_traceVars p0 pMin iStar hiStar fun a b ha hb => by
      simpa [p0] using hpMin_ord a b ha hb
  have hevMax : T.eval pMax = T.eval p0 :=
    T.eval_eq_of_not_mem_traceVars p0 pMax iStar hiStar fun a b ha hb => by
      simpa [p0] using hpMax_ord a b ha hb
  have huEq : Cslib.Multigraph.msf ends pMin Finset.univ =
      Cslib.Multigraph.msf ends pMax Finset.univ := by
    rw [← hcorr pMin, ← hcorr pMax, hevMin, hevMax]
  induction hi : ends iStar using Sym2.ind with
  | _ a b =>
    have hin : iStar ∈ Cslib.Multigraph.msf ends pMin Finset.univ := by
      rw [Cslib.Multigraph.mem_msf_iff pMin hi]
      refine ⟨Finset.mem_univ _, fun hc => ?_⟩
      have hemp : {f | f ∈ (Finset.univ : Finset (Fin e)) ∧ pMin f < pMin iStar} = ∅ := by
        ext x
        simp [Fin.lt_def, hpMin0]
      rw [hemp, joins_empty_iff] at hc
      subst hc
      exact hnoloop iStar (by simp [hi])
    have hout : iStar ∉ Cslib.Multigraph.msf ends pMax Finset.univ := by
      refine Cslib.Multigraph.notMem_msf_of_joins (w := pMax)
        (X := (Finset.univ.erase iStar : Finset (Fin e))) (by simp) (fun f hf => ?_) hi
        (hcyc iStar a b hi)
      rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff] at hf
      change (pMax f).val < (pMax iStar).val
      rw [hpMaxE]
      have he_pos : 0 < e := Nat.zero_lt_of_lt iStar.isLt
      have hlt_val : (pMax f).val < e := (pMax f).isLt
      have hne : (pMax f).val ≠ e - 1 := fun he => hf.2 (pMax.injective (by
        rw [hpMaxE]; exact Fin.ext he))
      dsimp only
      omega
    exact hout (huEq ▸ hin)

private theorem nat_cycle_edge_on_cycle {e n : ℕ} (ends : Fin e → Sym2 (Fin n))
    (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (hverts : ∀ t : Fin k, ∀ _ht : t.val + 1 < k,
      ∃ i : Fin e, ends i = s(⟨t.val, Nat.lt_of_lt_of_le t.isLt hkn⟩, ⟨t.val + 1, by omega⟩))
    (hwrap : ∃ i : Fin e, ends i = s(⟨0, by omega⟩, ⟨k - 1, by omega⟩))
    (hother : ∀ i : Fin e, ∀ v ∈ ends i, v.val < k) :
    ∀ i : Fin e, ∀ a b : Fin n, ends i = s(a, b) →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e)) a b := by
  classical
  let cEdge : ℕ → Fin e := fun t =>
    if ht : t + 1 < k then (hverts ⟨t, by omega⟩ ht).choose else hwrap.choose
  have hcEdge_sym : ∀ t (ht : t + 1 < k),
      ends (cEdge t) = s(⟨t, by omega⟩, ⟨t + 1, by omega⟩) := fun t ht => by
    simp only [cEdge, ht, ↓reduceDIte]
    exact (hverts ⟨t, by omega⟩ ht).choose_spec
  have hcWrap_sym : ends (cEdge (k - 1)) = s(⟨0, by omega⟩, ⟨k - 1, by omega⟩) := by
    have hnot : ¬ (k - 1 + 1 < k) := by omega
    simp only [cEdge, hnot, ↓reduceDIte]
    exact hwrap.choose_spec
  have conn_chain : ∀ (i : Fin e) (a b : ℕ), ∀ hab : a ≤ b, ∀ hbk : b < k,
      (∀ t, a ≤ t → t < b → cEdge t ≠ i) →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e))
        ⟨a, by omega⟩ ⟨b, by omega⟩ := by
    intro i a b hab hbk havoid
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; exact Cslib.Multigraph.Joins.refl _
    | succ b ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact Cslib.Multigraph.Joins.refl _
      · have ih' := ih (by omega) (by omega) fun t ht1 ht2 => havoid t ht1 (by omega)
        have he_mem : cEdge b ∈ ((Finset.univ.erase i : Finset (Fin e)) : Set (Fin e)) :=
          Finset.mem_coe.mpr (Finset.mem_erase.mpr
            ⟨havoid b (by omega) (Nat.lt_succ_self b), Finset.mem_univ _⟩)
        exact ih'.trans (Cslib.Multigraph.Joins.of_mem he_mem (hcEdge_sym b hbk))
  have conn_wrap : ∀ (i : Fin e), cEdge (k - 1) ≠ i →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e))
        ⟨0, by omega⟩ ⟨k - 1, by omega⟩ := fun i hne =>
    Cslib.Multigraph.Joins.of_mem
      (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)) hcWrap_sym
  intro i a b hab
  have h1 : a.val < k := hother i a (hab ▸ Sym2.mem_mk_left a b)
  have h2 : b.val < k := hother i b (hab ▸ Sym2.mem_mk_right a b)
  by_cases hcy : ∃ t < k, cEdge t = i
  · obtain ⟨t, htk, rfl⟩ := hcy
    by_cases htk1 : t + 1 < k
    · have hne_all : ∀ s < k, s ≠ t → cEdge s ≠ cEdge t := fun s hs hst h => by
        by_cases hs1 : s + 1 < k
        · have hseq : s((⟨s, by omega⟩ : Fin n), ⟨s + 1, by omega⟩) =
              s((⟨t, by omega⟩ : Fin n), ⟨t + 1, by omega⟩) :=
            (hcEdge_sym s hs1).symm.trans (h ▸ hcEdge_sym t htk1)
          rcases Sym2.eq_iff.mp hseq with ⟨e1, _⟩ | ⟨e1, e2⟩
          · exact hst (congrArg Fin.val e1)
          · have v1 : s = t + 1 := congrArg Fin.val e1
            have v2 : s + 1 = t := congrArg Fin.val e2
            omega
        · have hsk : s = k - 1 := by omega
          subst hsk
          have hseq : s((⟨0, by omega⟩ : Fin n), ⟨k - 1, by omega⟩) =
              s((⟨t, by omega⟩ : Fin n), ⟨t + 1, by omega⟩) :=
            hcWrap_sym.symm.trans (h ▸ hcEdge_sym t htk1)
          rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨e1, _⟩
          · have v1 : 0 = t := congrArg Fin.val e1
            have v2 : k - 1 = t + 1 := congrArg Fin.val e2
            omega
          · have v1 : 0 = t + 1 := congrArg Fin.val e1
            omega
      have p1 := conn_chain (cEdge t) (t + 1) (k - 1) (by omega) (by omega) fun s hs1 hs2 =>
        hne_all s (by omega) (by omega)
      have p2 := (conn_wrap (cEdge t) (hne_all (k - 1) (by omega) (by omega))).symm
      have p3 := conn_chain (cEdge t) 0 t (Nat.zero_le _) (by omega) fun s _ hs2 =>
        hne_all s (by omega) (by omega)
      have hconn_tt1 := (p1.trans (p2.trans p3)).symm
      have hseq : s(⟨t, by omega⟩, ⟨t + 1, by omega⟩) = s(a, b) :=
        (hcEdge_sym t htk1).symm.trans hab
      rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact hconn_tt1
      · rw [← e1, ← e2]; exact hconn_tt1.symm
    · have htk_eq : t = k - 1 := by omega
      subst htk_eq
      have hne_pre : ∀ s, s + 1 < k → cEdge s ≠ cEdge (k - 1) := fun s hs h => by
        have hseq : s((⟨s, by omega⟩ : Fin n), ⟨s + 1, by omega⟩) =
            s((⟨0, by omega⟩ : Fin n), ⟨k - 1, by omega⟩) :=
          (hcEdge_sym s hs).symm.trans (h ▸ hcWrap_sym)
        rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨_, e2⟩
        · have v1 : s = 0 := congrArg Fin.val e1
          have v2 : s + 1 = k - 1 := congrArg Fin.val e2
          omega
        · have v2 : s + 1 = 0 := congrArg Fin.val e2
          omega
      have p := conn_chain (cEdge (k - 1)) 0 (k - 1) (Nat.zero_le _) (by omega)
        fun s _ hs => hne_pre s (by omega)
      have hseq : s(⟨0, by omega⟩, ⟨k - 1, by omega⟩) = s(a, b) := hcWrap_sym.symm.trans hab
      rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact p
      · rw [← e1, ← e2]; exact p.symm
  · have hall : ∀ s, s < k - 1 → cEdge s ≠ i := fun s hs h => hcy ⟨s, by omega, h⟩
    have p1 := conn_chain i 0 a.val (Nat.zero_le _) h1 fun s _ hs => hall s (by omega)
    have p2 := conn_chain i 0 b.val (Nat.zero_le _) h2 fun s _ hs => hall s (by omega)
    exact p1.symm.trans p2

/-- Proposition 5.1 of [PettieRamachandran2002]: for `3 ≤ m`, `3 ≤ n`, and
`m ≤ maxSimpleEdges n`, `m ≤ 2 * optDepthMN m n`. -/
theorem le_two_mul_optDepthMN {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (hle : m ≤ maxSimpleEdges n) :
    m ≤ 2 * optDepthMN m n := by
  classical
  let k := min m n
  have hk3 : 3 ≤ k := le_min hm hn
  have hkm : k ≤ m := min_le_left m n
  have hkn : k ≤ n := min_le_right m n
  let cycIdxs : List (Fin (maxSimpleEdges n)) :=
    (List.finRange (k - 1)).map (fun a =>
      ⟨pairIdx a.val (a.val + 1), pairIdx_lt_maxSimpleEdges (Nat.lt_succ_self _) (by omega)⟩) ++
    [⟨pairIdx 0 (k - 1), pairIdx_lt_maxSimpleEdges (by omega) (by omega)⟩]
  have hpair_inj : ∀ {a₁ a₂ b₁ b₂ : ℕ}, a₁ < b₁ → b₁ < n → a₂ < b₂ → b₂ < n →
      pairIdx a₁ b₁ = pairIdx a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ h11 h12 h21 h22 heq
    have g1 := getElem_allPairs_pairIdx (r := n) (a := ⟨a₁, by omega⟩) (b := ⟨b₁, h12⟩) h11
    have g2 := getElem_allPairs_pairIdx (r := n) (a := ⟨a₂, by omega⟩) (b := ⟨b₂, h22⟩) h21
    have hprod : (allPairs n)[pairIdx a₁ b₁]'(by
        rw [length_allPairs]; exact pairIdx_lt_maxSimpleEdges h11 h12) =
        (allPairs n)[pairIdx a₂ b₂]'(by
        rw [length_allPairs]; exact pairIdx_lt_maxSimpleEdges h21 h22) := by
      simp only [heq]
    rw [g1, g2] at hprod
    exact ⟨congrArg (fun p : Fin n × Fin n => p.1.val) hprod,
      congrArg (fun p : Fin n × Fin n => p.2.val) hprod⟩
  have hcyc_nd : cycIdxs.Nodup := by
    refine List.nodup_append.mpr ⟨?_, List.nodup_singleton _, fun x hx y hy hxy => ?_⟩
    · refine (List.nodup_finRange (k - 1)).map fun a b hab => ?_
      have hidx : pairIdx a.val (a.val + 1) = pairIdx b.val (b.val + 1) := congrArg Fin.val hab
      have heq := hpair_inj (Nat.lt_succ_self _) (by omega) (Nat.lt_succ_self _) (by omega) hidx
      exact Fin.ext heq.1
    · rw [List.mem_map] at hx
      rw [List.mem_singleton] at hy
      obtain ⟨a, _, rfl⟩ := hx
      subst hy
      have hidx : pairIdx a.val (a.val + 1) = pairIdx 0 (k - 1) := congrArg Fin.val hxy
      have heq := hpair_inj (Nat.lt_succ_self _) (by omega) (by omega) (by omega) hidx
      omega
  have hcyc_len : cycIdxs.length = k := by
    simp only [cycIdxs, List.length_append, List.length_map, List.length_finRange,
      List.length_singleton]
    omega
  let rest : List (Fin (maxSimpleEdges n)) :=
    (List.finRange (maxSimpleEdges n)).filter fun x => x ∉ cycIdxs
  have hrest_part : cycIdxs.toFinset ∪ rest.toFinset = Finset.univ := by
    ext x
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_univ, iff_true, rest,
      List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact em (x ∈ cycIdxs)
  have hrest_disj : Disjoint cycIdxs.toFinset rest.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hrx
    simp only [List.mem_toFinset, rest, List.mem_filter, decide_eq_true_eq] at hx hrx
    exact hrx.2 hx
  have hrest_len : k + rest.length = maxSimpleEdges n := by
    rw [← hcyc_len, ← List.toFinset_card_of_nodup hcyc_nd,
      ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
      ← Finset.card_union_of_disjoint hrest_disj, hrest_part, Finset.card_univ, Fintype.card_fin]
  let extra := rest.take (m - k)
  have hextra_len : extra.length = m - k := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  let chosen := cycIdxs ++ extra
  have hchosen_nd : chosen.Nodup := by
    refine List.nodup_append.mpr ⟨hcyc_nd,
      ((List.nodup_finRange _).filter _).sublist (List.take_sublist _ _),
      fun x hx y hy hxy => ?_⟩
    subst hxy
    have hyr := List.mem_of_mem_take hy
    simp only [rest, List.mem_filter, decide_eq_true_eq] at hyr
    exact hyr.2 hx
  have hchosen_len : chosen.length = m := by
    simp only [chosen, extra, List.length_append, List.length_take, hcyc_len]
    omega
  let S : Finset (Fin (maxSimpleEdges n)) := chosen.toFinset
  have hS_card : S.card = m := by
    rw [List.toFinset_card_of_nodup hchosen_nd, hchosen_len]
  let mask := maskOfFinset S
  have hmask_lt : mask < 2 ^ maxSimpleEdges n := maskOfFinset_lt S
  have hlen_mask : (maskEdgePairs n mask).length = m := by
    dsimp only [maskEdgePairs]
    rw [length_filterMaskAux, length_allPairs]
    have hfilt : ((Finset.range (maxSimpleEdges n)).filter fun j =>
        mask.testBit (0 + j)) = S.map ⟨Fin.val, Fin.val_injective⟩ := by
      ext j
      simp only [Nat.zero_add, Finset.mem_filter, Finset.mem_range, Finset.mem_map,
        Function.Embedding.coeFn_mk, mask, testBit_maskOfFinset, decide_eq_true_eq]
      constructor
      · rintro ⟨_, hj', hmem⟩
        exact ⟨⟨j, hj'⟩, hmem, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.isLt, x.isLt, hx⟩
    rw [hfilt, Finset.card_map, hS_card]
  have hspec := filterMaskAux_bij mask (allPairs n) (nodup_allPairs n) 0
  have hmem_pair : ∀ x ∈ cycIdxs, (allPairs n)[x.val]'(by
      rw [length_allPairs]; exact x.isLt) ∈ maskEdgePairs n mask := by
    intro x hx
    refine hspec.2 x.val (by rw [length_allPairs]; exact x.isLt) ?_
    simp only [Nat.zero_add, mask, testBit_maskOfFinset, decide_eq_true_eq]
    refine ⟨x.isLt, List.mem_toFinset.mpr (List.mem_append_left _ hx)⟩
  let ends := endsOfMask n mask
  have hverts : ∀ t : Fin k, ∀ _ht : t.val + 1 < k,
      ∃ i : Fin (maskEdgePairs n mask).length,
        ends i = s(⟨t.val, Nat.lt_of_lt_of_le t.isLt hkn⟩, ⟨t.val + 1, by omega⟩) := by
    intro t ht
    let idx : Fin (maxSimpleEdges n) :=
      ⟨pairIdx t.val (t.val + 1), pairIdx_lt_maxSimpleEdges (Nat.lt_succ_self _) (by omega)⟩
    have hidx_cyc : idx ∈ cycIdxs := by
      refine List.mem_append_left _ (List.mem_map.mpr ?_)
      exact ⟨⟨t.val, by omega⟩, List.mem_finRange _, rfl⟩
    have hp := hmem_pair idx hidx_cyc
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨pos, hpos.1⟩, ?_⟩
    dsimp only [ends, endsOfMask]
    have hget := getElem_allPairs_pairIdx (r := n)
      (a := ⟨t.val, by omega⟩) (b := ⟨t.val + 1, by omega⟩) (Nat.lt_succ_self _)
    simp only [Fin.getElem_fin, hpos.2, idx]
    rw [hget]
  have hwrap : ∃ i : Fin (maskEdgePairs n mask).length,
      ends i = s(⟨0, by omega⟩, ⟨k - 1, by omega⟩) := by
    let idx : Fin (maxSimpleEdges n) :=
      ⟨pairIdx 0 (k - 1), pairIdx_lt_maxSimpleEdges (by omega) (by omega)⟩
    have hidx_cyc : idx ∈ cycIdxs := List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hp := hmem_pair idx hidx_cyc
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨pos, hpos.1⟩, ?_⟩
    dsimp only [ends, endsOfMask]
    have hget := getElem_allPairs_pairIdx (r := n)
      (a := ⟨0, by omega⟩) (b := ⟨k - 1, by omega⟩) (by dsimp only; omega)
    simp only [Fin.getElem_fin, hpos.2, idx]
    rw [hget]
  have hother : ∀ i : Fin (maskEdgePairs n mask).length, ∀ v ∈ ends i, v.val < k := by
    intro i v hv
    by_cases hmn : m ≤ n
    · have hkm_eq : k = m := min_eq_left hmn
      have hmt : m - k = 0 := by omega
      have hmem := List.getElem_mem i.isLt
      obtain ⟨j, hj, hget, htb⟩ := hspec.1 _ hmem
      simp only [Nat.zero_add, mask, testBit_maskOfFinset, decide_eq_true_eq] at htb
      obtain ⟨hj2, hmemS⟩ := htb
      have hmemc : (⟨j, hj2⟩ : Fin (maxSimpleEdges n)) ∈ cycIdxs := by
        have hm' : (⟨j, hj2⟩ : Fin (maxSimpleEdges n)) ∈ chosen := List.mem_toFinset.mp hmemS
        simpa [chosen, extra, hmt] using hm'
      simp only [cycIdxs, List.mem_append, List.mem_map, List.mem_finRange,
        List.mem_singleton] at hmemc
      have hend : (maskEdgePairs n mask)[i.val] = (allPairs n)[j]'hj := hget.symm
      dsimp only [ends, endsOfMask] at hv
      simp only [Fin.getElem_fin, hend] at hv
      rcases hmemc with ⟨a, _, ha⟩ | heq
      · have hjv : j = pairIdx a.val (a.val + 1) := congrArg Fin.val ha.symm
        have ha_lt := a.isLt
        have hga := getElem_allPairs_pairIdx (r := n)
          (a := ⟨a.val, by omega⟩) (b := ⟨a.val + 1, by omega⟩) (Nat.lt_succ_self _)
        have hpair : (allPairs n)[j]'hj = (⟨a.val, by omega⟩, ⟨a.val + 1, by omega⟩) := by
          simpa [hjv] using hga
        rw [hpair] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> dsimp only <;> omega
      · have hjv : j = pairIdx 0 (k - 1) := congrArg Fin.val heq
        have hga := getElem_allPairs_pairIdx (r := n)
          (a := ⟨0, by omega⟩) (b := ⟨k - 1, by omega⟩) (by dsimp only; omega)
        have hpair : (allPairs n)[j]'hj = (⟨0, by omega⟩, ⟨k - 1, by omega⟩) := by
          simpa [hjv] using hga
        rw [hpair] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> dsimp only <;> omega
    · have hkn_eq : k = n := min_eq_right (by omega)
      rw [hkn_eq]
      exact v.isLt
  have hcyc_G := nat_cycle_edge_on_cycle ends k hk3 hkn hverts hwrap hother
  have hlb := edges_le_two_mul_optDepth_of_all_on_cycle ends
    (endsOfMask_isSimple n mask).1 hcyc_G
  rw [← hlen_mask]
  exact hlb.trans (Nat.mul_le_mul_left 2
    (optDepth_endsOfMask_le_optDepthMN hmask_lt le_rfl))

/-- Proposition 5.2 (edge monotonicity) of [PettieRamachandran2002]:
`optDepthMN m₁ n ≤ optDepthMN m₂ n` when `m₁ ≤ m₂`. -/
theorem optDepthMN_mono_m {m₁ m₂ n : ℕ} (h : m₁ ≤ m₂) : optDepthMN m₁ n ≤ optDepthMN m₂ n := by
  obtain ⟨mask, hmask, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m₁ n
  rw [← heq]
  exact optDepth_endsOfMask_le_optDepthMN hmask (hlen.trans h)

/-- Proposition 5.2 (vertex monotonicity) of [PettieRamachandran2002]:
`optDepthMN m n₁ ≤ optDepthMN m n₂` when `n₁ ≤ n₂`. -/
theorem optDepthMN_mono_n {m n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : optDepthMN m n₁ ≤ optDepthMN m n₂ := by
  obtain ⟨mask, hmask, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m n₁
  rw [← heq, optDepth_endsOfMask_le h hmask]
  have hpow : 2 ^ maxSimpleEdges n₁ ≤ 2 ^ maxSimpleEdges n₂ :=
    Nat.pow_le_pow_right (by omega)
      (Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right h 1)))
  have hlen2 : (maskEdgePairs n₂ mask).length = (maskEdgePairs n₁ mask).length := by
    rw [maskEdgePairs_cast h hmask, List.length_map]
  exact optDepth_endsOfMask_le_optDepthMN (hmask.trans_le hpow) (hlen2 ▸ hlen)

end Cslib.Query.MinimumSpanningForest
