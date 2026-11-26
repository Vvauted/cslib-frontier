/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Perm.Subperm
import CslibFrontier.Foundations.Data.List.Perm

/-!
# Structural lemmas for `List.Subperm`

This module adds generic structural lemmas for `List.Subperm` (`<+~`) missing from `Init`,
`Batteries`, and `Mathlib.Data.List.Perm.Subperm`:

* Mapping without requiring injectivity (`List.subperm_map`) and lifting a subpermutation back
  through `List.map` (`List.Subperm.exists_map`, `List.subperm_map_iff`).
* Preserving `List.Nodup` (`List.Subperm.nodup`).
* Erasing a matched head element (`List.Subperm.cons_erase_left`).
* Combining disjoint subpermutations (`List.Subperm.append_of_disjoint`) and flattening lists of
  pairwise-disjoint or aligned subpermutations (`List.Subperm.flatten_of_pairwise_disjoint`,
  `List.Subperm.flatten_of_forall₂`, `List.subperm_flatten_of_forall`).

## Main results

* `List.subperm_map`: `xs <+~ ys → xs.map f <+~ ys.map f` for arbitrary `f`.
* `List.Subperm.exists_map`, `List.subperm_map_iff`: preimage lifting along `List.map`.
* `List.Subperm.nodup`: subpermutations of duplicate-free lists are duplicate-free.
* `List.Subperm.cons_erase_left`: `x :: xs <+~ ys → xs <+~ ys.erase x`.
* `List.Subperm.append_of_disjoint`: disjoint subpermutations of `zs` concatenate into `zs`.
* `List.Subperm.flatten_of_pairwise_disjoint`: pairwise-disjoint subpermutations of `G` flatten
  into `G`.
* `List.Subperm.flatten_of_forall₂`, `List.subperm_flatten_of_forall`: pointwise subpermutations
  flatten to a subpermutation.
-/

public section

namespace List

/-- `List.Subperm` is preserved by `List.map` without requiring injectivity
(unlike `List.Subperm.map`, which assumes `Function.Injective f`). -/
theorem subperm_map {α β : Type*} {xs ys : List α} (f : α → β) (h : xs <+~ ys) :
    xs.map f <+~ ys.map f := by
  obtain ⟨zs, hp, hs⟩ := subperm_iff.mp h
  exact subperm_iff.mpr ⟨zs.map f, hp.map f, hs.map f⟩

/-- If `l` is a subpermutation of `xs.map f`, some subpermutation of `xs` maps onto `l`. -/
theorem Subperm.exists_map {α β : Type*} {f : α → β} {l : List β} {xs : List α}
    (h : l <+~ xs.map f) : ∃ zs : List α, zs <+~ xs ∧ zs.map f = l := by
  obtain ⟨u, hpu, hsu⟩ := subperm_iff.mp h
  obtain ⟨zs', hpz', hm'⟩ := hpu.exists_perm_map_eq
  obtain ⟨zs, hsz, hmap⟩ := sublist_map_iff.mp (hm'.symm ▸ hsu)
  exact ⟨zs, subperm_iff.mpr ⟨zs', hpz', hsz⟩, hmap.symm⟩

/-- A list `l` is a subpermutation of `xs.map f` iff some subpermutation of `xs` maps onto `l`. -/
theorem subperm_map_iff {α β : Type*} {f : α → β} {l : List β} {xs : List α} :
    l <+~ xs.map f ↔ ∃ zs : List α, zs <+~ xs ∧ zs.map f = l :=
  ⟨Subperm.exists_map, fun ⟨_, hz, hm⟩ => hm ▸ subperm_map f hz⟩

/-- Subpermutations preserve `List.Nodup`. -/
theorem Subperm.nodup {α : Type*} {xs ys : List α} (h : xs <+~ ys) (hys : ys.Nodup) :
    xs.Nodup := by
  obtain ⟨zs, hp, hs⟩ := subperm_iff.mp h
  exact hs.nodup (hp.nodup_iff.mpr hys)

/-- Dropping the head from the left of `x :: xs <+~ ys` erases `x` on the right. -/
theorem Subperm.cons_erase_left {α : Type*} [BEq α] [LawfulBEq α] {x : α} {xs ys : List α}
    (h : x :: xs <+~ ys) : xs <+~ ys.erase x := by
  simpa [erase_cons_head] using h.erase x

/-- Two disjoint subpermutations of `zs` concatenate to a subpermutation of `zs`. -/
theorem Subperm.append_of_disjoint {α : Type*} {xs ys zs : List α}
    (hx : xs <+~ zs) (hy : ys <+~ zs) (hdisj : Disjoint xs ys) :
    xs ++ ys <+~ zs := by
  classical
  rw [subperm_ext_iff] at hx hy ⊢
  intro a ha
  rw [count_append]
  rcases mem_append.mp ha with hax | hay
  · rw [count_eq_zero.mpr (hdisj hax), Nat.add_zero]
    exact hx a hax
  · have hanx : a ∉ xs := fun h => hdisj h hay
    rw [count_eq_zero.mpr hanx, Nat.zero_add]
    exact hy a hay

/-- A list of pairwise-disjoint subpermutations of `G` flattens to a subpermutation of `G`. -/
theorem Subperm.flatten_of_pairwise_disjoint {α : Type*} {ls : List (List α)} {G : List α}
    (hdisj : ls.Pairwise Disjoint) (hsub : ∀ l ∈ ls, l <+~ G) :
    ls.flatten <+~ G := by
  induction ls with
  | nil => exact nil_subperm
  | cons l ls ih =>
    rw [pairwise_cons] at hdisj
    have hflat : ls.flatten <+~ G :=
      ih hdisj.2 fun l' hl' => hsub l' (mem_cons_of_mem _ hl')
    have hdisj_flat : Disjoint l ls.flatten := by
      intro a ha hmem
      obtain ⟨l', hl', hal'⟩ := mem_flatten.mp hmem
      exact hdisj.1 l' hl' ha hal'
    exact (hsub l mem_cons_self).append_of_disjoint hflat hdisj_flat

/-- Pointwise subpermutations of aligned lists flatten to a subpermutation. -/
theorem Subperm.flatten_of_forall₂ {α : Type*} {xs ys : List (List α)}
    (h : Forall₂ (· <+~ ·) xs ys) : xs.flatten <+~ ys.flatten := by
  induction h with
  | nil => exact nil_subperm
  | cons h₁ _ ih => exact h₁.append ih

/-- Indexed pointwise subpermutations of equal-length lists flatten to a subpermutation. -/
theorem subperm_flatten_of_forall {α : Type*} (xs ys : List (List α))
    (hlen : xs.length = ys.length)
    (hsub : ∀ i (hi : i < xs.length), xs[i] <+~ ys[i]'(hlen ▸ hi)) :
    xs.flatten <+~ ys.flatten := by
  refine Subperm.flatten_of_forall₂ ?_
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact .nil
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      exact .cons (hsub 0 (Nat.zero_lt_succ _))
        (ih ys (by simpa using hlen) fun i hi => hsub (i + 1) (Nat.succ_lt_succ hi))

end List
