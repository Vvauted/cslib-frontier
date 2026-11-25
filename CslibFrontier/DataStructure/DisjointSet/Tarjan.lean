/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.DisjointSet.UnionFind
public import CslibFrontier.DataStructure.StateTransition.Amortized
public import CslibFrontier.Foundations.Data.Nat.InverseAckermann
import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- `import all` unfolds `UnionFind.impl` and reuses `UnionFind`'s private `Batteries.UnionFind`
-- bridge lemmas (`compressWithSteps_*`, `rank_link`, `unionFind_ext`) without editing it.
import all CslibFrontier.DataStructure.DisjointSet.UnionFind
-- `import all` also unfolds `Batteries.UnionFind.findAux_s` and `parentD_findAux` for
-- `parentD_findAux_eq_findPathGo`.
import all Batteries.Data.UnionFind.Basic

/-!
# Tarjan's inverse-Ackermann amortized bounds for Union–Find

This module establishes Tarjan's (1975) inverse-Ackermann amortized upper bounds for
`Cslib.DataStructure.DisjointSet.UnionFind.impl` (`Batteries.UnionFind` with union by rank and
full path compression) using `Cslib.DataStructure.Amortized` certificates over `Execution.ofStep`.

Following Tarjan (1975) and Kozen (1992), each node `i < uf.size` receives a potential built
from the level `k = ackLevel (uf.rank i + d) (uf.rank (uf.parent i) + d)` and iteration count
`i₀ = ackIter (uf.rank i + d) (uf.rank (uf.parent i) + d)` such that
`ackermann k (uf.rank i + d) ≤ (ackermann k)^[i₀] (uf.rank i + d) ≤ uf.rank (uf.parent i) + d`.
Shifting node ranks by `d := max 1 d ≥ 1` ensures `1 ≤ uf.rank i + d` everywhere, avoiding
separate rank-zero handling during `find`.

A single parameterized potential `potentialCore zeroSingletons q d uf` unifies two regimes:

1. **`zeroSingletons = true, d = 1` (`tarjanAmortized`)**: initial potential at `init n` is `0`,
   giving single-parameter amortized bounds `2 * α(n) + 2` for `Op.same`, `5 * α(n) + 2` for
   `Op.union`, and `1` for `Op.numComponents`, hence `total id traces ≤ m * (5 * α(n) + 2)`.
2. **`zeroSingletons = false, d = m / n + 1` (`tarjanAmortizedAt`)**: initial potential at
   `init n` is `n * (q * (m / n + 1))`, while each `link` has amortized charge at most `q`. When
   `n ≤ m`, `n * (m / n + 1) ≤ 2 * m`, yielding Tarjan's two-parameter bound
   `total id traces ≤ m * (5 * α(m, n) + 2)` (`tarjan_run_two_param`) for every `m, n`, together
   with the linear `7 * m` corollary once `n * Nat.log 2 n ≤ m` (`tarjan_run_linear_of_dense`).

## Cost model and scope

Like `Cslib.DataStructure.DisjointSet.UnionFind`, `total id traces` counts the exact abstract
forest steps recorded by `UnionFind.step` (`findSteps` parent-pointer inspections per `find`,
`1` link step per `Op.union`, and `1` counter read per `Op.numComponents`), excluding the `O(n)`
creation of `init n`. These theorems bound abstract pointer/link steps on `Batteries.UnionFind`
and make no Word-RAM or Turing-machine instruction claim. `Nat.inverseAckermannTwo m n` uses
shift `d = m / n + 1` in `Nat.ackermann`, equivalent up to small constant shifts/factors to
Tarjan's (1975) `4 * ⌈m / n⌉` convention.

## Main definitions

* `tarjanPotential`, `tarjanCharge`: single-parameter Tarjan potential and per-operation charges.
* `tarjanPotentialAt`, `tarjanChargeAt`: rank-shifted potential and per-operation charges for the
  two-parameter analysis.

## Main results

* `tarjanAmortized`, `tarjanUniformAmortized`: `Amortized` certificates for the single-parameter
  `O(α(n))` bound.
* `tarjan_run_correct`: adaptive client correctness and `m * (5 * α(n) + 2)` bound from `init n`.
* `tarjanAmortizedAt`, `tarjanUniformAmortizedAt`: `Amortized` certificates parameterized by `d`.
* `tarjan_run_two_param`: Tarjan's (1975) two-parameter `m * (5 * α(m, n) + 2)` step bound for
  all universe sizes `n` and operation counts `m`.
* `tarjan_run_linear_of_dense`: strict linear step-count bound `total id traces ≤ 7 * m` whenever
  `n * Nat.log 2 n ≤ m`.

## References

* [R. E. Tarjan, *Efficiency of a Good But Not Linear Set Union Algorithm*, JACM 22(2),
  1975][Tarjan1975].
* [D. C. Kozen, *The Design and Analysis of Algorithms*, Lectures 10–11, 1992][Kozen1992].
-/

public section

namespace Cslib.DataStructure.DisjointSet.UnionFind

open Cslib.DataStructure Cslib.DataStructure.DisjointSet

/-- The representation invariant of `UnionFind.impl n` agrees with `UnionFind.Rep`. -/
theorem impl_rep_iff (n : ℕ) (p : Partition n) (s : State n) :
    (impl n).rep p s ↔ Rep p s := by
  unfold impl
  exact Iff.rfl

private theorem rank_compressWithSteps (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (compressWithSteps uf x).1.rank i = uf.rank i := by
  rw [compressWithSteps_fst, find_rank]

/-! ### Find-path traversal and path compression characterization -/

private def findPathGo (uf : Batteries.UnionFind) : ℕ → Fin uf.size → List ℕ
  | 0, x => [x.1]
  | fuel + 1, x =>
    let y := uf.arr[x.1].parent
    if y = x.1 then [x.1]
    else x.1 :: findPathGo uf fuel ⟨y, uf.parent'_lt x.1 x.2⟩

private def findPath (uf : Batteries.UnionFind) (x : Fin uf.size) : List ℕ :=
  findPathGo uf (rankBound uf) x

private theorem findPathGo_length_eq (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      (findPathGo uf fuel x).length = (findGo uf fuel x).2
  | 0, _ => rfl
  | fuel + 1, x => by
    rw [findPathGo, findGo]
    dsimp only
    split
    · rfl
    · simp only [List.length_cons,
        findPathGo_length_eq uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩]

private theorem findPath_length (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (findPath uf x).length = findSteps uf x :=
  findPathGo_length_eq uf (rankBound uf) x

private theorem findPathGo_mem_lt (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u : ℕ},
      u ∈ findPathGo uf fuel x → u < uf.size
  | 0, x, _, hu => by
    simp only [findPathGo, List.mem_singleton] at hu
    exact hu ▸ x.2
  | fuel + 1, x, _, hu => by
    rw [findPathGo] at hu
    split at hu
    · simp only [List.mem_singleton] at hu
      exact hu ▸ x.2
    · simp only [List.mem_cons] at hu
      rcases hu with rfl | htail
      · exact x.2
      · exact findPathGo_mem_lt uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ htail

private theorem findPath_mem_lt (uf : Batteries.UnionFind) (x : Fin uf.size) {u : ℕ}
    (hu : u ∈ findPath uf x) : u < uf.size :=
  findPathGo_mem_lt uf (rankBound uf) x hu

private theorem findPathGo_rank_ge (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u : ℕ},
      u ∈ findPathGo uf fuel x → uf.rank x.1 ≤ uf.rank u
  | 0, x, _, hu => by
    simp only [findPathGo, List.mem_singleton] at hu
    exact hu ▸ Nat.le_refl _
  | fuel + 1, x, _, hu => by
    rw [findPathGo] at hu
    split at hu
    · simp only [List.mem_singleton] at hu
      exact hu ▸ Nat.le_refl _
    · next h =>
      simp only [List.mem_cons] at hu
      rcases hu with rfl | htail
      · exact Nat.le_refl _
      · have hstep : uf.rank x.1 < uf.rank uf.arr[x.1].parent := uf.rank'_lt x.1 x.2 h
        have htail' := findPathGo_rank_ge uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
          htail
        exact (Nat.le_of_lt hstep).trans htail'

private theorem findPathGo_pairwise_rank_lt (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      (findPathGo uf fuel x).Pairwise (fun u v => uf.rank u < uf.rank v)
  | 0, x => by simp [findPathGo]
  | fuel + 1, x => by
    rw [findPathGo]
    split
    · simp
    · next h =>
      rw [List.pairwise_cons]
      refine ⟨fun v hv => ?_, findPathGo_pairwise_rank_lt uf fuel _⟩
      exact lt_of_lt_of_le (uf.rank'_lt x.1 x.2 h)
        (findPathGo_rank_ge uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ hv)

private theorem pairwise_ne_of_pairwise_rank_lt {uf : Batteries.UnionFind} {l : List ℕ}
    (hpw : l.Pairwise (fun u v => uf.rank u < uf.rank v)) : l.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (hpw.imp fun hlt heq => Nat.ne_of_lt hlt (congrArg uf.rank heq))

private theorem findPath_nodup (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (findPath uf x).Nodup :=
  pairwise_ne_of_pairwise_rank_lt (findPathGo_pairwise_rank_lt uf (rankBound uf) x)

private theorem rank_lt_or_gt_of_pairwise {uf : Batteries.UnionFind} {l : List ℕ}
    (hpw : l.Pairwise (fun u v => uf.rank u < uf.rank v))
    {u v : ℕ} (hu : u ∈ l) (hv : v ∈ l) (hne : u ≠ v) :
    uf.rank u < uf.rank v ∨ uf.rank v < uf.rank u := by
  induction l with
  | nil => simp at hu
  | cons a t ih =>
    rw [List.pairwise_cons] at hpw
    rw [List.mem_cons] at hu hv
    rcases hu with rfl | hu <;> rcases hv with rfl | hv
    · exact absurd rfl hne
    · exact .inl (hpw.1 v hv)
    · exact .inr (hpw.1 u hu)
    · exact ih hpw.2 hu hv

private theorem findPath_rank_ne_of_ne (uf : Batteries.UnionFind) (x : Fin uf.size) {u v : ℕ}
    (hu : u ∈ findPath uf x) (hv : v ∈ findPath uf x) (hne : u ≠ v) :
    uf.rank u < uf.rank v ∨ uf.rank v < uf.rank u :=
  rank_lt_or_gt_of_pairwise (findPathGo_pairwise_rank_lt uf (rankBound uf) x) hu hv hne

private theorem findPathGo_rootD (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u : ℕ},
      u ∈ findPathGo uf fuel x → uf.rootD u = uf.rootD x.1
  | 0, x, _, hu => by
    simp only [findPathGo, List.mem_singleton] at hu
    exact hu ▸ rfl
  | fuel + 1, x, _, hu => by
    rw [findPathGo] at hu
    split at hu
    · simp only [List.mem_singleton] at hu
      exact hu ▸ rfl
    · simp only [List.mem_cons] at hu
      rcases hu with rfl | htail
      · rfl
      · have ih := findPathGo_rootD uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ htail
        have hp : uf.arr[x.1].parent = uf.parent x.1 := (Batteries.UnionFind.parentD_eq x.2).symm
        rw [ih]
        dsimp only
        rw [hp, Batteries.UnionFind.rootD_parent]

private theorem findPath_rootD (uf : Batteries.UnionFind) (x : Fin uf.size) {u : ℕ}
    (hu : u ∈ findPath uf x) : uf.rootD u = uf.rootD x.1 :=
  findPathGo_rootD uf (rankBound uf) x hu

private theorem findPathGo_parent_rank_le (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) {u v : ℕ},
      u ∈ findPathGo uf fuel x → v ∈ findPathGo uf fuel x →
      uf.rank u < uf.rank v → uf.rank (uf.parent u) ≤ uf.rank v
  | 0, x, _, _, hu, hv, hlt => by
    simp only [findPathGo, List.mem_singleton] at hu hv
    subst hu hv
    exact absurd hlt (Nat.lt_irrefl _)
  | fuel + 1, x, u, v, hu, hv, hlt => by
    by_cases h : uf.arr[x.1].parent = x.1
    · simp only [findPathGo, ite_eq_left h, List.mem_singleton] at hu hv
      subst hu hv
      exact absurd hlt (Nat.lt_irrefl _)
    · simp only [findPathGo, ite_eq_right h, List.mem_cons] at hu hv
      let y : Fin uf.size := ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
      have hxy : uf.rank x.1 < uf.rank y.1 := uf.rank'_lt x.1 x.2 h
      rcases hu with rfl | hu <;> rcases hv with rfl | hv
      · exact absurd hlt (Nat.lt_irrefl _)
      · have hp : uf.parent x.1 = y.1 := Batteries.UnionFind.parentD_eq x.2
        rw [hp]
        exact findPathGo_rank_ge uf fuel y hv
      · have hge := findPathGo_rank_ge uf fuel y hu
        omega
      · exact findPathGo_parent_rank_le uf fuel y hu hv hlt

private theorem findPath_parent_rank_le (uf : Batteries.UnionFind) (x : Fin uf.size) {u v : ℕ}
    (hu : u ∈ findPath uf x) (hv : v ∈ findPath uf x) (hlt : uf.rank u < uf.rank v) :
    uf.rank (uf.parent u) ≤ uf.rank v :=
  findPathGo_parent_rank_le uf (rankBound uf) x hu hv hlt

private theorem parentD_findAux_eq_findPathGo (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size) (i : ℕ),
      uf.rankMax - uf.rank x.1 ≤ fuel →
      Batteries.UnionFind.parentD (uf.findAux x).s i =
        if i ∈ findPathGo uf fuel x then uf.rootD x.1 else uf.parent i
  | 0, x, _, hle => by
    have hlt := uf.lt_rankMax x.1
    omega
  | fuel + 1, x, i, hle => by
    by_cases h : uf.arr[x.1].parent = x.1
    · rw [Batteries.UnionFind.findAux_s, ite_eq_left h, findPathGo]
      rw [ite_eq_left h]
      split_ifs with him
      · rw [List.mem_singleton] at him
        subst him
        have hxroot : uf.parent x.1 = x.1 := by
          change Batteries.UnionFind.parentD uf.arr x.1 = x.1
          rw [Batteries.UnionFind.parentD_eq x.2]
          exact h
        rw [Batteries.UnionFind.rootD_eq_self.mpr hxroot]
        exact hxroot
      · rfl
    · let y : Fin uf.size := ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
      have hxy : uf.rank x.1 < uf.rank y.1 := uf.rank'_lt x.1 x.2 h
      have hmax := uf.lt_rankMax x.1
      have hfuel : uf.rankMax - uf.rank y.1 ≤ fuel := by omega
      have ih := parentD_findAux_eq_findPathGo uf fuel y i hfuel
      have hyroot : uf.rootD y.1 = uf.rootD x.1 := by
        have hp : y.1 = uf.parent x.1 := (Batteries.UnionFind.parentD_eq x.2).symm
        rw [hp, Batteries.UnionFind.rootD_parent]
      rw [Batteries.UnionFind.parentD_findAux, findPathGo]
      rw [ite_eq_right h]
      by_cases hi : i = x.1
      · subst hi
        rw [ite_eq_left rfl, ite_eq_left List.mem_cons_self]
      · rw [ite_eq_right hi, ih, hyroot]
        simp only [List.mem_cons, hi, false_or]
        rfl

private theorem parent_compressWithSteps (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (compressWithSteps uf x).1.parent i =
      if i ∈ findPath uf x then uf.rootD x.1 else uf.parent i := by
  rw [compressWithSteps_fst, Batteries.UnionFind.parent, Batteries.UnionFind.find]
  exact parentD_findAux_eq_findPathGo uf (rankBound uf) x i
    (by rw [rankBound_eq_rankMax]; exact Nat.sub_le _ _)

private theorem parent_compressWithSteps_eq_self_iff (uf : Batteries.UnionFind) (x : Fin uf.size)
    (i : ℕ) : (compressWithSteps uf x).1.parent i = i ↔ uf.parent i = i := by
  rw [parent_compressWithSteps]
  split_ifs with hi
  · rw [← findPath_rootD uf x hi, Batteries.UnionFind.rootD_eq_self]
  · rfl

/-! ### Level, iteration index, and non-root potential -/

private theorem exists_lt_ackermann {r : ℕ} (hr : 1 ≤ r) (p : ℕ) :
    ∃ k, p < Nat.ackermann k r :=
  ⟨p, Nat.lt_of_le_of_lt (Nat.le_add_left p r) (Nat.add_lt_ackermann p hr)⟩

private noncomputable def ackLevel (r p : ℕ) : ℕ :=
  if h : 1 ≤ r ∧ r < p then Nat.find (exists_lt_ackermann h.1 p) - 1 else 0

private theorem find_lt_ackermann_pos {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    1 ≤ Nat.find (exists_lt_ackermann hr p) := by
  by_contra h
  have h0 : Nat.find (exists_lt_ackermann hr p) = 0 := by omega
  have hspec := Nat.find_spec (exists_lt_ackermann hr p)
  rw [h0, Nat.ackermann_zero] at hspec
  omega

private theorem ackermann_ackLevel_le {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    Nat.ackermann (ackLevel r p) r ≤ p := by
  unfold ackLevel
  rw [dite_eq_left ⟨hr, hrp⟩]
  have hpos := find_lt_ackermann_pos hr hrp
  have hlt : Nat.find (exists_lt_ackermann hr p) - 1 < Nat.find (exists_lt_ackermann hr p) := by
    omega
  exact Nat.not_lt.mp (Nat.find_min (exists_lt_ackermann hr p) hlt)

private theorem lt_ackermann_ackLevel_succ {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    p < Nat.ackermann (ackLevel r p + 1) r := by
  unfold ackLevel
  rw [dite_eq_left ⟨hr, hrp⟩]
  have hpos := find_lt_ackermann_pos hr hrp
  have hspec := Nat.find_spec (exists_lt_ackermann hr p)
  rwa [show Nat.find (exists_lt_ackermann hr p) - 1 + 1 =
    Nat.find (exists_lt_ackermann hr p) by omega]

private theorem le_ackLevel_of_ackermann_le {r p k : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hle : Nat.ackermann k r ≤ p) : k ≤ ackLevel r p := by
  by_contra h
  have hsucc : ackLevel r p + 1 ≤ k := Nat.lt_of_not_ge h
  have hlt := lt_ackermann_ackLevel_succ hr hrp
  have hmono : Nat.ackermann (ackLevel r p + 1) r ≤ Nat.ackermann k r :=
    Nat.ackermann_monotone_left r hsucc
  omega

private theorem ackLevel_lt_of_lt_ackermann {r p q : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hlt : p < Nat.ackermann q r) : ackLevel r p < q := by
  unfold ackLevel
  rw [dite_eq_left ⟨hr, hrp⟩]
  have hpos := find_lt_ackermann_pos hr hrp
  have hmin : Nat.find (exists_lt_ackermann hr p) ≤ q := Nat.find_min' _ hlt
  omega

private theorem ackLevel_mono {r p₁ p₂ : ℕ} (hr : 1 ≤ r) (hrp₁ : r < p₁) (hle : p₁ ≤ p₂) :
    ackLevel r p₁ ≤ ackLevel r p₂ :=
  le_ackLevel_of_ackermann_le hr (lt_of_lt_of_le hrp₁ hle)
    ((ackermann_ackLevel_le hr hrp₁).trans hle)

private theorem exists_lt_iterate_ackermann {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    ∃ i, p < (Nat.ackermann (ackLevel r p))^[i] r :=
  ⟨r + 1, lt_ackermann_ackLevel_succ hr hrp⟩

private noncomputable def ackIter (r p : ℕ) : ℕ :=
  if h : 1 ≤ r ∧ r < p then Nat.find (exists_lt_iterate_ackermann h.1 h.2) - 1 else 0

private theorem two_le_find_iterate {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    2 ≤ Nat.find (exists_lt_iterate_ackermann hr hrp) := by
  by_contra h
  have hle : Nat.find (exists_lt_iterate_ackermann hr hrp) ≤ 1 := by omega
  have hspec := Nat.find_spec (exists_lt_iterate_ackermann hr hrp)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h0 | h1
  · rw [h0, Function.iterate_zero_apply] at hspec
    omega
  · rw [h1, Function.iterate_one] at hspec
    have hack := ackermann_ackLevel_le hr hrp
    omega

private theorem one_le_ackIter {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) : 1 ≤ ackIter r p := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  have h2 := two_le_find_iterate hr hrp
  omega

private theorem ackIter_le {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) : ackIter r p ≤ r := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  have hmin : Nat.find (exists_lt_iterate_ackermann hr hrp) ≤ r + 1 :=
    Nat.find_min' _ (lt_ackermann_ackLevel_succ hr hrp)
  omega

private theorem iterate_ackermann_ackIter_le {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    (Nat.ackermann (ackLevel r p))^[ackIter r p] r ≤ p := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  have h2 := two_le_find_iterate hr hrp
  have hlt : Nat.find (exists_lt_iterate_ackermann hr hrp) - 1 <
      Nat.find (exists_lt_iterate_ackermann hr hrp) := by omega
  exact Nat.not_lt.mp (Nat.find_min (exists_lt_iterate_ackermann hr hrp) hlt)

private theorem lt_iterate_ackermann_ackIter_succ {r p : ℕ} (hr : 1 ≤ r) (hrp : r < p) :
    p < (Nat.ackermann (ackLevel r p))^[ackIter r p + 1] r := by
  unfold ackIter
  rw [dite_eq_left ⟨hr, hrp⟩]
  have h2 := two_le_find_iterate hr hrp
  have hspec := Nat.find_spec (exists_lt_iterate_ackermann hr hrp)
  rwa [show Nat.find (exists_lt_iterate_ackermann hr hrp) - 1 + 1 =
    Nat.find (exists_lt_iterate_ackermann hr hrp) by omega]

private theorem iterate_mono_steps {f : ℕ → ℕ} (hf : ∀ x, x ≤ f x) (x : ℕ) :
    Monotone (fun t => f^[t] x) :=
  monotone_nat_of_le_succ fun t => by
    rw [Function.iterate_succ_apply']
    exact hf (f^[t] x)

private theorem le_ackIter_of_iterate_le {r p i : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hle : (Nat.ackermann (ackLevel r p))^[i] r ≤ p) : i ≤ ackIter r p := by
  by_contra h
  have hsucc : ackIter r p + 1 ≤ i := Nat.lt_of_not_ge h
  have hlt := lt_iterate_ackermann_ackIter_succ hr hrp
  have hmono : (Nat.ackermann (ackLevel r p))^[ackIter r p + 1] r ≤
      (Nat.ackermann (ackLevel r p))^[i] r :=
    iterate_mono_steps (f := Nat.ackermann (ackLevel r p))
      (fun x => Nat.le_of_lt (Nat.lt_ackermann _ x)) r hsucc
  omega

private noncomputable def nonRootPhi (q r p : ℕ) : ℕ :=
  (q - ackLevel r p) * r - ackIter r p

private theorem ackIter_le_mul {q r p : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hpq : p < Nat.ackermann q r) : ackIter r p ≤ (q - ackLevel r p) * r := by
  have hk : ackLevel r p < q := ackLevel_lt_of_lt_ackermann hr hrp hpq
  have hi : ackIter r p ≤ r := ackIter_le hr hrp
  have hmul : r ≤ (q - ackLevel r p) * r :=
    Nat.le_mul_of_pos_left r (Nat.sub_pos_of_lt hk)
  exact hi.trans hmul

private theorem nonRootPhi_le_mul_sub_one {q r p : ℕ} (hr : 1 ≤ r) (hrp : r < p)
    (hpq : p < Nat.ackermann q r) : nonRootPhi q r p + 1 ≤ q * r := by
  have h1 : 1 ≤ ackIter r p := one_le_ackIter hr hrp
  have himul : ackIter r p ≤ (q - ackLevel r p) * r := ackIter_le_mul hr hrp hpq
  have hqmul : (q - ackLevel r p) * r ≤ q * r := Nat.mul_le_mul_right r (Nat.sub_le q _)
  unfold nonRootPhi
  omega

private theorem nonRootPhi_lt_of_level_lt {q r p p' : ℕ} (hr : 1 ≤ r) (hrp : r < p) (hp : p ≤ p')
    (hp'q : p' < Nat.ackermann q r) (hklt : ackLevel r p < ackLevel r p') :
    nonRootPhi q r p' + 1 ≤ nonRootPhi q r p := by
  have hrp' : r < p' := lt_of_lt_of_le hrp hp
  have hk' : ackLevel r p' < q := ackLevel_lt_of_lt_ackermann hr hrp' hp'q
  have hi : ackIter r p ≤ r := ackIter_le hr hrp
  have hi'1 : 1 ≤ ackIter r p' := one_le_ackIter hr hrp'
  have hi'mul : ackIter r p' ≤ (q - ackLevel r p') * r := ackIter_le_mul hr hrp' hp'q
  have hq : (q - ackLevel r p') + 1 ≤ q - ackLevel r p := by omega
  have hmul : (q - ackLevel r p') * r + r ≤ (q - ackLevel r p) * r := by
    calc
      (q - ackLevel r p') * r + r = ((q - ackLevel r p') + 1) * r := (Nat.succ_mul _ _).symm
      _ ≤ (q - ackLevel r p) * r := Nat.mul_le_mul_right r hq
  unfold nonRootPhi
  omega

private theorem nonRootPhi_le_of_le {q r p p' : ℕ} (hr : 1 ≤ r) (hrp : r < p) (hp : p ≤ p')
    (hp'q : p' < Nat.ackermann q r) :
    nonRootPhi q r p' ≤ nonRootPhi q r p := by
  have hmono : ackLevel r p ≤ ackLevel r p' := ackLevel_mono hr hrp hp
  rcases Nat.eq_or_lt_of_le hmono with heq | hlt
  · have hrp' : r < p' := lt_of_lt_of_le hrp hp
    have hiter : ackIter r p ≤ ackIter r p' := by
      refine le_ackIter_of_iterate_le hr hrp' ?_
      rw [← heq]
      exact (iterate_ackermann_ackIter_le hr hrp).trans hp
    unfold nonRootPhi
    rw [heq]
    exact Nat.sub_le_sub_left hiter _
  · exact Nat.le_trans (Nat.le_succ _) (nonRootPhi_lt_of_level_lt hr hrp hp hp'q hlt)

private theorem nonRootPhi_lt_of_step {q r p p' : ℕ} (hr : 1 ≤ r) (hrp : r < p) (hp : p ≤ p')
    (hp'q : p' < Nat.ackermann q r)
    (hstep : (Nat.ackermann (ackLevel r p))^[ackIter r p + 1] r ≤ p') :
    nonRootPhi q r p' + 1 ≤ nonRootPhi q r p := by
  have hrp' : r < p' := lt_of_lt_of_le hrp hp
  have hmono : ackLevel r p ≤ ackLevel r p' := ackLevel_mono hr hrp hp
  rcases Nat.eq_or_lt_of_le hmono with heq | hlt
  · have hir : ackIter r p < r := by
      rcases Nat.eq_or_lt_of_le (ackIter_le hr hrp) with hir_eq | hir_lt
      · exfalso
        rw [hir_eq] at hstep
        have hack : ackLevel r p + 1 ≤ ackLevel r p' :=
          le_ackLevel_of_ackermann_le hr hrp' hstep
        omega
      · exact hir_lt
    have hiter : ackIter r p + 1 ≤ ackIter r p' := by
      refine le_ackIter_of_iterate_le hr hrp' ?_
      rwa [← heq]
    have himul' : ackIter r p' ≤ (q - ackLevel r p') * r := ackIter_le_mul hr hrp' hp'q
    unfold nonRootPhi
    rw [← heq] at himul' ⊢
    omega
  · exact nonRootPhi_lt_of_level_lt hr hrp hp hp'q hlt

/-! ### Unified node potential and find/link step inequalities -/

private noncomputable def nodePotential (zeroSingletons : Bool) (q d : ℕ)
    (uf : Batteries.UnionFind) (i : ℕ) : ℕ :=
  if uf.parent i = i then
    if zeroSingletons && uf.rank i = 0 then 0 else q * (uf.rank i + d)
  else
    nonRootPhi q (uf.rank i + d) (uf.rank (uf.parent i) + d)

private noncomputable def potentialCore (zeroSingletons : Bool) (q d : ℕ)
    (uf : Batteries.UnionFind) : ℕ :=
  ∑ i ∈ Finset.range uf.size, nodePotential zeroSingletons q d uf i

private theorem sum_const_nat (s : Finset ℕ) (c : ℕ) : ∑ _ ∈ s, c = s.card * c := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha, ih, Nat.succ_mul, Nat.add_comm]

private theorem potentialCore_true_ofSize (q d n : ℕ) :
    potentialCore true q d (ofSize n) = 0 := by
  unfold potentialCore nodePotential
  simp

private theorem potentialCore_false_ofSize (q d n : ℕ) :
    potentialCore false q d (ofSize n) = n * (q * d) := by
  unfold potentialCore nodePotential
  simp only [size_ofSize, parent_ofSize, ↓reduceIte, Bool.false_and, Bool.false_eq_true,
    rank_ofSize, Nat.zero_add]
  rw [sum_const_nat, Finset.card_range]

private theorem findSteps_add_potentialCore_le {uf : Batteries.UnionFind}
    (hvalid : ValidRank uf) {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 uf.size + d < Nat.ackermann q d)
    (zs : Bool) (x : Fin uf.size) :
    findSteps uf x + potentialCore zs q d (compressWithSteps uf x).1 ≤
      (q + 1) + potentialCore zs q d uf := by
  set uf' := (compressWithSteps uf x).1
  let S : Finset ℕ := (findPath uf x).toFinset
  have hS_sub : S ⊆ Finset.range uf.size := fun u hu =>
    Finset.mem_range.mpr (findPath_mem_lt uf x (List.mem_toFinset.mp hu))
  have hS_card : S.card = findSteps uf x := by
    rw [List.toFinset_card_of_nodup (findPath_nodup uf x), findPath_length]
  let lvl := fun u => ackLevel (uf.rank u + d) (uf.rank (uf.parent u) + d)
  let S_drop : Finset ℕ := S.filter fun u =>
    uf.parent u ≠ u ∧ ∃ v ∈ S, uf.rank u < uf.rank v ∧ uf.parent v ≠ v ∧ lvl u = lvl v
  let S_keep : Finset ℕ := S \ S_drop
  have hdrop_sub : S_drop ⊆ Finset.range uf.size :=
    (Finset.filter_subset _ _).trans hS_sub
  have hpath_bounds : ∀ u, uf.parent u ≠ u →
      1 ≤ uf.rank u + d ∧
      uf.rank u + d < uf.rank (uf.parent u) + d ∧
      uf.rank (uf.parent u) + d ≤ uf.rank (uf.rootD u) + d ∧
      uf.rank (uf.rootD u) + d < Nat.ackermann q (uf.rank u + d) := by
    intro u hroot
    refine ⟨Nat.le_trans hd (Nat.le_add_left d _),
      Nat.add_lt_add_right (uf.rank_lt hroot) d, ?_, ?_⟩
    · have := Batteries.UnionFind.le_rank_root (self := uf) (x := uf.parent u)
      rw [Batteries.UnionFind.rootD_parent] at this
      omega
    · have hlog := hvalid.rank_le_log (uf.rootD u)
      have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank u))
      omega
  have hpot_le : ∀ u, u < uf.size →
      nodePotential zs q d uf' u ≤ nodePotential zs q d uf u := by
    intro u hu
    by_cases hroot : uf.parent u = u
    · have hroot' : uf'.parent u = u := (parent_compressWithSteps_eq_self_iff uf x u).mpr hroot
      simp only [nodePotential, uf', hroot, hroot', ↓reduceIte, rank_compressWithSteps]
      exact Nat.le_refl _
    · have hroot' : uf'.parent u ≠ u := by
        rwa [ne_eq, parent_compressWithSteps_eq_self_iff]
      simp only [nodePotential, uf', hroot, hroot', ↓reduceIte, rank_compressWithSteps]
      by_cases huS : u ∈ findPath uf x
      · have hp' : uf'.parent u = uf.rootD u := by
          rw [parent_compressWithSteps, ite_eq_left huS, ← findPath_rootD uf x huS]
        rw [hp']
        obtain ⟨hr, hrp, hpp', hp'q⟩ := hpath_bounds u hroot
        exact nonRootPhi_le_of_le hr hrp hpp' hp'q
      · have hp' : uf'.parent u = uf.parent u := by
          rw [parent_compressWithSteps, ite_eq_right huS]
        rw [hp']
  have hpot_drop : ∀ u ∈ S_drop,
      nodePotential zs q d uf' u + 1 ≤ nodePotential zs q d uf u := by
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu with ⟨huS, hroot, v, hvS, hrank_uv, hvroot, hlvl⟩
    have huPath : u ∈ findPath uf x := List.mem_toFinset.mp huS
    have hvPath : v ∈ findPath uf x := List.mem_toFinset.mp hvS
    have hroot' : uf'.parent u ≠ u := by
      rwa [ne_eq, parent_compressWithSteps_eq_self_iff]
    have hp' : uf'.parent u = uf.rootD u := by
      rw [parent_compressWithSteps, ite_eq_left huPath, ← findPath_rootD uf x huPath]
    simp only [nodePotential, uf', hroot, hroot', ↓reduceIte, rank_compressWithSteps]
    rw [hp']
    obtain ⟨hr, hrp, hpp', hp'q⟩ := hpath_bounds u hroot
    refine nonRootPhi_lt_of_step hr hrp hpp' hp'q ?_
    have hpu_rv : uf.rank (uf.parent u) + d ≤ uf.rank v + d :=
      Nat.add_le_add_right (findPath_parent_rank_le uf x huPath hvPath hrank_uv) d
    have hrv : 1 ≤ uf.rank v + d := Nat.le_trans hd (Nat.le_add_left d _)
    have hrvp : uf.rank v + d < uf.rank (uf.parent v) + d :=
      Nat.add_lt_add_right (uf.rank_lt hvroot) d
    have hack_v : Nat.ackermann (lvl u) (uf.rank v + d) ≤ uf.rank (uf.parent v) + d := by
      rw [hlvl]
      exact ackermann_ackLevel_le hrv hrvp
    have hpv_root : uf.rank (uf.parent v) + d ≤ uf.rank (uf.rootD u) + d := by
      have hle := Batteries.UnionFind.le_rank_root (self := uf) (x := uf.parent v)
      rw [Batteries.UnionFind.rootD_parent, findPath_rootD uf x hvPath,
        ← findPath_rootD uf x huPath] at hle
      omega
    have hiter_le :
        (Nat.ackermann (lvl u))^[ackIter (uf.rank u + d) (uf.rank (uf.parent u) + d)]
          (uf.rank u + d) ≤ uf.rank v + d :=
      (iterate_ackermann_ackIter_le hr hrp).trans hpu_rv
    have hstep1 :
        (Nat.ackermann (lvl u))^[ackIter (uf.rank u + d) (uf.rank (uf.parent u) + d) + 1]
          (uf.rank u + d) ≤ Nat.ackermann (lvl u) (uf.rank v + d) := by
      rw [Function.iterate_succ_apply']
      exact Nat.ackermann_monotone_right (lvl u) hiter_le
    exact hstep1.trans (hack_v.trans hpv_root)
  have hsum_drop : potentialCore zs q d uf' + S_drop.card ≤ potentialCore zs q d uf := by
    have hsum_le :
        ∑ u ∈ Finset.range uf.size,
            (nodePotential zs q d uf' u + if u ∈ S_drop then 1 else 0) ≤
          ∑ u ∈ Finset.range uf.size, nodePotential zs q d uf u := by
      refine Finset.sum_le_sum fun u hu => ?_
      split_ifs with hud
      · exact hpot_drop u hud
      · rw [Nat.add_zero]
        exact hpot_le u (Finset.mem_range.mp hu)
    have hsz : uf'.size = uf.size := compressWithSteps_size uf x
    have hfilter_eq : (Finset.range uf.size).filter (· ∈ S_drop) = S_drop := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mp (hdrop_sub h), h⟩⟩
    have hboole :
        ∑ u ∈ Finset.range uf.size, (if u ∈ S_drop then (1 : ℕ) else 0) = S_drop.card := by
      rw [← Finset.sum_filter (fun u => u ∈ S_drop) (fun _ => (1 : ℕ)), hfilter_eq,
        sum_const_nat, Nat.mul_one]
    unfold potentialCore
    rw [hsz]
    rw [Finset.sum_add_distrib, hboole] at hsum_le
    exact hsum_le
  have hkeep_card : S_keep.card ≤ q + 1 := by
    let S_keep_roots := S_keep.filter (fun u => uf.parent u = u)
    let S_keep_nonroots := S_keep.filter (fun u => uf.parent u ≠ u)
    have hsplit := Finset.card_filter_add_card_filter_not (s := S_keep)
      (p := fun u => uf.parent u = u)
    have hroots : S_keep_roots.card ≤ 1 := by
      refine Finset.card_le_one.mpr fun a ha b hb => ?_
      rw [Finset.mem_filter, Finset.mem_sdiff] at ha hb
      have ha_root := (Batteries.UnionFind.rootD_eq_self.mpr ha.2).symm.trans
        (findPath_rootD uf x (List.mem_toFinset.mp ha.1.1))
      have hb_root := (Batteries.UnionFind.rootD_eq_self.mpr hb.2).symm.trans
        (findPath_rootD uf x (List.mem_toFinset.mp hb.1.1))
      exact ha_root.trans hb_root.symm
    have hnonroots : S_keep_nonroots.card ≤ q := by
      have hmap : Set.MapsTo lvl (S_keep_nonroots : Set ℕ) (Finset.range q : Set ℕ) := by
        intro u hu
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff] at hu
        have hroot := hu.2
        have hr : 1 ≤ uf.rank u + d := Nat.le_trans hd (Nat.le_add_left d _)
        have hrp : uf.rank u + d < uf.rank (uf.parent u) + d :=
          Nat.add_lt_add_right (uf.rank_lt hroot) d
        have hpq : uf.rank (uf.parent u) + d < Nat.ackermann q (uf.rank u + d) := by
          have hlog := hvalid.rank_le_log (uf.parent u)
          have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank u))
          omega
        exact Finset.mem_coe.mpr (Finset.mem_range.mpr
          (ackLevel_lt_of_lt_ackermann hr hrp hpq))
      have hinj : Set.InjOn lvl (S_keep_nonroots : Set ℕ) := by
        intro u₁ hu₁ u₂ hu₂ heq
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sdiff] at hu₁ hu₂
        by_contra hne
        have hu₁Path : u₁ ∈ findPath uf x := List.mem_toFinset.mp hu₁.1.1
        have hu₂Path : u₂ ∈ findPath uf x := List.mem_toFinset.mp hu₂.1.1
        rcases findPath_rank_ne_of_ne uf x hu₁Path hu₂Path hne with hlt | hlt
        · exact hu₁.1.2 (Finset.mem_filter.mpr
            ⟨hu₁.1.1, hu₁.2, u₂, hu₂.1.1, hlt, hu₂.2, heq⟩)
        · exact hu₂.1.2 (Finset.mem_filter.mpr
            ⟨hu₂.1.1, hu₂.2, u₁, hu₁.1.1, hlt, hu₁.2, heq.symm⟩)
      simpa only [Finset.card_range] using Finset.card_le_card_of_injOn lvl hmap hinj
    change S_keep_roots.card + S_keep_nonroots.card = S_keep.card at hsplit
    omega
  have hS_split : S_keep.card + S_drop.card = S.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  rw [← hS_card]
  omega

private theorem link_pot_aux {uf uf' : Batteries.UnionFind}
    (hvalid' : ValidRank uf')
    {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 uf.size + d < Nat.ackermann q d)
    {winner child : Fin uf.size}
    (hwinner : uf.parent winner.1 = winner.1)
    (hne : winner.1 ≠ child.1) (hsize : uf'.size = uf.size)
    (hparent : ∀ i, uf'.parent i = if child.1 = i then winner.1 else uf.parent i)
    (hrank : ∀ i, uf'.rank i =
      if uf.rank child.1 = uf.rank winner.1 ∧ winner.1 = i then uf.rank winner.1 + 1
      else uf.rank i)
    (hcrank : uf'.rank child.1 < uf'.rank winner.1)
    (zs : Bool) :
    1 + potentialCore zs q d uf' +
      (nodePotential zs q d uf winner.1 + nodePotential zs q d uf child.1) ≤
      q + (q * (uf.rank winner.1 + d) + q * (uf.rank child.1 + d)) +
        potentialCore zs q d uf := by
  let rest : Finset ℕ := ((Finset.range uf.size).erase winner.1).erase child.1
  have hmem_w : winner.1 ∈ Finset.range uf.size := Finset.mem_range.mpr winner.2
  have hmem_c : child.1 ∈ (Finset.range uf.size).erase winner.1 :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_range.mpr child.2⟩
  have hsplit_uf :
      nodePotential zs q d uf winner.1 +
        (nodePotential zs q d uf child.1 + ∑ i ∈ rest, nodePotential zs q d uf i) =
      potentialCore zs q d uf := by
    unfold potentialCore
    rw [Finset.add_sum_erase _ _ hmem_c, Finset.add_sum_erase _ _ hmem_w]
  have hsplit_uf' :
      nodePotential zs q d uf' winner.1 +
        (nodePotential zs q d uf' child.1 + ∑ i ∈ rest, nodePotential zs q d uf' i) =
      potentialCore zs q d uf' := by
    unfold potentialCore
    rw [hsize]
    rw [Finset.add_sum_erase _ _ hmem_c, Finset.add_sum_erase _ _ hmem_w]
  have hrest : ∀ i ∈ rest, nodePotential zs q d uf' i ≤ nodePotential zs q d uf i := by
    intro i hi
    have hi_ne_c : child.1 ≠ i := (Finset.mem_erase.mp hi).1.symm
    have hi_ne_w : winner.1 ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1.symm
    have hp_i : uf'.parent i = uf.parent i := by rw [hparent i, ite_eq_right hi_ne_c]
    have hr_i : uf'.rank i = uf.rank i := by rw [hrank i]; simp [hi_ne_w]
    by_cases hroot : uf.parent i = i
    · have hroot' : uf'.parent i = i := hp_i.trans hroot
      simp only [nodePotential, hroot, hroot', ↓reduceIte, hr_i]
      exact Nat.le_refl _
    · have hroot' : uf'.parent i ≠ i := by rwa [hp_i]
      simp only [nodePotential, hroot, hroot', ↓reduceIte, hr_i]
      by_cases hpw : uf.parent i = winner.1
      · have hle_p : uf.rank (uf.parent i) ≤ uf'.rank (uf'.parent i) := by
          rw [hp_i, hpw, hrank winner.1]
          split_ifs <;> omega
        have hr_pos : 1 ≤ uf.rank i + d := Nat.le_trans hd (Nat.le_add_left d _)
        have hrp : uf.rank i + d < uf.rank (uf.parent i) + d :=
          Nat.add_lt_add_right (uf.rank_lt hroot) d
        have hpp' : uf.rank (uf.parent i) + d ≤ uf'.rank (uf'.parent i) + d := by omega
        have hp'q : uf'.rank (uf'.parent i) + d < Nat.ackermann q (uf.rank i + d) := by
          have hlog := hvalid'.rank_le_log (uf'.parent i)
          rw [hsize] at hlog
          have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank i))
          omega
        exact nonRootPhi_le_of_le hr_pos hrp hpp' hp'q
      · have hp_ne_w : winner.1 ≠ uf.parent i := Ne.symm hpw
        have hrp_eq : uf'.rank (uf'.parent i) = uf.rank (uf.parent i) := by
          rw [hp_i, hrank (uf.parent i)]
          simp [hp_ne_w]
        rw [hrp_eq]
  have hsum_rest : ∑ i ∈ rest, nodePotential zs q d uf' i ≤
      ∑ i ∈ rest, nodePotential zs q d uf i := Finset.sum_le_sum hrest
  have hchild_bound : 1 + nodePotential zs q d uf' child.1 ≤ q * (uf.rank child.1 + d) := by
    have hpc : uf'.parent child.1 = winner.1 := by rw [hparent child.1, ite_eq_left rfl]
    have hpc_ne : uf'.parent child.1 ≠ child.1 := by rw [hpc]; exact hne
    have hrc : uf'.rank child.1 = uf.rank child.1 := by rw [hrank child.1]; simp [hne]
    simp only [nodePotential, hpc_ne, ↓reduceIte, hrc]
    rw [hpc]
    have hr_pos : 1 ≤ uf.rank child.1 + d := Nat.le_trans hd (Nat.le_add_left d _)
    have hrp : uf.rank child.1 + d < uf'.rank winner.1 + d := by rw [← hrc]; omega
    have hpq : uf'.rank winner.1 + d < Nat.ackermann q (uf.rank child.1 + d) := by
      have hlog := hvalid'.rank_le_log winner.1
      rw [hsize] at hlog
      have hack := Nat.ackermann_monotone_right q (Nat.le_add_left d (uf.rank child.1))
      omega
    have hmul := nonRootPhi_le_mul_sub_one hr_pos hrp hpq
    omega
  have hwinner_bound : nodePotential zs q d uf' winner.1 ≤ q * (uf.rank winner.1 + d) + q := by
    have hpw' : uf'.parent winner.1 = winner.1 := by
      rw [hparent winner.1, ite_eq_right hne.symm, hwinner]
    have hrw' : uf'.rank winner.1 ≤ uf.rank winner.1 + 1 := by
      rw [hrank winner.1]
      split_ifs <;> omega
    simp only [nodePotential, hpw', ↓reduceIte]
    split_ifs
    · exact Nat.zero_le _
    · calc
        q * (uf'.rank winner.1 + d) ≤ q * ((uf.rank winner.1 + 1) + d) :=
          Nat.mul_le_mul_left q (by omega)
        _ = q * ((uf.rank winner.1 + d) + 1) := by rw [Nat.add_right_comm]
        _ = q * (uf.rank winner.1 + d) + q := by rw [Nat.mul_add, Nat.mul_one]
  omega

private theorem link_pot_core {uf : Batteries.UnionFind}
    (hvalid : ValidRank uf) {q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hbound : Nat.log 2 uf.size + d < Nat.ackermann q d)
    {x y : Fin uf.size} (hx : uf.parent x.1 = x.1) (hy : uf.parent y.1 = y.1) (zs : Bool) :
    1 + potentialCore zs q d (uf.link x y hy) ≤
      (if zs then 2 * d * q + q else q) + potentialCore zs q d uf := by
  by_cases hxy : x.1 = y.1
  · have heq : uf.link x y hy = uf := unionFind_ext (by
      simp [Batteries.UnionFind.arr_link, Batteries.UnionFind.linkAux, hxy])
    rw [heq]
    split_ifs <;> omega
  · have hvalid' : ValidRank (uf.link x y hy) := hvalid.link hx hy
    have hsize : (uf.link x y hy).size = uf.size := Batteries.UnionFind.linkAux_size
    have haux_res : 1 + potentialCore zs q d (uf.link x y hy) +
        (if uf.rank y.1 < uf.rank x.1 then
          nodePotential zs q d uf x.1 + nodePotential zs q d uf y.1
        else
          nodePotential zs q d uf y.1 + nodePotential zs q d uf x.1) ≤
        q + (if uf.rank y.1 < uf.rank x.1 then
          q * (uf.rank x.1 + d) + q * (uf.rank y.1 + d)
        else
          q * (uf.rank y.1 + d) + q * (uf.rank x.1 + d)) + potentialCore zs q d uf := by
      by_cases hlt : uf.rank y.1 < uf.rank x.1
      · simp only [hlt, ↓reduceIte]
        have hcr : (uf.link x y hy).rank y.1 < (uf.link x y hy).rank x.1 := by
          rw [rank_link, rank_link]
          simp [Nat.ne_of_gt hlt, hlt]
        exact link_pot_aux hvalid' hd hbound hx hxy hsize
          (fun i => by rw [Batteries.UnionFind.parent_link hy]; simp [hxy, hlt])
          (fun i => by rw [rank_link]; simp [Nat.ne_of_lt hlt, Nat.ne_of_gt hlt])
          hcr zs
      · simp only [hlt, ↓reduceIte]
        have hcr : (uf.link x y hy).rank x.1 < (uf.link x y hy).rank y.1 := by
          rw [rank_link, rank_link]
          have hle : uf.rank x.1 ≤ uf.rank y.1 := Nat.not_lt.mp hlt
          rcases Nat.eq_or_lt_of_le hle with heq | hlt_xy
          · simp [hxy, Ne.symm hxy, heq]
          · simp [hxy, Nat.ne_of_lt hlt_xy, hlt_xy]
        exact link_pot_aux hvalid' hd hbound hy (Ne.symm hxy) hsize
          (fun i => by rw [Batteries.UnionFind.parent_link hy]; simp [hxy, hlt])
          (fun i => by rw [rank_link]; simp [hxy])
          hcr zs
    cases zs
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hx_pot : nodePotential false q d uf x.1 = q * (uf.rank x.1 + d) := by
        simp [nodePotential, hx]
      have hy_pot : nodePotential false q d uf y.1 = q * (uf.rank y.1 + d) := by
        simp [nodePotential, hy]
      split_ifs at haux_res <;> rw [hx_pot, hy_pot] at haux_res <;> omega
    · simp only [↓reduceIte]
      have hnode_le : ∀ u : Fin uf.size, uf.parent u.1 = u.1 →
          q * (uf.rank u.1 + d) ≤ nodePotential true q d uf u.1 + q * d := by
        intro u hu
        simp only [nodePotential, hu, ↓reduceIte, Bool.true_and]
        split_ifs with hr0
        · rw [of_decide_eq_true hr0, Nat.zero_add]
          exact Nat.le_add_left _ _
        · exact Nat.le_add_right _ _
      have hx_le := hnode_le x hx
      have hy_le := hnode_le y hy
      have hmul_comm : 2 * d * q = q * d + q * d := by
        rw [Nat.mul_assoc, Nat.mul_comm d q, Nat.two_mul]
      split_ifs at haux_res <;> omega

private theorem two_finds_union_step_core {n : ℕ} {s : State n} (x y : Fin n)
    (hrank : ValidRank s.uf) {q d : ℕ} (hq : 1 ≤ q) (hd : 1 ≤ d)
    (hbound : Nat.log 2 n + d < Nat.ackermann q d) (zs : Bool) :
    (step s (.union x y)).trace + potentialCore zs q d (step s (.union x y)).state.uf ≤
      (2 * (q + 1) + (if zs then 2 * d * q + q else q)) + potentialCore zs q d s.uf := by
  unfold step
  dsimp only
  let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
  set c₁ := compressWithSteps s.uf x'
  have hsz₁ : c₁.1.size = n := (compressWithSteps_size s.uf x').trans s.size_eq
  let y' : Fin c₁.1.size := ⟨y.1, by rw [hsz₁]; exact y.2⟩
  set c₂ := compressWithSteps c₁.1 y'
  have hsz₂ : c₂.1.size = n := (compressWithSteps_size c₁.1 y').trans hsz₁
  let rx : Fin c₂.1.size := ⟨c₁.2.1.1, by
    rw [compressWithSteps_size c₁.1 y', compressWithSteps_size s.uf x']
    exact c₁.2.1.2⟩
  let ry : Fin c₂.1.size := ⟨c₂.2.1.1, by
    rw [compressWithSteps_size c₁.1 y']
    exact c₂.2.1.2⟩
  have hxroot : c₂.1.parent rx.1 = rx.1 := by
    have hr1 : c₁.2.1.1 = s.uf.rootD x.1 := compressWithSteps_root s.uf x'
    have hroot1 : c₁.1.rootD c₁.2.1.1 = c₁.2.1.1 := by
      rw [rootD_compressWithSteps, hr1, Batteries.UnionFind.rootD_rootD]
    have hroot2 : c₂.1.rootD c₁.2.1.1 = c₁.2.1.1 := by
      change (compressWithSteps c₁.1 y').1.rootD c₁.2.1.1 = c₁.2.1.1
      rw [rootD_compressWithSteps, hroot1]
    exact Batteries.UnionFind.rootD_eq_self.mp hroot2
  have hyroot : c₂.1.parent ry.1 = ry.1 := by
    have hr2 : c₂.2.1.1 = c₁.1.rootD y.1 := compressWithSteps_root c₁.1 y'
    have hroot2 : c₂.1.rootD c₂.2.1.1 = c₂.2.1.1 := by
      change (compressWithSteps c₁.1 y').1.rootD c₂.2.1.1 = c₂.2.1.1
      rw [rootD_compressWithSteps, hr2, Batteries.UnionFind.rootD_rootD]
    exact Batteries.UnionFind.rootD_eq_self.mp hroot2
  have hvalid₁ : ValidRank c₁.1 := hrank.compressWithSteps x'
  have hvalid₂ : ValidRank c₂.1 := hvalid₁.compressWithSteps y'
  have hbound₀ : Nat.log 2 s.uf.size + d < Nat.ackermann q d := by rwa [s.size_eq]
  have hbound₁ : Nat.log 2 c₁.1.size + d < Nat.ackermann q d := by rwa [hsz₁]
  have hbound₂ : Nat.log 2 c₂.1.size + d < Nat.ackermann q d := by rwa [hsz₂]
  have hf1 := findSteps_add_potentialCore_le hrank hd hbound₀ zs x'
  have hf2 := findSteps_add_potentialCore_le hvalid₁ hd hbound₁ zs y'
  have hlink := link_pot_core hvalid₂ hq hd hbound₂ hxroot hyroot zs
  have hs1 : c₁.2.2 = findSteps s.uf x' := compressWithSteps_steps s.uf x'
  have hs2 : c₂.2.2 = findSteps c₁.1 y' := compressWithSteps_steps c₁.1 y'
  change (c₁.2.2 + c₂.2.2 + 1) + potentialCore zs q d (c₂.1.link rx ry _) ≤ _
  dsimp only [c₁, c₂] at hf1 hf2 hlink hs1 hs2 ⊢
  omega

private theorem two_finds_same_step_core {n : ℕ} {s : State n} (x y : Fin n)
    (hrank : ValidRank s.uf) {q d : ℕ} (hd : 1 ≤ d)
    (hbound : Nat.log 2 n + d < Nat.ackermann q d) (zs : Bool) :
    (step s (.same x y)).trace + potentialCore zs q d (step s (.same x y)).state.uf ≤
      (2 * q + 2) + potentialCore zs q d s.uf := by
  unfold step
  dsimp only
  let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
  set c₁ := compressWithSteps s.uf x'
  have hsz₁ : c₁.1.size = n := (compressWithSteps_size s.uf x').trans s.size_eq
  let y' : Fin c₁.1.size := ⟨y.1, by rw [hsz₁]; exact y.2⟩
  set c₂ := compressWithSteps c₁.1 y'
  have hvalid₁ : ValidRank c₁.1 := hrank.compressWithSteps x'
  have hbound₀ : Nat.log 2 s.uf.size + d < Nat.ackermann q d := by rwa [s.size_eq]
  have hbound₁ : Nat.log 2 c₁.1.size + d < Nat.ackermann q d := by rwa [hsz₁]
  have hf1 := findSteps_add_potentialCore_le hrank hd hbound₀ zs x'
  have hf2 := findSteps_add_potentialCore_le hvalid₁ hd hbound₁ zs y'
  have hs1 : c₁.2.2 = findSteps s.uf x' := compressWithSteps_steps s.uf x'
  have hs2 : c₂.2.2 = findSteps c₁.1 y' := compressWithSteps_steps c₁.1 y'
  change (c₁.2.2 + c₂.2.2) + potentialCore zs q d c₂.1 ≤ _
  dsimp only [c₁, c₂] at hf1 hf2 hs1 hs2 ⊢
  omega

/-! ### Public Tarjan potentials, amortized certificates, and client bounds -/

/-- Potential function on `Fin n` used for Tarjan's single-parameter `O(α(n))` analysis.
Singletons carry zero potential, so `tarjanPotential n _ (init n) = 0`. -/
noncomputable def tarjanPotential (n : ℕ) (_ : Partition n) (s : State n) : ℕ :=
  potentialCore true (Nat.inverseAckermann n) 1 s.uf

/-- Per-operation inverse-Ackermann amortized charge on `Fin n`: `2 * α(n) + 2` for `Op.same`,
`5 * α(n) + 2` for `Op.union`, and `1` for `Op.numComponents`. -/
@[expose] def tarjanCharge (n : ℕ) (_ : Partition n) : Op n → ℕ
  | .same _ _ => 2 * Nat.inverseAckermann n + 2
  | .union _ _ => 5 * Nat.inverseAckermann n + 2
  | .numComponents => 1

/-- Every disjoint-set operation has single-parameter Tarjan charge at most `5 * α(n) + 2`. -/
theorem tarjanCharge_le (n : ℕ) (p : Partition n) (o : Op n) :
    tarjanCharge n p o ≤ 5 * Nat.inverseAckermann n + 2 := by
  have h1 := Nat.one_le_inverseAckermann n
  cases o <;> simp only [tarjanCharge] <;> omega

/-- Initial single-parameter Tarjan potential at `init n` is `0`. -/
@[simp] theorem tarjanPotential_init (n : ℕ) (p : Partition n) :
    tarjanPotential n p (init n) = 0 :=
  potentialCore_true_ofSize _ 1 n

/-- Tarjan's (1975) single-parameter `O(α(n))` amortized step certificate over `impl n`. -/
theorem tarjanAmortized (n : ℕ) :
    Amortized (impl n) id (tarjanPotential n) (tarjanCharge n) := by
  refine Amortized.ofFn fun hr _ he => ?_
  have hstate : (step _ _).state = _ := congrArg StepResult.state he
  have hsteps : (step _ _).trace = _ := congrArg StepResult.trace he
  dsimp only at hstate hsteps
  rw [id, ← hsteps, ← hstate]
  have hvalid := hr.validRank
  have hq : 1 ≤ Nat.inverseAckermann n := Nat.one_le_inverseAckermann n
  have hbound : Nat.log 2 n + 1 < Nat.ackermann (Nat.inverseAckermann n) 1 :=
    Nat.log_add_one_lt_ackermann_inverseAckermann n
  cases ‹Op n› with
  | numComponents =>
    exact Nat.le_refl _
  | same x y =>
    simpa only [tarjanPotential, tarjanCharge] using
      two_finds_same_step_core x y hvalid (Nat.le_refl 1) hbound true
  | union x y =>
    have h := two_finds_union_step_core x y hvalid hq (Nat.le_refl 1) hbound true
    simp only [↓reduceIte, Nat.mul_one] at h
    have hq_eq : 2 * (Nat.inverseAckermann n + 1) +
        (2 * Nat.inverseAckermann n + Nat.inverseAckermann n) =
        5 * Nat.inverseAckermann n + 2 := by omega
    rw [hq_eq] at h
    exact h

/-- Uniform single-parameter amortized step certificate `5 * α(n) + 2` over `impl n`. -/
theorem tarjanUniformAmortized (n : ℕ) :
    Amortized (impl n) id (tarjanPotential n) (fun _ _ => 5 * Nat.inverseAckermann n + 2) where
  step hr hv he := by
    obtain ⟨s', hstep, hr', hpot⟩ := (tarjanAmortized n).step hr hv he
    exact ⟨s', hstep, hr', hpot.trans (Nat.add_le_add_right (tarjanCharge_le n _ _) _)⟩

/-- Running the concrete union-find interpreter from `init n` agrees with abstract `Partition n`
semantics, preserves `Rep`, and satisfies both the exact per-operation and uniform `5 * α(n) + 2`
Tarjan amortized step bounds. -/
theorem tarjan_run_correct {n : ℕ} {β : Type} (client : (spec n).Client β) :
    let (value, finalState, history) := (spec n).runClient (Partition.discrete n) client
    (run (init n) client).value = value ∧ Rep finalState (run (init n) client).state ∧
      total id (run (init n) client).traces ≤
        (spec n).totalCost (tarjanCharge n) (Partition.discrete n) history ∧
      total id (run (init n) client).traces ≤
        history.length * (5 * Nat.inverseAckermann n + 2) := by
  have hv := (spec n).validHistory_of_forall_valid (fun _ _ => trivial)
    (Partition.discrete n) ((spec n).clientHistory (Partition.discrete n) client)
  have hexec := Execution.executes_run step client (init n)
  have hc := (impl n).correct_client (rep_init n) hv hexec
  have hclient := (tarjanAmortized n).client (rep_init n) hv hexec
  have hconst := (tarjanUniformAmortized n).client_const (rep_init n) hv hexec
  rw [tarjanPotential_init] at hclient hconst
  dsimp only at hclient hconst ⊢
  exact ⟨hc.1, hc.2, le_trans (Nat.le_add_right _ _) hclient,
    le_trans (Nat.le_add_right _ _) hconst⟩

/-- Rank-shifted potential function parameterized by `d` on `Fin n` used for Tarjan's
two-parameter `O(m α(m, n))` analysis. Initial potential at `init n` is
`n * (inverseAckermannAt d n * max 1 d)`. -/
noncomputable def tarjanPotentialAt (d n : ℕ) (_ : Partition n) (s : State n) : ℕ :=
  potentialCore false (Nat.inverseAckermannAt d n) (max 1 d) s.uf

/-- Per-operation amortized charge parameterized by `d` on `Fin n`: `2 * α_d(n) + 2` for `Op.same`,
`3 * α_d(n) + 2` for `Op.union`, and `1` for `Op.numComponents`. -/
@[expose] def tarjanChargeAt (d n : ℕ) (_ : Partition n) : Op n → ℕ
  | .same _ _ => 2 * Nat.inverseAckermannAt d n + 2
  | .union _ _ => 3 * Nat.inverseAckermannAt d n + 2
  | .numComponents => 1

/-- Every disjoint-set operation has rank-shifted charge at most `3 * α_d(n) + 2`. -/
theorem tarjanChargeAt_le (d n : ℕ) (p : Partition n) (o : Op n) :
    tarjanChargeAt d n p o ≤ 3 * Nat.inverseAckermannAt d n + 2 := by
  have h1 := Nat.one_le_inverseAckermannAt d n
  cases o <;> simp only [tarjanChargeAt] <;> omega

/-- Initial rank-shifted Tarjan potential at `init n`. -/
@[simp] theorem tarjanPotentialAt_init (d n : ℕ) (p : Partition n) :
    tarjanPotentialAt d n p (init n) = n * (Nat.inverseAckermannAt d n * max 1 d) :=
  potentialCore_false_ofSize _ _ n

/-- Rank-shifted amortized step certificate over `impl n`. -/
theorem tarjanAmortizedAt (d n : ℕ) :
    Amortized (impl n) id (tarjanPotentialAt d n) (tarjanChargeAt d n) := by
  refine Amortized.ofFn fun hr _ he => ?_
  have hstate : (step _ _).state = _ := congrArg StepResult.state he
  have hsteps : (step _ _).trace = _ := congrArg StepResult.trace he
  dsimp only at hstate hsteps
  rw [id, ← hsteps, ← hstate]
  have hvalid := hr.validRank
  have hq : 1 ≤ Nat.inverseAckermannAt d n := Nat.one_le_inverseAckermannAt d n
  have hd : 1 ≤ max 1 d := Nat.le_max_left 1 d
  have hbound : Nat.log 2 n + max 1 d <
      Nat.ackermann (Nat.inverseAckermannAt d n) (max 1 d) :=
    Nat.log_add_lt_ackermann_inverseAckermannAt d n
  cases ‹Op n› with
  | numComponents =>
    exact Nat.le_refl _
  | same x y =>
    simpa only [tarjanPotentialAt, tarjanChargeAt] using
      two_finds_same_step_core x y hvalid hd hbound false
  | union x y =>
    have h := two_finds_union_step_core x y hvalid hq hd hbound false
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have hq_eq : 2 * (Nat.inverseAckermannAt d n + 1) + Nat.inverseAckermannAt d n =
        3 * Nat.inverseAckermannAt d n + 2 := by omega
    rw [hq_eq] at h
    exact h

/-- Uniform rank-shifted amortized step certificate `3 * α_d(n) + 2` over `impl n`. -/
theorem tarjanUniformAmortizedAt (d n : ℕ) :
    Amortized (impl n) id (tarjanPotentialAt d n)
      (fun _ _ => 3 * Nat.inverseAckermannAt d n + 2) where
  step hr hv he := by
    obtain ⟨s', hstep, hr', hpot⟩ := (tarjanAmortizedAt d n).step hr hv he
    exact ⟨s', hstep, hr', hpot.trans (Nat.add_le_add_right (tarjanChargeAt_le d n _ _) _)⟩

/-- **Tarjan (1975) two-parameter `O(m α(m, n))` theorem**: for every universe size `n` and every
adaptive client on `Fin n` issuing `m = history.length` operations from `init n`, the concrete
`Batteries.UnionFind` execution agrees with `Partition n` and executes at most
`m * (5 * Nat.inverseAckermannTwo m n + 2)` total pointer/link steps. -/
theorem tarjan_run_two_param {n : ℕ} {β : Type} (client : (spec n).Client β) :
    let (value, finalState, history) := (spec n).runClient (Partition.discrete n) client
    (run (init n) client).value = value ∧ Rep finalState (run (init n) client).state ∧
      total id (run (init n) client).traces ≤
        history.length * (5 * Nat.inverseAckermannTwo history.length n + 2) := by
  dsimp only
  let m := ((spec n).clientHistory (Partition.discrete n) client).length
  have hrun := tarjan_run_correct client
  dsimp only at hrun
  rcases Nat.lt_or_ge m n with hlt | hle
  · refine ⟨hrun.1, hrun.2.1, ?_⟩
    simpa only [m, Nat.inverseAckermannTwo_of_lt hlt] using hrun.2.2.2
  · refine ⟨hrun.1, hrun.2.1, ?_⟩
    let d := m / n + 1
    have hv := (spec n).validHistory_of_forall_valid (fun _ _ => trivial)
      (Partition.discrete n) ((spec n).clientHistory (Partition.discrete n) client)
    have hexec := Execution.executes_run step client (init n)
    have hconst := (tarjanUniformAmortizedAt d n).client_const (rep_init n) hv hexec
    rw [tarjanPotentialAt_init] at hconst
    dsimp only at hconst
    have hnd : n * max 1 d ≤ 2 * m := by
      rw [max_eq_right (Nat.succ_pos _)]
      cases Nat.eq_zero_or_pos n with
      | inl hn =>
        subst hn
        simp
      | inr hn =>
        have hdiv : n * (m / n) ≤ m := Nat.mul_div_le m n
        rw [Nat.mul_add, Nat.mul_one]
        omega
    have hinit : n * (Nat.inverseAckermannTwo m n * max 1 d) ≤
        m * (2 * Nat.inverseAckermannTwo m n) := by
      calc
        n * (Nat.inverseAckermannTwo m n * max 1 d) =
            (n * max 1 d) * Nat.inverseAckermannTwo m n := by
          rw [Nat.mul_comm (Nat.inverseAckermannTwo m n) (max 1 d), ← Nat.mul_assoc]
        _ ≤ (2 * m) * Nat.inverseAckermannTwo m n := Nat.mul_le_mul_right _ hnd
        _ = m * (2 * Nat.inverseAckermannTwo m n) := by
          rw [Nat.mul_comm 2 m, Nat.mul_assoc]
    have hbound : total id (run (init n) client).traces ≤
        m * (3 * Nat.inverseAckermannTwo m n + 2) +
          n * (Nat.inverseAckermannTwo m n * max 1 d) :=
      le_trans (Nat.le_add_right _ _) hconst
    have hcalc : total id (run (init n) client).traces ≤
        m * (5 * Nat.inverseAckermannTwo m n + 2) := by
      calc
        total id (run (init n) client).traces ≤
            m * (3 * Nat.inverseAckermannTwo m n + 2) +
              n * (Nat.inverseAckermannTwo m n * max 1 d) := hbound
        _ ≤ m * (3 * Nat.inverseAckermannTwo m n + 2) +
              m * (2 * Nat.inverseAckermannTwo m n) := Nat.add_le_add_left hinit _
        _ = m * ((3 * Nat.inverseAckermannTwo m n + 2) + 2 * Nat.inverseAckermannTwo m n) :=
          (Nat.mul_add _ _ _).symm
        _ = m * (5 * Nat.inverseAckermannTwo m n + 2) := by
          congr 1
          omega
    exact hcalc

/-- Strict linear step-count corollary of Tarjan's two-parameter bound: whenever
`n * Nat.log 2 n ≤ m`, every `m`-operation adaptive client on `Fin n` executes at most `7 * m`
pointer/link steps. -/
theorem tarjan_run_linear_of_dense {n : ℕ} {β : Type} (client : (spec n).Client β)
    (hdense : n * Nat.log 2 n ≤ ((spec n).clientHistory (Partition.discrete n) client).length) :
    total id (run (init n) client).traces ≤
      7 * ((spec n).clientHistory (Partition.discrete n) client).length := by
  have htwo := (tarjan_run_two_param client).2.2
  change total id (run (init n) client).traces ≤
    ((spec n).clientHistory (Partition.discrete n) client).length *
      (5 * Nat.inverseAckermannTwo
        ((spec n).clientHistory (Partition.discrete n) client).length n + 2) at htwo
  rw [Nat.inverseAckermannTwo_eq_one_of_mul_log_le hdense] at htwo
  omega

end Cslib.DataStructure.DisjointSet.UnionFind
