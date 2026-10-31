/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.DisjointSet
public import Complexity.Foundations.Semantics.Stateful.Resource
public import Batteries.Data.UnionFind
public import Mathlib.Data.Nat.Log
import all Batteries.Data.UnionFind.Basic

/-!
# Union-find realization and logarithmic step bounds

This module realizes `Cslib.Algorithms.Lean.DisjointSet.spec` using `Batteries.UnionFind`
(disjoint-set forests with union by rank and path compression) together with an explicit component
counter, and establishes worst-case `O(log n)` per-operation parent-pointer traversal bounds.

Under path compression, internal nodes can lose descendants when compressed paths bypass them, so
the naive subtree-size invariant `2 ^ rank u ≤ |subtree u|` is not preserved at internal nodes.
Following [Cormen et al., Exercise 21.4-2][CLRS2009], `ValidRank` instead bounds the
equivalence-class size of each *root* `r < uf.size` by `2 ^ uf.rank r ≤ (equivClass uf r).card`.
Path compression preserves `rootD`, all node ranks, and the set of roots, so `ValidRank` is
preserved immediately across `find` as well as across `push`, root `link`, `checkEquiv`, and
`union`. Because node ranks strictly increase along non-root parent pointers (`uf.rank_lt` and
`le_rank_root`, matching [Cormen et al., Lemma 21.4 and Corollary 21.5][CLRS2009]), every node
satisfies `uf.rank i ≤ Nat.log 2 uf.size`, and every `find` traverses at most
`Nat.log 2 uf.size + 1` nodes.

## Cost model and limitations

The native trace of `Exec` counts parent-pointer inspections during `find` (`1` at the root plus
`1` per parent hop, matching recursive calls of `Batteries.UnionFind.findAux`), plus `1` link step
for `Op.union` and `1` counter read for `Op.numComponents`. Because `Batteries.UnionFind.rankMax`
is marked `noncomputable`, the helpers `rankBound`, `findGo`, and `compressWithSteps` are exposed
solely so that `findSteps`, `step`, and `run` reduce in the Lean kernel (`rfl` / `decide`) while
remaining propositionally equal to `Batteries.UnionFind.find`. This gives a worst-case `O(log n)`
bound from union by rank alone (not Tarjan's inverse-Ackermann `O(α(n))` amortized bound), and
counts abstract forest steps in Lean rather than word-RAM instructions or array-copying overhead if
a `Batteries.UnionFind` value is shared non-linearly.

## Main definitions

* `ofSize`: initialize a `Batteries.UnionFind` forest of `n` singleton classes.
* `equivClass`, `ValidRank`: root equivalence-class finsets and the root rank-size invariant
  `2 ^ uf.rank r ≤ (equivClass uf r).card`.
* `findSteps`, `rankBound`, `findGo`, `compressWithSteps`: computable path-compression step counter
  and kernel-reducible helpers propositionally equal to `Batteries.UnionFind.find`.
* `State`, `init`, `step`, `Exec`, `Rep`, `realization`, `run`: concrete disjoint-set state,
  operations, `Cslib.Stateful.Realization`, and executable client runner.
* `charge`: worst-case per-operation step budget on `Fin n`.

## Main results

* `find_rank`, `union_size`, `checkEquiv_size`, `checkEquiv_snd_eq_true`: structural lemmas for
  `Batteries.UnionFind`.
* `ValidRank.empty`, `ValidRank.push`, `ValidRank.ofSize`, `ValidRank.find`, `ValidRank.link`,
  `ValidRank.checkEquiv`, `ValidRank.union`: preservation of the root rank-size invariant.
* `ValidRank.two_pow_rank_le_size`, `ValidRank.rank_le_log`: exponential class-size lower bound and
  logarithmic rank bound `uf.rank i ≤ Nat.log 2 uf.size`.
* `findSteps_eq`, `findSteps_le_rank_sub_add_one`, `ValidRank.findSteps_le_log_add_one`: recursive
  characterization and `Nat.log 2 uf.size + 1` bound on `find` traversal length.
* `Rep.validRank`, `Rep.rel_iff_equiv`, `Rep.numComp_eq`, `rep_init`: representation invariant
  projections and initialization.
* `stepBound`, `uniformStepBound`, `realized_client`, `run_correct`: stateful resource certificates
  and adaptive-client correctness and cost theorems.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Chapter 21][CLRS2009]
-/

public section

namespace Cslib.Algorithms.Lean.DisjointSet.UnionFind

open Cslib.Stateful Cslib.Algorithms.Lean.DisjointSet

/-! ### Structural lemmas for `Batteries.UnionFind` -/

private theorem unionFind_ext {u v : Batteries.UnionFind} (h : u.arr = v.arr) : u = v := by
  cases u
  cases v
  cases h
  rfl

private theorem coe_cast_fin {m n : ℕ} (h : m = n) (y : Fin n) :
    ((h ▸ y : Fin m) : ℕ) = y.1 := by
  subst h
  rfl

@[simp]
theorem size_empty : Batteries.UnionFind.empty.size = 0 := rfl

@[simp]
theorem size_push (uf : Batteries.UnionFind) : uf.push.size = uf.size + 1 :=
  Array.size_push _

/-- Path compression preserves every node's rank. -/
@[simp]
theorem find_rank (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (uf.find x).1.rank i = uf.rank i := by
  unfold Batteries.UnionFind.find
  exact Batteries.UnionFind.rankD_findAux

/-- `Batteries.UnionFind.union` preserves universe size. -/
@[simp]
theorem union_size (uf : Batteries.UnionFind) (x y : Fin uf.size) :
    (uf.union x y).size = uf.size := by
  simp [Batteries.UnionFind.union, Batteries.UnionFind.size]

/-- `Batteries.UnionFind.checkEquiv` preserves universe size. -/
@[simp]
theorem checkEquiv_size (uf : Batteries.UnionFind) (x y : Fin uf.size) :
    (uf.checkEquiv x y).1.size = uf.size := by
  unfold Batteries.UnionFind.checkEquiv
  simp

/-- `Batteries.UnionFind.checkEquiv` preserves the equivalence relation. -/
theorem equiv_checkEquiv (uf : Batteries.UnionFind) (x y : Fin uf.size) {a b : ℕ} :
    (uf.checkEquiv x y).1.Equiv a b ↔ uf.Equiv a b := by
  unfold Batteries.UnionFind.checkEquiv
  simp [Batteries.UnionFind.equiv_find]

/-- `Batteries.UnionFind.checkEquiv` returns `true` iff `x` and `y` are equivalent. -/
theorem checkEquiv_snd_eq_true (uf : Batteries.UnionFind) (x y : Fin uf.size) :
    (uf.checkEquiv x y).2 = true ↔ uf.Equiv x.1 y.1 := by
  unfold Batteries.UnionFind.checkEquiv
  have h1 := Batteries.UnionFind.find_root_2 uf x
  have hroot : ∀ i, (uf.find x).1.rootD i = uf.rootD i := Batteries.UnionFind.find_root_1 uf x
  generalize hfind : uf.find x = fx at h1 hroot ⊢
  rcases fx with ⟨s, ⟨r₁, hr₁⟩, h⟩
  dsimp only at h1 hroot ⊢
  have h2 := Batteries.UnionFind.find_root_2 s (h ▸ y)
  rw [beq_iff_eq, h1, h2, coe_cast_fin h y, hroot]
  rfl

private theorem rank_link (uf : Batteries.UnionFind) (x y : Fin uf.size)
    (hy : uf.parent y.1 = y.1) (i : ℕ) :
    (uf.link x y hy).rank i =
      if x.1 ≠ y.1 ∧ uf.rank x.1 = uf.rank y.1 ∧ y.1 = i then
        uf.rank y.1 + 1
      else
        uf.rank i := by
  simp only [Batteries.UnionFind.rank, Batteries.UnionFind.arr_link, Batteries.UnionFind.linkAux]
  by_cases hxy : x.1 = y.1
  · simp [hxy]
  · simp only [hxy, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    have hrx : Batteries.UnionFind.rankD uf.arr x.1 = uf.arr[x.1].rank :=
      Batteries.UnionFind.rankD_eq x.2
    have hry : Batteries.UnionFind.rankD uf.arr y.1 = uf.arr[y.1].rank :=
      Batteries.UnionFind.rankD_eq y.2
    rw [hrx, hry]
    by_cases hlt : uf.arr[y.1].rank < uf.arr[x.1].rank
    · have hne_rk : uf.arr[x.1].rank ≠ uf.arr[y.1].rank := Nat.ne_of_gt hlt
      simp only [hlt, ↓reduceIte, hne_rk, false_and, Batteries.UnionFind.rankD_set]
      by_cases hyi : y.1 = i
      · subst hyi
        simp [hry]
      · simp [hyi]
    · simp only [hlt, ↓reduceIte]
      by_cases heq_rk : uf.arr[x.1].rank = uf.arr[y.1].rank
      · simp only [heq_rk, ↓reduceIte, true_and, Batteries.UnionFind.rankD_set]
        by_cases hyi : y.1 = i
        · simp [hyi]
        · simp only [hyi, ↓reduceIte]
          by_cases hxi : x.1 = i
          · subst hxi
            simp [heq_rk, hrx]
          · simp [hxi]
      · simp only [heq_rk, ↓reduceIte, false_and, Batteries.UnionFind.rankD_set]
        by_cases hxi : x.1 = i
        · subst hxi
          simp [hrx]
        · simp [hxi]

/-- Initialize a `Batteries.UnionFind` forest of `n` singleton classes `{0}, …, {n - 1}`. -/
@[expose] def ofSize : ℕ → Batteries.UnionFind
  | 0 => .empty
  | n + 1 => (ofSize n).push

@[simp]
theorem size_ofSize (n : ℕ) : (ofSize n).size = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofSize, ih]

@[simp]
theorem parent_ofSize (n i : ℕ) : (ofSize n).parent i = i := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofSize, ih]

@[simp]
theorem rank_ofSize (n i : ℕ) : (ofSize n).rank i = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofSize, ih]

@[simp]
theorem rootD_ofSize (n i : ℕ) : (ofSize n).rootD i = i := by
  induction n with
  | zero => rfl
  | succ n ih => simp [ofSize, ih]

@[simp]
theorem equiv_ofSize {n a b : ℕ} : (ofSize n).Equiv a b ↔ a = b := by
  simp [Batteries.UnionFind.Equiv]

/-! ### Root rank-size invariant and logarithmic rank bound -/

/-- The finite set of in-bounds elements of `uf` whose canonical root is `r`. -/
@[expose] def equivClass (uf : Batteries.UnionFind) (r : ℕ) : Finset ℕ :=
  (Finset.range uf.size).filter fun i => uf.rootD i = r

@[simp]
theorem mem_equivClass {uf : Batteries.UnionFind} {r i : ℕ} :
    i ∈ equivClass uf r ↔ i < uf.size ∧ uf.rootD i = r := by
  simp [equivClass]

theorem card_equivClass_le_size (uf : Batteries.UnionFind) (r : ℕ) :
    (equivClass uf r).card ≤ uf.size :=
  (Finset.card_filter_le _ _).trans (by simp)

theorem disjoint_equivClass_of_ne (uf : Batteries.UnionFind) {r₁ r₂ : ℕ} (hne : r₁ ≠ r₂) :
    Disjoint (equivClass uf r₁) (equivClass uf r₂) :=
  Finset.disjoint_left.mpr fun _ h₁ h₂ =>
    hne ((mem_equivClass.mp h₁).2.symm.trans (mem_equivClass.mp h₂).2)

/-- Root rank-size invariant ([Cormen et al., Exercise 21.4-2][CLRS2009]): every root `r < uf.size`
has equivalence class of cardinality at least `2 ^ uf.rank r`. -/
@[expose] def ValidRank (uf : Batteries.UnionFind) : Prop :=
  ∀ ⦃r : ℕ⦄, r < uf.size → uf.parent r = r → 2 ^ uf.rank r ≤ (equivClass uf r).card

namespace ValidRank

theorem empty : ValidRank .empty := by
  intro r hr
  simp at hr

theorem push {uf : Batteries.UnionFind} (h : ValidRank uf) : ValidRank uf.push := by
  intro r hr hp
  rw [size_push] at hr
  rw [Batteries.UnionFind.parent_push] at hp
  rw [Batteries.UnionFind.rank_push]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hr) with hrlt | rfl
  · refine (h hrlt hp).trans (Finset.card_le_card fun i hi => ?_)
    obtain ⟨hilt, hiroot⟩ := mem_equivClass.mp hi
    exact mem_equivClass.mpr ⟨by rw [size_push]; exact Nat.lt_succ_of_lt hilt,
      by simpa using hiroot⟩
  · have hrank0 : uf.rank uf.size = 0 := by
      simp [Batteries.UnionFind.rank, Batteries.UnionFind.rankD]
    rw [hrank0, pow_zero]
    refine Finset.card_pos.mpr ⟨uf.size, mem_equivClass.mpr ⟨by simp, ?_⟩⟩
    rw [Batteries.UnionFind.root_push, Batteries.UnionFind.rootD_eq_self.mpr hp]

theorem ofSize (n : ℕ) : ValidRank (UnionFind.ofSize n) := by
  induction n with
  | zero => exact empty
  | succ _ ih => exact ih.push

theorem find {uf : Batteries.UnionFind} (h : ValidRank uf) (x : Fin uf.size) :
    ValidRank (uf.find x).1 := by
  intro r hr hp'
  rw [Batteries.UnionFind.find_size] at hr
  rw [find_rank]
  have hroot_r : uf.rootD r = r := by
    rw [← Batteries.UnionFind.find_root_1 uf x r]
    exact Batteries.UnionFind.rootD_eq_self.mpr hp'
  have hp : uf.parent r = r := Batteries.UnionFind.rootD_eq_self.mp hroot_r
  have heq : equivClass (uf.find x).1 r = equivClass uf r := by
    ext i
    simp [Batteries.UnionFind.find_size, Batteries.UnionFind.find_root_1]
  rw [heq]
  exact h hr hp

theorem link {uf : Batteries.UnionFind} (h : ValidRank uf) {x y : Fin uf.size}
    (hx : uf.parent x.1 = x.1) (hy : uf.parent y.1 = y.1) :
    ValidRank (uf.link x y hy) := by
  intro r hr hp'
  have hsize : (uf.link x y hy).size = uf.size := by
    simp [Batteries.UnionFind.size]
  rw [hsize] at hr
  by_cases hxy : x.1 = y.1
  · have heq : uf.link x y hy = uf := by
      apply unionFind_ext
      simp [Batteries.UnionFind.linkAux, hxy]
    rw [heq] at hp' ⊢
    exact h hr hp'
  · obtain ⟨r₀, hr₀, hroot⟩ := Batteries.UnionFind.root_link hx hy
    have hx_rootD : uf.rootD x.1 = x.1 := Batteries.UnionFind.rootD_eq_self.mpr hx
    have hr₀_eq : (uf.link x y hy).rootD x.1 = r₀.1 := by
      simpa [hx_rootD] using hroot x.1
    have hr₀_parent : (uf.link x y hy).parent r₀.1 = r₀.1 := by
      rw [← hr₀_eq]
      exact Batteries.UnionFind.parent_rootD _ _
    by_cases hlt : uf.rank y.1 < uf.rank x.1
    · have hparent : ∀ i, (uf.link x y hy).parent i = if y.1 = i then x.1 else uf.parent i := by
        intro i
        rw [Batteries.UnionFind.parent_link hy]
        simp [hxy, hlt]
      have hy_not_root : (uf.link x y hy).parent y.1 ≠ y.1 := by
        rw [hparent y.1, ite_eq_left rfl]
        exact hxy
      have hr₀_x : r₀ = x := by
        rcases hr₀ with hrx | hry
        · exact hrx
        · rw [hry] at hr₀_parent
          exact absurd hr₀_parent hy_not_root
      rw [hr₀_x] at hroot
      have hyr : y.1 ≠ r := fun heq => by
        rw [← heq] at hp'
        exact hy_not_root hp'
      have hp : uf.parent r = r := by
        have hp₁ := hp'
        rw [hparent r, ite_eq_right hyr] at hp₁
        exact hp₁
      have hrank : (uf.link x y hy).rank r = uf.rank r := by
        rw [rank_link, ite_eq_right]
        rintro ⟨_, _, hyr'⟩
        exact hyr hyr'
      have hsub : equivClass uf r ⊆ equivClass (uf.link x y hy) r := by
        intro i hi
        obtain ⟨hi_lt, hi_root⟩ := mem_equivClass.mp hi
        refine mem_equivClass.mpr ⟨by simpa [hsize] using hi_lt, ?_⟩
        rw [hroot i, hi_root]
        by_cases hrx : r = x.1
        · simp [hrx]
        · simp [hrx, Ne.symm hyr]
      rw [hrank]
      exact (h hr hp).trans (Finset.card_le_card hsub)
    · have hparent : ∀ i, (uf.link x y hy).parent i = if x.1 = i then y.1 else uf.parent i := by
        intro i
        rw [Batteries.UnionFind.parent_link hy]
        simp [hxy, hlt]
      have hx_not_root : (uf.link x y hy).parent x.1 ≠ x.1 := by
        rw [hparent x.1, ite_eq_left rfl]
        exact Ne.symm hxy
      have hr₀_y : r₀ = y := by
        rcases hr₀ with hrx | hry
        · rw [hrx] at hr₀_parent
          exact absurd hr₀_parent hx_not_root
        · exact hry
      rw [hr₀_y] at hroot
      have hxr : x.1 ≠ r := fun heq => by
        rw [← heq] at hp'
        exact hx_not_root hp'
      have hp : uf.parent r = r := by
        have hp₁ := hp'
        rw [hparent r, ite_eq_right hxr] at hp₁
        exact hp₁
      have hsub_r : equivClass uf r ⊆ equivClass (uf.link x y hy) r := by
        intro i hi
        obtain ⟨hi_lt, hi_root⟩ := mem_equivClass.mp hi
        refine mem_equivClass.mpr ⟨by simpa [hsize] using hi_lt, ?_⟩
        rw [hroot i, hi_root]
        by_cases hry : r = y.1
        · simp [hry]
        · simp [Ne.symm hxr, hry]
      rw [rank_link]
      split
      · next hcond =>
        obtain ⟨_, heq_rk, hyr⟩ := hcond
        subst hyr
        have hsub_x : equivClass uf x.1 ⊆ equivClass (uf.link x y hy) y.1 := by
          intro i hi
          obtain ⟨hi_lt, hi_root⟩ := mem_equivClass.mp hi
          refine mem_equivClass.mpr ⟨by simpa [hsize] using hi_lt, ?_⟩
          rw [hroot i, hi_root]
          simp
        have hcard_union :
            (equivClass uf x.1).card + (equivClass uf y.1).card ≤
              (equivClass (uf.link x y hy) y.1).card := by
          rw [← Finset.card_union_of_disjoint (disjoint_equivClass_of_ne uf hxy)]
          exact Finset.card_le_card (Finset.union_subset hsub_x hsub_r)
        have hx_card := h x.2 hx
        have hy_card := h y.2 hy
        rw [heq_rk] at hx_card
        rw [pow_succ]
        omega
      · exact (h hr hp).trans (Finset.card_le_card hsub_r)

theorem checkEquiv {uf : Batteries.UnionFind} (h : ValidRank uf) (x y : Fin uf.size) :
    ValidRank (uf.checkEquiv x y).1 := by
  unfold Batteries.UnionFind.checkEquiv
  exact (h.find x).find _

theorem union {uf : Batteries.UnionFind} (h : ValidRank uf) (x y : Fin uf.size) :
    ValidRank (uf.union x y) := by
  unfold Batteries.UnionFind.union
  dsimp only
  have h₁ : ValidRank (uf.find x).1 := h.find x
  have hrx_eq : ((uf.find x).2.1 : ℕ) = uf.rootD x.1 := Batteries.UnionFind.find_root_2 uf x
  generalize hfx : uf.find x = fx at h₁ hrx_eq ⊢
  rcases fx with ⟨uf₁, rx, ex⟩
  dsimp only at h₁ hrx_eq ⊢
  have hy : y.1 < uf₁.size := by rw [ex]; exact y.2
  have h₂ : ValidRank (uf₁.find ⟨y.1, hy⟩).1 := h₁.find ⟨y.1, hy⟩
  have hrx_root₁ : uf₁.rootD rx.1 = rx.1 := by
    have hfind1 := Batteries.UnionFind.find_root_1 uf x rx.1
    rw [hfx] at hfind1
    dsimp only at hfind1
    rw [hfind1, hrx_eq, Batteries.UnionFind.rootD_rootD]
  have hfind2 := Batteries.UnionFind.find_root_1 uf₁ ⟨y.1, hy⟩ rx.1
  refine h₂.link ?_ _
  exact Batteries.UnionFind.rootD_eq_self.mp (hfind2.trans hrx_root₁)

/-- Every in-bounds node `i < uf.size` satisfies `2 ^ uf.rank i ≤ uf.size`. -/
theorem two_pow_rank_le_size {uf : Batteries.UnionFind} (h : ValidRank uf) {i : ℕ}
    (hi : i < uf.size) : 2 ^ uf.rank i ≤ uf.size := by
  have hr_lt : uf.rootD i < uf.size := Batteries.UnionFind.rootD_lt.mpr hi
  have hr_parent : uf.parent (uf.rootD i) = uf.rootD i := Batteries.UnionFind.parent_rootD uf i
  have hpow : 2 ^ uf.rank i ≤ 2 ^ uf.rank (uf.rootD i) :=
    Nat.pow_le_pow_right (by decide) Batteries.UnionFind.le_rank_root
  exact (hpow.trans (h hr_lt hr_parent)).trans (card_equivClass_le_size uf _)

/-- Logarithmic rank bound ([Cormen et al., Exercise 21.4-2][CLRS2009]): every node in a rank-valid
`Batteries.UnionFind` forest has rank at most `Nat.log 2 uf.size`. -/
theorem rank_le_log {uf : Batteries.UnionFind} (h : ValidRank uf) (i : ℕ) :
    uf.rank i ≤ Nat.log 2 uf.size := by
  by_cases hi : i < uf.size
  · exact Nat.le_log_of_pow_le (by decide) (h.two_pow_rank_le_size hi)
  · have hrank0 : uf.rank i = 0 := by
      simp [Batteries.UnionFind.rank, Batteries.UnionFind.rankD, hi]
    rw [hrank0]
    exact Nat.zero_le _

end ValidRank

/-! ### Computable path-compression wrapper and step bounds -/

/-- Computable strict upper bound on all node ranks in `uf` (matching `Batteries.UnionFind.rankMax`
without `noncomputable`). -/
@[expose] def rankBound (uf : Batteries.UnionFind) : ℕ :=
  uf.arr.foldr (max ·.rank) 0 + 1

private theorem rankBound_eq_rankMax (uf : Batteries.UnionFind) :
    rankBound uf = uf.rankMax := rfl

/-- Structural-fuel traversal matching `Batteries.UnionFind.findAux` while counting visited nodes
(`1` at the root check plus `1` per parent hop). -/
@[expose] def findGo (uf : Batteries.UnionFind) :
    ℕ → Fin uf.size → Batteries.UnionFind.FindAux uf.size × ℕ
  | 0, x => (⟨uf.arr, x, rfl⟩, 1)
  | fuel + 1, x =>
    let y := uf.arr[x.1].parent
    if y = x.1 then
      (⟨uf.arr, x, rfl⟩, 1)
    else
      let res := findGo uf fuel ⟨y, uf.parent'_lt x.1 x.2⟩
      (⟨res.1.s.modify x.1 fun s => { s with parent := res.1.root.1 },
        res.1.root, Array.size_modify.trans res.1.size_eq⟩,
       res.2 + 1)

private theorem findGo_fst_eq_findAux (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      uf.rankMax - uf.rank x.1 ≤ fuel →
      (findGo uf fuel x).1 = uf.findAux x
  | 0, x, hle => by
    have hlt := uf.lt_rankMax x.1
    omega
  | fuel + 1, x, hle => by
    rw [findGo, Batteries.UnionFind.findAux]
    dsimp only [dite_eq_ite]
    split
    · rfl
    · next h =>
      have hrank := uf.rank'_lt x.1 x.2 h
      have hmax := uf.lt_rankMax x.1
      have hfuel : uf.rankMax - uf.rank uf.arr[x.1].parent ≤ fuel := by omega
      have ih := findGo_fst_eq_findAux uf fuel ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ hfuel
      dsimp only
      simp only [ih]

private theorem findGo_rankBound_fst (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (findGo uf (rankBound uf) x).1 = uf.findAux x :=
  findGo_fst_eq_findAux uf (rankBound uf) x (by rw [rankBound_eq_rankMax]; exact Nat.sub_le _ _)

private theorem findGo_snd_indep (uf : Batteries.UnionFind) :
    ∀ (fuel₁ fuel₂ : ℕ) (x : Fin uf.size),
      uf.rankMax - uf.rank x.1 ≤ fuel₁ →
      uf.rankMax - uf.rank x.1 ≤ fuel₂ →
      (findGo uf fuel₁ x).2 = (findGo uf fuel₂ x).2
  | 0, _, x, h₁, _ => by
    have hlt := uf.lt_rankMax x.1
    omega
  | _ + 1, 0, x, _, h₂ => by
    have hlt := uf.lt_rankMax x.1
    omega
  | fuel₁ + 1, fuel₂ + 1, x, h₁, h₂ => by
    rw [findGo, findGo]
    dsimp only
    split
    · rfl
    · next h =>
      have hrank := uf.rank'_lt x.1 x.2 h
      have hmax := uf.lt_rankMax x.1
      have hf₁ : uf.rankMax - uf.rank uf.arr[x.1].parent ≤ fuel₁ := by omega
      have hf₂ : uf.rankMax - uf.rank uf.arr[x.1].parent ≤ fuel₂ := by omega
      exact congrArg (· + 1)
        (findGo_snd_indep uf fuel₁ fuel₂ ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ hf₁ hf₂)

private theorem findGo_snd_le (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      uf.rankMax - uf.rank x.1 ≤ fuel →
      (findGo uf fuel x).2 ≤ (uf.rank (uf.rootD x.1) - uf.rank x.1) + 1
  | 0, x, hle => by
    have hlt := uf.lt_rankMax x.1
    omega
  | fuel + 1, x, hle => by
    rw [findGo]
    dsimp only
    split
    · omega
    · next h =>
      let y : Fin uf.size := ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
      have hrank : uf.rank x.1 < uf.rank y.1 := uf.rank'_lt x.1 x.2 h
      have hmax := uf.lt_rankMax x.1
      have hfuel : uf.rankMax - uf.rank y.1 ≤ fuel := by omega
      have ih := findGo_snd_le uf fuel y hfuel
      have hroot : uf.rootD y.1 = uf.rootD x.1 := by
        have hp : y.1 = uf.parent x.1 := (Batteries.UnionFind.parentD_eq x.2).symm
        rw [hp, Batteries.UnionFind.rootD_parent]
      have hle_root : uf.rank y.1 ≤ uf.rank (uf.rootD y.1) := Batteries.UnionFind.le_rank_root
      rw [hroot] at ih hle_root
      change (findGo uf fuel y).2 + 1 ≤ (uf.rank (uf.rootD x.1) - uf.rank x.1) + 1
      omega

/-- Number of nodes inspected by `Batteries.UnionFind.find` starting at `x` (`1` at the root plus
`1` per parent pointer traversed). -/
@[expose] def findSteps (uf : Batteries.UnionFind) (x : Fin uf.size) : ℕ :=
  (findGo uf (rankBound uf) x).2

/-- Recursive unfolding equation for `findSteps`. -/
theorem findSteps_eq (uf : Batteries.UnionFind) (x : Fin uf.size) :
    findSteps uf x =
      if uf.arr[x.1].parent = x.1 then
        1
      else
        findSteps uf ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩ + 1 := by
  unfold findSteps rankBound
  rw [findGo]
  dsimp only
  split
  · rfl
  · next h =>
    let y : Fin uf.size := ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
    have hrank : 0 < uf.rank y.1 :=
      Nat.lt_of_le_of_lt (Nat.zero_le (uf.rank x.1)) (uf.rank'_lt x.1 x.2 h)
    have hk₁ : uf.rankMax - uf.rank y.1 ≤ uf.arr.foldr (max ·.rank) 0 := by
      change (uf.arr.foldr (max ·.rank) 0 + 1) - uf.rank y.1 ≤ uf.arr.foldr (max ·.rank) 0
      omega
    have hk₂ : uf.rankMax - uf.rank y.1 ≤ uf.arr.foldr (max ·.rank) 0 + 1 :=
      Nat.le_succ_of_le hk₁
    exact congrArg (· + 1) (findGo_snd_indep uf _ _ y hk₁ hk₂)

/-- Every `find` inspects at least `1` node. -/
theorem findSteps_pos (uf : Batteries.UnionFind) (x : Fin uf.size) :
    0 < findSteps uf x := by
  rw [findSteps_eq]
  split <;> omega

/-- Because `uf.rank` increases strictly at every non-root parent hop, `findSteps uf x` is bounded
by `(uf.rank (uf.rootD x) - uf.rank x) + 1`. -/
theorem findSteps_le_rank_sub_add_one (uf : Batteries.UnionFind) (x : Fin uf.size) :
    findSteps uf x ≤ (uf.rank (uf.rootD x.1) - uf.rank x.1) + 1 :=
  findGo_snd_le uf (rankBound uf) x (by rw [rankBound_eq_rankMax]; exact Nat.sub_le _ _)

/-- Under `ValidRank uf`, every `find` inspects at most `Nat.log 2 uf.size + 1` nodes. -/
theorem ValidRank.findSteps_le_log_add_one {uf : Batteries.UnionFind} (h : ValidRank uf)
    (x : Fin uf.size) : findSteps uf x ≤ Nat.log 2 uf.size + 1 := by
  have hsteps := findSteps_le_rank_sub_add_one uf x
  have hlog := h.rank_le_log (uf.rootD x.1)
  omega

/-- Kernel-reducible path-compression `find` returning the updated `Batteries.UnionFind`, the root
in `Fin uf.size`, and `findSteps uf x`. Propositionally equal to `Batteries.UnionFind.find`. -/
@[expose] def compressWithSteps (uf : Batteries.UnionFind) (x : Fin uf.size) :
    Batteries.UnionFind × Fin uf.size × ℕ :=
  let res := findGo uf (rankBound uf) x
  let uf' : Batteries.UnionFind :=
    { arr := res.1.s
      parentD_lt := fun {i} hi => by
        rw [res.1.size_eq] at hi ⊢
        rw [findGo_rankBound_fst uf x]
        exact Batteries.UnionFind.parentD_findAux_lt hi
      rankD_lt := fun {i} hi => by
        rw [findGo_rankBound_fst uf x] at hi ⊢
        rw [Batteries.UnionFind.rankD_findAux, Batteries.UnionFind.rankD_findAux]
        exact Batteries.UnionFind.lt_rankD_findAux hi }
  (uf', res.1.root, res.2)

@[simp]
private theorem compressWithSteps_fst (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (compressWithSteps uf x).1 = (uf.find x).1 := by
  apply unionFind_ext
  unfold compressWithSteps Batteries.UnionFind.find
  dsimp only
  exact congrArg Batteries.UnionFind.FindAux.s (findGo_rankBound_fst uf x)

private theorem compressWithSteps_size (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (compressWithSteps uf x).1.size = uf.size := by
  simp

@[simp]
private theorem compressWithSteps_root (uf : Batteries.UnionFind) (x : Fin uf.size) :
    ((compressWithSteps uf x).2.1 : ℕ) = uf.rootD x.1 := by
  unfold compressWithSteps
  dsimp only
  rw [findGo_rankBound_fst, Batteries.UnionFind.findAux_root,
    Batteries.UnionFind.rootD, dite_eq_left x.2]

@[simp]
private theorem compressWithSteps_steps (uf : Batteries.UnionFind) (x : Fin uf.size) :
    (compressWithSteps uf x).2.2 = findSteps uf x := rfl

private theorem compressWithSteps_eq_find_of_eq {u v : Batteries.UnionFind} (h : u = v)
    {i : ℕ} (hu : i < u.size) (hv : i < v.size) :
    (compressWithSteps u ⟨i, hu⟩).1 = (v.find ⟨i, hv⟩).1 ∧
      ((compressWithSteps u ⟨i, hu⟩).2.1 : ℕ) = ((v.find ⟨i, hv⟩).2.1 : ℕ) := by
  subst h
  exact ⟨compressWithSteps_fst _ _,
    by rw [compressWithSteps_root, Batteries.UnionFind.find_root_2]⟩

private theorem link_eq_of_eq {u v : Batteries.UnionFind} (h : u = v)
    {x₁ y₁ : Fin u.size} {x₂ y₂ : Fin v.size} (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1)
    (hy₁ : u.parent y₁.1 = y₁.1) (hy₂ : v.parent y₂.1 = y₂.1) :
    u.link x₁ y₁ hy₁ = v.link x₂ y₂ hy₂ := by
  subst h
  obtain rfl : x₁ = x₂ := Fin.ext hx
  obtain rfl : y₁ = y₂ := Fin.ext hy
  rfl

/-! ### Stateful realization of `DisjointSet.spec` -/

/-- Concrete union-find state over `Fin n`: a `Batteries.UnionFind` forest of size `n` paired with
the maintained number of equivalence classes. -/
structure State (n : ℕ) where
  /-- Underlying `Batteries.UnionFind` forest. -/
  uf : Batteries.UnionFind
  /-- Fixed universe size invariant. -/
  size_eq : uf.size = n
  /-- Maintained number of connected components. -/
  numComp : ℕ

/-- Initial concrete disjoint-set state of `n` singleton components. -/
@[expose] def init (n : ℕ) : State n where
  uf := ofSize n
  size_eq := size_ofSize n
  numComp := n

/-- Execute a single `DisjointSet.Op n` on `s`, returning the updated state, answer, and step
count. -/
@[expose] def step {n : ℕ} (s : State n) (o : Op n) :
    State n × (spec n).Result o × ℕ :=
  match o with
  | .same x y =>
    let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := by exact (compressWithSteps_size s.uf x').trans s.size_eq
    let y' : Fin c₁.1.size := ⟨y.1, by rw [hsz₁]; exact y.2⟩
    let c₂ := compressWithSteps c₁.1 y'
    have hsz₂ : c₂.1.size = n := by exact (compressWithSteps_size c₁.1 y').trans hsz₁
    let r₁ := c₁.2.1.1
    let r₂ := c₂.2.1.1
    (⟨c₂.1, hsz₂, s.numComp⟩, r₁ == r₂, c₁.2.2 + c₂.2.2)
  | .union x y =>
    let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := by exact (compressWithSteps_size s.uf x').trans s.size_eq
    let y' : Fin c₁.1.size := ⟨y.1, by rw [hsz₁]; exact y.2⟩
    let c₂ := compressWithSteps c₁.1 y'
    have hsz₂ : c₂.1.size = n := by exact (compressWithSteps_size c₁.1 y').trans hsz₁
    let r₁ := c₁.2.1.1
    let r₂ := c₂.2.1.1
    let rx : Fin c₂.1.size := ⟨r₁, by
      rw [compressWithSteps_size c₁.1 y', compressWithSteps_size s.uf x']
      exact c₁.2.1.2⟩
    let ry : Fin c₂.1.size := ⟨r₂, by
      rw [compressWithSteps_size c₁.1 y']
      exact c₂.2.1.2⟩
    have hyroot : c₂.1.parent ry.1 = ry.1 := by
      have hr : r₂ = c₁.1.rootD y.1 := compressWithSteps_root c₁.1 y'
      have hf : c₂.1.rootD r₂ = c₁.1.rootD r₂ := by
        change (compressWithSteps c₁.1 y').1.rootD r₂ = c₁.1.rootD r₂
        rw [compressWithSteps_fst]
        exact Batteries.UnionFind.find_root_1 c₁.1 y' r₂
      change c₂.1.parent r₂ = r₂
      rw [← Batteries.UnionFind.rootD_eq_self, hf, hr, Batteries.UnionFind.rootD_rootD]
    let uf' := c₂.1.link rx ry hyroot
    have hsz' : uf'.size = n := by
      have hl : uf'.size = c₂.1.size := by simp [uf', Batteries.UnionFind.size]
      exact hl.trans hsz₂
    let merged := r₁ != r₂
    let numComp' := if merged then s.numComp - 1 else s.numComp
    (⟨uf', hsz', numComp'⟩, merged, c₁.2.2 + c₂.2.2 + 1)
  | .numComponents =>
    (s, s.numComp, 1)

private theorem step_union_uf_eq {n : ℕ} (s : State n) (x y : Fin n) :
    (step s (.union x y)).1.uf =
      s.uf.union ⟨x.1, s.size_eq.symm ▸ x.2⟩ ⟨y.1, s.size_eq.symm ▸ y.2⟩ := by
  unfold step Batteries.UnionFind.union
  dsimp only
  let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
  have ⟨huf₁, hrx₁⟩ := compressWithSteps_eq_find_of_eq (rfl : s.uf = s.uf) x'.2 x'.2
  have ⟨huf₂, hry₂⟩ := compressWithSteps_eq_find_of_eq huf₁
    (by rw [(compressWithSteps_size s.uf x').trans s.size_eq]; exact y.2)
    (by rw [(s.uf.find ⟨x.1, s.size_eq.symm ▸ x.2⟩).2.2, s.size_eq]; exact y.2)
  exact link_eq_of_eq huf₂ hrx₁ hry₂ _ _

/-- Native execution relation for `DisjointSet.spec n` over `State n`. -/
@[expose] def Exec (n : ℕ) : Execution (spec n) (State n) ℕ :=
  fun s o a s' steps => step s o = (s', a, steps)

/-- Representation relation coupling an abstract `Partition n` with a concrete `State n`. -/
@[expose] def Rep {n : ℕ} (p : Partition n) (s : State n) : Prop :=
  ValidRank s.uf ∧
    (∀ x y : Fin n, p.rel x y = true ↔ s.uf.Equiv x.1 y.1) ∧
    s.numComp = p.numComponents

/-- Extract the root rank-size invariant from `Rep`. -/
theorem Rep.validRank {n : ℕ} {p : Partition n} {s : State n} (h : Rep p s) :
    ValidRank s.uf := h.1

/-- Extract the element-equivalence coupling from `Rep`. -/
theorem Rep.rel_iff_equiv {n : ℕ} {p : Partition n} {s : State n} (h : Rep p s) (x y : Fin n) :
    p.rel x y = true ↔ s.uf.Equiv x.1 y.1 := h.2.1 x y

/-- Extract the maintained component-count equality from `Rep`. -/
theorem Rep.numComp_eq {n : ℕ} {p : Partition n} {s : State n} (h : Rep p s) :
    s.numComp = p.numComponents := h.2.2

/-- `init n` represents the discrete partition `Partition.discrete n` of `n` singletons. -/
theorem rep_init (n : ℕ) : Rep (Partition.discrete n) (init n) := by
  refine ⟨ValidRank.ofSize n, ?_, ?_⟩
  · intro x y
    simp [init, Fin.ext_iff]
  · simp [init]

private theorem step_correct {n : ℕ} {p : Partition n} {s : State n} (o : Op n)
    (hr : Rep p s) :
    (step s o).2.1 = ((spec n).step p o).2 ∧
      Rep ((spec n).step p o).1 (step s o).1 := by
  obtain ⟨hrank, hrel, hcomp⟩ := hr
  cases o with
  | numComponents =>
    exact ⟨hcomp, hrank, hrel, hcomp⟩
  | same x y =>
    let x' : Fin s.uf.size := ⟨x.1, s.size_eq.symm ▸ x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := (compressWithSteps_size s.uf x').trans s.size_eq
    let y' : Fin c₁.1.size := ⟨y.1, hsz₁.symm ▸ y.2⟩
    let c₂ := compressWithSteps c₁.1 y'
    have hroot₁ : (c₁.2.1 : ℕ) = s.uf.rootD x.1 := compressWithSteps_root s.uf x'
    have hroot₂ : (c₂.2.1 : ℕ) = s.uf.rootD y.1 := by
      rw [compressWithSteps_root]
      change c₁.1.rootD y.1 = s.uf.rootD y.1
      rw [compressWithSteps_fst, Batteries.UnionFind.find_root_1]
    have hans : (c₁.2.1.1 == c₂.2.1.1) = p.rel x y := by
      rw [Bool.eq_iff_iff, beq_iff_eq, hroot₁, hroot₂, hrel]
      rfl
    have hrank₂ : ValidRank c₂.1 := by
      have hr₁ : ValidRank c₁.1 := by
        change ValidRank (compressWithSteps s.uf x').1
        rw [compressWithSteps_fst]
        exact hrank.find x'
      change ValidRank (compressWithSteps c₁.1 y').1
      rw [compressWithSteps_fst]
      exact hr₁.find y'
    have hequiv₂ : ∀ u v : Fin n, p.rel u v = true ↔ c₂.1.Equiv u.1 v.1 := by
      intro u v
      rw [hrel u v]
      change s.uf.Equiv u.1 v.1 ↔ (compressWithSteps c₁.1 y').1.Equiv u.1 v.1
      rw [compressWithSteps_fst, Batteries.UnionFind.equiv_find]
      change s.uf.Equiv u.1 v.1 ↔ (compressWithSteps s.uf x').1.Equiv u.1 v.1
      rw [compressWithSteps_fst, Batteries.UnionFind.equiv_find]
    exact ⟨hans, hrank₂, hequiv₂, hcomp⟩
  | union x y =>
    let x' : Fin s.uf.size := ⟨x.1, s.size_eq.symm ▸ x.2⟩
    let y₀ : Fin s.uf.size := ⟨y.1, s.size_eq.symm ▸ y.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := (compressWithSteps_size s.uf x').trans s.size_eq
    let y' : Fin c₁.1.size := ⟨y.1, hsz₁.symm ▸ y.2⟩
    let c₂ := compressWithSteps c₁.1 y'
    have hroot₁ : (c₁.2.1 : ℕ) = s.uf.rootD x.1 := compressWithSteps_root s.uf x'
    have hroot₂ : (c₂.2.1 : ℕ) = s.uf.rootD y.1 := by
      rw [compressWithSteps_root]
      change c₁.1.rootD y.1 = s.uf.rootD y.1
      rw [compressWithSteps_fst, Batteries.UnionFind.find_root_1]
    have hmerged : (c₁.2.1.1 != c₂.2.1.1) = !p.rel x y := by
      rw [Bool.eq_iff_iff, bne_iff_ne, Bool.not_eq_true']
      constructor
      · intro hne
        cases hpxy : p.rel x y
        · rfl
        · exfalso
          exact hne (by rw [hroot₁, hroot₂]; exact (hrel x y).mp hpxy)
      · intro hfalse heq
        rw [hroot₁, hroot₂] at heq
        have htrue := (hrel x y).mpr heq
        rw [hfalse] at htrue
        cases htrue
    have huf_eq : (step s (.union x y)).1.uf = s.uf.union x' y₀ := step_union_uf_eq s x y
    refine ⟨hmerged, ?_, ?_, ?_⟩
    · rw [huf_eq]
      exact hrank.union x' y₀
    · intro u v
      rw [huf_eq, Batteries.UnionFind.equiv_union]
      change (p.merge x y).rel u v = true ↔ _
      rw [Partition.rel_merge_eq_true, hrel u v, hrel u x, hrel y v, hrel u y, hrel x v]
    · change (if (c₁.2.1.1 != c₂.2.1.1) = true then s.numComp - 1 else s.numComp) =
        (p.merge x y).numComponents
      rw [hmerged, hcomp]
      cases hpxy : p.rel x y
      · simp only [Bool.not_false, ↓reduceIte]
        have hm := Partition.numComponents_merge_of_not_rel hpxy
        omega
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact (Partition.numComponents_merge_of_rel hpxy).symm

/-- Semantic realization of `DisjointSet.spec n` by `Batteries.UnionFind` with path compression
and union by rank. -/
def realization (n : ℕ) : Realization (spec n) (Exec n) where
  rep := Rep
  total o _ _ := ⟨(step _ o).2.1, (step _ o).1, (step _ o).2.2, rfl⟩
  correct {p s o a s' steps} hr _ he := by
    have hc := step_correct o hr
    have hs : s' = (step s o).1 := (Prod.ext_iff.mp he).1.symm
    have ha : a = (step s o).2.1 := (Prod.ext_iff.mp (Prod.ext_iff.mp he).2).1.symm
    rw [ha, hs]
    exact hc

/-- Worst-case per-operation step budget on `Fin n`: at most `Nat.log 2 n + 1` nodes inspected per
`find`, plus `1` link step in `Op.union` and `1` counter read in `Op.numComponents`. -/
@[expose] def charge (n : ℕ) (_ : Partition n) : Op n → ℕ
  | .same _ _ => 2 * (Nat.log 2 n + 1)
  | .union _ _ => 2 * (Nat.log 2 n + 1) + 1
  | .numComponents => 1

/-- Every disjoint-set operation has worst-case charge at most `2 * Nat.log 2 n + 3`. -/
theorem charge_le (n : ℕ) (p : Partition n) (o : Op n) :
    charge n p o ≤ 2 * Nat.log 2 n + 3 := by
  cases o <;> simp only [charge] <;> omega

private theorem step_steps_le {n : ℕ} {p : Partition n} {s : State n} (o : Op n)
    (hr : Rep p s) : (step s o).2.2 ≤ charge n p o := by
  obtain ⟨hrank, _, _⟩ := hr
  cases o with
  | numComponents =>
    exact Nat.le_refl 1
  | same x y =>
    let x' : Fin s.uf.size := ⟨x.1, s.size_eq.symm ▸ x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := (compressWithSteps_size s.uf x').trans s.size_eq
    let y' : Fin c₁.1.size := ⟨y.1, hsz₁.symm ▸ y.2⟩
    have ht₁ : c₁.2.2 ≤ Nat.log 2 n + 1 := by
      change findSteps s.uf x' ≤ Nat.log 2 n + 1
      simpa only [s.size_eq] using hrank.findSteps_le_log_add_one x'
    have hr₁ : ValidRank c₁.1 := by
      change ValidRank (compressWithSteps s.uf x').1
      rw [compressWithSteps_fst]
      exact hrank.find x'
    have ht₂ : (compressWithSteps c₁.1 y').2.2 ≤ Nat.log 2 n + 1 := by
      simpa only [compressWithSteps_steps, hsz₁] using hr₁.findSteps_le_log_add_one y'
    change c₁.2.2 + (compressWithSteps c₁.1 y').2.2 ≤ 2 * (Nat.log 2 n + 1)
    omega
  | union x y =>
    let x' : Fin s.uf.size := ⟨x.1, s.size_eq.symm ▸ x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := (compressWithSteps_size s.uf x').trans s.size_eq
    let y' : Fin c₁.1.size := ⟨y.1, hsz₁.symm ▸ y.2⟩
    have ht₁ : c₁.2.2 ≤ Nat.log 2 n + 1 := by
      change findSteps s.uf x' ≤ Nat.log 2 n + 1
      simpa only [s.size_eq] using hrank.findSteps_le_log_add_one x'
    have hr₁ : ValidRank c₁.1 := by
      change ValidRank (compressWithSteps s.uf x').1
      rw [compressWithSteps_fst]
      exact hrank.find x'
    have ht₂ : (compressWithSteps c₁.1 y').2.2 ≤ Nat.log 2 n + 1 := by
      simpa only [compressWithSteps_steps, hsz₁] using hr₁.findSteps_le_log_add_one y'
    change c₁.2.2 + (compressWithSteps c₁.1 y').2.2 + 1 ≤ 2 * (Nat.log 2 n + 1) + 1
    omega

/-- Per-operation logarithmic step certificate for `realization n`. -/
theorem stepBound (n : ℕ) : Bound (realization n) id (charge n) := by
  intro p s o a s' steps hr _ he
  have hsteps : steps = (step s o).2.2 := (Prod.ext_iff.mp (Prod.ext_iff.mp he).2).2.symm
  rw [id, hsteps]
  exact step_steps_le o hr

/-- Uniform per-operation logarithmic step certificate `2 * Nat.log 2 n + 3`. -/
theorem uniformStepBound (n : ℕ) :
    Bound (realization n) id (fun _ _ => 2 * Nat.log 2 n + 3) :=
  fun hr hv he => (stepBound n hr hv he).trans (charge_le n _ _)

/-- Every adaptive disjoint-set client has a valid execution matching abstract partition semantics
and satisfying the additive `O(log n)` per-operation step bound. -/
theorem realized_client {n : ℕ} {β : Type} (client : (spec n).Client β)
    {p : Partition n} {s : State n} (hr : Rep p s) :
    ∃ s' traces, Executes (Exec n) client s ((spec n).runClient p client).1 s' traces ∧
      Rep ((spec n).runClient p client).2.1 s' ∧
      total id traces ≤ (spec n).totalCost (charge n) p ((spec n).runClient p client).2.2 := by
  have hv := (spec n).validHistory_of_forall_valid (fun _ _ => trivial)
    p ((spec n).runClient p client).2.2
  exact Bound.exists_executes (stepBound n) client hr hv

/-- Execute a disjoint-set client concretely, recording the exact step count of each operation. -/
@[expose] def run {n : ℕ} {β : Type} (s : State n) :
    (spec n).Client β → β × State n × List ℕ
  | .pure a => (a, s, [])
  | .liftBind o k =>
      let next := step s o
      let rest := run next.1 (k next.2.1)
      (rest.1, rest.2.1, next.2.2 :: rest.2.2)

/-- The concrete runner produces a valid `Executes (Exec n)` derivation. -/
theorem run_exec {n : ℕ} {β : Type} (client : (spec n).Client β) (s : State n) :
    Executes (Exec n) client s (run s client).1 (run s client).2.1 (run s client).2.2 := by
  induction client generalizing s with
  | pure a => exact .pure a s
  | liftBind o k ih => exact .call rfl (ih _ _)

/-- Running the concrete union-find interpreter agrees with abstract `Partition n` semantics,
preserves `Rep`, and satisfies both the exact per-operation and uniform `O(log n)` step bounds. -/
theorem run_correct {n : ℕ} {β : Type} (client : (spec n).Client β)
    {p : Partition n} {s : State n} (hr : Rep p s) :
    (run s client).1 = ((spec n).runClient p client).1 ∧
      Rep ((spec n).runClient p client).2.1 (run s client).2.1 ∧
      total id (run s client).2.2 ≤
        (spec n).totalCost (charge n) p ((spec n).runClient p client).2.2 ∧
      total id (run s client).2.2 ≤
        ((spec n).runClient p client).2.2.length * (2 * Nat.log 2 n + 3) := by
  have hv := (spec n).validHistory_of_forall_valid (fun _ _ => trivial)
    p ((spec n).runClient p client).2.2
  have hexec := run_exec client s
  have hc := (realization n).correct_client hr hv hexec
  exact ⟨hc.1, hc.2, Bound.client (stepBound n) hr hv hexec,
    Bound.client_const (uniformStepBound n) hr hv hexec⟩

end Cslib.Algorithms.Lean.DisjointSet.UnionFind
