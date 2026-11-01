/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Mixing
public import Complexity.Foundations.Combinatorics.Expander.Power
public import Mathlib.Data.Fin.Tuple.Take
import Complexity.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Walks on rotation maps

A walk of length `t` in a `D`-regular multigraph `G` on `V` is a start vertex together with `t`
labels, `p : V × (Fin t → D)`, and takes the edges labelled `p.2 0, …, p.2 (t - 1)` in turn.
There are `|V| |D| ^ t` of them, and they are the darts of the power `G.pow t`. Walks are the
combinatorial side of the powering step of Dinur's proof of the PCP theorem
[Dinur, Sections 3.2 and 5][Dinur2005]
[Arora and Barak, Chapter 22][AroraBarak09], whose analysis counts the steps of a random walk that
cross a given set of edges; this file provides the facts about walks that analysis rests on.

The trajectory `G.walkAt p i` is the vertex reached after `i` steps (constant after the last step)
and `G.walkDart p i` is the edge taken at step `i`, as a dart. A walk ends at
`(G.pow t).neighbor p.1 p.2` (`walkAt_length`), so averaging over the labels from a fixed start is
applying the walk operator `G.walk ^ t` (`expect_walkAt_length`, through `walk_pow`), and the
rotation map of `G.pow t` reverses walks: it reverses the trajectory (`walkAt_rot_pow`) and the
darts, each seen from its other end (`walkDart_rot_pow`), and it reverses the steps after the
`n`-th into the first `t - n` steps of the reverse (`rot_pow_walkDrop`).

Splitting a walk at its `i`-th step into the dart `q` taken there, the reverse of the first `i`
steps, which leads back from `q` to the start, and the steps after it, which lead on from the far
end of `q`, is a bijection `splitWalk i` onto `(V × D) × (Fin i → D) × (Fin (t - (i + 1)) → D)`.
So the three pieces of a uniformly random walk are independent and uniform (`expect_splitWalk`),
and walks crossing a dart with conditions on the two pieces are counted by independent factors
(`card_filter_splitWalk`). In particular **each step of a random walk is a uniformly random dart**
(`expect_walkDart`): every dart is the `i`-th dart of `|D| ^ (t - 1)` walks of length `t`
(`sum_walkDart`, `card_filter_walkDart_eq`). This is the fact behind the first-moment estimate of
the powering step.

For steps `i < j`, the correlation of a function of the `i`-th dart with a function of the `j`-th
dart is a correlation along `j - (i + 1)` steps of the random walk (`expect_walkDart_mul_walkDart`),
so the mixing lemma bounds its distance to the product of the averages by `λ(G) ^ (j - (i + 1))`
times the standard deviations (`sq_expect_walkDart_mul_walkDart_sub_le`). Summed over the pairs of
steps, this is the second-moment estimate of the powering step.

## Main definitions

* `Cslib.RotationMap.walkAt`: the vertex of a walk after `i` steps.
* `Cslib.RotationMap.walkDart`: the dart of a walk at step `i`.
* `Cslib.RotationMap.walkDrop`: the walk after the first `n` steps of a walk.
* `Cslib.RotationMap.splitWalk`: splitting a walk at a step into the dart taken there, the reverse
  of the steps before it and the steps after it.

## Main results

* `Cslib.RotationMap.walkAt_length`, `Cslib.RotationMap.expect_walkAt_length`: a walk ends at its
  neighbor in `G.pow t`, so averaging over the walks from a vertex applies `G.walk ^ t`.
* `Cslib.RotationMap.walkAt_rot_pow`, `Cslib.RotationMap.walkDart_rot_pow`,
  `Cslib.RotationMap.rot_pow_walkDrop`: the rotation map of `G.pow t` reverses walks.
* `Cslib.RotationMap.expect_splitWalk`, `Cslib.RotationMap.card_filter_splitWalk`: the pieces of a
  walk split at a step are independent and uniform.
* `Cslib.RotationMap.expect_walkDart`, `Cslib.RotationMap.sum_walkDart`: each step of a random walk
  is a uniformly random dart.
* `Cslib.RotationMap.expect_walkDart_mul_walkDart`: the correlation of two darts of a random walk
  is a correlation along the walk operator.
* `Cslib.RotationMap.sq_expect_walkDart_mul_walkDart_sub_le`,
  `Cslib.RotationMap.abs_expect_walkDart_mul_walkDart_sub_le`: two darts of a random walk are
  almost independent.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.RotationMap

open Finset
open scoped BigOperators

variable {V D : Type*} (G : RotationMap V D) {t : ℕ}

section Trajectory

/-- The vertex reached after `i` steps of the walk `p = (v, k)` of length `t`, which starts at `v`
and takes the edges labelled `k 0, …, k (t - 1)` in turn. After its last step the walk stays at its
end: `G.walkAt p i = G.walkAt p t` for `t ≤ i` (`walkAt_of_le`). -/
def walkAt (p : V × (Fin t → D)) : ℕ → V
  | 0 => p.1
  | i + 1 => if h : i < t then G.neighbor (walkAt p i) (p.2 ⟨i, h⟩) else walkAt p i

/-- A walk starts at its first vertex. -/
@[simp]
theorem walkAt_zero (p : V × (Fin t → D)) : G.walkAt p 0 = p.1 :=
  rfl

/-- At its step `i + 1 ≤ t`, a walk moves along its `i`-th label. -/
theorem walkAt_succ_of_lt (p : V × (Fin t → D)) {i : ℕ} (h : i < t) :
    G.walkAt p (i + 1) = G.neighbor (G.walkAt p i) (p.2 ⟨i, h⟩) :=
  dite_eq_left h

/-- After its last step, a walk does not move. -/
theorem walkAt_succ_of_le (p : V × (Fin t → D)) {i : ℕ} (h : t ≤ i) :
    G.walkAt p (i + 1) = G.walkAt p i :=
  dite_eq_right (Nat.not_lt.2 h)

/-- After its last step a walk stays at its end. -/
theorem walkAt_of_le (p : V × (Fin t → D)) {i : ℕ} (h : t ≤ i) : G.walkAt p i = G.walkAt p t := by
  induction i, h using Nat.le_induction with
  | base => rfl
  | succ i hi ih => rw [G.walkAt_succ_of_le p hi, ih]

/-- The `i`-th dart of the walk `p`: the edge taken at step `i`, seen from the vertex where it is
taken. -/
def walkDart (p : V × (Fin t → D)) (i : Fin t) : V × D :=
  (G.walkAt p i, p.2 i)

/-- The `i`-th dart of a walk starts at its `i`-th vertex. -/
@[simp]
theorem walkDart_fst (p : V × (Fin t → D)) (i : Fin t) : (G.walkDart p i).1 = G.walkAt p i :=
  rfl

/-- The `i`-th dart of a walk has its `i`-th label. -/
@[simp]
theorem walkDart_snd (p : V × (Fin t → D)) (i : Fin t) : (G.walkDart p i).2 = p.2 i :=
  rfl

/-- The `i`-th dart of a walk leads to its `(i + 1)`-th vertex. -/
theorem fst_rot_walkDart (p : V × (Fin t → D)) (i : Fin t) :
    (G.rot (G.walkDart p i)).1 = G.walkAt p (i + 1) :=
  (G.walkAt_succ_of_lt p i.isLt).symm

/-- A walk whose first label is `a` takes the edge `a` and then walks along the remaining labels. -/
theorem walkAt_cons_succ (v : V) (a : D) (k : Fin t → D) (i : ℕ) :
    G.walkAt (v, Fin.cons a k) (i + 1) = G.walkAt (G.neighbor v a, k) i := by
  induction i with
  | zero => exact G.walkAt_succ_of_lt _ t.succ_pos
  | succ i ih =>
    by_cases h : i < t
    · rw [G.walkAt_succ_of_lt _ (Nat.succ_lt_succ h), ih, G.walkAt_succ_of_lt _ h]
      rfl
    · rw [G.walkAt_succ_of_le _ (Nat.succ_le_succ (Nat.not_lt.1 h)), ih,
        G.walkAt_succ_of_le _ (Nat.not_lt.1 h)]

/-- The `(i + 1)`-th dart of a walk whose first label is `a` is the `i`-th dart of the walk along
the remaining labels from the neighbor along `a`. -/
theorem walkDart_cons_succ (v : V) (a : D) (k : Fin t → D) (i : Fin t) :
    G.walkDart (v, Fin.cons a k) i.succ = G.walkDart (G.neighbor v a, k) i := by
  rw [walkDart, Fin.val_succ, walkAt_cons_succ]
  rfl

/-- The walk along the first `n` labels of a walk follows it for `n` steps. -/
theorem walkAt_take (p : V × (Fin t → D)) {n i : ℕ} (hn : n ≤ t) (hi : i ≤ n) :
    G.walkAt (p.1, Fin.take n hn p.2) i = G.walkAt p i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [G.walkAt_succ_of_lt _ (by omega : i < n), ih (by omega),
      G.walkAt_succ_of_lt _ (by omega : i < t)]
    rfl

/-- The darts of the walk along the first `n` labels of a walk are its first `n` darts. -/
theorem walkDart_take (p : V × (Fin t → D)) {n : ℕ} (hn : n ≤ t) (i : Fin n) :
    G.walkDart (p.1, Fin.take n hn p.2) i = G.walkDart p (Fin.castLE hn i) := by
  rw [walkDart, walkDart, G.walkAt_take p hn i.isLt.le]
  rfl

/-- Appending a label to a walk does not change its first `t` steps. -/
theorem walkAt_snoc (v : V) (k : Fin t → D) (a : D) {i : ℕ} (hi : i ≤ t) :
    G.walkAt (v, Fin.snoc k a) i = G.walkAt (v, k) i := by
  rw [← G.walkAt_take (v, Fin.snoc k a) t.le_succ hi]
  simp [Fin.take_eq_init]

/-- The `i`-th dart of a walk extended by a label `a` is the `i`-th dart of the walk. -/
theorem walkDart_snoc_castSucc (v : V) (k : Fin t → D) (a : D) (i : Fin t) :
    G.walkDart (v, Fin.snoc k a) i.castSucc = G.walkDart (v, k) i := by
  rw [walkDart, walkDart, Fin.val_castSucc, G.walkAt_snoc v k a i.isLt.le]
  simp

/-- The walk along the labels of `p` after its `n`-th step, from the `n`-th vertex of `p`. -/
def walkDrop (p : V × (Fin t → D)) (n : ℕ) : V × (Fin (t - n) → D) :=
  (G.walkAt p n, fun j ↦ p.2 ⟨n + j, by have := j.isLt; omega⟩)

/-- The walk after the `n`-th step of `p` starts at the `n`-th vertex of `p`. -/
@[simp]
theorem walkDrop_fst (p : V × (Fin t → D)) (n : ℕ) : (G.walkDrop p n).1 = G.walkAt p n :=
  rfl

/-- The labels of the walk after the `n`-th step of `p` are the remaining labels of `p`. -/
theorem walkDrop_snd_apply (p : V × (Fin t → D)) (n : ℕ) (j : Fin (t - n)) :
    (G.walkDrop p n).2 j = p.2 ⟨n + j, by have := j.isLt; omega⟩ :=
  rfl

/-- The walk after the `n`-th step of `p` follows `p` from its `n`-th vertex on. -/
theorem walkAt_walkDrop (p : V × (Fin t → D)) (n i : ℕ) :
    G.walkAt (G.walkDrop p n) i = G.walkAt p (n + i) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    by_cases h : i < t - n
    · rw [G.walkAt_succ_of_lt _ h, ih, ← add_assoc, G.walkAt_succ_of_lt _ (by omega : n + i < t)]
      rfl
    · rw [G.walkAt_succ_of_le _ (Nat.not_lt.1 h), ih, ← add_assoc,
        G.walkAt_succ_of_le _ (by omega : t ≤ n + i)]

/-- The `j`-th dart of the walk after the `n`-th step of `p` is the `(n + j)`-th dart of `p`. -/
theorem walkDart_walkDrop (p : V × (Fin t → D)) (n : ℕ) (j : Fin (t - n)) :
    G.walkDart (G.walkDrop p n) j = G.walkDart p ⟨n + j, by have := j.isLt; omega⟩ := by
  rw [walkDart, walkDart, walkAt_walkDrop]
  rfl

/-- A walk of length `t` ends at the neighbor along its labels in the power `G ^ t`. -/
theorem walkAt_length (p : V × (Fin t → D)) : G.walkAt p t = (G.pow t).neighbor p.1 p.2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    obtain ⟨v, k⟩ := p
    calc G.walkAt (v, k) (t + 1) = G.walkAt (v, Fin.cons (k 0) (Fin.tail k)) (t + 1) := by
          rw [Fin.cons_self_tail]
      _ = (G.pow (t + 1)).neighbor v k := by
          rw [walkAt_cons_succ, ih, neighbor_pow_succ]

/-- The `n`-th vertex of a walk is the neighbor along its first `n` labels in the power `G ^ n`. -/
theorem walkAt_eq_neighbor_pow (p : V × (Fin t → D)) {n : ℕ} (hn : n ≤ t) :
    G.walkAt p n = (G.pow n).neighbor p.1 (Fin.take n hn p.2) := by
  rw [← G.walkAt_take p hn le_rfl, walkAt_length]

end Trajectory

section Reverse

/-- Reversing a walk in `G ^ t` reverses its darts: the `i`-th dart of the reverse of `p` is the
`(t - 1 - i)`-th dart of `p` seen from its other end. -/
theorem walkDart_rot_pow (p : V × (Fin t → D)) (i : Fin t) :
    G.walkDart ((G.pow t).rot p) i = G.rot (G.walkDart p i.rev) := by
  induction t with
  | zero => exact i.elim0
  | succ t ih =>
    obtain ⟨v, k⟩ := p
    -- the reverse of `(v, k)` is the reverse of the walk from the first neighbor, followed by the
    -- first edge seen from its other end
    rw [rot_pow_succ]
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.rev_last]
      refine Prod.ext ?_ ?_
      · rw [walkDart_fst, Fin.val_last, G.walkAt_snoc _ _ _ le_rfl, Prod.mk.eta, walkAt_length]
        exact (G.pow t).neighbor_neighbor_rot _ _
      · simp [walkDart]
    | cast i =>
      rw [walkDart_snoc_castSucc, Prod.mk.eta, ih, Fin.rev_castSucc]
      congr 1
      conv_rhs => rw [← Fin.cons_self_tail k]
      rw [walkDart_cons_succ]
      rfl

/-- Reversing a walk in `G ^ t` reverses its trajectory. -/
theorem walkAt_rot_pow (p : V × (Fin t → D)) {i : ℕ} (hi : i ≤ t) :
    G.walkAt ((G.pow t).rot p) i = G.walkAt p (t - i) := by
  rcases hi.lt_or_eq with hi | rfl
  · change G.walkAt _ (⟨i, hi⟩ : Fin t) = _
    rw [← walkDart_fst, walkDart_rot_pow, fst_rot_walkDart, Fin.val_rev, Fin.val_mk]
    congr 1
    omega
  · rw [walkAt_length, Nat.sub_self, walkAt_zero]
    exact (G.pow i).neighbor_neighbor_rot _ _

/-- The reverse of the walk after the `n`-th step of `p` is the walk along the first `t - n` labels
of the reverse of `p`. -/
theorem rot_pow_walkDrop (p : V × (Fin t → D)) (n : ℕ) :
    (G.pow (t - n)).rot (G.walkDrop p n) =
      (((G.pow t).rot p).1, Fin.take (t - n) (Nat.sub_le t n) ((G.pow t).rot p).2) := by
  refine Prod.ext ?_ (funext fun j ↦ ?_)
  · have h : G.walkAt (G.walkDrop p n) (t - n) = G.walkAt p t := by
      rw [walkAt_walkDrop]
      rcases le_total n t with h | h
      · rw [Nat.add_sub_of_le h]
      · rw [G.walkAt_of_le p (by omega : t ≤ n + (t - n))]
    exact (G.walkAt_length (G.walkDrop p n)).symm.trans (h.trans (G.walkAt_length p))
  · have h₁ := congrArg Prod.snd (G.walkDart_rot_pow (G.walkDrop p n) j)
    have h₂ := congrArg Prod.snd (G.walkDart_rot_pow p (Fin.castLE (Nat.sub_le t n) j))
    simp only [walkDart_snd] at h₁ h₂
    dsimp only
    rw [Fin.take_apply, h₁, h₂, walkDart_walkDrop]
    congr 3
    ext
    simp only [Fin.val_rev, Fin.val_castLE]
    omega

end Reverse

section Expect

variable [Fintype D]

/-- Averaged over its labels, a walk of length `t` from `v` ends where the random walk is after `t`
steps: the average of `f` over its ends is `(G.walk ^ t) f v`. -/
theorem expect_walkAt_length (v : V) (f : V → ℝ) :
    𝔼 k : Fin t → D, f (G.walkAt (v, k) t) = (G.walk ^ t) f v := by
  simp only [walkAt_length, ← walk_pow, walk_apply]

/-- The correlation of `f` at the start with `g` at the end of a uniformly random walk of length `t`
is `𝔼 v, f v * (G.walk ^ t) g v`, the quantity estimated by the mixing lemma
`sq_expect_mul_walk_pow_sub_le`. -/
theorem expect_mul_walkAt_length [Fintype V] (f g : V → ℝ) :
    𝔼 p : V × (Fin t → D), f p.1 * g (G.walkAt p t) = 𝔼 v, f v * (G.walk ^ t) g v := by
  rw [← univ_product_univ, expect_product]
  simp only [← mul_expect, expect_walkAt_length]

end Expect

section Split

/-- Gluing `r`, `a` and `s` gives back `r` before position `i`. -/
private theorem take_glue (i : Fin t) (r : Fin i → D) (a : D) (s : Fin (t - (i + 1)) → D) :
    Fin.take i i.isLt.le (Fin.append (Fin.snoc r a) s ∘ Fin.cast (Nat.add_sub_of_le i.isLt).symm) =
      r := by
  funext j
  rw [Fin.take_apply, Function.comp_apply,
    show (Fin.castLE i.isLt.le j).cast (Nat.add_sub_of_le i.isLt).symm =
      Fin.castAdd _ j.castSucc from Fin.ext rfl, Fin.append_left, Fin.snoc_castSucc]

/-- Gluing `r`, `a` and `s` gives `a` at position `i`. -/
private theorem glue_self (i : Fin t) (r : Fin i → D) (a : D) (s : Fin (t - (i + 1)) → D) :
    (Fin.append (Fin.snoc r a) s ∘ Fin.cast (Nat.add_sub_of_le i.isLt).symm) i = a := by
  rw [Function.comp_apply,
    show i.cast (Nat.add_sub_of_le i.isLt).symm = Fin.castAdd _ (Fin.last i) from Fin.ext rfl,
    Fin.append_left, Fin.snoc_last]

/-- Gluing `r`, `a` and `s` gives back `s` after position `i`. -/
private theorem glue_add (i : Fin t) (r : Fin i → D) (a : D) (s : Fin (t - (i + 1)) → D)
    (j : Fin (t - (i + 1))) :
    (Fin.append (Fin.snoc r a) s ∘ Fin.cast (Nat.add_sub_of_le i.isLt).symm)
      ⟨i + 1 + j, by have := j.isLt; omega⟩ = s j := by
  rw [Function.comp_apply,
    show (⟨i + 1 + j, _⟩ : Fin t).cast (Nat.add_sub_of_le i.isLt).symm = Fin.natAdd _ j from
      Fin.ext rfl, Fin.append_right]

/-- A tuple is glued from its labels before, at and after position `i`. -/
private theorem glue_take_drop (p : V × (Fin t → D)) (i : Fin t) :
    Fin.append (Fin.snoc (Fin.take i i.isLt.le p.2) (p.2 i)) (G.walkDrop p (i + 1)).2 ∘
      Fin.cast (Nat.add_sub_of_le i.isLt).symm = p.2 := by
  funext j
  rw [Function.comp_apply]
  rcases lt_trichotomy (j : ℕ) i with h | h | h
  · rw [show j.cast (Nat.add_sub_of_le i.isLt).symm = Fin.castAdd _ (⟨j, h⟩ : Fin i).castSucc from
      Fin.ext rfl, Fin.append_left, Fin.snoc_castSucc, Fin.take_apply]
    rfl
  · rw [show j.cast (Nat.add_sub_of_le i.isLt).symm = Fin.castAdd _ (Fin.last i) from Fin.ext h,
      Fin.append_left, Fin.snoc_last, Fin.ext h]
  · have := j.isLt
    rw [show j.cast (Nat.add_sub_of_le i.isLt).symm =
        Fin.natAdd (i + 1) ⟨j - (i + 1), by omega⟩ from
        Fin.ext (by simp only [Fin.val_cast, Fin.val_natAdd]; omega),
      Fin.append_right, walkDrop_snd_apply]
    exact congrArg p.2 (Fin.ext (by simp only; omega))

/-- **Splitting a walk at its `i`-th step.** A walk `p` of length `t` is determined by its `i`-th
dart `q`, the labels `r` of the reverse of its first `i` steps, which lead back from the start of
`q` to the start of `p`, and its labels `s` after step `i`, which lead on from the end of `q`; and
any such data come from a walk. So `(q, r, s)` ranges over all of
`(V × D) × (Fin i → D) × (Fin (t - (i + 1)) → D)` as `p` ranges over the walks: `q` is the crossed
dart, `(q.1, r)` the walk back to the start (`fst_rot_pow_take`, `walkAt_rot_pow_take`) and
`((G.rot q).1, s)` the walk on to the end (`fst_rot_walkDart`, `walkAt_walkDrop`). The inverse
glues a walk from these pieces. -/
def splitWalk (i : Fin t) :
    V × (Fin t → D) ≃ (V × D) × (Fin i → D) × (Fin (t - (i + 1)) → D) where
  toFun p := (G.walkDart p i, ((G.pow i).rot (p.1, Fin.take i i.isLt.le p.2)).2,
    (G.walkDrop p (i + 1)).2)
  invFun x := (((G.pow i).rot (x.1.1, x.2.1)).1,
    Fin.append (Fin.snoc ((G.pow i).rot (x.1.1, x.2.1)).2 x.1.2) x.2.2 ∘
      Fin.cast (Nat.add_sub_of_le i.isLt).symm)
  left_inv p := by
    have h : (G.walkAt p i, ((G.pow i).rot (p.1, Fin.take i i.isLt.le p.2)).2) =
        (G.pow i).rot (p.1, Fin.take i i.isLt.le p.2) :=
      Prod.ext (G.walkAt_eq_neighbor_pow p i.isLt.le) rfl
    simp only [walkDart, h, rot_rot, glue_take_drop]
  right_inv x := by
    obtain ⟨⟨w, a⟩, r, s⟩ := x
    dsimp only
    have hu : (G.pow i).rot ((G.pow i).rot (w, r)) = (w, r) := rot_rot _ _
    generalize (G.pow i).rot (w, r) = u at hu ⊢
    refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
    · rw [walkDart_fst, G.walkAt_eq_neighbor_pow _ i.isLt.le, take_glue, neighbor_def, Prod.mk.eta,
        hu]
    · exact glue_self i u.2 a s
    · rw [take_glue, Prod.mk.eta, hu]
    · funext j
      exact glue_add i u.2 a s j

/-- The pieces of a walk split at its `i`-th step. -/
theorem splitWalk_apply (i : Fin t) (p : V × (Fin t → D)) :
    G.splitWalk i p = (G.walkDart p i, ((G.pow i).rot (p.1, Fin.take i i.isLt.le p.2)).2,
      (G.walkDrop p (i + 1)).2) :=
  rfl

/-- The reverse of the first `n` steps of a walk starts at its `n`-th vertex. -/
theorem fst_rot_pow_take (p : V × (Fin t → D)) {n : ℕ} (hn : n ≤ t) :
    ((G.pow n).rot (p.1, Fin.take n hn p.2)).1 = G.walkAt p n :=
  (G.walkAt_eq_neighbor_pow p hn).symm

/-- The reverse of the first `n` steps of a walk retraces them. -/
theorem walkAt_rot_pow_take (p : V × (Fin t → D)) {n i : ℕ} (hn : n ≤ t) (hi : i ≤ n) :
    G.walkAt ((G.pow n).rot (p.1, Fin.take n hn p.2)) i = G.walkAt p (n - i) := by
  rw [G.walkAt_rot_pow _ hi, G.walkAt_take p hn (Nat.sub_le n i)]

variable [Fintype V] [Fintype D]

/-- **The pieces of a uniformly random walk are independent and uniform.** Split at its `i`-th
step, a uniformly random walk of length `t` has a uniformly random `i`-th dart, and independently
of it uniformly random labels before and after it. -/
theorem expect_splitWalk {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (i : Fin t)
    (F : (V × D) × (Fin i → D) × (Fin (t - (i + 1)) → D) → M) :
    𝔼 p, F (G.splitWalk i p) = 𝔼 q, 𝔼 r, 𝔼 s, F (q, r, s) := by
  rw [Fintype.expect_equiv (G.splitWalk i) _ F fun _ ↦ rfl, Fintype.expect_prod_type]
  simp only [Fintype.expect_prod_type]

/-- **The crossing count.** Counted by their `i`-th dart `q`, the walks of length `t` for which the
reverse of the first `i` steps satisfies `P q` and the steps after the `i`-th satisfy `Q q` are
counted by independent factors. -/
theorem card_filter_splitWalk (i : Fin t) (P : V × D → (Fin i → D) → Prop)
    (Q : V × D → (Fin (t - (i + 1)) → D) → Prop) [∀ q, DecidablePred (P q)]
    [∀ q, DecidablePred (Q q)] :
    #{p : V × (Fin t → D) | P (G.walkDart p i) ((G.pow i).rot (p.1, Fin.take i i.isLt.le p.2)).2 ∧
        Q (G.walkDart p i) (G.walkDrop p (i + 1)).2} =
      ∑ q, #{r | P q r} * #{s | Q q s} := by
  simp only [card_filter]
  refine (Fintype.sum_equiv (G.splitWalk i) _
    (fun x ↦ if P x.1 x.2.1 ∧ Q x.1 x.2.2 then 1 else 0) fun _ ↦ rfl).trans ?_
  simp only [Fintype.sum_prod_type, sum_mul_sum, ite_zero_mul_ite_zero, mul_one]

end Split

section Dart

variable [Fintype V] [Fintype D]

/-- **Each step of a walk is a uniform dart** (counting form): summing a function of the `i`-th dart
over the walks of length `t` sums it `|D| ^ (t - 1)` times over the darts, for every dart is the
`i`-th dart of `|D| ^ (t - 1)` walks. -/
theorem sum_walkDart {M : Type*} [AddCommMonoid M] (i : Fin t) (f : V × D → M) :
    ∑ p : V × (Fin t → D), f (G.walkDart p i) = Fintype.card D ^ (t - 1) • ∑ q, f q := by
  rw [Fintype.sum_equiv (G.splitWalk i) (fun p ↦ f (G.walkDart p i)) (fun x ↦ f x.1) fun _ ↦ rfl,
    Fintype.sum_prod_type]
  simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_pi, prod_const, card_univ,
    Fintype.card_fin, ← pow_add]
  rw [← smul_sum, show (i : ℕ) + (t - (i + 1)) = t - 1 by have := i.isLt; omega]

/-- **Each step of a uniformly random walk is a uniformly random dart.** -/
theorem expect_walkDart {M : Type*} [AddCommMonoid M] [Module ℚ≥0 M] (i : Fin t)
    (f : V × D → M) : 𝔼 p : V × (Fin t → D), f (G.walkDart p i) = 𝔼 q, f q := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have : IsEmpty (Fin t → D) := ⟨fun k ↦ hD.false (k i)⟩
    simp
  · rw [Fintype.expect_equiv (G.splitWalk i) (fun p ↦ f (G.walkDart p i)) (fun x ↦ f x.1)
      fun _ ↦ rfl, Fintype.expect_prod_type]
    simp only [Fintype.expect_const]

/-- The walks of length `t` whose `i`-th dart lies in `S` number `|D| ^ (t - 1) * |S|`. -/
theorem card_filter_walkDart_mem [DecidableEq V] [DecidableEq D] (i : Fin t)
    (S : Finset (V × D)) :
    #{p : V × (Fin t → D) | G.walkDart p i ∈ S} = Fintype.card D ^ (t - 1) * #S := by
  rw [card_filter, G.sum_walkDart i fun q ↦ if q ∈ S then 1 else 0, sum_boole,
    filter_mem_eq_inter, univ_inter, smul_eq_mul, Nat.cast_id]

/-- Every dart is the `i`-th dart of `|D| ^ (t - 1)` walks of length `t`. -/
theorem card_filter_walkDart_eq [DecidableEq V] [DecidableEq D] (i : Fin t) (q : V × D) :
    #{p : V × (Fin t → D) | G.walkDart p i = q} = Fintype.card D ^ (t - 1) := by
  simpa using G.card_filter_walkDart_mem i {q}

end Dart

section Correlation

variable [Fintype D]

/-- From a fixed start `v`, the `i`-th dart of a uniformly random walk leaves the vertex reached by
the random walk after `i` steps along a uniformly random label: the average of `f` over it is
`(G.walk ^ i) (fun w ↦ 𝔼 a, f (w, a)) v`. -/
theorem expect_walkDart_mk (v : V) (i : Fin t) (f : V × D → ℝ) :
    𝔼 k : Fin t → D, f (G.walkDart (v, k) i) = (G.walk ^ (i : ℕ)) (fun w ↦ 𝔼 a, f (w, a)) v := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have : IsEmpty (Fin t → D) := ⟨fun k ↦ hD.false (k i)⟩
    simp only [univ_eq_empty, expect_empty]
    exact (congrFun (map_zero (G.walk ^ (i : ℕ))) v).symm
  induction t generalizing v with
  | zero => exact i.elim0
  | succ t ih =>
    -- a tuple of `t + 1` labels is a first label and a tuple of `t` labels
    rw [Fin.expect_univ_cons]
    induction i using Fin.cases with
    | zero =>
      simp only [walkDart, Fin.val_zero, walkAt_zero, Fin.cons_zero, Fintype.expect_const,
        pow_zero, one_apply_eq_self]
    | succ i =>
      simp only [walkDart_cons_succ, ih, Fin.val_succ, pow_succ', mul_apply_eq_comp, walk_apply]

variable [Fintype V]

/-- **Two darts of a random walk.** For steps `i < j` of a uniformly random walk, the correlation of
`f` at the `i`-th dart with `g` at the `j`-th dart is the correlation, along `j - (i + 1)` steps of
the random walk, of the average `𝔼 a, f (G.rot (v, a))` of `f` over the darts into a vertex `v` with
the average `𝔼 a, g (w, a)` of `g` over the darts out of a vertex `w`. -/
theorem expect_walkDart_mul_walkDart {i j : Fin t} (hij : i < j) (f g : V × D → ℝ) :
    𝔼 p : V × (Fin t → D), f (G.walkDart p i) * g (G.walkDart p j) =
      𝔼 v, (𝔼 a, f (G.rot (v, a))) * (G.walk ^ (j - (i + 1) : ℕ)) (fun w ↦ 𝔼 a, g (w, a)) v := by
  have hj : (j : ℕ) - (i + 1) < t - (i + 1) := by have := j.isLt; omega
  rcases isEmpty_or_nonempty D with hD | hD
  · have : IsEmpty (Fin t → D) := ⟨fun k ↦ hD.false (k i)⟩
    simp
  -- the `j`-th dart is a dart of the walk after the `i`-th step
  have h (p : V × (Fin t → D)) : f (G.walkDart p i) * g (G.walkDart p j) =
      f (G.splitWalk i p).1 *
        g (G.walkDart ((G.rot (G.splitWalk i p).1).1, (G.splitWalk i p).2.2) ⟨_, hj⟩) := by
    rw [splitWalk_apply, fst_rot_walkDart, ← walkDrop_fst, Prod.mk.eta, walkDart_walkDrop]
    congr 3
    ext
    simp only
    omega
  simp only [h]
  rw [G.expect_splitWalk i fun x ↦ f x.1 * g (G.walkDart ((G.rot x.1).1, x.2.2) ⟨_, hj⟩)]
  simp only [Fintype.expect_const, ← mul_expect, expect_walkDart_mk]
  rw [← G.expect_comp_rot, Fintype.expect_prod_type]
  simp only [rot_rot, expect_mul]

/-- **Two darts of a random walk are almost independent.** For steps `i < j` of a uniformly random
walk, the correlation of `f` at the `i`-th dart with `g` at the `j`-th dart differs from the product
of their averages over the darts by at most `λ(G) ^ (j - (i + 1))` times their standard deviations.
Squared: the square of the difference is at most `λ(G) ^ (2 (j - (i + 1)))` times the product of the
variances `𝔼 f² - (𝔼 f)²` and `𝔼 g² - (𝔼 g)²`. -/
theorem sq_expect_walkDart_mul_walkDart_sub_le {i j : Fin t} (hij : i < j) (f g : V × D → ℝ) :
    (𝔼 p : V × (Fin t → D), f (G.walkDart p i) * g (G.walkDart p j) - (𝔼 q, f q) * 𝔼 q, g q) ^ 2 ≤
      G.spectralExpansion ^ (2 * (j - (i + 1) : ℕ)) * (𝔼 q, f q ^ 2 - (𝔼 q, f q) ^ 2) *
        (𝔼 q, g q ^ 2 - (𝔼 q, g q) ^ 2) := by
  rcases isEmpty_or_nonempty D with hD | hD
  · have : IsEmpty (Fin t → D) := ⟨fun k ↦ hD.false (k i)⟩
    simp
  set φ : V → ℝ := fun v ↦ 𝔼 a, f (G.rot (v, a))
  set ψ : V → ℝ := fun w ↦ 𝔼 a, g (w, a)
  have hφ : 𝔼 v, φ v = 𝔼 q, f q := by
    rw [← G.expect_comp_rot f, Fintype.expect_prod_type]
  have hψ : 𝔼 w, ψ w = 𝔼 q, g q := (Fintype.expect_prod_type g).symm
  have hφ₂ : 𝔼 v, φ v ^ 2 ≤ 𝔼 q, f q ^ 2 := by
    rw [← G.expect_comp_rot fun q ↦ f q ^ 2, Fintype.expect_prod_type]
    exact expect_le_expect fun v _ ↦ sq_expect_le_expect_sq _ _
  have hψ₂ : 𝔼 w, ψ w ^ 2 ≤ 𝔼 q, g q ^ 2 := by
    rw [Fintype.expect_prod_type fun q ↦ g q ^ 2]
    exact expect_le_expect fun v _ ↦ sq_expect_le_expect_sq _ _
  have hmix := G.sq_expect_mul_walk_pow_sub_le (j - (i + 1)) φ ψ
  rw [hφ, hψ] at hmix
  rw [G.expect_walkDart_mul_walkDart hij]
  refine hmix.trans ?_
  have := G.spectralExpansion_nonneg
  have h₂ : 0 ≤ 𝔼 w, ψ w ^ 2 - (𝔼 q, g q) ^ 2 := hψ ▸ sub_nonneg.2 (sq_expect_le_expect_sq _ ψ)
  have h₃ : 0 ≤ 𝔼 q, f q ^ 2 - (𝔼 q, f q) ^ 2 := sub_nonneg.2 (sq_expect_le_expect_sq _ f)
  gcongr

/-- **Two darts of a random walk are almost independent**: for steps `i < j` of a uniformly random
walk, the correlation of `f` at the `i`-th dart with `f` at the `j`-th dart differs from the square
of its average over the darts by at most `λ(G) ^ (j - (i + 1))` times its variance. -/
theorem abs_expect_walkDart_mul_walkDart_sub_le {i j : Fin t} (hij : i < j) (f : V × D → ℝ) :
    |𝔼 p : V × (Fin t → D), f (G.walkDart p i) * f (G.walkDart p j) - (𝔼 q, f q) ^ 2| ≤
      G.spectralExpansion ^ (j - (i + 1) : ℕ) * (𝔼 q, f q ^ 2 - (𝔼 q, f q) ^ 2) := by
  have := G.spectralExpansion_nonneg
  have hf : 0 ≤ 𝔼 q, f q ^ 2 - (𝔼 q, f q) ^ 2 := sub_nonneg.2 (sq_expect_le_expect_sq _ f)
  refine abs_le_of_sq_le_sq ?_ (by positivity)
  calc _ = (𝔼 p : V × (Fin t → D), f (G.walkDart p i) * f (G.walkDart p j) -
        (𝔼 q, f q) * 𝔼 q, f q) ^ 2 := by rw [sq (𝔼 q, f q)]
    _ ≤ _ := G.sq_expect_walkDart_mul_walkDart_sub_le hij f f
    _ = _ := by ring

end Correlation

end Cslib.RotationMap
