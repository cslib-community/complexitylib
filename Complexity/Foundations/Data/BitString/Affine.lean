/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Init
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.Ring

/-!
# Affine maps over `𝔽₂`

Over `𝔽₂`, a map between additive groups is *affine* when it preserves sums of three points:
`g (x + y + z) = g x + g y + g z` (`Cslib.BitString.IsAffine`). For maps between `𝔽₂`-vector
spaces this is the usual notion, a translate of a linear map
(`Cslib.BitString.isAffine_iff_exists_affineMap` in
`Complexity/Foundations/Data/BitString/AffineSubspace.lean`).

An affine map from `BitString d` is determined by its values at `0` and at the unit vectors
(`Cslib.BitString.IsAffine.ext_single`), so there are at most `2 ^ (n (d + 1))` affine maps from
`BitString d` to `BitString n` (`Cslib.BitString.card_isAffine_le`).

## Main definitions

* `Cslib.BitString.IsAffine`: affine maps over `𝔽₂`.

## Main results

* `Cslib.BitString.IsAffine.comp`: affine maps compose.
* `Cslib.BitString.isAffine_zeroExtend`: extension by zeros is affine.
* `Cslib.BitString.IsAffine.ext_single`: an affine map from `BitString d` is determined by its
  values at `0` and at the unit vectors.
* `Cslib.BitString.card_isAffine_le`: at most `2 ^ (n (d + 1))` maps from `BitString d` to
  `BitString n` are affine.
* `Cslib.BitString.exists_affine_of_add_add`: a Boolean function satisfying
  `g (u + w) = g u + g w + g 0` and depending only on a finite set `M` is `g u = g 0 + ∑ i ∈ T, u i`
  for some `T ⊆ M`.
* `Cslib.BitString.eq_add_sum_of_step`: prefix sums of a step recurrence `z (j + 1) = z j + f j`
  over `𝔽₂`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*, Definition 2.1][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.BitString

/-- A map is affine over `𝔽₂` when it preserves sums of three points. -/
def IsAffine {α β : Type*} [Add α] [Add β] (g : α → β) : Prop :=
  ∀ x y z, g (x + y + z) = g x + g y + g z

/-- The composition of affine maps is affine. -/
theorem IsAffine.comp {α β γ : Type*} [Add α] [Add β] [Add γ] {g : β → γ} {h : α → β}
    (hg : IsAffine g) (hh : IsAffine h) : IsAffine (g ∘ h) := fun x y z => by
  simp only [Function.comp_apply, hh x y z, hg (h x) (h y) (h z)]

/-- Constant maps into a group in which every element is its own negative (`b + b = 0`) are
affine. -/
theorem isAffine_const {α β : Type*} [Add α] [AddGroup β] (h : ∀ b : β, b + b = 0) (c : β) :
    IsAffine (fun _ : α => c) := fun _ _ _ => by rw [h, zero_add]

/-- Extension by zeros is affine. -/
theorem isAffine_zeroExtend {d d' : ℕ} : IsAffine (zeroExtend (d := d) (d' := d')) := by
  intro x y z
  funext i
  simp only [zeroExtend, Pi.add_apply]
  split_ifs <;> rfl

/-! ### Counting affine maps -/

section Counting

open Finset

/-- Affinity of a map between finite types is decidable. -/
instance {α β : Type*} [Fintype α] [DecidableEq β] [Add α] [Add β] (g : α → β) :
    Decidable (IsAffine g) :=
  inferInstanceAs (Decidable (∀ _ _ _, _))

/-- Affine maps from `BitString d` agreeing at `0` and at the unit vectors are equal. -/
theorem IsAffine.ext_single {d n : ℕ} {g g' : BitString d → BitString n} (hg : IsAffine g)
    (hg' : IsAffine g') (h0 : g 0 = g' 0) (hi : ∀ i, g (Pi.single i true) = g' (Pi.single i true)) :
    g = g' := by
  have key : ∀ s : Finset (Fin d), g (fun i => decide (i ∈ s)) = g' (fun i => decide (i ∈ s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun i : Fin d => decide (i ∈ (∅ : Finset (Fin d)))) = 0 := by
        funext i; simp [Bool.zero_eq_false]
      rw [this, h0]
    | insert j s hj ih =>
      have hsplit : (fun i => decide (i ∈ insert j s)) =
          (fun i => decide (i ∈ s)) + Pi.single j true + 0 := by
        funext i
        by_cases hij : i = j
        · subst hij
          simp only [Finset.mem_insert, true_or, decide_true, hj, decide_false, Pi.single_eq_same,
            Pi.add_apply, Pi.zero_apply, Bool.zero_eq_false]
          rfl
        · simp only [Finset.mem_insert, hij, false_or, Pi.add_apply, Pi.single_eq_of_ne hij,
            Pi.zero_apply, Bool.zero_eq_false]
          cases decide (i ∈ s) <;> rfl
      rw [hsplit, hg, hg', ih, hi, h0]
  funext x
  have hx : x = fun i => decide (i ∈ Finset.univ.filter fun i => x i = true) := by
    funext i; simp
  rw [hx, key]

/-- At most `2 ^ (n (d + 1))` maps from `BitString d` to `BitString n` are affine. -/
theorem card_isAffine_le (d n : ℕ) :
    (univ.filter fun g : BitString d → BitString n => IsAffine g).card ≤ 2 ^ (n * (d + 1)) := by
  classical
  calc _ ≤ (univ : Finset (Option (Fin d) → BitString n)).card :=
        card_le_card_of_injOn (fun g o => g (o.elim 0 fun i => Pi.single i true))
          (fun _ _ => mem_univ _) fun g hg g' hg' h =>
            IsAffine.ext_single (mem_filter.1 hg).2 (mem_filter.1 hg').2 (congrFun h none)
              fun i => congrFun h (some i)
    _ = 2 ^ (n * (d + 1)) := by
      rw [card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_option, Fintype.card_fin,
        Fintype.card_bool, Fintype.card_fin, ← pow_mul]

/-- A function of bits that depends only on the coordinates in `M` and preserves sums of three
points is affine: a constant plus the sum of the coordinates in some `T ⊆ M`. -/
theorem exists_affine_of_add_add {ι : Type*} {M : Finset ι} {g : (ι → Bool) → Bool}
    (hcongr : ∀ u u' : ι → Bool, (∀ j ∈ M, u j = u' j) → g u = g u')
    (hadd : ∀ u u' u'' : ι → Bool, g (u + u' + u'') = g u + g u' + g u'') :
    ∃ T ⊆ M, ∀ u, g u = g 0 + ∑ j ∈ T, u j := by
  classical
  let e : ι → ι → Bool := fun j => Pi.single j true
  have hsum : ∀ A : Finset ι, g (∑ j ∈ A, e j) = g 0 + ∑ j ∈ A, (g (e j) + g 0) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp
    | @insert j A hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      have := hadd (e j) (∑ i ∈ A, e i) 0
      rw [add_zero] at this
      rw [this, ih]
      ring
  refine ⟨M.filter fun j => g (e j) + g 0 = true, Finset.filter_subset _ _, fun u => ?_⟩
  have hu : g u = g (∑ j ∈ M.filter (fun j => u j = true), e j) := by
    apply hcongr
    intro i hi
    rw [Finset.sum_apply, Finset.sum_pi_single]
    simp only [Finset.mem_filter, hi, true_and]
    cases u i <;> rfl
  rw [hu, hsum]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  cases u j <;> cases g (e j) + g 0 <;> rfl

/-- A sequence that starts at `c` and adds `f j` at each step `j < n` holds `c + ∑ j' < j, f j'`
up to step `n`. -/
theorem eq_add_sum_of_step {z f : ℕ → Bool} {c : Bool} {n : ℕ} (h0 : z 0 = c)
    (hstep : ∀ j < n, z (j + 1) = (z j ^^ f j)) :
    ∀ j ≤ n, z j = c + ∑ j' ∈ Finset.range j, f j' := by
  intro j hj
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [hstep j (Nat.lt_of_succ_le hj), ih (Nat.le_of_succ_le hj), Finset.sum_range_succ,
      ← add_assoc]
    rfl

end Counting

end Cslib.BitString
