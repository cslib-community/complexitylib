/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.PPoly
public import Complexity.Computability.Circuit.Boolean.Substitution
public import Complexity.Computability.Circuit.Boolean.AtLeast
public import Complexity.Computability.Circuit.Complexity
public import Complexity.Foundations.Combinatorics.MajorityVote

/-!
# Randomness does not help polynomial-size circuits

Let `F` be a Boolean function of `n + p` variables, read as `F (x ++ r)` for an input `x` and a
random string `r`. If, for every `x`, at least two thirds of the random strings give the answer
`g x`, then `g` has circuits of size `O(n (C(F) + n))`, where `C(F)` is the circuit complexity of
`F` (Adleman's theorem in circuit form, [Arora and Barak, Theorem 7.14][AroraBarak09]): take
`12 (n + 1)` random strings that make the majority right for all `2 ^ n` inputs at once
(`Cslib.exists_forall_lt_card_filter_mem`), and hardwire them. For one-sided error, `n + 1` random
strings and their disjunction suffice. Applied at every length, bounded-error randomness over a
family of polynomial-size circuits stays in `P/poly`.

## Main results

* `Cslib.Circuits.Boolean.complexity_le_of_boundedError`,
  `Cslib.Circuits.Boolean.complexity_le_of_oneSidedError`: one input length.
* `Cslib.Circuits.Boolean.PPoly.of_boundedError`, `Cslib.Circuits.Boolean.PPoly.of_oneSidedError`:
  all input lengths.
* `Cslib.Circuits.Boolean.PPoly.exists_of_boundedError`,
  `Cslib.Circuits.Boolean.PPoly.exists_of_oneSidedError`: the same with a promise, on chosen sets
  of inputs, as needed for problems with an arbitrary encoding.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 7.5][AroraBarak09]
* [L. Adleman, *Two theorems on random polynomial time*][Adleman1978]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n p : ℕ}

/-- If `g` is a threshold of copies of `F` with hardwired random strings, its complexity is at
most that of the copies and of the threshold. -/
private theorem complexity_le_of_eq_threshold {m j : ℕ} (F : BooleanFunction (n + p))
    (g : BooleanFunction n) (ω : Fin m → Fin p → Bool)
    (h : ∀ x, g x = threshold m j fun i => F (Fin.append x (ω i))) :
    complexity interpretation (single g) ≤
      m * (complexity interpretation (single F) + 2) + (2 + m * (2 * (m + 2))) := by
  let f : Fin m → BooleanFunction n := fun i x => F (substitute (appendInputs (ω i)) x)
  have hg : single g = single (threshold m j) ∘ fun x i => f i x :=
    funext fun x => funext fun _ => by simp [f, h x, single]
  rw [hg]
  refine (complexity_comp_le _ _).trans (add_le_add ((complexity_pi_le f).trans ?_)
    (complexity_threshold_le m j))
  calc ∑ i, complexity interpretation (single (f i))
      ≤ ∑ _i : Fin m, (complexity interpretation (single F) + 2) :=
        sum_le_sum fun i _ => complexity_substitute_le _ _
    _ = m * (complexity interpretation (single F) + 2) := by
        rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Adleman's theorem**, for one input length, on a set of inputs. If, for every `x ∈ S`, at
least two thirds of the random strings `r` have `F (x ++ r) = g x`, then some function agreeing
with `g` on `S` has circuits of size `O(n (C(F) + n))`. -/
theorem exists_complexity_le_of_boundedError (S : Set (Fin n → Bool))
    (F : BooleanFunction (n + p)) (g : BooleanFunction n)
    (h : ∀ x ∈ S, 2 * 2 ^ p ≤
      3 * (univ.filter fun r : Fin p → Bool => F (Fin.append x r) = g x).card) :
    ∃ g' : BooleanFunction n, (∀ x ∈ S, g' x = g x) ∧
      complexity interpretation (single g') ≤
        (12 * n + 12) * (complexity interpretation (single F) + 2) +
          (2 + (12 * n + 12) * (2 * (12 * n + 12 + 2))) := by
  classical
  set R := 6 * n + 6 with hR
  obtain ⟨ω, hω⟩ := Cslib.exists_forall_lt_card_filter_mem (X := S) (n := n)
    ((Fintype.card_subtype_le _).trans (by simp))
    (fun x => univ.filter fun r => F (Fin.append x.1 r) = g x.1)
    fun x => by simpa [Fintype.card_fun] using h x.1 x.2
  refine ⟨fun x => threshold (2 * R) (R + 1) fun i => F (Fin.append x (ω i)), fun x hx => ?_,
    (complexity_le_of_eq_threshold F _ ω fun _ => rfl).trans_eq
      (by rw [show 2 * R = 12 * n + 12 by omega])⟩
  have hc := hω ⟨x, hx⟩
  simp only at hc
  change threshold _ _ (fun i => F (Fin.append x (ω i))) = g x
  rw [threshold_apply, BitString.weight, Bool.eq_iff_iff, decide_eq_true_iff]
  cases hgx : g x
  · have e : (univ.filter fun i => F (Fin.append x (ω i)) = true) =
        univ \ univ.filter fun i => ω i ∈ univ.filter fun r => F (Fin.append x r) = g x := by
      ext i
      simp [hgx]
    rw [e, card_univ_sdiff, Fintype.card_fin]
    simp only [Bool.false_eq_true, iff_false, not_le]
    omega
  · have e : (univ.filter fun i => F (Fin.append x (ω i)) = true) =
        univ.filter fun i => ω i ∈ univ.filter fun r => F (Fin.append x r) = g x := by
      ext i
      simp [hgx]
    rw [e]
    simpa using hc

/-- **Adleman's theorem**, for one input length. If, for every `x`, at least two thirds of the
random strings `r` have `F (x ++ r) = g x`, then `g` has circuits of size
`O(n (C(F) + n))`. -/
theorem complexity_le_of_boundedError (F : BooleanFunction (n + p)) (g : BooleanFunction n)
    (h : ∀ x, 2 * 2 ^ p ≤ 3 * (univ.filter fun r : Fin p → Bool => F (Fin.append x r) = g x).card) :
    complexity interpretation (single g) ≤
      (12 * n + 12) * (complexity interpretation (single F) + 2) +
        (2 + (12 * n + 12) * (2 * (12 * n + 12 + 2))) := by
  obtain ⟨g', hg', hc⟩ := exists_complexity_le_of_boundedError Set.univ F g fun x _ => h x
  rwa [show g' = g from funext fun x => hg' x trivial] at hc

/-- **Adleman's theorem for one-sided error**, for one input length, on a set of inputs. If, for
every `x ∈ S` with `g x = true`, at least half of the random strings `r` have `F (x ++ r) = true`,
and for every `x ∈ S` with `g x = false` none has, then some function agreeing with `g` on `S` has
circuits of size `O(n (C(F) + n))`. -/
theorem exists_complexity_le_of_oneSidedError (S : Set (Fin n → Bool))
    (F : BooleanFunction (n + p)) (g : BooleanFunction n)
    (h₁ : ∀ x ∈ S, g x = true →
      2 ^ p ≤ 2 * (univ.filter fun r : Fin p → Bool => F (Fin.append x r) = true).card)
    (h₂ : ∀ x ∈ S, g x = false → ∀ r, F (Fin.append x r) = false) :
    ∃ g' : BooleanFunction n, (∀ x ∈ S, g' x = g x) ∧
      complexity interpretation (single g') ≤
        (n + 1) * (complexity interpretation (single F) + 2) +
          (2 + (n + 1) * (2 * (n + 1 + 2))) := by
  classical
  let good : S → Finset (Fin p → Bool) := fun x =>
    if g x.1 = true then univ.filter fun r => F (Fin.append x.1 r) = true else univ
  obtain ⟨ω, hω⟩ := Cslib.exists_forall_exists_apply_mem (X := S) (n := n)
    ((Fintype.card_subtype_le _).trans (by simp)) good fun x => by
      rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      by_cases hx : g x.1 = true
      · simpa [good, hx] using h₁ x.1 x.2 hx
      · rw [show good x = univ from ite_eq_right hx, card_univ, Fintype.card_fun,
          Fintype.card_bool, Fintype.card_fin]
        omega
  refine ⟨fun x => threshold (n + 1) 1 fun i => F (Fin.append x (ω i)), fun x hx => ?_,
    complexity_le_of_eq_threshold F _ ω fun _ => rfl⟩
  change threshold _ _ (fun i => F (Fin.append x (ω i))) = g x
  rw [threshold_apply, BitString.weight, Bool.eq_iff_iff, decide_eq_true_iff,
    Nat.one_le_iff_ne_zero, Ne,
    card_eq_zero, filter_eq_empty_iff]
  push Not
  constructor
  · rintro ⟨i, -, hi⟩
    by_contra hgx
    rw [h₂ x hx (by simpa using hgx) (ω i)] at hi
    exact Bool.noConfusion hi
  · intro hgx
    obtain ⟨i, hi⟩ := hω ⟨x, hx⟩
    simp only [good, hgx, ite_true, mem_filter, mem_univ, true_and] at hi
    exact ⟨i, mem_univ _, hi⟩

/-- **Adleman's theorem for one-sided error**, for one input length. If, for every `x` with
`g x = true`, at least half of the random strings `r` have `F (x ++ r) = true`, and for every `x`
with `g x = false` none has, then `g` has circuits of size `O(n (C(F) + n))`. -/
theorem complexity_le_of_oneSidedError (F : BooleanFunction (n + p)) (g : BooleanFunction n)
    (h₁ : ∀ x, g x = true →
      2 ^ p ≤ 2 * (univ.filter fun r : Fin p → Bool => F (Fin.append x r) = true).card)
    (h₂ : ∀ x, g x = false → ∀ r, F (Fin.append x r) = false) :
    complexity interpretation (single g) ≤
      (n + 1) * (complexity interpretation (single F) + 2) + (2 + (n + 1) * (2 * (n + 1 + 2))) := by
  obtain ⟨g', hg', hc⟩ := exists_complexity_le_of_oneSidedError Set.univ F g
    (fun x _ => h₁ x) fun x _ => h₂ x
  rwa [show g' = g from funext fun x => hg' x trivial] at hc

/-- **Adleman's theorem**, on sets of inputs. If `F n` is a family of functions of `n + p n`
variables with circuits of polynomial size, and for every input `x ∈ S n` at least two thirds of the
random strings `r` have `F n (x ++ r) = g n x`, then some language in `P/poly` agrees with `g` on
the sets `S n`. -/
theorem PPoly.exists_of_boundedError {p : ℕ → ℕ} (F : ∀ n, BooleanFunction (n + p n))
    (hF : PolynomiallyBounded fun n => complexity interpretation (single (F n)))
    (S : ∀ n, Set (Fin n → Bool)) (g : ∀ n, BooleanFunction n)
    (h : ∀ n, ∀ x ∈ S n, 2 * 2 ^ p n ≤
      3 * (univ.filter fun r : Fin (p n) → Bool => F n (Fin.append x r) = g n x).card) :
    ∃ L ∈ PPoly, ∀ n, ∀ x ∈ S n, L.slice n x = g n x := by
  choose g' hg' hc using fun n => exists_complexity_le_of_boundedError (S n) (F n) (g n) (h n)
  refine ⟨Language.ofSlices g', ?_, fun n x hx => by rw [Language.slice_ofSlices, hg' n x hx]⟩
  set q := fun n => complexity interpretation (single (F n)) with hq
  have : PolynomiallyBounded q := hF
  refine PolynomiallyBounded.mono_of_le
    (g := fun n => (12 * n + 12) * (q n + 2) + (2 + (12 * n + 12) * (2 * (12 * n + 12 + 2))))
    (by fun_prop) fun n => ?_
  simpa only [Language.slice_ofSlices] using hc n

/-- **Adleman's theorem.** If `F n` is a family of functions of `n + p n` variables with circuits
of polynomial size, and for every input `x` of every length `n` at least two thirds of the random
strings `r` have `F n (x ++ r) = A.slice n x`, then `A ∈ P/poly`. -/
theorem PPoly.of_boundedError {A : Language Bool} {p : ℕ → ℕ}
    (F : ∀ n, BooleanFunction (n + p n))
    (hF : PolynomiallyBounded fun n => complexity interpretation (single (F n)))
    (h : ∀ n x, 2 * 2 ^ p n ≤
      3 * (univ.filter fun r : Fin (p n) → Bool => F n (Fin.append x r) = A.slice n x).card) :
    A ∈ PPoly := by
  obtain ⟨L, hL, hLA⟩ := PPoly.exists_of_boundedError F hF (fun _ => Set.univ) (fun n => A.slice n)
    fun n x _ => h n x
  have e : ∀ n, A.slice n = L.slice n := fun n => funext fun x => (hLA n x trivial).symm
  rw [mem_PPoly] at hL ⊢
  simpa only [e] using hL

/-- **Adleman's theorem for one-sided error**, on sets of inputs. -/
theorem PPoly.exists_of_oneSidedError {p : ℕ → ℕ} (F : ∀ n, BooleanFunction (n + p n))
    (hF : PolynomiallyBounded fun n => complexity interpretation (single (F n)))
    (S : ∀ n, Set (Fin n → Bool)) (g : ∀ n, BooleanFunction n)
    (h₁ : ∀ n, ∀ x ∈ S n, g n x = true →
      2 ^ p n ≤ 2 * (univ.filter fun r : Fin (p n) → Bool => F n (Fin.append x r) = true).card)
    (h₂ : ∀ n, ∀ x ∈ S n, g n x = false → ∀ r, F n (Fin.append x r) = false) :
    ∃ L ∈ PPoly, ∀ n, ∀ x ∈ S n, L.slice n x = g n x := by
  choose g' hg' hc using fun n =>
    exists_complexity_le_of_oneSidedError (S n) (F n) (g n) (h₁ n) (h₂ n)
  refine ⟨Language.ofSlices g', ?_, fun n x hx => by rw [Language.slice_ofSlices, hg' n x hx]⟩
  set q := fun n => complexity interpretation (single (F n)) with hq
  have : PolynomiallyBounded q := hF
  refine PolynomiallyBounded.mono_of_le
    (g := fun n => (n + 1) * (q n + 2) + (2 + (n + 1) * (2 * (n + 1 + 2))))
    (by fun_prop) fun n => ?_
  simpa only [Language.slice_ofSlices] using hc n

/-- **Adleman's theorem for one-sided error.** If `F n` is a family of functions of `n + p n`
variables with circuits of polynomial size, every input `x ∈ A` has `F n (x ++ r) = true` for at
least half of the random strings `r`, and no `x ∉ A` has it for any `r`, then `A ∈ P/poly`. -/
theorem PPoly.of_oneSidedError {A : Language Bool} {p : ℕ → ℕ}
    (F : ∀ n, BooleanFunction (n + p n))
    (hF : PolynomiallyBounded fun n => complexity interpretation (single (F n)))
    (h₁ : ∀ n x, A.slice n x = true →
      2 ^ p n ≤ 2 * (univ.filter fun r : Fin (p n) → Bool => F n (Fin.append x r) = true).card)
    (h₂ : ∀ n x, A.slice n x = false → ∀ r, F n (Fin.append x r) = false) :
    A ∈ PPoly := by
  obtain ⟨L, hL, hLA⟩ := PPoly.exists_of_oneSidedError F hF (fun _ => Set.univ)
    (fun n => A.slice n) (fun n x _ => h₁ n x) fun n x _ => h₂ n x
  have e : ∀ n, A.slice n = L.slice n := fun n => funext fun x => (hLA n x trivial).symm
  rw [mem_PPoly] at hL ⊢
  simpa only [e] using hL

end Cslib.Circuits.Boolean
