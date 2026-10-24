/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.RepeatedTrials
public import Complexity.Foundations.Order.BooleanSubalgebra
import Complexity.Computability.Complexity.Classes.SharpP
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.BitString.WordCount
import Complexity.Foundations.Data.List.OfFn

/-!
# Error reduction for BPP

The error `1 / 3` in the definition of `BPP` (`Cslib.Complexity.BPP`) can be made exponentially
small [Arora and Barak, Section 7.4.1][AroraBarak09]. Cut the random string into `2 r(n)` blocks of
`p(n)` bits, where `n` is the length of the encoded instance, run the bounded-error decider on
every block and accept when a strict majority, more than `r(n)`, of the runs accept
(`Cslib.Complexity.repeatMajority`). The answer is wrong only when at most half of the runs are
right, which happens on at most an `(8 / 9) ^ r(n)` fraction of the random strings
(`Cslib.card_filter_card_filter_le_le`, an exponential-moment bound). Since `2 * 8 ^ 6 < 9 ^ 6`,
`r = 6 q` runs make the error at most `2 ^ (-q(n))`.

The condition `Cslib.Complexity.DecidesWithErrorExponent enc q p V A` says that `V` errs on at most
a `2 ^ (-q(n))` fraction of the random strings. A problem is in `BPP` exactly when it is decided
in polynomial time with error at most `2 ^ (-q(n))` for every polynomial `q`
(`Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`). The one-sided version for `RP`
is `Cslib.Complexity.mem_RP_iff_forall_decidesWithOneSidedErrorExponent`.

## Main definitions

* `Cslib.Complexity.DecidesWithErrorExponent`: error at most `2 ^ (-q(n))`.
* `Cslib.Complexity.BPP.booleanSubalgebra`: `BPP` as a Boolean subalgebra of `Set α`.

## Main results

* `Cslib.Complexity.DecidesWithBoundedError.repeatMajority`: `12 q(n)` majority votes reduce the
  error to `2 ^ (-q(n))`.
* `Cslib.Complexity.DecidesWithErrorExponent.decidesWithBoundedError`: error at most
  `2 ^ (-q(n)) ≤ 1 / 4` is bounded error.
* `Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`: error reduction for `BPP`.
* `Cslib.Complexity.inter_mem_BPP`, `Cslib.Complexity.union_mem_BPP`,
  `Cslib.Complexity.diff_mem_BPP`, `Cslib.Complexity.symmDiff_mem_BPP`: Boolean closure of `BPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- `V` decides `A` with error at most `2 ^ (-q(n))`, using random strings whose length is `p`
evaluated at the length `n` of the encoded instance: for every instance `a`, the random strings `r`
giving the wrong answer, `V (a, r) = false` for members of `A` and `V (a, r) = true` for the
others, make up at most a `2 ^ (-q(n))` fraction. -/
def DecidesWithErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ q.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = false).card ≤ 2 ^ p.eval (enc a).length) ∧
    (a ∉ A → 2 ^ q.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).card ≤ 2 ^ p.eval (enc a).length)

variable {enc : α ↪ List Bool}

/-- **Error reduction for `BPP`** [Arora and Barak, Section 7.4.1][AroraBarak09]. The strict
majority of `12 q(n)` runs of a bounded-error decider, on independent blocks of random bits, errs on
at most a `2 ^ (-q(n))` fraction of the random strings. -/
theorem DecidesWithBoundedError.repeatMajority {p : Polynomial ℕ} {V : α × List Bool → Bool}
    {A : Set α} (h : DecidesWithBoundedError enc p V A) (q : Polynomial ℕ) :
    DecidesWithErrorExponent enc q (12 * q * p) (Complexity.repeatMajority enc (6 * q) p V) A := by
  intro a
  have hlen : (12 * q * p).eval (enc a).length =
      2 * (6 * q).eval (enc a).length * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  have hR : (6 * q).eval (enc a).length = 6 * q.eval (enc a).length := by simp
  rw [hlen]
  constructor
  · -- on a member, the majority rejects only when at most `R` runs accept
    intro ha
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => V (a, List.ofFn s) = true) ((h a).1 ha))
    rw [mem_filter, repeatMajority_ofFn, decide_eq_false_iff_not, not_lt] at hx
    exact mem_filter.2 ⟨mem_univ _, hx.2⟩
  · -- on a non-member, the majority accepts only when at most `R` runs reject
    intro ha
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => V (a, List.ofFn s) = false) ((h a).2 ha))
    rw [mem_filter, repeatMajority_ofFn, decide_eq_true_iff] at hx
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 *
      (6 * q).eval (enc a).length))))
      fun i => V (a, List.ofFn (BitString.block x i)) = true
    simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hsum
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    omega

/-- Error at most `2 ^ (-q(n)) ≤ 1 / 4` is bounded error. -/
theorem DecidesWithErrorExponent.decidesWithBoundedError {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} {A : Set α} (h : DecidesWithErrorExponent enc q p V A)
    (hq : ∀ n, 2 ≤ q.eval n) : DecidesWithBoundedError enc p V A := fun a => by
  have hsum := acceptCount_add_card_filter_eq_false (V := V) (a := a) (n := p.eval (enc a).length)
  have h4 : 2 ^ 2 ≤ 2 ^ q.eval (enc a).length := Nat.pow_le_pow_right (by norm_num) (hq _)
  rw [← acceptCount]
  constructor
  · intro ha
    have := (Nat.mul_le_mul_right _ h4).trans ((h a).1 ha)
    omega
  · intro ha
    have := (Nat.mul_le_mul_right _ h4).trans ((h a).2 ha)
    rw [← acceptCount] at this
    omega

/-- **Error reduction for `BPP`** [Arora and Barak, Section 7.4.1][AroraBarak09]: a problem is in
`BPP` exactly when, for every polynomial `q`, it is decided in polynomial time with error at most
`2 ^ (-q(n))`. -/
theorem mem_BPP_iff_forall_decidesWithErrorExponent {A : Set α} :
    A ∈ BPP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithErrorExponent enc q p V A := by
  have this : A ∈ BPP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧ DecidesWithErrorExponent enc q p
      V A := by
    rw [mem_BPP]
    refine ⟨fun ⟨p, V, hV, h⟩ q => ⟨12 * q * p, _,
      (computableInPolyTime_repeatMajority hV _ _).tidy, h.repeatMajority q⟩, fun h => ?_⟩
    obtain ⟨p, V, hV, h⟩ := h 2
    exact ⟨p, V, (.of_tidy hV), h.decidesWithBoundedError fun _ => by simp⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-! ### Boolean closure of `BPP` -/

open scoped symmDiff

/-- **`BPP` is closed under intersection**: reduce the error of both deciders to
`2 ^ (-3) = 1 / 8`, and accept when both accept on disjoint parts of the random string. -/
theorem inter_mem_BPP {A B : Set α} (hA : A ∈ BPP enc) (hB : B ∈ BPP enc) : A ∩ B ∈ BPP enc := by
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.1 hA 3
  obtain ⟨p₂, V₂, hV₂, h₂⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.1 hB 3
  refine mem_BPP.2 ⟨p₁ + p₂, andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂,
    by fun_prop, fun a => ?_⟩
  have hs₁ := acceptCount_add_card_filter_eq_false (V := V₁) (a := a)
    (n := p₁.eval (enc a).length)
  have hs₂ := acceptCount_add_card_filter_eq_false (V := V₂) (a := a)
    (n := p₂.eval (enc a).length)
  have hs := acceptCount_add_card_filter_eq_false
    (V := andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂) (a := a)
    (n := (p₁ + p₂).eval (enc a).length)
  have hc : acceptCount (andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂) a
      ((p₁ + p₂).eval (enc a).length) =
      acceptCount V₁ a (p₁.eval (enc a).length) * acceptCount V₂ a (p₂.eval (enc a).length) := by
    rw [Polynomial.eval_add, acceptCount_andVerifier]
  constructor
  · intro ha
    have e₁ := (h₁ a).1 ha.1
    have e₂ := (h₂ a).1 ha.2
    simp only [Polynomial.eval_ofNat] at e₁ e₂
    have f₁ : 7 * 2 ^ p₁.eval (enc a).length ≤ 8 * acceptCount V₁ a (p₁.eval (enc a).length) := by
      omega
    have f₂ : 7 * 2 ^ p₂.eval (enc a).length ≤ 8 * acceptCount V₂ a (p₂.eval (enc a).length) := by
      omega
    rw [← acceptCount, hc, Polynomial.eval_add, pow_add]
    nlinarith [Nat.mul_le_mul f₁ f₂]
  · intro ha
    have hacc : 8 * acceptCount (andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂) a
        ((p₁ + p₂).eval (enc a).length) ≤ 2 ^ (p₁ + p₂).eval (enc a).length := by
      rw [hc, Polynomial.eval_add, pow_add]
      by_cases ha₁ : a ∈ A
      · have ha₂ : a ∉ B := fun hb => ha ⟨ha₁, hb⟩
        have e₂ := (h₂ a).2 ha₂
        simp only [Polynomial.eval_ofNat] at e₂
        rw [← acceptCount] at e₂
        have hb₁ := acceptCount_le_two_pow (V := V₁) (a := a) (n := p₁.eval (enc a).length)
        nlinarith [Nat.mul_le_mul hb₁ e₂]
      · have e₁ := (h₁ a).2 ha₁
        simp only [Polynomial.eval_ofNat] at e₁
        rw [← acceptCount] at e₁
        have hb₂ := acceptCount_le_two_pow (V := V₂) (a := a) (n := p₂.eval (enc a).length)
        nlinarith [Nat.mul_le_mul e₁ hb₂]
    omega

/-- `BPP` as a Boolean subalgebra of `Set α`. -/
def BPP.booleanSubalgebra (enc : α ↪ List Bool) : BooleanSubalgebra (Set α) :=
  .ofComplInf (BPP enc) (P_subset_BPP empty_mem_P) (fun _ => compl_mem_BPP)
    (fun _ _ => inter_mem_BPP)

@[simp]
theorem BPP.coe_booleanSubalgebra : (BPP.booleanSubalgebra enc : Set (Set α)) = BPP enc := rfl

@[simp]
theorem BPP.mem_booleanSubalgebra {A : Set α} :
    A ∈ BPP.booleanSubalgebra enc ↔ A ∈ BPP enc := Iff.rfl

/-- `BPP` is closed under union. -/
theorem union_mem_BPP {A B : Set α} (hA : A ∈ BPP enc) (hB : B ∈ BPP enc) : A ∪ B ∈ BPP enc :=
  (BPP.booleanSubalgebra enc).sup_mem hA hB

/-- `BPP` is closed under set difference. -/
theorem diff_mem_BPP {A B : Set α} (hA : A ∈ BPP enc) (hB : B ∈ BPP enc) : A \ B ∈ BPP enc :=
  (BPP.booleanSubalgebra enc).sdiff_mem hA hB

/-- `BPP` is closed under symmetric difference. -/
theorem symmDiff_mem_BPP {A B : Set α} (hA : A ∈ BPP enc) (hB : B ∈ BPP enc) : A ∆ B ∈ BPP enc :=
  (BPP.booleanSubalgebra enc).symmDiff_mem hA hB

end Cslib.Complexity
