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

The condition `Cslib.Complexity.PromiseProblem.SolvesWithErrorExponent enc q p V Q` says that `V`
errs on at most a `2 ^ (-q(n))` fraction of the random strings on every instance in the promise of
`Q`; for a decision problem it is `Cslib.Complexity.DecidesWithErrorExponent`. Error reduction is
proved once, for promise problems: a promise problem is in `PromiseBPP` exactly when it is solved in
polynomial time with error at most `2 ^ (-q(n))` for every polynomial `q`
(`Cslib.Complexity.mem_PromiseBPP_iff_forall_solvesWithErrorExponent`), and the statement for
`BPP` is its instance at `PromiseProblem.ofSet A`. The one-sided version for `RP` is
`Cslib.Complexity.mem_PromiseRP_iff_forall_solvesWithOneSidedErrorExponent`.

## Main definitions

* `Cslib.Complexity.ErrorExponentAt`: the per-instance condition that a verifier errs from a
  specified Boolean answer on at most a `2 ^ (-q(n))` fraction of random strings.
* `Cslib.Complexity.PromiseProblem.SolvesWithErrorExponent`: error at most `2 ^ (-q(n))`.
* `Cslib.Complexity.DecidesWithErrorExponent`: its specialization to a decision problem.
* `Cslib.Complexity.BPP.booleanSubalgebra`: `BPP` as a Boolean subalgebra of `Set α`.

## Main results

* `Cslib.Complexity.ErrorExponentAt.congr`: extensionality for per-instance error-exponent bounds.
* `Cslib.Complexity.BoundedErrorAt.repeatMajority`,
  `Cslib.Complexity.PromiseProblem.SolvesWithBoundedError.repeatMajority`: `12 q(n)` majority
  votes reduce the error to `2 ^ (-q(n))`.
* `Cslib.Complexity.ErrorExponentAt.boundedErrorAt`,
  `Cslib.Complexity.PromiseProblem.SolvesWithErrorExponent.solvesWithBoundedError`: error at most
  `2 ^ (-q(n)) ≤ 1 / 4` is bounded error.
* `Cslib.Complexity.mem_PromiseBPP_iff_forall_solvesWithErrorExponent`,
  `Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`: error reduction for `PromiseBPP`
  and `BPP`.
* `Cslib.Complexity.inter_mem_BPP`, `Cslib.Complexity.union_mem_BPP`,
  `Cslib.Complexity.diff_mem_BPP`, `Cslib.Complexity.symmDiff_mem_BPP`: Boolean closure of `BPP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type}

/-- `V` gives the answer `b` with error at most `2 ^ (-q(n))` on the instance `a`, using random
strings whose length is `p` evaluated at the length `n` of the encoded instance: the random strings
`r` of length `p n` with `V (a, r) = !b` make up at most a `2 ^ (-q n)` fraction. -/
abbrev ErrorExponentAt (enc : α ↪ List Bool) (q p : Polynomial ℕ) (V : α × List Bool → Bool)
    (a : α) (b : Bool) : Prop :=
  2 ^ q.eval (enc a).length *
    (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = !b).card ≤
    2 ^ p.eval (enc a).length

/-- An error-exponent bound at an instance depends only on the verifier's values on strings of
length `p(|a|)`. -/
theorem ErrorExponentAt.congr {enc : α ↪ List Bool} {q p : Polynomial ℕ}
    {V W : α × List Bool → Bool} {a : α} {b : Bool} (h : ErrorExponentAt enc q p V a b)
    (hVW : ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = W (a, List.ofFn r)) :
    ErrorExponentAt enc q p W a b := by
  have hcard : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = !b).card =
    (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      W (a, List.ofFn r) = !b).card :=
    congrArg Finset.card (Finset.filter_congr fun r _ => by rw [hVW r])
  rwa [ErrorExponentAt, ← hcard]

/-- **Per-instance error reduction for bounded error**: the strict majority of `12 q(n)` runs of a
verifier on independent blocks of random bits errs from `b` on at most a `2 ^ (-q(n))` fraction of
the random strings whenever a single run produces `b` on at least two thirds of them. -/
theorem BoundedErrorAt.repeatMajority {enc : α ↪ List Bool} {p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {b : Bool} (h : BoundedErrorAt enc p V a b)
    (q : Polynomial ℕ) :
    ErrorExponentAt enc q (12 * q * p) (Complexity.repeatMajority enc (6 * q) p V) a b := by
  unfold ErrorExponentAt
  have hlen : (12 * q * p).eval (enc a).length =
      2 * (6 * q).eval (enc a).length * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  have hR : (6 * q).eval (enc a).length = 6 * q.eval (enc a).length := by simp
  rw [hlen]
  refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
    (BitString.two_pow_mul_card_filter_card_filter_block_le hR
      (fun s => V (a, List.ofFn s) = b) h)
  rw [mem_filter, repeatMajority_ofFn] at hx
  cases b
  · rw [Bool.not_false, decide_eq_true_iff] at hx
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 *
      (6 * q).eval (enc a).length))))
      fun i => V (a, List.ofFn (BitString.block x i)) = true
    simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hsum
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    omega
  · rw [Bool.not_true, decide_eq_false_iff_not, not_lt] at hx
    exact mem_filter.2 ⟨mem_univ _, hx.2⟩

/-- Error at most `2 ^ (-q(n)) ≤ 1 / 4` on an instance is bounded error on that instance. -/
theorem ErrorExponentAt.boundedErrorAt {enc : α ↪ List Bool} {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} {a : α} {b : Bool} (h : ErrorExponentAt enc q p V a b)
    (hq : 2 ≤ q.eval (enc a).length) : BoundedErrorAt enc p V a b := by
  refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le
    (fun r => V (a, List.ofFn r) = b) ?_
  have hnot : (univ.filter fun r : BitString (p.eval (enc a).length) => ¬V (a, List.ofFn r) = b) =
      univ.filter fun r : BitString (p.eval (enc a).length) => V (a, List.ofFn r) = !b :=
    filter_congr fun _ _ => by cases b <;> simp
  rw [hnot]
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hq)).trans h

namespace PromiseProblem

/-- `V` solves the promise problem `Q` with error at most `2 ^ (-q(n))`, using random strings whose
length is `p` evaluated at the length `n` of the encoded instance: for every yes-instance the
rejected random strings, and for every no-instance the accepted ones, make up at most a
`2 ^ (-q(n))` fraction. Nothing is required on instances outside the promise. -/
def SolvesWithErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  ∀ a, (a ∈ Q.yes → ErrorExponentAt enc q p V a true) ∧
    (a ∈ Q.no → ErrorExponentAt enc q p V a false)

variable {enc : α ↪ List Bool} {Q : PromiseProblem α}

/-- **Error reduction for bounded error**: the majority-vote argument of
[Arora and Barak, Section 7.4.1][AroraBarak09], which the book states for languages, applied to
promise problems. The strict majority of `12 q(n)` runs of a bounded-error solver, on independent
blocks of random bits, errs on at most a `2 ^ (-q(n))` fraction of the random strings. -/
theorem SolvesWithBoundedError.repeatMajority {p : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : Q.SolvesWithBoundedError enc p V) (q : Polynomial ℕ) :
    Q.SolvesWithErrorExponent enc q (12 * q * p) (Complexity.repeatMajority enc (6 * q) p V) :=
  fun a => ⟨fun ha => ((h a).1 ha).repeatMajority q, fun ha => ((h a).2 ha).repeatMajority q⟩

/-- Error at most `2 ^ (-q(n)) ≤ 1 / 4` is bounded error. -/
theorem SolvesWithErrorExponent.solvesWithBoundedError {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : Q.SolvesWithErrorExponent enc q p V)
    (hq : ∀ n, 2 ≤ q.eval n) : Q.SolvesWithBoundedError enc p V :=
  fun a => ⟨fun ha => ((h a).1 ha).boundedErrorAt (hq _),
    fun ha => ((h a).2 ha).boundedErrorAt (hq _)⟩

end PromiseProblem

open PromiseProblem

/-- `V` decides `A` with error at most `2 ^ (-q(n))`, using random strings whose length is `p`
evaluated at the length `n` of the encoded instance: it solves `ofSet A` with that error. For every
instance `a`, the random strings `r` giving the wrong answer, `V (a, r) = false` for members of `A`
and `V (a, r) = true` for the others, make up at most a `2 ^ (-q(n))` fraction. -/
def DecidesWithErrorExponent (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  (ofSet A).SolvesWithErrorExponent enc q p V

variable {enc : α ↪ List Bool}

/-- **Error reduction for `PromiseBPP`**, the promise-problem form of the `BPP` error reduction of
[Arora and Barak, Section 7.4.1][AroraBarak09]: a promise problem is in `PromiseBPP` exactly when,
for every polynomial `q`, it is solved in polynomial time with error at most `2 ^ (-q(n))`. -/
theorem mem_PromiseBPP_iff_forall_solvesWithErrorExponent {Q : PromiseProblem α} :
    Q ∈ PromiseBPP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧ Q.SolvesWithErrorExponent enc q p V :=
  ⟨fun ⟨p, V, hV, h⟩ q => ⟨12 * q * p, _, computableInPolyTime_repeatMajority hV _ _,
      h.repeatMajority q⟩,
    fun h => let ⟨p, V, hV, h⟩ := h 2; ⟨p, V, hV, h.solvesWithBoundedError fun _ => by simp⟩⟩

/-- **Error reduction for `BPP`** [Arora and Barak, Section 7.4.1][AroraBarak09]: a problem is in
`BPP` exactly when, for every polynomial `q`, it is decided in polynomial time with error at most
`2 ^ (-q(n))`. -/
theorem mem_BPP_iff_forall_decidesWithErrorExponent {A : Set α} :
    A ∈ BPP enc ↔ ∀ q : Polynomial ℕ, ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        DecidesWithErrorExponent enc q p V A :=
  mem_PromiseBPP_iff_forall_solvesWithErrorExponent (Q := ofSet A)

/-! ### Boolean closure of `BPP` -/

open scoped symmDiff

/-- **`BPP` is closed under intersection**: reduce the error of both deciders to
`2 ^ (-3) = 1 / 8`, and accept when both accept on disjoint parts of the random string. -/
theorem inter_mem_BPP {A B : Set α} (hA : A ∈ BPP enc) (hB : B ∈ BPP enc) : A ∩ B ∈ BPP enc := by
  obtain ⟨p₁, V₁, hV₁, h₁⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.1 hA 3
  obtain ⟨p₂, V₂, hV₂, h₂⟩ := mem_BPP_iff_forall_decidesWithErrorExponent.1 hB 3
  refine mem_BPP.2 ⟨p₁ + p₂, andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂,
    by fun_prop, fun a => ?_⟩
  have hs₁ := acceptCount_add_card_filter_eq_false (V := V₁) (a := a) (n := p₁.eval (enc a).length)
  have hs₂ := acceptCount_add_card_filter_eq_false (V := V₂) (a := a) (n := p₂.eval (enc a).length)
  have hs := acceptCount_add_card_filter_eq_false
    (V := andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂) (a := a)
    (n := (p₁ + p₂).eval (enc a).length)
  have hc : acceptCount (andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂) a
      ((p₁ + p₂).eval (enc a).length) =
      acceptCount V₁ a (p₁.eval (enc a).length) *
        acceptCount V₂ a (p₂.eval (enc a).length) := by
    rw [Polynomial.eval_add]
    exact acceptCount_andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂ a (p₂.eval (enc a).length)
  constructor
  · intro ha
    have e₁ := (h₁ a).1 ha.1
    have e₂ := (h₂ a).1 ha.2
    simp only [ErrorExponentAt, Bool.not_true, Polynomial.eval_ofNat] at e₁ e₂
    have f₁ : 7 * 2 ^ p₁.eval (enc a).length ≤
        8 * acceptCount V₁ a (p₁.eval (enc a).length) := by omega
    have f₂ : 7 * 2 ^ p₂.eval (enc a).length ≤
        8 * acceptCount V₂ a (p₂.eval (enc a).length) := by omega
    unfold BoundedErrorAt
    rw [← acceptCount, hc, Polynomial.eval_add, pow_add]
    nlinarith [Nat.mul_le_mul f₁ f₂]
  · intro ha
    have hacc : 8 * acceptCount (andVerifier (fun a => p₁.eval (enc a).length) V₁ V₂) a
        ((p₁ + p₂).eval (enc a).length) ≤ 2 ^ (p₁ + p₂).eval (enc a).length := by
      rw [hc, Polynomial.eval_add, pow_add]
      by_cases ha₁ : a ∈ A
      · have ha₂ : a ∉ B := fun hb => ha ⟨ha₁, hb⟩
        have e₂ := (h₂ a).2 ha₂
        simp only [ErrorExponentAt, Bool.not_false, Polynomial.eval_ofNat] at e₂
        rw [← acceptCount] at e₂
        have hb₁ : acceptCount V₁ a (p₁.eval (enc a).length) ≤
            2 ^ p₁.eval (enc a).length := by omega
        nlinarith [Nat.mul_le_mul hb₁ e₂]
      · have e₁ := (h₁ a).2 ha₁
        simp only [ErrorExponentAt, Bool.not_false, Polynomial.eval_ofNat] at e₁
        rw [← acceptCount] at e₁
        have hb₂ : acceptCount V₂ a (p₂.eval (enc a).length) ≤
            2 ^ p₂.eval (enc a).length := by omega
        nlinarith [Nat.mul_le_mul e₁ hb₂]
    unfold BoundedErrorAt
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
