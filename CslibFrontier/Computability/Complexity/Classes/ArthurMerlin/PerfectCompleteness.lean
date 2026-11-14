/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PH

import CslibFrontier.Foundations.Combinatorics.Lautemann

/-!
# Perfect completeness and perfect soundness for MA and AM

Two-sided bounded error `(2 / 3, 1 / 3)` in `MA` and `AM` (`Cslib.Complexity.MA`,
`Cslib.Complexity.AM`) can be replaced by perfect completeness (`1`) and soundness error `1 / 2`
without changing either class ([Goldreich, Chapter 6, Footnote 7 and
Exercise 6.12][Goldreich2007Draft]; [Goldreich, Exercises 9.8(2) and 9.9][Goldreich2007DraftR5];
Fürer, Goldreich, Mansour, Sipser and Zachos):

* `MAOne` (`Cslib.Complexity.MAOne`) and `AMOne` (`Cslib.Complexity.AMOne`) require some proof (in
  `MAOne`) or every random string (in `AMOne`) to be accepted with probability `1` on members, and
  at most half of the random strings to be accepted (or to have an accepted reply) on non-members.
* Two independent trials (`r = 1` in `merlinArthurRepeat` and `arthurMerlinRepeat`, where a strict
  majority of `2` trials requires both to accept) reduce soundness error from `1 / 2` to
  `1 / 4 ≤ 1 / 3` while keeping completeness `1`, giving `MAOne ⊆ MA` and `AMOne ⊆ AM`.
* Conversely, amplifying a verifier in `MA` or `AM` to error `2 ^ (-e(n))` with
  `e(n) = k(n) = 12 p(n) + 1` and applying `sigmaTwoVerifier` or `piTwoVerifier`
  (`CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.PH`) gives perfect completeness by
  Lautemann's covering lemma and soundness error at most `1 / 2` by the union-bound cardinality
  estimates `Cslib.BitString.two_mul_card_filter_exists_add_mem_le` and
  `Cslib.BitString.two_mul_card_filter_exists_forall_add_mem_le`, yielding `MA = MAOne` and
  `AM = AMOne`.

By contrast, requiring perfect soundness (`0` acceptance on non-members) and completeness `1 / 2`
on members defines `MAZero` (`Cslib.Complexity.MAZero`, written `MA^{(1)}` in
[Goldreich, Exercise 6.12(1)][Goldreich2007Draft]), which collapses to `NP`: any accepted pair of a
proof and a random string is a deterministic certificate (`MAZero = NP`).

## Main definitions

* `Cslib.Complexity.IsMerlinArthurZeroVerifier`, `Cslib.Complexity.MAZero`: completeness `1 / 2`
  and perfect soundness (`0`).
* `Cslib.Complexity.IsMerlinArthurOneVerifier`, `Cslib.Complexity.MAOne`: perfect completeness (`1`)
  and soundness error `1 / 2` for Merlin–Arthur verifiers.
* `Cslib.Complexity.IsArthurMerlinOneVerifier`, `Cslib.Complexity.AMOne`: perfect completeness (`1`)
  and soundness error `1 / 2` for Arthur–Merlin verifiers.

## Main results

* `Cslib.Complexity.MAZero_eq_NP`: `MAZero enc = NP enc`
  ([Goldreich, Exercise 6.12(1)][Goldreich2007Draft]).
* `Cslib.Complexity.ArthurMerlin.isMerlinArthurOneVerifier_sigmaTwoVerifier`,
  `Cslib.Complexity.MA_eq_MAOne`: `MA enc = MAOne enc`
  ([Goldreich, Exercise 6.12(2)][Goldreich2007Draft];
  [Goldreich, Exercise 9.9 at `f ≡ 1`][Goldreich2007DraftR5]).
* `Cslib.Complexity.ArthurMerlin.isArthurMerlinOneVerifier_piTwoVerifier`,
  `Cslib.Complexity.AM_eq_AMOne`: `AM enc = AMOne enc` (two-message constant-round milestone of
  [Goldreich, Exercise 9.8(2)][Goldreich2007DraftR5]).
* `Cslib.Complexity.MAOne_subset_AMOne`: `MAOne enc ⊆ AMOne enc`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, Draft `r3.pdf`,
  Exercise 6.12][Goldreich2007Draft]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, Draft `r5.pdf`,
  Exercises 9.8 and 9.9][Goldreich2007DraftR5]
* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [C. Lautemann, *BPP and the polynomial hierarchy*][Lautemann1983]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-! ### Perfect soundness for `MA`: `MA^{(1)} = NP` -/

/-- `V` is a Merlin–Arthur verifier for `A` with completeness `1 / 2` and perfect soundness (`0`),
the class `MA^{(1)}` of [Goldreich, Exercise 6.12(1)][Goldreich2007Draft], with proofs of length `q`
and random strings of length `p`, both evaluated at the length of the encoded instance: on a member
`a` some proof `y` is accepted on at least half of the random strings `r`; on a non-member every
proof and random string are rejected. -/
def IsMerlinArthurZeroVerifier (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → ∃ y : Fin (q.eval (enc a).length) → Bool,
      2 ^ p.eval (enc a).length ≤
        2 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
          V (a, List.ofFn y ++ List.ofFn r) = true).card) ∧
    (a ∉ A → ∀ (y : Fin (q.eval (enc a).length) → Bool)
      (r : Fin (p.eval (enc a).length) → Bool), V (a, List.ofFn y ++ List.ofFn r) = false)

/-- The problems with polynomial-time Merlin–Arthur verifiers with completeness `1 / 2` and
soundness error `0` (`MA^{(1)}` in [Goldreich, Exercise 6.12(1)][Goldreich2007Draft]). -/
def MAZero (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsMerlinArthurZeroVerifier enc q p V A}

theorem mem_MAZero : A ∈ MAZero enc ↔ ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsMerlinArthurZeroVerifier enc q p V A :=
  Iff.rfl

/-- A Merlin–Arthur verifier with completeness `1 / 2` and perfect soundness is a deterministic
`NP` verifier when the proof and random string are read together as one certificate of length
`q + p`. -/
theorem IsMerlinArthurZeroVerifier.isVerifier {q p : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : IsMerlinArthurZeroVerifier enc q p V A) : IsVerifier enc (q + p) V A := fun a => by
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := (h a).1 ha
    have hpos : 0 < 2 ^ p.eval (enc a).length := by positivity
    obtain ⟨r, hr⟩ := card_pos.1 (by omega : 0 < (univ.filter
      fun r : Fin (p.eval (enc a).length) → Bool => V (a, List.ofFn y ++ List.ofFn r) = true).card)
    exact ⟨List.ofFn y ++ List.ofFn r, by simp [Polynomial.eval_add], (mem_filter.1 hr).2⟩
  · rintro ⟨w, hw, hVw⟩
    by_contra ha
    have htake : (w.take (q.eval (enc a).length)).length = q.eval (enc a).length := by
      rw [List.length_take]
      simp [Polynomial.eval_add] at hw
      omega
    have hdrop : (w.drop (q.eval (enc a).length)).length = p.eval (enc a).length := by
      rw [List.length_drop]
      simp [Polynomial.eval_add] at hw
      omega
    have hfalse := (h a).2 ha (BitString.ofList _ (w.take (q.eval (enc a).length)))
      (BitString.ofList _ (w.drop (q.eval (enc a).length)))
    rw [BitString.ofFn_ofList htake, BitString.ofFn_ofList hdrop, List.take_append_drop] at hfalse
    simp [hfalse] at hVw

/-- A deterministic `NP` verifier is a Merlin–Arthur verifier with completeness `1 / 2` and
perfect soundness that flips no coins. -/
theorem IsVerifier.isMerlinArthurZeroVerifier {q : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : IsVerifier enc q V A) : IsMerlinArthurZeroVerifier enc q 0 V A := fun a => by
  constructor
  · intro ha
    obtain ⟨w, hw, hVw⟩ := (h a).1 ha
    refine ⟨BitString.ofList _ w, ?_⟩
    rw [filter_true_of_mem fun r _ => by
      rw [BitString.ofFn_ofList hw,
        List.eq_nil_of_length_eq_zero (by simp : (List.ofFn r).length = 0),
        List.append_nil, hVw]]
    simp
  · intro ha y r
    rw [List.eq_nil_of_length_eq_zero (by simp : (List.ofFn r).length = 0), List.append_nil]
    by_contra hVy
    exact ha ((h a).2 ⟨List.ofFn y, List.length_ofFn, Bool.eq_true_of_not_eq_false hVy⟩)

/-- **`MAZero ⊆ NP`**: absorb the verifier's coins into Merlin's certificate. -/
theorem MAZero_subset_NP : MAZero enc ⊆ NP enc :=
  fun _ ⟨q, p, V, hV, h⟩ => ⟨q + p, V, hV, h.isVerifier⟩

/-- **`NP ⊆ MAZero`**: an `NP` verifier flips no coins. -/
theorem NP_subset_MAZero : NP enc ⊆ MAZero enc :=
  fun _ ⟨q, V, hV, h⟩ => ⟨q, 0, V, hV, h.isMerlinArthurZeroVerifier⟩

/-- **`MA^{(1)} = NP`** [Goldreich, Exercise 6.12(1)][Goldreich2007Draft]: Merlin–Arthur proof
systems with completeness `1 / 2` and perfect soundness (`0`) characterize `NP`. -/
theorem MAZero_eq_NP : MAZero enc = NP enc :=
  Set.Subset.antisymm MAZero_subset_NP NP_subset_MAZero

/-! ### Perfect completeness for `MA` and `AM`: definitions and two-trial reduction -/

/-- `V` is a Merlin–Arthur verifier for `A` with perfect completeness (`1`) and soundness error
`1 / 2` ([Goldreich, Chapter 6, Footnote 7 and Exercise 6.12(2)][Goldreich2007Draft]), with proofs
of length `q` and random strings of length `p`, both evaluated at the length of the encoded
instance: on a member `a` some proof `y` is accepted on every random string `r`,
`V (a, y ++ r) = true`; on a non-member every proof is accepted on at most half of the random
strings. -/
def IsMerlinArthurOneVerifier (enc : α ↪ List Bool) (q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → ∃ y : Fin (q.eval (enc a).length) → Bool,
      ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn y ++ List.ofFn r) = true) ∧
    (a ∉ A → ∀ y : Fin (q.eval (enc a).length) → Bool,
      2 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn y ++ List.ofFn r) = true).card ≤ 2 ^ p.eval (enc a).length)

/-- The problems with polynomial-time Merlin–Arthur verifiers with perfect completeness and
soundness error `1 / 2` (`MA` in [Goldreich, Chapter 6, Footnote 7][Goldreich2007Draft]). -/
def MAOne (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsMerlinArthurOneVerifier enc q p V A}

theorem mem_MAOne : A ∈ MAOne enc ↔ ∃ (q p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsMerlinArthurOneVerifier enc q p V A :=
  Iff.rfl

/-- `V` is an Arthur–Merlin verifier for `A` with perfect completeness (`1`) and soundness error
`1 / 2` ([Goldreich, Exercise 9.8(2)][Goldreich2007DraftR5]; Fürer, Goldreich, Mansour, Sipser and
Zachos), with random strings of length `p` and replies of length `q`, both evaluated at the length
of the encoded instance: on a member `a` every random string `r` has a reply `y` with
`V (a, r ++ y) = true`; on a non-member at most half of the random strings have one. -/
def IsArthurMerlinOneVerifier (enc : α ↪ List Bool) (p q : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → ∀ r : Fin (p.eval (enc a).length) → Bool,
      ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true) ∧
    (a ∉ A → 2 * (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true).card ≤
        2 ^ p.eval (enc a).length)

/-- The problems with polynomial-time Arthur–Merlin verifiers with perfect completeness and
soundness error `1 / 2` ([Goldreich, Exercise 9.8(2)][Goldreich2007DraftR5]; Fürer, Goldreich,
Mansour, Sipser and Zachos). -/
def AMOne (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧ IsArthurMerlinOneVerifier enc p q V A}

theorem mem_AMOne : A ∈ AMOne enc ↔ ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      IsArthurMerlinOneVerifier enc p q V A :=
  Iff.rfl

/-- If every single-trial string `s : BitString m` satisfies `P`, then every two-trial string
`x : BitString (2 * r * m)` (with `r = 1`) has strictly more than `r` satisfying blocks. -/
private theorem two_mul_two_pow_le_three_mul_card_two_trials_of_forall {r m : ℕ} (hr : r = 1)
    (P : BitString m → Prop) [DecidablePred P] (hP : ∀ s, P s) :
    2 * 2 ^ (2 * r * m) ≤
      3 * #{x : BitString (2 * r * m) | r < #{i : Fin (2 * r) | P (BitString.block x i)}} := by
  subst hr
  have hall (x : BitString (2 * 1 * m)) : 1 < #{i : Fin (2 * 1) | P (BitString.block x i)} := by
    rw [filter_true_of_mem fun i _ => hP (BitString.block x i)]
    decide
  rw [filter_true_of_mem fun x _ => hall x, card_univ, BitString.card]
  omega

/-- If at most half of the single-trial strings `s : BitString m` satisfy `P`, then at most a
quarter (and hence at most a third) of the two-trial strings `x : BitString (2 * r * m)` (with
`r = 1`) have strictly more than `r` satisfying blocks. -/
private theorem two_mul_two_pow_le_three_mul_card_two_trials_not_of_two_mul_le {r m : ℕ}
    (hr : r = 1) (P : BitString m → Prop) [DecidablePred P]
    (hP : 2 * #{s : BitString m | P s} ≤ 2 ^ m) :
    2 * 2 ^ (2 * r * m) ≤
      3 * #{x : BitString (2 * r * m) | ¬ r < #{i : Fin (2 * r) | P (BitString.block x i)}} := by
  subst hr
  refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le
    (fun x : BitString (2 * 1 * m) => ¬ 1 < #{i : Fin (2 * 1) | P (BitString.block x i)}) ?_
  simp only [not_not]
  have hsub : (univ.filter fun x : BitString (2 * 1 * m) =>
      1 < #{i : Fin (2 * 1) | P (BitString.block x i)}) ⊆
      univ.filter fun x : BitString (2 * 1 * m) =>
        ∀ i : Fin (2 * 1), P (BitString.block x i) := fun x hx => by
    have hx' : 1 < #{i : Fin (2 * 1) | P (BitString.block x i)} := (mem_filter.1 hx).2
    have hle : #{i : Fin (2 * 1) | P (BitString.block x i)} ≤ 2 :=
      (card_le_univ _).trans_eq (by simp)
    have heq : #{i : Fin (2 * 1) | P (BitString.block x i)} = #(univ : Finset (Fin (2 * 1))) := by
      simp only [card_univ, Fintype.card_fin]
      omega
    have hall := filter_eq_self.1 (eq_of_subset_of_card_le (filter_subset _ _) heq.ge)
    exact mem_filter.2 ⟨mem_univ _, fun i => hall i (mem_univ i)⟩
  exact (Nat.mul_le_mul_left (2 ^ (2 * 1)) (card_le_card hsub)).trans
    (BitString.two_pow_mul_card_filter_forall_block_le P hP)

/-- Repeating a perfectly complete Merlin–Arthur verifier twice (`r = 1`) reduces its soundness
error from `1 / 2` to `1 / 4 ≤ 1 / 3`. -/
theorem IsMerlinArthurOneVerifier.merlinArthurRepeat_one {q p : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : IsMerlinArthurOneVerifier enc q p V A) :
    IsMerlinArthurVerifier enc q (2 * 1 * p) (merlinArthurRepeat enc q 1 p V) A := by
  intro a
  have hlen : (2 * 1 * p).eval (enc a).length =
      2 * (1 : Polynomial ℕ).eval (enc a).length * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  have hrep (y : Fin (q.eval (enc a).length) → Bool)
      (x : BitString (2 * (1 : Polynomial ℕ).eval (enc a).length * p.eval (enc a).length)) :
      merlinArthurRepeat enc q 1 p V (a, List.ofFn y ++ List.ofFn x) =
        decide ((1 : Polynomial ℕ).eval (enc a).length <
          #{i : Fin (2 * (1 : Polynomial ℕ).eval (enc a).length) |
            V (a, List.ofFn y ++ List.ofFn (BitString.block x i)) = true}) := by
    rw [merlinArthurRepeat, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn,
      repeatMajority_ofFn]
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := (h a).1 ha
    refine ⟨y, ?_⟩
    unfold BoundedErrorAt
    rw [hlen]
    simpa only [hrep y, decide_eq_true_iff] using
      two_mul_two_pow_le_three_mul_card_two_trials_of_forall Polynomial.eval_one
        (fun r => V (a, List.ofFn y ++ List.ofFn r) = true) hy
  · intro ha y
    unfold BoundedErrorAt
    rw [hlen]
    simpa only [hrep y, decide_eq_false_iff_not] using
      two_mul_two_pow_le_three_mul_card_two_trials_not_of_two_mul_le Polynomial.eval_one
        (fun r => V (a, List.ofFn y ++ List.ofFn r) = true) ((h a).2 ha y)

/-- **`MAOne ⊆ MA`**. -/
theorem MAOne_subset_MA : MAOne enc ⊆ MA enc :=
  fun _ ⟨q, p, V, hV, h⟩ =>
    ⟨q, 2 * 1 * p, merlinArthurRepeat enc q 1 p V,
      computableInPolyTime_merlinArthurRepeat hV q 1 p, h.merlinArthurRepeat_one⟩

/-- Repeating a perfectly complete Arthur–Merlin verifier twice in parallel (`r = 1`) reduces its
soundness error from `1 / 2` to `1 / 4 ≤ 1 / 3`. -/
theorem IsArthurMerlinOneVerifier.arthurMerlinRepeat_one {p q : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : IsArthurMerlinOneVerifier enc p q V A) :
    IsArthurMerlinVerifier enc (2 * 1 * p) (2 * 1 * q) (arthurMerlinRepeat enc 1 p q V) A := by
  intro a
  have hlenP : (2 * 1 * p).eval (enc a).length =
      2 * (1 : Polynomial ℕ).eval (enc a).length * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  have hlenQ : (2 * 1 * q).eval (enc a).length =
      2 * (1 : Polynomial ℕ).eval (enc a).length * q.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
  have hex := exists_arthurMerlinRepeat_ofFn_append_ofFn_iff (enc := enc) (r := 1) (p := p) (q := q)
    (V := V) a
  constructor
  · intro ha
    rw [hlenP, hlenQ]
    simpa only [hex] using
      two_mul_two_pow_le_three_mul_card_two_trials_of_forall Polynomial.eval_one
        (fun r : BitString (p.eval (enc a).length) =>
          ∃ z : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn z) = true)
        ((h a).1 ha)
  · intro ha
    rw [hlenP, hlenQ]
    refine (two_mul_two_pow_le_three_mul_card_two_trials_not_of_two_mul_le Polynomial.eval_one
      (fun r : BitString (p.eval (enc a).length) =>
        ∃ z : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn z) = true)
      ((h a).2 ha)).trans_eq (congrArg (3 * ·) (congrArg card (filter_congr fun x _ => ?_)))
    simp only [← Bool.not_eq_true, ← not_exists, hex]

/-- **`AMOne ⊆ AM`**. -/
theorem AMOne_subset_AM : AMOne enc ⊆ AM enc :=
  fun _ ⟨p, q, V, hV, h⟩ =>
    ⟨2 * 1 * p, 2 * 1 * q, arthurMerlinRepeat enc 1 p q V,
      computableInPolyTime_arthurMerlinRepeat hV 1 p q, h.arthurMerlinRepeat_one⟩

/-! ### Shift covers give perfect completeness: `MA = MAOne` and `AM = AMOne` -/

namespace ArthurMerlin

/-- **Perfect completeness for `MA` via Lautemann's shifts**
([Goldreich, Exercise 6.12(2)][Goldreich2007Draft];
[Goldreich, Exercise 9.9][Goldreich2007DraftR5]): if `W` is a Merlin–Arthur verifier for `A` with
error at most `2 ^ (-e(n))` and random strings of `p(n)` bits, and `k(n)` shifts satisfy
`p(n) < e(n) k(n)` and `2 k(n) ≤ 2 ^ e(n)`, then `sigmaTwoVerifier enc q k p W` is a perfectly
complete Merlin–Arthur verifier for `A` with soundness error `1 / 2`. -/
theorem isMerlinArthurOneVerifier_sigmaTwoVerifier {e q k p : Polynomial ℕ}
    {W : α × List Bool → Bool} (h : IsMerlinArthurVerifierWithErrorExponent enc e q p W A)
    (hcover : ∀ n, p.eval n < e.eval n * k.eval n)
    (hshifts : ∀ n, 2 * k.eval n ≤ 2 ^ e.eval n) :
    IsMerlinArthurOneVerifier enc (q + k * p) p (sigmaTwoVerifier enc q k p W) A := by
  have hshifts_lt (n : ℕ) : k.eval n < 2 ^ e.eval n := by
    have hpos : 0 < 2 ^ e.eval n := by positivity
    have := hshifts n
    omega
  have halt := isAlternatingVerifier_sigmaTwoVerifier h hcover hshifts_lt
  intro a
  constructor
  · intro ha
    obtain ⟨w, hw, hall⟩ := (halt a).1 ha
    simp only [List.map_cons, List.map_nil, alternation_false_cons,
      alternation_nil, List.append_nil] at hw hall
    refine ⟨BitString.ofList _ w, fun r => ?_⟩
    rw [BitString.ofFn_ofList hw]
    exact hall (List.ofFn r) List.length_ofFn
  · intro ha w
    have hw : (List.ofFn w).length =
        q.eval (enc a).length + k.eval (enc a).length * p.eval (enc a).length := by
      simp [Polynomial.eval_add, Polynomial.eval_mul]
    set y : BitString (q.eval (enc a).length) :=
      BitString.ofList (q.eval (enc a).length) ((List.ofFn w).take (q.eval (enc a).length))
    set u : Fin (k.eval (enc a).length) → BitString (p.eval (enc a).length) :=
      BitString.block (BitString.ofList (k.eval (enc a).length * p.eval (enc a).length)
        ((List.ofFn w).drop (q.eval (enc a).length)))
    have hy : List.ofFn y = (List.ofFn w).take (q.eval (enc a).length) :=
      BitString.ofFn_ofList (by simp)
    set S : Finset (BitString (p.eval (enc a).length)) :=
      univ.filter fun z => W (a, List.ofFn y ++ List.ofFn z) = true
    have hsub : (univ.filter fun r : BitString (p.eval (enc a).length) =>
        sigmaTwoVerifier enc q k p W (a, List.ofFn w ++ List.ofFn r) = true) ⊆
        univ.filter fun r => ∃ i, r + u i ∈ S := fun r hr => by
      obtain ⟨i, hi⟩ := (sigmaTwoVerifier_append_ofFn hw r).1 (mem_filter.1 hr).2
      exact mem_filter.2 ⟨mem_univ _, i, mem_filter.2 ⟨mem_univ _, by rwa [hy]⟩⟩
    exact (Nat.mul_le_mul_left 2 (card_le_card hsub)).trans
      (BitString.two_mul_card_filter_exists_add_mem_le S ((h a).2 ha y) (hshifts _) u)

/-- **Perfect completeness for `AM` via Lautemann's shifts**
([Goldreich, Exercise 9.8(2)][Goldreich2007DraftR5]; Fürer, Goldreich, Mansour, Sipser and Zachos):
if `W` is an Arthur–Merlin verifier for `A` with error at most `2 ^ (-e(n))`, random strings of
`p(n)` bits and replies of `q(n)` bits, and `k(n)` shifts satisfy `p(n) < e(n) k(n)` and
`k(n) < 2 ^ e(n)`, then `piTwoVerifier enc k p q W` is a perfectly complete Arthur–Merlin verifier
for `A` with soundness error `1 / 2`. -/
theorem isArthurMerlinOneVerifier_piTwoVerifier {e k p q : Polynomial ℕ}
    {W : α × List Bool → Bool} (h : IsArthurMerlinVerifierWithErrorExponent enc e p q W A)
    (hcover : ∀ n, p.eval n < e.eval n * k.eval n)
    (hshifts : ∀ n, k.eval n < 2 ^ e.eval n) :
    IsArthurMerlinOneVerifier enc (k * p) (p + k * q) (piTwoVerifier enc k p q W) A := by
  have halt := isAlternatingVerifier_piTwoVerifier h hcover hshifts
  intro a
  constructor
  · intro ha u
    have hall := (halt a).1 ha
    simp only [List.map_cons, List.map_nil, alternation_true_cons, alternation_false_cons,
      alternation_nil, List.append_nil] at hall
    obtain ⟨v, hv, hacc⟩ := hall (List.ofFn u) (by simp [Polynomial.eval_mul])
    exact ⟨BitString.ofList _ v, by rwa [BitString.ofFn_ofList hv]⟩
  · intro ha
    set K := k.eval (enc a).length
    set m := p.eval (enc a).length
    set l := q.eval (enc a).length
    have hlen : (k * p).eval (enc a).length = K * m := Polynomial.eval_mul
    set S : Finset (BitString m) :=
      univ.filter fun z : BitString m => ∃ y : BitString l, W (a, List.ofFn z ++ List.ofFn y) = true
    have hbound := BitString.two_mul_card_filter_exists_forall_add_mem_le S ((h a).2 ha) (hcover _)
    have hbij : #{u : BitString (K * m) | ∃ r : BitString m, ∀ i, r + BitString.block u i ∈ S} =
        #{u : Fin K → BitString m | ∃ r : BitString m, ∀ i, r + u i ∈ S} :=
      card_nbij' BitString.blocksEquiv BitString.blocksEquiv.symm
        (fun u hu => by simpa using hu) (fun u hu => by simpa using hu)
        (fun _ _ => by simp) (fun _ _ => by simp)
    rw [← hbij] at hbound
    rw [hlen]
    refine (Nat.mul_le_mul_left 2 (card_le_card fun u hu => ?_)).trans hbound
    obtain ⟨v, hv⟩ := (mem_filter.1 hu).2
    have hall := (piTwoVerifier_append List.length_ofFn (List.ofFn v)).1 hv
    refine mem_filter.2 ⟨mem_univ _, BitString.ofList m (List.ofFn v), fun i => ?_⟩
    rw [BitString.ofList_ofFn] at hall
    exact mem_filter.2 ⟨mem_univ _, _, hall i⟩

/-- Twice `12 p(n) + 1` is at most `2 ^ (12 p(n) + 1)`. -/
private theorem two_mul_eval_le_two_pow (p : Polynomial ℕ) (n : ℕ) :
    2 * (12 * p + 1).eval n ≤ 2 ^ (12 * p + 1).eval n := by
  simp only [Polynomial.eval_add, Polynomial.eval_one]
  rw [pow_succ']
  exact Nat.mul_le_mul_left 2 Nat.lt_two_pow_self

end ArthurMerlin

open ArthurMerlin

/-- **`MA ⊆ MAOne`** ([Goldreich, Exercise 6.12(2)][Goldreich2007Draft];
[Goldreich, Exercise 9.9 at `f ≡ 1`][Goldreich2007DraftR5]): amplify a Merlin–Arthur verifier and
attach Lautemann's shifts to Merlin's proof. -/
theorem MA_subset_MAOne : MA enc ⊆ MAOne enc := by
  rintro A ⟨q, p, V, hV, h⟩
  exact ⟨q + (12 * p + 1) * (12 * (12 * p + 1) * p), 12 * (12 * p + 1) * p,
    sigmaTwoVerifier enc q (12 * p + 1) (12 * (12 * p + 1) * p)
      (merlinArthurRepeat enc q (6 * (12 * p + 1)) p V),
    computableInPolyTime_sigmaTwoVerifier
      (computableInPolyTime_merlinArthurRepeat hV _ _ _) _ _ _,
    isMerlinArthurOneVerifier_sigmaTwoVerifier (h.repeatMajority _) (eval_lt_mul p)
      (two_mul_eval_le_two_pow p)⟩

/-- **`MA = MAOne`** ([Goldreich, Exercise 6.12(2)][Goldreich2007Draft];
[Goldreich, Exercise 9.9 at `f ≡ 1`][Goldreich2007DraftR5]): two-sided bounded error
`(2 / 3, 1 / 3)` and perfect completeness `(1, 1 / 2)` define the same class `MA`. -/
theorem MA_eq_MAOne : MA enc = MAOne enc :=
  Set.Subset.antisymm MA_subset_MAOne MAOne_subset_MA

/-- **`AM ⊆ AMOne`** ([Goldreich, Exercise 9.8(2)][Goldreich2007DraftR5]; Fürer, Goldreich,
Mansour, Sipser and Zachos): amplify an Arthur–Merlin verifier and have Arthur send `k` random
strings while Merlin replies with one shift and `k` replies. -/
theorem AM_subset_AMOne : AM enc ⊆ AMOne enc := by
  rintro A ⟨p, q, V, hV, h⟩
  exact ⟨(12 * p + 1) * (12 * (12 * p + 1) * p),
    12 * (12 * p + 1) * p + (12 * p + 1) * (12 * (12 * p + 1) * q),
    piTwoVerifier enc (12 * p + 1) (12 * (12 * p + 1) * p) (12 * (12 * p + 1) * q)
      (arthurMerlinRepeat enc (6 * (12 * p + 1)) p q V),
    computableInPolyTime_piTwoVerifier
      (computableInPolyTime_arthurMerlinRepeat hV _ _ _) _ _ _,
    isArthurMerlinOneVerifier_piTwoVerifier (h.repeatMajority _) (eval_lt_mul p)
      fun _ => Nat.lt_two_pow_self⟩

/-- **`AM = AMOne`** (two-message constant-round milestone of
[Goldreich, Exercise 9.8(2)][Goldreich2007DraftR5]; Fürer, Goldreich, Mansour, Sipser and Zachos):
two-sided bounded error `(2 / 3, 1 / 3)` and perfect completeness `(1, 1 / 2)` define the same
class `AM`. -/
theorem AM_eq_AMOne : AM enc = AMOne enc :=
  Set.Subset.antisymm AM_subset_AMOne AMOne_subset_AM

/-- **`MAOne ⊆ AMOne`**. -/
theorem MAOne_subset_AMOne : MAOne enc ⊆ AMOne enc := by
  rw [← MA_eq_MAOne, ← AM_eq_AMOne]
  exact MA_subset_AM

end Cslib.Complexity
