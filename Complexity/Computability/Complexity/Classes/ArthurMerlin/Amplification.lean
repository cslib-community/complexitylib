/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin
public import Complexity.Computability.Complexity.Classes.RepeatedTrials
public import Complexity.Computability.Complexity.Classes.SBP
public import Complexity.Foundations.Data.BitString.WordCount

import Complexity.Computability.Complexity.Classes.SharpP.Closure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Foundations.Data.List.OfFn

/-!
# Error reduction for MA and AM, `MA ⊆ AM`, `MA ⊆ SBP` and `MAM = AM`

The error `1 / 3` in the definitions of `MA` and `AM` (`Cslib.Complexity.MA`,
`Cslib.Complexity.AM`) can be made exponentially small by majority votes over independent runs,
as for `BPP` (`Cslib.Complexity.mem_BPP_iff_forall_decidesWithErrorExponent`)
[Babai][Babai1985], [Arora and Barak, Section 8.2][AroraBarak09]. Write `n` for the length of the
encoded instance.

* For `MA` (`Cslib.Complexity.merlinArthurRepeat`), Arthur keeps Merlin's proof and runs the
  verifier with it on `2 r(n)` independent random rows. The proof length does not change, which
  is what makes the error smaller than `2 ^ (-q(n))` for proofs of `q(n)` bits possible.
* For `AM` (`Cslib.Complexity.arthurMerlinRepeat`), Arthur sends `2 r(n)` random rows at once and
  Merlin answers each of them. Merlin can answer every row independently, so the amplified
  acceptance condition is the majority vote of the original one
  (`Cslib.Complexity.exists_arthurMerlinRepeat_ofFn_append_ofFn_iff`).

In both cases a majority of `12 e(n)` runs errs on at most a `2 ^ (-e(n))` fraction of the random
strings (`Cslib.BitString.two_pow_mul_card_filter_card_filter_block_le`, from the exponential
moment bound `Cslib.card_filter_card_filter_le_le`).

With error below `2 ^ (-q(n) - 2)`, a union bound over Merlin's proofs shows that the Merlin–Arthur
verifier, with the order of its messages swapped, is an Arthur–Merlin verifier: `MA ⊆ AM`
[Babai][Babai1985]. The same bound shows that the number of accepted pairs of a proof and a random
string is at least `3 / 4` of the random strings on members and at most `1 / 4` on non-members,
so `MA ⊆ SBP` [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006].

The swap behind `MA ⊆ AM` also works for an Arthur–Merlin verifier on pairs `(a, w)`: reduce its
error below `2 ^ (-|w| - 2)` and let Merlin send `w` with his reply. By the union bound over the
words `w`, Arthur's coins rarely admit an accepted answer for any `w` when no `w` works, so `AM`
is closed under polynomially bounded existential quantification (`MAM = AM`,
`Cslib.Complexity.mem_AM_of_exists`) [Babai][Babai1985].

## Main definitions

* `Cslib.Complexity.IsMerlinArthurVerifierWithErrorExponent`,
  `Cslib.Complexity.IsArthurMerlinVerifierWithErrorExponent`: error at most `2 ^ (-e(n))`.
* `Cslib.Complexity.merlinArthurRepeat`, `Cslib.Complexity.arthurMerlinRepeat`: majority votes.

## Main results

* `Cslib.Complexity.IsMerlinArthurVerifier.repeatMajority`,
  `Cslib.Complexity.mem_MA_iff_exists_forall_errorExponent`: error reduction for `MA`, with the
  proof length fixed before the error.
* `Cslib.Complexity.IsArthurMerlinVerifier.repeatMajority`,
  `Cslib.Complexity.mem_AM_iff_forall_errorExponent`: error reduction for `AM`.
* `Cslib.Complexity.MA_subset_AM`, `Cslib.Complexity.NP_subset_AM`,
  `Cslib.Complexity.BPP_subset_AM`.
* `Cslib.Complexity.MA_subset_SBP`.
* `Cslib.Complexity.mem_AM_of_exists`: `AM` is closed under polynomially bounded existential
  quantification (`MAM = AM`).

## References

* [L. Babai, *Trading group theory for randomness*][Babai1985]
* [L. Babai, S. Moran, *Arthur–Merlin games: a randomized proof system, and a hierarchy of
  complexity classes*][BabaiMoran1988]
* [E. Böhler, C. Glaßer, D. Meister, *Error-bounded probabilistic computations between
  MA and AM*][BoehlerGlasserMeister2006]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-! ### Error reduction for `MA` -/

/-- `V` is a Merlin–Arthur verifier for `A` with error at most `2 ^ (-e(n))`, with proofs of length
`q` and random strings of length `p`, all evaluated at the length `n` of the encoded instance: on a
member some proof is rejected on at most a `2 ^ (-e(n))` fraction of the random strings; on a
non-member every proof is accepted on at most such a fraction. -/
def IsMerlinArthurVerifierWithErrorExponent (enc : α ↪ List Bool) (e q p : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → ∃ y : Fin (q.eval (enc a).length) → Bool, 2 ^ e.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn y ++ List.ofFn r) = false).card ≤ 2 ^ p.eval (enc a).length) ∧
    (a ∉ A → ∀ y : Fin (q.eval (enc a).length) → Bool, 2 ^ e.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn y ++ List.ofFn r) = true).card ≤ 2 ^ p.eval (enc a).length)

/-- The strict majority of `2 r(n)` runs of a Merlin–Arthur verifier `V` on one proof, where `n` is
the length of the encoded instance: the string is a proof of `q(n)` bits followed by `2 r(n)`
random rows of `p(n)` bits (`Cslib.Complexity.repeatMajority`), and `V` runs on the proof followed
by each row. -/
def merlinArthurRepeat (enc : α ↪ List Bool) (q r p : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  repeatMajority enc r p (fun z => V (z.1, x.2.take (q.eval (enc x.1).length) ++ z.2))
    (x.1, x.2.drop (q.eval (enc x.1).length))

/-- Majority votes of a polynomial-time Merlin–Arthur verifier take polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_merlinArthurRepeat {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (q r p : Polynomial ℕ) :
    ComputableInPolyTime (merlinArthurRepeat enc q r p V) (encPair enc encBits) encBool := by
  have hV := hV.tidy
  refine .of_tidy ?_
  unfold merlinArthurRepeat repeatMajority repeatVotes
  fun_prop

/-- On a proof followed by `2 r(n)` rows of `p(n)` bits, the majority vote compares the number of
rows accepted with the proof with `r(n)`. -/
private theorem merlinArthurRepeat_ofFn_append_ofFn {q r p : Polynomial ℕ}
    {V : α × List Bool → Bool}
    (a : α) (y : Fin (q.eval (enc a).length) → Bool)
    (x : BitString (2 * r.eval (enc a).length * p.eval (enc a).length)) :
    merlinArthurRepeat enc q r p V (a, List.ofFn y ++ List.ofFn x) = decide (r.eval (enc a).length <
      #{i | V (a, List.ofFn y ++ List.ofFn (BitString.block x i)) = true}) := by
  rw [merlinArthurRepeat, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]
  exact repeatMajority_ofFn (V := fun z => V (z.1, List.ofFn y ++ z.2)) a x

/-- **Error reduction for `MA`** [Babai][Babai1985]. The strict majority of `12 e(n)` runs of a
Merlin–Arthur verifier with one proof, on independent blocks of random bits, errs on at most a
`2 ^ (-e(n))` fraction of the random strings. The proofs keep their length. -/
theorem IsMerlinArthurVerifier.repeatMajority {q p : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : IsMerlinArthurVerifier enc q p V A) (e : Polynomial ℕ) :
    IsMerlinArthurVerifierWithErrorExponent enc e q (12 * e * p)
      (merlinArthurRepeat enc q (6 * e) p V) A := by
  intro a
  have hlen : (12 * e * p).eval (enc a).length =
      2 * (6 * e).eval (enc a).length * p.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  have hR : (6 * e).eval (enc a).length = 6 * e.eval (enc a).length := by simp
  rw [hlen]
  constructor
  · -- on a member, the good proof is rejected only when at most `R` runs accept
    intro ha
    obtain ⟨y, hy⟩ := (h a).1 ha
    refine ⟨y, (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => V (a, List.ofFn y ++ List.ofFn s) = true) hy)⟩
    rw [mem_filter, merlinArthurRepeat_ofFn_append_ofFn, decide_eq_false_iff_not, not_lt] at hx
    exact mem_filter.2 ⟨mem_univ _, hx.2⟩
  · -- on a non-member, every proof is accepted only when at most `R` runs reject
    intro ha y
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => V (a, List.ofFn y ++ List.ofFn s) = false) ((h a).2 ha y))
    rw [mem_filter, merlinArthurRepeat_ofFn_append_ofFn, decide_eq_true_iff] at hx
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 *
      (6 * e).eval (enc a).length))))
      fun i => V (a, List.ofFn y ++ List.ofFn (BitString.block x i)) = true
    simp only [Bool.not_eq_true, card_univ, Fintype.card_fin] at hsum
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    omega

/-- Error at most `2 ^ (-e(n)) ≤ 1 / 4` is error at most `1 / 3`. -/
theorem IsMerlinArthurVerifierWithErrorExponent.isMerlinArthurVerifier {e q p : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : IsMerlinArthurVerifierWithErrorExponent enc e q p V A)
    (he : ∀ n, 2 ≤ e.eval n) : IsMerlinArthurVerifier enc q p V A := fun a => by
  have h4 : 4 ≤ 2 ^ e.eval (enc a).length :=
    (Nat.pow_le_pow_right (by norm_num) (he _) : 2 ^ 2 ≤ _)
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := (h a).1 ha
    refine ⟨y, BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_⟩
    simpa only [Bool.not_eq_true] using (Nat.mul_le_mul_right _ h4).trans hy
  · intro ha y
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    simpa only [Bool.not_eq_false] using (Nat.mul_le_mul_right _ h4).trans ((h a).2 ha y)

/-- **Error reduction for `MA`** [Babai][Babai1985]: a problem is in `MA` exactly when, for some
polynomial proof length `q` and every polynomial `e`, it has a polynomial-time Merlin–Arthur
verifier with proofs of length `q` and error at most `2 ^ (-e(n))`. The proof length is chosen
before the error, so the error can be made smaller than `2 ^ (-q(n))`. -/
theorem mem_MA_iff_exists_forall_errorExponent :
    A ∈ MA enc ↔ ∃ q : Polynomial ℕ, ∀ e : Polynomial ℕ, ∃ (p : Polynomial ℕ)
      (V : α × List Bool → Bool), ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsMerlinArthurVerifierWithErrorExponent enc e q p V A := by
  have this : A ∈ MA enc ↔ ∃ q : Polynomial ℕ, ∀ e : Polynomial ℕ, ∃ (p : Polynomial ℕ)
      (V : α × List Bool → Bool), ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      IsMerlinArthurVerifierWithErrorExponent enc e q p V A := by
    rw [mem_MA]
    refine ⟨fun ⟨q, p, V, hV, h⟩ => ⟨q, fun e => ⟨12 * e * p, _,
      (computableInPolyTime_merlinArthurRepeat hV _ _ _).tidy, h.repeatMajority e⟩⟩,
      fun ⟨q, h⟩ => ?_⟩
    obtain ⟨p, V, hV, h⟩ := h 2
    exact ⟨q, p, V, (.of_tidy hV), h.isMerlinArthurVerifier fun _ => by simp⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-! ### Error reduction for `AM` -/

/-- `V` is an Arthur–Merlin verifier for `A` with error at most `2 ^ (-e(n))`, with random strings
of length `p` and replies of length `q`, all evaluated at the length `n` of the encoded instance:
on a member at most a `2 ^ (-e(n))` fraction of the random strings have no accepted reply; on a
non-member at most such a fraction have one. -/
def IsArthurMerlinVerifierWithErrorExponent (enc : α ↪ List Bool) (e p q : Polynomial ℕ)
    (V : α × List Bool → Bool) (A : Set α) : Prop :=
  ∀ a, (a ∈ A → 2 ^ e.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        ∀ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = false).card ≤
      2 ^ p.eval (enc a).length) ∧
    (a ∉ A → 2 ^ e.eval (enc a).length *
      (univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        ∃ y : Fin (q.eval (enc a).length) → Bool, V (a, List.ofFn r ++ List.ofFn y) = true).card ≤
      2 ^ p.eval (enc a).length)

/-- The strict majority of `2 r(n)` parallel runs of an Arthur–Merlin verifier `V`, where `n` is the
length of the encoded instance: the string consists of `2 r(n)` random rows of `p(n)` bits followed
by `2 r(n)` replies of `q(n)` bits (`Cslib.BitString.listRow`), and `V` runs on each row followed
by its reply. Bits missing from a short string read as `false`. -/
def arthurMerlinRepeat (enc : α ↪ List Bool) (r p q : Polynomial ℕ) (V : α × List Bool → Bool)
    (x : α × List Bool) : Bool :=
  decide (r.eval (enc x.1).length < (List.range (2 * r.eval (enc x.1).length)).countP fun i =>
    V (x.1, BitString.listRow (p.eval (enc x.1).length) i x.2 ++
      BitString.listRow (q.eval (enc x.1).length) i
        (x.2.drop (2 * r.eval (enc x.1).length * p.eval (enc x.1).length))))

/-- Parallel majority votes of a polynomial-time Arthur–Merlin verifier take polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_arthurMerlinRepeat {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (r p q : Polynomial ℕ) :
    ComputableInPolyTime (arthurMerlinRepeat enc r p q V) (encPair enc encBits) encBool := by
  have hV := hV.tidy
  refine .of_tidy ?_
  unfold arthurMerlinRepeat
  fun_prop

/-- On `2 r(n)` rows followed by `2 r(n)` replies, the parallel majority vote compares the number
of rows accepted with their replies with `r(n)`. -/
private theorem arthurMerlinRepeat_ofFn_append_ofFn {r p q : Polynomial ℕ}
    {V : α × List Bool → Bool}
    (a : α) (x : BitString (2 * r.eval (enc a).length * p.eval (enc a).length))
    (y : BitString (2 * r.eval (enc a).length * q.eval (enc a).length)) :
    arthurMerlinRepeat enc r p q V (a, List.ofFn x ++ List.ofFn y) =
      decide (r.eval (enc a).length < #{i | V (a, List.ofFn (BitString.block x i) ++
        List.ofFn (BitString.block y i)) = true}) := by
  rw [arthurMerlinRepeat, List.drop_left' List.length_ofFn, List.countP_range_eq_card_filter]
  refine congrArg (fun c => decide (r.eval (enc a).length < c))
    (congrArg card (filter_congr fun i _ => ?_))
  rw [BitString.listRow_eq_ofFn _ i, BitString.listRow_eq_ofFn _ i, BitString.ofList_ofFn_append,
    BitString.ofList_ofFn]

/-- **Parallel answers.** Some replies make a strict majority of the parallel runs accept iff a
strict majority of the random rows have an accepted reply each. -/
theorem exists_arthurMerlinRepeat_ofFn_append_ofFn_iff {r p q : Polynomial ℕ}
    {V : α × List Bool → Bool} (a : α)
    (x : BitString (2 * r.eval (enc a).length * p.eval (enc a).length)) :
    (∃ y : BitString (2 * r.eval (enc a).length * q.eval (enc a).length),
        arthurMerlinRepeat enc r p q V (a, List.ofFn x ++ List.ofFn y) = true) ↔
      r.eval (enc a).length < #{i | ∃ z : Fin (q.eval (enc a).length) → Bool,
        V (a, List.ofFn (BitString.block x i) ++ List.ofFn z) = true} := by
  simp only [arthurMerlinRepeat_ofFn_append_ofFn, decide_eq_true_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact hy.trans_le (card_le_card fun i hi =>
      mem_filter.2 ⟨mem_univ _, _, (mem_filter.1 hi).2⟩)
  · intro h
    classical
    let z : Fin (2 * r.eval (enc a).length) → Fin (q.eval (enc a).length) → Bool := fun i =>
      if hi : ∃ z : Fin (q.eval (enc a).length) → Bool,
          V (a, List.ofFn (BitString.block x i) ++ List.ofFn z) = true then hi.choose
      else fun _ => false
    refine ⟨BitString.blocksEquiv.symm z, h.trans_le (card_le_card fun i hi => ?_)⟩
    have hi := (mem_filter.1 hi).2
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    rw [BitString.block_blocksEquiv_symm]
    simp only [z, hi, ↓reduceDIte]
    exact hi.choose_spec

/-- **Error reduction for `AM`** [Babai][Babai1985]. The strict majority of `12 e(n)` parallel runs
of an Arthur–Merlin verifier, on independent blocks of random bits answered independently, errs on
at most a `2 ^ (-e(n))` fraction of the random strings. -/
theorem IsArthurMerlinVerifier.repeatMajority {p q : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : IsArthurMerlinVerifier enc p q V A) (e : Polynomial ℕ) :
    IsArthurMerlinVerifierWithErrorExponent enc e (12 * e * p) (12 * e * q)
      (arthurMerlinRepeat enc (6 * e) p q V) A := by
  intro a
  have hlen (s : Polynomial ℕ) : (12 * e * s).eval (enc a).length =
      2 * (6 * e).eval (enc a).length * s.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  have hR : (6 * e).eval (enc a).length = 6 * e.eval (enc a).length := by simp
  rw [hlen p, hlen q]
  -- the amplified acceptance condition is a majority vote of the original one
  have hacc (x : BitString (2 * (6 * e).eval (enc a).length * p.eval (enc a).length)) :
      (∃ y : BitString (2 * (6 * e).eval (enc a).length * q.eval (enc a).length),
        arthurMerlinRepeat enc (6 * e) p q V (a, List.ofFn x ++ List.ofFn y) = true) ↔
      (6 * e).eval (enc a).length < #{i | ∃ z : Fin (q.eval (enc a).length) → Bool,
        V (a, List.ofFn (BitString.block x i) ++ List.ofFn z) = true} :=
    exists_arthurMerlinRepeat_ofFn_append_ofFn_iff a x
  constructor
  · -- on a member, no reply is accepted only when at most `R` rows have an accepted reply
    intro ha
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => ∃ z : Fin (q.eval (enc a).length) → Bool,
          V (a, List.ofFn s ++ List.ofFn z) = true) ((h a).1 ha))
    have hx := (mem_filter.1 hx).2
    refine mem_filter.2 ⟨mem_univ _, not_lt.1 fun hlt => ?_⟩
    obtain ⟨y, hy⟩ := (hacc x).2 hlt
    rw [hx y] at hy
    exact Bool.false_ne_true hy
  · -- on a non-member, some reply is accepted only when at most `R` rows have none
    intro ha
    refine (Nat.mul_le_mul_left _ (card_le_card fun x hx => ?_)).trans
      (BitString.two_pow_mul_card_filter_card_filter_block_le hR
        (fun s => ∀ z : Fin (q.eval (enc a).length) → Bool,
          V (a, List.ofFn s ++ List.ofFn z) = false) ((h a).2 ha))
    have hx := (hacc x).1 (mem_filter.1 hx).2
    have hsum := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 *
      (6 * e).eval (enc a).length))))
      fun i => ∃ z : Fin (q.eval (enc a).length) → Bool,
        V (a, List.ofFn (BitString.block x i) ++ List.ofFn z) = true
    simp only [not_exists, Bool.not_eq_true, card_univ, Fintype.card_fin] at hsum
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    omega

/-- Error at most `2 ^ (-e(n)) ≤ 1 / 4` is error at most `1 / 3`. -/
theorem IsArthurMerlinVerifierWithErrorExponent.isArthurMerlinVerifier {e p q : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : IsArthurMerlinVerifierWithErrorExponent enc e p q V A)
    (he : ∀ n, 2 ≤ e.eval n) : IsArthurMerlinVerifier enc p q V A := fun a => by
  have h4 : 4 ≤ 2 ^ e.eval (enc a).length :=
    (Nat.pow_le_pow_right (by norm_num) (he _) : 2 ^ 2 ≤ _)
  constructor
  · intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    simpa only [not_exists, Bool.not_eq_true] using (Nat.mul_le_mul_right _ h4).trans ((h a).1 ha)
  · intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    simpa only [not_forall, Bool.not_eq_false] using
      (Nat.mul_le_mul_right _ h4).trans ((h a).2 ha)

/-- **Error reduction for `AM`** [Babai][Babai1985]: a problem is in `AM` exactly when, for every
polynomial `e`, it has a polynomial-time Arthur–Merlin verifier with error at most
`2 ^ (-e(n))`. -/
theorem mem_AM_iff_forall_errorExponent :
    A ∈ AM enc ↔ ∀ e : Polynomial ℕ, ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsArthurMerlinVerifierWithErrorExponent enc e p q V A := by
  have this : A ∈ AM enc ↔ ∀ e : Polynomial ℕ, ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableTidilyInPolyTime V (encPair enc encBits) encBool ∧
      IsArthurMerlinVerifierWithErrorExponent enc e p q V A := by
    rw [mem_AM]
    refine ⟨fun ⟨p, q, V, hV, h⟩ e => ⟨12 * e * p, 12 * e * q, _,
      (computableInPolyTime_arthurMerlinRepeat hV _ _ _).tidy, h.repeatMajority e⟩, fun h => ?_⟩
    obtain ⟨p, q, V, hV, h⟩ := h 2
    exact ⟨p, q, V, (.of_tidy hV), h.isArthurMerlinVerifier fun _ => by simp⟩
  simpa only [computableInPolyTime_iff_computableTidilyInPolyTime] using this

/-! ### `MA ⊆ AM` -/

/-- **`MA ⊆ AM`** [Babai][Babai1985], [Arora and Barak, Section 8.2][AroraBarak09]. Reduce the
error of a Merlin–Arthur verifier with proofs of `q(n)` bits below `2 ^ (-q(n) - 2)` and let
Arthur send his coins first: on a member the good proof still answers three quarters of the random
strings, and on a non-member, by the union bound over the `2 ^ q(n)` proofs, at most a quarter of
the random strings have an accepted reply. -/
theorem MA_subset_AM : MA enc ⊆ AM enc := by
  rintro A ⟨q, p, V, hV, h⟩
  have h' := h.repeatMajority (q + 2)
  set W := merlinArthurRepeat enc q (6 * (q + 2)) p V with hW
  set P : Polynomial ℕ := 12 * (q + 2) * p with hP
  have hPu : ComputableTidilyInPolyTime (fun a => P.eval (enc a).length) enc encUnary :=
    (ComputableTidilyInPolyTime.unary_eval P).comp (ComputableTidilyInPolyTime.encoding_length enc)
  refine ⟨P, q, fun x => W (x.1, x.2.drop (P.eval (enc x.1).length) ++
    x.2.take (P.eval (enc x.1).length)), ?_, fun a => ?_⟩
  · exact .of_tidy <| (computableInPolyTime_merlinArthurRepeat hV _ _ _).tidy.comp
      ((ComputableTidilyInPolyTime.fst enc encBits).prod
        (.bitsAppend (.bitsDropWithInput (.snd enc encBits) (hPu.comp (.fst enc encBits)))
          (.bitsTakeWithInput (.snd enc encBits) (hPu.comp (.fst enc encBits)))))
  have hswap (r : Fin (P.eval (enc a).length) → Bool) (y : Fin (q.eval (enc a).length) → Bool) :
      (List.ofFn r ++ List.ofFn y).drop (P.eval (enc a).length) ++
          (List.ofFn r ++ List.ofFn y).take (P.eval (enc a).length) =
        List.ofFn y ++ List.ofFn r := by
    rw [List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn]
  simp only [hswap]
  have h4 : 2 ^ (q + 2).eval (enc a).length = 2 ^ q.eval (enc a).length * 4 := by
    simp [pow_add]
  have hpos : 0 < 2 ^ q.eval (enc a).length := by positivity
  constructor
  · -- the good proof answers all but a quarter of the random strings
    intro ha
    obtain ⟨y, hy⟩ := (h' a).1 ha
    rw [h4] at hy
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hsub : #{r : Fin (P.eval (enc a).length) → Bool |
          ¬∃ y' : Fin (q.eval (enc a).length) → Bool, W (a, List.ofFn y' ++ List.ofFn r) = true} ≤
        #{r : Fin (P.eval (enc a).length) → Bool | W (a, List.ofFn y ++ List.ofFn r) = false} :=
      card_le_card fun r hr => mem_filter.2 ⟨mem_univ _, by
        simpa using (not_exists.1 (mem_filter.1 hr).2) y⟩
    refine (Nat.mul_le_mul_left 4 hsub).trans (Nat.le_of_mul_le_mul_left ?_ hpos)
    calc 2 ^ q.eval (enc a).length * (4 * #{r : Fin (P.eval (enc a).length) → Bool |
          W (a, List.ofFn y ++ List.ofFn r) = false})
        = 2 ^ q.eval (enc a).length * 4 * #{r : Fin (P.eval (enc a).length) → Bool |
          W (a, List.ofFn y ++ List.ofFn r) = false} := by ring
      _ ≤ 2 ^ P.eval (enc a).length := hy
      _ ≤ 2 ^ q.eval (enc a).length * 2 ^ P.eval (enc a).length :=
        Nat.le_mul_of_pos_left _ hpos
  · -- by the union bound, at most a quarter of the random strings have an accepted reply
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hunion : #{r : Fin (P.eval (enc a).length) → Bool |
          ¬∀ y : Fin (q.eval (enc a).length) → Bool, W (a, List.ofFn y ++ List.ofFn r) = false} ≤
        ∑ y : Fin (q.eval (enc a).length) → Bool,
          #{r : Fin (P.eval (enc a).length) → Bool | W (a, List.ofFn y ++ List.ofFn r) = true} := by
      refine (card_le_card fun r hr => ?_).trans card_biUnion_le
      obtain ⟨y, hy⟩ := not_forall.1 (mem_filter.1 hr).2
      exact mem_biUnion.2 ⟨y, mem_univ _, mem_filter.2 ⟨mem_univ _, by simpa using hy⟩⟩
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ q.eval (enc a).length * (4 * #{r : Fin (P.eval (enc a).length) → Bool |
          ¬∀ y : Fin (q.eval (enc a).length) → Bool, W (a, List.ofFn y ++ List.ofFn r) = false})
        ≤ 2 ^ (q + 2).eval (enc a).length * ∑ y : Fin (q.eval (enc a).length) → Bool,
          #{r : Fin (P.eval (enc a).length) → Bool | W (a, List.ofFn y ++ List.ofFn r) = true} := by
          rw [h4, mul_assoc]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hunion)
      _ = ∑ y : Fin (q.eval (enc a).length) → Bool, 2 ^ (q + 2).eval (enc a).length *
          #{r : Fin (P.eval (enc a).length) → Bool | W (a, List.ofFn y ++ List.ofFn r) = true} :=
          mul_sum _ _ _
      _ ≤ ∑ _y : Fin (q.eval (enc a).length) → Bool, 2 ^ P.eval (enc a).length :=
          sum_le_sum fun y _ => (h' a).2 ha y
      _ = 2 ^ q.eval (enc a).length * 2 ^ P.eval (enc a).length := by
          rw [sum_const, card_univ, smul_eq_mul, BitString.card]

/-- **`NP ⊆ AM`**. -/
theorem NP_subset_AM : NP enc ⊆ AM enc := NP_subset_MA.trans MA_subset_AM

/-- **`BPP ⊆ AM`**. -/
theorem BPP_subset_AM : BPP enc ⊆ AM enc := BPP_subset_MA.trans MA_subset_AM

/-! ### `MA ⊆ SBP` -/

/-- **`MA ⊆ SBP`** [Böhler, Glaßer and Meister][BoehlerGlasserMeister2006]. Reduce the error of a
Merlin–Arthur verifier with proofs of `q(n)` bits below `2 ^ (-q(n) - 2)` and count the accepted
pairs of a proof and a random string of `P(n)` bits: on a member the good proof alone gives at least
`3 / 4 ⬝ 2 ^ P(n)` of them, and on a non-member all `2 ^ q(n)` proofs together give at most
`1 / 4 ⬝ 2 ^ P(n)`. Four times the count is a `#P` function with threshold `3 ⬝ 2 ^ P(n)`. -/
theorem MA_subset_SBP : MA enc ⊆ SBP enc := by
  rintro A ⟨q, p, V, hV, h⟩
  have h' := h.repeatMajority (q + 2)
  set W := merlinArthurRepeat enc q (6 * (q + 2)) p V with hW
  set P : Polynomial ℕ := 12 * (q + 2) * p with hP
  have hf : (fun a => acceptCount W a ((q + P).eval (enc a).length)) ∈ SharpP enc :=
    ⟨q + P, W, (computableInPolyTime_merlinArthurRepeat hV _ _ _), fun _ => rfl⟩
  have hd : ComputableTidilyInPolyTime (fun a => 2 ^ P.eval (enc a).length) enc encNat :=
    ComputableTidilyInPolyTime.binary_two_pow.comp
      ((ComputableTidilyInPolyTime.unary_eval P).comp (.encoding_length enc))
  refine ⟨_, SharpP.mul_mem (SharpP.natCast_mem 4) hf, fun a => 3 * 2 ^ P.eval (enc a).length,
    .of_tidy ((ComputableTidilyInPolyTime.const 3).binary_mul' hd), fun a => ?_⟩
  change (a ∈ A → 3 * 2 ^ P.eval (enc a).length ≤
      4 * acceptCount W a ((q + P).eval (enc a).length)) ∧
    (a ∉ A → 2 * (4 * acceptCount W a ((q + P).eval (enc a).length)) <
      3 * 2 ^ P.eval (enc a).length)
  rw [Polynomial.eval_add, acceptCount_add]
  have h4 : 2 ^ (q + 2).eval (enc a).length = 2 ^ q.eval (enc a).length * 4 := by
    simp [pow_add]
  have hpos : 0 < 2 ^ q.eval (enc a).length := by positivity
  have hPpos : 0 < 2 ^ P.eval (enc a).length := by positivity
  constructor
  · -- the good proof alone is accepted with three quarters of the random strings
    intro ha
    obtain ⟨y, hy⟩ := (h' a).1 ha
    rw [h4] at hy
    have hsum := acceptCount_add_card_filter_eq_false
      (V := fun x => W (x.1, List.ofFn y ++ x.2)) (a := a) (n := P.eval (enc a).length)
    have hle := single_le_sum (f := fun u : Fin (q.eval (enc a).length) → Bool =>
      acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a (P.eval (enc a).length))
      (fun _ _ => Nat.zero_le _) (mem_univ y)
    have hbad : 4 * #{r : Fin (P.eval (enc a).length) → Bool |
        W (a, List.ofFn y ++ List.ofFn r) = false} ≤ 2 ^ P.eval (enc a).length := by
      refine Nat.le_of_mul_le_mul_left ?_ hpos
      calc 2 ^ q.eval (enc a).length * (4 * #{r : Fin (P.eval (enc a).length) → Bool |
            W (a, List.ofFn y ++ List.ofFn r) = false})
          = 2 ^ q.eval (enc a).length * 4 * #{r : Fin (P.eval (enc a).length) → Bool |
            W (a, List.ofFn y ++ List.ofFn r) = false} := by ring
        _ ≤ 2 ^ P.eval (enc a).length := hy
        _ ≤ 2 ^ q.eval (enc a).length * 2 ^ P.eval (enc a).length :=
          Nat.le_mul_of_pos_left _ hpos
    change acceptCount (fun x => W (x.1, List.ofFn y ++ x.2)) a (P.eval (enc a).length) +
      #{r : Fin (P.eval (enc a).length) → Bool | W (a, List.ofFn y ++ List.ofFn r) = false} =
      2 ^ P.eval (enc a).length at hsum
    omega
  · -- all proofs together are accepted with at most a quarter of the random strings
    intro ha
    have hsum : 2 ^ q.eval (enc a).length * (4 * ∑ u : Fin (q.eval (enc a).length) → Bool,
        acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a (P.eval (enc a).length)) ≤
        2 ^ q.eval (enc a).length * 2 ^ P.eval (enc a).length := by
      calc 2 ^ q.eval (enc a).length * (4 * ∑ u : Fin (q.eval (enc a).length) → Bool,
            acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a (P.eval (enc a).length))
          = ∑ u : Fin (q.eval (enc a).length) → Bool, 2 ^ (q + 2).eval (enc a).length *
            acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a (P.eval (enc a).length) := by
            rw [h4, mul_sum, mul_sum]
            exact sum_congr rfl fun _ _ => by ring
        _ ≤ ∑ _u : Fin (q.eval (enc a).length) → Bool, 2 ^ P.eval (enc a).length :=
            sum_le_sum fun u _ => (h' a).2 ha u
        _ = 2 ^ q.eval (enc a).length * 2 ^ P.eval (enc a).length := by
            rw [sum_const, card_univ, smul_eq_mul, BitString.card]
    have := Nat.le_of_mul_le_mul_left hsum hpos
    omega

/-! ### Existential quantification -/

/-- **`AM` is closed under existential quantification** [Babai][Babai1985]: if the pairs `(a, w)`
form a problem in `AM`, with respect to the encoding of pairs, then so do the instances `a` for
which some word `w` of length `p(n)`, `n` the length of the encoded instance, makes `(a, w)` a
member. -/
theorem mem_AM_of_exists {B : Set (α × List Bool)} (hB : B ∈ AM (encPair enc encBits))
    (p : Polynomial ℕ) :
    {a | ∃ w : List Bool, w.length = p.eval (enc a).length ∧ (a, w) ∈ B} ∈ AM enc := by
  obtain ⟨pB, qB, VB, hVB, hB'⟩ := mem_AM_iff_forall_errorExponent.mp hB (Polynomial.X + 2)
  -- the length of the encoded pair of an instance and a word of length `p(n)`
  set L : Polynomial ℕ := 2 * Polynomial.X + 1 + p with hLdef
  have hL (a : α) (w : List Bool) (hw : w.length = p.eval (enc a).length) :
      (encPair enc encBits (a, w)).length = L.eval (enc a).length := by
    simp only [length_encPair, encBits_apply, hw, hLdef, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_ofNat]
  have hP : ComputableTidilyInPolyTime (fun x : α × List Bool => (pB.comp L).eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval _).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).comp (.fst _ _)
  have hp : ComputableTidilyInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableTidilyInPolyTime.unary_eval _).comp
      (ComputableTidilyInPolyTime.encoding_length enc)).comp (.fst _ _)
  refine ⟨pB.comp L, p + qB.comp L, fun x => VB ((x.1,
      (x.2.drop ((pB.comp L).eval (enc x.1).length)).take (p.eval (enc x.1).length)),
      x.2.take ((pB.comp L).eval (enc x.1).length) ++
        x.2.drop ((pB.comp L).eval (enc x.1).length + p.eval (enc x.1).length)), ?_,
    fun a => ?_⟩
  · exact .of_tidy <| hVB.tidy.comp (((ComputableTidilyInPolyTime.fst _ _).prod
      (ComputableTidilyInPolyTime.bitsTakeWithInput
        (ComputableTidilyInPolyTime.bitsDropWithInput (.snd _ _) hP) hp)).prod
      (ComputableTidilyInPolyTime.bitsAppend
        (ComputableTidilyInPolyTime.bitsTakeWithInput (.snd _ _) hP)
        (ComputableTidilyInPolyTime.bitsDropWithInput (.snd _ _)
          (ComputableTidilyInPolyTime.unary_add.comp (hP.prod hp)))))
  rw [Polynomial.eval_add]
  -- the verifier reads the word and runs the verifier of the pairs
  have hsplit (r : BitString ((pB.comp L).eval (enc a).length))
      (y : BitString (p.eval (enc a).length + (qB.comp L).eval (enc a).length)) :
      VB ((a, ((List.ofFn r ++ List.ofFn y).drop ((pB.comp L).eval (enc a).length)).take
          (p.eval (enc a).length)), (List.ofFn r ++ List.ofFn y).take
            ((pB.comp L).eval (enc a).length) ++ (List.ofFn r ++ List.ofFn y).drop
              ((pB.comp L).eval (enc a).length + p.eval (enc a).length)) =
        VB ((a, List.ofFn ((Fin.appendEquiv _ _).symm y).1),
          List.ofFn r ++ List.ofFn ((Fin.appendEquiv _ _).symm y).2) := by
    rw [List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn,
      List.ofFn_add, List.take_left' List.length_ofFn, ← List.append_assoc,
      List.drop_left' (by simp)]
    rfl
  simp only [hsplit]
  -- the error bounds of the pairs, at the length of the encoded instance
  have herr (w : BitString (p.eval (enc a).length)) :
      ((a, List.ofFn w) ∈ B → 2 ^ (L.eval (enc a).length + 2) *
        #{r : BitString (pB.eval (L.eval (enc a).length)) |
          ∀ y : BitString (qB.eval (L.eval (enc a).length)),
            VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = false} ≤
          2 ^ pB.eval (L.eval (enc a).length)) ∧
      ((a, List.ofFn w) ∉ B → 2 ^ (L.eval (enc a).length + 2) *
        #{r : BitString (pB.eval (L.eval (enc a).length)) |
          ∃ y : BitString (qB.eval (L.eval (enc a).length)),
            VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} ≤
          2 ^ pB.eval (L.eval (enc a).length)) := by
    have h := hB' (a, List.ofFn w)
    rw [hL a _ List.length_ofFn,
      show (Polynomial.X + 2 : Polynomial ℕ).eval (L.eval (enc a).length) =
        L.eval (enc a).length + 2 by simp] at h
    exact h
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  have hLp : p.eval (enc a).length ≤ L.eval (enc a).length := by
    simp [hLdef]
  constructor
  · -- a good word leaves a quarter of the random strings without an accepted answer
    rintro ⟨w, hw, hmem⟩
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hw' : List.ofFn (BitString.ofList _ w) = w := BitString.ofFn_ofList hw
    have hbad := (herr (BitString.ofList _ w)).1 (by rwa [hw'])
    have h4 : 4 ≤ 2 ^ (L.eval (enc a).length + 2) := by
      rw [pow_add]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    refine (Nat.mul_le_mul_left 4 (card_le_card fun r hr => ?_)).trans
      ((Nat.mul_le_mul_right _ h4).trans hbad)
    rw [mem_filter] at hr ⊢
    refine ⟨mem_univ _, fun y => ?_⟩
    have := not_exists.1 hr.2 (Fin.append (BitString.ofList _ w) y)
    simpa [Fin.appendEquiv] using this
  · -- by the union bound over the words, a quarter of the random strings have an accepted answer
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hunion : #{r : BitString (pB.eval (L.eval (enc a).length)) |
        ¬∀ y : BitString (p.eval (enc a).length + qB.eval (L.eval (enc a).length)),
          VB ((a, List.ofFn ((Fin.appendEquiv _ _).symm y).1),
            List.ofFn r ++ List.ofFn ((Fin.appendEquiv _ _).symm y).2) = false} ≤
        ∑ w : BitString (p.eval (enc a).length),
          #{r : BitString (pB.eval (L.eval (enc a).length)) |
            ∃ y : BitString (qB.eval (L.eval (enc a).length)),
              VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} := by
      refine (card_le_card fun r hr => ?_).trans card_biUnion_le
      obtain ⟨y, hy⟩ := not_forall.1 (mem_filter.1 hr).2
      exact mem_biUnion.2 ⟨_, mem_univ _, mem_filter.2 ⟨mem_univ _, _, by simpa using hy⟩⟩
    have hpos : 0 < 2 ^ p.eval (enc a).length := by positivity
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ p.eval (enc a).length * (4 * #{r : BitString (pB.eval (L.eval (enc a).length)) |
          ¬∀ y : BitString (p.eval (enc a).length + qB.eval (L.eval (enc a).length)),
            VB ((a, List.ofFn ((Fin.appendEquiv _ _).symm y).1),
              List.ofFn r ++ List.ofFn ((Fin.appendEquiv _ _).symm y).2) = false})
        ≤ 2 ^ (L.eval (enc a).length + 2) * ∑ w : BitString (p.eval (enc a).length),
          #{r : BitString (pB.eval (L.eval (enc a).length)) |
            ∃ y : BitString (qB.eval (L.eval (enc a).length)),
              VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} := by
          have h4 : 2 ^ p.eval (enc a).length * 4 ≤ 2 ^ (L.eval (enc a).length + 2) := by
            rw [pow_add]
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hLp)
          rw [← mul_assoc]
          exact Nat.mul_le_mul h4 hunion
      _ = ∑ w : BitString (p.eval (enc a).length), 2 ^ (L.eval (enc a).length + 2) *
          #{r : BitString (pB.eval (L.eval (enc a).length)) |
            ∃ y : BitString (qB.eval (L.eval (enc a).length)),
              VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y) = true} := mul_sum _ _ _
      _ ≤ ∑ _w : BitString (p.eval (enc a).length), 2 ^ pB.eval (L.eval (enc a).length) :=
          sum_le_sum fun w _ => (herr w).2 fun hw => ha ⟨_, List.length_ofFn, hw⟩
      _ = 2 ^ p.eval (enc a).length * 2 ^ pB.eval (L.eval (enc a).length) := by
          rw [sum_const, card_univ, smul_eq_mul, BitString.card]

end Cslib.Complexity
