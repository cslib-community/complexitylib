/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.ArthurMerlin
public import Complexity.Computability.Complexity.Classes.BPP.Amplification
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
* `Cslib.Complexity.isArthurMerlinVerifierWithErrorExponent_iff_decidesWithErrorExponent`,
  `Cslib.Complexity.IsArthurMerlinVerifier.repeatMajority`,
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
  ∀ a, (a ∈ A → ∃ y : Fin (q.eval (enc a).length) → Bool,
      ErrorExponentAt enc e p (fun z => V (z.1, List.ofFn y ++ z.2)) a true) ∧
    (a ∉ A → ∀ y : Fin (q.eval (enc a).length) → Bool,
      ErrorExponentAt enc e p (fun z => V (z.1, List.ofFn y ++ z.2)) a false)

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
  unfold merlinArthurRepeat repeatMajority repeatVotes
  fun_prop

/-- On a proof of length `q(n)` followed by a random string `w`, `merlinArthurRepeat` is
`repeatMajority` with that proof fixed. -/
private theorem merlinArthurRepeat_ofFn_append {q r p : Polynomial ℕ}
    {V : α × List Bool → Bool}
    (a : α) (y : Fin (q.eval (enc a).length) → Bool) (w : List Bool) :
    merlinArthurRepeat enc q r p V (a, List.ofFn y ++ w) =
      repeatMajority enc r p (fun z => V (z.1, List.ofFn y ++ z.2)) (a, w) := by
  rw [merlinArthurRepeat, List.take_left' List.length_ofFn, List.drop_left' List.length_ofFn]

/-- **Error reduction for `MA`** [Babai][Babai1985]. The strict majority of `12 e(n)` runs of a
Merlin–Arthur verifier with one proof, on independent blocks of random bits, errs on at most a
`2 ^ (-e(n))` fraction of the random strings. The proofs keep their length. -/
theorem IsMerlinArthurVerifier.repeatMajority {q p : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : IsMerlinArthurVerifier enc q p V A) (e : Polynomial ℕ) :
    IsMerlinArthurVerifierWithErrorExponent enc e q (12 * e * p)
      (merlinArthurRepeat enc q (6 * e) p V) A :=
  fun a => ⟨fun ha => let ⟨y, hy⟩ := (h a).1 ha
      ⟨y, (hy.repeatMajority e).congr fun _ => (merlinArthurRepeat_ofFn_append a y _).symm⟩,
    fun ha y => (((h a).2 ha y).repeatMajority e).congr fun _ =>
      (merlinArthurRepeat_ofFn_append a y _).symm⟩

/-- Error at most `2 ^ (-e(n)) ≤ 1 / 4` is error at most `1 / 3`. -/
theorem IsMerlinArthurVerifierWithErrorExponent.isMerlinArthurVerifier {e q p : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : IsMerlinArthurVerifierWithErrorExponent enc e q p V A)
    (he : ∀ n, 2 ≤ e.eval n) : IsMerlinArthurVerifier enc q p V A :=
  fun a => ⟨fun ha => let ⟨y, hy⟩ := (h a).1 ha; ⟨y, hy.boundedErrorAt (he _)⟩,
    fun ha y => ((h a).2 ha y).boundedErrorAt (he _)⟩

/-- **Error reduction for `MA`** [Babai][Babai1985]: a problem is in `MA` exactly when, for some
polynomial proof length `q` and every polynomial `e`, it has a polynomial-time Merlin–Arthur
verifier with proofs of length `q` and error at most `2 ^ (-e(n))`. The proof length is chosen
before the error, so the error can be made smaller than `2 ^ (-q(n))`. -/
theorem mem_MA_iff_exists_forall_errorExponent :
    A ∈ MA enc ↔ ∃ q : Polynomial ℕ, ∀ e : Polynomial ℕ, ∃ (p : Polynomial ℕ)
      (V : α × List Bool → Bool), ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsMerlinArthurVerifierWithErrorExponent enc e q p V A :=
  ⟨fun ⟨q, p, V, hV, h⟩ => ⟨q, fun e => ⟨12 * e * p, _,
      computableInPolyTime_merlinArthurRepeat hV _ _ _, h.repeatMajority e⟩⟩,
    fun ⟨q, h⟩ => let ⟨p, V, hV, h⟩ := h 2
      ⟨q, p, V, hV, h.isMerlinArthurVerifier fun _ => by simp⟩⟩

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

/-- An Arthur–Merlin verifier has error exponent `e` iff its reply-existence slice decides with
error exponent `e`. -/
theorem isArthurMerlinVerifierWithErrorExponent_iff_decidesWithErrorExponent
    {e p q : Polynomial ℕ} {V : α × List Bool → Bool} :
    IsArthurMerlinVerifierWithErrorExponent enc e p q V A ↔
      DecidesWithErrorExponent enc e p (arthurMerlinSlice enc q V) A := by
  simp only [IsArthurMerlinVerifierWithErrorExponent, DecidesWithErrorExponent,
    PromiseProblem.SolvesWithErrorExponent, ErrorExponentAt, Bool.not_true, Bool.not_false,
    arthurMerlinSlice, decide_eq_true_iff, decide_eq_false_iff_not, not_exists, Bool.not_eq_true]
  rfl

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

private theorem arthurMerlinSlice_arthurMerlinRepeat {e p q : Polynomial ℕ}
    {V : α × List Bool → Bool} (a : α)
    (x : Fin ((12 * e * p).eval (enc a).length) → Bool) :
    repeatMajority enc (6 * e) p (arthurMerlinSlice enc q V) (a, List.ofFn x) =
      arthurMerlinSlice enc (12 * e * q) (arthurMerlinRepeat enc (6 * e) p q V)
        (a, List.ofFn x) := by
  have hlen (s : Polynomial ℕ) : (12 * e * s).eval (enc a).length =
      2 * (6 * e).eval (enc a).length * s.eval (enc a).length := by
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat]
    ring
  revert x
  rw [hlen p]
  intro x
  rw [repeatMajority_ofFn, arthurMerlinSlice, hlen q]
  simp only [arthurMerlinSlice, decide_eq_true_iff,
    exists_arthurMerlinRepeat_ofFn_append_ofFn_iff]

/-- **Error reduction for `AM`** [Babai][Babai1985]. The strict majority of `12 e(n)` parallel runs
of an Arthur–Merlin verifier, on independent blocks of random bits answered independently, errs on
at most a `2 ^ (-e(n))` fraction of the random strings. -/
theorem IsArthurMerlinVerifier.repeatMajority {p q : Polynomial ℕ} {V : α × List Bool → Bool}
    (h : IsArthurMerlinVerifier enc p q V A) (e : Polynomial ℕ) :
    IsArthurMerlinVerifierWithErrorExponent enc e (12 * e * p) (12 * e * q)
      (arthurMerlinRepeat enc (6 * e) p q V) A := by
  rw [isArthurMerlinVerifierWithErrorExponent_iff_decidesWithErrorExponent]
  have h' := (isArthurMerlinVerifier_iff_decidesWithBoundedError.1 h).repeatMajority e
  exact fun a => ⟨fun ha => ((h' a).1 ha).congr (arthurMerlinSlice_arthurMerlinRepeat a),
    fun ha => ((h' a).2 ha).congr (arthurMerlinSlice_arthurMerlinRepeat a)⟩

/-- Error at most `2 ^ (-e(n)) ≤ 1 / 4` is error at most `1 / 3`. -/
theorem IsArthurMerlinVerifierWithErrorExponent.isArthurMerlinVerifier {e p q : Polynomial ℕ}
    {V : α × List Bool → Bool} (h : IsArthurMerlinVerifierWithErrorExponent enc e p q V A)
    (he : ∀ n, 2 ≤ e.eval n) : IsArthurMerlinVerifier enc p q V A :=
  isArthurMerlinVerifier_iff_decidesWithBoundedError.2
    ((isArthurMerlinVerifierWithErrorExponent_iff_decidesWithErrorExponent.1
      h).solvesWithBoundedError he)

/-- **Error reduction for `AM`** [Babai][Babai1985]: a problem is in `AM` exactly when, for every
polynomial `e`, it has a polynomial-time Arthur–Merlin verifier with error at most
`2 ^ (-e(n))`. -/
theorem mem_AM_iff_forall_errorExponent :
    A ∈ AM enc ↔ ∀ e : Polynomial ℕ, ∃ (p q : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsArthurMerlinVerifierWithErrorExponent enc e p q V A :=
  ⟨fun ⟨p, q, V, hV, h⟩ e => ⟨12 * e * p, 12 * e * q, _,
      computableInPolyTime_arthurMerlinRepeat hV _ _ _, h.repeatMajority e⟩,
    fun h => let ⟨p, q, V, hV, h⟩ := h 2
      ⟨p, q, V, hV, h.isArthurMerlinVerifier fun _ => by simp⟩⟩

/-! ### `MA ⊆ AM` -/

/-- If every `y : BitString Q` accepts at most a `2 ^ -(Q + 2)` fraction of `r : BitString P`, then
at most a quarter of `r : BitString P` have some accepted `y`. -/
private theorem four_mul_card_filter_not_forall_eq_false_le {P Q : ℕ}
    {f : BitString Q → BitString P → Bool}
    (hf : ∀ y, 2 ^ (Q + 2) * #{r : BitString P | f y r = true} ≤ 2 ^ P) :
    4 * #{r : BitString P | ¬∀ y, f y r = false} ≤ 2 ^ P := by
  have hunion : #{r : BitString P | ¬∀ y, f y r = false} ≤
      ∑ y : BitString Q, #{r : BitString P | f y r = true} := by
    refine (card_le_card fun r hr => ?_).trans card_biUnion_le
    obtain ⟨y, hy⟩ := not_forall.1 (mem_filter.1 hr).2
    exact mem_biUnion.2 ⟨y, mem_univ _, mem_filter.2 ⟨mem_univ _, by simpa using hy⟩⟩
  have hpos : 0 < 2 ^ Q := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  calc 2 ^ Q * (4 * #{r : BitString P | ¬∀ y, f y r = false})
      ≤ 2 ^ (Q + 2) * ∑ y : BitString Q, #{r : BitString P | f y r = true} := by
        rw [pow_add, mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hunion)
    _ = ∑ y : BitString Q, 2 ^ (Q + 2) * #{r : BitString P | f y r = true} := mul_sum _ _ _
    _ ≤ ∑ _y : BitString Q, 2 ^ P := sum_le_sum fun y _ => hf y
    _ = 2 ^ Q * 2 ^ P := by rw [sum_const, card_univ, smul_eq_mul, BitString.card]

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
  have hPu : ComputableInPolyTime (fun a => P.eval (enc a).length) enc encUnary :=
    (ComputableInPolyTime.unary_eval P).comp (ComputableInPolyTime.encoding_length enc)
  refine ⟨P, q, fun x => W (x.1, x.2.drop (P.eval (enc x.1).length) ++
    x.2.take (P.eval (enc x.1).length)), ?_, fun a => ?_⟩
  · exact (computableInPolyTime_merlinArthurRepeat hV _ _ _).comp
      ((ComputableInPolyTime.fst enc encBits).prod
        (.bitsAppend (.bitsDropWithInput (.snd enc encBits) (hPu.comp (.fst enc encBits)))
          (.bitsTakeWithInput (.snd enc encBits) (hPu.comp (.fst enc encBits)))))
  have hswap (r : Fin (P.eval (enc a).length) → Bool) (y : Fin (q.eval (enc a).length) → Bool) :
      (List.ofFn r ++ List.ofFn y).drop (P.eval (enc a).length) ++
          (List.ofFn r ++ List.ofFn y).take (P.eval (enc a).length) =
        List.ofFn y ++ List.ofFn r := by
    rw [List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn]
  simp only [hswap]
  have h4 : 4 ≤ 2 ^ (q + 2).eval (enc a).length := by
    simp only [Polynomial.eval_add, Polynomial.eval_ofNat, pow_add]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  constructor
  · -- the good proof answers all but a quarter of the random strings
    intro ha
    obtain ⟨y, hy⟩ := (h' a).1 ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hsub : #{r : Fin (P.eval (enc a).length) → Bool |
          ¬∃ y' : Fin (q.eval (enc a).length) → Bool, W (a, List.ofFn y' ++ List.ofFn r) = true} ≤
        #{r : Fin (P.eval (enc a).length) → Bool | W (a, List.ofFn y ++ List.ofFn r) = false} :=
      card_le_card fun r hr => mem_filter.2 ⟨mem_univ _, by
        simpa using (not_exists.1 (mem_filter.1 hr).2) y⟩
    exact (Nat.mul_le_mul_left 4 hsub).trans ((Nat.mul_le_mul_right _ h4).trans hy)
  · -- by the union bound, at most a quarter of the random strings have an accepted reply
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    exact four_mul_card_filter_not_forall_eq_false_le fun y => by
      simpa [Polynomial.eval_add] using (h' a).2 ha y

/-- **`NP ⊆ AM`**. -/
theorem NP_subset_AM : NP enc ⊆ AM enc := NP_subset_MA.trans MA_subset_AM

/-- **`BPP ⊆ AM`**. -/
theorem BPP_subset_AM : BPP enc ⊆ AM enc := BPP_subset_MA.trans MA_subset_AM

/-! ### `MA ⊆ SBP` -/

/-- If some proof `y : BitString Q` fails on at most a `2 ^ -(Q + 2)` fraction of random strings,
then four times the total accepted pairs is at least `3 * 2 ^ P`. -/
private theorem three_mul_two_pow_le_four_mul_sum {P Q : ℕ} (W : α × List Bool → Bool) (a : α)
    (y : BitString Q)
    (hy : 2 ^ (Q + 2) * #{r : BitString P | W (a, List.ofFn y ++ List.ofFn r) = false} ≤ 2 ^ P) :
    3 * 2 ^ P ≤ 4 * ∑ u : BitString Q, acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a P := by
  have hsum : acceptCount (fun x => W (x.1, List.ofFn y ++ x.2)) a P +
      #{r : BitString P | W (a, List.ofFn y ++ List.ofFn r) = false} = 2 ^ P :=
    acceptCount_add_card_filter_eq_false
      (V := fun x => W (x.1, List.ofFn y ++ x.2)) (a := a) (n := P)
  have hle := single_le_sum (f := fun u : BitString Q =>
    acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a P)
    (fun _ _ => Nat.zero_le _) (mem_univ y)
  have hbad : 4 * #{r : BitString P | W (a, List.ofFn y ++ List.ofFn r) = false} ≤ 2 ^ P :=
    (Nat.mul_le_mul_right _
      (by rw [pow_add]; exact Nat.le_mul_of_pos_left _ (by positivity))).trans hy
  omega

/-- If each of the `2 ^ Q` proofs is accepted on at most `2 ^ (P - (Q + 2))` random strings, then
twice four times the total accepted pairs is strictly below `3 * 2 ^ P`. -/
private theorem two_mul_four_mul_sum_lt {P Q : ℕ} {f : BitString Q → ℕ}
    (hf : ∀ u, 2 ^ (Q + 2) * f u ≤ 2 ^ P) :
    2 * (4 * ∑ u : BitString Q, f u) < 3 * 2 ^ P := by
  have hpos : 0 < 2 ^ Q := by positivity
  have hPpos : 0 < 2 ^ P := by positivity
  have hle : 4 * ∑ u : BitString Q, f u ≤ 2 ^ P := by
    refine Nat.le_of_mul_le_mul_left ?_ hpos
    calc 2 ^ Q * (4 * ∑ u : BitString Q, f u)
        = ∑ u : BitString Q, 2 ^ (Q + 2) * f u := by
          rw [pow_add, mul_sum, mul_sum]
          exact sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ _u : BitString Q, 2 ^ P := sum_le_sum fun u _ => hf u
      _ = 2 ^ Q * 2 ^ P := by rw [sum_const, card_univ, smul_eq_mul, BitString.card]
  omega

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
  have hd : ComputableInPolyTime (fun a => 2 ^ P.eval (enc a).length) enc encNat :=
    ComputableInPolyTime.binary_two_pow.comp
      ((ComputableInPolyTime.unary_eval P).comp (.encoding_length enc))
  refine ⟨_, SharpP.mul_mem (SharpP.natCast_mem 4) hf, fun a => 3 * 2 ^ P.eval (enc a).length,
    ((ComputableInPolyTime.const 3).binary_mul' hd), fun a => ?_⟩
  change (a ∈ A → 3 * 2 ^ P.eval (enc a).length ≤
      4 * acceptCount W a ((q + P).eval (enc a).length)) ∧
    (a ∉ A → 2 * (4 * acceptCount W a ((q + P).eval (enc a).length)) <
      3 * 2 ^ P.eval (enc a).length)
  rw [Polynomial.eval_add, acceptCount_add]
  constructor
  · -- the good proof alone is accepted with three quarters of the random strings
    intro ha
    obtain ⟨y, hy⟩ := (h' a).1 ha
    dsimp only [ErrorExponentAt, Bool.not_true] at hy
    rw [Polynomial.eval_add, Polynomial.eval_ofNat] at hy
    exact three_mul_two_pow_le_four_mul_sum W a y hy
  · -- all proofs together are accepted with at most a quarter of the random strings
    intro ha
    refine two_mul_four_mul_sum_lt
      (f := fun u : Fin (q.eval (enc a).length) → Bool =>
        acceptCount (fun x => W (x.1, List.ofFn u ++ x.2)) a (P.eval (enc a).length))
      fun u => ?_
    simpa only [ErrorExponentAt, Bool.not_false, acceptCount, Polynomial.eval_add,
      Polynomial.eval_ofNat] using (h' a).2 ha u

/-! ### Existential quantification -/

/-- The verifier for existential quantification over words of length `p(n)` before an `AM`
verifier `VB` is computable in polynomial time. -/
private theorem computableInPolyTime_existsAMVerifier {VB : (α × List Bool) × List Bool → Bool}
    (hVB : ComputableInPolyTime VB (encPair (encPair enc encBits) encBits) encBool)
    (P p : Polynomial ℕ) :
    ComputableInPolyTime (fun x : α × List Bool => VB ((x.1,
      (x.2.drop (P.eval (enc x.1).length)).take (p.eval (enc x.1).length)),
      x.2.take (P.eval (enc x.1).length) ++
        x.2.drop (P.eval (enc x.1).length + p.eval (enc x.1).length)))
      (encPair enc encBits) encBool := by
  have hP : ComputableInPolyTime (fun x : α × List Bool => P.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableInPolyTime.unary_eval _).comp
      (ComputableInPolyTime.encoding_length enc)).comp (.fst _ _)
  have hp : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
      (encPair enc encBits) encUnary :=
    ((ComputableInPolyTime.unary_eval _).comp
      (ComputableInPolyTime.encoding_length enc)).comp (.fst _ _)
  exact hVB.comp (((ComputableInPolyTime.fst _ _).prod
    (ComputableInPolyTime.bitsTakeWithInput
      (ComputableInPolyTime.bitsDropWithInput (.snd _ _) hP) hp)).prod
    (ComputableInPolyTime.bitsAppend
      (ComputableInPolyTime.bitsTakeWithInput (.snd _ _) hP)
      (ComputableInPolyTime.bitsDropWithInput (.snd _ _)
        (ComputableInPolyTime.unary_add.comp (hP.prod hp)))))

/-- On `List.ofFn r ++ List.ofFn y`, the existential `AM` verifier extracts the first component of
`y` as the word and passes `r` followed by the second component of `y` to `VB`. -/
private theorem existsAMVerifier_ofFn_append (VB : (α × List Bool) × List Bool → Bool) (a : α)
    {P W Q : ℕ} (r : BitString P) (y : BitString (W + Q)) :
    VB ((a, ((List.ofFn r ++ List.ofFn y).drop P).take W),
      (List.ofFn r ++ List.ofFn y).take P ++ (List.ofFn r ++ List.ofFn y).drop (P + W)) =
      VB ((a, List.ofFn ((Fin.appendEquiv W Q).symm y).1),
        List.ofFn r ++ List.ofFn ((Fin.appendEquiv W Q).symm y).2) := by
  -- the verifier reads the word and runs the verifier of the pairs
  rw [List.drop_left' List.length_ofFn, List.take_left' List.length_ofFn,
     List.ofFn_add, List.take_left' List.length_ofFn, ← List.append_assoc,
     List.drop_left' (by simp)]
  rfl

/-- Completeness for existential `AM`: if `w : BitString W` fails on at most a `2 ^ -(E + 2)`
fraction of `r : BitString P`, then the existential verifier fails on at most a quarter of `r`. -/
private theorem four_mul_card_filter_not_exists_word_le {P W Q E : ℕ}
    {f : BitString W → BitString P → BitString Q → Bool} (w : BitString W)
    (hw : 2 ^ (E + 2) * #{r : BitString P | ∀ y, f w r y = false} ≤ 2 ^ P) :
    4 * #{r : BitString P | ¬∃ y : BitString (W + Q),
      f ((Fin.appendEquiv W Q).symm y).1 r ((Fin.appendEquiv W Q).symm y).2 = true} ≤ 2 ^ P := by
  have h4 : 4 ≤ 2 ^ (E + 2) := by
    rw [pow_add]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  refine (Nat.mul_le_mul_left 4 (card_le_card fun r hr => ?_)).trans
    ((Nat.mul_le_mul_right _ h4).trans hw)
  rw [mem_filter] at hr ⊢
  refine ⟨mem_univ _, fun y => ?_⟩
  simpa [Fin.appendEquiv] using not_exists.1 hr.2 (Fin.append w y)

/-- Union bound over `w : BitString W` and certificates `y : BitString Q` for existential `AM`
soundness. -/
private theorem four_mul_card_filter_exists_word_le {P W Q E : ℕ}
    {f : BitString W → BitString P → BitString Q → Bool} (hWE : W ≤ E)
    (hf : ∀ w, 2 ^ (E + 2) * #{r : BitString P | ∃ y, f w r y = true} ≤ 2 ^ P) :
    4 * #{r : BitString P | ¬∀ y : BitString (W + Q),
      f ((Fin.appendEquiv W Q).symm y).1 r ((Fin.appendEquiv W Q).symm y).2 = false} ≤ 2 ^ P := by
  have hunion : #{r : BitString P | ¬∀ y : BitString (W + Q),
      f ((Fin.appendEquiv W Q).symm y).1 r ((Fin.appendEquiv W Q).symm y).2 = false} ≤
      ∑ w : BitString W, #{r : BitString P | ∃ y, f w r y = true} := by
    refine (card_le_card fun r hr => ?_).trans card_biUnion_le
    obtain ⟨y, hy⟩ := not_forall.1 (mem_filter.1 hr).2
    exact mem_biUnion.2 ⟨_, mem_univ _, mem_filter.2 ⟨mem_univ _, _, by simpa using hy⟩⟩
  have hpos : 0 < 2 ^ W := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hpos
  have h4 : 2 ^ W * 4 ≤ 2 ^ (E + 2) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hWE)
  calc 2 ^ W * (4 * #{r : BitString P | ¬∀ y : BitString (W + Q),
        f ((Fin.appendEquiv W Q).symm y).1 r ((Fin.appendEquiv W Q).symm y).2 = false})
      ≤ 2 ^ (E + 2) * ∑ w : BitString W, #{r : BitString P | ∃ y, f w r y = true} := by
        rw [← mul_assoc]
        exact Nat.mul_le_mul h4 hunion
    _ = ∑ w : BitString W, 2 ^ (E + 2) * #{r : BitString P | ∃ y, f w r y = true} :=
        mul_sum _ _ _
    _ ≤ ∑ _w : BitString W, 2 ^ P := sum_le_sum fun w _ => hf w
    _ = 2 ^ W * 2 ^ P := by rw [sum_const, card_univ, smul_eq_mul, BitString.card]

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
  refine ⟨pB.comp L, p + qB.comp L, fun x => VB ((x.1,
      (x.2.drop ((pB.comp L).eval (enc x.1).length)).take (p.eval (enc x.1).length)),
      x.2.take ((pB.comp L).eval (enc x.1).length) ++
        x.2.drop ((pB.comp L).eval (enc x.1).length + p.eval (enc x.1).length)),
      computableInPolyTime_existsAMVerifier hVB (pB.comp L) p, fun a => ?_⟩
  -- the verifier reads the word and runs the verifier of the pairs
  rw [Polynomial.eval_add]
  simp only [existsAMVerifier_ofFn_append]
  -- the error bounds of the pairs, at the length of the encoded instance
  have herr (w : BitString (p.eval (enc a).length)) := by
    have h := hB' (a, List.ofFn w)
    rw [hL a _ List.length_ofFn,
      show (Polynomial.X + 2 : Polynomial ℕ).eval (L.eval (enc a).length) =
        L.eval (enc a).length + 2 by simp] at h
    exact h
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  constructor
  · -- a good word leaves a quarter of the random strings without an accepted answer
    rintro ⟨w, hw, hmem⟩
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    have hw' : List.ofFn (BitString.ofList _ w) = w := BitString.ofFn_ofList hw
    exact four_mul_card_filter_not_exists_word_le
      (f := fun w r y => VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y))
      (BitString.ofList _ w) ((herr (BitString.ofList _ w)).1 (by rwa [hw']))
  · -- by the union bound over the words, a quarter of the random strings have an accepted answer
    intro ha
    refine BitString.two_mul_two_pow_le_of_four_mul_card_filter_not_le _ ?_
    exact four_mul_card_filter_exists_word_le
      (f := fun w r y => VB ((a, List.ofFn w), List.ofFn r ++ List.ofFn y))
      (E := L.eval (enc a).length) (by simp [hLdef])
      fun w => (herr w).2 fun hw => ha ⟨_, List.length_ofFn, hw⟩

end Cslib.Complexity
