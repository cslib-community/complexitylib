/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Advice
import CslibFrontier.Computability.Complexity.Classes.P.Countable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import Mathlib.Data.Fintype.Card

/-!
# Comparing arbitrary exact advice lengths

Exact advice length itself can carry information when the bound is not computable. There
are polynomially bounded `lower` and `gap`, with unbounded `gap` and `lower + gap ≤ 2 ^ n`,
for which `PWithAdvice lower` is not contained in `PWithAdvice (lower + gap)`. The lower
advice has length zero or one; at selected odd lengths, its three possible code words give
three different output patterns, while the upper schedule allows exactly one bit and only
two patterns per fixed decider. Countability diagonalizes against every polynomial-time
decider. No efficient construction of these lower bounds or advice families is claimed.

This qualifies a reading of the displayed arbitrary-gap hypotheses in Goldreich's January
2007 draft Exercise 3.3 (PDF16/printed132) and Theorem 4.1 (PDF22/printed138)
[Goldreich2007DraftR2]. Their displayed hypotheses allow an unbounded gap to vanish; prose
following Theorem 3.7 also writes a positive difference, which may express the intended extra
condition. This is a model qualification, not a claim that every advice hierarchy is false.

The author's official fixed-one-bit addendum [GoldreichAdviceHierarchyAddendum] is separate.
`PWithAdvice_subset_succ` proves its safe inclusion direction by appending one bit and
removing the final advice bit, without computing the length bound. More generally,
`PWithAdvice_subset_of_lt` proves inclusion for every strictly larger bound using a delimiter
and arbitrary false padding. Strict fixed-gap separation and general positive-gap strict
hierarchy results are not proved here.

## Main results

* `Cslib.Complexity.PWithAdvice_subset_of_lt`: strictly more advice preserves the class.
* `Cslib.Complexity.PWithAdvice_subset_succ`: one extra bit preserves exact-length advice.
* `Cslib.Complexity.exists_nonmonotone_advice_bounds`: an unbounded nonnegative gap does not
  suffice for monotonicity of arbitrary exact-length advice classes.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

private def pattern (c : Fin 3) : Bool × Bool :=
  if c = 0 then (false, false) else if c = 1 then (true, true) else (false, true)

private theorem pattern_injective : Function.Injective pattern := by decide

private theorem exists_avoiding_pattern (g : Bool → Bool × Bool) :
    ∃ c : Fin 3, ∀ b, pattern c ≠ g b := by
  classical
  by_contra! h
  choose f hf using h
  have hinj : Function.Injective f := fun c d hcd =>
    pattern_injective ((hf c).trans ((congrArg g hcd).trans (hf d).symm))
  have hcard := Fintype.card_le_of_injective f hinj
  simp at hcard

private def patternCode (c : Fin 3) : List Bool :=
  if c = 0 then [] else if c = 1 then [false] else [true]

private theorem length_patternCode (c : Fin 3) : (patternCode c).length ≤ 1 := by
  fin_cases c <;> decide

private def decodePattern (p : List Bool × List Bool) : Bool :=
  if p.1.isEmpty then false else if p.1.headD false then p.2.headD false else true

private theorem computableInPolyTime_decodePattern :
    ComputableInPolyTime decodePattern (encPair encBits encBits) encBool := by
  have he : ComputableInPolyTime (List.isEmpty (α := Bool)) encBits encBool :=
    .of_tidy ComputableTidilyInPolyTime.bitsIsEmpty
  unfold decodePattern
  fun_prop

private theorem decodePattern_code (c : Fin 3) (x : List Bool) :
    decodePattern (patternCode c, x) =
      if x.headD false then (pattern c).2 else (pattern c).1 := by
  fin_cases c <;> cases x with
  | nil => rfl
  | cons b xs => cases b <;> rfl

/-- Strict pointwise growth preserves exact advice classes, even for noncomputable bounds.
A final `true` marks the old advice; trailing `false` padding fills the new length. Binary
normalization strips the padding, and removing the marker recovers the original advice. -/
theorem PWithAdvice_subset_of_lt {lower upper : ℕ → ℕ} (hlt : ∀ n, lower n < upper n) :
    PWithAdvice lower ⊆ PWithAdvice upper := by
  rintro L ⟨advice, hlength, A, ⟨v, hv, hvA⟩, hL⟩
  let trim : List Bool × List Bool → List Bool × List Bool :=
    fun p => ((encNat (ofBits p.1)).reverse.tail.reverse, p.2)
  have hn : ComputableInPolyTime (fun w => encNat (ofBits w)) encBits encBits :=
    ComputableInPolyTime.bitsToNat.of_enc_eq (fun _ => rfl)
  have ht : ComputableInPolyTime trim (encPair encBits encBits) (encPair encBits encBits) := by
    dsimp only [trim]
    fun_prop
  have htrim (w : List Bool) (k : ℕ) :
      (encNat (ofBits (w ++ [true] ++ List.replicate k false))).reverse.tail.reverse = w := by
    rw [encNat_apply, bits_ofBits]
    induction k with
    | zero => simp
    | succ k ih =>
      simpa only [List.replicate_succ', ← List.append_assoc,
        List.rdropWhile_concat_pos (fun b : Bool => !b) _ false (by decide)] using ih
  refine ⟨fun n => advice n ++ [true] ++ List.replicate (upper n - lower n - 1) false,
    ?_, {p | v (trim p) = true}, ?_, ?_⟩
  · intro n
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate,
      hlength]
    have := hlt n
    omega
  · exact ⟨fun p => v (trim p), hv.comp ht, fun _ => Iff.rfl⟩
  · intro x
    change x ∈ L ↔ v (trim (advice x.length ++ [true] ++
      List.replicate (upper x.length - lower x.length - 1) false, x)) = true
    rw [hL x, hvA]
    simp only [trim, htrim]

/-- One extra advice bit preserves the class without requiring the length bound to be
computable. This is the zero-padding case of delimiter padding. -/
theorem PWithAdvice_subset_succ (length : ℕ → ℕ) :
    PWithAdvice length ⊆ PWithAdvice (fun n => length n + 1) :=
  PWithAdvice_subset_of_lt (fun _ => Nat.lt_succ_self _)

/-- Arbitrary exact advice-length classes need not be monotone, even for polynomial bounds
and an unbounded additive gap. The gap here vanishes at some lengths; this is not a
counterexample to a strictly positive-gap hierarchy. -/
theorem exists_nonmonotone_advice_bounds :
    ∃ (lower gap : ℕ → ℕ) (L : Set (List Bool)),
      PolynomiallyBounded lower ∧ PolynomiallyBounded gap ∧
      (∀ n, lower n < 2 ^ (n - 1)) ∧
      (∀ n, lower n + gap n ≤ 2 ^ n) ∧
      (∀ b, ∃ n, b < gap n) ∧
      L ∈ PWithAdvice lower ∧ L ∉ PWithAdvice (fun n => lower n + gap n) := by
  classical
  obtain ⟨predicates, hpredicates⟩ :=
    (countable_P (encPair encBits encBits)).exists_eq_range ⟨∅, empty_mem_P⟩
  let observations : ℕ → Bool → Bool × Bool := fun j b =>
    (decide (([b], List.replicate (2 * j + 3) false) ∈ predicates j),
      decide (([b], List.replicate (2 * j + 3) true) ∈ predicates j))
  choose color hcolor using fun j => exists_avoiding_pattern (observations j)
  let advice : ℕ → List Bool := fun n =>
    if n % 2 = 1 ∧ 3 ≤ n then patternCode (color ((n - 3) / 2)) else []
  let lower : ℕ → ℕ := fun n => (advice n).length
  let upper : ℕ → ℕ := fun n => if n % 2 = 0 then n else 1
  let gap : ℕ → ℕ := fun n => upper n - lower n
  let L : Set (List Bool) := {x | decodePattern (advice x.length, x) = true}
  have hlow : ∀ n, lower n ≤ 1 := by
    intro n
    dsimp only [lower, advice]
    split_ifs
    · exact length_patternCode _
    · decide
  have heven : ∀ n, n % 2 = 0 → advice n = [] := by
    intro n hn
    simp [advice, hn]
  have hle : ∀ n, lower n ≤ upper n := by
    intro n
    by_cases hn : n % 2 = 0
    · simp [lower, upper, heven n hn, hn]
    · simpa [upper, hn] using hlow n
  have hsum : (fun n => lower n + gap n) = upper := by
    funext n
    exact Nat.add_sub_of_le (hle n)
  have hu : ∀ n, upper n ≤ n + 1 := by
    intro n
    dsimp only [upper]
    split_ifs <;> omega
  have hlowPoly : PolynomiallyBounded lower :=
    (show PolynomiallyBounded (fun _ : ℕ => 1) by fun_prop).mono_of_le hlow
  have hgapPoly : PolynomiallyBounded gap :=
    (show PolynomiallyBounded (fun n : ℕ => n + 1) by fun_prop).mono_of_le
      (fun n => (Nat.sub_le _ _).trans (hu n))
  have hcap : ∀ n, lower n < 2 ^ (n - 1) := by
    intro n
    by_cases hn : n % 2 = 1 ∧ 3 ≤ n
    · have hp : 2 ≤ 2 ^ (n - 1) := by
        simpa using Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ n - 1)
      exact (hlow n).trans_lt ((by decide : 1 < 2).trans_le hp)
    · have hz : lower n = 0 := by simp [lower, advice, hn]
      rw [hz]
      exact Nat.two_pow_pos _
  have hupperPow : ∀ n, upper n ≤ 2 ^ n := by
    intro n
    dsimp only [upper]
    split_ifs
    · exact (Nat.lt_two_pow_self (n := n)).le
    · exact Nat.two_pow_pos n
  have hunbounded : ∀ b, ∃ n, b < gap n := by
    intro b
    let n := 2 * (b + 1)
    have hn : n % 2 = 0 := by dsimp [n]; omega
    refine ⟨n, ?_⟩
    have hz : lower n = 0 := by simp [lower, heven n hn]
    simp only [gap, upper, hn, ↓reduceIte, hz, Nat.sub_zero]
    dsimp [n]
    omega
  have hL : L ∈ PWithAdvice lower := by
    exact ⟨advice, fun _ => rfl, {p | decodePattern p = true},
      ⟨decodePattern, computableInPolyTime_decodePattern, fun _ => Iff.rfl⟩,
      fun _ => Iff.rfl⟩
  have hnot : L ∉ PWithAdvice upper := by
    rintro ⟨otherAdvice, hlength, A, hA, hLA⟩
    rw [hpredicates] at hA
    obtain ⟨j, hj⟩ := hA
    let n := 2 * j + 3
    have hodd : n % 2 = 1 := by dsimp [n]; omega
    have hge : 3 ≤ n := by dsimp [n]; omega
    have hidx : (n - 3) / 2 = j := by dsimp [n]; omega
    have hlen : (otherAdvice n).length = 1 := by
      simpa [upper, hodd] using hlength n
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp hlen
    have hadvice : advice n = patternCode (color j) := by
      simp [advice, hodd, hge, hidx]
    have heval (w : List Bool) (hw : w.length = n) :
        decodePattern (advice n, w) = decide (([b], w) ∈ predicates j) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [L, Set.mem_ofPred_eq, hw, hb, ← hj, decide_eq_true_eq] using hLA w
    apply hcolor j b
    apply Prod.ext
    · have h := heval (List.replicate n false) (by simp)
      rw [hadvice, decodePattern_code] at h
      simpa [n, observations, List.replicate_succ] using h
    · have h := heval (List.replicate n true) (by simp)
      rw [hadvice, decodePattern_code] at h
      simpa [n, observations, List.replicate_succ] using h
  refine ⟨lower, gap, L, hlowPoly, hgapPoly, hcap, ?_, hunbounded, hL, ?_⟩
  · intro n
    simpa only [congrFun hsum n] using hupperPow n
  · simpa only [hsum] using hnot

end Cslib.Complexity
