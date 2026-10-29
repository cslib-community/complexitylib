/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Toda
import Complexity.Computability.Complexity.Classes.Toda.Counting

/-! Parity-P and the class operators on concrete problems, the Valiant–Vazirani test and the
counting tests of Toda's theorem on concrete words, and non-vacuity witnesses. -/

namespace ComplexityTests.Toda

open Cslib Cslib.Complexity Cslib.Complexity.Toda Finset Turing.MultiTapeTM

/-! ### Parity-P and the operators -/

/-- The words starting with `true`: a verifier reading the first bit and ignoring its single
certificate of length `0`. -/
example : {w : List Bool | w.headD false = true} ∈ ParityP encBits := by
  refine mem_ParityP.2 ⟨0, fun x => x.1.headD false, by fun_prop, fun w => ?_⟩
  simp only [Set.mem_ofPred_eq, Polynomial.eval_zero]
  cases w with
  | nil => simp [acceptCount]
  | cons b w => cases b <;> simp [acceptCount]

/-- `⊕P` is closed under complement. -/
example : {w : List Bool | w.headD false = true}ᶜ ∈ ParityP encBits :=
  compl_mem_ParityP (P_subset_ParityP ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩)

/-- One more accepted string flips the parity. -/
example : acceptCount (succVerifier fun x : Unit × List Bool => x.2.headD false) () 3 = 3 := by
  rw [acceptCount_succVerifier]
  decide

/-- `BP·P` is `BPP`, so any problem in `BPP` lies in `BP·⊕P` via `P ⊆ ⊕P`. -/
example : BPP encBits ⊆ BPOp encBits (ParityP (encPair encBits encBits)) :=
  BPOp_P.symm.subset.trans (BPOp_mono P_subset_ParityP)

/-- The words starting with `true`, through the parity operator with one certificate bit: the
pairs whose word and certificate both start with `true`. A word starting with `true` is accepted
with one of the two certificates `[false]` and `[true]`, an odd count, and any other word with
none. -/
theorem headD_mem_ParityOp : {w : List Bool | w.headD false = true} ∈
    ParityOp encBits (P (encPair encBits encBits)) := by
  refine mem_ParityOp.2 ⟨1, {x | (x.1.headD false && x.2.headD false) = true},
    ⟨fun x => x.1.headD false && x.2.headD false, by fun_prop, fun _ => Iff.rfl⟩, fun w => ?_⟩
  simp only [Set.mem_ofPred_eq, Polynomial.eval_one]
  cases w with
  | nil => simp [acceptCount]
  | cons b w =>
    cases b
    · simp [acceptCount]
    · simp only [List.headD_cons, acceptCount, List.ofFn_succ, List.ofFn_zero, Bool.true_and,
        Bool.decide_eq_true, true_iff]
      decide

/-- The parity operator is monotone: the same problem is in `⊕·NP`. -/
example : {w : List Bool | w.headD false = true} ∈
    ParityOp encBits (NP (encPair encBits encBits)) :=
  ParityOp_mono P_subset_NP headD_mem_ParityOp

/-! ### The Valiant–Vazirani test -/

/-- With one equation read from the seed `10 1`, coefficients `10` and offset `1`, the word `10`
satisfies `x₀ = 1`, and `01` does not. -/
example : hashesToZero 1 [true, false, true] [true, false] = true := by decide

example : hashesToZero 1 [true, false, true] [false, true] = false := by decide

/-- With no equation, every word passes. -/
example : hashesToZero 0 [] [true, true] = true := by decide

/-- The parity form of a disjunction. -/
example : Odd (1 + ∏ j : Fin 3, (1 + ![2, 3, 4] j)) := by decide

/-! ### The counting tests -/

/-- The binomial expansion of the parity: `5 - 2 * 10 + 4 * 10 - 8 * 5 + 16 * 1 = 1`. -/
example : ∑ i ∈ range 5, (-2 : ℤ) ^ i * ((5 : ℕ).choose (i + 1) : ℤ) = 1 := by decide

/-- The lexicographic order on words of equal length. -/
example : BitString.wordLt [false, true] [true, false] = true := by decide

example : BitString.wordLt [true, false] [true, false] = false := by decide

/-- The coefficients of the amplification modulo `2 ^ 3`: `1, 6, 4`, that is `1, -2, 4`. -/
example : (parityCoeff 3 0, parityCoeff 3 1, parityCoeff 3 2) = (1, 6, 4) := by decide

/-- With one random string (`R = 0`) and the one witness `1` of length `1` accepted, the
witnesses are odd in all random strings, and bit `1` of the count of the `#P` test is set. -/
example : ((univ.filter fun w : Fin (0 + 1 + ((0 + 1) + (0 + (0 + 1) * 1)) + 1 + 1) → Bool =>
    sharpTest (fun _ z => z.headD false) 0 1 (List.ofFn w) = true).card).testBit (0 + 1) =
      true :=
  (testBit_card_filter_sharpTest (fun _ z => z.headD false) 0 1).trans (by decide)

/-! ### Random parity representations -/

/-- A polynomial-time predicate is represented by itself, with every error. -/
example (e : Polynomial ℕ) : IsRandomParityRep encBits 1 e 0 0
    (fun x => (fun y : List Bool × List Bool => y.2.headD false)
      (x.1, x.2.take ((1 : Polynomial ℕ).eval (encBits x.1).length)))
    (fun _ u => u.headD false = true) :=
  isRandomParityRep_base 1 e fun y => y.2.headD false

/-! ### Counting-oracle answers outside valid codes -/

/-- Even the empty word may receive either oracle answer: it is not a pair code. -/
example {β : Type} (enc : β ↪ List Bool) (f : β → ℕ) :
    AnswersBits enc f (bitGraph enc f ∪ {[]}) := by
  intro b i
  have hne : encPair enc encNat (b, i) ≠ [] := by
    intro h
    have := length_encPair (enc₁ := enc) (enc₂ := encNat) (b, i)
    rw [h] at this
    simp only [List.length_nil] at this
    lia
  simpa only [Set.mem_union, Set.mem_singleton_iff, hne, or_false] using
    answersBits_bitGraph enc f b i

/-- The zero function's empty bit graph is also a valid oracle. -/
example : AnswersBits encBits (fun _ => 0) ∅ := by
  intro b i
  simp

/-! ### Toda's theorem -/

/-- `P ⊆ P^#P` applied to the words starting with `true`. -/
example : {w : List Bool | w.headD false = true} ∈ PWithSharpPOracle encBits :=
  P_subset_PWithSharpPOracle ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

/-- **Toda's theorem** places every `NP` problem in `P^#P`, here the universal language via
`P ⊆ NP ⊆ PH`. -/
example : (Set.univ : Set (List Bool)) ∈ PWithSharpPOracle encBits :=
  PH_subset_PWithSharpPOracle (NP_subset_PH
    (P_subset_NP ⟨fun _ => true, .const true, fun _ => by simp⟩))

/-- `NP ⊆ P^#P`. -/
example : NP encBits ⊆ PWithSharpPOracle encBits := NP_subset_PH.trans PH_subset_PWithSharpPOracle

/-- `coNP ⊆ BP·⊕P`. -/
example : coNP encBits ⊆ BPOp encBits (ParityP (encPair encBits encBits)) :=
  coNP_subset_PH.trans PH_subset_BPOp_ParityP

end ComplexityTests.Toda
