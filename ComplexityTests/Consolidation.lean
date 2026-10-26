/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Synthesis
import Complexity.Computability.Complexity.Classes.Ladner
import Complexity.Computability.Complexity.Classes.LogSpace
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Universal.PolyTime
import Complexity.Foundations.Data.BitString.Parity
import Complexity.Foundations.Data.Nat.Asymptotics
import Complexity.Foundations.Data.Nat.Log
import Complexity.Foundations.Data.Nat.PolynomialBound.Log
import Mathlib.Tactic.FinCases

/-! General lemmas in their library homes: the costs of projections and the one-gate lower bound
for circuits on two and three inputs, the decoders of binary numbers and Booleans on encoded and
malformed words, `P` under reductions and `NP`-complete problems in `P`, deterministic deciders as
nondeterministic ones, the parity of a symmetric difference, and logarithmic bounds, with their
boundary cases. -/

namespace ComplexityTests.Consolidation

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Projections and the first gate -/

section Circuits

open Cslib.Circuits Cslib.Circuits.Boolean

example : complexity interpretation (single fun x : BitString 2 => x 1) = 0 :=
  complexity_single_proj 1

example : complexity interpretation (single fun x : BitString 3 => x 2) = 0 :=
  complexity_single_proj 2

/-- The conjunction of two inputs costs exactly one gate. -/
example : complexity interpretation (single fun x : BitString 2 => x 0 && x 1) = 1 := by
  refine le_antisymm ?_ (one_le_complexity_single fun i h => ?_)
  · have h := complexity_and_le (fun x : BitString 2 => x 0) fun x => x 1
    rw [complexity_single_proj, complexity_single_proj] at h
    exact h
  · fin_cases i
    · exact absurd (congrFun h ![true, false]) (by decide)
    · exact absurd (congrFun h ![false, true]) (by decide)

/-- The conjunction of three inputs needs at least one gate. -/
example : 1 ≤ complexity interpretation (single fun x : BitString 3 => x 0 && x 1 && x 2) :=
  one_le_complexity_single fun i h => by
    fin_cases i
    · exact absurd (congrFun h ![true, false, false]) (by decide)
    · exact absurd (congrFun h ![false, true, false]) (by decide)
    · exact absurd (congrFun h ![false, false, true]) (by decide)

/-- Negating the input costs at most one gate. -/
example : complexity interpretation (single fun x : BitString 1 => !x 0) ≤ 1 := by
  have h := complexity_not_le (fun x : BitString 1 => x 0)
  rwa [complexity_single_proj] at h

end Circuits

/-! ### Decoders of binary numbers and Booleans -/

/-- Binary digits are read least significant first: `[true, false, true]` is `5`. -/
example : Decoder.nat.decode [true, false, true] = 5 := rfl

example : Decoder.nat.decode (encNat 6) = 6 := Decoder.nat.decode_enc 6

/-- Malformed words: trailing `false`s are ignored, and the empty word is `0`. -/
example : Decoder.nat.decode [true, false, false] = 1 := rfl

example : Decoder.nat.decode [] = 0 := rfl

example : (ofBits [false, true, false]).bits = [false, true] := by
  rw [bits_ofBits]
  decide

example : Decoder.bool.decode (encBool true) = true := Decoder.bool.decode_enc true

/-- The empty word, which encodes no Boolean, decodes to `false`. -/
example : Decoder.bool.decode [] = false := rfl

/-! ### `P` under reductions and `NP`-complete problems -/

example {A : Set (List Bool)} (h : A ∈ P encBits) : A ∈ P encBits :=
  (PolyTimeReducible.refl encBits A).mem_P h

/-- With `SAT` in `P`, every encoding has `P = NP`. -/
example (h : SAT ∈ P encCNF) : P encBits = NP encBits :=
  CookLevin.SAT_npComplete.P_eq_NP_of_mem_P h encBits

example (h : SAT ∈ P encCNF) : P encCNF = NP encCNF :=
  Ladner.P_eq_NP_of_SAT_mem_P h encCNF

/-! ### Deterministic deciders as nondeterministic ones -/

example {α : Type} {enc : α ↪ List Bool} : L enc ⊆ NL enc := L_subset_NL

example {α : Type} {enc : α ↪ List Bool} : PSPACE enc ⊆ NPSPACE enc := PSPACE_subset_NPSPACE

/-- `NPSPACE` is stated with `DecidesInSpace`. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NPSPACE enc ↔ ∃ (k : ℕ) (State : Type) (_ : Finite State)
      (ntm : MultiTapeNTM k Bool State) (s : α → ℕ),
        PolyBounded (fun a => (enc a).length) s ∧ ntm.DecidesInSpace enc A s :=
  Iff.rfl

/-! ### Parities of symmetric differences -/

example : ∀ x : Fin 3 → Bool,
    parityOn (symmDiff ({0, 1} : Finset (Fin 3)) {1, 2}) x =
      (parityOn {0, 1} x ^^ parityOn {1, 2} x) := by
  decide

/-- The symmetric difference of a set with itself is empty, of parity `false`. -/
example (s : Finset (Fin 4)) (x : Fin 4 → Bool) : (parityOn s x ^^ parityOn s x) = false := by
  rw [← parityOn_symmDiff, symmDiff_self, Finset.bot_eq_empty, parityOn_empty]

/-! ### Logarithmic bounds -/

example : 2 ^ (Nat.log2 5 + 1) ≤ 2 * (5 + 1) := Nat.two_pow_log2_succ_le 5

/-- At `n = 0` the bound is `2 ≤ 2`, attained. -/
example : 2 ^ (Nat.log2 0 + 1) = 2 * (0 + 1) := by decide

example (c : ℕ) : PolynomiallyBounded fun n => c * (Nat.log2 n + 1) :=
  polynomiallyBounded_mul_log2_add_one c

example (c : ℕ) : PolyBounded (fun w : List Bool => w.length)
    fun w => c * (Nat.log2 w.length + 1) :=
  polyBounded_log _ c

/-- Adding one increases `⌊log_b n⌋` by at most one, and equality holds at `n = b ^ k - 1`. -/
example : Nat.log 2 (7 + 1) ≤ Nat.log 2 7 + 1 ∧ Nat.log 2 (7 + 1) = Nat.log 2 7 + 1 :=
  ⟨Nat.log_add_one_le 2 7, by decide⟩

/-- `Nat.log_add_one_le` also holds for degenerate bases `b ≤ 1` and at `n = 0`. -/
example : Nat.log 0 (5 + 1) ≤ Nat.log 0 5 + 1 ∧ Nat.log 2 (0 + 1) ≤ Nat.log 2 0 + 1 :=
  ⟨Nat.log_add_one_le 0 5, Nat.log_add_one_le 2 0⟩

end ComplexityTests.Consolidation
