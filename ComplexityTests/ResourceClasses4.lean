/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Padding
import Complexity.Computability.Complexity.Classes.RP

/-! Padding: the padded problem of a nondeterministic machine, the translation lemma and
`P = NP → EXP = NEXP`; and error reduction for deciders of a nontrivial problem. -/

namespace ComplexityTests.ResourceClasses4

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Padding -/

/-- `2 ^ n` is computed in unary from any word of length `n` within time
`O(n + (n + 1) * 2 ^ n)`: the hypothesis of the translation lemma is satisfiable. -/
theorem computableInO_two_pow_length :
    ComputableInO (fun x : List Bool => 2 ^ x.length) encBits encUnary
      (fun x => x.length + (x.length + 1) * 2 ^ x.length)
      fun x => x.length + 2 ^ x.length :=
  ComputableInO.unary_two_pow.comp ComputableInO.lengthUnary

/-- The translation lemma for nondeterministic time `O(2 ^ n)`. -/
example (hNP : NP encBits ⊆ P encBits) :
    NTIME encBits (2 ^ ·) ⊆
      ⋃ d, DTIME encBits fun n => (n + (n + (n + 1) * 2 ^ n) + 1) ^ d :=
  NTIME_subset_iUnion_DTIME_of_NP_subset_P hNP computableInO_two_pow_length

/-- **Padded instances decide the original problem.** Every nondeterministic machine has a padded
problem in `NP`, and a problem in `NTIME t` is the preimage of the padded problem of its machine
along `a ↦ frame (enc a) ++ 1 ^ t n`, for enough coins per padded bit. -/
example {α : Type} {enc : α ↪ List Bool} {t : ℕ → ℕ} {A : Set α} (hA : A ∈ NTIME enc t) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (ntm : MultiTapeNTM k Bool State) (c : ℕ),
      ntm.padded c ∈ NP encBits ∧
        ∀ a, frame (enc a) ++ List.replicate (t (enc a).length) true ∈ ntm.padded c ↔ a ∈ A := by
  obtain ⟨c₁, c₂, k, State, hfinite, ntm, hdec⟩ := hA
  refine ⟨k, State, hfinite, ntm, Nat.card (Turing.Action k Bool State) * (c₁ + c₂),
    ntm.padded_mem_NP _, fun a => hdec.frame_append_mem_padded_iff ?_⟩
  rw [List.length_append, List.length_replicate, length_frame, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (by nlinarith)

/-- Separating linear-exponential time `E` and `NE` separates `P` from `NP`. -/
example : E encNat ≠ NE encNat → P encBits ≠ NP encBits :=
  fun hE hP => hE (E_eq_NE_of_P_eq_NP hP)

/-! ### Error reduction on a nontrivial problem -/

/-- The bit words starting with `true`. -/
def startsTrue : Set (List Bool) := {x | x.headD false = true}

/-- Accept when one of two random bits is `true` on instances starting with `true`, and when both
are on the others: right with probability `3 / 4`. -/
def orAnd (x : List Bool × List Bool) : Bool :=
  if x.1.headD false then x.2.headD false || x.2.getD 1 false
  else x.2.headD false && x.2.getD 1 false

/-- `orAnd` decides `startsTrue` with bounded error, with genuinely random answers. -/
theorem decidesWithBoundedError_orAnd : DecidesWithBoundedError encBits 2 orAnd startsTrue :=
  fun a => by
  have hor (n : ℕ) (hn : n = 2) : 2 * 2 ^ n ≤ 3 * (Finset.univ.filter fun r : Fin n → Bool =>
      ((List.ofFn r).headD false || (List.ofFn r).getD 1 false) = true).card := by
    subst hn
    decide
  have hand (n : ℕ) (hn : n = 2) : 2 * 2 ^ n ≤ 3 * (Finset.univ.filter fun r : Fin n → Bool =>
      ((List.ofFn r).headD false && (List.ofFn r).getD 1 false) = false).card := by
    subst hn
    decide
  rcases ha : a.headD false
  · refine ⟨fun h => absurd (ha.symm.trans h) Bool.false_ne_true, fun _ => ?_⟩
    simp only [BoundedErrorAt, orAnd, ha, Bool.false_eq_true, ↓reduceIte]
    exact hand _ (Polynomial.eval_ofNat 2 _)
  · refine ⟨fun _ => ?_, fun h => absurd ha h⟩
    simp only [BoundedErrorAt, orAnd, ha, ↓reduceIte]
    exact hor _ (Polynomial.eval_ofNat 2 _)

/-- Majority votes of `12 q(n)` runs of `orAnd` decide `startsTrue` with error at most
`2 ^ (-q(n))`, and at `q + 2` recover bounded error `1 / 3`. -/
example (q : Polynomial ℕ) :
    DecidesWithErrorExponent encBits q (12 * q * 2) (repeatMajority encBits (6 * q) 2 orAnd)
      startsTrue ∧
    DecidesWithBoundedError encBits (12 * (q + 2) * 2)
      (repeatMajority encBits (6 * (q + 2)) 2 orAnd) startsTrue :=
  ⟨decidesWithBoundedError_orAnd.repeatMajority q,
    (decidesWithBoundedError_orAnd.repeatMajority (q + 2)).solvesWithBoundedError
      (fun _ => by simp)⟩

example : startsTrue ∈ BPP encBits :=
  ⟨2, orAnd, by unfold orAnd; fun_prop, decidesWithBoundedError_orAnd⟩

/-- Accept when the instance and one random bit start with `true`. -/
def andHead (x : List Bool × List Bool) : Bool := x.1.headD false && x.2.headD false

/-- `andHead` decides `startsTrue` with one-sided error `1 / 2`. -/
theorem decidesWithOneSidedError_andHead :
    DecidesWithOneSidedError encBits 1 andHead startsTrue := fun a => by
  have key (n : ℕ) (hn : n = 1) : 2 ^ n ≤ 2 * (Finset.univ.filter fun r : Fin n → Bool =>
      (List.ofFn r).headD false = true).card := by
    subst hn
    decide
  rcases ha : a.headD false
  · refine ⟨fun h => absurd (ha.symm.trans h) Bool.false_ne_true, fun _ r => ?_⟩
    simp only [andHead, ha, Bool.false_and]
  · refine ⟨fun _ => ?_, fun h => absurd ha h⟩
    simp only [andHead, ha, Bool.true_and]
    exact key _ Polynomial.eval_one

/-- `q(n)` runs of `andHead` decide `startsTrue` with one-sided error at most `2 ^ (-q(n))`, and
at `q + 1` recover one-sided error `1 / 2`. -/
example (q : Polynomial ℕ) :
    DecidesWithOneSidedErrorExponent encBits q (q * 1) (repeatAny encBits q 1 andHead)
      startsTrue ∧
    DecidesWithOneSidedError encBits ((q + 1) * 1) (repeatAny encBits (q + 1) 1 andHead)
      startsTrue :=
  ⟨decidesWithOneSidedError_andHead.repeatAny q,
    (decidesWithOneSidedError_andHead.repeatAny (q + 1)).solvesWithOneSidedError
      (fun _ => by simp)⟩

example : startsTrue ∈ RP encBits :=
  ⟨1, andHead, by unfold andHead; fun_prop, decidesWithOneSidedError_andHead⟩

end ComplexityTests.ResourceClasses4
