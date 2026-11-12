/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.MCSP.AntiChecker.Threshold
import CslibFrontier.Computability.Circuit.Boolean.Hierarchy

/-!
# Tests for the threshold greedy anti-checker

Besides the hash oracle, the exact counting oracle is a threshold oracle, so the abstraction is
not tied to hashing. The greedy theorem is applied to the two constant functions on `Bool`
against the identity, and to the hash oracle's anti-checker for one-input circuits with zero gates
against the constant-true function, which meets the circuit-hardness hypothesis.
-/

namespace CslibFrontierTests.AntiCheckerThreshold

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.MCSP Cslib.MCSP.AntiChecker Finset

/-- The exact counting oracle: yes when `(u + 1) #consistent ^ ℓ < 2 ^ u`. -/
private def exactOracle {α β : Type*} (G : Finset β) (eval : β → α → Bool) (ℓ : ℕ)
    (P : List (α × Bool)) (u : ℕ) : Bool :=
  decide ((u + 1) * #(consistent G eval P) ^ ℓ < 2 ^ u)

/-- The exact counting oracle is a threshold oracle for every power `ℓ`; at `ℓ = 0` it never
answers yes at threshold `0`. -/
private theorem isThresholdOracle_exactOracle {α β : Type*} (G : Finset β) (eval : β → α → Bool)
    (ℓ : ℕ) : IsThresholdOracle G eval ℓ (exactOracle G eval ℓ) where
  card_pow_lt {P u} h := by
    have h' : (u + 1) * #(consistent G eval P) ^ ℓ < 2 ^ u := of_decide_eq_true h
    calc #(consistent G eval P) ^ ℓ ≤ (u + 1) * #(consistent G eval P) ^ ℓ :=
          Nat.le_mul_of_pos_left _ (Nat.succ_pos u)
      _ < 2 ^ u := h'
      _ < 2 ^ (u + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self u)
  apply_eq_true_of_lt h := decide_eq_true h
  consistent_eq_empty {P} h := by
    have h' : (0 + 1) * #(consistent G eval P) ^ ℓ < 2 ^ 0 := of_decide_eq_true h
    rw [zero_add, one_mul, pow_zero, Nat.lt_one_iff, Nat.pow_eq_zero] at h'
    exact card_eq_zero.1 h'.1

/-- The two constant functions on `Bool`. -/
private def constEval (b x : Bool) : Bool := (fun _ => b) x

-- Every nonempty set of constant functions is half refuted against the identity on some input.
private theorem constEval_good : ∀ G' ⊆ (univ : Finset Bool), G'.Nonempty →
    ∃ x ∈ [false, true], #G' ≤ 16 * #{g ∈ G' | constEval g x ≠ id x} := by
  decide

-- Against the exact oracle, `1 * 201 + 1` greedy rounds refute both constant functions.
example : consistent univ constEval
    (greedy (exactOracle univ constEval 201) id [false, true] (1 * 201 + 1) []) = ∅ :=
  consistent_greedy_eq_empty (isThresholdOracle_exactOracle _ _ _) constEval_good
    (L := 1) (by decide) (four_mul_mul_add_one_mul_fifteen_pow_le_sixteen_pow 1)

-- The same greedy against the hash oracle on strings of one bit.
example : consistent univ (fun (w : BitString 1) x => constEval (w 0) x)
    (greedy (hashOracle univ (fun (w : BitString 1) x => constEval (w 0) x) 201) id
      [false, true] (1 * 201 + 1) []) = ∅ := by
  refine consistent_greedy_eq_empty (isThresholdOracle_hashOracle _ _ (by decide)) ?_
    (L := 1) (by decide) (four_mul_mul_add_one_mul_fifteen_pow_le_sixteen_pow 1)
  decide

private theorem strictMajority_one_complexity :
    complexity interpretation (single (strictMajority 1)) = 0 := by
  have h : strictMajority 1 = fun x : BitString 1 => x 0 := by decide
  rw [h]
  exact complexity_wiring (I := interpretation) (fun _ : Fin 1 => (0 : Fin 1))

-- The constant-true function on one input needs one gate, and a majority of one zero-gate
-- circuit needs none, so the greedy anti-checker refutes every zero-gate circuit.
example : IsAntiChecker (computableFunctions 1 0) (fun _ => true)
    {x | x ∈ hashAntiChecker 1 0 fun _ => true} := by
  refine isAntiChecker_hashAntiChecker (by decide) ?_
  rw [strictMajority_one_complexity, complexity_const]
  decide

-- Its length is `L (L + 200) + 1` for the certificate length `L = certLength 1 0 = 1`.
example : (hashAntiChecker 1 0 fun _ => true).length = 202 := by
  rw [length_hashAntiChecker]
  decide

end CslibFrontierTests.AntiCheckerThreshold
