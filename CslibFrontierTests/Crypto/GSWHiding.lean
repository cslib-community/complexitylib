/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Hiding

/-!
GSW statistical-hiding regressions: composite moduli, retained adaptive state, nontrivial concrete
bounds, empty inputs and outputs, repeated coin rows, and the failure of whole-matrix universality.
These are unconditional finite-distribution results, not decision-LWE or native-runtime proofs.
-/

namespace ComplexityTests.GSWHiding

open Cslib.Probability Cslib.Probability.PMF Cslib.Crypto.Homomorphic.GSW
open Cslib.BitString.SubsetSum
open scoped BigOperators Matrix

-- The row collision law works modulo 4, which is not a field.
example :
    (∑ A : Matrix (Fin 1) (Fin 1) (ZMod 4),
      if (fun _ : Fin 1 => (0 : ZMod 4)) ᵥ* A = (fun _ : Fin 1 => (1 : ZMod 4)) ᵥ* A then
        ((PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 4))) A).toReal else 0) = 1 / 4 := by
  simpa using vecMul_collision_probability (q := 4) (d := 1)
    (fun _ : Fin 1 => false) (fun _ => true) (by decide +kernel)

private def firstRows : Matrix (Fin 2) (Fin 1) Bool := fun _ _ => false
private def secondRows : Matrix (Fin 2) (Fin 1) Bool := fun i _ => i == 0

-- Kernel computation uses the actual modular matrix multiplication, independently of hashing.
private theorem whole_collision_iff (A : Matrix (Fin 1) (Fin 1) (ZMod 4)) :
    bitMatrix (ZMod 4) firstRows * A = bitMatrix (ZMod 4) secondRows * A ↔ A = 0 := by
  revert A
  decide +kernel

private theorem card_public : Fintype.card (Matrix (Fin 1) (Fin 1) (ZMod 4)) = 4 := by
  rw [← Fintype.card_congr (Matrix.of : (Fin 1 → Fin 1 → ZMod 4) ≃ _)]
  simp

private theorem card_output : Fintype.card (Matrix (Fin 2) (Fin 1) (ZMod 4)) = 16 := by
  rw [← Fintype.card_congr (Matrix.of : (Fin 2 → Fin 1 → ZMod 4) ≃ _)]
  simp

private theorem whole_collision_probability :
    (∑ A : Matrix (Fin 1) (Fin 1) (ZMod 4),
      if bitMatrix (ZMod 4) firstRows * A = bitMatrix (ZMod 4) secondRows * A then
        ((PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 4))) A).toReal else 0) = 1 / 4 := by
  classical
  simp [whole_collision_iff, PMF.uniformOfFintype_apply, card_public]

-- Two output rows do not give a two-universal hash on entire matrices: 1/4 exceeds 1/16.
example : ¬ IsTwoUniversal (PMF.uniformOfFintype (Matrix (Fin 1) (Fin 1) (ZMod 4)))
    (fun A (R : Matrix (Fin 2) (Fin 1) Bool) => bitMatrix (ZMod 4) R * A) := by
  intro h
  have hbad := h firstRows secondRows (by decide +kernel)
  norm_num [whole_collision_iff, PMF.uniformOfFintype_apply, card_public, card_output] at hbad

private theorem sqrt_sixtyFour : Real.sqrt (64 : ℝ) = 8 := by
  rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

-- The joint statement keeps the shared matrix and gives a genuinely subunit concrete bound.
example :
    dist
      ((PMF.uniformOfFintype (Matrix (Fin 8) (Fin 1) (ZMod 4))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 8) Bool)).map
          (fun R => (A, bitMatrix (ZMod 4) R * A))))
      ((PMF.uniformOfFintype (Matrix (Fin 8) (Fin 1) (ZMod 4))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 1) (ZMod 4))).map (A, ·))) ≤ 1 / 8 := by
  have h := dist_mul_le (q := 4) (m := 8) (d := 1) (Rows := Fin 2)
  norm_num [bitMatrix, Real.sqrt_div, sqrt_sixtyFour] at h ⊢
  exact h

-- Repeated rows occur in the actual uniform law; they are not excluded by a rank condition.
private def repeatedRows : Matrix (Fin 2) (Fin 2) Bool := fun _ j => j == 0

example : repeatedRows ∈ (PMF.uniformOfFintype (Matrix (Fin 2) (Fin 2) Bool)).support := by
  rw [PMF.mem_support_iff, PMF.uniformOfFintype_apply]
  simp

example : ∀ A : Matrix (Fin 2) (Fin 1) (ZMod 4),
    (bitMatrix (ZMod 4) repeatedRows * A) 0 = (bitMatrix (ZMod 4) repeatedRows * A) 1 := by
  decide +kernel

-- No rows means exact equality, even with an empty source and a nontrivial modulus.
example :
    dist
      ((PMF.uniformOfFintype (Matrix (Fin 0) (Fin 1) (ZMod 4))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix (Fin 0) (Fin 0) Bool)).map
          (fun R => (A, bitMatrix (ZMod 4) R * A))))
      ((PMF.uniformOfFintype (Matrix (Fin 0) (Fin 1) (ZMod 4))).bind (fun A =>
        (PMF.uniformOfFintype (Matrix (Fin 0) (Fin 1) (ZMod 4))).map (A, ·))) = 0 := by
  apply le_antisymm _ dist_nonneg
  simpa [bitMatrix] using dist_mul_le (q := 4) (m := 0) (d := 1) (Rows := Fin 0)

private abbrev Public := Matrix (Fin 8) (Fin 1) (ZMod (2 ^ 2))
private abbrev Saved := Public × Bool

private def publicBit (A : Public) : Bool := (A 0 0).val % 2 == 1

-- Messages depend on the public matrix and a fresh random bit; the state retains both.
private noncomputable def choose (A : Public) : PMF ((Bool × Bool) × Saved) := do
  let nonce ← PMF.uniformOfFintype Bool
  let message := publicBit A ^^ nonce
  return ((message, !message), (A, nonce))

private noncomputable def guess (saved : Saved) (C : Ciphertext 0 2) : PMF Bool :=
  pure (C (0, 1) (0, 1) ^^ saved.2 ^^ publicBit saved.1)

example (A : Public) (nonce : Bool) :
    ((publicBit A ^^ nonce, !(publicBit A ^^ nonce)), (A, nonce)) ∈ (choose A).support := by
  simp only [choose, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff]
  refine ⟨nonce, ?_, ?_⟩
  · rw [PMF.mem_support_iff, PMF.uniformOfFintype_apply]
    simp
  · simp

example : publicBit (0 : Public) = false ∧ publicBit (fun _ _ => 1) = true := by
  decide +kernel

-- Instantiates both actual stages, including random saved state, at n=0,m=8,w=2.
example : |(uniformPublicGame choose guess false true).toReal -
    (uniformPublicGame choose guess true true).toReal| ≤ 1 / 4 := by
  have h := uniformPublicGame_advantage_le choose guess
  norm_num [Real.sqrt_div, sqrt_sixtyFour] at h
  exact h

private abbrev SmallPublic := Matrix (Fin 1) (Fin 1) (ZMod (2 ^ 1))
private abbrev SmallCoins := Matrix (Fin 1 × Fin 1) (Fin 1) Bool

private def smallPublicEquiv : Bool ≃ SmallPublic where
  toFun bit _ _ := if bit then 1 else 0
  invFun A := A 0 0 == 1
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by
    intro A
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i j
    have h : ∀ x : ZMod 2, (if x == 1 then 1 else 0) = x := by decide +kernel
    exact h (A 0 0)

private def smallCoinsEquiv : Bool ≃ SmallCoins where
  toFun bit _ _ := bit
  invFun R := R (0, 0) 0
  left_inv := by unfold Function.LeftInverse; decide +kernel
  right_inv := by
    intro R
    ext i j
    have hi : i = (0, 0) := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i j
    rfl

private noncomputable def smallChoose (A : SmallPublic) :
    PMF ((Bool × Bool) × (SmallPublic × Bool)) := do
  let nonce ← PMF.uniformOfFintype Bool
  let message := (A 0 0 == 1) ^^ nonce
  return ((message, !message), (A, nonce))

private noncomputable def smallGuess (saved : SmallPublic × Bool)
    (C : Ciphertext 0 1) : PMF Bool :=
  pure (C (0, 0) (0, 0) ^^ saved.2 ^^ (saved.1 0 0 == 1))

private theorem small_response (A : SmallPublic) (nonce bit : Bool) (R : SmallCoins) :
    (encryptWithCoins A (if bit then !((A 0 0 == 1) ^^ nonce) else (A 0 0 == 1) ^^ nonce) R
        (0, 0) (0, 0) ^^ nonce ^^ (A 0 0 == 1)) =
      (bit ^^ (R (0, 0) 0 && (A 0 0 == 1))) := by
  revert A nonce bit R
  decide +kernel

private theorem small_game (bit : Bool) :
    uniformPublicGame smallChoose smallGuess bit = (do
      let a ← PMF.uniformOfFintype Bool
      let r ← PMF.uniformOfFintype Bool
      pure (bit ^^ (r && a))) := by
  have hpublic := (PMF.uniformOfFintype_map_equiv smallPublicEquiv).symm
  have hcoins := (PMF.uniformOfFintype_map_equiv smallCoinsEquiv).symm
  simp only [uniformPublicGame, smallChoose, smallGuess, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind, small_response]
  simp only [hpublic, hcoins, PMF.bind_map, Function.comp_def]
  simp only [PMF.bind_const]
  congr 1
  funext a
  congr 1
  funext r
  cases a <;> cases r <;> rfl

-- Exact acceptance probabilities check that retaining the correlated nonce matters.
example : (uniformPublicGame smallChoose smallGuess false true).toReal = 1 / 4 ∧
    (uniformPublicGame smallChoose smallGuess true true).toReal = 3 / 4 := by
  simp only [small_game, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.bind_apply_toReal]
  norm_num [PMF.uniformOfFintype_apply, Fintype.sum_bool]

-- Infinite state is allowed, and width zero has exactly the same law as the common ideal.
example {State : Type} (choose : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 0)) →
    PMF ((Bool × Bool) × State)) (guess : State → Ciphertext 1 0 → PMF Bool) (bit : Bool) :
    uniformPublicGame choose guess bit = idealGame choose guess := by
  apply dist_le_zero.mp
  simpa using dist_uniformPublicGame_ideal_le choose guess bit

private noncomputable def emptyChoose
    (_ : Matrix (Fin 0) (Fin 1) (ZMod (2 ^ 1))) : PMF ((Bool × Bool) × Unit) :=
  pure ((false, true), ())

private noncomputable def emptyGuess (_ : Unit) (C : Ciphertext 0 1) : PMF Bool :=
  pure (C (0, 0) (0, 0))

private theorem empty_ciphertext_bit (μ : Bool)
    (A : Matrix (Fin 0) (Fin 1) (ZMod (2 ^ 1)))
    (R : Matrix (Fin 1 × Fin 1) (Fin 0) Bool) :
    encryptWithCoins A μ R (0, 0) (0, 0) = μ := by
  revert μ A R
  decide +kernel

-- Empty source coins need not hide the message. The theorem keeps its explicit entropy loss.
example (bit : Bool) : uniformPublicGame emptyChoose emptyGuess bit = PMF.pure bit := by
  cases bit <;> simp [uniformPublicGame, emptyChoose, emptyGuess, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, empty_ciphertext_bit, PMF.bind_const]

end ComplexityTests.GSWHiding
