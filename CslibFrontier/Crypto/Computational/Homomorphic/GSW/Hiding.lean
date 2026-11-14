/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.Homomorphic.GSW.Basic
public import CslibFrontier.Probability.BitString.SubsetSum.Matrix
public import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.PMFSwap

/-!
# Statistical hiding of GSW ciphertexts under a uniform public matrix

The public matrix is sampled uniformly and remains visible to the adversary. Independent binary
rows of encryption coins share this one matrix. Their joint leftover-hash bound applies to the
actual `encryptWithCoins` ciphertext. The first adversarial stage may inspect the public matrix,
choose both messages, and retain arbitrary randomized state for the final guess.

This is the unconditional statistical step of the GSW security reduction. It supplies neither a
decision-LWE assumption, security of generated public keys, native runtime certificates, nor
bootstrappability.

## Main definitions

* `uniformPublicGame`: the adaptive two-stage experiment with a uniform public matrix.
* `idealGame`: retain the first-stage state and replace the ciphertext by independent uniform
  modular coefficients followed by decomposition.

## Main results

* `dist_uniformPublicGame_ideal_le`: the shared-matrix statistical bound preserves saved state.
* `uniformPublicGame_advantage_le`: the two chosen-message games differ by at most
  `N * sqrt(2^(w * (n + 1)) / 2^m)`, where `N = (n + 1) * w`.

## References

* [C. Gentry, A. Sahai and B. Waters, *Homomorphic Encryption from Learning with Errors:
  Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, Section 3.2]
  [GentrySahaiWaters2013]
-/

@[expose] public section

namespace Cslib.Crypto.Homomorphic.GSW

open Probability Probability.PMF
open scoped _root_.Matrix NNReal

variable {n m w : ℕ}

/-- Adding any fixed modular message shift preserves the decomposed uniform distribution. -/
theorem uniform_decomposeMatrix_add
    (shift : Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w))) :
    (PMF.uniformOfFintype (Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w)))).map
      (fun U => decomposeMatrix w (shift + U)) =
    (PMF.uniformOfFintype (Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w)))).map
      (decomposeMatrix w) := by
  conv_rhs => rw [← PMF.uniformOfFintype_map_add_left shift, PMF.map_comp]
  rfl

variable {State : Type}
  (choose : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)) → PMF ((Bool × Bool) × State))
  (guess : State → Ciphertext n w → PMF Bool)

/-- The first stage sees the public matrix before choosing two bits and retaining its state.
The second stage receives that same state and the actual challenge ciphertext. -/
noncomputable def uniformPublicGame (bit : Bool) : PMF Bool := do
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)))
  let choice ← choose A
  let ((m₀, m₁), state) := choice
  let R ← PMF.uniformOfFintype (Matrix (Fin (n + 1) × Fin w) (Fin m) Bool)
  guess state (encryptWithCoins A (if bit then m₁ else m₀) R)

/-- The common ideal experiment retains the first-stage state. Its ciphertext no longer depends
on either chosen message. The state type need not be finite. -/
noncomputable def idealGame : PMF Bool := do
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)))
  let choice ← choose A
  let U ← PMF.uniformOfFintype
    (Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w)))
  guess choice.2 (decomposeMatrix w U)

private noncomputable def shiftedGuess (bit : Bool)
    (A : Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)))
    (M : Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w))) : PMF Bool := do
  let choice ← choose A
  let μ := if bit then choice.1.2 else choice.1.1
  guess choice.2 (decomposeMatrix w ((μ.toNat : ZMod (2 ^ w)) • gadgetMatrix n w + M))

/-- The entire adaptive experiment is close to one common ideal game. No efficiency or finite
state assumption is imposed on either adversarial stage. -/
theorem dist_uniformPublicGame_ideal_le (bit : Bool) :
    dist (uniformPublicGame choose guess bit) (idealGame choose guess) ≤
      ((n + 1) * w : ℕ) * Real.sqrt ((2 : ℝ) ^ (w * (n + 1)) / (2 : ℝ) ^ m) / 2 := by
  have hreal : uniformPublicGame choose guess bit =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)))).bind fun A =>
        (PMF.uniformOfFintype (Matrix (Fin (n + 1) × Fin w) (Fin m) Bool)).bind fun R =>
          shiftedGuess choose guess bit A
            (R.map (fun bit => (bit.toNat : ZMod (2 ^ w))) * A) := by
    simp only [pmf_norm, uniformPublicGame, shiftedGuess, encryptWithCoins_eq_decomposeMatrix]
    pmf_swap
  have hideal : idealGame choose guess =
      (PMF.uniformOfFintype (Matrix (Fin m) (Fin (n + 1)) (ZMod (2 ^ w)))).bind fun A =>
        (PMF.uniformOfFintype (Matrix (Fin (n + 1) × Fin w) (Fin (n + 1)) (ZMod (2 ^ w)))).bind
          fun U => shiftedGuess choose guess bit A U := by
    simp only [pmf_norm, idealGame, shiftedGuess]
    congr 1 with A : 1
    conv_rhs => rw [PMF.bind_comm]
    congr 1 with choice : 1
    have h := congrArg (fun law => law.bind (guess choice.2))
      (uniform_decomposeMatrix_add
        (((if bit then choice.1.2 else choice.1.1).toNat : ZMod (2 ^ w)) • gadgetMatrix n w))
    simpa only [PMF.bind_map, Function.comp_def] using h.symm
  rw [hreal, hideal]
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat, pow_mul] using
    BitString.SubsetSum.dist_bind_mul_le (q := 2 ^ w) (m := m) (d := n + 1)
      (Rows := Fin (n + 1) × Fin w) (shiftedGuess choose guess bit)

/-- Under a uniform public matrix, arbitrary adaptive message selection and saved state give
acceptance probabilities differing by at most `N * sqrt(2^(w * (n + 1)) / 2^m)`.
This concerns the uniform-matrix world, not the public-key distribution generated from LWE. -/
theorem uniformPublicGame_advantage_le :
    |(uniformPublicGame choose guess false true).toReal -
      (uniformPublicGame choose guess true true).toReal| ≤
      ((n + 1) * w : ℕ) * Real.sqrt ((2 : ℝ) ^ (w * (n + 1)) / (2 : ℝ) ^ m) := by
  have hfalse := dist_uniformPublicGame_ideal_le choose guess false
  have htrue := dist_uniformPublicGame_ideal_le choose guess true
  have htriangle := dist_triangle (uniformPublicGame choose guess false) (idealGame choose guess)
    (uniformPublicGame choose guess true)
  rw [dist_comm (idealGame choose guess)] at htriangle
  have heq := congrArg (fun x : ℝ≥0 => (x : ℝ))
    (Game.advantage_eq_nndist (uniformPublicGame choose guess false)
      (uniformPublicGame choose guess true))
  simp only [Game.succProbability, coe_nndist, NNReal.dist_eq,
    ENNReal.coe_toNNReal_eq_toReal] at heq
  rw [heq]
  linarith

end Cslib.Crypto.Homomorphic.GSW
