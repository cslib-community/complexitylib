/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Boolean.Braverman.Approximation
import Complexity.Computability.Circuit.Pi
import Complexity.Probability.PMF
import Cslib.Probability.PMF

/-!
# Braverman's real approximation of AND gates

Concrete clients of Braverman's gate approximators and circuit approximation on the gate `AND₃`:
the approximator's values at bits, exact where some set holds exactly one zero and wrong where
none does, the choice of sets against the uniform distribution, and the circuit-level
approximation of the one-gate circuit `AND₃`.
-/

namespace ComplexityTests.BravermanApproximation

open Cslib Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.Braverman

/-- One set holding all three arguments. -/
abbrev allSet : Fin 1 → Fin 3 → Bool := fun _ _ => true

-- The set holds exactly one zero of `(1, 0, 1)`, so the factor vanishes, as `AND` does.
example : andApprox allSet ![1, 0, 1] = 0 := by
  norm_num [andApprox, Fin.sum_univ_three]

-- With two zeros the only set misses, and the approximator is `1 - 2 = -1`, not a bit.
example : AndMiss allSet ![false, false, true] := by decide

example : andApprox allSet ![0, 0, 1] = -1 := by
  norm_num [andApprox, Fin.sum_univ_three]

-- At all-ones bits the approximator is exactly `1`.
example : andApprox allSet ![1, 1, 1] = 1 := by
  norm_num [andApprox, Fin.sum_univ_three]

-- Adding the set `{0}` repairs the miss: it holds exactly one zero, so the value is `AND = 0`.
example : andApprox ![fun j : Fin 3 => decide (j = 0), fun _ => true]
    (fun j => bitVal ℝ (![false, false, true] j)) = 0 := by
  rw [andApprox_bitVal (by decide)]
  rfl

-- The OR approximator at bits is exact when the negated bits are not missed.
example : orApprox allSet (fun j => bitVal ℝ (![false, true, false] j)) = 1 := by
  rw [orApprox_bitVal (by decide)]
  rfl

-- Braverman's choice of sets for `AND₃` against the uniform distribution, with two rates and
-- two sets per rate: the sets miss with probability at most `(41 / 50) ^ 2`.
example : ∃ S : Fin (2 * 2) → Fin 3 → Bool,
    ∑ x with GateMiss (.and 3) S x, (Probability.PMF.uniformOfFintype (Fin 3 → Bool) x).toReal ≤
      (41 / 50) ^ 2 := by
  obtain ⟨S, hS⟩ := exists_sum_gateMiss_le (ℓ := 2) (s := 2)
    (fun x => (Probability.PMF.uniformOfFintype (Fin 3 → Bool) x).toReal)
    (fun _ => ENNReal.toReal_nonneg) (.and 3) (by norm_num) id
  rw [Cslib.Probability.PMF.sum_toReal, mul_one] at hS
  exact ⟨S, hS⟩

/-- The one-gate circuit computing `AND₃`. -/
abbrev and3 : Circuit Unbounded.signature 3 1 := Circuit.oneGate (.and 3) id

-- Braverman's approximation of the circuit `AND₃` for any distribution: a function of degree at
-- most `4` that agrees with `AND₃` wherever a witness of depth at most `7` is false, and the
-- witness is true with probability at most `(41 / 50) ^ 2`.
example (ν : PMF (Fin 3 → Bool)) : ∃ f ∈ lowDegree ℝ (Fin 3) 4,
    ∃ W : Circuit Unbounded.signature 3 1, W.depth ≤ 7 ∧
      ∑ x with W.eval Unbounded.interpretation x 0 = true, (ν x).toReal ≤ (41 / 50) ^ 2 ∧
      ∀ x, W.eval Unbounded.interpretation x 0 = false →
        f x = bitVal ℝ (decide (∀ j, x j = true)) := by
  obtain ⟨f, hf, -, W, -, hWd, hWν, hWf⟩ := exists_lowDegree_approx ν (ℓ := 2) (s := 2) (r := 3)
    (by norm_num) (by norm_num) and3 (by decide)
  have hd : and3.depth = 1 := Circuit.depth_oneGate _ _
  have hsz : and3.size = 1 := rfl
  rw [hd, pow_one] at hf
  rw [hd] at hWd
  rw [hsz, Nat.cast_one, mul_one] at hWν
  exact ⟨f, hf, W, hWd, hWν, fun x hx => (hWf x hx).trans rfl⟩

end ComplexityTests.BravermanApproximation
