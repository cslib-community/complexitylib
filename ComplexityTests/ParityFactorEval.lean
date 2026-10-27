/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module

import Complexity.Computability.PolyTime.ParityFactorEval
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Concrete tests for Beigel–Tarui parity-amplifier coefficients and factor jet evaluation

Nonvacuous computational and type-checking tests for `Cslib.parityLinearCoeffs`,
`Cslib.evalParityAmplifier`, and `Cslib.evalParityFactorJet` across boundary (`ℓ = 0`, `J = 0`,
`Δ = 0` homogenized evaluation, short `yJet` zero-padding), negative, zero, odd, and even inputs,
nontrivial rational $z$-jet homogenization, shared `IsTableShape` / `rowEntry` / `jetL1Norm`
bridges, and compositional `fun_prop` pipeline synthesis.
-/

namespace Cslib.ParityFactorEvalTests

open Turing.MultiTapeTM

/-! ### Beigel–Tarui linear expansion tables (`ℓ = 0, 1, 2, 3, 4`) -/

-- At `ℓ = 2`, matches the p. 37 example `(1 - Y) + (-1 + 2 Y) Y (Y - 1)`.
example :
    parityLinearCoeffs 0 = [] ∧
      parityLinearCoeffs 1 = [(1, -1)] ∧
      parityLinearCoeffs 2 = [(1, -1), (-1, 2)] ∧
      parityLinearCoeffs 3 = [(1, -1), (-1, 2), (3, -6)] ∧
      parityLinearCoeffs 4 = [(1, -1), (-1, 2), (3, -6), (-10, 20)] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Exact modular congruence `p_ℓ(y) mod 2^ℓ` for `ℓ = 1..4` and `y = -3..4` -/

example :
    ([1, 2, 3, 4].all fun ℓ =>
      ([-3, -2, -1, 0, 1, 2, 3, 4] : List ℤ).all fun y =>
        decide (evalParityAmplifier ℓ y % ((2 : ℤ) ^ ℓ) = if y % 2 = 0 then 1 else 0)) = true :=
  rfl

/-! ### Boundary shapes (`J = 0`, `ℓ = 0`), `Δ = 0` homogenization, and short-input zero-padding -/

example :
    evalParityFactorJet 0 3 6 [12, -3, 5] = [] ∧
      evalParityFactorJet 3 0 6 [12, -3, 5] = [[], [], []] ∧
      evalParityFactorJet 3 2 6 [12] = [[-216, 1296], [0, 0], [0, 0]] ∧
      evalParityFactorJet 1 1 0 [1] = [[-1]] ∧
      evalParityFactorJet 2 2 0 [1, 2] = [[0, 2], [0, 12]] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### Nontrivial `J = 3, ℓ = 3, Δ = 6` rational `z`-jet homogenization test -/

-- Represents `Y(z) = (12 - 3 z + 5 z^2) / 6 = 2 - (1/2) z + (5/6) z^2 mod z^3` cleared by
-- `Γ = 6^(2 * 3 - 1) = 7776`.
example :
    evalParityFactorJet 3 3 6 [12, -3, 5] =
      [[-7776, 46656, -279936],
       [3888, -50544, 513216],
       [-6480, 101736, -1222776]] :=
  rfl

-- Row-sum (`V = 1`) specialization at `z = 0` (`j = 0`, where `Y(0) = 12 / 6 = 2` is even):
-- `-241056 = 7776 * (-31) = 6^5 * p_3(2)`, and `(-31) % 8 = 1` (`-31 ≡ 1 [ZMOD 2^3]`).
example :
    ((evalParityFactorJet 3 3 6 [12, -3, 5]).getD 0 []).sum = 6 ^ 5 * evalParityAmplifier 3 2 ∧
      evalParityAmplifier 3 2 = -31 ∧
      Int.emod (evalParityAmplifier 3 2) 8 = 1 :=
  ⟨rfl, rfl, rfl⟩

-- Full `z`-jet row sums match the Taylor coefficients of `6^5 * p_3(2 - z/2 + 5 z^2 / 6) mod z^3`:
-- `6^5 * (-31 + 60 z - 145 z^2) = -241056 + 466560 z - 1127520 z^2`.
example :
    (evalParityFactorJet 3 3 6 [12, -3, 5]).map List.sum = [-241056, 466560, -1127520] :=
  rfl

/-! ### Shared `IsTableShape`, `rowEntry`, and `jetL1Norm` bridges (`Table` & `JetArray`) -/

example :
    IsTableShape 3 3 (evalParityFactorJet 3 3 6 [12, -3, 5]) ∧
      rowEntry (evalParityFactorJet 3 3 6 [12, -3, 5]) 2 1 = 101736 ∧
      rowEntry (evalParityFactorJet 3 3 6 [12, -3, 5]) 2 4 = 0 ∧
      jetL1Norm (evalParityFactorJet 3 3 6 [12, -3, 5]) = 2233008 ∧
      jetL1Norm (evalParityFactorJet 3 3 6 [12, -3, 5]) ≤
        3 * 2 ^ (7 * 3 ^ 2) * (polyNorm1 ([12, -3, 5].take 3) + (6 : ℤ).natAbs + 2) ^ (2 * 3 - 1) :=
  ⟨isTableShape_evalParityFactorJet 3 3 6 [12, -3, 5], rfl, rfl, rfl,
   jetL1Norm_evalParityFactorJet_le 3 3 6 [12, -3, 5]⟩

/-! ### Concrete specification bridges to `ParityAmplifier`, `CoeffNorm1`, and `SparseEquations` -/

example :
    ((Polynomial.parityBaseDigit 3 2).coeff 0, (Polynomial.parityBaseDigit 3 2).coeff 1) =
        (3, -6) ∧
      ((Polynomial.parityBaseDigit 3 5).coeff 0, (Polynomial.parityBaseDigit 3 5).coeff 1) =
        (0, 0) ∧
      (Polynomial.ofCoeffList [12, -3, 5]).coeffNorm1 = 20 :=
  ⟨(getD_parityLinearCoeffs_eq_parityBaseDigit 3 2).symm,
   (getD_parityLinearCoeffs_eq_parityBaseDigit 3 5).symm,
   Polynomial.coeffNorm1_ofCoeffList [12, -3, 5]⟩

example :
    ((Cslib.BitString.parityFactorCleared 3 (Polynomial.C 6)
        (Polynomial.ofCoeffList [12, -3, 5])).coeff 1).coeff 2 = 101736 ∧
      ((Cslib.BitString.parityFactorCleared 3 (Polynomial.C 6)
        (Polynomial.ofCoeffList [12, -3, 5])).coeff 4).coeff 2 = 0 :=
  ⟨(evalParityFactorJet_entry_eq_parityFactorCleared (J := 3) (by decide) 3 1 6 [12, -3, 5]).symm,
   (evalParityFactorJet_entry_eq_parityFactorCleared (J := 3) (by decide) 3 4 6 [12, -3, 5]).symm⟩

/-! ### Compositional `fun_prop` pipeline synthesis for plain `ComputableInPolyTime` -/

example :
    ComputableInPolyTime (fun n : ℕ => parityLinearCoeffs (2 * n + 1))
      encUnary (encList (encPair encIntBin encIntBin)) := by
  fun_prop

example :
    ComputableInPolyTime
      (fun p : (ℕ × ℕ) × (ℤ × List ℤ) =>
        let A := evalParityFactorJet (p.1.1 + 1) (p.1.2 + 1) p.2.1
          (polyAdd (truncZJet (p.1.1 + 1) p.2.2)
            (powZJet (p.1.1 + 1) (mulZJet (p.1.1 + 1) p.2.2 p.2.2) p.1.2))
        rowEntry (convJet (p.1.1 + 1) (p.1.2 + 1) A A) p.1.1 p.1.2)
      (encPair (encPair encUnary encUnary) (encPair encIntBin (encList encIntBin)))
      encIntBin := by
  fun_prop

end Cslib.ParityFactorEvalTests
