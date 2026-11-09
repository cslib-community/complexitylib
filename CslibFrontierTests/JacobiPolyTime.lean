/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Jacobi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! Checked instances for the polynomial-time Jacobi symbol: the certificates, a composed client
in the shape of the Solovay–Strassen comparison, and runs of the counted loop on concrete inputs,
including an even modulus and the modulus `0`, checked against `norm_num`'s independent evaluation
of `jacobiSym`. -/

namespace CslibFrontierTests.JacobiPolyTime

open NumberTheorySymbols Turing.MultiTapeTM Turing.MultiTapeTM.BinaryJacobi

/-! ### Certificates -/

example : ComputableInPolyTime (fun p : ℕ × ℕ => J((p.1 : ℤ) | p.2))
    (encPair encNat encNat) encIntBin :=
  ComputableInPolyTime.binary_jacobiSym

example : ComputableInPolyTime (fun p : ℤ × ℕ => J(p.1 | p.2))
    (encPair encIntBin encNat) encIntBin :=
  ComputableInPolyTime.intBin_jacobiSym

-- `fun_prop` composes the certificate: `J(a | 2 n + 1)` for binary `a, n`.
example : ComputableInPolyTime (fun p : ℕ × ℕ => J((p.1 : ℤ) | 2 * p.2 + 1))
    (encPair encNat encNat) encIntBin := by
  fun_prop

-- The Solovay–Strassen comparison `a ^ ((n - 1) / 2) ≡ J(a | n) (mod n)` for odd `n = 2 m + 3`,
-- with the symbol reduced to a residue modulo `n`.
example : ComputableInPolyTime
    (fun p : ℕ × ℕ => decide (p.1 ^ (p.2 + 1) % (2 * p.2 + 3) =
      (J((p.1 : ℤ) | 2 * p.2 + 3) % ((2 * p.2 + 3 : ℕ) : ℤ)).toNat))
    (encPair encNat encNat) encBool := by
  have hpow : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 ^ (p.2 + 1) % (2 * p.2 + 3))
      (encPair encNat encNat) encNat :=
    ComputableInPolyTime.binary_powMod (by fun_prop) (by fun_prop) (by fun_prop)
      fun _ => Nat.succ_pos _
  fun_prop

/-! ### Runs of the loop -/

-- `J(1001 | 9907) = -1`, the classic worked example, in `2 * Nat.size 9907 = 28` steps.
example : jacobiReadout (jacobiStep^[jacobiCount (1001, 9907)] (jacobiInit (1001, 9907))) = -1 :=
  by decide +kernel

example : J((1001 : ℤ) | 9907) = -1 := by norm_num

-- An even modulus: `J(5 | 12) = J(5 | 2) ^ 2 · J(5 | 3) = -1`.
example : jacobiReadout (jacobiStep^[jacobiCount (5, 12)] (jacobiInit (5, 12))) = -1 :=
  by decide +kernel

-- `norm_num`'s `jacobiSym` extension halves an even modulus once and then treats it as odd, so on
-- `J(5 | 12)` the kernel rejects its proof; split off one factor `2` before calling it.
example : J((5 : ℤ) | 12) = -1 := by
  rw [show (12 : ℕ) = 2 * 6 from rfl, jacobiSym.mul_right]
  norm_num

-- A common factor: `J(6 | 15) = 0`.
example : jacobiReadout (jacobiStep^[jacobiCount (6, 15)] (jacobiInit (6, 15))) = 0 :=
  by decide +kernel

example : J((6 : ℤ) | 15) = 0 := by norm_num

-- The modulus `0`: `J(3 | 0) = 1`, read out from the initial state without any step.
example : jacobiReadout (jacobiStep^[jacobiCount (3, 0)] (jacobiInit (3, 0))) = 1 :=
  by decide +kernel

example : J((3 : ℤ) | 0) = 1 := by norm_num

-- The step count is `2 * Nat.size n`: 28 for `n = 9907 < 2 ^ 14`.
example : jacobiCount (1001, 9907) = 28 := by decide +kernel

-- The general correctness theorem specializes to these inputs.
example : J((1001 : ℤ) | 9907) =
    jacobiReadout (jacobiStep^[jacobiCount (1001, 9907)] (jacobiInit (1001, 9907))) :=
  (jacobiReadout_iterate_jacobiStep (1001, 9907)).symm

end CslibFrontierTests.JacobiPolyTime
