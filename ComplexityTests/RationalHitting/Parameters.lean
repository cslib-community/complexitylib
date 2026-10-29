/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Karn Seth
-/

import Complexity.Computability.Circuit.Rational.Runtime.Parameters
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time parameters of the rational hitting list

Concrete parameter values for small `n` and `s`, computed by the kernel and by evaluation, the
certifiable forms of the ambient dimension and the cyclotomic degree, the parameter and dimension
certificates from unary `(n, s)`, and their use by `fun_prop` on shifted inputs.
-/

namespace ComplexityTests.RationalHitting.Parameters

open Turing MultiTapeTM
open Cslib.Circuits.Rational Cslib.Circuits.Rational

/-! ### Concrete values -/

example : threshold 0 0 = 2 := by decide
example : threshold 1 1 = 144 := by decide
example : generatorParameters 0 0 = (2, 1, 4, 2, 385, 8) := by decide
example : generatorParameters 1 1 = (208, 7, 256, 128, 452984833, 32768) := by decide

/-- info: [(2, 1, 4, 2, 385, 8), (208, 7, 256, 128, 452984833, 32768),
 (350, 8, 512, 256, 3623878657, 131072), (16, 4, 32, 16, 196609, 512)] -/
#guard_msgs (whitespace := lax) in
#eval [generatorParameters 0 0, generatorParameters 1 1, generatorParameters 2 1,
  generatorParameters 1 0]

-- The last component of the parameters is the common dimension of the hitting list.
example (n s : ℕ) : (generatorParameters n s).2.2.2.2.2 = (hittingList n s).dimension := rfl
example : (hittingList 2 1).dimension = 131072 := by decide

/-! ### Certifiable forms -/

example : 2 ^ Nat.clog 2 (threshold 1 1 + 1) = 256 := by
  rw [← Parameters.ambientDimension_eq 1 1]
  decide

example (n s : ℕ) : 2 * CyclotomicRing.degree (Parameters.exponent n s) =
    Parameters.ambientDimension n s := by
  rw [Parameters.degree_eq, Parameters.ambientDimension, pow_succ, Nat.mul_div_cancel _ two_pos,
    mul_comm]

/-! ### Certificates -/

-- The registered certificates compose under `fun_prop`, here on the shifted input of the final
-- generator.
example : ComputableInPolyTime (fun p : ℕ × ℕ => generatorParameters (p.1 + 1) (p.2 + 1))
    (encPair encUnary encUnary)
    (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
      (encPair encUnary encUnary))))) :=
  computableInPolyTime_generatorParameters.comp (g := fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1))
    (by fun_prop)

example : ComputableInPolyTime (fun p : ℕ × ℕ => (hittingList (p.1 + 1) (p.2 + 1)).dimension)
    (encPair encUnary encUnary) encUnary :=
  computableInPolyTime_hittingList_dimension.comp (g := fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1))
    (by fun_prop)

example : ComputableInPolyTime (fun p : ℕ × ℕ => (hittingList (p.1 + 1) (p.2 + 1)).dimension + 1)
    (encPair encUnary encUnary) encNat :=
  (ComputableInPolyTime.of_tidy computableTidilyInPolyTime_succ).comp
    (computableInPolyTime_hittingList_dimension_binary.comp
      (g := fun p : ℕ × ℕ => (p.1 + 1, p.2 + 1)) (by fun_prop))

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => Parameters.gridSize (p.1 + 1) (p.2 + 1)) (encPair encUnary encUnary)
    encUnary := by
  apply computableInPolyTime_gridSize <;> fun_prop

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => Parameters.truncation (p.1 + 1) (p.2 + 1) *
      CyclotomicRing.degree (Parameters.exponent (p.1 + 1) (p.2 + 1)))
    (encPair encUnary encUnary) encUnary := by
  have ht : ComputableInPolyTime
      (fun p : ℕ × ℕ => Parameters.truncation (p.1 + 1) (p.2 + 1))
      (encPair encUnary encUnary) encUnary := by
    apply computableInPolyTime_truncation <;> fun_prop
  have hd : ComputableInPolyTime
      (fun p : ℕ × ℕ => CyclotomicRing.degree (Parameters.exponent (p.1 + 1) (p.2 + 1)))
      (encPair encUnary encUnary) encUnary := by
    apply computableInPolyTime_degree <;> fun_prop
  fun_prop

end ComplexityTests.RationalHitting.Parameters
