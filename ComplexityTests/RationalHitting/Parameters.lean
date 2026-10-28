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
open Cslib.Circuits.Rational

/-! ### Concrete values, certifiable forms, and certificates -/

/-- info: [(2, 1, 4, 2, 385, 8), (208, 7, 256, 128, 452984833, 32768),
 (350, 8, 512, 256, 3623878657, 131072), (16, 4, 32, 16, 196609, 512)] -/
#guard_msgs (whitespace := lax) in
#eval [generatorParameters 0 0, generatorParameters 1 1, generatorParameters 2 1,
  generatorParameters 1 0]

attribute [local fun_prop] ComputableInPolyTime.tidy in
example (n s : ℕ) :
    (threshold 0 0 = 2 ∧ threshold 1 1 = 144 ∧
      generatorParameters 0 0 = (2, 1, 4, 2, 385, 8) ∧
      generatorParameters 1 1 = (208, 7, 256, 128, 452984833, 32768) ∧
      (generatorParameters n s).2.2.2.2.2 = (hittingList n s).dimension ∧
      (hittingList 2 1).dimension = 131072) ∧
    (Parameters.ambientDimension 1 1 = 2 ^ Nat.clog 2 (threshold 1 1 + 1) ∧
      2 * CyclotomicRing.degree (Parameters.exponent n s) = Parameters.ambientDimension n s) ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => generatorParameters p.1 p.2)
      (encPair encUnary encUnary)
      (encPair encUnary (encPair encUnary (encPair encUnary (encPair encUnary
        (encPair encUnary encUnary))))) ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => (hittingList p.1 p.2).dimension)
      (encPair encUnary encUnary) encUnary ∧
    ComputableInPolyTime (fun p : ℕ × ℕ => (hittingList p.1 p.2).dimension)
      (encPair encUnary encUnary) encNat ∧
    ComputableInPolyTime
      (fun p : ℕ × ℕ => Parameters.gridSize (p.1 + 1) (p.2 + 1)) (encPair encUnary encUnary)
      encUnary ∧
    ComputableInPolyTime
      (fun p : ℕ × ℕ => Parameters.truncation (p.1 + 1) (p.2 + 1) *
        CyclotomicRing.degree (Parameters.exponent (p.1 + 1) (p.2 + 1)))
      (encPair encUnary encUnary) encUnary := by
  refine ⟨⟨by decide, by decide, by decide, by decide, rfl, by decide⟩,
    ⟨Parameters.ambientDimension_eq 1 1, ?_⟩,
    computableInPolyTime_generatorParameters,
    computableInPolyTime_hittingList_dimension,
    computableInPolyTime_hittingList_dimension_binary,
    ?_, ?_⟩
  · rw [Parameters.degree_eq, Parameters.ambientDimension, pow_succ, Nat.mul_div_cancel _ two_pos,
      mul_comm]
  · apply computableInPolyTime_gridSize <;> exact .of_tidy (by fun_prop)
  · apply ComputableInPolyTime.of_tidy
    have ht : ComputableTidilyInPolyTime
        (fun p : ℕ × ℕ => Parameters.truncation (p.1 + 1) (p.2 + 1))
        (encPair encUnary encUnary) encUnary := by
      apply ComputableInPolyTime.tidy
      apply computableInPolyTime_truncation <;> exact .of_tidy (by fun_prop)
    have hd : ComputableTidilyInPolyTime
        (fun p : ℕ × ℕ => CyclotomicRing.degree (Parameters.exponent (p.1 + 1) (p.2 + 1)))
        (encPair encUnary encUnary) encUnary := by
      apply ComputableInPolyTime.tidy
      apply computableInPolyTime_degree <;> exact .of_tidy (by fun_prop)
    fun_prop

end ComplexityTests.RationalHitting.Parameters
