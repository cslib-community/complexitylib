/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Complexity.Classes.Oracle.WitnessBit

/-!
# Regression tests for witness bits in `E ^ NP`

The witness bits of a satisfiable formula are forced by its unit clauses, and a family of
formulas prepared in exponential time has its witness bits in `E ^ NP`.
-/

@[expose] public section

namespace ComplexityTests.OracleWitnessBit

open Cslib Cslib.Complexity Cslib.Complexity.SAT Cslib.Logic.PL Turing.MultiTapeTM

/-- `x₀ ∧ ¬x₁`. -/
def φ : CNF ℕ := [[(0, true)], [(1, false)]]

theorem φ_mem_SAT : φ ∈ SAT := ⟨fun v => decide (v = 0), by decide⟩

/-- The witness bits satisfy `φ`, so they set `x₀` true and `x₁` false. -/
example : witnessBit (φ, 0) = true ∧ witnessBit (φ, 1) = false := by
  have h := eval_witnessBit φ_mem_SAT
  simpa [φ, CNF.eval, Clause.eval, Literal.eval] using h

/-- The witness bit is polynomial time relative to `encCNF '' SAT`. -/
example : ComputableInPolyTimeWithOracle (encCNF '' SAT) witnessBit (encPair encCNF encNat)
    encBool :=
  computableInPolyTimeWithOracle_witnessBit

/-- A preparation that ignores the instance is within time `O(2 ^ n)`, so the instances whose
prepared witness bit is `true` form a problem in `E ^ NP`; here it is every word. -/
example : {_x : List Bool | witnessBit (φ, 0) = true} ∈ ENP encBits :=
  preimage_witnessBit_mem_ENP (d := 1)
    ((ComputableInO.const (encIn := encBits) (encMid := encPair encCNF encNat) (φ, 0)).mono_le
      (fun x => by simpa using Nat.lt_two_pow_self.le) (fun _ => le_rfl))

end ComplexityTests.OracleWitnessBit
