/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Native
import Complexity.Tactic.PolyTime

/-! Plain `polytime` must invoke compositional, captured-local and named certificates. -/

open Turing.MultiTapeTM

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2)
    (encPair encNat encNat) encNat := by fun_prop

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 &&& p.2)
    (encPair encNat encNat) encNat := by polytime

example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableInPolyTime
    (B.genericModel.checkedConstant c) encUnary (encOption encNat) := by fun_prop

example (B : Cslib.WordRAM.Basis) (c : ℕ) : ComputableInPolyTime
    (B.genericModel.checkedConstant c) encUnary (encOption encNat) := by polytime

example (routine : ℕ × ℕ → ℕ)
    (hroutine : ComputableInPolyTime routine (encPair encNat encNat) encNat) :
    ComputableInPolyTime (fun p : ℕ × ℕ => routine (p.2, p.1))
      (encPair encNat encNat) encNat := by polytime

namespace PlainDriverTests

-- Keep this body opaque to compositional search: the named certificate carries the contract.
@[irreducible] def checkedNamedConstant (B : Cslib.WordRAM.Basis) (limit c w : ℕ) : Option ℕ :=
  if c ≤ limit then B.genericModel.checkedConstant c w else none

@[program_certificate hbound]
theorem checkedNamedConstant_polyTime (B : Cslib.WordRAM.Basis) (limit c : ℕ)
    (hbound : c ≤ limit) : ComputableInPolyTime (checkedNamedConstant B limit c)
      encUnary (encOption encNat) := by
  unfold checkedNamedConstant
  simp only [ite_eq_left hbound]
  exact Cslib.WordRAM.checkedConstant_polyTime B c

-- `fun_prop` cannot discharge the contract; named lookup must expose and solve it through Aesop.
example (B : Cslib.WordRAM.Basis) (c : ℕ) :
    ComputableInPolyTime (checkedNamedConstant B c c) encUnary (encOption encNat) := by
  fail_if_success fun_prop
  polytime

end PlainDriverTests
