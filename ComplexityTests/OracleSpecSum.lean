/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Languages.Probabilistic.Oracle
import Complexity.Crypto.Protocols.Signature.RandomOracle

/-! # Sums of oracle interfaces -/

namespace ComplexityTests.OracleSpecSum

open Cslib

-- A query of the sum reduces to the response type of its side at reducible transparency.
example : ((fun _ : Unit => Bool) ⊕ₒ (fun _ : ℕ => ℕ)) (.inl ()) = Bool := by with_reducible rfl
example : ((fun _ : Unit => Bool) ⊕ₒ (fun _ : ℕ => ℕ)) (.inr 3) = ℕ := by with_reducible rfl

-- Programs with private coins and a forger's calls are sums.
example (spec : Bool → Type) : probOracleSpec spec = unifSpec ⊕ₒ spec := rfl
example : Crypto.Protocols.ROMSignature.ForgerSpec Unit Bool ℕ (Fin 2) =
    (fun _ : Unit => ℕ) ⊕ₒ (fun _ : Bool => Fin 2) := rfl

private def left : OracleComp (fun _ : Unit => Bool) Bool := do
  let a ← OracleComp.query ()
  let b ← OracleComp.query ()
  return a && !b

-- An embedded program uses only its own side's handler; the other side is never called.
example :
    OracleComp.interpret
      (OracleComp.sumHandler (spec₁ := fun _ : Unit => Bool) (spec₂ := OracleSpec.empty)
        (fun _ => (some true : Option Bool)) (fun q => q.elim))
      (OracleComp.liftLeft left) = some false := by
  simp [left]

-- Sampling in a program with private coins is the left embedding.
example (program : ProbComp Bool) :
    ProbOracleComp.sample (spec := fun _ : Bool => Bool) program = OracleComp.liftLeft program :=
  ProbOracleComp.sample_eq_liftLeft program

end ComplexityTests.OracleSpecSum
