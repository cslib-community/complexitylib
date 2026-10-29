/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Sampling
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Crypto.Computational.GGM.Evaluation
import Complexity.Tactic.PPT

/-! PPT certificates reuse deterministic automation and require explicit sampling certificates. -/

namespace ComplexityTests.PPT

open Cslib Cslib.Probability Turing.MultiTapeTM

-- Nested deterministic loops remain reusable inside a closed probabilistic computation.
example {α : Type} (input : α ↪ List Bool) (N C : α → ℕ)
    (call : α → ℕ → ℕ → Bool)
    (hN : ComputableInPolyTime N input encUnary)
    (hC : ComputableInPolyTime C input encUnary)
    (hcall : ComputableInPolyTime
      (fun p : (α × ℕ) × ℕ => call p.1.1 p.1.2 p.2)
      (encPair (encPair input encUnary) encUnary) encBool) :
    IsPPTOn input encBool (fun a => pure
      (BitString.listStrictMajority ((List.range (N a)).map fun i =>
        ((List.range (C a)).map (call a i)).foldl Bool.xor false))) := by
  fail_if_success (clear hcall; ppt)
  ppt

example (offset : ℕ) : IsPPTOn encUnary encUnary (fun n => pure (n + offset)) := by fun_prop

-- This is a direct client of the existing GGM evaluator certificate, with no new machine table.
example {generator : List Bool → List Bool}
    (hgenerator : ComputableInPolyTime generator encBits encBits) :
    IsPPTOn (encPair encBits encBits) encBits
      (fun pair => pure (Crypto.GGM.eval generator pair.1 pair.2)) := by fun_prop

example : IsPPTOn encBits encBool (fun _ => ProbComp.uniform Bool) := by fun_prop

-- The frontend allows this sampler, but finite uniformity is not a PPT automation rule.
example : True := by
  let encFin3 : Fin 3 ↪ List Bool := Fin.valEmbedding.trans encNat
  fail_if_success have : IsPPTOn encBits encFin3 (fun _ => ProbComp.uniform (Fin 3)) := by fun_prop
  trivial

-- Reuse output bounds on a concrete PPT program without unpacking machines.
example :
    ∃ c d : ℕ, ∀ (n : ℕ) (b : ℕ), b ∈ (ProbComp.eval (pure (n + 1) : ProbComp ℕ)).support →
      (encUnary b).length ≤ c * ((encUnary n).length + 1) ^ d :=
  (by fun_prop : IsPPTOn encUnary encUnary (fun n => pure (n + 1))).length_le

-- A state-changing oracle would be observable if the deterministic embedding queried it.
example {input : List Bool} (machine : Turing.MultiTapeTM 0 Bool Unit) (fuel : ℕ)
    (cfg : Turing.MultiTapeMachine.Config 0 Bool Unit Bool input) (initial : ℕ) :
    (OracleComp.interpret (m := StateT ℕ PMF)
      (fun _ : Unit => modifyGet fun state => ([true], state + 1))
      ((Turing.MultiTapePTM.ofDeterministic machine).runConfigFrom (pure false)
        (fun _ _ => OracleComp.query ()) fuel cfg)).run initial =
      PMF.pure ({ cfg with tapes := machine.runFrom cfg.tapes fuel }, initial) := by
  apply Turing.MultiTapePTM.run_interpret_runConfigFrom_ofDeterministic
    (coinLaw := PMF.pure false)
  intro state
  simp

end ComplexityTests.PPT
