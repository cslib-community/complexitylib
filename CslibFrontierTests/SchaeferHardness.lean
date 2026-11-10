/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Problems.CSP.Hardness

/-!
# Native Boolean CSP hardness regression tests

The absent-six hypothesis has a concrete NAE instance. The reference lift is tested on
satisfiable and contradictory formulas, malformed scopes, repeated variables and large labels.
-/

namespace CslibFrontierTests.SchaeferHardness

open Cslib.Logic Cslib.Logic.PL Cslib.Complexity Turing.MultiTapeTM

private def naeArity (_ : Unit) : ℕ := 3

private def naeSem (_ : Unit) : List Bool → Bool
  | [x, y, z] => !((x == y) && (y == z))
  | _ => false

private theorem nae_missing : ¬ CSP.HasSchaeferPolymorphism naeArity naeSem := by
  unfold CSP.HasSchaeferPolymorphism CSP.HasPolymorphism IsPolymorphism
    CSP.booleanRelation naeArity
  simp only [Set.mem_ofPred_eq, not_or]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- The full native hard endpoint has no assumed solver or gadget premise.
example (encUnit : Unit ↪ List Bool) :
    NPComplete (encCSP encUnit encNat) (CSPSAT naeArity naeSem) :=
  CSPSAT.npComplete_of_not_hasSchaeferPolymorphism encUnit naeArity naeSem nae_missing

example : SelfDualThreeSAT.sem (true, false, true) [true, false, false, false] = true := by
  decide

example : (SelfDualThreeSAT.ofExactThreeSAT [[(2 ^ 80, true), (2 ^ 80, true),
    (2 ^ 80, true)]]).WellFormed SelfDualThreeSAT.arity := by decide

example : SelfDualThreeSAT.ofExactThreeSAT [[(7, true)]] ∉ SelfDualThreeSAT := by
  rw [SelfDualThreeSAT.ofExactThreeSAT_mem_iff]
  simp [ExactThreeSAT]

example : SelfDualThreeSAT.ofExactThreeSAT
    [[(9, true), (9, true), (9, true)], [(9, false), (9, false), (9, false)]] ∉
      SelfDualThreeSAT := by
  rw [SelfDualThreeSAT.ofExactThreeSAT_mem_iff]
  simp [ExactThreeSAT, CNF.Satisfiable, CNF.eval, Clause.eval, Literal.eval]

example : SelfDualThreeSAT.ofExactThreeSAT [] ∈ SelfDualThreeSAT := by
  rw [SelfDualThreeSAT.ofExactThreeSAT_mem_iff]
  exact ⟨by simp, fun _ => false, rfl⟩

end CslibFrontierTests.SchaeferHardness
