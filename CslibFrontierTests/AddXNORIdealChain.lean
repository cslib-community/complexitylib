/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Cryptanalysis.AddXNORIdealChain

/-!
# Ideal-chain experiment clients

Distinct indexed tables, inverse calls, a non-self-inverse permutation and a private-coin
adversary exercise the actual model. The search client's impossible planted trace remains an
obstruction to the manuscript's literal frontier sampler, not to these valid-table games.
-/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

namespace IdealChainClient

/-- A three-cycle: forward and inverse evaluation differ. -/
def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

example : cycle 0 = 1 ∧ cycle.symm 0 = 2 := by decide

/-- One branch uses a three-cycle, the other its inverse, independently at each label. -/
def family : Label 2 → Equiv.Perm (Fin 3) := fun label =>
  if label.2 then cycle.symm else cycle

example : chain family (fun _ => false) 0 = 2 ∧
    chain family (fun i => i.val = 1) 0 = 0 := by decide

example : Family.eval family ((0, false), .inverse 1) = 0 := by decide

/-- Sample a private bit, make a forward call followed by its inverse, and use the bit as the
operator word. The inverse argument depends on the fresh forward answer. -/
def attack (seed _target : Fin 3) : ProbOracleComp (Spec 2 (Fin 3)) (Operators 2) := do
  let bit ← ProbOracleComp.sample (ProbComp.unifFin 1)
  let image ← ProbOracleComp.query ((0, false), .forward seed)
  let _ ← ProbOracleComp.query ((0, false), .inverse image)
  return fun _ => bit.val = 1

example (seed target : Fin 3) : ProbOracleComp.IsQueryBounded (attack seed target) 2 := by
  have hsample := ProbOracleComp.IsQueryBounded.sample (spec := Spec 2 (Fin 3))
    (ProbComp.unifFin 1)
  simpa only [attack, Nat.zero_add, Nat.add_zero] using hsample.bind fun bit =>
    (ProbOracleComp.IsQueryBounded.query ((0, false), .forward seed)).bind fun image =>
      (ProbOracleComp.IsQueryBounded.query ((0, false), .inverse image)).bind fun _ =>
        IsCostBounded.pure (fun _ : Fin 2 => decide (bit.val = 1)) 0

example : plantedSearch attack = (do
    let seed ← PMF.uniformOfFintype (Fin 3)
    let bits ← PMF.uniformOfFintype (Operators 2)
    ((interpret Family.probAnswer (plantedProgram seed bits attack)).run (fun _ => [])).map
      Prod.fst) := plantedSearch_eq_lazy attack

/-- With no layers the planted target is the seed and the sole operator string verifies. -/
example : plantedSearch (q := 0) (Word := Fin 3)
    (fun _ _ => pure (fun i => Fin.elim0 i)) = PMF.pure true := by
  simp [plantedSearch, chain, evaluate, Family.probEval]

end IdealChainClient
