/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.OfFnGetD
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

/-!
# Tractability from a common Boolean constant

A fixed finite Boolean constraint language preserved by either unary constant has a native
polynomial-time satisfiability problem. The decider checks exact arities and rejects constraints
using an empty relation. Otherwise the common constant satisfies the whole instance. This
includes empty and nullary relations and arbitrary binary variable labels.

These are the first two cases of [Chen2006CSP], Theorem 3.20. Testing relation nonemptiness is
fixed preprocessing of a finite alphabet, not a uniform solver for supplied truth tables.

## Main results

* `Cslib.Complexity.CSPSAT.mem_P_of_constant`: native P from a common unary constant.
-/

public section

namespace Cslib.Complexity.CSPSAT

open Cslib.Logic.PL Turing.MultiTapeTM

variable {Rel : Type}

private theorem nonempty_of_eval {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
    {c : Constraint Rel ℕ} (hc : c.2.length = arity c.1) {σ : ℕ → Bool}
    (hσ : c.eval sem σ = true) : (CSP.booleanRelation arity sem c.1).Nonempty := by
  refine ⟨fun i => σ (c.2.getD i 0), ?_⟩
  change sem c.1 (List.ofFn fun i : Fin (arity c.1) => σ (c.2.getD i 0)) = true
  change sem c.1 (c.2.map σ) = true at hσ
  rwa [List.ofFn_getD_eq_map_of_length σ 0 hc]

/-- A common unary constant gives native polynomial-time satisfiability for a fixed finite
Boolean constraint language. Empty relations are rejected before applying the constant model. -/
theorem mem_P_of_constant [Finite Rel] (encRel : Rel ↪ List Bool) (arity : Rel → ℕ)
    (sem : Rel → List Bool → Bool) (b : Bool)
    (hb : CSP.HasPolymorphism arity sem (fun _ : Fin 1 → Bool => b)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) := by
  classical
  let possible : Rel → Bool := fun R => decide ((CSP.booleanRelation arity sem R).Nonempty)
  let solver : CSP Rel ℕ → Bool := fun F =>
    F.validArity arity && F.all (fun c => possible c.1)
  have hp : ComputableInPolyTime possible encRel encBool := ComputableInPolyTime.of_finite _
  have hall : ComputableInPolyTime
      (fun F : CSP Rel ℕ => F.all (fun c => possible c.1)) (encCSP encRel encNat) encBool := by
    exact ComputableInPolyTime.allWithInput ComputableInPolyTime.id'
      ((hp.comp (ComputableInPolyTime.fst _ _)).comp (ComputableInPolyTime.snd _ _))
  have hs : ComputableInPolyTime solver (encCSP encRel encNat) encBool := by
    exact ComputableInPolyTime.bool_and.comp
      ((CSP.computableInPolyTime_validArity encRel arity).prod hall)
  refine ⟨solver, hs, fun F => ?_⟩
  change F.WellFormed arity ∧ F.Satisfiable sem ↔ solver F = true
  simp only [solver, Bool.and_eq_true, CSP.validArity_eq_true_iff, List.all_eq_true]
  constructor
  · rintro ⟨hF, σ, hσ⟩
    refine ⟨hF, fun c hc => ?_⟩
    exact decide_eq_true (nonempty_of_eval (hF c hc) ((List.all_eq_true.mp hσ) c hc))
  · rintro ⟨hF, hpossible⟩
    refine ⟨hF, fun _ => b, List.all_eq_true.mpr (fun c hc => ?_)⟩
    have hne : (CSP.booleanRelation arity sem c.1).Nonempty :=
      of_decide_eq_true (hpossible c hc)
    have hconst := (CSP.hasPolymorphism_const_iff arity sem b).mp hb c.1 hne
    change sem c.1 (List.ofFn (fun _ : Fin (arity c.1) => b)) = true at hconst
    simpa only [Constraint.eval, List.ofFn_const, List.map_const', hF c hc] using hconst

end Cslib.Complexity.CSPSAT
