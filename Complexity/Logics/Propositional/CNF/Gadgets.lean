/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF
import Mathlib.Data.List.Basic

/-!
# Gluing CNF gadgets with private auxiliary variables

A gadget has shared variables `V` and auxiliary variables `W`. Gluing a finite list of gadgets
tags every auxiliary variable with its site, keeping auxiliary variables of different sites
distinct. Only the shared variables connect the gadgets. A shared assignment extends to the
assembled formula exactly when it extends to every gadget separately.

This is the semantic substitution rule used when finite SAT reductions replace crossings by
fixed gadgets. It concerns satisfiability; geometric compatibility and resource bounds are
separate obligations.

## Main definitions

* `Cslib.Logic.PL.CNF.glue`: assemble gadgets with site-tagged auxiliary variables.

## Main results

* `Cslib.Logic.PL.CNF.eval_glue`: evaluate the assembled formula one gadget at a time.
* `Cslib.Logic.PL.CNF.exists_eval_glue_iff`: local auxiliary assignments can be chosen
  independently for a fixed shared assignment.
* `Cslib.Logic.PL.CNF.satisfiable_glue_iff`: the satisfiability substitution rule.
* `Cslib.Logic.PL.CNF.length_glue`, `Cslib.Logic.PL.CNF.length_vars_glue`: exact size identities.

## References

This indexed-list formulation of gadget gluing and its proofs are original.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V W I : Type*}

/-- Assemble gadgets sharing `V`, tagging each auxiliary variable with its gadget site. Repeated
sites repeat the same constraints and the same auxiliary variables. -/
def glue (sites : List I) (gadget : I → CNF (V ⊕ W)) : CNF (V ⊕ (I × W)) :=
  sites.flatMap fun i => (gadget i).relabel (Sum.map id (fun w => (i, w)))

/-- A global assignment satisfies the assembly exactly when it satisfies every relabelled gadget.
-/
theorem eval_glue (sites : List I) (gadget : I → CNF (V ⊕ W))
    (σ : V ⊕ (I × W) → Bool) :
    (glue sites gadget).eval σ = true ↔
      ∀ i ∈ sites, (gadget i).eval
        (Sum.elim (fun v => σ (.inl v)) (fun w => σ (.inr (i, w)))) = true := by
  rw [glue, eval_flatMap_eq_true_iff]
  refine forall₂_congr fun i _ => ?_
  rw [eval_relabel]
  have h : σ ∘ Sum.map id (fun w => (i, w)) =
      Sum.elim (fun v => σ (.inl v)) (fun w => σ (.inr (i, w))) := by
    funext x
    cases x <;> rfl
  rw [h]

/-- For a fixed assignment of the shared variables, the private assignments of distinct gadgets
can be chosen independently. -/
theorem exists_eval_glue_iff (sites : List I) (gadget : I → CNF (V ⊕ W)) (σ : V → Bool) :
    (∃ τ : I × W → Bool, (glue sites gadget).eval (Sum.elim σ τ) = true) ↔
      ∀ i ∈ sites, ∃ τ : W → Bool, (gadget i).eval (Sum.elim σ τ) = true := by
  classical
  constructor
  · rintro ⟨τ, hτ⟩ i hi
    exact ⟨fun w => τ (i, w), (eval_glue sites gadget (Sum.elim σ τ)).1 hτ i hi⟩
  · intro h
    let τ : I × W → Bool := fun p =>
      if hi : p.1 ∈ sites then (h p.1 hi).choose p.2 else false
    refine ⟨τ, (eval_glue sites gadget (Sum.elim σ τ)).2 ?_⟩
    intro i hi
    simpa only [τ, hi, dite_true, Sum.elim_inl, Sum.elim_inr] using (h i hi).choose_spec

/-- The assembly is satisfiable exactly when one shared assignment extends to each local gadget.
-/
theorem satisfiable_glue_iff (sites : List I) (gadget : I → CNF (V ⊕ W)) :
    (glue sites gadget).Satisfiable ↔
      ∃ σ : V → Bool, ∀ i ∈ sites,
        ∃ τ : W → Bool, (gadget i).eval (Sum.elim σ τ) = true := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun v => σ (.inl v), ?_⟩
    intro i hi
    exact ⟨fun w => σ (.inr (i, w)), (eval_glue sites gadget σ).1 hσ i hi⟩
  · rintro ⟨σ, hσ⟩
    obtain ⟨τ, hτ⟩ := (exists_eval_glue_iff sites gadget σ).2 hσ
    exact ⟨Sum.elim σ τ, hτ⟩

/-- The number of clauses is the sum of the numbers of clauses in the local gadgets. -/
theorem length_glue (sites : List I) (gadget : I → CNF (V ⊕ W)) :
    (glue sites gadget).length = (sites.map fun i => (gadget i).length).sum := by
  simp [glue, List.length_flatMap, CNF.relabel]

/-- Relabelling and gluing preserve every literal occurrence, including repetitions. -/
theorem length_vars_glue (sites : List I) (gadget : I → CNF (V ⊕ W)) :
    (glue sites gadget).vars.length = (sites.map fun i => (gadget i).vars.length).sum := by
  induction sites with
  | nil => rfl
  | cons i sites ih =>
    change ((gadget i).relabel (Sum.map id (fun w => (i, w))) ++ glue sites gadget).vars.length = _
    simp only [CNF.vars, List.flatten_append, List.map_append, List.length_append]
    change ((gadget i).relabel (Sum.map id (fun w => (i, w)))).vars.length +
      (glue sites gadget).vars.length = _
    rw [vars_relabel, List.length_map, ih]
    rfl

end Cslib.Logic.PL.CNF
