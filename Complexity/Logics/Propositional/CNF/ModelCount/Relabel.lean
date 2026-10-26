/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ModelCount

/-!
# Model counts under CNF relabelling

Relabelling preserves the count when it is injective on the occurring variables. Collisions
outside that support are harmless, including when the source variable type is infinite or empty.

## Main results

* `Cslib.Logic.PL.CNF.modelCount_relabel_of_injOn`: support-injective relabelling preserves counts.
* `Cslib.Logic.PL.CNF.modelCount_relabel`: globally injective relabelling preserves counts.

## References

These are original elementary transport proofs for the existing occurring-variable model count.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V W : Type*} [DecidableEq V]

/-- Relabelling injectively on the occurring variables preserves the number of satisfying
assignments. No injectivity is required outside those variables. -/
theorem modelCount_relabel_of_injOn [DecidableEq W] {f : V → W} (φ : CNF V)
    (hf : Set.InjOn f {v | v ∈ φ.vars}) : (φ.relabel f).modelCount = φ.modelCount := by
  have hf' : Function.Injective (fun v : φ.vars.toFinset => f v) :=
    fun a b h => Subtype.ext (hf (List.mem_toFinset.1 a.2) (List.mem_toFinset.1 b.2) h)
  refine modelCount_eq_card_filter (fun σ (v : φ.vars.toFinset) => σ (f v))
    (fun τ => φ.eval (φ.extendAssignment τ) = true) (fun σ τ _ _ => ?_) fun τ => ?_
  · rw [vars_relabel, List.forall_mem_map, funext_iff, Subtype.forall]
    simp only [List.mem_toFinset]
  · constructor
    · intro hτ
      let σ := Function.extend (fun v : φ.vars.toFinset => f v) τ (fun _ => false)
      have he (v : V) (hv : v ∈ φ.vars) : σ (f v) = φ.extendAssignment τ v := by
        rw [extendAssignment_of_mem _ hv]
        exact hf'.extend_apply τ (fun _ => false) ⟨v, List.mem_toFinset.2 hv⟩
      refine ⟨σ, ?_, funext fun v => ?_⟩
      · rw [eval_relabel]
        exact (eval_congr he).trans hτ
      · exact hf'.extend_apply τ (fun _ => false) v
    · rintro ⟨σ, hσ, rfl⟩
      rw [eval_relabel] at hσ
      rw [← hσ]
      exact eval_congr fun v hv => extendAssignment_of_mem _ hv

/-- **Relabelling along an injective map preserves the number of satisfying assignments.** -/
theorem modelCount_relabel [DecidableEq W] {f : V → W} (hf : Function.Injective f)
    (φ : CNF V) : (φ.relabel f).modelCount = φ.modelCount :=
  modelCount_relabel_of_injOn φ (fun _ _ _ _ h => hf h)

end Cslib.Logic.PL.CNF
