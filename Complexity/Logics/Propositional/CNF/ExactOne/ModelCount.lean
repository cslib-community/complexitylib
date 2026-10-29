/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ExactOne
public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Logics.Propositional.CNF.ModelCount.Relabel

/-!
# Counting exact-one satisfying assignments

The exact-one count reuses `CNF.modelCount` through the ordinary CNF encoding, which preserves
both assignments and occurring variables. Variables outside the formula are not counted.

## Main definitions

* `CNF.oneModelCount`: the exact-one satisfying-assignment count.

## Main results

* `CNF.oneModelCount_eq_card_filter`: count through a finite assignment representation.
* `CNF.oneModelCount_relabel_of_injOn`: support-injective relabelling preserves the count.
* `CNF.oneModelCount_compact`: compact numbering preserves the count.

## References

These are original consequences of the ordinary CNF model-count API.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V W : Type*} [DecidableEq V]

/-- The number of exact-one satisfying assignments on the occurring variables. -/
def oneModelCount (φ : CNF V) : ℕ := φ.oneEncoding.modelCount

/-- Count exact-one assignments through any faithful finite representation of them. -/
theorem oneModelCount_eq_card_filter {ι : Type*} [Fintype ι] {φ : CNF V}
    (f : (V → Bool) → ι) (P : ι → Prop) [DecidablePred P]
    (hf : ∀ σ τ, φ.evalOne σ = true → φ.evalOne τ = true →
      (f σ = f τ ↔ ∀ v ∈ φ.vars, σ v = τ v))
    (hP : ∀ i, P i ↔ ∃ σ, φ.evalOne σ = true ∧ f σ = i) :
    φ.oneModelCount = (Finset.univ.filter P).card := by
  apply modelCount_eq_card_filter f P
  · intro σ τ hσ hτ
    simpa only [mem_vars_oneEncoding] using hf σ τ
      ((eval_oneEncoding σ φ) ▸ hσ) ((eval_oneEncoding τ φ) ▸ hτ)
  · simpa only [eval_oneEncoding] using hP

/-- An exact-one model exists exactly when the exact-one count is positive. -/
theorem oneModelCount_pos_iff {φ : CNF V} : 0 < φ.oneModelCount ↔ φ.OneSatisfiable := by
  rw [oneModelCount, modelCount_pos_iff, satisfiable_oneEncoding]

/-- Support-injective relabelling preserves the number of exact-one models. -/
theorem oneModelCount_relabel_of_injOn [DecidableEq W] {f : V → W} (φ : CNF V)
    (hf : Set.InjOn f {v | v ∈ φ.vars}) :
    (φ.relabel f).oneModelCount = φ.oneModelCount := by
  rw [oneModelCount, oneModelCount, oneEncoding_relabel]
  exact modelCount_relabel_of_injOn φ.oneEncoding
    (fun _ ha _ hb h => hf (mem_vars_oneEncoding.mp ha) (mem_vars_oneEncoding.mp hb) h)

/-- Injective relabelling preserves the number of exact-one models. -/
theorem oneModelCount_relabel [DecidableEq W] {f : V → W} (hf : Function.Injective f)
    (φ : CNF V) : (φ.relabel f).oneModelCount = φ.oneModelCount :=
  oneModelCount_relabel_of_injOn φ (fun _ _ _ _ h => hf h)

/-- Compact variable numbering preserves the number of exact-one models. -/
theorem oneModelCount_compact (φ : CNF V) : φ.compact.oneModelCount = φ.oneModelCount :=
  oneModelCount_relabel_of_injOn φ (fun _ ha _ _ h => (List.idxOf_inj ha).mp h)

/-- Reading original names at compact positions preserves exact-one evaluation. -/
theorem evalOne_compact (φ : CNF V) (σ : V → Bool) :
    φ.compact.evalOne (fun i => φ.vars[i]?.elim false σ) = φ.evalOne σ := by
  rw [compact, evalOne_relabel]
  apply evalOne_congr
  intro v hv
  simp [List.getElem?_idxOf hv]

/-- Compact variable numbering preserves exact-one satisfiability. -/
theorem oneSatisfiable_compact (φ : CNF V) : φ.compact.OneSatisfiable ↔ φ.OneSatisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ φ.vars.idxOf, by simpa only [compact, evalOne_relabel] using hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨fun i => φ.vars[i]?.elim false σ, (evalOne_compact φ σ).trans hσ⟩

end Cslib.Logic.PL.CNF
