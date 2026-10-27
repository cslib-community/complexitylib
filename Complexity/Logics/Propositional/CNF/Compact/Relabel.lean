/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.Compact
public import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Count

/-!
# First-occurrence order under injective CNF relabeling

Compaction assigns the position of a variable's first literal occurrence. The list of distinct
variables keeps its order under this renaming, even though compact names may have gaps.

## Main results

* `Cslib.Logic.PL.CNF.distinctVars_relabel_of_injOn`,
  `Cslib.Logic.PL.CNF.numVars_relabel_of_injOn`, `Cslib.Logic.PL.CNF.numVars_relabel`: injective
  variable relabelings preserve `distinctVars` order and `numVars`.
* `Cslib.Logic.PL.CNF.distinctVars_compact`: exact ordered list of compact variable names.
* `Cslib.Logic.PL.CNF.idxOf_distinctVars_compact`: graph vertex indices are preserved.

## References

These are elementary list identities for the existing CNF compaction operation.
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

private theorem idxOf_map_injOn (l : List V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ l}) {v : V} (hv : v ∈ l) :
    (l.map f).idxOf (f v) = l.idxOf v := by
  induction l with
  | nil => exact False.elim (List.not_mem_nil hv)
  | cons a l ih =>
    by_cases h : a = v
    · subst a
      simp
    · have hv' : v ∈ l := List.mem_of_ne_of_mem (Ne.symm h) hv
      have hfa : f a ≠ f v := fun heq => h (hf (by simp) hv heq)
      rw [List.map_cons, List.idxOf_cons_ne _ hfa, List.idxOf_cons_ne _ h]
      exact congrArg Nat.succ (ih
        (fun _ hx _ hy => hf (List.mem_cons_of_mem a hx) (List.mem_cons_of_mem a hy)) hv')

private theorem selectDistinct_map_injOn (l : List V) (w : List Bool) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ l}) :
    Cslib.Complexity.selectDistinct (l.map f) w =
      (Cslib.Complexity.selectDistinct l w).map f := by
  simp only [Cslib.Complexity.selectDistinct, List.zipIdx_map, List.filter_map,
    List.map_map, Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  congr 1
  apply List.filter_congr
  intro e he
  simp only [idxOf_map_injOn l f hf (List.fst_mem_of_mem_zipIdx he)]

/-- Relabeling injectively on the used variables preserves their first-occurrence order. -/
theorem distinctVars_relabel_of_injOn (φ : CNF V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ φ.vars}) :
    (φ.relabel f).distinctVars = φ.distinctVars.map f := by
  simp only [distinctVars, vars_relabel, List.length_map]
  exact selectDistinct_map_injOn _ _ _ hf

/-- Relabeling injectively on the occurring variables preserves `numVars`. -/
theorem numVars_relabel_of_injOn (φ : CNF V) (f : V → W)
    (hf : Set.InjOn f {v | v ∈ φ.vars}) :
    (φ.relabel f).numVars = φ.numVars := by
  rw [← length_distinctVars, ← length_distinctVars, distinctVars_relabel_of_injOn φ f hf,
    List.length_map]

/-- Relabeling along an injective map preserves `numVars`. -/
@[simp]
theorem numVars_relabel {f : V → W} (hf : Function.Injective f) (φ : CNF V) :
    (φ.relabel f).numVars = φ.numVars :=
  numVars_relabel_of_injOn φ f fun _ _ _ _ h => hf h

variable [BEq V] [LawfulBEq V]

/-- Compaction preserves the exact order of the distinct variables. Any lawful Boolean
equality on the original variable type gives the same first-occurrence names. -/
theorem distinctVars_compact (φ : CNF V) :
    φ.compact.distinctVars = φ.distinctVars.map φ.vars.idxOf := by
  have h := distinctVars_relabel_of_injOn φ φ.vars.idxOf
    (fun _ ha _ _ h => (List.idxOf_inj ha).1 h)
  simpa only [compact, List.idxOf, beq_eq_decide] using h

/-- The index of a used variable in the distinct-variable list is unchanged by compaction. -/
theorem idxOf_distinctVars_compact (φ : CNF V) {v : V} (hv : v ∈ φ.vars) :
    φ.compact.distinctVars.idxOf (φ.vars.idxOf v) = φ.distinctVars.idxOf v := by
  rw [distinctVars_compact]
  have hf : Set.InjOn φ.vars.idxOf {v | v ∈ φ.distinctVars} :=
    fun _ ha _ _ h => (List.idxOf_inj (mem_distinctVars.mp ha)).1 h
  simpa only [List.idxOf, beq_eq_decide] using
    idxOf_map_injOn φ.distinctVars φ.vars.idxOf hf (mem_distinctVars.mpr hv)

/-- Drawing data indexed by the distinct-variable list retain the same lookup after compaction. -/
theorem getD_idxOf_distinctVars_compact {P : Type*} (φ : CNF V) (data : List P) (fallback : P)
    {v : V} (hv : v ∈ φ.vars) :
    data.getD (φ.compact.distinctVars.idxOf (φ.vars.idxOf v)) fallback =
      data.getD (φ.distinctVars.idxOf v) fallback := by
  rw [idxOf_distinctVars_compact φ hv]

/-- Compaction relabels the full variable-occurrence list in its original order. -/
theorem vars_compact (φ : CNF V) : φ.compact.vars = φ.vars.map φ.vars.idxOf := by
  simp only [compact, vars_relabel, List.idxOf, beq_eq_decide]

/-- Every used variable keeps its exact literal-occurrence count after compaction. -/
theorem count_vars_compact (φ : CNF V) {v : V} (hv : v ∈ φ.vars) :
    φ.compact.vars.count (φ.vars.idxOf v) = φ.vars.count v := by
  rw [vars_compact]
  simp only [List.count_eq_countP, List.countP_map, Function.comp_def]
  apply List.countP_congr
  intro w _
  simp only [beq_iff_eq]
  rw [eq_comm, List.idxOf_inj hv, eq_comm]

/-- A bound on all original literal-occurrence counts also bounds every compact variable. -/
theorem count_vars_compact_le (φ : CNF V) {k : ℕ} (h : ∀ v, φ.vars.count v ≤ k) :
    ∀ i, φ.compact.vars.count i ≤ k := by
  intro i
  by_cases hi : i ∈ φ.compact.vars
  · rw [vars_compact] at hi
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hi
    rw [count_vars_compact φ hv]
    exact h v
  · rw [List.count_eq_zero.mpr hi]
    exact Nat.zero_le _

end Cslib.Logic.PL.CNF

namespace Cslib.Logic.PL

/-- Relabeling preserves literal-occurrence order and both occurrence indices. -/
theorem occurrences_relabel {V W : Type*} (φ : CNF V) (f : V → W) :
    occurrences (φ.relabel f) =
      (occurrences φ).map (fun o => (o.1, o.2.1, (f o.2.2.1, o.2.2.2))) := by
  simp only [occurrences, CNF.relabel, Clause.relabel, List.zipIdx_map,
    List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
    Prod.map_fst, Prod.map_snd, id_eq]
  rfl

end Cslib.Logic.PL
