/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence.Positions

/-!
# Actual occurrence coordinates under variable renaming

Renaming preserves every constraint and argument position, including repeated or identified
names. The forward map reads the original renamed variable; it needs no injectivity premise.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V W : Type}

/-- Rename variables at an actual occurrence while keeping its two original positions. -/
@[expose] def relabelOccurrence (F : CSP Rel V) (f : V → W) (o : F.Occurrence) :
    (F.relabel f).Occurrence :=
  ⟨⟨o.1.val, by simpa only [CSP.relabel, List.length_map] using o.1.isLt⟩,
    ⟨o.2.val, by
      simpa only [CSP.relabel, List.getElem_map, Constraint.relabel, List.length_map]
        using o.2.isLt⟩⟩

/-- Variable renaming retains the exact original constraint position. -/
theorem relabelOccurrence_constraint (F : CSP Rel V) (f : V → W) (o : F.Occurrence) :
    (relabelOccurrence F f o).1.val = o.1.val := rfl

/-- Variable renaming retains the exact original argument position. -/
theorem relabelOccurrence_argument (F : CSP Rel V) (f : V → W) (o : F.Occurrence) :
    (relabelOccurrence F f o).2.val = o.2.val := rfl

/-- The actual occurrence getter reads the original variable through the supplied map. -/
theorem var_relabelOccurrence (F : CSP Rel V) (f : V → W) (o : F.Occurrence) :
    (relabelOccurrence F f o).var = f o.var := by
  simp only [Occurrence.var, relabelOccurrence, CSP.relabel, List.getElem_map,
    Constraint.relabel]

/-- Renaming never identifies distinct positions, even when it identifies variable names. -/
theorem relabelOccurrence_injective (F : CSP Rel V) (f : V → W) :
    Function.Injective (relabelOccurrence F f) := by
  intro o p he
  exact Occurrence.eq_of_positions (congrArg (fun q => q.1.val) he)
    (congrArg (fun q => q.2.val) he)

/-- Every occurrence after renaming comes from an original indexed occurrence. -/
theorem exists_relabelOccurrence (F : CSP Rel V) (f : V → W)
    (o : (F.relabel f).Occurrence) : ∃ p : F.Occurrence, relabelOccurrence F f p = o := by
  let i : Fin F.length := ⟨o.1.val, by
    simpa only [CSP.relabel, List.length_map] using o.1.isLt⟩
  let p : F.Occurrence := ⟨i, ⟨o.2.val, by
    simpa only [CSP.relabel, List.getElem_map, Constraint.relabel, List.length_map]
      using o.2.isLt⟩⟩
  exact ⟨p, Occurrence.eq_of_positions rfl rfl⟩

end Cslib.Logic.PL.CSP
