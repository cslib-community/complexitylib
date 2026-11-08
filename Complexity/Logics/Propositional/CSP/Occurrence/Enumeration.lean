/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CSP.Occurrence

/-!
# Deterministic typed occurrence enumeration

`incidenceList` lists every positional incidence in constraint and scope order.
`occurrences_eq_map_incidenceList` identifies its records with the existing executable scan.
The Boolean validity instance supports finite scans without importing augmentation.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type*} {F : CSP Rel V}

/-- Positional incidences in constraint order and then argument order. This is a typed view of
`CSP.occurrences`, without choosing representatives or identifying repeated constraints. -/
@[expose] def incidenceList (F : CSP Rel V) : List (Occurrence F) :=
  (List.ofFn fun i : Fin F.length =>
    List.ofFn fun j : Fin F[i].2.length => (⟨i, j⟩ : Occurrence F)).flatten

/-- Every incidence appears in the deterministic scan. -/
theorem mem_incidenceList (o : Occurrence F) : o ∈ incidenceList F := by
  rcases o with ⟨i, j⟩
  exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩,
    List.mem_ofFn.mpr ⟨j, rfl⟩⟩

instance (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool) :
    Decidable (ValidLabeling sem f) :=
  inferInstanceAs (Decidable (∀ i : Fin F.length,
    sem F[i].1 (localTuple f i) = true))

/-- Typed and untyped enumeration retain exactly the same order and positions. -/
theorem occurrences_eq_map_incidenceList (F : CSP Rel V) :
    F.occurrences = (incidenceList F).map Occurrence.record := by
  have he : F.occurrences =
      F.zipIdx.flatMap (fun c => c.1.2.zipIdx.map fun v => (c.2, v.2, v.1)) := by
    simp only [CSP.occurrences, Cslib.Logic.PL.occurrences, varCNF,
      List.zipIdx_map, List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def,
      Prod.map, id_eq]
  rw [he]
  unfold incidenceList
  conv_lhs => rw [← List.ofFn_getElem (xs := F.zipIdx)]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add]
  simp only [List.flatMap, List.map_flatten, List.map_ofFn, Function.comp_def]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp only [Fin.val_cast]
  conv_lhs => rw [← List.ofFn_getElem (xs := F[i.val].2.zipIdx)]
  simp only [List.length_zipIdx, List.getElem_zipIdx, Nat.zero_add, List.map_ofFn]
  rfl

/-- Positional incidences are not duplicated by the typed scan. -/
theorem incidenceList_nodup (F : CSP Rel V) : (incidenceList F).Nodup := by
  apply List.Nodup.of_map (f := Occurrence.record)
  rw [← occurrences_eq_map_incidenceList]
  exact occurrences_nodup F

end Cslib.Logic.PL.CSP
