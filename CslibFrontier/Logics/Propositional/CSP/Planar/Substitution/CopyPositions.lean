/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.Table
import CslibFrontier.Foundations.Data.List.FlatMapPositions
import CslibFrontier.Computability.PolyTime.CSP.Gadget.Size

/-!
# Literal occurrence positions in fixed-gadget replacement

Every local occurrence in a source constraint's template has exactly its actual prefix
offset in the existing flat-mapped replacement body. The intervals are disjoint and exhaustive;
repeated source constraints, repeated names and empty templates do not change their identity.
No enumeration up to a variable name or supplied certificate entry is involved.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Src Rel : Type}

/-- The replacement's variable word retains every instantiated template position in order. -/
theorem vars_replaceGadgets (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) :
    (replaceGadgets B templates F).vars = F.zipIdx.flatMap fun ⟨⟨relation, scope⟩, i⟩ =>
      (templates relation).vars.map fun p =>
        if p.1 then 2 * (B * i + p.2) + 1 else 2 * scope.getD p.2 0 := by
  change (F.zipIdx.flatMap fun entry =>
    instantiate B entry.2 entry.1.2 (templates entry.1.1)).flatMap (fun ⟨_, scope⟩ => scope) = _
  rw [List.flatMap_assoc]
  change F.zipIdx.flatMap (fun entry =>
    (instantiate B entry.2 entry.1.2 (templates entry.1.1)).vars) = _
  simp only [instantiate, vars_relabel]

/-- Instantiating the preceding templates preserves their exact occurrence-prefix length. -/
theorem instantiatedPrefix_length (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) (i : ℕ) :
    ((F.zipIdx.take i).flatMap fun ⟨⟨relation, scope⟩, i⟩ =>
      (templates relation).vars.map fun p =>
        if p.1 then 2 * (B * i + p.2) + 1 else 2 * scope.getD p.2 0).length =
      occurrencePrefix templates F i := by
  simp only [List.length_flatMap, List.length_map, occurrencePrefix]
  conv_rhs => rw [← List.zipIdx_map_fst 0 F, List.map_take, List.map_map]
  simp only [← List.map_take, Function.comp_def]

/-- Local template positions shift into the actual replacement's bounded occurrence word. -/
theorem copyIndex_lt (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) {i j : ℕ} (hi : i < F.length)
    (hj : j < (templates F[i].1).vars.length) :
    occurrencePrefix templates F i + j < (replaceGadgets B templates F).vars.length := by
  have h := List.flatMap_prefix_add_lt F (fun c => (templates c.1).vars) hi hj
  simpa only [occurrencePrefix, vars_length_replaceGadgets, List.length_flatMap] using h

/-- The actual target getter reads the selected original template occurrence after renaming.
The equation is positional, so coincident source variables and duplicate rows remain distinct. -/
theorem getElem_vars_copyIndex (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ))
    (F : CSP Src ℕ) {i j : ℕ} (hi : i < F.length)
    (hj : j < (templates F[i].1).vars.length) :
    (replaceGadgets B templates F).vars[occurrencePrefix templates F i + j]'
      (copyIndex_lt B templates F hi hj) =
      let p := (templates F[i].1).vars[j]
      if p.1 then 2 * (B * i + p.2) + 1 else 2 * F[i].2.getD p.2 0 := by
  have hi' : i < F.zipIdx.length := by simpa only [List.length_zipIdx] using hi
  have hj' : j < ((templates F.zipIdx[i].1.1).vars.map fun p =>
      if p.1 then 2 * (B * F.zipIdx[i].2 + p.2) + 1
      else 2 * F.zipIdx[i].1.2.getD p.2 0).length := by
    simpa only [List.length_map, List.getElem_zipIdx] using hj
  have h := List.getElem_flatMap_prefix_add F.zipIdx
    (fun entry => (templates entry.1.1).vars.map fun p =>
    if p.1 then 2 * (B * entry.2 + p.2) + 1 else 2 * entry.1.2.getD p.2 0) hi' hj'
  simpa only [instantiatedPrefix_length, ← vars_replaceGadgets, List.getElem_zipIdx,
    List.getElem_map, Nat.zero_add] using h

/-- Different source or local positions remain different literal target occurrences. -/
theorem copyIndex_injective (templates : Src → CSP Rel (Bool × ℕ)) (F : CSP Src ℕ)
    {i j k q : ℕ} (hi : i < F.length) (hj : j < (templates F[i].1).vars.length)
    (hk : k < F.length) (hq : q < (templates F[k].1).vars.length)
    (he : occurrencePrefix templates F i + j = occurrencePrefix templates F k + q) :
    i = k ∧ j = q :=
  List.flatMap_prefix_add_injective F (fun c => (templates c.1).vars) hi hj hk hq he

/-- Every actual target occurrence comes from exactly one source copy and local position.
In particular no auxiliary padding or unused template port creates a target occurrence. -/
theorem exists_copyIndex (B : ℕ) (templates : Src → CSP Rel (Bool × ℕ)) (F : CSP Src ℕ)
    {index : ℕ} (hindex : index < (replaceGadgets B templates F).vars.length) :
    ∃ (i : ℕ) (hi : i < F.length) (j : ℕ), j < (templates F[i].1).vars.length ∧
      index = occurrencePrefix templates F i + j := by
  rw [vars_length_replaceGadgets] at hindex
  apply List.exists_flatMap_prefix_add F (fun c => (templates c.1).vars)
  simpa only [List.length_flatMap] using hindex

end Cslib.Complexity.CSP.GadgetRotation
