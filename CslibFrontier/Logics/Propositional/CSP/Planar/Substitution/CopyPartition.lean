/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.BoundaryPartition
public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyPositions
import CslibFrontier.Foundations.Data.List.FlatMapPositions

/-!
# The disjoint occurrence partition across actual gadget copies

Every fixed gadget contributes its free and auxiliary words at the literal replacement
prefix offset. Across all source constraint positions these words partition all actual target
occurrences. Empty blocks and closed components are retained, without assumptions on source
names, source arities or source certificates.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- Each copy's full shifted occurrence word enumerates exactly its literal target interval. -/
theorem shifted_boundaryBlocks_perm_range
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (F : CSP Src ℕ) (r : Src) (i : ℕ) :
    ((freeBoundaryBlocks (gadgets r) (witnesses r) ++
      auxiliaryBoundaryBlocks (gadgets r) (witnesses r)).flatten.map
        (occurrencePrefix (fun s => (gadgets s).template) F i + ·)).Perm
      ((List.range (gadgets r).template.vars.length).map
        (occurrencePrefix (fun s => (gadgets s).template) F i + ·)) := by
  have hp := (flatten_boundaryBlocks_perm_range (gadgets r) (witnesses r)).map
    (occurrencePrefix (fun s => (gadgets s).template) F i + ·)
  have hl : (gadgets r).body.occurrences.length = (gadgets r).template.vars.length := by
    rw [PPGadget.template, vars_relabel, List.length_map, ← CSP.map_occurrences,
      List.length_map]
  simpa only [hl] using hp

/-- The complete shifted copy words are duplicate-free before regrouping free blocks into
source-variable cycles. In particular duplicate source constraints remain separate copies. -/
theorem nodup_shifted_boundaryBlocks
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (F : CSP Src ℕ) :
    (F.zipIdx.flatMap fun ⟨⟨relation, _⟩, i⟩ =>
      (freeBoundaryBlocks (gadgets relation) (witnesses relation) ++
        auxiliaryBoundaryBlocks (gadgets relation) (witnesses relation)).flatten.map
          (occurrencePrefix (fun r => (gadgets r).template) F i + ·)).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨?_, ?_⟩
  · intro entry _
    exact (nodup_flatten_boundaryBlocks (gadgets entry.1.1) (witnesses entry.1.1)).map
      (fun _ _ he => Nat.add_left_cancel he)
  · apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij
    apply List.disjoint_left.mpr
    intro index hleft hright
    have hl := (shifted_boundaryBlocks_perm_range gadgets witnesses F
      F.zipIdx[i].1.1 F.zipIdx[i].2).mem_iff.mp hleft
    have hr := (shifted_boundaryBlocks_perm_range gadgets witnesses F
      F.zipIdx[j].1.1 F.zipIdx[j].2).mem_iff.mp hright
    simp only [List.mem_map, List.mem_range, List.getElem_zipIdx, Nat.zero_add] at hl hr
    obtain ⟨p, hp, he⟩ := hl
    obtain ⟨q, hq, he'⟩ := hr
    have hiF : i < F.length := by simpa only [List.length_zipIdx] using hi
    have hp' : p < (gadgets F[i].rel).template.vars.length := by
      have hl := congrArg (fun entry : Constraint Src ℕ × ℕ =>
        (gadgets entry.1.1).template.vars.length) (List.getElem_zipIdx (l := F) (i := i) hi)
      exact hl ▸ hp
    have hpos := List.flatMap_prefix_add_lt_of_lt (q := q) F
      (fun c => (gadgets c.rel).template.vars)
      hiF hp' hij
    exact (Nat.ne_of_lt hpos) (he.trans he'.symm)

/-- The shifted copy words cover exactly the actual target occurrence interval, on all raw
source bodies. This is not yet a statement about their regrouped vertex-cycle order or genus. -/
theorem mem_shifted_boundaryBlocks_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) (index : ℕ) :
    index ∈ (F.zipIdx.flatMap fun ⟨⟨relation, _⟩, i⟩ =>
      (freeBoundaryBlocks (gadgets relation) (witnesses relation) ++
        auxiliaryBoundaryBlocks (gadgets relation) (witnesses relation)).flatten.map
          (occurrencePrefix (fun r => (gadgets r).template) F i + ·)) ↔
      index < (replaceGadgets B (fun r => (gadgets r).template) F).vars.length := by
  constructor
  · intro hm
    obtain ⟨entry, he, hm⟩ := List.mem_flatMap.mp hm
    have hp :=
      (shifted_boundaryBlocks_perm_range gadgets witnesses F entry.1.1 entry.2).mem_iff.mp hm
    obtain ⟨hi, hentry⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp he)
    obtain ⟨j, hj, hindex⟩ := List.mem_map.mp hp
    rw [← hindex]
    apply copyIndex_lt B _ F hi
    have hl := congrArg (fun c : Constraint Src ℕ => (gadgets c.rel).template.vars.length) hentry
    rw [hl]
    exact List.mem_range.mp hj
  · intro htarget
    obtain ⟨i, hsource, j, hj, rfl⟩ :=
      exists_copyIndex B (fun r => (gadgets r).template) F htarget
    apply List.mem_flatMap.mpr
    refine ⟨(F[i], i), ?_, ?_⟩
    · exact List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hsource, rfl⟩)
    · apply (shifted_boundaryBlocks_perm_range gadgets witnesses F F[i].rel i).mem_iff.mpr
      exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

/-- Reordering all literal copy words only permutes the target occurrence enumeration.
The target binary names do not affect this positional partition. -/
theorem shifted_boundaryBlocks_perm_target_range
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (witnesses : ∀ r, GadgetWitness (gadgets r)) (B : ℕ) (F : CSP Src ℕ) :
    (F.zipIdx.flatMap fun ⟨⟨relation, _⟩, i⟩ =>
      (freeBoundaryBlocks (gadgets relation) (witnesses relation) ++
        auxiliaryBoundaryBlocks (gadgets relation) (witnesses relation)).flatten.map
          (occurrencePrefix (fun r => (gadgets r).template) F i + ·)).Perm
      (List.range (replaceGadgets B (fun r => (gadgets r).template) F).vars.length) := by
  apply (List.perm_ext_iff_of_nodup (nodup_shifted_boundaryBlocks gadgets witnesses F)
    List.nodup_range).mpr
  intro index
  rw [mem_shifted_boundaryBlocks_iff gadgets witnesses B, List.mem_range]

end Cslib.Complexity.CSP.GadgetRotation
