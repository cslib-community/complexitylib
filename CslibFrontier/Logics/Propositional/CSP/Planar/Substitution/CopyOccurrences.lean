/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.CopyLabels
public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceFlatMap
public import CslibFrontier.Computability.Complexity.Problems.CSP.IncidenceRelabel
import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.OccurrenceMaps

/-!
# Actual copied occurrences in the exact replacement body

The positional map follows the existing template renaming, instantiation and flat-map in
`replaceGadgets`. Its edge index is the already proved copy offset. Its constraint and argument
coordinates retain the local body row and scope positions, including duplicate records.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP

variable {Src Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {srcArity : Src → ℕ} {srcSem : Src → List Bool → Bool}

/-- The local occurrence after the two existing variable renamings, at unchanged positions. -/
@[expose] def instantiatedOccurrence {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) (B index : ℕ) (scope : List ℕ) (o : g.body.Occurrence) :
    (instantiate B index scope g.template).Occurrence :=
  CSP.relabelOccurrence g.template
    (fun p => if p.1 then 2 * (B * index + p.2) + 1 else 2 * scope.getD p.2 0)
    (CSP.relabelOccurrence g.body
      (Sum.elim (fun i => (false, i.val)) (fun j => (true, j.val))) o)

/-- The existing template and instantiation renamings keep literal positive argument order. -/
theorem argumentSuccessor_instantiatedOccurrence {n : ℕ} {R : Set (Fin n → Bool)}
    (g : PPGadget arity sem R) (B index : ℕ) (scope : List ℕ) (o : g.body.Occurrence) :
    argumentSuccessor (instantiatedOccurrence g B index scope o) =
      instantiatedOccurrence g B index scope (argumentSuccessor o) := by
  unfold instantiatedOccurrence instantiate PPGadget.template
  rw [argumentSuccessor_relabelOccurrence, argumentSuccessor_relabelOccurrence]

private def replacementLocalOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (instantiate B F.zipIdx[i.val].2 F.zipIdx[i.val].1.2
      (gadgets F.zipIdx[i.val].1.1).template).Occurrence := by
  have he : F.zipIdx[i.val] = (F[i.val], i.val) := by
    simpa only [Nat.zero_add] using
      (List.getElem_zipIdx (l := F) (i := i.val)
        (show i.val < F.zipIdx.length from by
          simpa only [List.length_zipIdx] using i.isLt))
  have hbody := congrArg (fun entry : Constraint Src ℕ × ℕ =>
    instantiate B entry.2 entry.1.2 (gadgets entry.1.1).template) he
  exact hbody.symm ▸ instantiatedOccurrence (gadgets F[i.val].rel) B i.val F[i.val].scope o

/-- Copy an actual local occurrence through the exact original replacement operation. -/
def replacementOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (replaceGadgets B (fun r => (gadgets r).template) F).Occurrence :=
  CSP.flatMapOccurrence F.zipIdx
    (fun ⟨⟨relation, scope⟩, i⟩ => instantiate B i scope (gadgets relation).template)
    ⟨i.val, by simpa only [List.length_zipIdx] using i.isLt⟩
    (replacementLocalOccurrence gadgets B F i o)

private theorem incidenceEdgeIndex_cast {H K : CSP Rel ℕ} (h : H = K)
    (o : H.Occurrence) : incidenceEdgeIndex (h ▸ o) = incidenceEdgeIndex o := by
  subst K
  rfl

private theorem record_cast {H K : CSP Rel ℕ} (h : H = K) (o : H.Occurrence) :
    (h ▸ o).record = o.record := by
  subst K
  rfl

private theorem argumentSuccessor_cast {H K : CSP Rel ℕ} (h : H = K) (o : H.Occurrence) :
    argumentSuccessor (h ▸ o) = h ▸ argumentSuccessor o := by
  subst K
  rfl

private theorem argumentSuccessor_replacementLocalOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    argumentSuccessor (replacementLocalOccurrence gadgets B F i o) =
      replacementLocalOccurrence gadgets B F i (argumentSuccessor o) := by
  unfold replacementLocalOccurrence
  rw [argumentSuccessor_cast, argumentSuccessor_instantiatedOccurrence]

private theorem record_replacementLocalOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (replacementLocalOccurrence gadgets B F i o).record =
      (instantiatedOccurrence (gadgets F[i.val].rel) B i.val F[i.val].scope o).record := by
  unfold replacementLocalOccurrence
  exact record_cast _ _

/-- The copied occurrence's edge index is the literal prefix offset used by the executed
table. This identifies positions, without rank preservation assumptions about dense names. -/
theorem incidenceEdgeIndex_replacementOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    incidenceEdgeIndex (replacementOccurrence gadgets B F i o) =
      occurrencePrefix (fun r => (gadgets r).template) F i.val + incidenceEdgeIndex o := by
  unfold replacementOccurrence replaceGadgets
  rw [incidenceEdgeIndex_flatMapOccurrence]
  have hp : (CSP.vars ((F.zipIdx.take i.val).flatMap fun entry =>
      instantiate B entry.2 entry.1.2 (gadgets entry.1.1).template)).length =
      occurrencePrefix (fun r => (gadgets r).template) F i.val := by
    rw [CSP.vars, List.flatMap_assoc]
    change ((F.zipIdx.take i.val).flatMap fun entry =>
      (instantiate B entry.2 entry.1.2 (gadgets entry.1.1).template).vars).length = _
    simp only [instantiate, vars_relabel]
    exact instantiatedPrefix_length B (fun r => (gadgets r).template) F i.val
  rw [hp]
  congr 1
  unfold replacementLocalOccurrence
  rw [incidenceEdgeIndex_cast]
  unfold instantiatedOccurrence instantiate PPGadget.template
  rw [incidenceEdgeIndex_relabelOccurrence, incidenceEdgeIndex_relabelOccurrence]

/-- Copied constraints retain their actual local row position after the preceding bodies.
This offset counts rows, independently of their arities or repeated relation records. -/
theorem replacementOccurrence_constraint
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (replacementOccurrence gadgets B F i o).1.val =
      ((F.take i.val).flatMap fun row => (gadgets row.rel).template).length + o.1.val := by
  have hp (k : ℕ) : ((F.zipIdx.take k).flatMap fun entry =>
      instantiate B entry.2 entry.1.2 (gadgets entry.1.1).template).length =
      ((F.take k).flatMap fun row => (gadgets row.rel).template).length := by
    simp only [List.length_flatMap, instantiate, PPGadget.template, CSP.relabel,
      List.length_map]
    conv_rhs => rw [← List.zipIdx_map_fst 0 F, List.map_take, List.map_map]
    simp only [← List.map_take, Function.comp_def]
  unfold replacementOccurrence replaceGadgets
  rw [CSP.flatMapOccurrence_constraint, hp]
  congr 1
  change (replacementLocalOccurrence gadgets B F i o).record.1 = _
  rw [record_replacementLocalOccurrence]
  rfl

/-- Copied argument positions keep exactly their local scope indices. -/
theorem replacementOccurrence_argument
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (replacementOccurrence gadgets B F i o).2.val = o.2.val := by
  unfold replacementOccurrence replaceGadgets
  rw [CSP.flatMapOccurrence_argument]
  change (replacementLocalOccurrence gadgets B F i o).record.2.1 = _
  rw [record_replacementLocalOccurrence]
  rfl

/-- The actual copied occurrence map preserves the original positive scope successor.
Neither local nor source scope names need to be distinct. -/
theorem argumentSuccessor_replacementOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    argumentSuccessor (replacementOccurrence gadgets B F i o) =
      replacementOccurrence gadgets B F i (argumentSuccessor o) := by
  unfold replacementOccurrence replaceGadgets
  rw [argumentSuccessor_flatMapOccurrence, argumentSuccessor_replacementLocalOccurrence]

/-- The actual copied occurrence reads its original instantiated free or private name. -/
theorem var_replacementOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    (replacementOccurrence gadgets B F i o).var =
      Sum.elim (fun a => 2 * F[i.val].scope.getD a.val 0)
        (fun j => 2 * (B * i.val + j.val) + 1) o.var := by
  unfold replacementOccurrence replaceGadgets
  rw [CSP.var_flatMapOccurrence]
  change (replacementLocalOccurrence gadgets B F i o).record.2.2 = _
  rw [record_replacementLocalOccurrence]
  change (instantiatedOccurrence _ _ _ _ o).var = _
  unfold instantiatedOccurrence instantiate PPGadget.template
  rw [CSP.var_relabelOccurrence, CSP.var_relabelOccurrence]
  cases o.var <;> rfl

/-- The typed copied occurrences exhaust the actual replacement body's occurrences. The
existing public incidence-index inverse recovers the unique local positional source. -/
theorem exists_replacementOccurrence
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ)
    (o : (replaceGadgets B (fun r => (gadgets r).template) F).Occurrence) :
    ∃ (i : Fin F.length) (p : (gadgets F[i.val].rel).body.Occurrence),
      replacementOccurrence gadgets B F i p = o := by
  obtain ⟨i, hi, p, hp⟩ := exists_gadgetCopy gadgets B F (incidenceEdgeIndex_lt_vars o)
  refine ⟨⟨i, hi⟩, p, incidenceEdgeIndex_injective ?_⟩
  rw [incidenceEdgeIndex_replacementOccurrence]
  exact hp

/-- Equality of copied constraint positions retains both the source copy and local body
row. Repeated relation records and nullary rows are not identified. -/
theorem replacementOccurrence_constraint_eq_iff
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i k : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence)
    (p : (gadgets F[k.val].rel).body.Occurrence) :
    (replacementOccurrence gadgets B F i o).1 =
      (replacementOccurrence gadgets B F k p).1 ↔ i.val = k.val ∧ o.1.val = p.1.val := by
  rw [Fin.ext_iff, replacementOccurrence_constraint, replacementOccurrence_constraint]
  constructor
  · exact List.flatMap_prefix_add_injective F (fun row => (gadgets row.rel).template)
      i.isLt (by simpa only [PPGadget.template, CSP.relabel, List.length_map] using o.1.isLt)
      k.isLt (by simpa only [PPGadget.template, CSP.relabel, List.length_map] using p.1.isLt)
  · rintro ⟨hi, hp⟩
    exact congrArg₂ (fun a b =>
      ((F.take a).flatMap fun row => (gadgets row.rel).template).length + b) hi hp

/-- The exact replacement retains every copy/local occurrence identity. In particular
coincident free labels and duplicate source rows never identify their indexed edges. -/
theorem replacementOccurrence_injective
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) :
    Function.Injective (fun p : (i : Fin F.length) × (gadgets F[i.val].rel).body.Occurrence =>
      replacementOccurrence gadgets B F p.1 p.2) := by
  rintro ⟨i, o⟩ ⟨k, p⟩ he
  have hindex := congrArg incidenceEdgeIndex he
  rw [incidenceEdgeIndex_replacementOccurrence, incidenceEdgeIndex_replacementOccurrence] at hindex
  have hlocal (j : Fin F.length) (q : (gadgets F[j.val].rel).body.Occurrence) :
      incidenceEdgeIndex q < (gadgets F[j.val].rel).template.vars.length := by
    simpa only [PPGadget.template, vars_relabel, List.length_map] using
      incidenceEdgeIndex_lt_vars q
  have hpos := copyIndex_injective (fun r => (gadgets r).template) F
    i.isLt (hlocal i o) k.isLt (hlocal k p) hindex
  have hik : i = k := Fin.ext hpos.1
  subst k
  have hop : o = p := incidenceEdgeIndex_injective hpos.2
  subst p
  rfl

/-- Actual target occurrences correspond bijectively to their original copy/local positions.
The inverse is proof-side finite choice; the executed compiler continues to use literal scans. -/
@[expose] noncomputable def replacementOccurrenceEquiv
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) :
    ((i : Fin F.length) × (gadgets F[i.val].rel).body.Occurrence) ≃
      (replaceGadgets B (fun r => (gadgets r).template) F).Occurrence :=
  Equiv.ofBijective (fun p => replacementOccurrence gadgets B F p.1 p.2)
    ⟨replacementOccurrence_injective gadgets B F, fun o => by
      obtain ⟨i, p, hp⟩ := exists_replacementOccurrence gadgets B F o
      exact ⟨⟨i, p⟩, hp⟩⟩

/-- The forward copy/local coordinate map is exactly the original positional occurrence map. -/
@[simp] theorem replacementOccurrenceEquiv_apply
    (gadgets : ∀ r, PPGadget arity sem (booleanRelation srcArity srcSem r))
    (B : ℕ) (F : CSP Src ℕ) (i : Fin F.length)
    (o : (gadgets F[i.val].rel).body.Occurrence) :
    replacementOccurrenceEquiv gadgets B F ⟨i, o⟩ = replacementOccurrence gadgets B F i o := rfl

end Cslib.Complexity.CSP.GadgetRotation
