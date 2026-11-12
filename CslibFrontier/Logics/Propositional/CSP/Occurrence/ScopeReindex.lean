/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Occurrence.AppendScope

/-!
# Reindexing the positions of one actual appended scope

The original body is retained literally, and only the selected last constraint's argument
positions are permuted. The existing occurrence type records the resulting coordinates.
This does not preserve prescribed cyclic order for arbitrary permutations; that condition
must be proved separately, and is essential in ordered incidence transport.
-/

public section

namespace Cslib.Logic.PL.CSP

variable {Rel V : Type}

/-- Reindex the final scope by `q`, using its inverse to locate each old argument in the
new list. Body occurrences retain their original constraint and argument positions. -/
noncomputable def reindexLastScopeOccurrenceEquiv (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n)) :
    (F ++ [(r, List.ofFn scope)]).Occurrence ≃
      (F ++ [(r, List.ofFn (scope ∘ q))]).Occurrence :=
  (appendOfFnOccurrenceEquiv F r scope).symm.trans
    ((Equiv.sumCongr (Equiv.refl F.Occurrence) q.symm).trans
      (appendOfFnOccurrenceEquiv F r (scope ∘ q)))

/-- The reindexing is the literal conjugated body/last-scope coordinate map. -/
theorem reindexLastScopeOccurrenceEquiv_apply (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n)) (o : F.Occurrence ⊕ Fin n) :
    reindexLastScopeOccurrenceEquiv F r scope q (appendOfFnOccurrenceEquiv F r scope o) =
      appendOfFnOccurrenceEquiv F r (scope ∘ q)
        ((Equiv.sumCongr (Equiv.refl F.Occurrence) q.symm) o) := by
  simp [reindexLastScopeOccurrenceEquiv]

/-- Every occurrence retains its original variable and constraint position, including
repeated variables; only argument positions of the last scope can differ. -/
theorem header_reindexLastScopeOccurrenceEquiv (F : CSP Rel V) (r : Rel) {n : ℕ}
    (scope : Fin n → V) (q : Equiv.Perm (Fin n))
    (o : (F ++ [(r, List.ofFn scope)]).Occurrence) :
    ((reindexLastScopeOccurrenceEquiv F r scope q o).1.val,
        (reindexLastScopeOccurrenceEquiv F r scope q o).var) = (o.1.val, o.var) := by
  obtain ⟨o, rfl⟩ := (appendOfFnOccurrenceEquiv F r scope).surjective o
  rw [reindexLastScopeOccurrenceEquiv_apply]
  cases o with
  | inl o =>
    have ht := congrArg (fun (i, (_j, v)) => (i, v))
      (record_appendOfFnOccurrenceEquiv_inl F r (scope ∘ q) o)
    have hs := congrArg (fun (i, (_j, v)) => (i, v))
      (record_appendOfFnOccurrenceEquiv_inl F r scope o)
    exact ht.trans hs.symm
  | inr j =>
    have ht := congrArg (fun (i, (_j, v)) => (i, v))
      (record_appendOfFnOccurrenceEquiv_inr F r (scope ∘ q) (q.symm j))
    have hs := congrArg (fun (i, (_j, v)) => (i, v))
      (record_appendOfFnOccurrenceEquiv_inr F r scope j)
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at ht
    exact ht.trans hs.symm

end Cslib.Logic.PL.CSP
