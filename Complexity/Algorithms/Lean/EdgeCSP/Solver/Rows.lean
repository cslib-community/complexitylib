/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.EdgeCSP.Blossom.Contraction
public import Complexity.Logics.Propositional.CSP.Occurrence.Enumeration
import Mathlib.Data.List.GetD

/-!
# Materializing actual positional row buffers

Flattening one exact-width row per constraint is exactly the existing incidence-order buffer.
This original representation bookkeeping is shared by initialization and blossom references.
-/

public section

namespace Cslib.Logic.PL.CSP.Solver

/-- Materializing a complete row buffer in incidence order is exactly list flattening.
Both the number of rows and every actual scope width are explicit hypotheses. -/
theorem materialize_labels (F : CSP Table ℕ) (rows : List (List Bool))
    (hlen : rows.length = F.length)
    (hw : ∀ i : Fin F.length, (rows.getD i.val []).length = F[i.val].2.length) :
    (incidenceList F).map (Blossom.labels F rows) = rows.flatten := by
  have he : List.ofFn (fun i : Fin F.length => localTuple (Blossom.labels F rows) i) = rows := by
    apply List.ext_getElem
    · simpa only [List.length_ofFn] using hlen.symm
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rw [Blossom.localTuple_labels F rows ⟨i, by simpa using hi⟩ (hw ⟨i, by simpa using hi⟩)]
      exact List.getD_eq_getElem _ _ hj
  conv_rhs => rw [← he]
  simp [incidenceList, List.map_flatten, List.map_ofFn, localTuple, Function.comp_def]

end Cslib.Logic.PL.CSP.Solver
