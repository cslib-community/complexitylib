/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Collapse

/-! Clients of the complete-language collapse bridge, including the actual reduction chain. -/

open Cslib.Complexity Turing.MultiTapeTM

example {α : Type} (enc : α ↪ List Bool) (A : Set α) (hA : A ∈ coNP enc)
    (h : PolyTimeReducible encCNF encCNF ThreeSAT ThreeSATᶜ) : A ∈ NP enc := by
  have hToCompl : PolyTimeReducible enc encCNF A ThreeSATᶜ := by
    simpa only [compl_compl] using (ThreeSAT_npHard enc Aᶜ hA).compl
  have hFromCompl : PolyTimeReducible encCNF encCNF ThreeSATᶜ ThreeSAT := by
    simpa only [compl_compl] using h.compl
  exact (hToCompl.trans hFromCompl).mem_NP ThreeSAT.mem_NP

-- A raw-bit PH language gets an NP verifier; its complement gets one as well.
example (L : Set (List Bool)) (hL : L ∈ PH encBits)
    (h : PolyTimeReducible encCNF encCNF ThreeSAT ThreeSATᶜ) :
    L ∈ NP encBits ∧ Lᶜ ∈ NP encBits := by
  rw [PH_eq_NP_of_ThreeSAT_reducible_compl encBits h] at hL
  refine ⟨hL, ?_⟩
  have hEq := ThreeSAT_npComplete.NP_eq_coNP_of_reducible_compl (enc := encBits) h
  rw [hEq] at hL
  exact hL
