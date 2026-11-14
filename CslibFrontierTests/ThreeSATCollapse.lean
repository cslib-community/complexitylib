/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Complexity.Problems.TMSigmaSAT
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Collapse

/-! Clients of the complete-language collapse bridge, fixed-domain (`encBits`) polynomial-hierarchy
collapse equivalences (Arora–Barak Theorem 5.6 / Goldreich Proposition 3.10), and `PH`-completeness
equivalences (Arora–Barak Claim 5.7 and Chapter 5, Exercise 4). -/

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

-- Raw-word preimage representation at `encCNF`: `ThreeSAT ∈ SigmaP 1 encCNF` and
-- `ThreeSATᶜ ∈ PiP 1 encCNF` extend to raw-word languages in `SigmaP 1 encBits` and `PiP 1 encBits`
-- without requiring a decoder for `encCNF`.
example : (∃ B ∈ SigmaP 1 encBits, encCNF ⁻¹' B = ThreeSAT) ∧
    (∃ C ∈ PiP 1 encBits, encCNF ⁻¹' C = ThreeSATᶜ) :=
  ⟨exists_mem_SigmaP_encBits_preimage (SigmaP_one ▸ ThreeSAT.mem_NP),
    exists_mem_PiP_encBits_preimage (compl_mem_PiP_of_mem_SigmaP (SigmaP_one ▸ ThreeSAT.mem_NP))⟩

-- Arora–Barak Theorem 5.6 / Goldreich Proposition 3.10: fixed-domain
-- `PiP k encBits = SigmaP k encBits` and `P encBits = NP encBits` collapse `PH` at `encCNF`
-- (and every explicit encoding).
example (k : ℕ) (hk : 1 ≤ k) (h : PiP k encBits = SigmaP k encBits) :
    PH encCNF = SigmaP k encCNF :=
  PH_eq_SigmaP_of_PiP_encBits_eq_SigmaP hk h

example (h : P encBits = NP encBits) : PH encCNF = P encCNF :=
  PH_eq_P_of_P_encBits_eq_NP h

-- Goldreich Proposition 3.10 equivalence: `PH = SigmaP k` (at all encodings or on `encBits`) is
-- equivalent to `SigmaP (k + 1) encBits = SigmaP k encBits` and `PiP k encBits = SigmaP k encBits`.
example (k : ℕ) (hk : 1 ≤ k) :
    ((∀ {α : Type} (enc : α ↪ List Bool), PH enc = SigmaP k enc) ↔
      SigmaP (k + 1) encBits = SigmaP k encBits) ∧
    (PH encBits = SigmaP k encBits ↔ PiP k encBits = SigmaP k encBits) :=
  ⟨forall_PH_eq_SigmaP_iff_SigmaP_succ_encBits_eq_SigmaP,
    PH_encBits_eq_SigmaP_iff_PiP_encBits_eq_SigmaP hk⟩

-- Level-`k` machine satisfiability `TMSigmaSAT k` is unconditionally `SigmaP k`-complete.
example (k : ℕ) : SigmaPComplete k encTMSATInstance (TMSigmaSAT k) :=
  TMSigmaSAT.sigmaPComplete k

-- Arora–Barak Claim 5.7 / Exercise 5.4: if `PH = NP` on `encBits`, then `ThreeSAT` is
-- `PH`-complete; conversely, any `PH`-complete language collapses `PH` to some level `SigmaP k`.
example (h : PH encBits = NP encBits) : PHComplete encCNF ThreeSAT :=
  SigmaPComplete.phComplete_of_PH_encBits_eq_SigmaP
    (k := 1) (sigmaPComplete_one_iff.mpr ThreeSAT_npComplete) (SigmaP_one.symm ▸ h)

example : (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
    ∃ k, PH encBits = SigmaP k encBits :=
  exists_phComplete_iff_exists_PH_encBits_eq_SigmaP

example : (∃ (β : Type) (encB : β ↪ List Bool) (B : Set β), PHComplete encB B) ↔
    ∃ k, 1 ≤ k ∧ PiP k encBits = SigmaP k encBits :=
  exists_phComplete_iff_exists_PiP_encBits_eq_SigmaP
