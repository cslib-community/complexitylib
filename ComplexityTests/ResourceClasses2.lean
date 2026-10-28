/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.PH.Collapse
import Complexity.Computability.Complexity.Classes.PH.Projection
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Collapses of the polynomial hierarchy, with concrete instances of cutting blocks of
certificates and of peeling off the first quantifier of `Σₖ₊₁`. -/

namespace ComplexityTests.ResourceClasses2

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Collapses of the polynomial hierarchy -/

/-- Cutting blocks of lengths `X + 1` and `2` at `2`, namely `3` and `2`, to their lengths at `1`,
namely `2` and `2`. -/
example : truncateBlocks [.X + 1, 2] 1 2 [true, false, true, false, true] =
    [true, false, false, true] := by
  simp [truncateBlocks]

/-- Cutting at equal lengths keeps the concatenated blocks. -/
example : truncateBlocks [.X, .X] 2 2 [true, false, true, true] = [true, false, true, true] := by
  simp [truncateBlocks]

/-- The quantifiers over longer blocks, cut, are the quantifiers over shorter blocks. -/
example :
    Alternation true ([Polynomial.X, 1].map fun p => p.eval 3)
      (fun w => (truncateBlocks [.X, 1] 1 3 w).headD false = true) := by
  rw [alternation_truncateBlocks (P := fun w => w.headD false = true) (by norm_num)]
  simp only [List.map, Polynomial.eval_X, Polynomial.eval_one, Alternation]
  exact ⟨[true], rfl, fun _ _ => rfl⟩

private def headLang : Set (List Bool) := {w | w.headD false = true}

private theorem headLang_mem_P : headLang ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

private theorem headLang_mem_SigmaP_one : headLang ∈ SigmaP 1 encBits := by
  have h0 : headLang ∈ SigmaP 0 encBits := by
    rw [SigmaP_zero]
    exact headLang_mem_P
  exact SigmaP_mono (by decide : 0 ≤ 1) h0

private def alternatingLang : Set (List Bool) :=
  {a | Alternation true [1, 1] fun w => (a ++ w).headD false = true}

private theorem alternatingLang_mem_SigmaP_two : alternatingLang ∈ SigmaP 2 encBits :=
  ⟨[1, 1], fun x => (x.1 ++ x.2).headD false, rfl, by fun_prop, fun _ => by simp [alternatingLang]⟩

private theorem alternatingLang_compl_mem_PiP_two : alternatingLangᶜ ∈ PiP 2 encBits :=
  compl_mem_PiP_of_mem_SigmaP alternatingLang_mem_SigmaP_two

private theorem alternatingLang_compl_mem_PiP_three : alternatingLangᶜ ∈ PiP 3 encBits :=
  PiP_subset_PiP_succ 2 alternatingLang_compl_mem_PiP_two

/-- A problem in `Σ₂` is the projection of a `coNP` problem on pairs of an instance and a word. -/
example :
    ∃ (p : Polynomial ℕ) (B : Set (List Bool × List Bool)), B ∈ coNP (encPair encBits encBits) ∧
      ∀ a, a ∈ alternatingLang ↔
        ∃ w : List Bool, w.length = p.eval (encBits a).length ∧ (a, w) ∈ B := by
  obtain ⟨p, B, hB, hA⟩ := exists_mem_PiP_of_mem_SigmaP_succ alternatingLang_mem_SigmaP_two
  exact ⟨p, B, PiP_one_eq_coNP ▸ hB, hA⟩

/-- At the first level, an `NP` problem is the projection of a `P` problem on pairs. -/
example :
    ∃ (p : Polynomial ℕ) (B : Set (List Bool × List Bool)), B ∈ P (encPair encBits encBits) ∧
      ∀ a, a ∈ headLang ↔ ∃ w : List Bool, w.length = p.eval (encBits a).length ∧ (a, w) ∈ B := by
  obtain ⟨p, B, hB, hA⟩ := exists_mem_PiP_of_mem_SigmaP_succ (k := 0) headLang_mem_SigmaP_one
  exact ⟨p, B, PiP_zero ▸ hB, hA⟩

/-- `Σₖ = Πₖ` (or `Πₖ ⊆ Σₖ`) at level `k ≥ 1` collapses `PH` to `Σₖ`. -/
example {k : ℕ} (hk : 1 ≤ k)
    (h : ∀ {β : Type} (encB : β ↪ List Bool), SigmaP k encB = PiP k encB) :
    alternatingLangᶜ ∈ SigmaP k encBits := by
  rw [← PH_eq_SigmaP_of_PiP_subset_SigmaP hk fun encB => (h encB).ge]
  exact PiP_subset_PH 2 alternatingLang_compl_mem_PiP_two

/-- `NP = coNP` collapses `PH` to `NP`. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB = coNP encB) :
    alternatingLang ∈ NP encBits := by
  rw [← PH_eq_NP_of_coNP_subset_NP fun encB => (h encB).ge]
  exact SigmaP_subset_PH 2 alternatingLang_mem_SigmaP_two

/-- `P = NP` collapses `PH` to `P`, and then `PH = NP` too. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), P encB = NP encB) :
    alternatingLang ∈ P encBits ∧ alternatingLang ∈ NP encBits := by
  have hPH : PH encBits = P encBits := PH_eq_P_of_NP_subset_P fun encB => (h encB).ge
  have hmem : alternatingLang ∈ P encBits := hPH ▸ SigmaP_subset_PH 2 alternatingLang_mem_SigmaP_two
  exact ⟨hmem, h encBits ▸ hmem⟩

/-- The collapse at the second level, as used by the Karp–Lipton theorem. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), SigmaP 3 encB ⊆ SigmaP 2 encB) :
    alternatingLangᶜ ∈ SigmaP 2 encBits := by
  rw [← PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP h]
  exact PiP_subset_PH 3 alternatingLang_compl_mem_PiP_three

/-- At `k = 0` the hypothesis `Π₀ ⊆ Σ₀` holds outright, both levels being `P`, which is why the
collapse from `Πₖ ⊆ Σₖ` needs `1 ≤ k`. -/
example : headLang ∈ SigmaP 0 encBits := by
  have h0 : PiP 0 encBits ⊆ SigmaP 0 encBits := by rw [PiP_zero, SigmaP_zero]
  exact h0 (PiP_zero.symm ▸ headLang_mem_P)

/-- At `k = 0`, `Σ₁ ⊆ Σ₀` is `NP ⊆ P`, which collapses `PH` to `Σ₀ = P`. -/
example (h : ∀ {β : Type} (encB : β ↪ List Bool), NP encB ⊆ P encB) :
    alternatingLang ∈ SigmaP 0 encBits := by
  have hcol : PH encBits = SigmaP 0 encBits :=
    PH_eq_SigmaP_of_SigmaP_succ_subset_SigmaP fun encB => by
      simpa only [zero_add, SigmaP_one, SigmaP_zero] using h encB
  exact hcol ▸ SigmaP_subset_PH 2 alternatingLang_mem_SigmaP_two

end ComplexityTests.ResourceClasses2
