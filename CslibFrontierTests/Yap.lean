/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.PH.Yap
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Parameterized.LongPathKernel

/-!
# Tests: PH reduction/quantifier closure, Yap's theorem, and `PH ≠ Σ₃` kernel lower bounds

Concrete unconditional instantiations of `PolyTimeReducible.mem_SigmaP`,
`PolyTimeReducible.mem_PiP`, `PolyTimeReducible.mem_PH`, `mem_SigmaP_of_exists_length`, and
`mem_PiP_of_forall_length` with checked yes- and no-instances; the exact equivalences between
`coNP encBits ⊆ NPPoly encBits`, `NP encBits ⊆ coNPPoly encBits`, `UNSAT ∈ NPPoly encCNF`, and
`SAT ∈ coNPPoly encCNF`; and client instantiations of Yap's collapse `PH = Σ₃` and the
Bodlaender–Jansen–Kratsch `PH ≠ Σ₃` kernelization lower bounds.
-/

namespace CslibFrontierTests.Yap

open Cslib Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM ComputableInPolyTime

/-! ### Unconditional PH reduction and bounded-quantifier closure -/

/-- The singleton language `{[false, true]}`, in `P ⊆ Σ₀`. -/
abbrev isFalseTrue : Set (List Bool) := {x | x = [false, true]}

theorem isFalseTrue_mem_SigmaP_zero : isFalseTrue ∈ SigmaP 0 encBits :=
  P_subset_SigmaP_zero
    ⟨fun x => decide (x = [false, true]), decide_eq' id' (.const [false, true]),
      fun _ => decide_eq_true_iff.symm⟩

/-- Pulling `isFalseTrue` back along `List.reverse` places `{[true, false]}` in `Σ₀`, `Π₀`, and
`PH`, with `[true, false]` a yes-instance and `[false, true]` a no-instance. -/
example :
    (let revLang : Set (List Bool) := {x | x.reverse ∈ isFalseTrue}
     revLang ∈ SigmaP 0 encBits ∧
     revLang ∈ PiP 0 encBits ∧
     revLang ∈ PH encBits ∧
     [true, false] ∈ revLang ∧
     [false, true] ∉ revLang) := by
  have hred : PolyTimeReducible encBits encBits {x : List Bool | x.reverse ∈ isFalseTrue}
      isFalseTrue :=
    ⟨List.reverse, bitsReverse, fun _ => Iff.rfl⟩
  exact ⟨hred.mem_SigmaP isFalseTrue_mem_SigmaP_zero,
    hred.mem_PiP (SigmaP_zero_eq_PiP_zero ▸ isFalseTrue_mem_SigmaP_zero),
    hred.mem_PH (SigmaP_subset_PH 0 isFalseTrue_mem_SigmaP_zero),
    by simp [isFalseTrue], by simp [isFalseTrue]⟩

/-- Existential quantification over words of computed unary length `x.length`: the strings `x` for
which some word `w` of length `x.length` reverses to `x` and equals `[false, true]` form a language
in `Σ₁`, with `[true, false]` a yes-instance and `[false, true]` a no-instance. -/
example :
    (let A : Set (List Bool) :=
      {x | ∃ w : List Bool, w.length = x.length ∧ w.reverse = x ∧ w ∈ isFalseTrue}
     A ∈ SigmaP 1 encBits ∧ [true, false] ∈ A ∧ [false, true] ∉ A) := by
  let C : Set (List Bool × List Bool) := {p | p.2.reverse = p.1 ∧ p.2 ∈ isFalseTrue}
  have hC_P : C ∈ P (encPair encBits encBits) := by
    refine ⟨fun p => decide (p.2.reverse = p.1) && decide (p.2 = [false, true]),
      bool_and' (decide_eq' (bitsReverse.comp (snd _ _)) (fst _ _))
        (decide_eq' (snd _ _) (.const [false, true])),
      fun p => ?_⟩
    simp [C, isFalseTrue]
  have hC : C ∈ SigmaP 1 (encPair encBits encBits) :=
    SigmaP_mono (Nat.zero_le 1) (P_subset_SigmaP_zero hC_P)
  refine ⟨mem_SigmaP_of_exists_length le_rfl length_bits hC,
    ⟨[false, true], rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨w, -, hw, rfl⟩
  simp at hw

/-- Universal quantification over words of computed unary length `x.length` via
`mem_PiP_of_forall_length`, witnessing `[]` as a yes-instance and `[false]` as a no-instance. -/
example :
    (let A : Set (List Bool) := {x | ∀ w : List Bool, w.length = x.length → w = []}
     A ∈ PiP 1 encBits ∧ [] ∈ A ∧ [false] ∉ A) := by
  let C : Set (List Bool × List Bool) := {p | p.2 = []}
  have hC_P : C ∈ P (encPair encBits encBits) :=
    ⟨fun p => decide (p.2 = []), decide_eq' (snd _ _) (.const []), fun _ => decide_eq_true_iff.symm⟩
  have hC0 : C ∈ PiP 0 (encPair encBits encBits) := by
    rw [← SigmaP_zero_eq_PiP_zero]
    exact P_subset_SigmaP_zero hC_P
  have hC : C ∈ PiP 1 (encPair encBits encBits) := PiP_mono (Nat.zero_le 1) hC0
  refine ⟨mem_PiP_of_forall_length le_rfl length_bits hC,
    fun w hw => List.length_eq_zero_iff.1 hw, fun h => ?_⟩
  exact List.cons_ne_nil false [] (h [false] rfl)

/-! ### Equivalences of the nonuniform hypotheses -/

/-- Equivalence of the bit-string inclusions and single-problem hypotheses for `UNSAT` and `SAT`. -/
example :
    (coNP encBits ⊆ NPPoly encBits ↔ UNSAT ∈ NPPoly encCNF) ∧
    (NP encBits ⊆ coNPPoly encBits ↔ SAT ∈ coNPPoly encCNF) ∧
    (UNSAT ∈ NPPoly encCNF ↔ ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NPPoly encB) := by
  refine ⟨coNP_encBits_subset_NPPoly_iff_UNSAT, ?_, UNSAT_mem_NPPoly_iff_forall_coNP_subset_NPPoly⟩
  rw [← coNP_subset_NPPoly_iff, coNP_encBits_subset_NPPoly_iff_UNSAT, SAT_mem_coNPPoly_iff_UNSAT]

/-! ### Yap's theorem and cross-composition corollaries -/

/-- Under `UNSAT ∈ NP/poly`, `Σ₂ ⊆ NP/poly`, `Π₂ ⊆ coNP/poly`, and `PH = Σ₃ = Σ₃ ∩ Π₃` for any
instance encoding. -/
example (h : UNSAT ∈ NPPoly encCNF) {α : Type} (enc : α ↪ List Bool) :
    SigmaP 2 enc ⊆ NPPoly enc ∧
    PiP 2 enc ⊆ coNPPoly enc ∧
    PH enc = SigmaP 3 enc ∧
    PH enc = SigmaP 3 enc ∩ PiP 3 enc := by
  have hall : ∀ {β : Type} (encB : β ↪ List Bool), coNP encB ⊆ NPPoly encB :=
    UNSAT_mem_NPPoly_iff_forall_coNP_subset_NPPoly.1 h
  exact ⟨SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly (hall _),
    PiP_two_subset_coNPPoly_of_coNP_subset_NPPoly (hall _),
    PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly h,
    PH_eq_SigmaP_three_inter_PiP_three_of_coNP_subset_NPPoly hall⟩

/-- Theorem 2 of Bodlaender, Jansen and Kratsch: an OR-distillation of `SAT` with polynomial size
bound collapses `PH` to `Σ₃`. -/
example {β : Type} {encB : β ↪ List Bool} {B : Set β} {f : List (CNF ℕ) → β} {s : ℕ → ℕ}
    (hf : IsORDistillation encCNF encB SAT B f s) (hs : PolynomiallyBounded s) :
    PH encBits = SigmaP 3 encBits :=
  PH_eq_SigmaP_three_of_orDistillation CookLevin.SAT_npComplete.2 hf hs encBits

/-- Corollary 2 of Bodlaender, Jansen and Kratsch under `PH ≠ Σ₃`: k-Path has neither a polynomial
kernel nor a polynomial compression if `PH encBits ≠ SigmaP 3 encBits`. -/
example (hPH : PH encBits ≠ SigmaP 3 encBits) :
    ¬ HasPolyKernel (encPair encGraph encNat) Prod.snd LongPath ∧
    ¬ HasPolyCompression (encPair encGraph encNat) Prod.snd LongPath :=
  ⟨not_hasPolyKernel_LongPath_of_PH_ne_SigmaP_three hPH,
    not_hasPolyCompression_LongPath_of_PH_ne_SigmaP_three hPH⟩

end CslibFrontierTests.Yap
