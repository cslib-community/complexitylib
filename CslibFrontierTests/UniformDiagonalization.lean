/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Ladner.Density
import CslibFrontier.Computability.Complexity.Classes.RecursivelyPresentable.Classes
import CslibFrontier.Computability.Complexity.Classes.UniformDiagonalization
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.BoundedHalting
import CslibFrontier.Computability.Complexity.Reduction.Isomorphism.Paddable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec

/-! Uniform diagonalization and Ladner density: stage progression, `markedUnion` on concrete words,
recursive presentations and finite-variation closure of standard classes and polynomial-time
degrees, two decidable degrees strictly between `∅` and `BoundedHalting`, an `NP`-intermediate
problem strictly below decoded `SAT` under `P ≠ NP`, and the `∅ <ₘᵖ {[true]}` sharpness witness
showing that `B ∉ P` cannot be dropped from Ladner's density theorem. -/

namespace CslibFrontierTests.UniformDiagonalization

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### The construction -/

/-- Even stages diagonalize against the first family and odd ones against the second. -/
example : UniformDiagonalization.side 0 = true ∧ UniformDiagonalization.side 1 = false ∧
    UniformDiagonalization.side 4 = true :=
  ⟨rfl, rfl, rfl⟩

/-- The construction starts at stage `0` and advances at most one stage per length. -/
example (dA dF : Bool → Universal.Desc) (n : ℕ) :
    UniformDiagonalization.stage dA dF 0 = 0 ∧ UniformDiagonalization.stage dA dF n ≤ n :=
  ⟨UniformDiagonalization.stage_zero dA dF, UniformDiagonalization.stage_le_self dA dF n⟩

/-! ### The marked union -/

/-- `false :: x` is in the marked union exactly when `x` is in the first set, and `true :: x`
exactly when `x` is in the second. -/
example : [false, true] ∈ markedUnion {[true]} ∅ ∧ [true, true] ∉ markedUnion {[true]} ∅ ∧
    [] ∉ markedUnion {[true]} Set.univ := by
  refine ⟨cons_mem_markedUnion.mpr rfl, fun h => ?_, fun ⟨x, h⟩ => ?_⟩
  · simpa using cons_mem_markedUnion.mp h
  · rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-! ### Hypotheses on complexity classes -/

/-- `P`, `NP`, `coNP`, `Σₖᵖ`, `Πₖᵖ`, `PH`, `PSPACE`, and `EXP` on bit words all meet Schöning's
recursive-presentability and finite-variation-closure hypotheses. -/
example (k : ℕ) :
    (RecursivelyPresentable encBits (P encBits) ∧ ClosedUnderFiniteVariation (P encBits)) ∧
    (RecursivelyPresentable encBits (NP encBits) ∧ ClosedUnderFiniteVariation (NP encBits)) ∧
    (RecursivelyPresentable encBits (coNP encBits) ∧ ClosedUnderFiniteVariation (coNP encBits)) ∧
    (RecursivelyPresentable encBits (SigmaP k encBits) ∧
      ClosedUnderFiniteVariation (SigmaP k encBits)) ∧
    (RecursivelyPresentable encBits (PiP k encBits) ∧
      ClosedUnderFiniteVariation (PiP k encBits)) ∧
    (RecursivelyPresentable encBits (PH encBits) ∧ ClosedUnderFiniteVariation (PH encBits)) ∧
    (RecursivelyPresentable encBits (PSPACE encBits) ∧
      ClosedUnderFiniteVariation (PSPACE encBits)) ∧
    (RecursivelyPresentable encBits (EXP encBits) ∧ ClosedUnderFiniteVariation (EXP encBits)) :=
  ⟨⟨recursivelyPresentable_P, closedUnderFiniteVariation_P encBits⟩,
    ⟨recursivelyPresentable_NP, closedUnderFiniteVariation_NP encBits⟩,
    ⟨recursivelyPresentable_coNP, closedUnderFiniteVariation_coNP encBits⟩,
    ⟨recursivelyPresentable_SigmaP k, closedUnderFiniteVariation_SigmaP k encBits⟩,
    ⟨recursivelyPresentable_PiP k, closedUnderFiniteVariation_PiP k encBits⟩,
    ⟨recursivelyPresentable_PH, closedUnderFiniteVariation_PH encBits⟩,
    ⟨recursivelyPresentable_PSPACE, closedUnderFiniteVariation_PSPACE encBits⟩,
    ⟨recursivelyPresentable_EXP, closedUnderFiniteVariation_EXP encBits⟩⟩

/-- The class containing only the empty set is not closed under finite variations. -/
example : ¬ ClosedUnderFiniteVariation ({∅} : Set (Set (List Bool))) := fun h => by
  have hmem := h (L := ∅) (L' := {[]}) rfl (by simp)
  exact Set.singleton_ne_empty _ hmem

/-- Every recursively presentable class is nonempty, since `0 : ℕ` indexes a member. -/
example {C : Set (Set (List Bool))} (hC : RecursivelyPresentable encBits C) : C.Nonempty := by
  obtain ⟨F, -, rfl⟩ := hC
  exact ⟨{w | F (0, w) = true}, 0, rfl⟩

/-! ### Bounded halting and Ladner density -/

/-- The corollaries on bounded halting and its complement: the mixed set is decidable and reduces
to their marked union. (Here `G = Set.univ` already gives a problem outside `P`.) -/
example : ∃ G ∈ P encBits, G.ite BoundedHalting BoundedHaltingᶜ ∉ P encBits ∧
    IsDecidable (G.ite BoundedHalting BoundedHaltingᶜ) encBits ∧
    PolyTimeReducible encBits encBits (G.ite BoundedHalting BoundedHaltingᶜ)
      (markedUnion BoundedHalting BoundedHaltingᶜ) := by
  have hc : BoundedHaltingᶜ ∉ P encBits := fun h =>
    BoundedHalting.notMem_P (by simpa using compl_mem_P h)
  obtain ⟨G, hG, h₁, -⟩ := exists_mem_P_ite_notMem_P recursivelyPresentable_P
    (closedUnderFiniteVariation_P encBits) BoundedHalting.isDecidable
    BoundedHalting.isDecidable.compl BoundedHalting.notMem_P hc
  exact ⟨G, hG, h₁, isDecidable_ite (isDecidable_of_mem_P hG) BoundedHalting.isDecidable
    BoundedHalting.isDecidable.compl, polyTimeReducible_ite_markedUnion hG⟩

/-- **A problem strictly between `P` and bounded halting**, from the effective form with
`A₁ = ∅` against the constant family of bounded halting, and `A₂` = bounded halting against the
presentation of `P`. The mixed set `Gᶜ ∩ BoundedHalting` is outside `P`, differs from bounded
halting and reduces to it. -/
example : ∃ G ∈ P encBits, G.ite ∅ BoundedHalting ∉ P encBits ∧
    G.ite ∅ BoundedHalting ≠ BoundedHalting ∧
    PolyTimeReducible encBits encBits (G.ite ∅ BoundedHalting) BoundedHalting := by
  have hinf : BoundedHalting.Infinite := fun h => BoundedHalting.notMem_P h.mem_P
  obtain ⟨f, hf, hBH⟩ := BoundedHalting.isDecidable.exists_isComputable
  have hset : {w | f w = true} = BoundedHalting := Set.ext fun w => (hBH w).symm
  have hsnd : IsComputable (fun p : ℕ × List Bool => p.2) (encPair encUnary encBits) encBits :=
    ComputableInPolyTime.isComputable (by fun_prop)
  obtain ⟨G, hG, hne⟩ := exists_mem_P_forall_ite_ne (A₁ := ∅) (A₂ := BoundedHalting)
    (F₁ := fun p => f p.2) (F₂ := UniformDiagonalization.pIndexed)
    (isDecidable_of_mem_P empty_mem_P) BoundedHalting.isDecidable (hf.comp hsnd)
    UniformDiagonalization.isComputable_pIndexed
    (fun i => by rwa [hset, ← Set.bot_eq_empty, bot_symmDiff])
    (fun i => (closedUnderFiniteVariation_P encBits).infinite_symmDiff BoundedHalting.notMem_P
      (UniformDiagonalization.setOf_pIndexed_mem_P i))
  have h₀ : ∃ y, y ∉ BoundedHalting := by
    by_contra h
    exact BoundedHalting.notMem_P
      (Set.eq_univ_of_forall (fun y => not_not.mp fun hy => h ⟨y, hy⟩) ▸ univ_mem_P)
  have h₁ : ∃ y, y ∈ BoundedHalting := hinf.nonempty
  obtain ⟨y₀, hy₀⟩ := h₀
  obtain ⟨y₁, hy₁⟩ := h₁
  refine ⟨G, hG, fun hM => ?_, ?_, polyTimeReducible_ite_of_mem_P hG empty_mem_P hy₀ hy₁⟩
  · obtain ⟨i, -, hi⟩ := UniformDiagonalization.exists_setOf_pIndexed_eq hM 0
    exact (hne i).2 hi.symm
  · simpa only [hset] using (hne 0).1

/-- The polynomial-time `m`-degree of `BoundedHalting` is recursively presentable and closed under
finite variations. -/
example : RecursivelyPresentable encBits (polyTimeDegree BoundedHalting) ∧
    ClosedUnderFiniteVariation (polyTimeDegree BoundedHalting) :=
  ⟨recursivelyPresentable_polyTimeDegree BoundedHalting.isDecidable BoundedHalting.notMem_P,
    closedUnderFiniteVariation_polyTimeDegree BoundedHalting.notMem_P⟩

/-- **Unconditional two-step density chain below `BoundedHalting`**: Ladner's downward theorem and
full density theorem produce decidable sets `A, C ∉ P` with `∅ <ₘᵖ A <ₘᵖ C <ₘᵖ BoundedHalting`
(exercising the `A ∉ P` branch of `exists_isDecidable_between_of_notMem_P`). -/
example : ∃ A C : Set (List Bool),
    IsDecidable A encBits ∧ IsDecidable C encBits ∧
    A ∉ P encBits ∧ C ∉ P encBits ∧
    PolyTimeReducible encBits encBits ∅ A ∧ ¬PolyTimeReducible encBits encBits A ∅ ∧
    PolyTimeReducible encBits encBits A C ∧ ¬PolyTimeReducible encBits encBits C A ∧
    PolyTimeReducible encBits encBits C BoundedHalting ∧
    ¬PolyTimeReducible encBits encBits BoundedHalting C := by
  obtain ⟨A, hdecA, hAP, hABH, hBHA⟩ :=
    exists_isDecidable_notMem_P_lt BoundedHalting.isDecidable BoundedHalting.notMem_P
  obtain ⟨C, hdecC, hAC, hCA, hCBH, hBHC⟩ :=
    exists_isDecidable_between_of_notMem_P BoundedHalting.isDecidable
      BoundedHalting.notMem_P hABH hBHA
  obtain ⟨⟨a₀, ha₀⟩, ⟨a₁, ha₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hAP
  refine ⟨A, C, hdecA, hdecC, hAP, fun hCP => hAP (hAC.mem_P hCP),
    polyTimeReducible_of_mem_P empty_mem_P ha₁ ha₀,
    fun hA0 => hAP (hA0.mem_P empty_mem_P), hAC, hCA, hCBH, hBHC⟩

/-- **An `NP`-intermediate problem strictly below decoded `SAT`** under `P ≠ NP`, followed by a
second `NP`-intermediate problem strictly between them via `exists_mem_NP_between_of_notMem_P`. -/
example (hne : P encCNF ≠ NP encCNF) :
    let satBits := cnfDecoder.decode ⁻¹' SAT
    ∃ A C : Set (List Bool), A ∈ NP encBits ∧ C ∈ NP encBits ∧
      A ∉ P encBits ∧ C ∉ P encBits ∧ ¬NPComplete encBits A ∧ ¬NPComplete encBits C ∧
      PolyTimeReducible encBits encBits A C ∧ ¬PolyTimeReducible encBits encBits C A ∧
      PolyTimeReducible encBits encBits C satBits ∧
      ¬PolyTimeReducible encBits encBits satBits C := by
  intro satBits
  have hsat : NPComplete encBits satBits := CookLevin.SAT_npComplete.preimage_decode cnfDecoder
  obtain ⟨A, hANP, hAP, hAnc, hAsat, hsatA⟩ := hsat.exists_NP_not_P_not_npComplete_lt hne
  obtain ⟨C, hCNP, hAC, hCA, hCsat, hsatC⟩ :=
    exists_mem_NP_between_of_notMem_P hANP hsat.1
      (fun hP => hne (hsat.P_eq_NP_of_mem_P hP encCNF)) hAsat hsatA
  refine ⟨A, C, hANP, hCNP, hAP, fun hCP => hAP (hAC.mem_P hCP), hAnc,
    fun hCnc => hsatC (hCnc.2 encBits satBits hsat.1), hAC, hCA, hCsat, hsatC⟩

/-- **Sharpness of `B ∉ P` in Ladner's density theorem**: `∅ <ₘᵖ {[true]}`, yet no set `C` lies
strictly `≤ₘᵖ`-between `∅` and `{[true]}`. -/
example : PolyTimeReducible encBits encBits (∅ : Set (List Bool)) {[true]} ∧
    ¬PolyTimeReducible encBits encBits ({[true]} : Set (List Bool)) ∅ ∧
    ¬∃ C : Set (List Bool),
      PolyTimeReducible encBits encBits ∅ C ∧ ¬PolyTimeReducible encBits encBits C ∅ ∧
      PolyTimeReducible encBits encBits C {[true]} ∧
      ¬PolyTimeReducible encBits encBits {[true]} C := by
  refine ⟨⟨fun _ => [], .const [], fun _ => by simp⟩,
    fun ⟨f, _, hf⟩ => (hf [true]).mp rfl, ?_⟩
  rintro ⟨C, ⟨f₀, -, hf₀⟩, hC₀, -, h₁C⟩
  have hc₀ : f₀ [] ∉ C := fun hc => (hf₀ []).mpr hc
  have hne : C.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    exact hC₀ (hempty ▸ .refl encBits ∅)
  obtain ⟨c₁, hc₁⟩ := hne
  have htrueP : ({[true]} : Set (List Bool)) ∈ P encBits :=
    (Set.finite_singleton [true]).mem_P
  exact h₁C (polyTimeReducible_of_mem_P htrueP hc₁ hc₀)

end CslibFrontierTests.UniformDiagonalization
