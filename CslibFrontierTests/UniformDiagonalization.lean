/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.UniformDiagonalization
import CslibFrontier.Computability.Complexity.Problems.BoundedHalting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec

/-! Uniform diagonalization: the sides of the stages, the marked union on concrete words, `P`
meeting the hypotheses, a class that is not closed under finite variations, and the theorem applied
to bounded halting and its complement, which are decidable and outside `P`. -/

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

/-! ### The hypotheses -/

/-- `P` meets both hypotheses on classes. -/
example : RecursivelyPresentable encBits (P encBits) ∧ ClosedUnderFiniteVariation (P encBits) :=
  ⟨recursivelyPresentable_P, closedUnderFiniteVariation_P encBits⟩

/-- The class containing only the empty set is not closed under finite variations. -/
example : ¬ ClosedUnderFiniteVariation ({∅} : Set (Set (List Bool))) := fun h => by
  have hmem := h (L := ∅) (L' := {[]}) rfl (by simp)
  exact Set.singleton_ne_empty _ hmem

/-! ### Bounded halting -/

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

end CslibFrontierTests.UniformDiagonalization
