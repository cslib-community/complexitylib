/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Quadratic

/-!
# Clients of quadratic Fusion completeness

A two-intersection cover compiles with cost four, including over infinite carriers. Empty
pair lists and empty input families exercise the free-constant boundary of the construction.
-/

namespace CslibFrontierTests.FusionQuadratic

open Cslib.Circuits Fusion

private def triple : Formula Monotone.signature 3 :=
  Monotone.and (Monotone.and (.input 0) (.input 1)) (.input 2)

private def tripleCover {U : Type*} (A B C : Set U) : PairCover (A ∩ B ∩ C) ![A, B, C] :=
  PairCover.ofCircuit triple.toCircuit ![A, B, C] 0 (by
    rw [Formula.eval_toCircuit]
    rfl)

example {U : Type*} (A B C : Set U) : (tripleCover A B C).pairs.length = 2 := by
  rw [tripleCover, PairCover.length_ofCircuit, Formula.cost_toCircuit]
  simp [triple, Monotone.and, Fin.sum_univ_two]

example {U : Type*} (A B C : Set U) :
    (tripleCover A B C).toCircuit.program.cost Monotone.andCost = 4 := by
  rw [PairCover.cost_toCircuit, tripleCover, PairCover.length_ofCircuit, Formula.cost_toCircuit]
  simp [triple, Monotone.and, Fin.sum_univ_two]

example (A B C : Set ℕ) :
    (tripleCover A B C).toCircuit.eval (Monotone.setInterpretation ℕ) ![A, B, C] =
      fun _ => A ∩ B ∩ C := PairCover.eval_toCircuit _

private def emptyCover {U : Type*} : PairCover (∅ : Set U) (Fin.elim0 : Fin 0 → Set U) :=
  PairCover.ofDerivesEmpty [] (fun _ h => h.elim)

private def fullCover {U : Type*} : PairCover (Set.univ : Set U) (Fin.elim0 : Fin 0 → Set U) :=
  PairCover.ofDerivesEmpty [] (fun _ _ => by
    have h : (∅ : Set ↥((Set.univ : Set U)ᶜ)) = Set.univ := by
      ext x
      exact (x.property (Set.mem_univ x.val)).elim
    rw [h]
    exact .univ)

example {U : Type*} : (emptyCover (U := U)).toCircuit.program.cost Monotone.andCost = 0 := by
  rw [PairCover.cost_toCircuit]
  rfl

example {U : Type*} : (fullCover (U := U)).toCircuit.program.cost Monotone.andCost = 0 := by
  rw [PairCover.cost_toCircuit]
  rfl

example {U : Type*} : (fullCover (U := U)).toCircuit.eval (Monotone.setInterpretation U)
    Fin.elim0 = fun _ => Set.univ := PairCover.eval_toCircuit _

end CslibFrontierTests.FusionQuadratic
