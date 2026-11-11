/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.Immune.Construction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! Immunity holding and failing on small classes, finite and cofinite problems in `P`, the
`P`-bi-immune problem in `E`: a concrete non-member, membership in `E` and `EXP`, meeting a
concrete infinite problem in `P` and its complement, not being decidable in polynomial time, and
not being complete or hard for `E` or `EXP`. -/

namespace CslibFrontierTests.Immune

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM

/-! ### Immunity on small classes -/

/-- Every infinite set is immune to the class of finite sets. -/
example {A : Set ℕ} (hA : A.Infinite) : IsImmune {B | B.Finite} A :=
  isImmune_iff.mpr ⟨hA, fun _ hB _ => hB⟩

/-- The empty set is never immune, and a member of the class is not immune to it. -/
example (C : Set (Set ℕ)) : ¬ IsImmune C ∅ ∧ ¬ IsImmune ({Set.univ} : Set (Set ℕ)) Set.univ :=
  ⟨fun h => h.infinite Set.finite_empty, fun h => h.notMem rfl⟩

/-- The universe is never bi-immune: its complement is empty. -/
example (C : Set (Set ℕ)) : ¬ IsBiImmune C Set.univ :=
  fun h => h.isImmune_compl.infinite (by simp)

/-! ### Problems in `P` -/

/-- Finite problems, the universe and cofinite problems are in `P`. -/
example : ({[true], [false, true]} : Set (List Bool)) ∈ P encBits ∧
    (Set.univ : Set (List Bool)) ∈ P encBits ∧
    (Set.univ \ {[]} : Set (List Bool)) ∈ P encBits :=
  ⟨(Set.toFinite _).mem_P, univ_mem_P, diff_mem_P univ_mem_P (Set.finite_singleton _).mem_P⟩

/-- The universe is in `P`, so it is not `P`-immune. -/
example : ¬ IsImmune (P encBits) (Set.univ : Set (List Bool)) := fun h => h.notMem univ_mem_P

/-- The words of even length form an infinite problem in `P`. -/
theorem even_length_mem_P : {w : List Bool | w.length % 2 = 0} ∈ P encBits :=
  ⟨fun w => decide (w.length % 2 = 0), by fun_prop, fun _ => by simp⟩

theorem even_length_infinite : {w : List Bool | w.length % 2 = 0}.Infinite :=
  Set.infinite_of_injective_forall_mem (f := fun n : ℕ => List.replicate (2 * n) false)
    (fun m n h => by simpa using congrArg List.length h) fun n => by simp

/-! ### The `P`-bi-immune problem -/

/-- The empty word, at stage `0`, is outside the problem. -/
example : [] ∉ BiImmune.language := by
  have h0 : Ladner.index [] = 0 := by decide
  rw [BiImmune.mem_language_iff, h0]
  have := BiImmune.act_le 0
  omega

example : BiImmune.language ∈ E encBits ∧ BiImmune.language ∈ EXP encBits :=
  ⟨BiImmune.language_mem_E, BiImmune.language_mem_EXP⟩

example : IsBiImmune (P encBits) BiImmune.language ∧ IsBiImmune (P encBits) BiImmune.languageᶜ :=
  ⟨BiImmune.isBiImmune_language, isBiImmune_compl.mpr BiImmune.isBiImmune_language⟩

/-- Neither the problem nor its complement is decidable in polynomial time, and both are
infinite. -/
example : BiImmune.language ∉ P encBits ∧ BiImmune.languageᶜ ∉ P encBits ∧
    BiImmune.language.Infinite ∧ BiImmune.languageᶜ.Infinite :=
  ⟨BiImmune.isBiImmune_language.isImmune.notMem, BiImmune.isBiImmune_language.compl_notMem,
    BiImmune.isBiImmune_language.isImmune.infinite,
    BiImmune.isBiImmune_language.isImmune_compl.infinite⟩

/-- The problem contains a word of even length and misses another. -/
example : ∃ w ∈ BiImmune.language, w.length % 2 = 0 ∧
    ∃ w' ∉ BiImmune.language, w'.length % 2 = 0 := by
  obtain ⟨⟨w, hw, hwL⟩, ⟨w', hw', hw'L⟩⟩ :=
    isBiImmune_P_iff.mp BiImmune.isBiImmune_language _ even_length_mem_P even_length_infinite
  exact ⟨w, hwL, hw, w', hw'L, hw'⟩

/-- The problem is not complete or hard for `E` or `EXP` under polynomial-time many-one
reductions. -/
example : ¬ PolyTimeComplete @E encBits BiImmune.language ∧
    ¬ PolyTimeHard @E encBits BiImmune.language ∧
    ¬ PolyTimeComplete @EXP encBits BiImmune.language ∧
    ¬ PolyTimeHard @EXP encBits BiImmune.language :=
  ⟨BiImmune.not_polyTimeComplete_E_language, BiImmune.not_polyTimeHard_E_language,
    BiImmune.not_polyTimeComplete_EXP_language, BiImmune.not_polyTimeHard_EXP_language⟩

/-- `E` and `EXP` contain `P`-bi-immune problems. -/
example : (∃ A ∈ E encBits, IsBiImmune (P encBits) A) ∧
    ∃ A ∈ EXP encBits, IsBiImmune (P encBits) A :=
  ⟨BiImmune.exists_mem_E_isBiImmune_P, BiImmune.exists_mem_EXP_isBiImmune_P⟩

/-! ### Berman's theorem -/

/-- A problem complete for `E` is not `P`-bi-immune, and both it and its complement have infinite
subsets in `P`. -/
example {A : Set (List Bool)} (h : PolyTimeComplete @E encBits A) :
    ¬ IsBiImmune (P encBits) A ∧ ¬ IsImmune (P encBits) Aᶜ :=
  ⟨not_isBiImmune_P_of_polyTimeComplete_E h, (not_isImmune_P_of_polyTimeComplete_E h).2⟩

example {A : Set (List Bool)} (h : PolyTimeComplete @EXP encBits A) :
    ∃ B ∈ P encBits, B.Infinite ∧ B ⊆ Aᶜ :=
  (exists_infinite_subset_mem_P_of_polyTimeComplete_EXP h).2

end CslibFrontierTests.Immune
