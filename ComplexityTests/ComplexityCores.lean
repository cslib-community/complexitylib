/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.EXP.Decidable
import Complexity.Computability.Complexity.Classes.Immune.Construction
import Complexity.Computability.Complexity.Classes.Immune.PolyTimeCore
import Complexity.Computability.Complexity.Classes.Immune.RecursiveCore
import Complexity.Computability.Machines.Turing.MultiTape.Halting

/-!
# Tests for complexity cores

Checked instances of complexity cores: finite sets are cores and cores of problems in `P` are
finite; bounded halting has an infinite core but the universe is not one of its cores; the
`P`-bi-immune problem in `E` has the universe as a core, and it is decidable, so the machine
statement is not vacuous; every set is a machine core of the undecidable halting problem, which is
why the class form needs decidability. Bounded halting also has an infinite decidable core inside
it, while the recursive core construction applied to a problem in `P` yields a finite set.
-/

namespace ComplexityTests.ComplexityCores

open Cslib.Complexity Turing.MultiTapeTM

/-- Finite sets are cores of every problem. -/
example (A : Set (List Bool)) : IsComplexityCore (P encBits) A {[], [true]} :=
  (Set.toFinite _).isComplexityCore

/-- There are countably many problems in `P`. -/
example : (P encBits).Countable := countable_P encBits

/-- Cores of the universe for `P` are finite: no infinite set is a core of a problem in `P`. -/
example (X : Set (List Bool)) (h : IsComplexityCore (P encBits) Set.univ X) : X.Finite :=
  h.finite_of_mem_P univ_mem_P

/-- The universe is not a core of the nonempty words, a problem in `P`. -/
example : ¬ IsComplexityCore (P encBits) {[]}ᶜ Set.univ := fun h =>
  Set.infinite_univ (α := List Bool)
    (h.finite_of_mem_P (compl_mem_P (Set.finite_singleton _).mem_P))

/-- Bounded halting is outside `P`, so it has an infinite polynomial complexity core inside it. -/
example : ∃ X ⊆ BoundedHalting, X.Infinite ∧ IsPolyTimeCore encBits BoundedHalting X :=
  notMem_P_iff_exists_infinite_isPolyTimeCore.mp BoundedHalting.notMem_P

/-- The same follows from hardness for `EXP`. -/
example : ∃ X ⊆ BoundedHalting, X.Infinite ∧ IsPolyTimeCore encBits BoundedHalting X :=
  (BoundedHalting.polyTimeHard_EXP).exists_infinite_isPolyTimeCore_EXP

/-- Bounded halting is not `P`-bi-immune, so the universe is not one of its cores: some decider of
bounded halting runs in polynomial time on infinitely many instances. -/
example : ¬ IsComplexityCore (P encBits) BoundedHalting Set.univ := fun h =>
  let ⟨⟨B, hB, hBinf, hBA⟩, _⟩ := BoundedHalting.exists_infinite_subset_mem_P
  hBinf (isComplexityCore_univ_iff.mp h B hB (.inl hBA))

/-- The `P`-bi-immune problem in `E` is decidable, and every decider runs in superpolynomial time
almost everywhere. -/
example : IsDecidable BiImmune.language encBits ∧
    IsPolyTimeCore encBits BiImmune.language Set.univ :=
  ⟨BiImmune.isDecidable_language, BiImmune.isPolyTimeCore_univ_language⟩

/-- No machine decides the halting problem, so every set is one of its machine cores: the
correspondence with complexity cores needs decidability. -/
example (X : Set (List Bool × List Bool)) :
    IsPolyTimeCore (encPair encBits encBits) haltingProblem X := by
  refine isPolyTimeCore_iff.mpr fun k State _ tm htm => ?_
  exact absurd (isDecidable_iff_isComputable_indicator.mpr
    (isComputable_iff.mpr ⟨k, State, inferInstance, tm, htm⟩)) not_isDecidable_haltingProblem

/-- Decidability of problems in `P` agrees with the time-bounded case. -/
example (A : Set (List Bool)) (hA : A ∈ P encBits) : IsDecidable A encBits :=
  let ⟨_, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  isDecidable_of_mem_DTIME hk

/-- Bounded halting is decidable and outside `P`, so it has an infinite decidable polynomial
complexity core inside it. -/
example : ∃ X ⊆ BoundedHalting, X.Infinite ∧ IsDecidable X encBits ∧
    IsPolyTimeCore encBits BoundedHalting X :=
  exists_infinite_isDecidable_isPolyTimeCore BoundedHalting.isDecidable BoundedHalting.notMem_P

/-- The universe is decidable and in `P`, so it has no infinite decidable core. -/
example : ¬ ∃ X ⊆ (Set.univ : Set (List Bool)), X.Infinite ∧ IsDecidable X encBits ∧
    IsPolyTimeCore encBits Set.univ X := fun h =>
  (notMem_P_iff_exists_infinite_isDecidable_isPolyTimeCore
    (isDecidable_of_mem_P univ_mem_P)).mpr h univ_mem_P

/-- The recursive core construction applied to a decider of the universe, a problem in `P`, yields
a finite set. -/
example (d : Universal.Desc)
    (hs : ∀ w t b, Universal.runBool d w t = some b → b = indicator Set.univ w)
    (hc : ∀ w, ∃ T, ∀ t, T ≤ t → Universal.runBool d w t = some (indicator Set.univ w)) :
    (RecursiveCore.core d Set.univ).Finite :=
  (RecursiveCore.isComplexityCore_core hs hc).finite_of_mem_P univ_mem_P

/-- The `P`-bi-immune problem in `E` has a description whose clocked runs are sound and eventually
complete, so the hypotheses on the decider are not vacuous. -/
example : ∃ d : Universal.Desc,
    (∀ w t b, Universal.runBool d w t = some b → b = indicator BiImmune.language w) ∧
      ∀ w, ∃ T, ∀ t, T ≤ t → Universal.runBool d w t = some (indicator BiImmune.language w) :=
  (isDecidable_iff_isComputable_indicator.mp BiImmune.isDecidable_language).exists_runBool

/-- The requirements are exactly the problems in `P`. -/
example (B : Set (List Bool)) : B ∈ P encBits ↔ ∃ e, RecursiveCore.requirement e = B :=
  ⟨fun hB => let ⟨e, _, he⟩ := RecursiveCore.exists_requirement_eq hB 0; ⟨e, he⟩,
    fun ⟨e, he⟩ => he ▸ RecursiveCore.requirement_mem_P e⟩

/-- Decidable problems are closed under intersection and union. -/
example : IsDecidable (BoundedHalting ∩ BiImmune.language) encBits ∧
    IsDecidable (BoundedHalting ∪ BiImmune.language) encBits :=
  ⟨BoundedHalting.isDecidable.inter BiImmune.isDecidable_language,
    BoundedHalting.isDecidable.union BiImmune.isDecidable_language⟩

end ComplexityTests.ComplexityCores
