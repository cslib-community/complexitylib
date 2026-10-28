/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Reduction.Autoreducibility
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Tests for resource-bounded autoreducibility and mitoticity: singleton and co-singleton
obstructions, concrete autoreducible language instances, hierarchy projections, and mitoticity
implications. -/

namespace ComplexityTests.Autoreducibility

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {encA : α ↪ List Bool} {A : Set α}

/-! ### Singleton and co-singleton obstructions -/

example : ¬ PolyTimeManyOneAutoreducible encBits {[true]} :=
  not_polyTimeManyOneAutoreducible_singleton [true]

example : ¬ PolyTimeManyOneAutoreducible encBits {[true]}ᶜ :=
  not_polyTimeManyOneAutoreducible_compl_singleton [true]

example : ¬ LogSpaceManyOneAutoreducible encBits {[true]} :=
  not_logSpaceManyOneAutoreducible_singleton [true]

example : ¬ LogSpaceManyOneAutoreducible encBits {[true]}ᶜ :=
  not_logSpaceManyOneAutoreducible_compl_singleton [true]

/-! ### Non-trivial language in `P` is many-one autoreducible -/

private def headTrueSet : Set (List Bool) :=
  {w : List Bool | w.headD false = true}

private theorem headTrueSet_mem_P : headTrueSet ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

example : PolyTimeManyOneAutoreducible encBits headTrueSet :=
  PolyTimeManyOneAutoreducible.of_two_mem_two_notMem headTrueSet_mem_P
    (y₀ := [true]) (y₁ := [true, false]) rfl rfl (by decide)
    (n₀ := []) (n₁ := [false]) (fun h => by cases h) (fun h => by cases h) (by decide)

/-! ### Autoreducibility hierarchy projections -/

example (h : LogSpaceManyOneAutoreducible encA A) : PolyTimeManyOneAutoreducible encA A :=
  h.polyTimeManyOneAutoreducible

example (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeKTruthTableAutoreducible 1 encA A :=
  h.polyTimeKTruthTableAutoreducible_one

example (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeDTTAutoreducible encA A :=
  h.polyTimeDTTAutoreducible

example (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeCTTAutoreducible encA A :=
  h.polyTimeCTTAutoreducible

example (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeBTTAutoreducible encA A :=
  h.polyTimeBTTAutoreducible

example (h : PolyTimeManyOneAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible

example (h : PolyTimeDTTAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible

example (h : PolyTimeCTTAutoreducible encA A) : PolyTimeTruthTableAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible

example : PolyTimeDTTAutoreducible encA A ↔ PolyTimeCTTAutoreducible encA Aᶜ :=
  polyTimeDTTAutoreducible_iff_polyTimeCTTAutoreducible_compl

/-! ### Mitoticity hierarchy and autoreducibility implications -/

example (h : LogSpaceManyOneMitotic encA A) : PolyTimeManyOneMitotic encA A :=
  h.polyTimeManyOneMitotic

example (h : PolyTimeManyOneMitotic encA A) : PolyTimeBTTMitotic encA A :=
  h.polyTimeBTTMitotic

example (h : PolyTimeManyOneMitotic encA A) : PolyTimeTruthTableMitotic encA A :=
  h.polyTimeTruthTableMitotic

example (h : PolyTimeManyOneMitotic encA A) : PolyTimeDTTAutoreducible encA A :=
  h.polyTimeDTTAutoreducible

example (h : PolyTimeManyOneMitotic encA A) : PolyTimeKTruthTableAutoreducible 1 encA A :=
  h.polyTimeKTruthTableAutoreducible_one

example (h : PolyTimeManyOneMitotic encA A) : PolyTimeBTTAutoreducible encA A :=
  h.polyTimeBTTAutoreducible

example (h : PolyTimeManyOneMitotic encA A) : PolyTimeTruthTableAutoreducible encA A :=
  h.polyTimeTruthTableAutoreducible

example (h : PolyTimeManyOneMitotic encA A) :
    PolyTimeManyOneAutoreducible encA A ↔ ∀ a ∉ A, ∃ n ∉ A, n ≠ a :=
  h.polyTimeManyOneAutoreducible_iff

end ComplexityTests.Autoreducibility
