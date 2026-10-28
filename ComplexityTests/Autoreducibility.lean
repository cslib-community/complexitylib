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

/-! ### Concrete polynomial-time many-one mitotic set -/

/-- `{[]}ᶜ` is polynomial-time many-one mitotic, split by `headTrueSet`. Both halves `{w | w ≠ [] ∧
w.headD false = true}` and `{w | w ≠ [] ∧ w.headD false = false}` are non-empty and non-universal
sets in `P`, so both are mutually polynomial-time reducible to `{[]}ᶜ`. -/
theorem coSingleton_mitotic : PolyTimeManyOneMitotic encBits ({[]}ᶜ : Set (List Bool)) :=
  ⟨headTrueSet, headTrueSet_mem_P,
    ⟨⟨fun w => if w.isEmpty then [] else [true], by fun_prop,
       fun w => by cases w <;> simp [headTrueSet]⟩,
     ⟨fun w => if w.headD false then [true] else [], by fun_prop,
       fun w => by rcases w with _ | ⟨_ | _, _⟩ <;> simp [headTrueSet]⟩⟩,
    ⟨⟨fun w => if w.isEmpty then [] else [false], by fun_prop,
       fun w => by cases w <;> simp [headTrueSet]⟩,
     ⟨fun w => if !w.isEmpty && !w.headD false then [true] else [], by fun_prop,
       fun w => by rcases w with _ | ⟨_ | _, _⟩ <;> simp [headTrueSet]⟩⟩⟩

-- `{[]}ᶜ` is disjunctive, 1-truth-table, bounded truth-table, and truth-table autoreducible.
example : PolyTimeDTTAutoreducible encBits ({[]}ᶜ : Set (List Bool)) :=
  coSingleton_mitotic.polyTimeDTTMitotic.polyTimeDTTAutoreducible

example : PolyTimeKTruthTableAutoreducible 1 encBits ({[]}ᶜ : Set (List Bool)) :=
  coSingleton_mitotic.polyTimeKTruthTableMitotic_one.polyTimeKTruthTableAutoreducible

example : PolyTimeKTruthTableAutoreducible 2 encBits ({[]}ᶜ : Set (List Bool)) :=
  (coSingleton_mitotic.polyTimeKTruthTableMitotic_one.mono
    (by decide : 1 ≤ 2)).polyTimeKTruthTableAutoreducible

example : PolyTimeBTTAutoreducible encBits ({[]}ᶜ : Set (List Bool)) :=
  coSingleton_mitotic.polyTimeBTTMitotic.polyTimeBTTAutoreducible

example : PolyTimeTruthTableAutoreducible encBits ({[]}ᶜ : Set (List Bool)) :=
  coSingleton_mitotic.polyTimeTruthTableMitotic.polyTimeTruthTableAutoreducible

-- By complement closure, the singleton `{[]}` is 1-truth-table, bounded truth-table,
-- and truth-table autoreducible, and its complement is conjunctive truth-table autoreducible.
example : PolyTimeKTruthTableAutoreducible 1 encBits ({[]} : Set (List Bool)) := by
  simpa using coSingleton_mitotic.polyTimeKTruthTableAutoreducible_one.compl

example : PolyTimeBTTAutoreducible encBits ({[]} : Set (List Bool)) := by
  simpa using coSingleton_mitotic.polyTimeBTTAutoreducible.compl

example : PolyTimeTruthTableAutoreducible encBits ({[]} : Set (List Bool)) := by
  simpa using coSingleton_mitotic.polyTimeTruthTableAutoreducible.compl

example : PolyTimeCTTAutoreducible encBits ({[]} : Set (List Bool)) := by
  simpa using polyTimeDTTAutoreducible_iff_polyTimeCTTAutoreducible_compl.mp
    coSingleton_mitotic.polyTimeDTTAutoreducible

-- However, `{[]}ᶜ` is strictly not many-one autoreducible, because its complement is a singleton.
example : ¬ PolyTimeManyOneAutoreducible encBits ({[]}ᶜ : Set (List Bool)) :=
  not_polyTimeManyOneAutoreducible_compl_singleton []

end ComplexityTests.Autoreducibility
