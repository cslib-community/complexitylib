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

/-! ### Non-trivial language in `P` is many-one autoreducible -/

private def headTrueSet : Set (List Bool) :=
  {w : List Bool | w.headD false = true}

private theorem headTrueSet_mem_P : headTrueSet ∈ P encBits :=
  ⟨fun w => w.headD false, by fun_prop, fun _ => Iff.rfl⟩

example : PolyTimeManyOneAutoreducible encBits headTrueSet :=
  PolyTimeManyOneAutoreducible.of_two_mem_two_notMem headTrueSet_mem_P
    (y₀ := [true]) (y₁ := [true, false]) rfl rfl (by decide)
    (n₀ := []) (n₁ := [false]) (fun h => by cases h) (fun h => by cases h) (by decide)

/-! ### Concrete polynomial-time many-one mitotic set and separations -/

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

-- `{[]}ᶜ` witnesses that polynomial-time many-one mitoticity (and DTT / 1-tt / btt / tt
-- autoreducibility) does not imply polynomial-time or log-space many-one autoreducibility.
example :
    ∃ A : Set (List Bool),
      PolyTimeManyOneMitotic encBits A ∧
      PolyTimeDTTAutoreducible encBits A ∧
      PolyTimeKTruthTableAutoreducible 2 encBits A ∧
      ¬ PolyTimeManyOneAutoreducible encBits A ∧
      ¬ LogSpaceManyOneAutoreducible encBits A :=
  ⟨{[]}ᶜ,
    coSingleton_mitotic,
    coSingleton_mitotic.polyTimeDTTMitotic.polyTimeDTTAutoreducible,
    (coSingleton_mitotic.polyTimeKTruthTableMitotic_one.mono
      (by decide : 1 ≤ 2)).polyTimeKTruthTableAutoreducible,
    not_polyTimeManyOneAutoreducible_compl_singleton [],
    not_logSpaceManyOneAutoreducible_compl_singleton []⟩

-- `{[]}` witnesses that 1-tt, btt, tt, and CTT autoreducibility do not imply polynomial-time or
-- log-space many-one autoreducibility.
example :
    ∃ A : Set (List Bool),
      PolyTimeKTruthTableAutoreducible 1 encBits A ∧
      PolyTimeBTTAutoreducible encBits A ∧
      PolyTimeTruthTableAutoreducible encBits A ∧
      PolyTimeCTTAutoreducible encBits A ∧
      ¬ PolyTimeManyOneAutoreducible encBits A ∧
      ¬ LogSpaceManyOneAutoreducible encBits A :=
  ⟨{[]},
    by simpa using coSingleton_mitotic.polyTimeKTruthTableAutoreducible_one.compl,
    by simpa using coSingleton_mitotic.polyTimeBTTAutoreducible.compl,
    by simpa using coSingleton_mitotic.polyTimeTruthTableAutoreducible.compl,
    by
      simpa using polyTimeDTTAutoreducible_iff_polyTimeCTTAutoreducible_compl.mp
        coSingleton_mitotic.polyTimeDTTAutoreducible,
    not_polyTimeManyOneAutoreducible_singleton [],
    not_logSpaceManyOneAutoreducible_singleton []⟩

end ComplexityTests.Autoreducibility
