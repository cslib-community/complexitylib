/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Oracle.TQBF
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.CountingSAT
import Complexity.Computability.Complexity.Reduction.Turing
import Complexity.Crypto.Game

/-!
# Witnesses for hypotheses of public theorems

Some public theorems take a hypothesis that no other declaration or test discharges. This file
supplies an instance of each such hypothesis, so that the theorems are known to apply.

* `NPTuringHard.P_eq_NP_of_mem_P`, `PPTuringHard.P_eq_PP_of_mem_P` and
  `PSPACETuringHard.P_eq_PSPACE_of_mem_P` apply to the words that encode satisfiable formulas,
  formulas satisfied by a strict majority of assignments, and true quantified formulas. These
  languages of words are hard under polynomial-time many-one reductions (Cook–Levin, `MAJSAT`,
  `TQBF`), hence under Turing reductions.
* `Crypto.Game.IndistinguishableWithError` holds with error `0` between a game family and itself,
  and its conversion `IndistinguishableWithError.indistinguishable` applies.
-/

namespace ComplexityTests.HypothesisWitnesses

open Turing Turing.MultiTapeTM Cslib Cslib.Complexity Cslib.Logic.PL

/-! ### Hardness under polynomial-time Turing reductions, on words -/

/-- The words encoding satisfiable formulas are `NP`-hard under Turing reductions. -/
theorem image_SAT_npTuringHard : NPTuringHard encBits (encCNF '' SAT) :=
  (CookLevin.SAT_npHard.trans ⟨fun φ => encCNF φ, by fun_prop,
    fun φ => encCNF.injective.mem_set_image.symm⟩).polyTimeTuringHard

/-- The words encoding majority-satisfiable formulas are `PP`-hard under Turing reductions. -/
theorem image_MAJSAT_ppTuringHard : PPTuringHard encBits (encCNF '' MAJSAT) :=
  (MAJSAT_ppHard.trans ⟨fun φ => encCNF φ, by fun_prop,
    fun φ => encCNF.injective.mem_set_image.symm⟩).polyTimeTuringHard

/-- The words encoding true quantified formulas are `PSPACE`-hard under Turing reductions. -/
theorem image_TQBF_pspaceTuringHard : PSPACETuringHard encBits (encQBF '' TQBF) :=
  image_TQBF_pspaceHard.polyTimeTuringHard

/-- `NPTuringHard.P_eq_NP_of_mem_P` applies. -/
example (h : encCNF '' SAT ∈ P encBits) : P encBits = NP encBits :=
  image_SAT_npTuringHard.P_eq_NP_of_mem_P h

/-- `PPTuringHard.P_eq_PP_of_mem_P` applies. -/
example (h : encCNF '' MAJSAT ∈ P encBits) : P encBits = PP encBits :=
  image_MAJSAT_ppTuringHard.P_eq_PP_of_mem_P h

/-- `PSPACETuringHard.P_eq_PSPACE_of_mem_P` applies. -/
example (h : encQBF '' TQBF ∈ P encBits) : P encBits = PSPACE encBits :=
  image_TQBF_pspaceTuringHard.P_eq_PSPACE_of_mem_P h

/-! ### Concrete indistinguishability bounds -/

/-- A game family is indistinguishable from itself with error `0`, for any admissibility
predicate. -/
theorem indistinguishableWithError_self {Adversary : Type} (game : Adversary → ℕ → Crypto.Game)
    (Admissible : Adversary → Prop) :
    Crypto.Game.IndistinguishableWithError game game Admissible 0 :=
  fun adversary _ n => by simp

/-- `IndistinguishableWithError.indistinguishable` applies. -/
example {Adversary : Type} (game : Adversary → ℕ → Crypto.Game)
    (Admissible : Adversary → Prop) : Crypto.Game.Indistinguishable game game Admissible :=
  (indistinguishableWithError_self game Admissible).indistinguishable Crypto.negligible_zero

end ComplexityTests.HypothesisWitnesses
