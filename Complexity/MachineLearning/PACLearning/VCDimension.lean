/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.MachineLearning.PACLearning.VCDimension
public import Mathlib.Data.Fintype.EquivFin

/-!
# Basic facts about the VC dimension

Two small facts about the upstream `vcDim` and `HasFiniteVCDim`:
* every finite set shattered by a class of finite VC dimension has at most `vcDim C` elements
  (`SetShatters.card_le_vcDim`), the step `le_csSup` that lower bounds on `vcDim` need;
* a class on a finite domain has finite VC dimension (`hasFiniteVCDim_of_finite`).

## Main results

* `Cslib.MachineLearning.PACLearning.SetShatters.card_le_vcDim`: a shattered finite set bounds the
  VC dimension from below.
* `Cslib.MachineLearning.PACLearning.hasFiniteVCDim_of_finite`: finite domains have finite VC
  dimension.
-/

public section

namespace Cslib.MachineLearning.PACLearning

variable {α : Type*}

/-- A finite set shattered by a class of finite VC dimension has at most `vcDim C` elements. -/
theorem SetShatters.card_le_vcDim {C : ConceptClass α Bool} (hC : HasFiniteVCDim C)
    {W : Finset α} (hW : SetShatters C ↑W) : W.card ≤ vcDim C :=
  le_csSup hC ⟨W, rfl, hW⟩

/-- Every class on a finite domain has finite VC dimension. -/
theorem hasFiniteVCDim_of_finite [Finite α] (C : ConceptClass α Bool) : HasFiniteVCDim C :=
  have := Fintype.ofFinite α
  hasFiniteVCDim_iff.mpr ⟨Fintype.card α, fun W _ => W.card_le_univ⟩

end Cslib.MachineLearning.PACLearning
