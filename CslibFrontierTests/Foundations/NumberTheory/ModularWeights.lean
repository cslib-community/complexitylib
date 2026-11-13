/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.ModularWeights
public import Mathlib.Tactic.NormNum.Prime

/-!
# Modular weights: concrete checks

The weight `modWeight 5 2` on two variables is `(2, 4)`. For `p = 5` some `a < 5` separates the
exponent vectors of `x₀` and `x₁`; the residue `a = 1` does not, so the choice of `a` matters.
-/

public section

namespace CslibFrontierTests.ModularWeights

open Cslib

/-- `2 ^ 2 mod 5 = 4`. -/
theorem modWeight_five_two : modWeight 5 2 (1 : Fin 2) = 4 := by decide

/-- The values of `modWeight 5 a` are below `5`. -/
theorem modWeight_five_lt (a : ℕ) (i : Fin 2) : modWeight 5 a i < 5 :=
  modWeight_lt (by norm_num) a i

/-- Some `a < 5` gives the exponent vectors of `x₀` and `x₁` different weights. -/
theorem exists_separating : ∃ a < 5,
    Finsupp.weight (modWeight 5 a) (Finsupp.single (0 : Fin 2) 1) ≠
      Finsupp.weight (modWeight 5 a) (Finsupp.single (1 : Fin 2) 1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a, ha, h⟩ := exists_modWeight_separating (p := 5) (δ := 1) (by norm_num)
    {(Finsupp.single (0 : Fin 2) 1, Finsupp.single (1 : Fin 2) 1)}
    (by simp [Finsupp.single_left_inj]) (by simp)
  exact ⟨a, ha, h _ (Finset.mem_singleton_self _)⟩

/-- The residue `1` does not separate the exponent vectors of `x₀` and `x₁`. -/
theorem not_separating_one :
    Finsupp.weight (modWeight 5 1) (Finsupp.single (0 : Fin 2) 1) =
      Finsupp.weight (modWeight 5 1) (Finsupp.single (1 : Fin 2) 1) := by
  simp [Finsupp.weight_apply, modWeight]

end CslibFrontierTests.ModularWeights
