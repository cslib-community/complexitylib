/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Circuit.Boolean.AuxiliaryFormula
import Mathlib.Tactic

/-! Lemma 6.1 of submission 865 on the one-bit identity with one row. -/

namespace CslibFrontierTests.CircuitAuxiliaryFormula
open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Communication

/-- The first bit of a one-bit string. -/
def g₁ (x : BitString 1) : Bool := x 0

/-- The one-row matrix with row `(true)`. -/
def Z₁ : Fin 1 → BitString 1 := fun _ _ => true

/-- The protocol that always rejects solves `R_g(X)` when `gᵐ` is constant on `X`: here the
single matrix with row `(true)`. -/
private theorem reject_solves :
    (Protocol.output none : Protocol (Fin 1 → BitString 1) (Fin 1 → BitString 1)
      (Option (Fin 1 × Fin 1))).Solves (composeKW g₁) {Z₁} {Z₁} := by
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst hx hy
  exact fun _ => rfl

/-- Lemma 6.1 gives a formula of depth zero that equals `p_{gᵐ(Z)}` on that matrix. -/
example : ∃ φ : Formula signature (1 * 1 + 2 ^ 1), φ.depthWith binaryCost ≤ 0 ∧
    ∀ q : BitString 1 → Bool, φ.eval interpretation (auxInput Z₁ q) = q (rowValues g₁ Z₁) := by
  obtain ⟨φ, hd, -, h⟩ := exists_auxFormula reject_solves
  exact ⟨φ, hd, h _ rfl⟩

/-- Its predictor is correct on that matrix: `τ_φ(Z) = gᵐ(Z) = (true)`. -/
example : predictor (auxFormula g₁ (Protocol.output none) {Z₁} {Z₁}) Z₁ =
    some (fun _ => true : BitString 1) :=
  predictor_auxFormula reject_solves rfl

/-- The predictor of the constant formula `false` is `⊥`: no `p_c` is constantly false. -/
example : predictor (Formula.const false : Formula signature (1 * 1 + 2 ^ 1)) Z₁ = none := by
  cases h : predictor (Formula.const false : Formula signature (1 * 1 + 2 ^ 1)) Z₁
  · rfl
  · rw [predictor_eq_some_iff] at h
    simpa using h fun _ => true

end CslibFrontierTests.CircuitAuxiliaryFormula
