/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Logics.Propositional.Resolution.TseitinSpace

/-!
# Tests: clause space of resolution refutations

Refutations of `x ∧ ¬x` in clause space `3`, and none in space `2`; a refutation that erases
clauses to stay in space `3` although it has five lines; the Atserias–Dalmau inequality on it, and
its use for the width of a refutation of a formula with a clause of width `3`; space lower bounds
for Tseitin formulas; and the axioms of the headline theorems.
-/

namespace ComplexityTests.ProofComplexity.Space

open Cslib Cslib.Logic.PL

/-! ### `x ∧ ¬x` -/

/-- `x₀ ∧ ¬x₀`. -/
private def ψ : CNF ℕ := [[(0, true)], [(0, false)]]

/-- Download both clauses and resolve them: three clauses at the end. -/
private theorem refutableInSpace_ψ : ψ.RefutableInSpace 3 :=
  ⟨[.download [(0, true)], .download [(0, false)], .infer [(0, true)] [(0, false)] 0], _,
    .stepL ⟨.download (by decide), by decide⟩ <| .stepL ⟨.download (by decide), by decide⟩ <|
      .stepL ⟨.infer 0 (by decide) (by decide) (by decide) (by decide), by decide⟩ .refl,
    by decide⟩

example : ψ.RefutableInSpace 3 ∧ ¬ ψ.RefutableInSpace 2 :=
  ⟨refutableInSpace_ψ, fun h => absurd (h.three_le (by decide)) (by decide)⟩

/-- A formula containing the empty clause is refutable in clause space `1`. -/
example : CNF.RefutableInSpace ([[]] : CNF ℕ) 1 :=
  ⟨[.download []], _, .stepL ⟨.download (by decide), by decide⟩ .refl, by decide⟩

/-- The empty, satisfiable formula is refutable in no clause space. -/
example : ¬ ∃ s, CNF.RefutableInSpace ([] : CNF ℕ) s := by
  rw [CNF.exists_refutableInSpace_iff_not_satisfiable, not_not]
  exact ⟨fun _ => false, rfl⟩

/-! ### Erasing clauses saves space -/

/-- `x₀ ∧ (¬x₀ ∨ x₁) ∧ ¬x₁`. -/
private def φ : CNF ℕ := [[(0, true)], [(0, false), (1, true)], [(1, false)]]

/-- Derive `x₁`, erase its parents, then refute `x₁ ∧ ¬x₁`: never more than three clauses, although
the refutation has five lines. -/
private theorem refutableInSpace_φ : φ.RefutableInSpace 3 :=
  ⟨[.download [(0, true)], .download [(0, false), (1, true)],
      .infer [(0, true)] [(0, false), (1, true)] 0, .erase [(0, true)],
      .erase [(0, false), (1, true)], .download [(1, false)], .infer [(1, true)] [(1, false)] 1],
    _,
    .stepL ⟨.download (by decide), by decide⟩ <| .stepL ⟨.download (by decide), by decide⟩ <|
      .stepL ⟨.infer 0 (by decide) (by decide) (by decide) (by decide), by decide⟩ <|
      .stepL ⟨.erase _, by decide⟩ <| .stepL ⟨.erase _, by decide⟩ <|
      .stepL ⟨.download (by decide), by decide⟩ <|
      .stepL ⟨.infer 1 (by decide) (by decide) (by decide) (by decide), by decide⟩ .refl,
    by decide⟩

/-- The Atserias–Dalmau inequality: clauses of width at most `2`, clause space `3`, so width
`3 + 2 - 3 = 2`. -/
example : φ.RefutableInWidth 2 :=
  refutableInSpace_φ.refutableInWidth (k := 2) (by decide)

/-! ### The width of the formula matters -/

/-- `(x₀ ∨ x₁ ∨ x₂) ∧ ¬x₀ ∧ ¬x₁ ∧ ¬x₂`. Its only clause of width more than `1` is needed, so every
refutation has a line of width `3`, while it is refutable in clause space `3`. -/
private def χ : CNF ℕ :=
  [[(0, true), (1, true), (2, true)], [(0, false)], [(1, false)], [(2, false)]]

/-- Resolve the long clause against the unit clauses one at a time, erasing as we go. -/
private theorem refutableInSpace_χ : χ.RefutableInSpace 3 :=
  ⟨[.download [(0, true), (1, true), (2, true)], .download [(0, false)],
      .infer [(0, true), (1, true), (2, true)] [(0, false)] 0,
      .erase [(0, true), (1, true), (2, true)], .erase [(0, false)], .download [(1, false)],
      .infer [(1, true), (2, true)] [(1, false)] 1, .erase [(1, true), (2, true)],
      .erase [(1, false)], .download [(2, false)], .infer [(2, true)] [(2, false)] 2],
    _,
    .stepL ⟨.download (by decide), by decide⟩ <| .stepL ⟨.download (by decide), by decide⟩ <|
      .stepL ⟨.infer 0 (by decide) (by decide) (by decide) (by decide), by decide⟩ <|
      .stepL ⟨.erase _, by decide⟩ <| .stepL ⟨.erase _, by decide⟩ <|
      .stepL ⟨.download (by decide), by decide⟩ <|
      .stepL ⟨.infer 1 (by decide) (by decide) (by decide) (by decide), by decide⟩ <|
      .stepL ⟨.erase _, by decide⟩ <| .stepL ⟨.erase _, by decide⟩ <|
      .stepL ⟨.download (by decide), by decide⟩ <|
      .stepL ⟨.infer 2 (by decide) (by decide) (by decide) (by decide), by decide⟩ .refl,
    by decide⟩

/-- Without the long clause the formula is satisfiable. -/
private theorem satisfiable_tail : CNF.Satisfiable ([[(0, false)], [(1, false)], [(2, false)]] :
    CNF ℕ) :=
  ⟨fun _ => false, rfl⟩

/-- So no refutation has width `2`: its lines would all be derivable from the unit clauses. -/
private theorem not_refutableInWidth_χ : ¬ χ.RefutableInWidth 2 := by
  rintro ⟨ls, hp, hnil, hw⟩
  -- a proof avoiding the long clause refutes the satisfiable unit clauses
  suffices ∀ {ls}, χ.IsProof ls → (∀ c ∈ ls, c.width ≤ 2) →
      CNF.IsProof [[(0, false)], [(1, false)], [(2, false)]] ls from
    satisfiable_tail.elim fun σ hσ =>
      absurd ⟨σ, hσ⟩ ((this hp hw).derives hnil).not_satisfiable
  intro ls hp hw
  induction hp with
  | nil => exact .nil
  | @mem ls c _ hc ih =>
    have hw' := hw c List.mem_cons_self
    refine (ih fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')).mem ?_
    simp only [χ, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact absurd hw' (by decide)
    all_goals decide
  | resolvent v _ h₁ h₂ hv₁ hv₂ ih =>
    exact (ih fun c' hc' => hw c' (List.mem_cons_of_mem _ hc')).resolvent v h₁ h₂ hv₁ hv₂

/-- The Atserias–Dalmau inequality is attained: clauses of width at most `3`, clause space `3`,
width `3 + 3 - 3 = 3` and not `2`. -/
example : χ.RefutableInWidth 3 ∧ ¬ χ.RefutableInWidth 2 :=
  ⟨refutableInSpace_χ.refutableInWidth (k := 3) (by decide), not_refutableInWidth_χ⟩

/-- Its contrapositive: clause space `3` is the least possible. -/
example {s : ℕ} (h : χ.RefutableInSpace s) : 3 ≤ s := by
  have := h.add_four_le (k := 3) (by decide) not_refutableInWidth_χ
  omega

/-! ### Tseitin formulas -/

/-- The space bound for rotation maps applies to the expanders. -/
example (n : ℕ) [Nontrivial (Fin n)] {χ : Fin n → Bool} {s : ℕ}
    (h : (CNF.tseitinFormula (RotationMap.expander (Fin n)).edgeEnds χ).RefutableInSpace s) :
    (n : ℝ) / 18000 + 3 ≤ s + 120 := by
  have hh := RotationMap.le_edgeExpansion_expander (Fin n)
  have := Tseitin.edgeExpansion_mul_card_div_three_add_three_le_of_refutableInSpace _
    (lt_of_lt_of_le (by norm_num) hh) h
  simp only [Fintype.card_fin] at this
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

/-- The hard family at its least size needs clause space at least `122`. -/
example : ∃ m, ∃ φ : CNF (Fin m), ¬ φ.Satisfiable ∧ ∀ s, φ.RefutableInSpace s → 122 ≤ s := by
  obtain ⟨m, -, φ, -, -, hφ, hs⟩ := CNF.exists_forall_refutableInSpace_le 4392000 le_rfl
  exact ⟨m, φ, hφ, fun s h => by have := hs s h; omega⟩

/-! ### Axioms -/

/--
info: 'Cslib.Logic.PL.CNF.RefutableInSpace.refutableInWidth' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.RefutableInSpace.refutableInWidth

/--
info: 'Cslib.Logic.PL.CNF.exists_forall_refutableInSpace_le' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Logic.PL.CNF.exists_forall_refutableInSpace_le

end ComplexityTests.ProofComplexity.Space
