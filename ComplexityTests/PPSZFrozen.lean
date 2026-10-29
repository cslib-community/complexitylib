/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.Frozen

/-! Frozen variables and guess probabilities for PPSZ on `(x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁)`, which has two
satisfying assignments. The variable `x₀` is frozen and `x₁` is not. With `w = 1`, `x₀` is guessed
exactly when it comes before `x₁`, so its guess probability is `1 / 2`, which the first-step
identity computes and which meets the frozen guess bound `1 - qbar 2 1`. In `¬x₀ ∨ x₁` the variable
`x₁` is liquid, and becomes frozen once `x₀` is fixed. -/

namespace ComplexityTests.PPSZFrozen

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.PPSZ Finset

/-- `(x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁)`: its solutions are the assignments with `x₀ = true`. -/
def φ : CNF (Fin 2) := [[(0, true), (1, true)], [(0, true), (1, false)]]

/-- The all-true solution. -/
def σ : Fin 2 → Bool := fun _ => true

theorem φ_sat : φ.eval σ = true := by decide

theorem φ_len : ∀ c ∈ φ, c.length ≤ 2 := by decide

theorem eq_true_of_eval : ∀ γ : Fin 2 → Bool, φ.eval γ = true → γ 0 = true := by decide

-- Fixing `x₁ = true` satisfies the first clause and shortens the second to `x₀`.
example : φ.restrictBy (PPZ.restrict σ {1}) = [[(0, true)]] := by decide

-- Under an assignment that extends the restriction, the restricted formula has the value of `φ`;
-- `x₀ = false, x₁ = true` falsifies both.
example : (φ.restrictBy (PPZ.restrict σ {1})).eval ![false, true] = φ.eval ![false, true] :=
  CNF.eval_restrictBy (by decide)

-- Restriction does not widen clauses.
example : ∀ c ∈ φ.restrictBy (PPZ.restrict σ {1}), c.length ≤ 2 :=
  CNF.length_le_of_mem_restrictBy φ_len

/-- `x₀` is frozen with nothing assigned. -/
theorem frozen_zero : Frozen φ (PPZ.restrict σ ∅) 0 :=
  ⟨by simp [PPZ.restrict], fun γ γ' h h' => by
    rw [eq_true_of_eval γ h.2, eq_true_of_eval γ' h'.2]⟩

-- `x₁` is not frozen: both of its values extend to solutions.
example : ¬Frozen φ (PPZ.restrict σ ∅) 1 := fun h => by
  have := h.2 σ ![true, false] (isSatExtension_restrict φ_sat ∅)
    ⟨fun _ _ h => by simp [PPZ.restrict] at h, by decide⟩
  simp [σ] at this

/-- With nothing assigned, no single clause implies `x₀ = true`. -/
theorem not_wImplied_empty : ¬WImplied φ 1 (PPZ.restrict σ ∅) 0 true := by
  rintro ⟨ψ, hψ, hlen, himp⟩
  have hnone : ∀ γ : Fin 2 → Bool, ∀ y c, PPZ.restrict σ ∅ y = some c → γ y = c := by
    simp [PPZ.restrict]
  rcases ψ with _ | ⟨c, _ | ⟨c', ψ⟩⟩
  · exact absurd (himp (fun _ => false) (hnone _) rfl) (by decide)
  · have hc := hψ c List.mem_cons_self
    simp only [φ, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact absurd (himp ![false, true] (hnone _) (by decide)) (by decide)
    · exact absurd (himp (fun _ => false) (hnone _) (by decide)) (by decide)
  · simp at hlen

/-- With `x₁` fixed, the second clause implies `x₀ = true`. -/
theorem wImplied_one : WImplied φ 1 (PPZ.restrict σ {1}) 0 true := by
  refine ⟨[[(0, true), (1, false)]], by simp [φ], by simp, fun γ hγ hψ => ?_⟩
  have h1 : γ 1 = true := hγ 1 true (by simp [PPZ.restrict, σ])
  simpa [CNF.eval, Clause.eval, Literal.eval, h1] using hψ

/-- **The guess probability of `x₀` is `1 / 2`**, by the first-step identity: `2 * u = 1 + 0`,
since `x₀` is not implied at the start and is implied once `x₁` is fixed. -/
theorem guessProb_zero : guessProb φ 1 ∅ σ 0 = 1 / 2 := by
  have h := card_compl_mul_guessProb (φ := φ) (w := 1) (σ := σ) (x := 0) (T := ∅) (by simp)
  rw [show ((∅ : Finset (Fin 2))ᶜ.erase 0) = {1} by decide, sum_singleton, insert_empty_eq,
    guessProb_eq_zero_of_wImplied wImplied_one, ite_eq_right
      (show ¬WImplied φ 1 (PPZ.restrict σ ∅) 0 (σ 0) from not_wImplied_empty),
    compl_empty, card_univ, Fintype.card_fin, Nat.cast_ofNat] at h
  linarith

-- The frozen guess bound for `k = 2`, `h = 1` is `1 - qbar 2 1 = 1 / 2`, attained here.
example : guessProb φ 1 ∅ σ 0 ≤ 1 - qbar 2 1 :=
  guessProb_le_of_frozen φ_sat frozen_zero φ_len (by decide)

example : 1 - qbar 2 1 = guessProb φ 1 ∅ σ 0 := by
  rw [guessProb_zero, qbar_one (by norm_num)]
  norm_num

-- Fixing `x₁` can only lower the guess probability (here to `0`).
example : guessProb φ 1 {1} σ 0 ≤ guessProb φ 1 ∅ σ 0 :=
  guessProb_le_of_subset (empty_subset _)

-- Wider clauses give smaller bounds: `qbar 4 2 ≤ qbar 3 2 = 31 / 70`.
example : qbar 4 2 ≤ 31 / 70 :=
  qbar_three_two ▸ antitone_qbar_width 2 (by norm_num : 3 ≤ 4)

/-! ### A variable that becomes frozen only after a restriction -/

/-- `¬x₀ ∨ x₁`: with nothing fixed `x₁` is liquid, and fixing `x₀ = true` freezes it. -/
def χ : CNF (Fin 2) := [[(0, false), (1, true)]]

theorem χ_sat : χ.eval σ = true := by decide

/-- With nothing assigned, `x₁` is not frozen: the all-false assignment also satisfies `χ`. -/
theorem not_frozen_χ : ¬Frozen χ (PPZ.restrict σ ∅) 1 := fun h => by
  have := h.2 σ (fun _ => false) (isSatExtension_restrict χ_sat ∅)
    ⟨fun _ _ h => by simp [PPZ.restrict] at h, by decide⟩
  simp [σ] at this

/-- After fixing `x₀ = true`, `x₁` is frozen. -/
theorem frozen_χ : Frozen χ (PPZ.restrict σ {0}) 1 := by
  have key : ∀ γ : Fin 2 → Bool, γ 0 = true → χ.eval γ = true → γ 1 = true := by decide
  refine ⟨by simp [PPZ.restrict], fun γ γ' h h' => ?_⟩
  have h0 : ∀ γ : Fin 2 → Bool, IsSatExtension χ (PPZ.restrict σ {0}) γ → γ 0 = true :=
    fun γ h => h.1 0 true (by simp [PPZ.restrict, σ])
  rw [key γ (h0 γ h) h.2, key γ' (h0 γ' h') h'.2]

-- The frozen guess bound then applies to `x₁` under the restriction.
example : guessProb χ 1 {0} σ 1 ≤ 1 - qbar 2 1 :=
  guessProb_le_of_frozen χ_sat frozen_χ (by decide) (by decide)

-- A frozen variable carries a single satisfying literal.
example : ¬SatLit χ (PPZ.restrict σ {0}) 1 false := fun h => by
  simpa [σ] using (satLit_iff_of_frozen (isSatExtension_restrict χ_sat {0}) frozen_χ).1 h

end ComplexityTests.PPSZFrozen
