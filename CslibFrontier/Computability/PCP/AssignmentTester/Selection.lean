/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.AssignmentTester

/-!
# Selecting one check of the Hadamard assignment tester

The five checks of `hadamardTester` make at most six queries each. Selecting one uniformly,
instead of running their conjunction, reduces the query count from seventeen to six. The union
bound loses at most a factor of five in rejection. The original product of random strings is
retained, so this construction makes no claim of saving random bits.

## Main definitions

* `Cslib.PCP.HadamardTester.checks`: the five checks, padded to a common six-query interface.
* `Cslib.PCP.selectedHadamardTester`: the tester selecting one of those checks uniformly.

## Main results

* `Cslib.PCP.HadamardTester.one_sub_acceptProb_le_five_mul_selected`: rejection comparison.
* `Cslib.PCP.HadamardTester.passes_selected_honestProof`: perfect completeness.
* `Cslib.PCP.HadamardTester.exists_inputDist_div_le_one_sub_acceptProb_selected`: proximity
  soundness with loss `140`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

namespace HadamardTester

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The five checks on a common coin space and six query positions. The coefficient table is an
argument so that the same construction works with mathematical and executable constraints. -/
def checks (coeff : ((Fin 2 × α) × (Fin 2 × α) ⊕ Fin 2) →
    (Fin 2 × α) × (Fin 2 × α) → Bool) :
    Fin 5 → LocalTest (Pos α) (Rand α) (Fin 6) Bool :=
  ![(((blrTest _).map fun y ↦ .inr (.inl y)).padQueries (by decide)).comapRand Prod.fst,
    (((blrTest _).map fun z ↦ .inr (.inr z)).padQueries (by decide)).comapRand
      (fun ω ↦ ω.2.1),
    ((tensorTest _).map (Sum.elim (fun y ↦ .inr (.inl y)) fun z ↦ .inr (.inr z))).comapRand
      (fun ω ↦ ω.2.2.1),
    (((equationTest coeff equationRhs).map fun z ↦ .inr (.inr z)).padQueries
      (by decide)).comapRand (fun ω ↦ ω.2.2.2.1),
    (((inputTest α).map (Sum.elim .inl fun y ↦ .inr (.inl y))).padQueries
      (by decide)).comapRand (fun ω ↦ ω.2.2.2.2)]

/-- On the shared product coins, the original tester passes precisely when all padded checks pass.
This coupling is used only in the proof; the selected tester reads just one check. -/
private theorem passes_iff_forall_checks (C : α → α → Prop) (π : Pos α → Bool) (ω : Rand α) :
    (hadamardTester C).Passes π ω ↔
      ∀ i, (checks (equationCoeff C) i).Passes π ω := by
  simp [checks, hadamardTester, test, Fin.forall_fin_succ]

end HadamardTester

open HadamardTester

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Select one of the five Hadamard checks uniformly. Shorter checks repeat queries to reach six
positions; their acceptance predicates ignore the extra answers. -/
noncomputable def selectedHadamardTester (C : α → α → Prop) :
    LocalTest (Pos α) (Fin 5 × Rand α) (Fin 6) Bool :=
  LocalTest.mix (checks (equationCoeff C))

namespace HadamardTester

variable {C : α → α → Prop}

/-- Selecting a single check loses at most a factor of five in rejection probability. -/
theorem one_sub_acceptProb_le_five_mul_selected (π : Pos α → Bool) :
    1 - (hadamardTester C).acceptProb π ≤ 5 * (1 - (selectedHadamardTester C).acceptProb π) := by
  simpa only [selectedHadamardTester, Fintype.card_fin, Nat.cast_ofNat] using
    LocalTest.one_sub_acceptProb_le_card_mul_one_sub_acceptProb_mix
      (hadamardTester C) (checks (equationCoeff C)) π
      (fun ω ↦ (passes_iff_forall_checks C π ω).2)

/-- Every selected check passes the honest proof of satisfying labels. -/
theorem passes_selected_honestProof {σ : Fin 2 → α} (hσ : C (σ 0) (σ 1))
    (ω : Fin 5 × Rand α) : (selectedHadamardTester C).Passes (honestProof σ) ω :=
  (passes_iff_forall_checks C (honestProof σ) ω.2).1 (passes_honestProof hσ ω.2) ω.1

/-- Perfect completeness of the six-query tester. -/
theorem acceptProb_selected_honestProof {σ : Fin 2 → α} (hσ : C (σ 0) (σ 1)) :
    (selectedHadamardTester C).acceptProb (honestProof σ) = 1 :=
  ((selectedHadamardTester C).acceptProb_eq_one_iff).2 (passes_selected_honestProof hσ)

/-- High acceptance by the selected tester decodes to satisfying labels near the input tables. -/
theorem exists_inputDist_le_of_le_acceptProb_selected {π : Pos α → Bool} {ρ : ℝ}
    (hρ : ρ < 1 / 140) (h : 1 - ρ ≤ (selectedHadamardTester C).acceptProb π) :
    ∃ σ : Fin 2 → α, C (σ 0) (σ 1) ∧ inputDist π σ ≤ 15 * ρ := by
  have hc := one_sub_acceptProb_le_five_mul_selected (C := C) π
  obtain ⟨σ, hσ, hd⟩ := exists_inputDist_le_of_le_acceptProb (ρ := 5 * ρ)
    (by linarith) (by linarith)
  exact ⟨σ, hσ, by linarith⟩

/-- Proximity soundness of the six-query tester, with rejection coefficient `1/140`. -/
theorem exists_inputDist_div_le_one_sub_acceptProb_selected (hC : ∃ a b, C a b)
    (π : Pos α → Bool) : ∃ σ : Fin 2 → α, C (σ 0) (σ 1) ∧
      inputDist π σ / 140 ≤ 1 - (selectedHadamardTester C).acceptProb π := by
  obtain ⟨σ, hσ, hd⟩ := exists_inputDist_div_le_one_sub_acceptProb hC π
  have hc := one_sub_acceptProb_le_five_mul_selected (C := C) π
  exact ⟨σ, hσ, by linarith⟩

/-- An unsatisfiable constraint is rejected with probability at least `1/140`. -/
theorem one_div_le_one_sub_acceptProb_selected_of_forall_not (hC : ∀ a b, ¬ C a b)
    (π : Pos α → Bool) : 1 / 140 ≤ 1 - (selectedHadamardTester C).acceptProb π := by
  have hs := one_div_le_one_sub_acceptProb_of_forall_not hC π
  have hc := one_sub_acceptProb_le_five_mul_selected (C := C) π
  linarith

end HadamardTester

end Cslib.PCP
