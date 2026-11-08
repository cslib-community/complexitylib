/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract library)

import CslibFrontierAbstracts.Check
import CslibFrontier.Probability.Extractor.TwoSource

/-! # Transfer of the Chor–Goldreich theorem to explicit probabilities

The abstract states min-entropy as a bound on every outcome probability and statistical distance
from a uniform bit as `|Pr[true] - 1 / 2|`. This bridge converts both to the library's
`PMF.minEntropy` and statistical distance.
-/

namespace ComplexityAbstracts.ChorGoldreichBridge

open Cslib Cslib.Probability Cslib.Probability.PMF

/-- The probability that a computed bit is `true`, minus one half, is half its bias. -/
private theorem abs_map_true_sub_half {α : Type} [Fintype α] (p : PMF α) (f : α → Bool) :
    |((p.map f) true).toReal - 1 / 2| = |∑ a, (p a).toReal * BitString.signVal (f a)| / 2 := by
  rw [← dist_uniformOfFintype_bool, dist_map_uniformOfFintype_bool]

private theorem do_eq_bind {n : ℕ} (p q : PMF (Fin n → Bool)) :
    (do
        let x ← p
        let y ← q
        return ∑ i, x i * y i : PMF Bool) =
      p.bind fun x => q.map fun y => x ⬝ᵥ y := by
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rfl

theorem chorGoldreich {n : ℕ} {k₁ k₂ : ℝ} (p q : PMF (Fin n → Bool))
    (hp : ∀ x, (p x).toReal ≤ 2 ^ (-k₁)) (hq : ∀ y, (q y).toReal ≤ 2 ^ (-k₂)) :
    |((do
        let x ← p
        let y ← q
        return ∑ i, x i * y i : PMF Bool) true).toReal - 1 / 2| ≤
      2 ^ ((n - k₁ - k₂) / 2) / 2 := by
  have h := isTwoSourceExtractor_dotProduct (ι := Fin n) k₁ k₂ p q
    ((le_minEntropy_iff p).mpr hp) ((le_minEntropy_iff q).mpr hq)
  rw [dist_uniformOfFintype_bool, Fintype.card_fin] at h
  rwa [do_eq_bind]

theorem chorGoldreich_strong {n : ℕ} {k₁ k₂ : ℝ} (p q : PMF (Fin n → Bool))
    (hp : ∀ x, (p x).toReal ≤ 2 ^ (-k₁)) (hq : ∀ y, (q y).toReal ≤ 2 ^ (-k₂)) :
    ∑ y, (q y).toReal * |((do
        let x ← p
        return ∑ i, x i * y i : PMF Bool) true).toReal - 1 / 2| ≤
      2 ^ ((n - k₁ - k₂) / 2) / 2 := by
  have h := sum_mul_abs_bias_dotProduct_le (ι := Fin n)
    ((le_minEntropy_iff p).mpr hp) ((le_minEntropy_iff q).mpr hq)
  rw [Fintype.card_fin] at h
  have hmap (y : Fin n → Bool) : (do
        let x ← p
        return ∑ i, x i * y i : PMF Bool) = p.map fun x => x ⬝ᵥ y := by
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    rfl
  simp only [hmap, abs_map_true_sub_half, mul_div_assoc', ← Finset.sum_div]
  gcongr

theorem orthogonal_sources {n : ℕ} (S : Finset (Fin n)) :
    ∃ p q : PMF (Fin n → Bool),
      (∀ x, (p x).toReal ≤ 2 ^ (-(S.card : ℝ))) ∧
      (∀ y, (q y).toReal ≤ 2 ^ (-((n : ℝ) - S.card))) ∧
      ((do
        let x ← p
        let y ← q
        return ∑ i, x i * y i : PMF Bool) true).toReal = 0 := by
  obtain ⟨p, q, hp, hq, hconst⟩ := exists_minEntropy_bind_dotProduct_eq_pure S
  refine ⟨p, q, (le_minEntropy_iff p).mp hp.ge, (le_minEntropy_iff q).mp ?_, ?_⟩
  · rw [hq, Finset.card_compl, Fintype.card_fin, Nat.cast_sub (S.card_le_univ.trans_eq
      (Fintype.card_fin n))]
  · rw [do_eq_bind, hconst]
    simp

end ComplexityAbstracts.ChorGoldreichBridge
