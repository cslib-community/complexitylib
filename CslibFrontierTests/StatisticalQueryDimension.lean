/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.MachineLearning.StatisticalQuery.Dimension
import CslibFrontier.MachineLearning.StatisticalQuery.Parity
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-! Checks for the statistical query dimension and its characterization of weak learning: the
dimension of the empty class, of a singleton and of the identity and negation on a bit, which
separates the absolute and one-sided dimensions (`1` and `2`); the weak learner, which learns the
identity and negation on a bit exactly with one query of tolerance `1/8`, returning the negation
of the queried concept on a negative answer; and the parities on `n` bits, whose dimension is at
least `2 ^ n`, so that by the characterization they are not weakly learnable from polynomially
many statistical queries of inverse-polynomial tolerance with inverse-polynomial advantage. -/

namespace ComplexityTests.StatisticalQueryDimension

open Cslib Cslib.MachineLearning Cslib.MachineLearning.StatisticalQuery Cslib.Probability
open Filter Finset

/-! ### Edge cases -/

/-- The empty class has dimension `0`. -/
example (D : PMF Bool) : sqDim D (∅ : PACLearning.ConceptClass Bool Bool) = 0 := by simp

/-- A single concept has dimension `1`. -/
theorem sqDim_singleton {X : Type} [Fintype X] (D : PMF X) (c : X → Bool) : sqDim D {c} = 1 :=
  le_antisymm ((sqDim_le_ncard D {c}).trans_eq (Set.ncard_singleton c)) (one_le_sqDim ⟨c, rfl⟩)

/-! ### The identity and negation on a bit -/

/-- The identity and the negation on a bit. -/
def idNot : PACLearning.ConceptClass Bool Bool := {id, not}

theorem id_ne_not : (id : Bool → Bool) ≠ not := fun h => by simpa using congrFun h true

/-- The identity and the negation are perfectly anticorrelated. -/
theorem corr_id_not : corr (PMF.uniformOfFintype Bool) id not = -1 := by
  simp only [corr, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool, id,
    Bool.not_true, Bool.not_false, BitString.signVal_true, BitString.signVal_false]
  norm_num

/-- The identity and the negation on a bit have dimension `1`: they are perfectly anticorrelated,
so no two of them have correlation of absolute value at most `1/2`. -/
theorem sqDim_idNot : sqDim (PMF.uniformOfFintype Bool) idNot = 1 := by
  classical
  refine le_antisymm ?_ (one_le_sqDim ⟨id, by simp [idNot]⟩)
  by_contra hlt
  push Not at hlt
  obtain ⟨F, hFC, hF, hpair⟩ := exists_finset_card_eq_sqDim (PMF.uniformOfFintype Bool) idNot
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by rw [hF]; exact hlt)
  have h : |corr (PMF.uniformOfFintype Bool) a b| ≤
      1 / (sqDim (PMF.uniformOfFintype Bool) idNot : ℝ) := hpair ha hb hab
  have hd : (2 : ℝ) ≤ sqDim (PMF.uniformOfFintype Bool) idNot := by exact_mod_cast hlt
  have habs : |corr (PMF.uniformOfFintype Bool) a b| = 1 := by
    rcases hFC ha with rfl | rfl <;> rcases hFC hb with rfl | rfl
    · exact absurd rfl hab
    · rw [corr_id_not, abs_neg, abs_one]
    · rw [corr_comm, corr_id_not, abs_neg, abs_one]
    · exact absurd rfl hab
  rw [habs] at h
  have : (1 : ℝ) / sqDim (PMF.uniformOfFintype Bool) idNot ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  linarith

/-- The identity and the negation on a bit have one-sided dimension `2`: their correlation `-1`
is at most `1/2`. -/
theorem sqDimOneSided_idNot : sqDimOneSided (PMF.uniformOfFintype Bool) idNot = 2 := by
  classical
  refine le_antisymm ((sqDimOneSided_le_ncard _ _).trans_eq (Set.ncard_pair id_ne_not)) ?_
  have hcard : ({id, not} : Finset (Bool → Bool)).card = 2 := card_pair id_ne_not
  have h := le_sqDimOneSided (D := PMF.uniformOfFintype Bool) (C := idNot) (F := {id, not})
    (by simp [idNot]) (by
      rw [hcard, coe_pair]
      refine Set.pairwise_pair.2 fun _ => ⟨?_, ?_⟩
      · rw [corr_id_not]
        norm_num
      · rw [corr_comm, corr_id_not]
        norm_num)
  rwa [hcard] at h

/-- The absolute and one-sided dimensions differ. -/
example :
    sqDim (PMF.uniformOfFintype Bool) idNot < sqDimOneSided (PMF.uniformOfFintype Bool) idNot := by
  rw [sqDim_idNot, sqDimOneSided_idNot]
  norm_num

/-- Under the uniform distribution on a bit, the error of a hypothesis is `0`, `1/2` or `1`, so an
error below `1/2` is `0`. -/
theorem disagreement_eq_zero_of_lt {c h : Bool → Bool}
    (hlt : disagreement (PMF.uniformOfFintype Bool) c h < 1 / 2) :
    disagreement (PMF.uniformOfFintype Bool) c h = 0 := by
  revert hlt
  simp only [disagreement, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  split_ifs <;> norm_num

/-- The weak learner from the dimension makes at most one query and learns the identity and
negation on a bit exactly with tolerance `1/8`: its error bound `1/2 - 1/4 + 1/8` is below
`1/2`. -/
theorem exists_learns_idNot :
    ∃ A : Algorithm Bool, A.IsQueryBounded 1 ∧
      Learns A (PMF.uniformOfFintype Bool) idNot (1 / 8) 0 := by
  obtain ⟨A, hq, -, hA⟩ := exists_learns_sqDim (PMF.uniformOfFintype Bool) idNot
  rw [sqDim_idNot] at hq hA
  refine ⟨A, hq, fun c hc h hh => (disagreement_eq_zero_of_lt ?_).le⟩
  have := hA (1 / 8) c hc h hh
  norm_num at this ⊢
  linarith

/-- The correlational learner for the single concept `id` learns the identity and its negation
exactly with tolerance `1/8`: both have correlation of absolute value `1` with `id`, and on a
negative answer the learner returns the negation of `id`. -/
example : Learns (corrLearner [id]) (PMF.uniformOfFintype Bool) idNot (1 / 8) 0 := by
  have h := learns_corrLearner (D := PMF.uniformOfFintype Bool) (C := idNot) (gs := [id])
    (γ := 1 / 2) (fun c hc => ⟨id, List.mem_singleton_self _, by
      rcases hc with rfl | rfl
      · rw [corr_self, abs_one]
        norm_num
      · rw [corr_comm, corr_id_not, abs_neg, abs_one]
        norm_num⟩) (1 / 8)
  refine fun c hc g hg => (disagreement_eq_zero_of_lt ?_).le
  have := h c hc g hg
  norm_num at this ⊢
  linarith

/-! ### Parities -/

/-- The parities on `n` bits. -/
def parities (n : ℕ) : PACLearning.ConceptClass (Fin n → Bool) Bool :=
  Set.range fun S : Finset (Fin n) => parityOn S

/-- The `2 ^ n` parities on `n` bits are pairwise uncorrelated under the uniform distribution, so
their dimension is at least `2 ^ n`. -/
theorem two_pow_le_sqDim_parities (n : ℕ) :
    2 ^ n ≤ sqDim (PMF.uniformOfFintype (Fin n → Bool)) (parities n) := by
  classical
  have hinj : Function.Injective fun S : Finset (Fin n) => parityOn S := by
    intro S T hST
    by_contra hne
    have h := corr_uniformOfFintype_parityOn S T
    rw [show parityOn S = parityOn T from hST, corr_self] at h
    simp only [hne, ↓reduceIte, one_ne_zero] at h
  set F : Finset ((Fin n → Bool) → Bool) := univ.image fun S : Finset (Fin n) => parityOn S
  have hcard : F.card = 2 ^ n := by
    rw [card_image_of_injective _ hinj, card_univ, Fintype.card_finset, Fintype.card_fin]
  rw [← hcard]
  refine le_sqDim (fun f hf => ?_) fun f hf g hg hfg => ?_
  · obtain ⟨S, -, rfl⟩ := mem_image.1 hf
    exact ⟨S, rfl⟩
  · obtain ⟨S, -, rfl⟩ := mem_image.1 hf
    obtain ⟨T, -, rfl⟩ := mem_image.1 hg
    have hST : S ≠ T := fun h => hfg (by rw [h])
    simp only [corr_uniformOfFintype_parityOn, hST, ↓reduceIte, abs_zero]
    positivity

/-- `2 ^ n` is not polynomially bounded. -/
theorem not_polynomiallyBounded_two_pow : ¬ PolynomiallyBounded fun n => 2 ^ n := fun h => by
  obtain ⟨n, hn⟩ := h.eventually_lt_two_pow.exists
  exact lt_irrefl _ hn

/-- **Parities are not weakly learnable from statistical queries**, through the characterization:
there are no polynomially bounded `q` and `p` with learners for the parities on `n` bits under the
uniform distribution making at most `q n` queries of tolerance `1 / (p n + 1)` with error
`1/2 - 1 / (p n + 1)`, even against fixed answer functions. -/
theorem not_weakly_learnable_parities :
    ¬ ∃ q p : ℕ → ℕ, PolynomiallyBounded q ∧ PolynomiallyBounded p ∧ ∀ n,
      ∃ A : Algorithm (Fin n → Bool), A.IsQueryBounded (q n) ∧
        LearnsStateless A (PMF.uniformOfFintype (Fin n → Bool)) (parities n)
          (1 / ((p n : ℝ) + 1)) (1 / 2 - 1 / ((p n : ℝ) + 1)) := by
  have hT := tfae_polynomiallyBounded_sqDim (fun n => PMF.uniformOfFintype (Fin n → Bool)) parities
  intro h
  have hdim : PolynomiallyBounded fun n =>
      sqDim (PMF.uniformOfFintype (Fin n → Bool)) (parities n) := (hT.out 4 1).1 h
  exact not_polynomiallyBounded_two_pow (hdim.mono_of_le two_pow_le_sqDim_parities)

end ComplexityTests.StatisticalQueryDimension
