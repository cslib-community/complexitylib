/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.MachineLearning.StatisticalQuery.Dimension
import Complexity.MachineLearning.StatisticalQuery.Parity

/-! Checks for the statistical query dimension and its characterization of weak learning: the
dimension of the empty class, of a singleton and of the identity and negation on a bit; the weak
learner, which learns the identity and negation on a bit exactly with tolerance `1/8`; and the
parities on `n` bits, whose dimension is at least `2 ^ n`, so that by the characterization they
are not weakly learnable from polynomially many statistical queries of inverse-polynomial
tolerance with inverse-polynomial advantage. -/

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

/-- The identity and the negation on a bit have dimension `2`. -/
theorem sqDim_idNot : sqDim (PMF.uniformOfFintype Bool) idNot = 2 := by
  classical
  refine le_antisymm ((sqDim_le_ncard _ _).trans_eq (Set.ncard_pair id_ne_not)) ?_
  have hcard : ({id, not} : Finset (Bool → Bool)).card = 2 := card_pair id_ne_not
  have h := le_sqDim (D := PMF.uniformOfFintype Bool) (C := idNot) (F := {id, not})
    (by simp [idNot]) (by
      rw [hcard, coe_pair]
      refine Set.pairwise_pair.2 fun _ => ⟨?_, ?_⟩
      · rw [corr_id_not]
        norm_num
      · rw [corr_comm, corr_id_not]
        norm_num)
  rwa [hcard] at h

/-- Under the uniform distribution on a bit, the error of a hypothesis is `0`, `1/2` or `1`, so an
error below `1/2` is `0`. -/
theorem disagreement_eq_zero_of_lt {c h : Bool → Bool}
    (hlt : disagreement (PMF.uniformOfFintype Bool) c h < 1 / 2) :
    disagreement (PMF.uniformOfFintype Bool) c h = 0 := by
  revert hlt
  simp only [disagreement, Fintype.sum_bool, PMF.uniformOfFintype_apply, Fintype.card_bool]
  split_ifs <;> norm_num

/-- The weak learner from the dimension makes at most two queries and learns the identity and
negation on a bit exactly with tolerance `1/8`: its error bound `1/2 - 1/6 + 1/8` is below
`1/2`. -/
theorem exists_learns_idNot :
    ∃ A : Algorithm Bool, A.IsQueryBounded 2 ∧
      Learns A (PMF.uniformOfFintype Bool) idNot (1 / 8) 0 := by
  obtain ⟨A, hq, -, hA⟩ := exists_learns_sqDim (PMF.uniformOfFintype Bool) idNot
  rw [sqDim_idNot] at hq hA
  refine ⟨A, hq, fun c hc h hh => (disagreement_eq_zero_of_lt ?_).le⟩
  have := hA (1 / 8) c hc h hh
  norm_num at this ⊢
  linarith

/-- The correlational learner for the list `[id, not]` learns the class exactly with tolerance
`1/8`: each concept has correlation `1 > 1/2` with itself. -/
example : Learns (corrLearner [id, not]) (PMF.uniformOfFintype Bool) idNot (1 / 8) 0 := by
  have h := corrLearner_learns (D := PMF.uniformOfFintype Bool) (C := idNot) (gs := [id, not])
    (γ := 1 / 2) (fun c hc => ⟨c, by rcases hc with rfl | rfl <;> simp, by
      rw [corr_self]
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
    simp only [corr_uniformOfFintype_parityOn, hST, ↓reduceIte]
    positivity

/-- `2 ^ n` is not polynomially bounded. -/
theorem not_polynomiallyBounded_two_pow : ¬ PolynomiallyBounded fun n => 2 ^ n := by
  rintro ⟨d, hd⟩
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ d / 2 ^ n < 1 :=
    (tendsto_pow_const_div_const_pow_of_one_lt d one_lt_two).eventually (gt_mem_nhds one_pos)
  obtain ⟨n, hn, hlt⟩ := (hd.and hev).exists
  have hle : (2 : ℝ) ^ n ≤ (n : ℝ) ^ d := by exact_mod_cast hn
  rw [div_lt_one (by positivity)] at hlt
  linarith

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
      sqDim (PMF.uniformOfFintype (Fin n → Bool)) (parities n) := (hT.out 3 1).1 h
  exact not_polynomiallyBounded_two_pow (hdim.mono_of_le two_pow_le_sqDim_parities)

end ComplexityTests.StatisticalQueryDimension
