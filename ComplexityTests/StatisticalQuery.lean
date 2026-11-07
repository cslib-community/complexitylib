/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.MachineLearning.StatisticalQuery.LowerBound
import Complexity.MachineLearning.StatisticalQuery.Parity

/-! Checks for learning from statistical queries: a one-query learner that learns the two
constant concepts on a point exactly with tolerance `1/2`, the same learner failing with tolerance
`1`, and instances of the lower bounds for parities. -/

namespace ComplexityTests.StatisticalQuery

open Cslib Cslib.MachineLearning Cslib.MachineLearning.StatisticalQuery Cslib.Probability

/-! ### A learner for the constant concepts on a point -/

/-- The two constant concepts on a point. -/
def constants : PACLearning.ConceptClass Unit Bool := {fun _ => false, fun _ => true}

/-- The query reading the label as a sign. -/
noncomputable def signQuery : Query Unit where
  toFun _ y := BitString.signVal y
  abs_le_one' _ y := (BitString.abs_signVal y).le

/-- Ask for the expected sign of the label and return the constant it points to. (A learner is
built at the unfolded type `OracleComp (spec X) (X → Bool)` of `Algorithm X`, so that `>>=`
elaborates in the monad `OracleComp (spec X)`.) -/
noncomputable def signLearner : OracleComp (spec Unit) (Unit → Bool) :=
  OracleComp.query signQuery >>= fun a => pure fun _ => decide (a < 0)

theorem expect_signQuery (c : Unit → Bool) :
    expect (PMF.pure ()) c signQuery = BitString.signVal (c ()) := by
  simp [expect, signQuery]

theorem disagreement_pure (c h : Unit → Bool) :
    disagreement (PMF.pure ()) c h = if c () = h () then 0 else 1 := by
  simp [disagreement]

/-- The learner makes one query. -/
theorem signLearner_isQueryBounded : signLearner.IsQueryBounded 1 :=
  .liftBind signQuery _ 0 fun _ => .pure _ 0

/-- With tolerance `1/2` the learner learns the constant concepts exactly. -/
theorem signLearner_learns : Learns signLearner (PMF.pure ()) constants (1 / 2) 0 := by
  intro c hc h hh
  rw [signLearner, OracleComp.mem_supportWith_bind_iff] at hh
  obtain ⟨a, ha, hh⟩ := hh
  rw [OracleComp.supportWith_query] at ha
  rw [OracleComp.eq_of_mem_supportWith_pure hh]
  change |a - expect (PMF.pure ()) c signQuery| ≤ 1 / 2 at ha
  rw [expect_signQuery] at ha
  rw [disagreement_pure]
  rcases hc with rfl | rfl
  · have : ¬ a < 0 := by
      rw [BitString.signVal_false] at ha
      linarith [(abs_le.1 ha).1]
    simp [this]
  · have : a < 0 := by
      rw [BitString.signVal_true] at ha
      linarith [(abs_le.1 ha).2]
    simp [this]

/-- The learner is also correct against every answer function within tolerance `1/2`. -/
example : LearnsStateless signLearner (PMF.pure ()) constants (1 / 2) 0 :=
  signLearner_learns.learnsStateless

/-- With tolerance `1` the answer `0` is valid for both concepts, and the learner errs on the
constant `true`. -/
theorem not_signLearner_learnsStateless :
    ¬ LearnsStateless signLearner (PMF.pure ()) constants 1 0 := by
  intro h
  have hvalid : ∀ φ, |(fun _ : Query Unit => (0 : ℝ)) φ - expect (PMF.pure ()) (fun _ => true) φ|
      ≤ 1 := by
    intro φ
    simp only [expect, Fintype.univ_unit, Finset.sum_singleton, PMF.pure_apply, ite_true,
      ENNReal.toReal_one, one_mul, zero_sub, abs_neg]
    exact φ.abs_le_one () true
  have hdis := h (fun _ => true) (Or.inr rfl) _ hvalid
  have hrun : run signLearner (fun _ => 0) = fun _ => false := by
    funext x
    rw [run, signLearner, OracleComp.interpret_id_query_bind]
    simp only [lt_self_iff_false, decide_false]
    rfl
  rw [hrun, disagreement_pure] at hdis
  norm_num at hdis

/-! ### Parities -/

/-- No learner learns the parities on four bits exactly under the uniform distribution from one
query of tolerance `1/2`: that would need `2 ^ 4 ≤ 1 / (1/2) ^ 2 + 1`. -/
example (A : Algorithm (Fin 4 → Bool)) (hq : A.IsQueryBounded 1) :
    ¬ LearnsStateless A (PMF.uniformOfFintype (Fin 4 → Bool)) {f | ∃ S, f = parityOn S}
      (1 / 2) 0 := by
  intro hA
  have h := hA.two_pow_card_le_of_parityOn_mem hq (fun S => ⟨S, rfl⟩) (by norm_num) le_rfl
    (by norm_num)
  rw [Fintype.card_fin] at h
  norm_num at h

/-- Distinct parities are uncorrelated. -/
example : corr (PMF.uniformOfFintype (Fin 3 → Bool)) (parityOn {0}) (parityOn {0, 1}) = 0 := by
  rw [corr_uniformOfFintype_parityOn, ite_eq_right (by decide)]

/-- The statistical query dimension bound for the `2 ^ n` parities, which have pairwise correlation
`0 ≤ 1 / 2 ^ n`: exact learning from `q` queries of tolerance `τ` needs `2 ^ n τ ^ 2 - 1 ≤ 2 q`. -/
example (n : ℕ) (hn : 1 ≤ n) (A : Algorithm (Fin n → Bool)) (q : ℕ) (hq : A.IsQueryBounded q)
    (τ : ℝ) (hτ : 0 ≤ τ)
    (hA : LearnsStateless A (PMF.uniformOfFintype (Fin n → Bool)) {f | ∃ S, f = parityOn S} τ 0) :
    (2 : ℝ) ^ n * τ ^ 2 - 1 ≤ 2 * q := by
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    rw [Fintype.card_finset, Fintype.card_fin]
  have h := hA.card_mul_sq_sub_one_le_two_mul hq (f := fun S : Finset (Fin n) => parityOn S)
    (fun S => ⟨S, rfl⟩) (fun S T hST => by
      rw [corr_uniformOfFintype_parityOn, ite_eq_right hST]
      positivity)
    (by
      rw [hcard]
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right two_pos hn) hτ
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- The statistical query dimension bound with accuracy `τ` for the `2 ^ n` parities: learning them
with error `(1 - τ) / 2` from `q` queries of tolerance `τ` needs `2 ^ n τ ^ 2 - 1 ≤ 2 q + 1`. -/
example (n : ℕ) (A : Algorithm (Fin n → Bool)) (q : ℕ) (hq : A.IsQueryBounded q)
    (τ : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hA : LearnsStateless A (PMF.uniformOfFintype (Fin n → Bool)) {f | ∃ S, f = parityOn S} τ
      ((1 - τ) / 2)) :
    (2 : ℝ) ^ n * τ ^ 2 - 1 ≤ 2 * q + 1 := by
  have hcard : Fintype.card (Finset (Fin n)) = 2 ^ n := by
    rw [Fintype.card_finset, Fintype.card_fin]
  have h := hA.card_mul_sq_sub_one_le_two_mul_add_one hq
    (f := fun S : Finset (Fin n) => parityOn S) (fun S => ⟨S, rfl⟩) (fun S T hST => by
      rw [corr_uniformOfFintype_parityOn, ite_eq_right hST]
      positivity) hτ (by linarith) (by linarith)
  rw [hcard, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

end ComplexityTests.StatisticalQuery
