/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyIncomingPreparationBias
public import Complexity.Foundations.Probability.HierarchyJointAllocation

/-!
# The width obstruction to incoming PREP's coarse salary

These original results concern the sufficient envelope, not a lower bound on actual
PREP error. Fix HP, regularity/decoder constants, positive relative floor and structural
charge before geometry. At fixed positive terminal rate the coarse coefficient is
`c * P^2`, where `c = C^4 * (L / (f * scale))^4`. For every fixed positive `c`,
bounded-prime fields eventually exceed the fixed pilot/actual rank salary, even before
paying the negative child-budget loss. Increasing both request precisions does not
repair their ratio. No conclusion is made for `c = 0`.

The joint guard construction below keeps positive parent precision and the production
child budget; successful child execution and positive own-request accuracy remain
separate obligations. It does not replace the actual incoming input by residual zero,
change usage, alter completion steps or assert an estimator-error counterexample.

A concrete next bound is a fourth-moment sensitivity theorem for the actual incoming
column gate: average its rank perturbation over source/terminal masks before replacing
it by a full source-by-terminal maximum. The source-column rank and each terminal-row
rank in `correctionPrep` must be retained, and support must be proved for the actual
completed input, not borrowed from selected dense-bin preparation. The existing
`correction_preparation_stability_constants` is the pointwise entry seam; its
`correction_preparation_row_moment` consumer currently replaces both by a global maximum.

## Main results

* `preparation_envelope_unpaid`: the literal production allowance fails the coarse envelope.
* `exists_preparation_envelope_depth`: every positive fixed coefficient eventually fails.
* `exists_joint_preparation_envelope_obstruction`: the joint depth guards coexist with failure.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Cslib
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- A field threshold rejects only the sufficient envelope. The actual input's own
error can be strictly below its allowance, and actual PREP bias can be smaller still. -/
theorem preparation_envelope_unpaid (B : BudgetData HP P) (M : ℕ)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (c : ℝ)
    (hwidth : (2 : ℝ) ^ (4 * B.rankCharge * (if pilot then 40 else 4)) < c * (P : ℝ) ^ 2) :
    let q := {r with task := .row 0 (if pilot then .pilotInput i else .input i)}
    ¬ c * (P : ℝ) ^ 2 * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  dsimp only
  rw [show (c * (P : ℝ) ^ 2 * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M)
      {r with task := .row 0 (if pilot then .pilotInput i else .input i)})) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4) ↔ _ from
    B.preparation_bias_production_salary_iff M pilot i r hr (c * (P : ℝ) ^ 2)]
  apply not_le.mpr
  apply lt_of_le_of_lt _ hwidth
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hm : B.childBudget M ≤ M := Nat.sub_le _ _
  have hmr : (B.childBudget M : ℝ) ≤ M := by exact_mod_cast hm
  have hs : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hd : (4 * ((B.childBudget M : ℝ) - M)) / (16 * B.slack) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- The obstruction does not rely on an inactive input child. With slack one and
charge at least one, positive PREP precision implies positive precision at its literal
corresponding input child. This supplies neither success nor its accuracy. -/
theorem requestPrecision_preparation_input_pos (B : BudgetData HP P)
    (hslack : B.slack = 1) (hcharge : 1 ≤ B.rankCharge) (M : ℕ) (hM : 0 < M)
    (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hp : 0 < B.requestPrecision M r) :
    0 < B.requestPrecision (B.childBudget M)
      {r with task := .row 0 (if pilot then .pilotInput i else .input i)} := by
  have hm : B.childBudget M = M - 1 := by
    simp [childBudget, LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, hslack]
  have hcast : (B.childBudget M : ℝ) = (M : ℝ) - 1 := by
    rw [hm, Nat.cast_sub (by omega : 1 ≤ M)]; norm_num
  have hd := B.requestPrecision_preparation_input M (B.childBudget M) pilot i r hr
  dsimp only at hd
  rw [hcast, hslack] at hd
  cases pilot <;> norm_num at hd ⊢ <;> linarith

/-- No fixed positive coefficient can absorb growing fields into a fixed rank salary.
The deliberately elementary threshold works for every field above `2^n`, hence also
for the bounded primes in the joint family. -/
theorem exists_preparation_envelope_depth (c A : ℝ) (hc : 0 < c) (pilot : Bool) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ P : ℕ, 2 ^ n < P →
      (2 : ℝ) ^ (4 * A * (if pilot then 40 else 4)) < c * (P : ℝ) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max 1
    ((2 : ℝ) ^ (4 * A * (if pilot then 40 else 4)) / c))
  refine ⟨n₀, ?_⟩
  intro n hn P hP
  have hnp : n < P := (Nat.lt_two_pow_self).trans hP
  have hnr : (n₀ : ℝ) < P := by exact_mod_cast (lt_of_le_of_lt hn hnp)
  have hbig : (2 : ℝ) ^ (4 * A * (if pilot then 40 else 4)) / c < P :=
    (le_max_right _ _).trans_lt (hn₀.trans hnr)
  have hp : (1 : ℝ) < P := (le_max_left _ _).trans_lt (hn₀.trans hnr)
  have hsq : (P : ℝ) ≤ (P : ℝ) ^ 2 := by nlinarith
  have hpay : (2 : ℝ) ^ (4 * A * (if pilot then 40 else 4)) < c * P := by
    simpa only [mul_comm] using (div_lt_iff₀ hc).mp hbig
  exact hpay.trans_le (mul_le_mul_of_nonneg_left hsq hc.le)

/-- A representative fixed request supplies the joint scalar guards. The field is
then chosen at that depth. Any budget data at the chosen prime with the same slack,
charge and task/rates has the same precision, so it inherits these scalar guards.
This is guard feasibility only, with no claim of recursive execution or accuracy. -/
theorem exists_joint_preparation_envelope_obstruction
    (B : BudgetData HP P) (hslack : B.slack = 1)
    (A ks ka ku idMax : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (c : ℝ) (hc : 0 < c) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let M := 2 ^ N
      let n := M / 8 + 1
      ks ≤ n ∧ 2 * ka ≤ n ∧ ku ≤ n ∧ idMax < 2 ^ n ∧
      B.slack * (1 + 4 * (n + ka)) < M ∧ M ≤ 32 * B.slack * n ∧
      16 * (B.slack : ℝ) * (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M ∧
      0 < B.requestPrecision M r ∧
      ∃ Q, Q.Prime ∧ 2 ^ n < Q ∧ Q ≤ 2 ^ (n + 1) ∧
        (∃ H : Horizon Q, H.maxExponent = n ∧ H.maxIdentifier = idMax) ∧
        ∀ (D : BudgetData HP Q) (s : HierarchyTask.Request HP.k (Fin 3) (ZMod Q)),
          D.slack = B.slack → D.rankCharge = B.rankCharge →
          s.task = r.task → s.source.rate = r.source.rate →
          s.terminal.rate = r.terminal.rate →
          0 < D.requestPrecision M s ∧
          (let q := {s with task := .row 0 (if pilot then .pilotInput i else .input i)}
          ¬ c * (Q : ℝ) ^ 2 * ((2 : ℝ) ^ (-D.requestPrecision (D.childBudget M) q)) ^ 4 ≤
            ((2 : ℝ) ^ (-D.requestPrecision M s)) ^ 4) := by
  obtain ⟨N₁, hguards⟩ := exists_prefix_joint_depth_family A B hslack ks ka ku idMax r hs ht
  obtain ⟨n₀, hfail⟩ := exists_preparation_envelope_depth c B.rankCharge hc pilot
  refine ⟨max N₁ (8 * n₀), ?_⟩
  intro N hN
  have hg := hguards N ((le_max_left _ _).trans hN)
  have hlarge : 8 * n₀ ≤ N := (le_max_right _ _).trans hN
  have hpow := Nat.lt_two_pow_self (n := N)
  have hn : n₀ ≤ 2 ^ N / 8 + 1 := by omega
  obtain ⟨Q, hQ, hlo, hhi, H, hHn, hHi⟩ := exists_bounded_depth_prime
    (2 ^ N / 8 + 1) idMax hg.2.2.2.1
  refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1,
    hg.2.2.2.2.2.1, hg.2.2.2.2.2.2.1, hg.2.2.2.2.2.2.2,
    Q, hQ, hlo, hhi, ⟨H, hHn, hHi⟩, ?_⟩
  intro D s hDs hDc hst hss hsa
  have hp : D.requestPrecision (2 ^ N) s = B.requestPrecision (2 ^ N) r := by
    simp only [requestPrecision, LogSpaceEstimation.precision, hDs, hDc, hst, hss, hsa]
  refine ⟨hp.symm ▸ hg.2.2.2.2.2.2.2, ?_⟩
  apply D.preparation_envelope_unpaid (2 ^ N) pilot i s (hst.trans hr) c
  rw [hDc]
  exact hfail _ hn Q hlo

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
