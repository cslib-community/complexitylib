/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteSampleInformation.Payments
public import CslibFrontier.Probability.PeerPrediction.Quadratic

/-!
# Interoperability with the four-task QMI construction

The author's calculus uses matrices as iterated real function spaces, avoiding
norm-instance diamonds. The existing payment API uses `Matrix`. These bridges
identify their probability tables, dependence functionals and reported laws.
The author's `fdi` is the same quadratic mutual information used by the actual
four-task payment, rather than an alternative dependence functional.
-/

public section
namespace Cslib.FiniteSampleInformation
open GeneralAsymmetricC1
open Cslib.Probability.PeerPrediction

/-- The two APIs impose exactly the same probability-table conditions. -/
theorem simplex_iff_quadratic_isJoint {n m : ℕ} (U : Mat n m) :
    Simplex U ↔ Quadratic.IsJoint (Matrix.of U) := Iff.rfl

/-- The author's Frobenius dependence is the existing four-task QMI target. -/
theorem fdi_eq_qmi {n m : ℕ} (U : Mat n m) :
    FrobeniusDependence.fdi U = Quadratic.qmi (Matrix.of U) := rfl

/-- The taskwise channel actions are the existing reported-law construction. -/
theorem reports_eq_quadratic_reportedLaw {n m : ℕ}
    (T : Mat n n) (S : Mat m m) (U : Mat n m) :
    Matrix.of (T * bobReports S U) =
      Quadratic.reportedLaw (Matrix.of U) (Matrix.of T) (Matrix.of S) := by
  rw [Quadratic.reportedLaw_eq]
  ext i b
  simp only [Matrix.of_apply, mat_mul_apply, bobReports, swapAgents, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The expected payoff under the processed law equals the literal experiment:
first draw independent latent signal pairs, then randomize each report independently
using the corresponding agent's channel. No desired incentive inequality is assumed. -/
theorem memoryless_payoff_eq {n m d : ℕ} (M : Payment n m d)
    (T : Mat n n) (S : Mat m m) (U : Mat n m) :
    expectedPayment M (T * bobReports S U) =
      ∑ v : Fin d → Fin n × Fin m, (∏ t, U (v t).1 (v t).2) *
        ∑ w : Fin d → Fin n × Fin m, M w *
          ∏ t, (T (w t).1 (v t).1 * S (w t).2 (v t).2) := by
  have hq : (fun z : Fin n × Fin m => (T * bobReports S U) z.1 z.2) =
      (fun z => ∑ x : Fin n × Fin m, U x.1 x.2 * (T z.1 x.1 * S z.2 x.2)) := by
    funext z
    simp only [mat_mul_apply, bobReports, swapAgents, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    ring
  change Estimation.expectation _ d M = _
  rw [hq]
  exact Estimation.expectation_channel _ _ _ _

end Cslib.FiniteSampleInformation
