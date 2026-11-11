/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF.ObservedProcess
public import CslibFrontier.Probability.PMF.ToMeasure
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Tactic

/-!
# Infinite trajectories of a discrete PMF transition

The Ionescu--Tulcea construction is applied to the actual hidden-state PMF
transition. States need not be finite or countable. Their measurable structure
is discrete; the infinite trajectory has the product sigma algebra. This is not
a claim about arbitrary nonatomic state kernels.

## Main definitions

* `transitionKernel`, `trajectory`: the concrete transition and infinite path measure.

## Main results

* `trajectory_prefix_joint`: the actual joint past/next-state transition law.
* `lintegral_coordinate`: every coordinate has the original finite-state-law expectation.
* `ae_step`: measurable supported transition properties hold along the actual path.
-/

public section
noncomputable section
namespace Cslib.Probability.ObservedProcess
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal
variable {S : Type} [MeasurableSpace S] [DiscreteMeasurableSpace S]

/-- The original PMF transition, made into a kernel on the discrete state space. -/
@[expose] def transitionKernel (step : S → PMF S) : Kernel S S where
  toFun s := (step s).toMeasure
  measurable' := Measurable.of_discrete

instance transitionKernel_isMarkovKernel (step : S → PMF S) :
    IsMarkovKernel (transitionKernel step) := ⟨fun s => by
      change IsProbabilityMeasure (step s).toMeasure
      infer_instance⟩

/-- The next state depends on the last full hidden state, which may itself retain
an unbounded history. No finite observation approximation is used. -/
@[expose] def trajectoryKernel (step : S → PMF S) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → S) S :=
  (transitionKernel step).comap (fun x => x ⟨n, by simp⟩) (by fun_prop)

instance trajectoryKernel_isMarkovKernel (step : S → PMF S) (n : ℕ) :
    IsMarkovKernel (trajectoryKernel step n) := by unfold trajectoryKernel; infer_instance

/-- Actual infinite execution from the original initial state. -/
@[expose] def trajectory (step : S → PMF S) (start : S) : Measure (ℕ → S) :=
  Kernel.trajMeasure (Measure.dirac start) (trajectoryKernel step)

instance trajectory_isProbabilityMeasure (step : S → PMF S) (start : S) :
    IsProbabilityMeasure (trajectory step start) := by unfold trajectory; infer_instance

/-- The actual joint prefix/next-state law is obtained by applying the original
transition kernel after the entire retained prefix, with all correlations intact. -/
theorem trajectory_prefix_joint (step : S → PMF S) (start : S) (n : ℕ) :
    (trajectory step start).map (frestrictLe n) ⊗ₘ trajectoryKernel step n =
      (trajectory step start).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

private theorem trajectory_prefix_zero (step : S → PMF S) (start : S) :
    (trajectory step start).map (frestrictLe 0) =
      (Measure.dirac start).map (MeasurableEquiv.piUnique _).symm := by
  rw [trajectory, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]

/-- Every nonnegative coordinate observable has exactly the finite native
transition-law expectation, with no integrability premise. -/
theorem lintegral_coordinate (step : S → PMF S) (start : S) (n : ℕ) (f : S → ℝ≥0∞) :
    (∫⁻ ω, f (ω n) ∂trajectory step start) = ∑' s, stateLaw step n start s * f s := by
  induction n generalizing f with
  | zero =>
    have hf : Measurable (fun x : (i : Finset.Iic 0) → S => f (x ⟨0, by simp⟩)) :=
      Measurable.of_discrete.comp (measurable_pi_apply _)
    have he := lintegral_map (μ := trajectory step start) hf (measurable_frestrictLe 0)
    rw [trajectory_prefix_zero, lintegral_map hf (by fun_prop)] at he
    simpa [stateLaw] using he.symm
  | succ n ih =>
    have hj := trajectory_prefix_joint step start n
    have hprod : Measurable (fun x : ((i : Finset.Iic n) → S) × S => f x.2) :=
      Measurable.of_discrete.comp measurable_snd
    have he := lintegral_map (μ := trajectory step start) hprod
      (by fun_prop : Measurable (fun ω : ℕ → S => (frestrictLe n ω, ω (n + 1))))
    rw [← hj, Measure.lintegral_compProd hprod] at he
    have hkernel (x : (i : Finset.Iic n) → S) :
        (∫⁻ y, f y ∂trajectoryKernel step n x) =
          ∑' y, step (x ⟨n, by simp⟩) y * f y :=
      PMF.lintegral_toMeasure _ Measurable.of_discrete
    simp_rw [hkernel] at he
    have hlast : Measurable (fun x : (i : Finset.Iic n) → S =>
        ∑' y, step (x ⟨n, by simp⟩) y * f y) :=
      (show Measurable (fun s : S => ∑' y, step s y * f y) from
        Measurable.of_discrete).comp (measurable_pi_apply (⟨n, by simp⟩ : Finset.Iic n))
    rw [lintegral_map hlast (measurable_frestrictLe n)] at he
    rw [he.symm]
    simp only [frestrictLe_apply]
    rw [ih (fun s => ∑' y, step s y * f y)]
    exact (PMF.tsum_bind_mul _ _ _).symm

/-- Every coordinate has the original finite hidden-state PMF law. -/
theorem map_coordinate (step : S → PMF S) (start : S) (n : ℕ) :
    (trajectory step start).map (fun ω => ω n) = (stateLaw step n start).toMeasure := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_pi_apply n), lintegral_coordinate,
    PMF.lintegral_toMeasure _ hf]

/-- A measurable relation supported by every actual transition holds at each
path step. No finite-state bound or supplied path representation is needed. -/
theorem ae_step (step : S → PMF S) (start : S) (n : ℕ) (R : S → S → Prop)
    (hR : MeasurableSet {p : S × S | R p.1 p.2})
    (H : ∀ s next, next ∈ (step s).support → R s next) :
    ∀ᵐ ω ∂trajectory step start, R (ω n) (ω (n + 1)) := by
  have hp : MeasurableSet {p : ((i : Finset.Iic n) → S) × S |
      R (p.1 ⟨n, by simp⟩) p.2} := by
    exact hR.preimage (by fun_prop : Measurable
      (fun p : ((i : Finset.Iic n) → S) × S => (p.1 ⟨n, by simp⟩, p.2)))
  have h : ∀ᵐ p ∂(trajectory step start).map (frestrictLe n) ⊗ₘ trajectoryKernel step n,
      R (p.1 ⟨n, by simp⟩) p.2 := by
    apply (Measure.ae_compProd_iff hp).mpr
    apply Filter.Eventually.of_forall
    intro x
    change ∀ᵐ y ∂(step (x ⟨n, by simp⟩)).toMeasure, R (x ⟨n, by simp⟩) y
    rw [ae_iff]
    apply (PMF.toMeasure_apply_eq_zero_iff _ MeasurableSet.of_discrete).mpr
    exact Set.disjoint_left.mpr (fun y hy hn => hn (H _ y hy))
  have hj := trajectory_prefix_joint step start n
  rw [hj] at h
  exact (ae_map_iff (by fun_prop) hp).mp h

end Cslib.Probability.ObservedProcess
