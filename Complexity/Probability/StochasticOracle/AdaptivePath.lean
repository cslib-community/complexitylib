/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveSelection
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-!
# Infinite response law for adaptive selection

`responseMeasure` constructs the full-history response process used in
[Wang2027], Theorem 5 and Appendix A.5 (PDF pp. 12, 16), from finite conditional
response tables. Histories are newest first, as in `AdaptiveSelection`.
The trajectory coordinates are responses, including auxiliary bill information;
they are not independent progress indicators.

`responseMeasure_condDistrib` identifies the conditional next-response law given
all preceding responses. It is an almost-everywhere statement on the actual prefix
law, including zero-probability histories without conditioning on null events.
This construction alone does not establish termination or total-cost integrability.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.AdaptiveSelection
open MeasureTheory ProbabilityTheory Preorder

variable {Ω : Type*}

/-- Newest-first history after the first `n` responses of an infinite trajectory. -/
@[expose] def responseHistory (ω : ℕ → Ω) (n : ℕ) : List Ω :=
  (List.ofFn fun i : Fin n => ω i).reverse

/-- Decode all coordinates of a finite prefix into a newest-first history. -/
@[expose] def prefixHistory (n : ℕ) (x : (i : Finset.Iic n) → Ω) : List Ω :=
  (List.ofFn fun i : Fin (n + 1) => x ⟨i, by simpa using Nat.le_of_lt_succ i.isLt⟩).reverse

/-- The finite-prefix decoder agrees with the infinite-path observable. -/
theorem prefixHistory_restrict (ω : ℕ → Ω) (n : ℕ) :
    prefixHistory n (frestrictLe n ω) = responseHistory ω (n + 1) := rfl

/-- The next response is prepended, matching the finite execution convention. -/
theorem responseHistory_succ (ω : ℕ → Ω) (n : ℕ) :
    responseHistory ω (n + 1) = ω n :: responseHistory ω n := by
  simp only [responseHistory, List.ofFn_succ_last, List.reverse_append,
    List.reverse_singleton, Fin.val_last, Fin.val_castSucc, List.singleton_append]

variable [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

/-- The conditional response kernel reads the entire prefix, including auxiliary
response information. Discreteness makes every finite-history table measurable. -/
@[expose] def responseKernel
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → Ω) Ω where
  toFun x := (law (prefixHistory n x)).toPMF.toMeasure
  measurable' := measurable_of_finite _

instance responseKernel_isMarkovKernel
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    IsMarkovKernel (responseKernel law n) :=
  ⟨fun x => by
    change IsProbabilityMeasure (law (prefixHistory n x)).toPMF.toMeasure
    infer_instance⟩

/-- Actual infinite response law, with first response sampled from `law []` and
subsequent responses from the table at their full newest-first history. -/
@[expose] def responseMeasure
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) :
    Measure (ℕ → Ω) :=
  Kernel.trajMeasure (law []).toPMF.toMeasure (responseKernel law)

instance responseMeasure_isProbabilityMeasure
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) :
    IsProbabilityMeasure (responseMeasure law) := by
  unfold responseMeasure
  infer_instance

/-- Consistent finite truncations: the joint law of a prefix and the next
response is obtained by applying the specified full-history kernel to that prefix.
This is a measure identity, without positivity requirements on individual histories. -/
theorem responseMeasure_prefix_joint
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    (responseMeasure law).map (frestrictLe n) ⊗ₘ responseKernel law n =
      (responseMeasure law).map (fun ω => (frestrictLe n ω, ω (n + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

/-- The infinite process has the specified conditional response law, almost
surely under its actual finite-prefix law. No independence is assumed. -/
theorem responseMeasure_condDistrib [StandardBorelSpace Ω] [Nonempty Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ) (n : ℕ) :
    condDistrib (fun ω : ℕ → Ω => ω (n + 1)) (frestrictLe n)
        (responseMeasure law) =ᵐ[(responseMeasure law).map (frestrictLe n)]
      responseKernel law n :=
  Kernel.condDistrib_trajMeasure

end Cslib.Probability.StochasticOracle.AdaptiveSelection
