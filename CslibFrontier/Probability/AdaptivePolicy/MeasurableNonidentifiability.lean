/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Nonidentifiability with measurable contexts

[Aldridge2027], Proposition 5.2 (PDF p. 5), for arbitrary measurable context
spaces. The behavior policy is represented by its actual joint context/action
law `μ`. Its two marginals determine the open-loop joint law. Failure of overlap
on a rectangle means `μ (E ×ˢ {a}) = 0` while both marginal masses are positive.
For the paper's kernel model `D(dx) π(a|x)`, the hypothesis follows from
`π(a|x)=0` on `E`; no finite-context or disintegration assumption is needed.

Losses are deterministic binary losses, hence bounded and conditionally
independent of action sampling given context. Logs retain the entire context,
action and observed loss. Any logged propensity is a deterministic function of
these retained coordinates. Equal single-log laws give equal independent log
laws at every sample count, including zero.

## Main results

* `measurable_nonidentifiability`: two bounded instances with identical log laws
  for every sample count and different actual expected adaptivity costs.
-/

public section
noncomputable section
open MeasureTheory
open scoped ProbabilityTheory
namespace Cslib.Probability.AdaptivePolicy
variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]

/-- The joint law under the open-loop marginal, retaining the original context law. -/
def marginalProduct (μ : Measure (X × A)) : Measure (X × A) :=
  (μ.map Prod.fst).prod (μ.map Prod.snd)

/-- Actual bandit log law, retaining context, action and binary observed loss. -/
def measurableLogLaw (μ : Measure (X × A)) (loss : X × A → Bool) :
    Measure ((X × A) × Bool) := μ.map (fun z => (z, loss z))

/-- Independent repeated full logs. -/
def measurableSampleLaw (μ : Measure (X × A)) (loss : X × A → Bool) (T : ℕ) :
    Measure (Fin T → (X × A) × Bool) :=
  Measure.pi (fun _ => measurableLogLaw μ loss)

/-- Expected binary loss under the policy minus under its open-loop marginal. -/
def measurableGap (μ : Measure (X × A)) (loss : X × A → Bool) : ℝ :=
  μ.real {z | loss z = true} - (marginalProduct μ).real {z | loss z = true}

/-- The binary-event definition is the actual difference of expected costs. -/
theorem measurableGap_eq_integral (μ : Measure (X × A)) (loss : X × A → Bool)
    (hloss : Measurable loss) :
    measurableGap μ loss =
      (∫ z, (if loss z then 1 else 0 : ℝ) ∂μ) -
      ∫ z, (if loss z then 1 else 0 : ℝ) ∂(marginalProduct μ) := by
  have he : MeasurableSet {z | loss z = true} := hloss (measurableSet_singleton true)
  have hfun : (fun z => (if loss z then 1 else 0 : ℝ)) =
      {z | loss z = true}.indicator (fun _ => (1:ℝ)) := by
    funext z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [hfun]
  simp only [integral_indicator_const (1:ℝ) he, smul_eq_mul, mul_one]
  rfl

/-- General measurable-context Proposition 5.2, with the exact gap difference.
The rectangle is never observed under the policy but has positive open-loop mass. -/
theorem measurable_nonidentifiability (μ : Measure (X × A)) [IsProbabilityMeasure μ]
    (E : Set X) (a : A) (hE : MeasurableSet E) (ha : MeasurableSet ({a} : Set A))
    (hoverlap : μ (E ×ˢ {a}) = 0)
    (hcontext : 0 < (μ.map Prod.fst) E)
    (haction : 0 < (μ.map Prod.snd) {a}) :
    ∃ loss₀ loss₁ : X × A → Bool,
      Measurable loss₀ ∧ Measurable loss₁ ∧
      (∀ T, measurableSampleLaw μ loss₀ T = measurableSampleLaw μ loss₁ T) ∧
      measurableGap μ loss₁ - measurableGap μ loss₀ =
        -(μ.map Prod.fst).real E * (μ.map Prod.snd).real {a} ∧
      measurableGap μ loss₁ ≠ measurableGap μ loss₀ := by
  classical
  let B := E ×ˢ {a}
  let loss₀ : X × A → Bool := fun _ => false
  let loss₁ : X × A → Bool := fun z => if z ∈ B then true else false
  have hB : MeasurableSet B := hE.prod ha
  have hm : Measurable loss₁ := Measurable.ite hB measurable_const measurable_const
  have heq : loss₀ =ᵐ[μ] loss₁ := by
    filter_upwards [show ∀ᵐ z ∂μ, z ∉ B from (ae_iff.mpr (by simpa using hoverlap))] with z hz
    simp [loss₀, loss₁, hz]
  have hlog : measurableLogLaw μ loss₀ = measurableLogLaw μ loss₁ := by
    apply Measure.map_congr
    exact heq.mono fun z hz => by simp only [hz]
  have hgap : measurableGap μ loss₁ - measurableGap μ loss₀ =
      -(μ.map Prod.fst).real E * (μ.map Prod.snd).real {a} := by
    have hevent : {z | loss₁ z = true} = B := by ext z; simp [loss₁]
    have hzero : {z | loss₀ z = true} = ∅ := by simp [loss₀]
    rw [measurableGap, measurableGap, hevent, hzero]
    simp only [measureReal_def, B, hoverlap, ENNReal.toReal_zero, measure_empty, sub_zero,
      zero_sub, marginalProduct, Measure.prod_prod, ENNReal.toReal_mul, neg_mul]
  have hpos : 0 < (μ.map Prod.fst).real E * (μ.map Prod.snd).real {a} := by
    exact mul_pos (ENNReal.toReal_pos hcontext.ne' (measure_ne_top _ _))
      (ENNReal.toReal_pos haction.ne' (measure_ne_top _ _))
  refine ⟨loss₀, loss₁, measurable_const, hm, ?_, hgap, ?_⟩
  · intro T
    unfold measurableSampleLaw
    simp only [hlog]
  · intro h
    rw [h, sub_self] at hgap
    nlinarith

/-- The deterministic-policy consequence of Proposition 5.2: every measurable
finite-action policy that is not almost surely constant is unidentifiable. -/
theorem deterministic_nonidentifiability [Finite A] [MeasurableSingletonClass A]
    (D : Measure X) [IsProbabilityMeasure D] (f : X → A) (hf : Measurable f)
    (hnotconstant : ∀ a, ¬ ∀ᵐ x ∂D, f x = a) :
    ∃ loss₀ loss₁ : X × A → Bool,
      Measurable loss₀ ∧ Measurable loss₁ ∧
      (∀ T, measurableSampleLaw (D.map (fun x => (x, f x))) loss₀ T =
        measurableSampleLaw (D.map (fun x => (x, f x))) loss₁ T) ∧
      measurableGap (D.map (fun x => (x, f x))) loss₁ ≠
        measurableGap (D.map (fun x => (x, f x))) loss₀ := by
  classical
  have hcover : (⋃ a, f ⁻¹' ({a} : Set A)) = Set.univ := by ext x; simp
  obtain ⟨a, ha⟩ := exists_pos_measure_of_cover (μ := D) hcover (IsProbabilityMeasure.ne_zero D)
  let E : Set X := {x | f x ≠ a}
  have hE : MeasurableSet E := (hf (measurableSet_singleton a)).compl
  have hmass : 0 < D E := by
    by_contra h
    have hz : D E = 0 := le_antisymm (not_lt.mp h) (zero_le)
    exact hnotconstant a (ae_iff.mpr hz)
  let μ := D.map (fun x => (x, f x))
  have hgraph : Measurable (fun x => (x, f x)) := measurable_id.prodMk hf
  have hfst : μ.map Prod.fst = D := by
    rw [Measure.map_map measurable_fst hgraph]
    exact Measure.map_id
  have hsnd : μ.map Prod.snd = D.map f := by
    rw [Measure.map_map measurable_snd hgraph]
    rfl
  have hoverlap : μ (E ×ˢ {a}) = 0 := by
    rw [Measure.map_apply hgraph (hE.prod (measurableSet_singleton a))]
    have hempty : (fun x => (x, f x)) ⁻¹' (E ×ˢ {a}) = ∅ := by
      ext x; simp [E]
    rw [hempty, measure_empty]
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hgraph.aemeasurable).mpr
    inferInstance
  obtain ⟨l₀, l₁, hl₀, hl₁, hlaw, _, hgap⟩ := measurable_nonidentifiability μ E a hE
    (measurableSet_singleton a) hoverlap (by rw [hfst]; exact hmass)
    (by rw [hsnd, Measure.map_apply hf (measurableSet_singleton a)]; exact ha)
  exact ⟨l₀, l₁, hl₀, hl₁, hlaw, hgap⟩

/-- Proposition 5.2 in the paper's context-distribution/Markov-kernel model.
The zero probability of the unobserved rectangle is derived from the policy. -/
theorem kernel_nonidentifiability (D : Measure X) [IsProbabilityMeasure D]
    (π : ProbabilityTheory.Kernel X A) [ProbabilityTheory.IsMarkovKernel π]
    (E : Set X) (a : A) (hE : MeasurableSet E) (ha : MeasurableSet ({a} : Set A))
    (hoverlap : ∀ x ∈ E, π x {a} = 0) (hcontext : 0 < D E)
    (haction : 0 < ((D ⊗ₘ π).map Prod.snd) {a}) :
    ∃ loss₀ loss₁ : X × A → Bool,
      Measurable loss₀ ∧ Measurable loss₁ ∧
      (∀ T, measurableSampleLaw (D ⊗ₘ π) loss₀ T =
        measurableSampleLaw (D ⊗ₘ π) loss₁ T) ∧
      measurableGap (D ⊗ₘ π) loss₁ - measurableGap (D ⊗ₘ π) loss₀ =
        -D.real E * ((D ⊗ₘ π).map Prod.snd).real {a} ∧
      measurableGap (D ⊗ₘ π) loss₁ ≠ measurableGap (D ⊗ₘ π) loss₀ := by
  have hz : (D ⊗ₘ π) (E ×ˢ {a}) = 0 := by
    rw [Measure.compProd_apply_prod hE ha]
    exact setLIntegral_eq_zero hE hoverlap
  have hfst : (D ⊗ₘ π).map Prod.fst = D := Measure.fst_compProd D π
  have h := measurable_nonidentifiability (D ⊗ₘ π) E a hE ha hz
    (by rw [hfst]; exact hcontext) haction
  simpa only [hfst] using h

end Cslib.Probability.AdaptivePolicy
