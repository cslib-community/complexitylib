/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.Entropy
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Complexity.Probability.PMF.Event
import Mathlib.Analysis.Convex.Jensen

/-!
# Fano's inequality

**Fano's inequality** bounds the entropy left in a hidden value by the probability that it is
guessed wrongly [Cover and Thomas, Theorem 2.10.1 and the remark following it][CoverThomas2006].
If an estimator `g` recovers a value `X : α` from an observation `Y` except with probability
`Pe = Pr[g Y ≠ X]`, then `H(X | Y) ≤ h₂(Pe) + Pe log₂ (|α| - 1)`, where
`h₂(e) = Real.binEntropy e / Real.log 2` is the binary entropy in bits. This is the sharper
`|α| - 1` form of the remark, for deterministic estimators `g Y` with values in `α`; it implies the
theorem's `Pe log₂ |α|` form for them. Joint laws list the observation first, as for
`Cslib.Probability.PMF.conditionalEntropy`.

The proof averages the unconditional inequality `H(q) ≤ h₂(1 - q a) + (1 - q a) log₂ (|α| - 1)`,
for one law `q` and one guess `a`, over the conditional laws of `X` given `Y = y`. The unconditional
inequality is concavity of `x ↦ -x log x` on the outcomes other than `a`; averaging uses concavity
of `Real.binEntropy` (Jensen's inequality). This is not the textbook proof, which expands
`H(E, X | Y)` for the error indicator `E` by the chain rule in two ways; the statement is the same.

## Main results

* `Cslib.Probability.PMF.entropy_bool`: the entropy of a bit is its binary entropy.
* `Cslib.Probability.PMF.entropy_le_binEntropy_add_mul_logb`: Fano's inequality without side
  information.
* `Cslib.Probability.PMF.conditionalEntropy_le_binEntropy_add_mul_logb`: Fano's inequality for a
  joint law and an estimator.
* `Cslib.Probability.PMF.conditionalEntropy_map_le_binEntropy_add_mul_logb`: the same for random
  variables `X, Y` on a common probability space.
* `Cslib.Probability.PMF.conditionalEntropy_le_one_add_mul_logb`: the weak form
  `H(X | Y) ≤ 1 + Pe log₂ |α|`.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], 2nd ed.,
  Section 2.10.
-/

public section

namespace Cslib.Probability.PMF

variable {α β Ω : Type*}

/-- The entropy of a bit is the binary entropy, in bits, of its probability of being `true`. -/
theorem entropy_bool (q : PMF Bool) :
    entropy q = Real.binEntropy (q true).toReal / Real.log 2 := by
  have h : (q false).toReal = 1 - (q true).toReal := by
    have := sum_toReal q
    rw [Fintype.sum_bool] at this
    linarith
  rw [entropy_eq_sum, Fintype.sum_bool, h, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]

/-- **Fano's inequality** without side information: if the guess `a` misses a sample of `q` with
probability `e = 1 - q a`, then `H(q) ≤ h₂(e) + e log₂ (|α| - 1)`. -/
theorem entropy_le_binEntropy_add_mul_logb [Fintype α] (q : PMF α) (a : α) :
    entropy q ≤ Real.binEntropy (1 - (q a).toReal) / Real.log 2 +
      (1 - (q a).toReal) * Real.logb 2 (Fintype.card α - 1) := by
  classical
  set e : ℝ := 1 - (q a).toReal with he
  have hsum : ∑ x ∈ Finset.univ.erase a, (q x).toReal = e := by
    have := sum_toReal q
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at this
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- `S` is the contribution of the outcomes other than `a` to `H(q) log 2`
  set S : ℝ := ∑ x ∈ Finset.univ.erase a, Real.negMulLog (q x).toReal with hS
  have hcard : (Finset.univ.erase a).card = Fintype.card α - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
  have hK : 1 ≤ Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  have hSle : S ≤ Real.negMulLog e + e * Real.log (Fintype.card α - 1) := by
    rcases Nat.eq_or_lt_of_le hK with hK1 | hK1
    · -- a single outcome: nothing else contributes
      have hempty : Finset.univ.erase a = ∅ := by
        rw [← Finset.card_eq_zero, hcard, ← hK1]
      have he0 : e = 0 := by rw [← hsum, hempty, Finset.sum_empty]
      rw [hS, hempty, Finset.sum_empty, he0, Real.negMulLog_zero, zero_mul, add_zero]
    · -- Jensen's inequality for `negMulLog` on the `c = |α| - 1` other outcomes
      set c : ℝ := ((Fintype.card α - 1 : ℕ) : ℝ) with hc
      have hcpos : 0 < c := by
        rw [hc]
        exact_mod_cast Nat.sub_pos_of_lt hK1
      have hc' : (Fintype.card α : ℝ) - 1 = c := by
        rw [hc, Nat.cast_sub hK, Nat.cast_one]
      have hJ := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ.erase a)
        (w := fun _ => c⁻¹) (p := fun x => (q x).toReal) (fun _ _ => by positivity)
        (by rw [Finset.sum_const, hcard, nsmul_eq_mul, ← hc, mul_inv_cancel₀ hcpos.ne'])
        (fun _ _ => Set.mem_Ici.mpr ENNReal.toReal_nonneg)
      simp only [smul_eq_mul, ← Finset.mul_sum, hsum] at hJ
      rw [Real.negMulLog_mul, Real.negMulLog, Real.log_inv] at hJ
      rw [hc']
      have := mul_le_mul_of_nonneg_left hJ hcpos.le
      rw [← hS] at this
      have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hcpos.ne'
      calc S = c * (c⁻¹ * S) := by rw [← mul_assoc, hcc, one_mul]
        _ ≤ c * (e * (-c⁻¹ * -Real.log c) + c⁻¹ * Real.negMulLog e) := this
        _ = e * Real.log c * (c * c⁻¹) + Real.negMulLog e * (c * c⁻¹) := by ring
        _ = Real.negMulLog e + e * Real.log c := by rw [hcc]; ring
  have h1e : 1 - e = (q a).toReal := by rw [he]; ring
  rw [entropy_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← hS,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, h1e, Real.logb, mul_div_assoc',
    ← add_div (Real.negMulLog e + Real.negMulLog (q a).toReal)]
  exact div_le_div_of_nonneg_right (by linarith) hlog.le

/-- **Fano's inequality** [Cover and Thomas, Theorem 2.10.1 and the remark following
it][CoverThomas2006]: for a joint law of an observation `Y : β` and a hidden value `X : α`, listed
observation first, and an estimator `g : β → α` erring with probability `Pe = Pr[g Y ≠ X]`,
`H(X | Y) ≤ h₂(Pe) + Pe log₂ (|α| - 1)`. This is the sharper `|α| - 1` form, for deterministic
estimators with values in `α`. -/
theorem conditionalEntropy_le_binEntropy_add_mul_logb [Finite β] [Fintype α]
    (joint : PMF (β × α)) (g : β → α) :
    conditionalEntropy joint ≤
      Real.binEntropy (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal / Real.log 2 +
        (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal * Real.logb 2 (Fintype.card α - 1) := by
  classical
  let := Fintype.ofFinite β
  set Pe := (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal with hPe
  set w : β → ℝ := fun y => ((joint.map Prod.fst) y).toReal with hw
  set ey : β → ℝ := fun y => 1 - (conditionalSnd joint y (g y)).toReal with hey
  have hw0 : ∀ y, 0 ≤ w y := fun y => ENNReal.toReal_nonneg
  have hw1 : ∑ y, w y = 1 := sum_toReal _
  have hey01 : ∀ y, ey y ∈ Set.Icc (0 : ℝ) 1 := fun y =>
    ⟨sub_nonneg.mpr (ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using (conditionalSnd joint y).coe_le_one (g y))),
      sub_le_self _ ENNReal.toReal_nonneg⟩
  -- the error probability is the average of the conditional error probabilities
  have hPe' : Pe = ∑ y, w y * ey y := by
    rw [hPe, toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hrow : ∀ x, (joint (y, x)).toReal = w y * (conditionalSnd joint y x).toReal := by
      intro x
      rw [hw, ← ENNReal.toReal_mul, marginal_mul_conditionalSnd]
    have hsumc : ∑ x, (conditionalSnd joint y x).toReal = 1 := sum_toReal _
    simp only [Set.mem_ofPred_eq, hrow, hey]
    have hf : Finset.univ.filter (fun x => g y ≠ x) = Finset.univ.erase (g y) := by
      ext x
      simp [eq_comm]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hf, ← Finset.mul_sum]
    have h2 := Finset.add_sum_erase Finset.univ (fun x => (conditionalSnd joint y x).toReal)
      (Finset.mem_univ (g y))
    rw [hsumc] at h2
    have h3 : ∑ x ∈ Finset.univ.erase (g y), (conditionalSnd joint y x).toReal =
        1 - (conditionalSnd joint y (g y)).toReal := by linarith
    rw [h3]
  rw [conditionalEntropy_eq_sum]
  calc ∑ y, w y * entropy (conditionalSnd joint y)
      ≤ ∑ y, w y * (Real.binEntropy (ey y) / Real.log 2 +
          ey y * Real.logb 2 (Fintype.card α - 1)) :=
        Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
          (entropy_le_binEntropy_add_mul_logb _ (g y)) (hw0 y)
    _ = (∑ y, w y * Real.binEntropy (ey y)) / Real.log 2 +
          Pe * Real.logb 2 (Fintype.card α - 1) := by
        rw [hPe', Finset.sum_mul, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun y _ => ?_
        ring
    _ ≤ Real.binEntropy Pe / Real.log 2 + Pe * Real.logb 2 (Fintype.card α - 1) := by
        gcongr
        have hJ := Real.strictConcave_binEntropy.concaveOn.le_map_sum (t := Finset.univ)
          (w := w) (p := ey) (fun y _ => hw0 y) hw1 (fun y _ => hey01 y)
        simpa only [smul_eq_mul, ← hPe'] using hJ

/-- **Fano's inequality** for random variables `X : Ω → α` and `Y : Ω → β` on a probability space
`ν`, with the estimate `g ∘ Y` of `X`: `H(X | Y) ≤ h₂(Pe) + Pe log₂ (|α| - 1)`, where
`Pe = Pr[g (Y ω) ≠ X ω]`. -/
theorem conditionalEntropy_map_le_binEntropy_add_mul_logb [Finite β] [Fintype α] (ν : PMF Ω)
    (X : Ω → α) (Y : Ω → β) (g : β → α) :
    conditionalEntropy (ν.map fun ω => (Y ω, X ω)) ≤
      Real.binEntropy (ν.toOuterMeasure {ω | g (Y ω) ≠ X ω}).toReal / Real.log 2 +
        (ν.toOuterMeasure {ω | g (Y ω) ≠ X ω}).toReal * Real.logb 2 (Fintype.card α - 1) := by
  have h := conditionalEntropy_le_binEntropy_add_mul_logb (ν.map fun ω => (Y ω, X ω)) g
  rwa [PMF.toOuterMeasure_map_apply] at h

/-- **Fano's inequality**, weak form: `H(X | Y) ≤ 1 + Pe log₂ |α|`. -/
theorem conditionalEntropy_le_one_add_mul_logb [Finite β] [Fintype α] (joint : PMF (β × α))
    (g : β → α) :
    conditionalEntropy joint ≤
      1 + (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal * Real.logb 2 (Fintype.card α) := by
  have h := conditionalEntropy_le_binEntropy_add_mul_logb joint g
  set Pe := (joint.toOuterMeasure {z | g z.1 ≠ z.2}).toReal
  have hh : Real.binEntropy Pe / Real.log 2 ≤ 1 := by
    rw [div_le_one (Real.log_pos one_lt_two)]
    exact Real.binEntropy_le_log_two
  have hcard : (1 : ℝ) ≤ Fintype.card α := by
    have : Nonempty α := ⟨joint.support_nonempty.choose.2⟩
    exact_mod_cast Fintype.card_pos
  have hlog : Real.logb 2 (Fintype.card α - 1) ≤ Real.logb 2 (Fintype.card α) := by
    rcases eq_or_lt_of_le hcard with h1 | h1
    · rw [← h1, sub_self, Real.logb_zero, Real.logb_one]
    · exact Real.logb_le_logb_of_le one_lt_two (by linarith) (by linarith)
  have := mul_le_mul_of_nonneg_left hlog ENNReal.toReal_nonneg (a := Pe)
  linarith

end Cslib.Probability.PMF
