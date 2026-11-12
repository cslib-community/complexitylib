/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.MoserTardos
public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.LocalLemma

/-!
# Symmetric Moser–Tardos theorem and `PMF.pi` local-lemma bridge

This module provides two specializations of `Cslib.Probability.MoserTardos`:

1. **Symmetric Moser–Tardos** (`e * q * (d + 1) ≤ 1`): when every event `A i` has probability at
   most `q` and shares variables with at most `d` other events, we obtain the asymmetric weights
   explicitly (`1 / (d + 1)` when `1 ≤ d`, and `Pr[A i]` when `d = 0`), yielding constructive
   expected-resampling bounds (`1 / d` for `1 ≤ d`, `q / (1 - q)` / `1 / (e - 1)` for `d = 0`),
   almost sure finite termination, and an avoiding assignment.
2. **`PMF.pi` / `LocalLemma` bridge**: connecting `MoserTardos.table (fun v => (p v).toMeasure)`
   to `Cslib.Probability.PMF.pi p` via `Cslib.Probability.PMF.toMeasure_pi`, so hypotheses stated
   for `(PMF.pi p).toOuterMeasure` (as in `Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl`
   and `pi_iInter_compl_pos`) yield both positive avoidance probability and constructive
   resampling termination.

## Main results

* `Cslib.Probability.MoserTardos.exists_weights_of_symmetric`: converts `e * q * (d + 1) ≤ 1` into
  asymmetric weights `x i ∈ [0, 1)`.
* `Cslib.Probability.MoserTardos.lintegral_resamplings_le_symmetric`: expected resampling count at
  most `1 / d` under `e * q * (d + 1) ≤ 1` with `1 ≤ d`.
* `Cslib.Probability.MoserTardos.ae_exists_forall_notMem_run_symmetric`,
  `Cslib.Probability.MoserTardos.exists_forall_notMem_symmetric`: almost sure termination and
  constructive existence under `e * q * (d + 1) ≤ 1` for every `d : ℕ`.
* `Cslib.Probability.MoserTardos.toReal_toOuterMeasure_pi_eq_measureReal`: relates
  `(PMF.pi p).toOuterMeasure` and `(Measure.pi fun v => (p v).toMeasure).real`.
* `Cslib.Probability.MoserTardos.lintegral_resamplings_le_pmfPi`,
  `Cslib.Probability.MoserTardos.lintegral_resamplings_le_pmfPi_symmetric`: Moser–Tardos
  resampling bounds and constructive termination directly from `(PMF.pi p).toOuterMeasure`
  hypotheses.

## References

* [R. A. Moser, G. Tardos, *A constructive proof of the general Lovász Local Lemma*]
  [MoserTardos2010]
-/

public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Cslib.Probability.MoserTardos

section Weights

private theorem div_one_sub_le_div_one_sub {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    a / (1 - a) ≤ b / (1 - b) := by
  have ha1 : 0 < 1 - a := by linarith
  have hb1 : 0 < 1 - b := by linarith
  rw [div_le_div_iff₀ ha1 hb1]
  nlinarith

/-- Convert the symmetric Local Lemma hypothesis `Real.exp 1 * q * (d + 1) ≤ 1` into asymmetric
weights `x i ∈ [0, 1)`: constant `1 / (d + 1)` when `1 ≤ d` (using
`Cslib.Probability.le_inv_add_one_mul_one_sub_pow`), and `b i` when `d = 0`. -/
theorem exists_weights_of_symmetric {ι : Type*} (Γ : ι → Finset ι) {d : ℕ}
    (hd : ∀ i, #(Γ i) ≤ d) {b : ι → ℝ} (hb0 : ∀ i, 0 ≤ b i) {q : ℝ} (hq : ∀ i, b i ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    ∃ x : ι → ℝ, (∀ i, x i ∈ Set.Ico 0 1) ∧
      (∀ i, b i ≤ x i * ∏ j ∈ Γ i, (1 - x j)) ∧
      (1 ≤ d → ∀ i, x i / (1 - x i) = 1 / (d : ℝ)) ∧
      (d = 0 → ∀ i, x i / (1 - x i) ≤ q / (1 - q) ∧
        x i / (1 - x i) ≤ 1 / (Real.exp 1 - 1)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · have hexp : 1 < Real.exp 1 := Real.one_lt_exp_iff.2 zero_lt_one
    have hq_exp : q ≤ (Real.exp 1)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      calc q * Real.exp 1 = Real.exp 1 * q * ((0 : ℕ) + 1) := by ring
        _ ≤ 1 := hlll
    have hexp_lt : (Real.exp 1)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hexp
    refine ⟨b, fun i => ⟨hb0 i, (hq i).trans_lt (hq_exp.trans_lt hexp_lt)⟩, fun i => ?_,
      fun h => absurd h (by omega), fun _ i => ⟨?_, ?_⟩⟩
    · have hempty : Γ i = ∅ := card_eq_zero.1 (Nat.eq_zero_of_le_zero (hd i))
      simp [hempty]
    · exact div_one_sub_le_div_one_sub (hb0 i) (hq i) (hq_exp.trans_lt hexp_lt)
    · have hle := div_one_sub_le_div_one_sub (hb0 i) ((hq i).trans hq_exp) hexp_lt
      refine hle.trans_eq ?_
      have he0 : Real.exp 1 ≠ 0 := by positivity
      have he1 : Real.exp 1 - 1 ≠ 0 := by linarith
      field_simp
  · refine ⟨fun _ => 1 / ((d : ℝ) + 1), fun _ => ⟨by positivity, ?_⟩, fun i => ?_,
      fun _ _ => ?_, fun h => absurd h (by omega)⟩
    · have hd1 : (1 : ℝ) < (d : ℝ) + 1 := by
        exact_mod_cast Nat.lt_succ_of_le hdpos
      exact (div_lt_one (by positivity)).2 hd1
    · simpa only [prod_const] using
        (hq i).trans (Cslib.Probability.le_inv_add_one_mul_one_sub_pow (hd i) hlll)
    · have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
      have hsub : 1 - 1 / ((d : ℝ) + 1) = d / (d + 1) := by
        field_simp
        ring
      rw [hsub, div_div_div_cancel_right₀ hd1]

end Weights

section Symmetric

variable {V ι : Type*} [DecidableEq V] [DecidableEq ι] [Fintype ι]

private def symNbhd (vbl : ι → Finset V) (i : ι) : Finset ι :=
  univ.filter fun j => j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)

private theorem mem_symNbhd (vbl : ι → Finset V) (i j : ι) (hji : j ≠ i)
    (hdj : ¬Disjoint (vbl i) (vbl j)) : j ∈ symNbhd vbl i :=
  mem_filter.2 ⟨mem_univ _, hji, hdj⟩

private theorem symNbhd_card_le (vbl : ι → Finset V) {d : ℕ}
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d) (i : ι) :
    #(symNbhd vbl i) ≤ d := by
  simpa [symNbhd] using hd i

variable [Fintype V] {α : V → Type*} [∀ v, MeasurableSpace (α v)]
  (μ : ∀ v, Measure (α v)) [∀ v, IsProbabilityMeasure (μ v)] (vbl : ι → Finset V)

/-- Under `e * q * (d + 1) ≤ 1` with `1 ≤ d`, the expected supremum over all valid logs of
`w.count i` is at most `1 / d`. -/
theorem lintegral_iSup_count_le_symmetric_of_pos (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) (i : ι) :
    ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≤
      ENNReal.ofReal (1 / (d : ℝ)) := by
  obtain ⟨x, hx, hP, hx1, -⟩ := exists_weights_of_symmetric (symNbhd vbl)
    (symNbhd_card_le vbl hd) (fun _ => measureReal_nonneg) hq hlll
  exact (lintegral_iSup_count_le μ vbl A hAm hA (symNbhd vbl) (mem_symNbhd vbl) hx hP i).trans
    (le_of_eq (congrArg ENNReal.ofReal (hx1 hdpos i)))

/-- Under `e * q * (d + 1) ≤ 1` with `d = 0`, the expected supremum over valid logs of
`w.count i` is at most `q / (1 - q)` (and hence at most `1 / (e - 1)`). -/
theorem lintegral_iSup_count_le_symmetric_zero (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ 0)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * ((0 : ℕ) + 1) ≤ 1) (i : ι) :
    ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≤
      ENNReal.ofReal (q / (1 - q)) := by
  obtain ⟨x, hx, hP, -, hx0⟩ := exists_weights_of_symmetric (symNbhd vbl)
    (symNbhd_card_le vbl hd) (fun _ => measureReal_nonneg) hq hlll
  exact (lintegral_iSup_count_le μ vbl A hAm hA (symNbhd vbl) (mem_symNbhd vbl) hx hP i).trans
    (ENNReal.ofReal_le_ofReal (hx0 rfl i).1)

/-- For any `d : ℕ` with `e * q * (d + 1) ≤ 1`, every event's supremum resampling count has
finite expectation (hence the algorithm terminates almost surely). -/
theorem lintegral_iSup_count_ne_top_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) (i : ι) :
    ∫⁻ T, ⨆ (w : List ι) (_ : IsLog vbl A T w), (w.count i : ℝ≥0∞) ∂table μ ≠ ∞ := by
  obtain ⟨x, hx, hP, -, -⟩ := exists_weights_of_symmetric (symNbhd vbl)
    (symNbhd_card_le vbl hd) (fun _ => measureReal_nonneg) hq hlll
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_iSup_count_le μ vbl A hAm hA (symNbhd vbl) (mem_symNbhd vbl) hx hP i)

/-- **Symmetric Moser–Tardos theorem** (`1 ≤ d`) [MoserTardos2010]: under `e * q * (d + 1) ≤ 1`
with `1 ≤ d`, every valid selection rule resamples each event at most `1 / d` times in
expectation. -/
theorem lintegral_resamplings_le_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (1 / (d : ℝ)) :=
  lintegral_resamplings_le_of_bound μ vbl A
    (lintegral_iSup_count_le_symmetric_of_pos μ vbl A hAm hA hdpos hd hq hlll i) hsel

/-- Symmetric Moser–Tardos expected resampling count when `d = 0` (`e * q ≤ 1`): at most
`q / (1 - q)` (which is at most `1 / (e - 1)`). -/
theorem lintegral_resamplings_le_symmetric_zero (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ 0)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * ((0 : ℕ) + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table μ ≤ ENNReal.ofReal (q / (1 - q)) :=
  lintegral_resamplings_le_of_bound μ vbl A
    (lintegral_iSup_count_le_symmetric_zero μ vbl A hAm hA hd hq hlll i) hsel

/-- Measurable rule-independent dominating bound (`1 / d`) under the symmetric local lemma when
`1 ≤ d`. -/
theorem exists_measurable_ge_resamplings_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) (i : ι) :
    ∃ g : (∀ p : V × ℕ, α p.1) → ℝ≥0∞, Measurable g ∧
      ∫⁻ T, g T ∂table μ ≤ ENNReal.ofReal (1 / (d : ℝ)) ∧
      ∀ sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι,
        (∀ T w j, sel T w = some j → current vbl T w ∈ A j) →
          ∀ T, resamplings sel i T ≤ g T :=
  exists_measurable_ge_resamplings_of_bound μ vbl A hAm
    (lintegral_iSup_count_le_symmetric_of_pos μ vbl A hAm hA hdpos hd hq hlll i)

/-- Expected total number of resamplings under the symmetric local lemma (`1 ≤ d`): at most
`card ι / d`. -/
theorem lintegral_sum_resamplings_le_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∫⁻ T, ∑ i, resamplings sel i T ∂table μ ≤ Fintype.card ι * ENNReal.ofReal (1 / (d : ℝ)) := by
  have h := lintegral_sum_resamplings_le_of_bound μ vbl A hAm
    (fun i => lintegral_iSup_count_le_symmetric_of_pos μ vbl A hAm hA hdpos hd hq hlll i) hsel
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

/-- Almost sure termination under `e * q * (d + 1) ≤ 1`, for every `d : ℕ` and every valid
selection rule. -/
theorem ae_exists_run_eq_none_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) :
    ∀ᵐ T ∂table μ, ∃ n, sel T (run sel T n) = none := by
  obtain ⟨x, hx, hP, -, -⟩ := exists_weights_of_symmetric (symNbhd vbl)
    (symNbhd_card_le vbl hd) (fun _ => measureReal_nonneg) hq hlll
  exact ae_exists_run_eq_none μ vbl A hAm hA (symNbhd vbl) (mem_symNbhd vbl) hx hP hsel

/-- Almost sure success under `e * q * (d + 1) ≤ 1`, for every `d : ℕ` and every valid stopping
rule. -/
theorem ae_exists_forall_notMem_run_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ p : V × ℕ, α p.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i := by
  filter_upwards [ae_exists_run_eq_none_symmetric μ vbl A hAm hA hd hq hlll hsel] with T ⟨n, hn⟩
  exact ⟨n, hstop T _ hn⟩

/-- Almost sure success of `greedy` under `e * q * (d + 1) ≤ 1`, for every `d : ℕ`. -/
theorem ae_exists_forall_notMem_run_greedy_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    ∀ᵐ T ∂table μ, ∃ n, ∀ i, current vbl T (run (greedy vbl A) T n) ∉ A i :=
  ae_exists_forall_notMem_run_symmetric μ vbl A hAm hA hd hq hlll
    (fun _ _ _ h => greedy_eq_some vbl h) (fun _ _ h => greedy_eq_none vbl h)

/-- **Symmetric variable local lemma, constructively** (`e * q * (d + 1) ≤ 1`): some assignment
avoids every event. -/
theorem exists_forall_notMem_symmetric (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, (Measure.pi μ).real (A i) ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1) :
    ∃ σ : ∀ v, α v, ∀ i, σ ∉ A i := by
  classical
  obtain ⟨T, n, hn⟩ :=
    (ae_exists_forall_notMem_run_greedy_symmetric μ vbl A hAm hA hd hq hlll).exists
  exact ⟨_, hn⟩

end Symmetric

section PMFBridge

variable {V ι : Type*} [Fintype V] {α : V → Type*} [∀ v, Finite (α v)]
  [∀ v, MeasurableSpace (α v)] [∀ v, MeasurableSingletonClass (α v)]

/-- For a finite product of PMFs `PMF.pi p`, the outer measure `(PMF.pi p).toOuterMeasure` agrees
with `(Measure.pi fun v => (p v).toMeasure).real` on measurable sets via
`Cslib.Probability.PMF.toMeasure_pi`. -/
theorem toReal_toOuterMeasure_pi_eq_measureReal (p : ∀ v, PMF (α v)) {E : Set (∀ v, α v)}
    (hE : MeasurableSet E) :
    ((Cslib.Probability.PMF.pi p).toOuterMeasure E).toReal =
      (Measure.pi (fun v => (p v).toMeasure)).real E := by
  rw [← Cslib.Probability.PMF.toMeasure_pi, measureReal_def,
    PMF.toMeasure_apply_eq_toOuterMeasure_apply _ hE]

/-- Bridge from `Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl` to Moser–Tardos expected
resampling bounds on `table (fun v => (p v).toMeasure)`. Under `(PMF.pi p).toOuterMeasure`
local-lemma hypotheses with `x i ∈ [0, 1)`, every valid rule resamples `A i` at most
`x i / (1 - x i)` times in expectation. -/
theorem lintegral_resamplings_le_pmfPi [DecidableEq V] [DecidableEq ι] [Finite ι]
    (p : ∀ v, PMF (α v)) (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hAx : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤
      x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ q : V × ℕ, α q.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal (x i / (1 - x i)) :=
  lintegral_resamplings_le (fun v => (p v).toMeasure) vbl A hAm hA Γ hΓ hx
    (fun j => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm j)] using hAx j)
    hsel i

/-- Almost sure termination and avoidance for `table (fun v => (p v).toMeasure)` directly from the
asymmetric `Cslib.Probability.PMF.prod_one_sub_le_pi_iInter_compl` hypothesis with `x i ∈ [0, 1)`.
-/
theorem ae_exists_forall_notMem_run_pmfPi [DecidableEq V] [Finite ι]
    (p : ∀ v, PMF (α v)) (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    (Γ : ι → Finset ι) (hΓ : ∀ i j, j ≠ i → ¬Disjoint (vbl i) (vbl j) → j ∈ Γ i)
    {x : ι → ℝ} (hx : ∀ i, x i ∈ Set.Ico 0 1)
    (hAx : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤
      x i * ∏ j ∈ Γ i, (1 - x j))
    {sel : (∀ q : V × ℕ, α q.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table (fun v => (p v).toMeasure),
      ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i :=
  ae_exists_forall_notMem_run (fun v => (p v).toMeasure) vbl A hAm hA Γ hΓ hx
    (fun j => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm j)] using hAx j)
    hsel hstop

/-- Symmetric `PMF.pi` Moser–Tardos resampling bound (`1 ≤ d`): expected resamplings of `A i`
at most `1 / d` under `(PMF.pi p).toOuterMeasure (A i) ≤ q` and `e * q * (d + 1) ≤ 1`. -/
theorem lintegral_resamplings_le_pmfPi_symmetric [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (p : ∀ v, PMF (α v)) (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hdpos : 1 ≤ d)
    (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ q' : V × ℕ, α q'.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i) (i : ι) :
    ∫⁻ T, resamplings sel i T ∂table (fun v => (p v).toMeasure) ≤
      ENNReal.ofReal (1 / (d : ℝ)) :=
  lintegral_resamplings_le_symmetric (fun v => (p v).toMeasure) vbl A hAm hA hdpos hd
    (fun j => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm j)] using hq j)
    hlll hsel i

/-- Almost sure termination and avoidance for `table (fun v => (p v).toMeasure)` directly from the
symmetric `Cslib.Probability.PMF.pi_iInter_compl_pos` hypothesis `e * q * (d + 1) ≤ 1`. -/
theorem ae_exists_forall_notMem_run_pmfPi_symmetric [DecidableEq V] [DecidableEq ι] [Fintype ι]
    (p : ∀ v, PMF (α v)) (vbl : ι → Finset V) (A : ι → Set (∀ v, α v))
    (hAm : ∀ i, MeasurableSet (A i)) (hA : ∀ i, DependsOn (· ∈ A i) (vbl i : Set V))
    {d : ℕ} (hd : ∀ i, #{j : ι | j ≠ i ∧ ¬Disjoint (vbl i) (vbl j)} ≤ d)
    {q : ℝ} (hq : ∀ i, ((Cslib.Probability.PMF.pi p).toOuterMeasure (A i)).toReal ≤ q)
    (hlll : Real.exp 1 * q * (d + 1) ≤ 1)
    {sel : (∀ q' : V × ℕ, α q'.1) → List ι → Option ι}
    (hsel : ∀ T w i, sel T w = some i → current vbl T w ∈ A i)
    (hstop : ∀ T w, sel T w = none → ∀ i, current vbl T w ∉ A i) :
    ∀ᵐ T ∂table (fun v => (p v).toMeasure),
      ∃ n, ∀ i, current vbl T (run sel T n) ∉ A i :=
  ae_exists_forall_notMem_run_symmetric (fun v => (p v).toMeasure) vbl A hAm hA hd
    (fun j => by
      simpa only [toReal_toOuterMeasure_pi_eq_measureReal p (hAm j)] using hq j)
    hlll hsel hstop

end PMFBridge

end Cslib.Probability.MoserTardos
