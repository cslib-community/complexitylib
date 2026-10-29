/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.UniformNat
public import Complexity.Languages.Probabilistic.Repeat
import Mathlib.Data.Fintype.Fin
import Mathlib.Logic.Equiv.Option
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Finite-attempt uniform interval and integer-box sampling

Draw a fixed number of capped fair-bit samples and retain the first valid index. Exhaustion is
an explicit `none`, never an unbounded retry. Conditioned on success the result is uniform;
the unconditional law retains its failure mass. Bounds and all attempt/coordinate counts are
runtime inputs. The strict PPT implementation uses unary resource parameters.

At a positive interval bound, let `p = (dyadicSize bound - bound) / dyadicSize bound`.
The exact failure mass is `p ^ attempts`; every valid index has mass
`(1 - p ^ attempts) / bound`. The box success mass is `(1 - p ^ attempts) ^ dimension`, with
`bound = 2 * radius + 1`, and every Boolean test has unconditional error at most
`dimension * (1 / 2) ^ attempts`. No conditioning is part of the sampled program.

An empty interval always fails. Zero dimension returns `some []` without drawing even when
attempts is zero; radius zero is a singleton reference box but can still suffer retry failure.
These samplers are only a foundation for cryptographic realizations: a simulator's full
transcript/error and an extractor's implementation require separate proofs.

## Main definitions

* `Cslib.ProbComp.sampleUniformInterval`: bounded retry with an explicit failure result.
* `Cslib.ProbComp.intervalFailure`, `Cslib.ProbComp.intervalSuccess`: exact event masses.
* `Cslib.ProbComp.collectBox`, `Cslib.ProbComp.sampleIntegerBox`: coordinate gathering and
  coordinatewise finite-attempt integer-box sampling.
* `Cslib.ProbComp.integerBoxLaw`: the exact mathematical uniform reference law.

## Main results

* `Cslib.ProbComp.eval_sampleUniformInterval_none`,
  `Cslib.ProbComp.eval_sampleUniformInterval_some_toReal`: the full interval law.
* `Cslib.ProbComp.sampleUniformInterval_conditional`: conditional uniformity at observable
  success events.
* `Cslib.ProbComp.sampleUniformInterval_test_error_le`: unconditional interval error,
  including the binary-bound implementation.
* `Cslib.ProbComp.eval_sampleIntegerBox_some`, `Cslib.ProbComp.eval_sampleIntegerBox_none`:
  the full joint success/failure law.
* `Cslib.ProbComp.sampleIntegerBox_test_error_le`: explicit unconditional statistical error.
* `Cslib.ProbComp.sampleIntegerBox_support`: exact output dimension and integer bounds.
-/

@[expose] public section

namespace Cslib.ProbComp

open Probability
open scoped ENNReal NNReal

/-- The probability that one capped draw is rejected. At bound zero every draw is rejected. -/
noncomputable def intervalFailure (bound : ℕ) : ℝ≥0 :=
  (dyadicSize bound - bound : ℕ) / dyadicSize bound

/-- Draw all `attempts` capped samples, then return their first index strictly below `bound`.
Zero attempts and bound zero return `none`. -/
noncomputable def sampleUniformInterval (bound attempts : ℕ) : ProbComp (Option ℕ) :=
  (fun values => values.find? (fun value => decide (value < bound))) <$>
    OracleComp.replicate attempts (sampleBoundedIndex bound)

/-- With no attempts, exhaustion is immediate. -/
@[simp] theorem sampleUniformInterval_zero (bound : ℕ) :
    sampleUniformInterval bound 0 = pure none := rfl

/-- The capped sampler is also a binary natural sampler followed by binary capping. This
identity permits a binary implementation without writing the numerical bound in unary. -/
theorem sampleBoundedIndex_eq_binary (bound : ℕ) :
    sampleBoundedIndex bound = (min bound ·) <$> sampleBinaryNat (Nat.log 2 bound + 1) := by
  unfold sampleBoundedIndex sampleBinaryNat
  rw [Functor.map_map]
  congr 1
  funext word
  exact BitString.boundedBinaryValue_eq bound word

/-- A capped draw has equal mass at each valid index. -/
theorem eval_sampleBoundedIndex_lt (bound value : ℕ) (hvalue : value < bound) :
    ProbComp.eval (sampleBoundedIndex bound) value = (dyadicSize bound : ℝ≥0∞)⁻¹ := by
  rw [eval_sampleBoundedIndex]
  change ((PMF.uniformOfFintype (Fin (dyadicSize bound))).map
    (fun i => min bound i.val)) value = _
  rw [PMF.map_apply, tsum_fintype]
  let j : Fin (dyadicSize bound) := ⟨value, hvalue.trans (lt_dyadicSize bound)⟩
  rw [Finset.sum_eq_single j]
  · simp [j, Nat.min_eq_right hvalue.le]
  · intro i _ hij
    have hne : min bound i.val ≠ value := by
      intro h
      have : i = j := Fin.ext (by dsimp [j]; omega)
      exact hij this
    simp [Ne.symm hne]
  · simp

/-- All the excess dyadic mass is the rejection sentinel. -/
theorem eval_sampleBoundedIndex_sentinel (bound : ℕ) :
    ProbComp.eval (sampleBoundedIndex bound) bound = (intervalFailure bound : ℝ≥0∞) := by
  rw [eval_sampleBoundedIndex]
  change ((PMF.uniformOfFintype (Fin (dyadicSize bound))).map
    (fun i => min bound i.val)) bound = _
  have hcard : (Finset.univ.filter (fun i : Fin (dyadicSize bound) => bound ≤ i.val)).card =
      dyadicSize bound - bound := by
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin (dyadicSize bound) => i.val < bound)
    simp only [Fin.card_filter_val_lt, Finset.card_univ, Fintype.card_fin,
      Nat.min_eq_right (lt_dyadicSize bound).le, not_lt] at h
    omega
  have hmin (i : Fin (dyadicSize bound)) : bound = min bound i.val ↔ bound ≤ i.val := by omega
  simp only [PMF.map_apply, tsum_fintype, PMF.uniformOfFintype_apply, Fintype.card_fin, hmin]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  simp [intervalFailure, div_eq_mul_inv]

/-- The retry law, including the remaining failure event. All unused draws are integrated out. -/
theorem eval_sampleUniformInterval_succ (bound attempts : ℕ) :
    ProbComp.eval (sampleUniformInterval bound (attempts + 1)) =
      (ProbComp.eval (sampleBoundedIndex bound)).bind fun value =>
        if value < bound then PMF.pure (some value)
        else ProbComp.eval (sampleUniformInterval bound attempts) := by
  simp only [sampleUniformInterval, OracleComp.replicate_succ, ProbComp.eval_map,
    ProbComp.eval_bind, PMF.map_bind, PMF.map_comp, Function.comp_def]
  refine congrArg (PMF.bind _) (funext fun value => ?_)
  by_cases h : value < bound
  · simp only [List.find?_cons, h, decide_true, ↓reduceIte]
    exact PMF.map_const _ _
  · simp [h]

/-- A capped draw is never above its sentinel. -/
theorem le_bound_of_mem_support_sampleBoundedIndex {bound value : ℕ}
    (h : value ∈ (ProbComp.eval (sampleBoundedIndex bound)).support) : value ≤ bound := by
  rw [eval_sampleBoundedIndex, PMF.mem_support_map_iff] at h
  obtain ⟨i, _, rfl⟩ := h
  exact min_le_left _ _

private theorem capped_eq_zero {bound value : ℕ} (h : bound < value) :
    ProbComp.eval (sampleBoundedIndex bound) value = 0 :=
  (PMF.apply_eq_zero_iff _ _).mpr fun hm =>
    (not_le_of_gt h) (le_bound_of_mem_support_sampleBoundedIndex hm)

private theorem retry_none (bound : ℕ) (next : PMF (Option ℕ)) :
    ((ProbComp.eval (sampleBoundedIndex bound)).bind fun value =>
      if value < bound then PMF.pure (some value) else next) none =
      (intervalFailure bound : ℝ≥0∞) * next none := by
  rw [PMF.bind_apply, tsum_eq_single bound]
  · simp only [lt_self_iff_false, ↓reduceIte, eval_sampleBoundedIndex_sentinel]
  · intro value hne
    by_cases hv : value < bound
    · simp [hv]
    · rw [capped_eq_zero (by omega), zero_mul]

private theorem retry_some (bound value : ℕ) (next : PMF (Option ℕ)) :
    ((ProbComp.eval (sampleBoundedIndex bound)).bind fun i =>
      if i < bound then PMF.pure (some i) else next) (some value) =
      (intervalFailure bound : ℝ≥0∞) * next (some value) +
        if value < bound then (dyadicSize bound : ℝ≥0∞)⁻¹ else 0 := by
  let μ := ProbComp.eval (sampleBoundedIndex bound)
  have hterm (i : ℕ) : μ i *
      (if i < bound then PMF.pure (some i) else next) (some value) =
      (if i = bound then μ bound * next (some value) else 0) +
        (if i = value ∧ value < bound then μ value else 0) := by
    by_cases hib : i = bound
    · subst i
      have hfalse : ¬(bound = value ∧ value < bound) := by omega
      simp [hfalse]
    · by_cases hiv : i = value
      · subst i
        by_cases hv : value < bound
        · simp [hv, hib]
        · rw [show μ value = 0 from capped_eq_zero (by omega)]
          simp [hib]
      · by_cases hi : i < bound
        · simp [hi, hib, hiv, Ne.symm hiv]
        · rw [show μ i = 0 from capped_eq_zero (by omega)]
          simp [hib, hiv]
  change (∑' i, μ i * (if i < bound then PMF.pure (some i) else next) (some value)) = _
  simp_rw [hterm]
  rw [tsum_add]
  simp only [tsum_ite_eq]
  rw [show μ bound = (intervalFailure bound : ℝ≥0∞) from eval_sampleBoundedIndex_sentinel bound]
  by_cases hv : value < bound
  · simp only [hv, and_true, ↓reduceIte, tsum_ite_eq]
    rw [show μ value = (dyadicSize bound : ℝ≥0∞)⁻¹ from eval_sampleBoundedIndex_lt _ _ hv]
  · simp [hv]

/-- The exact exhaustion probability after a finite number of attempts. -/
theorem eval_sampleUniformInterval_none (bound attempts : ℕ) :
    ProbComp.eval (sampleUniformInterval bound attempts) none =
      (intervalFailure bound : ℝ≥0∞) ^ attempts := by
  induction attempts with
  | zero => simp
  | succ attempts ih =>
    rw [eval_sampleUniformInterval_succ, retry_none, ih, pow_succ, mul_comm]

/-- Every valid index has the same geometric-series mass; invalid indices have zero mass. -/
theorem eval_sampleUniformInterval_some (bound attempts value : ℕ) :
    ProbComp.eval (sampleUniformInterval bound attempts) (some value) =
      if value < bound then
        (∑ j ∈ Finset.range attempts, (intervalFailure bound : ℝ≥0∞) ^ j) /
          dyadicSize bound else 0 := by
  induction attempts with
  | zero => simp
  | succ attempts ih =>
    rw [eval_sampleUniformInterval_succ, retry_some, ih]
    by_cases hv : value < bound
    · simp only [hv, ↓reduceIte, div_eq_mul_inv]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, pow_succ']
      rw [← Finset.mul_sum]
      ring
    · simp [hv]

/-- Positive bounds accept with probability at least one half on each attempt. -/
theorem intervalFailure_le_half {bound : ℕ} (hbound : 0 < bound) :
    intervalFailure bound ≤ 1 / 2 := by
  have hsize : dyadicSize bound ≤ 2 * bound := by
    have h := Nat.pow_log_le_self 2 hbound.ne'
    unfold dyadicSize
    rw [pow_succ]
    omega
  have hpos : (0 : ℝ≥0) < dyadicSize bound := by exact_mod_cast dyadicSize_pos bound
  unfold intervalFailure
  rw [div_le_div_iff₀ hpos (by norm_num : (0 : ℝ≥0) < 2)]
  norm_num only [one_mul]
  exact_mod_cast (show (dyadicSize bound - bound) * 2 ≤ dyadicSize bound by omega)

/-- Exhaustion is exponentially unlikely at a positive bound; zero remains a separate case. -/
theorem eval_sampleUniformInterval_none_le {bound : ℕ} (hbound : 0 < bound) (attempts : ℕ) :
    ProbComp.eval (sampleUniformInterval bound attempts) none ≤ (1 / 2 : ℝ≥0∞) ^ attempts := by
  rw [eval_sampleUniformInterval_none]
  gcongr
  simpa using (ENNReal.coe_le_coe.mpr (intervalFailure_le_half hbound))

/-- A real-valued form of the complete success law, with no conditioning away of failure. -/
theorem eval_sampleUniformInterval_some_toReal {bound : ℕ} (hbound : 0 < bound)
    (attempts value : ℕ) :
    (ProbComp.eval (sampleUniformInterval bound attempts) (some value)).toReal =
      if value < bound then (1 - (intervalFailure bound : ℝ) ^ attempts) / bound else 0 := by
  rw [eval_sampleUniformInterval_some]
  by_cases hv : value < bound
  · simp only [hv, ↓reduceIte, ENNReal.toReal_div, ENNReal.toReal_natCast]
    rw [ENNReal.toReal_sum (fun _ _ => ENNReal.pow_ne_top ENNReal.coe_ne_top)]
    simp only [ENNReal.toReal_pow, ENNReal.coe_toReal]
    have hD : (dyadicSize bound : ℝ) ≠ 0 := by exact_mod_cast (dyadicSize_pos bound).ne'
    have hb : (bound : ℝ) ≠ 0 := by exact_mod_cast hbound.ne'
    have hrate : (intervalFailure bound : ℝ) = 1 - (bound : ℝ) / dyadicSize bound := by
      simp only [intervalFailure, NNReal.coe_div, NNReal.coe_natCast,
        Nat.cast_sub (lt_dyadicSize bound).le]
      field_simp
    have hrel : (1 - (intervalFailure bound : ℝ)) * dyadicSize bound = bound := by
      rw [hrate]
      field_simp
      ring
    apply (div_eq_div_iff hD hb).mpr
    calc (∑ j ∈ Finset.range attempts, (intervalFailure bound : ℝ) ^ j) * bound
        = (∑ j ∈ Finset.range attempts, (intervalFailure bound : ℝ) ^ j) *
            ((1 - (intervalFailure bound : ℝ)) * dyadicSize bound) := by rw [hrel]
      _ = (1 - (intervalFailure bound : ℝ) ^ attempts) * dyadicSize bound := by
          rw [← mul_assoc, geom_sum_mul_neg]
  · simp [hv]

private theorem option_false {α : Type} (μ : PMF (Option α)) :
    (μ.map Option.isSome) false = μ none := by
  rw [PMF.map_apply, tsum_eq_single none]
  · simp
  · intro value hvalue
    cases value with
    | none => exact (hvalue rfl).elim
    | some value => simp

private theorem option_success_toReal {α : Type} (μ : PMF (Option α)) :
    ((μ.map Option.isSome) true).toReal = 1 - (μ none).toReal := by
  have h := (μ.map Option.isSome).tsum_coe
  have hsum : (μ.map Option.isSome) false + (μ.map Option.isSome) true = 1 := by
    simpa only [tsum_fintype, Fintype.sum_bool, add_comm] using h
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    ENNReal.toReal_one, option_false] at hreal
  linarith

/-- The denominator used for conditioning is exactly the probability of success. -/
theorem eval_sampleUniformInterval_success (bound attempts : ℕ) :
    (((ProbComp.eval (sampleUniformInterval bound attempts)).map Option.isSome) true).toReal =
      1 - (intervalFailure bound : ℝ) ^ attempts := by
  rw [option_success_toReal, eval_sampleUniformInterval_none, ENNReal.toReal_pow,
    ENNReal.coe_toReal]

/-- Conditioned on the observable success event, every valid interval value has probability
`1 / bound`. Positivity of the attempt budget and bound makes this conditioning meaningful. -/
theorem sampleUniformInterval_conditional {bound attempts value : ℕ}
    (hbound : 0 < bound) (hattempts : 0 < attempts) (hvalue : value < bound) :
    (ProbComp.eval (sampleUniformInterval bound attempts) (some value)).toReal /
      (((ProbComp.eval (sampleUniformInterval bound attempts)).map Option.isSome) true).toReal =
        (1 : ℝ) / bound := by
  have hp : (intervalFailure bound : ℝ) < 1 := by
    have h := intervalFailure_le_half hbound
    have : (intervalFailure bound : ℝ) ≤ 1 / 2 := by exact_mod_cast h
    linarith
  have hpow : (intervalFailure bound : ℝ) ^ attempts < 1 :=
    pow_lt_one₀ (NNReal.coe_nonneg _) hp hattempts.ne'
  have hden : 1 - (intervalFailure bound : ℝ) ^ attempts ≠ 0 := by linarith
  rw [eval_sampleUniformInterval_some_toReal hbound, ite_eq_left hvalue,
    eval_sampleUniformInterval_success]
  field_simp

/-- Total mass retained by the finite-attempt sampler. -/
noncomputable def intervalSuccess (bound attempts : ℕ) : ℝ≥0 :=
  1 - intervalFailure bound ^ attempts

private theorem intervalFailure_le_one (bound : ℕ) : intervalFailure bound ≤ 1 := by
  have h := (ProbComp.eval (sampleBoundedIndex bound)).coe_le_one bound
  rw [eval_sampleBoundedIndex_sentinel] at h
  exact_mod_cast h

private theorem intervalSuccess_coe (bound attempts : ℕ) :
    (intervalSuccess bound attempts : ℝ) = 1 - (intervalFailure bound : ℝ) ^ attempts := by
  have hp : intervalFailure bound ^ attempts ≤ 1 :=
    pow_le_one₀ (show 0 ≤ intervalFailure bound from zero_le) (intervalFailure_le_one bound)
  simp only [intervalSuccess, NNReal.coe_sub hp, NNReal.coe_one, NNReal.coe_pow]

private theorem uniformFin_nat_apply (bound value : ℕ) [NeZero bound] :
    ((PMF.uniformOfFintype (Fin bound)).map Fin.val) value =
      if value < bound then (bound : ℝ≥0∞)⁻¹ else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hv : value < bound
  · let j : Fin bound := ⟨value, hv⟩
    rw [tsum_eq_single j]
    · simp [j, hv]
    · intro i hi
      have : value ≠ i.val := fun h => hi (Fin.ext h.symm)
      simp [this]
  · rw [tsum_eq_zero_iff.mpr]
    · simp [hv]
    · intro i
      have : value ≠ i.val := by omega
      simp [this]

/-- The successful part of the full sampler law is its success mass times exact uniformity. -/
theorem eval_sampleUniformInterval_some_eq (bound attempts value : ℕ) [NeZero bound] :
    ProbComp.eval (sampleUniformInterval bound attempts) (some value) =
      (intervalSuccess bound attempts : ℝ≥0∞) *
        ((PMF.uniformOfFintype (Fin bound)).map Fin.val) value := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top (PMF.apply_ne_top _ _))).mp
  rw [eval_sampleUniformInterval_some_toReal (Nat.pos_of_ne_zero (NeZero.ne bound)),
    ENNReal.toReal_mul, ENNReal.coe_toReal, intervalSuccess_coe, uniformFin_nat_apply]
  by_cases hv : value < bound
  · simp [hv, div_eq_mul_inv]
  · simp [hv]

private theorem tsum_option_eq {α : Type} (f : Option α → ℝ≥0∞) :
    ∑' x, f x = f none + ∑' x, f (some x) := by
  rw [← (Equiv.optionEquivSumPUnit.{0, 0} α).symm.tsum_eq f]
  rw [CompleteLattice.summable.tsum_sum CompleteLattice.summable]
  simp [add_comm]

private theorem optional_map_density {α β : Type} (μ : PMF (Option α)) (ν : PMF α)
    (mass : ℝ≥0∞) (h : ∀ a, μ (some a) = mass * ν a) (f : α → β) (b : β) :
    (μ.map (fun x => x.elim none (fun a => some (f a)))) (some b) = mass * (ν.map f) b := by
  classical
  rw [PMF.map_apply, tsum_option_eq]
  simp only [Option.elim_none, Option.elim_some, reduceCtorEq, ↓reduceIte, zero_add,
    Option.some.injEq]
  simp_rw [h]
  rw [PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro a
  split_ifs <;> simp

/-- Gather successful coordinates, preserving the entire failure event. -/
def collectBox (values : List (Option ℤ)) : Option (List ℤ) :=
  if values.all Option.isSome then some (values.map (fun value => value.getD 0)) else none

/-- Gathering coordinates agrees with ordinary option sequencing. -/
theorem collectBox_cons (value : Option ℤ) (values : List (Option ℤ)) :
    collectBox (value :: values) = (do
      let z ← value
      let rest ← collectBox values
      pure (z :: rest)) := by
  cases value with
  | none => simp [collectBox]
  | some z =>
    by_cases h : values.all Option.isSome
    · simp [collectBox, h]
    · simp [collectBox, h]

/-- Successful gathering preserves every coordinate and cannot hide a failed coordinate. -/
theorem collectBox_eq_some (values : List (Option ℤ)) (out : List ℤ) :
    collectBox values = some out ↔ values = out.map some := by
  induction values generalizing out with
  | nil => cases out <;> simp [collectBox]
  | cons value values ih =>
    rw [collectBox_cons]
    cases value with
    | none => cases out <;> simp
    | some z =>
      cases out with
      | nil => cases h : collectBox values <;> simp
      | cons a out =>
        cases h : collectBox values with
        | none => simp [← ih, h]
        | some rest => simp [← ih, h]

/-- Sample each coordinate of `[-radius,radius]^dimension` with its own finite attempt budget.
The result is a list of exactly `dimension` integers on success. Radius is a unary resource in the
strict PPT certificate; this definition makes no logarithmic-radius complexity claim. -/
noncomputable def sampleIntegerBox (radius dimension attempts : ℕ) : ProbComp (Option (List ℤ)) :=
  collectBox <$> OracleComp.replicate dimension
    ((fun value => value.elim none (fun (i : ℕ) => some ((i : ℤ) - radius))) <$>
      sampleUniformInterval (2 * radius + 1) attempts)

/-- An empty box has one point and needs no samples, even with no attempts. -/
@[simp] theorem sampleIntegerBox_zero_dimension (radius attempts : ℕ) :
    sampleIntegerBox radius 0 attempts = pure (some []) := rfl

/-- Reference uniform box law, represented as a list of independent uniform integer coordinates.
This is a mathematical PMF, not an assertion of exact fair-bit realizability. -/
noncomputable def integerBoxLaw (radius dimension : ℕ) : PMF (List ℤ) :=
  (PMF.iid ((PMF.uniformOfFintype (Fin (2 * radius + 1))).map
    (fun i => (i.val : ℤ) - radius)) dimension).map List.ofFn

private theorem iid_list_apply {α : Type} (μ : PMF α) {n : ℕ} (f : Fin n → α) :
    ((PMF.iid μ n).map List.ofFn) (List.ofFn f) = ∏ i, μ (f i) := by
  classical
  rw [PMF.map_apply, tsum_eq_single f]
  · simp [PMF.iid_apply]
  · intro g hg
    have hne : List.ofFn f ≠ List.ofFn g := fun h => hg (List.ofFn_injective h).symm
    simp [hne]

private theorem gather_iid_apply (μ : PMF (Option ℤ)) {n : ℕ} (f : Fin n → ℤ) :
    ((PMF.iid μ n).map (fun v => collectBox (List.ofFn v))) (some (List.ofFn f)) =
      ∏ i, μ (some (f i)) := by
  classical
  rw [PMF.map_apply, tsum_eq_single (fun i => some (f i))]
  · have hcollect : collectBox (List.ofFn (fun i => some (f i))) = some (List.ofFn f) := by
      rw [collectBox_eq_some, List.map_ofFn]
      rfl
    rw [ite_eq_left hcollect.symm, PMF.iid_apply]
  · intro g hg
    refine ite_eq_right fun h => hg ?_
    have heq := (collectBox_eq_some _ _).mp h.symm
    rw [List.map_ofFn] at heq
    exact List.ofFn_injective heq

private theorem gather_off_length (μ : PMF (Option ℤ)) (n : ℕ) (out : List ℤ)
    (hlen : out.length ≠ n) :
    ((PMF.iid μ n).map (fun v => collectBox (List.ofFn v))) (some out) = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro h
  obtain ⟨v, _, hv⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have heq := congrArg List.length ((collectBox_eq_some _ _).mp hv)
  simp only [List.length_ofFn, List.length_map] at heq
  exact hlen heq.symm

private theorem iid_off_length (μ : PMF ℤ) (n : ℕ) (out : List ℤ)
    (hlen : out.length ≠ n) : ((PMF.iid μ n).map List.ofFn) out = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro h
  obtain ⟨v, _, hv⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  have heq := congrArg List.length hv
  simp only [List.length_ofFn] at heq
  exact hlen heq.symm

/-- The full successful box law is the exact uniform box law scaled by the probability that
all coordinate samplers succeed. It includes zero dimension and zero attempts. -/
theorem eval_sampleIntegerBox_some (radius dimension attempts : ℕ) (out : List ℤ) :
    ProbComp.eval (sampleIntegerBox radius dimension attempts) (some out) =
      (intervalSuccess (2 * radius + 1) attempts : ℝ≥0∞) ^ dimension *
        integerBoxLaw radius dimension out := by
  let μ := ProbComp.eval ((fun value =>
    value.elim none (fun (i : ℕ) => some ((i : ℤ) - radius))) <$>
      sampleUniformInterval (2 * radius + 1) attempts)
  let ν := (PMF.uniformOfFintype (Fin (2 * radius + 1))).map
    (fun i => (i.val : ℤ) - radius)
  have hdensity (z : ℤ) : μ (some z) =
      (intervalSuccess (2 * radius + 1) attempts : ℝ≥0∞) * ν z := by
    dsimp only [μ, ν]
    rw [ProbComp.eval_map]
    simpa only [PMF.map_comp, Function.comp_def] using
      optional_map_density (ProbComp.eval (sampleUniformInterval (2 * radius + 1) attempts))
        ((PMF.uniformOfFintype (Fin (2 * radius + 1))).map Fin.val)
        (intervalSuccess (2 * radius + 1) attempts)
        (fun value => eval_sampleUniformInterval_some_eq (2 * radius + 1) attempts value)
        (fun i => (i : ℤ) - radius) z
  rw [sampleIntegerBox, ProbComp.eval_map, ProbComp.eval_replicate_iid, PMF.map_comp]
  change ((PMF.iid μ dimension).map (fun v => collectBox (List.ofFn v))) (some out) = _
  by_cases hlen : out.length = dimension
  · subst dimension
    have h := gather_iid_apply μ out.get
    simp only [List.ofFn_get] at h
    rw [h]
    simp_rw [hdensity]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have href := iid_list_apply ν out.get
    simp only [List.ofFn_get] at href
    rw [← href]
    rfl
  · rw [gather_off_length μ dimension out hlen]
    change 0 = _ * ((PMF.iid ν dimension).map List.ofFn) out
    rw [iid_off_length ν dimension out hlen, mul_zero]

/-- Real-valued joint success masses, using only the displayed retry-error parameters. -/
theorem eval_sampleIntegerBox_some_toReal (radius dimension attempts : ℕ) (out : List ℤ) :
    (ProbComp.eval (sampleIntegerBox radius dimension attempts) (some out)).toReal =
      (1 - (intervalFailure (2 * radius + 1) : ℝ) ^ attempts) ^ dimension *
        (integerBoxLaw radius dimension out).toReal := by
  rw [eval_sampleIntegerBox_some, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.coe_toReal, intervalSuccess_coe]

/-- The exact total box exhaustion probability. Failure is present in the joint law, rather
than discarded by conditioning. -/
theorem eval_sampleIntegerBox_none (radius dimension attempts : ℕ) :
    (ProbComp.eval (sampleIntegerBox radius dimension attempts) none).toReal =
      1 - (1 - (intervalFailure (2 * radius + 1) : ℝ) ^ attempts) ^ dimension := by
  let μ := ProbComp.eval (sampleIntegerBox radius dimension attempts)
  have h := μ.tsum_coe
  rw [tsum_option_eq] at h
  simp_rw [show ∀ out, μ (some out) =
      (intervalSuccess (2 * radius + 1) attempts : ℝ≥0∞) ^ dimension *
        integerBoxLaw radius dimension out from
          eval_sampleIntegerBox_some radius dimension attempts]
    at h
  rw [ENNReal.tsum_mul_left, (integerBoxLaw radius dimension).tsum_coe, mul_one] at h
  have hreal := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add (μ.apply_ne_top _) (ENNReal.pow_ne_top ENNReal.coe_ne_top),
    ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.coe_toReal, intervalSuccess_coe] at hreal
  linarith

private theorem one_sub_pow_le (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (n : ℕ) :
    1 - s ^ n ≤ n * (1 - s) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc 1 - s ^ (n + 1) = (1 - s ^ n) + s ^ n * (1 - s) := by rw [pow_succ]; ring
      _ ≤ n * (1 - s) + (1 - s) := by
        apply add_le_add ih
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_le_one₀ hs0 hs1) (sub_nonneg.mpr hs1)
      _ = (n + 1 : ℕ) * (1 - s) := by push_cast; ring

/-- The unconditional failure error is at most the dimension times the per-coordinate dyadic
retry error. In particular, dimension zero has zero error even when attempts is zero. -/
theorem eval_sampleIntegerBox_none_le (radius dimension attempts : ℕ) :
    (ProbComp.eval (sampleIntegerBox radius dimension attempts) none).toReal ≤
      dimension * (1 / 2 : ℝ) ^ attempts := by
  rw [eval_sampleIntegerBox_none]
  have hp0 : (0 : ℝ) ≤ (intervalFailure (2 * radius + 1) : ℝ) ^ attempts :=
    pow_nonneg (NNReal.coe_nonneg _) _
  have hp1 : (intervalFailure (2 * radius + 1) : ℝ) ^ attempts ≤ 1 := by
    apply pow_le_one₀ (NNReal.coe_nonneg _)
    exact_mod_cast intervalFailure_le_one (2 * radius + 1)
  calc
    _ ≤ dimension * (1 - (1 - (intervalFailure (2 * radius + 1) : ℝ) ^ attempts)) :=
      one_sub_pow_le _ (sub_nonneg.mpr hp1) (by linarith) dimension
    _ = dimension * (intervalFailure (2 * radius + 1) : ℝ) ^ attempts := by ring
    _ ≤ _ := by
      gcongr
      have h := intervalFailure_le_half (by omega : 0 < 2 * radius + 1)
      exact_mod_cast h

/-- Given success, the box has exactly its uniform product law. A positive attempt budget makes
that event observable; the empty box already has its separate exact no-draw law. -/
theorem sampleIntegerBox_conditional (radius dimension attempts : ℕ) (hattempts : 0 < attempts)
    (out : List ℤ) :
    (ProbComp.eval (sampleIntegerBox radius dimension attempts) (some out)).toReal /
      (((ProbComp.eval (sampleIntegerBox radius dimension attempts)).map Option.isSome)
        true).toReal = (integerBoxLaw radius dimension out).toReal := by
  have hp : (intervalFailure (2 * radius + 1) : ℝ) < 1 := by
    have h := intervalFailure_le_half (by omega : 0 < 2 * radius + 1)
    have : (intervalFailure (2 * radius + 1) : ℝ) ≤ 1 / 2 := by exact_mod_cast h
    linarith
  have hpow := pow_lt_one₀ (NNReal.coe_nonneg _) hp hattempts.ne'
  have hpositive : 0 < (intervalSuccess (2 * radius + 1) attempts : ℝ) := by
    rw [intervalSuccess_coe]
    linarith
  rw [option_success_toReal, eval_sampleIntegerBox_none, eval_sampleIntegerBox_some,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal]
  rw [← intervalSuccess_coe]
  have hcancel : 1 - (1 - (intervalSuccess (2 * radius + 1) attempts : ℝ) ^ dimension) =
      (intervalSuccess (2 * radius + 1) attempts : ℝ) ^ dimension := by ring
  rw [hcancel]
  exact mul_div_cancel_left₀ _ (pow_pos hpositive _).ne'

private theorem optional_test {α : Type} (μ : PMF (Option α)) (ν : PMF α)
    (mass : ℝ≥0∞) (h : ∀ a, μ (some a) = mass * ν a) (test : Option α → Bool) :
    (μ.map test) true = (if test none then μ none else 0) +
      mass * (ν.map (fun a => test (some a))) true := by
  classical
  rw [PMF.map_apply, tsum_option_eq, PMF.map_apply, ← ENNReal.tsum_mul_left]
  congr 1
  · cases htest : test none <;> simp
  · apply tsum_congr
    intro a
    by_cases ht : true = test (some a)
    · simp [ht, h]
    · simp [ht]

private theorem optional_test_error {α : Type} (μ : PMF (Option α)) (ν : PMF α)
    (mass : ℝ≥0∞) (hmass_top : mass ≠ ⊤) (h : ∀ a, μ (some a) = mass * ν a)
    (test : Option α → Bool) :
    |((μ.map test) true).toReal - ((ν.map (fun a => test (some a))) true).toReal| ≤
      (μ none).toReal := by
  have hd := optional_test μ ν mass h test
  have htotal := μ.tsum_coe
  rw [tsum_option_eq] at htotal
  simp_rw [h] at htotal
  rw [ENNReal.tsum_mul_left, ν.tsum_coe, mul_one] at htotal
  have hmass : mass.toReal = 1 - (μ none).toReal := by
    have hr := congrArg ENNReal.toReal htotal
    rw [ENNReal.toReal_add (μ.apply_ne_top _) hmass_top, ENNReal.toReal_one] at hr
    linarith
  let u := ((ν.map (fun out => test (some out))) true).toReal
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  have hu1 : u ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top
      ((ν.map (fun out => test (some out))).coe_le_one true)
  have hf0 : 0 ≤ (μ none).toReal := ENNReal.toReal_nonneg
  have hfirst : (if test none then μ none else 0) ≠ (⊤ : ℝ≥0∞) := by
    split_ifs
    · exact μ.apply_ne_top _
    · exact ENNReal.zero_ne_top
  have hprod : mass * (ν.map (fun out => test (some out))) true ≠ ⊤ :=
    ENNReal.mul_ne_top hmass_top (PMF.apply_ne_top _ _)
  have hreal := congrArg ENNReal.toReal hd
  rw [ENNReal.toReal_add hfirst hprod, ENNReal.toReal_mul, hmass] at hreal
  change |(μ.map test true).toReal - u| ≤ (μ none).toReal
  change (μ.map test true).toReal = _ + (1 - (μ none).toReal) * u at hreal
  cases htest : test none
  · simp only [htest, Bool.false_eq_true, ↓reduceIte, ENNReal.toReal_zero, zero_add] at hreal
    rw [hreal, show (1 - (μ none).toReal) * u - u = -((μ none).toReal * u) by ring,
      abs_neg, abs_of_nonneg (mul_nonneg hf0 hu0)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu1 hf0
  · simp only [htest, ↓reduceIte] at hreal
    rw [hreal, show (μ none).toReal + (1 - (μ none).toReal) * u - u =
      (μ none).toReal * (1 - u) by ring, abs_of_nonneg (mul_nonneg hf0 (sub_nonneg.mpr hu1))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith : 1 - u ≤ 1) hf0

/-- Any Boolean test changes acceptance probability by at most the explicit failure mass when
compared with an exact uniform box. This is an unconditional statistical-error statement. -/
theorem sampleIntegerBox_test_error (radius dimension attempts : ℕ)
    (test : Option (List ℤ) → Bool) :
    |(((ProbComp.eval (sampleIntegerBox radius dimension attempts)).map test) true).toReal -
      (((integerBoxLaw radius dimension).map (fun out => test (some out))) true).toReal| ≤
        (ProbComp.eval (sampleIntegerBox radius dimension attempts) none).toReal :=
  optional_test_error _ _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    (eval_sampleIntegerBox_some radius dimension attempts) test

/-- For a positive interval, every Boolean test has unconditional error at most the dyadic
retry-failure bound against exact uniformity. This applies to binary cryptographic bounds too;
it neither discards failure nor asserts an exact non-dyadic fair-bit sampler. -/
theorem sampleUniformInterval_test_error_le (bound attempts : ℕ) [NeZero bound]
    (test : Option ℕ → Bool) :
    |(((ProbComp.eval (sampleUniformInterval bound attempts)).map test) true).toReal -
      ((((PMF.uniformOfFintype (Fin bound)).map Fin.val).map
        (fun value => test (some value))) true).toReal| ≤ (1 / 2 : ℝ) ^ attempts := by
  calc
    _ ≤ (ProbComp.eval (sampleUniformInterval bound attempts) none).toReal :=
      optional_test_error _ _ _ ENNReal.coe_ne_top
        (fun value => eval_sampleUniformInterval_some_eq bound attempts value) test
    _ ≤ _ := by
      rw [eval_sampleUniformInterval_none, ENNReal.toReal_pow, ENNReal.coe_toReal]
      gcongr
      have h := intervalFailure_le_half (Nat.pos_of_ne_zero (NeZero.ne bound))
      exact_mod_cast h

/-- Explicit statistical error of the bounded box sampler for every Boolean test. -/
theorem sampleIntegerBox_test_error_le (radius dimension attempts : ℕ)
    (test : Option (List ℤ) → Bool) :
    |(((ProbComp.eval (sampleIntegerBox radius dimension attempts)).map test) true).toReal -
      (((integerBoxLaw radius dimension).map (fun out => test (some out))) true).toReal| ≤
        dimension * (1 / 2 : ℝ) ^ attempts :=
  (sampleIntegerBox_test_error radius dimension attempts test).trans
    (eval_sampleIntegerBox_none_le radius dimension attempts)

/-- The zero bound is an exact, total failure case. -/
@[simp] theorem intervalFailure_zero : intervalFailure 0 = 1 := by
  norm_num [intervalFailure, dyadicSize]

/-- No attempt can produce a valid index for an empty interval. -/
@[simp] theorem eval_sampleUniformInterval_zero_bound (attempts : ℕ) :
    ProbComp.eval (sampleUniformInterval 0 attempts) = PMF.pure none := by
  ext value
  cases value with
  | none => simp [eval_sampleUniformInterval_none]
  | some value => simp [eval_sampleUniformInterval_some]

/-- Every supported reference output has the requested dimension and integer radius. -/
theorem integerBoxLaw_support {radius dimension : ℕ} {out : List ℤ}
    (h : out ∈ (integerBoxLaw radius dimension).support) :
    out.length = dimension ∧ ∀ z ∈ out, -(radius : ℤ) ≤ z ∧ z ≤ radius := by
  obtain ⟨v, hv, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  refine ⟨List.length_ofFn, ?_⟩
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  have hi := (PMF.mem_support_iid_iff _ _).mp hv i
  obtain ⟨value, _, hvalue⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
  rw [← hvalue]
  have hlt := value.isLt
  constructor <;> omega

/-- Every successful bounded sample lies in the intended integer box with the exact dimension. -/
theorem sampleIntegerBox_support {radius dimension attempts : ℕ} {out : List ℤ}
    (h : some out ∈ (ProbComp.eval (sampleIntegerBox radius dimension attempts)).support) :
    out.length = dimension ∧ ∀ z ∈ out, -(radius : ℤ) ≤ z ∧ z ≤ radius := by
  rw [PMF.mem_support_iff, eval_sampleIntegerBox_some, mul_ne_zero_iff] at h
  exact integerBoxLaw_support h.2

/-- Each indexed point of the reference integer box has the same product mass. -/
theorem integerBoxLaw_apply_index (radius dimension : ℕ)
    (v : Fin dimension → Fin (2 * radius + 1)) :
    integerBoxLaw radius dimension (List.ofFn (fun i => (v i : ℤ) - radius)) =
      ((2 * radius + 1 : ℕ) : ℝ≥0∞)⁻¹ ^ dimension := by
  rw [integerBoxLaw, iid_list_apply]
  have hcoord (i : Fin dimension) :
      ((PMF.uniformOfFintype (Fin (2 * radius + 1))).map
        (fun j => (j.val : ℤ) - radius)) ((v i : ℤ) - radius) =
          ((2 * radius + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [PMF.map_apply, tsum_eq_single (v i)]
    · simp
    · intro j hj
      have hne : (v i : ℤ) - radius ≠ (j.val : ℤ) - radius := by
        intro h
        apply hj
        apply Fin.ext
        omega
      simp [hne]
  simp_rw [hcoord]
  simp

end Cslib.ProbComp
