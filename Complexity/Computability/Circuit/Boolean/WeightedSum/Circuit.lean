/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.WeightedSum.Grouping
public import Complexity.Computability.Circuit.Boolean.Modular.Multiply.PolyTime
public import Complexity.Computability.Circuit.Boolean.PopulationCount.ThresholdPolyTime
public import Complexity.Computability.Circuit.Boolean.FunctionalCNF
import Mathlib.Tactic.GCongr
import Complexity.Foundations.Data.Nat.Log

/-!
# Grouped weighted comparison circuits

Actual radix-group population counts feed modular multipliers by known coefficients and a
carry-save sum. No input assignment, gate values or desired comparison circuit is supplied.
The modular sum is exact when the original total fits the derived width. Full truth-table CNF
therefore has unique auxiliary extensions. Source: [ChenJiangZhu2027], Lemma A.1 (PDF pp.28–29).

## Main definitions

* `groupCount`: count the actual signed literals in a radix group.
* `sumCircuit`: compute all weighted group contributions and their sum.
* `leCircuit`: binary integer upper comparison, including out-of-range targets.

## Main results

* `val_eval_sumCircuit`: exact original weighted sum under the coefficient promise.
* `eval_leCircuit`: actual upper comparison on every original assignment.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

open scoped BigOperators
open BitString

/-- One bit per actual grouped literal; positive literals are just wires. -/
@[expose] def literals {n : ℕ} (positive : Fin n → Bool) (is : List (Fin n)) :
    Circuit signature n is.length :=
  Circuit.pi fun j =>
    (if positive (is[j.val]) then (Formula.input is[j.val])
      else (Formula.input is[j.val]).not).toCircuit

private theorem eval_literals {n : ℕ} (positive x : Fin n → Bool) (is : List (Fin n)) :
    (literals positive is).eval interpretation x =
      fun j => literal (positive is[j.val]) (x is[j.val]) := by
  funext j
  simp only [literals, Circuit.eval_pi, Formula.eval_toCircuit]
  split_ifs <;> simp_all [literal]

private theorem size_literals_le {n : ℕ} (positive : Fin n → Bool) (is : List (Fin n)) :
    (literals positive is).size ≤ is.length := by
  rw [literals, Circuit.size_pi]
  calc _ ≤ ∑ _ : Fin is.length, 1 := Finset.sum_le_sum fun j _ => by
          split_ifs <;> simp
    _ = _ := by simp

/-- Group population word, widened with one shared zero gate. -/
@[expose] def groupCount {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P a q w : ℕ) : Circuit signature n w :=
  let is := group weights P a q
  (PopulationCount.pad (Nat.clog 2 (is.length + 1) + 1) w).comp
    ((populationCountCircuit is.length).comp (literals positive is))

private theorem val_zeroExtend {u w : ℕ} (h : u ≤ w) (x : BitString u) :
    (equivFin w (zeroExtend x) : ℕ) = (equivFin u x : ℕ) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction k with
  | zero => simp [zeroExtend_self]
  | succ k ih =>
    rw [show u + (k + 1) = (u + k) + 1 by omega, val_equivFin_succ,
      init_zeroExtend_succ, ih (by omega)]
    simp [zeroExtend]

private theorem val_eval_groupCount {n : ℕ} (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (P a q w : ℕ)
    (hw : Nat.clog 2 (n + 1) + 1 ≤ w) :
    (equivFin w ((groupCount weights positive P a q w).eval interpretation x) : ℕ) =
      ((group weights P a q).map (fun i => (literal (positive i) (x i)).toNat)).sum := by
  have hg : (group weights P a q).length ≤ n := by
    simpa only [group, List.length_finRange] using List.length_filter_le
      (fun i : Fin n => decide (digit P a (weights i) = q)) (List.finRange n)
  have hl := Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.add_le_add_right hg 1)) 1
  rw [groupCount, Circuit.eval_comp, PopulationCount.eval_pad,
    val_zeroExtend (hl.trans hw), Circuit.eval_comp, val_eval_populationCountCircuit,
    eval_literals, weight_eq_sum_toNat]
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map (group weights P a q)
    (fun i => (literal (positive i) (x i)).toNat)

/-- Multiply one group count by its actual radix contribution. -/
@[expose] def contribution {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P a q w : ℕ) : Circuit signature n w :=
  (Modular.multiply w).comp
    ((groupCount weights positive P a q w).append
      (wordConstCircuit n ((equivFin w).symm ⟨P ^ a * q % 2 ^ w,
        Nat.mod_lt _ (Nat.two_pow_pos _)⟩)))

/-- Complete group traversal and arithmetic reduction. -/
@[expose] def sumCircuit {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P d w : ℕ) : Circuit signature n w :=
  sumPairs n w ((List.range d).flatMap fun a =>
    (List.finRange P).map fun q : Fin P =>
      pairWithZero (contribution weights positive P a q.val w))

private theorem val_eval_contribution {n : ℕ} (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (P a q w : ℕ)
    (hw : Nat.clog 2 (n + 1) + 1 ≤ w) :
    (equivFin w ((contribution weights positive P a q w).eval interpretation x) : ℕ) =
      (P ^ a * q * ((group weights P a q).map
        (fun i => (literal (positive i) (x i)).toNat)).sum) % 2 ^ w := by
  rw [contribution, Circuit.eval_comp, Circuit.eval_append, Modular.val_eval_multiply,
    eval_wordConstCircuit, Equiv.apply_symm_apply, Fin.val_mk,
    val_eval_groupCount weights positive x P a q w hw]
  simp only [Nat.mul_mod, Nat.mod_mod, Nat.mul_comm]

/-- Modular arithmetic loses no bits: the complete output is the original weighted value. -/
theorem val_eval_sumCircuit {n P : ℕ} (hP : 0 < P) (d w : ℕ)
    (weights : Fin n → ℕ) (positive x : Fin n → Bool)
    (hw : Nat.clog 2 (n + 1) + 1 ≤ w) (hweights : ∀ i, weights i < P ^ d)
    (htotal : value weights positive x < 2 ^ w) :
    (equivFin w ((sumCircuit weights positive P d w).eval interpretation x) : ℕ) =
      value weights positive x := by
  rw [sumCircuit, val_eval_sumPairs]
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    pairVal_eval_pairWithZero, val_eval_contribution weights positive x P _ _ w hw,
    Nat.mod_mod]
  rw [List.flatMap_def, List.sum_flatten]
  simp only [List.map_map, Function.comp_def, List.finRange, List.map_ofFn, List.sum_ofFn]
  rw [← List.map_coe_finRange_eq_range]
  simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ q : Fin P,
    P ^ a * q.val * ((group weights P a q).map
      (fun i => (literal (positive i) (x i)).toNat)).sum % 2 ^ w) d]
  let f (p : ℕ × Fin P) := P ^ p.1 * p.2.val * ((group weights P p.1 p.2.val).map
    (fun i => (literal (positive i) (x i)).toNat)).sum
  rw [← Finset.sum_product (Finset.range d) Finset.univ (fun p => f p % 2 ^ w),
    ← Finset.sum_nat_mod, Finset.sum_product]
  dsimp only [f]
  simp only [Nat.mul_assoc]
  simp_rw [← Finset.mul_sum]
  rw [reconstruct hP d weights positive x hweights, Nat.mod_eq_of_lt htotal]

/-- A width derived from input count and fixed coefficient exponent, never supplied as advice. -/
@[expose] def width (n c : ℕ) : ℕ := Nat.clog 2 (n ^ (c + 1) + 1) + 1

/-- The derived word has room for the full total, including the carry and all zero weights. -/
theorem width_budget {n c : ℕ} (weights : Fin n → ℕ) (positive x : Fin n → Bool)
    (hw : ∀ i, weights i ≤ n ^ c) :
    Nat.clog 2 (n + 1) + 1 ≤ width n c ∧ value weights positive x < 2 ^ width n c := by
  have hn : n ≤ n ^ (c + 1) := Nat.le_self_pow (by omega) n
  constructor
  · exact Nat.add_le_add_right (Nat.clog_mono_right 2 (Nat.add_le_add_right hn 1)) 1
  · have hv : value weights positive x ≤ n * n ^ c := by
      unfold value
      calc _ ≤ ∑ _ : Fin n, n ^ c := Finset.sum_le_sum fun i _ => by
              have hb : (literal (positive i) (x i)).toNat ≤ 1 := by
                cases literal (positive i) (x i) <;> decide
              nlinarith [hw i]
        _ = _ := by simp
    have ht := Nat.le_pow_clog Nat.one_lt_two (n ^ (c + 1) + 1)
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
      (Nat.le_succ (Nat.clog 2 (n ^ (c + 1) + 1)))
    unfold width
    rw [pow_succ] at ht
    exact Nat.lt_of_lt_of_le (by nlinarith : value weights positive x <
      2 ^ Nat.clog 2 (n ^ c * n + 1)) (by simpa only [pow_succ] using hp)

private theorem width_height_le (n c : ℕ) : width n c ≤ 2 * (c + 1) * height n + 1 := by
  have hn := (radix_budget n c).2.1
  have hpow := Nat.pow_lt_pow_left hn (by omega : c + 1 ≠ 0)
  have hclog : Nat.clog 2 (n ^ (c + 1) + 1) ≤ 2 * (c + 1) * height n := by
    apply Nat.clog_le_of_le_pow
    have he : (radix n ^ 2) ^ (c + 1) = 2 ^ (2 * (c + 1) * height n) := by
      unfold radix
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    rw [← he]
    omega
  unfold width
  omega

/-- Upper comparison with an arbitrary binary integer target. Negative targets reject directly;
nonnegative targets above the representable range accept directly. -/
@[expose] def leCircuit {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) : Circuit signature n 1 :=
  if target < 0 then Circuit.oneGate (.const false) Fin.elim0
  else if ht : target.toNat < 2 ^ width n c then
    (Boolean.leCircuit (width n c)).comp
      ((sumCircuit weights positive (radix n) (positions c) (width n c)).append
        (wordConstCircuit n ((equivFin (width n c)).symm ⟨target.toNat, ht⟩)))
  else Circuit.oneGate (.const true) Fin.elim0

/-- The actual grouped comparison accepts exactly the original integer inequality. -/
theorem eval_leCircuit {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (positive x : Fin n → Bool) (target : ℤ) (hw : ∀ i, weights i ≤ n ^ c) :
    (leCircuit c weights positive target).eval interpretation x =
      fun _ => decide ((value weights positive x : ℤ) ≤ target) := by
  obtain ⟨hwidth, htotal⟩ := width_budget weights positive x hw
  have hweights : ∀ i, weights i < radix n ^ positions c :=
    fun i => (hw i).trans_lt (radix_budget n c).2.2
  unfold leCircuit
  split_ifs with ht hfit
  · funext j
    simp only [Circuit.eval_oneGate, interpretation]
    exact (decide_eq_false (by omega)).symm
  · rw [Circuit.eval_comp, Circuit.eval_append, Boolean.eval_leCircuit, eval_wordConstCircuit]
    simp only [Equiv.apply_symm_apply, Fin.le_iff_val_le_val]
    rw [val_eval_sumCircuit (by have := (radix_budget n c).1; omega) _ _ weights positive x
      hwidth hweights htotal]
    funext j
    exact decide_eq_decide.mpr (by omega)
  · funext j
    simp only [Circuit.eval_oneGate, interpretation]
    exact (decide_eq_true (by omega)).symm

/-- Every gate of signed-literal extraction, population counting and padding is charged. -/
theorem size_groupCount_le {n : ℕ} (weights : Fin n → ℕ) (positive : Fin n → Bool)
    (P a q w : ℕ) :
    (groupCount weights positive P a q w).size ≤
      464 * (group weights P a q).length + 464 := by
  have hp := size_populationCountCircuit_le (group weights P a q).length
  have hl := size_literals_le positive (group weights P a q)
  simp only [groupCount, Circuit.size_comp, PopulationCount.size_pad]
  omega

/-- Literal groups do not multiply the original inputs: at each digit their total size is n. -/
theorem size_sumCircuit_le {n P : ℕ} (hP : 0 < P) (d w : ℕ)
    (weights : Fin n → ℕ) (positive : Fin n → Bool) :
    (sumCircuit weights positive P d w).size ≤
      464 * d * n + d * P * (467 + 63 * (w + 1) ^ 2 + 40 * w) +
        21 * (w + 1) ^ 2 + 1 := by
  have hcon (a q : ℕ) : (pairWithZero (contribution weights positive P a q w)).size ≤
      464 * (group weights P a q).length + 467 + 63 * (w + 1) ^ 2 := by
    have hg := size_groupCount_le weights positive P a q w
    have hm := Modular.size_multiply_le w
    simp only [size_pairWithZero, contribution, Circuit.size_comp,
      Circuit.size_append, size_wordConstCircuit]
    omega
  let cs := (List.range d).flatMap fun a =>
    (List.finRange P).map fun q : Fin P =>
      pairWithZero (contribution weights positive P a q.val w)
  have hlen : cs.length = d * P := by
    simp [cs, List.length_flatMap]
  have hs : (cs.map Circuit.size).sum ≤
      464 * d * n + d * P * (467 + 63 * (w + 1) ^ 2) := by
    simp only [cs, List.map_flatMap, List.map_map, Function.comp_def]
    rw [List.flatMap_def, List.sum_flatten]
    simp only [List.finRange, List.map_ofFn, Function.comp_def]
    rw [← List.map_coe_finRange_eq_range]
    simp only [List.finRange, List.map_ofFn, List.sum_ofFn, Function.comp_def]
    calc _ ≤ ∑ a : Fin d, ∑ q : Fin P,
        (464 * (group weights P a q).length + 467 + 63 * (w + 1) ^ 2) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun q _ => hcon a q
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sum_group_lengths hP,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring
  have h := size_sumPairs_le cs
  change (sumPairs n w cs).size ≤ _
  rw [hlen] at h
  nlinarith

private theorem height_square_le (h : ℕ) : (h + 1) ^ 2 ≤ 8 * 2 ^ h := by
  have hs : h ^ 2 + 4 * h + 8 ≤ 8 * 2 ^ h := by
    induction h with
    | zero => norm_num
    | succ h ih => rw [pow_succ 2 h]; nlinarith
  nlinarith

private theorem radix_square_le (n : ℕ) : radix n ^ 2 ≤ 8 * (n + 1) := by
  have he : 2 * height n ≤ Nat.clog 2 (n + 1) + 2 := by unfold height; omega
  have h := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) he
  have hp := Nat.pow_clog_le_mul Nat.one_lt_two (Nat.succ_ne_zero n)
  rw [pow_add] at h
  dsimp only [radix]
  rw [← pow_mul, Nat.mul_comm]
  norm_num at h
  nlinarith

/-- Concrete constant for the actual grouped sum, depending only on the coefficient exponent. -/
@[expose] def sumBudget (c : ℕ) : ℕ :=
  464 * positions c + 8 * (positions c * (467 + 824 * (2 * c + 4) ^ 2) +
    168 * (2 * c + 4) ^ 2 + 1)

/-- Uniform explicit linear auxiliary budget for each fixed coefficient exponent.
The bound comes from the actual grouped circuit, not a supplied desired-size contract. -/
theorem size_sumCircuit_linear {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) :
    (sumCircuit weights positive (radix n) (positions c) (width n c)).size ≤
      sumBudget c * (n + 1) := by
  let P := radix n
  let d := positions c
  let w := width n c
  let B := 2 * c + 4
  have hP : 1 ≤ P := by have := (radix_budget n c).1; dsimp only [P]; omega
  have hw : w + 1 ≤ B * (height n + 1) := by
    have h := width_height_le n c
    dsimp only [w, B]
    nlinarith
  have hsq : (w + 1) ^ 2 ≤ 8 * B ^ 2 * P := by
    have h := Nat.pow_le_pow_left hw 2
    have hh := Nat.mul_le_mul_left (B ^ 2) (height_square_le (height n))
    dsimp only [P, radix]
    nlinarith
  have hPsq : P ^ 2 ≤ 8 * (n + 1) := radix_square_le n
  have hmono : P ≤ P ^ 2 := by nlinarith
  have hs := size_sumCircuit_le (by omega : 0 < P) d w weights positive
  have hm1 := Nat.mul_le_mul_left (d * P * 103) hsq
  have hm2 := Nat.mul_le_mul_left 21 hsq
  have hw2 : w ≤ (w + 1) ^ 2 := by nlinarith
  have hpre : (sumCircuit weights positive P d w).size ≤
      464 * d * n + (d * (467 + 824 * B ^ 2) + 168 * B ^ 2 + 1) * P ^ 2 := by
    have hm3 := Nat.mul_le_mul_left (d * 467 + 168 * B ^ 2) hmono
    have hm4 := Nat.mul_le_mul_left (d * P * 40) hw2
    nlinarith
  have hfinal := Nat.mul_le_mul_left
    (d * (467 + 824 * B ^ 2) + 168 * B ^ 2 + 1) hPsq
  dsimp only [P, d, w, B] at hpre hfinal
  unfold sumBudget
  nlinarith

/-- The actual derived width is logarithmic, and in particular has this simple linear bound. -/
theorem width_le (n c : ℕ) : width n c ≤ (4 * c + 5) * (n + 1) := by
  have hl : Nat.clog 2 (n + 1) ≤ n + 1 :=
    Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
  have hh : height n ≤ n + 1 := by unfold height; omega
  have h := width_height_le n c
  nlinarith

/-- The comparator and all constant gates retain the linear total budget, even for huge targets. -/
theorem size_leCircuit_linear {n : ℕ} (c : ℕ) (weights : Fin n → ℕ)
    (positive : Fin n → Bool) (target : ℤ) :
    (leCircuit c weights positive target).size ≤
      (sumBudget c + 5 * (4 * c + 5) + 3) * (n + 1) := by
  have hs := size_sumCircuit_linear c weights positive
  have hw := width_le n c
  unfold leCircuit
  split_ifs <;> simp only [Circuit.size_oneGate, Circuit.size_comp, Circuit.size_append,
    Boolean.size_leCircuit, size_wordConstCircuit] <;> nlinarith

end Cslib.Circuits.Boolean.WeightedSum
