/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Algebra.Order.Field.Rat
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Probability.UniformNat

/-!
# Exact rational probabilities and Bernoulli coins in `ProbComp`

Every closed `ProbComp` program is a finite tree of uniform `Fin (n + 1)` choices, so the mass it
assigns to any output is a rational number in `[0, 1]`, computed structurally by `ProbComp.evalRat`
without passing through `ℝ≥0∞` (`ProbComp.coe_evalRat_eq_toReal_eval`,
`ProbComp.eval_eq_iff_evalRat_eq`). Conversely, `ProbComp.bernoulliRat p` samples a single
`Fin q.den` draw (`q = min (max p 0) 1`) to realize any clamped rational acceptance probability
`p ∈ ℚ` without rejection loops (`ProbComp.toReal_eval_bernoulliRat_true`).

## Main definitions

* `Cslib.ProbComp.evalRat`: exact rational output probability of a closed `ProbComp` program.
* `Cslib.ProbComp.bernoulliRat`: exact clamped rational Bernoulli coin in `ProbComp Bool`.

## Main results

* `Cslib.ProbComp.coe_evalRat_eq_toReal_eval`: `(evalRat M a : ℝ) = (eval M a).toReal`.
* `Cslib.ProbComp.evalRat_eq_of_eval_eq`, `Cslib.ProbComp.eval_eq_iff_evalRat_eq`: equality of
  `ProbComp.eval` laws is equivalent to pointwise equality of `evalRat`.
* `Cslib.ProbComp.evalRat_nonneg`, `Cslib.ProbComp.evalRat_le_one`,
  `Cslib.ProbComp.evalRat_unifFin`, `Cslib.ProbComp.evalRat_uniform`,
  `Cslib.ProbComp.evalRat_bind`, `Cslib.ProbComp.evalRat_map`: range bounds and structural laws of
  `evalRat`.
* `Cslib.ProbComp.eval_bernoulliRat_true`, `Cslib.ProbComp.toReal_eval_bernoulliRat_true`,
  `Cslib.ProbComp.evalRat_bernoulliRat_true`, `Cslib.ProbComp.evalRat_bernoulliRat_false`:
  exact `ℝ≥0∞`, `ℝ`, and `ℚ` outcome probabilities of `bernoulliRat`.
-/

public section

open scoped ENNReal

namespace Cslib.ProbComp

open Probability

variable {α : Type}

/-- The exact rational probability with which the closed program `M` outputs `a`, computed by
recursion on its finite tree of `unifFin` calls. -/
@[expose] def evalRat [DecidableEq α] : ProbComp α → α → ℚ
  | .pure b, a => if a = b then 1 else 0
  | .liftBind n cont, a => ((n + 1 : ℚ))⁻¹ * ∑ k : Fin (n + 1), evalRat (cont k) a

@[simp] theorem evalRat_pure [DecidableEq α] (b a : α) :
    evalRat (pure b : ProbComp α) a = if a = b then 1 else 0 := by
  rfl

/-- `evalRat` agrees with the real-valued `PMF` semantics `(ProbComp.eval M a).toReal`. -/
theorem coe_evalRat_eq_toReal_eval [DecidableEq α] (M : ProbComp α) (a : α) :
    ((evalRat M a : ℚ) : ℝ) = (eval M a).toReal := by
  induction M with
  | pure b =>
    by_cases h : a = b <;> simp [evalRat, h, PMF.pure_apply]
  | liftBind n cont ih =>
    change ((((n + 1 : ℚ))⁻¹ * ∑ k : Fin (n + 1), evalRat (cont k) a : ℚ) : ℝ) =
      (eval (unifFin n >>= cont) a).toReal
    rw [eval_bind, eval_unifFin, PMF.bind_apply_toReal]
    push_cast
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, ENNReal.toReal_inv, Nat.cast_add,
      Nat.cast_one, ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top,
      ENNReal.toReal_natCast, ENNReal.toReal_one, Finset.mul_sum, ih]

/-- Programs with equal `ProbComp.eval` distributions have equal rational probabilities at every
outcome. -/
theorem evalRat_eq_of_eval_eq [DecidableEq α] {M N : ProbComp α} (h : eval M = eval N) (a : α) :
    evalRat M a = evalRat N a := by
  have hR : ((evalRat M a : ℚ) : ℝ) = ((evalRat N a : ℚ) : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval, coe_evalRat_eq_toReal_eval, h]
  exact_mod_cast hR

/-- Two closed `ProbComp` programs have the same `PMF` law if and only if they assign the same
rational probability to every outcome. -/
theorem eval_eq_iff_evalRat_eq [DecidableEq α] {M N : ProbComp α} :
    eval M = eval N ↔ ∀ a, evalRat M a = evalRat N a := by
  refine ⟨evalRat_eq_of_eval_eq, fun h => ?_⟩
  ext a
  rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top (eval M) a),
    ← ENNReal.ofReal_toReal (PMF.apply_ne_top (eval N) a),
    ← coe_evalRat_eq_toReal_eval, ← coe_evalRat_eq_toReal_eval, h a]

theorem evalRat_nonneg [DecidableEq α] (M : ProbComp α) (a : α) : 0 ≤ evalRat M a := by
  exact_mod_cast (coe_evalRat_eq_toReal_eval M a).symm ▸ ENNReal.toReal_nonneg

theorem evalRat_le_one [DecidableEq α] (M : ProbComp α) (a : α) : evalRat M a ≤ 1 := by
  have h : ((evalRat M a : ℚ) : ℝ) ≤ (1 : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval]
    exact PMF.toReal_apply_le_one (eval M) a
  exact_mod_cast h

@[simp] theorem evalRat_unifFin (n : ℕ) (k : Fin (n + 1)) :
    evalRat (unifFin n) k = ((n + 1 : ℚ))⁻¹ := by
  have h : ((evalRat (unifFin n) k : ℚ) : ℝ) = ((((n + 1 : ℚ))⁻¹ : ℚ) : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval, eval_unifFin, PMF.uniformOfFintype_apply, Fintype.card_fin,
      ENNReal.toReal_inv, Nat.cast_add, Nat.cast_one,
      ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top, ENNReal.toReal_natCast,
      ENNReal.toReal_one]
    push_cast
    rfl
  exact_mod_cast h

@[simp] theorem evalRat_uniform [Fintype α] [Nonempty α] [DecidableEq α] (a : α) :
    evalRat (ProbComp.uniform α) a = (Fintype.card α : ℚ)⁻¹ := by
  have h : ((evalRat (ProbComp.uniform α) a : ℚ) : ℝ) = (((Fintype.card α : ℚ)⁻¹ : ℚ) : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval, eval_uniform, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, Rat.cast_inv, Rat.cast_natCast]
  exact_mod_cast h

theorem evalRat_bind {β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (M : ProbComp α) (f : α → ProbComp β) (b : β) :
    evalRat (M >>= f) b = ∑ a : α, evalRat M a * evalRat (f a) b := by
  have h : ((evalRat (M >>= f) b : ℚ) : ℝ) =
      ((∑ a : α, evalRat M a * evalRat (f a) b : ℚ) : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval, eval_bind, PMF.bind_apply_toReal]
    push_cast
    simp only [coe_evalRat_eq_toReal_eval]
  exact_mod_cast h

theorem evalRat_map {β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) (M : ProbComp α) (b : β) :
    evalRat (f <$> M) b = ∑ a : α, if b = f a then evalRat M a else 0 := by
  rw [← bind_pure_comp, evalRat_bind]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : b = f a <;> simp [h]

/-- Flip a biased coin with clamped rational acceptance probability `min (max p 0) 1` using one
uniform draw from `Fin q.den`. -/
@[expose] def bernoulliRat (p : ℚ) : ProbComp Bool :=
  let q := min (max p 0) 1
  (fun u : Fin q.den => decide (u.val < q.num.toNat)) <$>
    (Fin.cast (Nat.sub_add_cancel q.den_pos) <$> unifFin (q.den - 1))

/-- Exact `ℝ≥0∞` acceptance probability of `bernoulliRat p`. -/
theorem eval_bernoulliRat_true (p : ℚ) :
    eval (bernoulliRat p) true =
      ((min (max p 0) 1).num.toNat : ℝ≥0∞) / (min (max p 0) 1).den := by
  set q := min (max p 0) 1
  have hq0 : 0 ≤ q := le_min (le_max_right p 0) zero_le_one
  have hq1 : q ≤ 1 := min_le_right (max p 0) 1
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hden_pos : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hnum_le_real : (q.num : ℝ) ≤ q.den := by
    have hqr : (q : ℝ) ≤ 1 := by exact_mod_cast hq1
    have hdiv : (q.num : ℝ) / q.den ≤ 1 := by simpa [Rat.cast_def] using hqr
    exact (div_le_one hden_pos).mp hdiv
  have hnum_le_int : q.num ≤ q.den := by exact_mod_cast hnum_le_real
  have hnum_le : q.num.toNat ≤ q.den := by omega
  let _ : NeZero q.den := ⟨q.den_pos.ne'⟩
  have hcast :
      eval (Fin.cast (Nat.sub_add_cancel q.den_pos) <$> unifFin (q.den - 1)) =
        PMF.uniformOfFintype (Fin q.den) := by
    rw [eval_map, eval_unifFin]
    exact PMF.uniformOfFintype_map_equiv (finCongr (Nat.sub_add_cancel q.den_pos))
  rw [bernoulliRat, eval_map]
  change (eval (Fin.cast (Nat.sub_add_cancel q.den_pos) <$> unifFin (q.den - 1))).map
    (fun u : Fin q.den => decide (u.val < q.num.toNat)) true = _
  rw [hcast, uniformFin_decide_lt, Nat.min_eq_right hnum_le]

/-- Exact real acceptance probability of `bernoulliRat p`: `min (max (p : ℝ) 0) 1`. -/
theorem toReal_eval_bernoulliRat_true (p : ℚ) :
    (eval (bernoulliRat p) true).toReal = min (max (p : ℝ) 0) 1 := by
  set q := min (max p 0) 1
  have hq0 : 0 ≤ q := le_min (le_max_right p 0) zero_le_one
  have hnum0 : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  rw [eval_bernoulliRat_true, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  have hcast_n : (q.num.toNat : ℝ) = (q.num : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hnum0
  rw [hcast_n, ← Rat.cast_def]
  simp [q]

theorem toReal_eval_bernoulliRat_true_of_mem_Icc {p : ℚ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (eval (bernoulliRat p) true).toReal = (p : ℝ) := by
  rw [toReal_eval_bernoulliRat_true, max_eq_left (by exact_mod_cast hp0),
    min_eq_left (by exact_mod_cast hp1)]

/-- Complementary `false` probability of `bernoulliRat p`. -/
theorem toReal_eval_bernoulliRat_false (p : ℚ) :
    (eval (bernoulliRat p) false).toReal = 1 - min (max (p : ℝ) 0) 1 := by
  rw [PMF.toReal_false_eq_one_sub, toReal_eval_bernoulliRat_true]

@[simp] theorem evalRat_bernoulliRat_true (p : ℚ) :
    evalRat (bernoulliRat p) true = min (max p 0) 1 := by
  have h : ((evalRat (bernoulliRat p) true : ℚ) : ℝ) = ((min (max p 0) 1 : ℚ) : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval, toReal_eval_bernoulliRat_true]
    simp
  exact_mod_cast h

@[simp] theorem evalRat_bernoulliRat_false (p : ℚ) :
    evalRat (bernoulliRat p) false = 1 - min (max p 0) 1 := by
  have h : ((evalRat (bernoulliRat p) false : ℚ) : ℝ) = ((1 - min (max p 0) 1 : ℚ) : ℝ) := by
    rw [coe_evalRat_eq_toReal_eval, toReal_eval_bernoulliRat_false]
    simp
  exact_mod_cast h

/-- When `1 ≤ p`, `bernoulliRat p` outputs `true` with probability `1`. -/
theorem eval_bernoulliRat_of_one_le {p : ℚ} (hp : 1 ≤ p) :
    eval (bernoulliRat p) = PMF.pure true := by
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hmax : max (p : ℝ) 0 = p := max_eq_left (zero_le_one.trans hpR)
  have hmin : min (max (p : ℝ) 0) 1 = 1 := by rw [hmax]; exact min_eq_right hpR
  ext b
  rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]
  cases b
  · rw [toReal_eval_bernoulliRat_false, hmin, sub_self, ENNReal.ofReal_zero, PMF.pure_apply,
      ite_eq_right Bool.false_ne_true]
  · rw [toReal_eval_bernoulliRat_true, hmin, ENNReal.ofReal_one, PMF.pure_apply, ite_eq_left rfl]

end Cslib.ProbComp
