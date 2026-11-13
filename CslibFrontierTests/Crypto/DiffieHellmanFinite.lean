/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Fixed-group discrete-logarithm and Diffie–Hellman experiments: checked instances

Concrete checks for the typed experiments of
`CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean`, first in any `ZMod q`-module `G`
on which `c ↦ c • g` is injective, then in `ZMod 5` with `g = 1`:

* Guessing the exponent `0` has discrete-logarithm advantage `1 / q`. In `ZMod 5`, returning the
  challenge itself always wins, and `dlToCDH` turns it into a CDH adversary that always wins.
* The identity test, which accepts when the first and third elements are `0`, accepts with
  probability `1 / q` in the real DDH world and `1 / q²` in the random one. Its DDH advantage in
  `ZMod 5` is `1 / 5 - 1 / 25 = 4 / 25`.
* A distinguisher that ignores its input has DDH advantage `0`.
* `cdhAdvantage_le_ddhAdvantage_cdhToDDH_add` applies in `ZMod 5`.
-/

namespace CslibFrontierTests.Crypto.DiffieHellmanFinite

open Cslib Cslib.Probability Cslib.Crypto
open scoped NNReal ENNReal

section General

variable {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)

/-- Guessing the exponent `0` wins the discrete-logarithm experiment with probability `1 / q`,
whatever the group. -/
theorem dlAdvantage_const_zero : dlAdvantage q g (fun _ => pure 0) = (q : ℝ≥0)⁻¹ := by
  simp only [dlAdvantage, dlExperiment, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- A distinguisher that ignores its input has DDH advantage `0`. -/
theorem ddhAdvantage_const (p : ProbComp Bool) :
    ddhAdvantage q g (fun _ _ _ => p) = 0 := by
  simp only [ddhAdvantage, ddhRealExperiment, ddhRandomExperiment, ProbComp.eval_bind,
    PMF.bind_const, Game.advantage_self]

variable {q g}

omit [NeZero q] in
/-- When `c ↦ c • g` is injective, `c • g = 0` exactly when `c = 0`. -/
theorem smul_eq_zero_iff (hg : Function.Injective fun c : ZMod q => c • g) (c : ZMod q) :
    c • g = 0 ↔ c = 0 :=
  ⟨fun h => hg (h.trans (zero_smul (ZMod q) g).symm), fun h => h ▸ zero_smul (ZMod q) g⟩

variable [DecidableEq G]

/-- Accept when the first and third elements are both `0`. -/
noncomputable def identityTest (u _v w : G) : ProbComp Bool :=
  pure (decide (u = 0 ∧ w = 0))

/-- In the real DDH world the identity test accepts exactly when `a = 0`, with probability
`1 / q`. -/
theorem succProbability_ddhRealExperiment_identityTest
    (hg : Function.Injective fun c : ZMod q => c • g) :
    Game.succProbability (ProbComp.eval (ddhRealExperiment q g identityTest)) =
      (q : ℝ≥0)⁻¹ := by
  have h (a b : ZMod q) : (a = 0 ∧ a * b = 0) ↔ 0 = a :=
    ⟨fun h => h.1.symm, fun ha => ⟨ha.symm, by rw [← ha, zero_mul]⟩⟩
  simp only [ddhRealExperiment, identityTest, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, smul_eq_zero_iff hg, h, PMF.bind_const]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-- In the random DDH world the identity test accepts exactly when `a = c = 0`, with probability
`1 / q²`. -/
theorem succProbability_ddhRandomExperiment_identityTest
    (hg : Function.Injective fun c : ZMod q => c • g) :
    Game.succProbability (ProbComp.eval (ddhRandomExperiment q g identityTest)) =
      (q : ℝ≥0)⁻¹ ^ 2 := by
  simp only [ddhRandomExperiment, identityTest, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, smul_eq_zero_iff hg, PMF.bind_const]
  rw [Game.succProbability, ← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_inv,
    ← ENNReal.toNNReal_pow]
  congr 1
  simp [PMF.bind_apply, tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply, ite_and,
    Finset.sum_ite_eq', sq]

end General

/-! ### The group `ZMod 5` with generator `1` -/

theorem zmod5_injective : Function.Injective fun c : ZMod 5 => c • (1 : ZMod 5) := by
  intro a b h
  simpa using h

example : dlAdvantage 5 (1 : ZMod 5) (fun _ => pure 0) = 1 / 5 := by
  rw [dlAdvantage_const_zero, one_div, Nat.cast_ofNat]

/-- In `ZMod 5` with `g = 1`, the challenge `a • 1` is `a`, so returning it always wins. -/
theorem dlAdvantage_zmod5_id : dlAdvantage 5 (1 : ZMod 5) pure = 1 := by
  simp only [dlAdvantage, dlExperiment, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    smul_eq_mul, mul_one, decide_true, PMF.bind_const]
  simp [Game.succProbability]

example : 1 ≤ cdhAdvantage 5 (1 : ZMod 5) (dlToCDH pure) :=
  dlAdvantage_zmod5_id ▸ dlAdvantage_le_cdhAdvantage_dlToCDH 5 1 pure

example : Game.succProbability (ProbComp.eval (ddhRealExperiment 5 (1 : ZMod 5) identityTest)) =
    1 / 5 := by
  rw [succProbability_ddhRealExperiment_identityTest zmod5_injective, one_div, Nat.cast_ofNat]

example :
    Game.succProbability (ProbComp.eval (ddhRandomExperiment 5 (1 : ZMod 5) identityTest)) =
      1 / 25 := by
  rw [succProbability_ddhRandomExperiment_identityTest zmod5_injective]
  norm_num

/-- The identity test has DDH advantage `1 / 5 - 1 / 25 = 4 / 25` in `ZMod 5`. -/
example : ddhAdvantage 5 (1 : ZMod 5) identityTest = 4 / 25 := by
  apply NNReal.eq
  rw [ddhAdvantage, Game.coe_advantage,
    succProbability_ddhRealExperiment_identityTest zmod5_injective,
    succProbability_ddhRandomExperiment_identityTest zmod5_injective]
  norm_num

example (p : ProbComp Bool) : ddhAdvantage 5 (1 : ZMod 5) (fun _ _ _ => p) = 0 :=
  ddhAdvantage_const 5 1 p

example (A : ZMod 5 → ZMod 5 → ProbComp (ZMod 5)) :
    cdhAdvantage 5 (1 : ZMod 5) A ≤ ddhAdvantage 5 1 (cdhToDDH A) + 1 / 5 := by
  simpa using cdhAdvantage_le_ddhAdvantage_cdhToDDH_add 5 (1 : ZMod 5) zmod5_injective A

end CslibFrontierTests.Crypto.DiffieHellmanFinite
