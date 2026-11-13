/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

import CslibFrontier.Crypto.Protocols.PIR.Cube
import CslibFrontier.Crypto.Protocols.PIR.SmoothConverse
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests: smooth codes from private information retrieval (`PIR.SmoothConverse`)

* `ProbComp.evalRat` and `ProbComp.bernoulliRat` compute exact rational outcome probabilities
  (including clamping outside `[0, 1]`).
* On `twoServer (Fin 3)`, every server-query pair has replication count `2`, `SmoothPos` has exact
  cardinality `32 ≤ 6 · 8 = 48`, `smoothCode` is a linear code (`smoothCodeAddHom`),
  `smoothDecoder` preserves the exact output law `PMF.pure (x i)`
  (`decodeLaw_smoothDecoder_of_isPrivate`), and gives a `(2, 3, 1 / 2)`-smooth decoder
  (`isSmoothDecoder_smoothDecoder_of_isCorrect`).
* A genuinely noisy, imperfectly private two-server scheme `noisyTwoServer` (`δ = 1 / 8 > 0`,
  `ε = 3 / 8 < 1 / 2`, satisfying `¬ IsPrivate` and `¬ IsCorrect`) yields a nonvacuous
  `(2, 3, 1 / 4)`-smooth decoder via `isSmoothDecoder_smoothDecoder_two`.
* A two-server scheme with `2`-bit answers (`Fin 2 → Bool`) whose reconstruction reads only the
  predetermined coordinate `{0}` satisfies `smoothDecoder_eq_of_predetermined` (GKST Lemma 7.1,
  item 2).
* The single-server smooth-converse bounds (`card_mul_sq_le_card_answer_sub_one_of_isPrivate` and
  `card_mul_sq_le_card_answer_sub_one_of_statPrivate`) rule out `1`-bit-answer one-server schemes
  with high imperfect recovery (`9 / 10` on `Fin 9` under perfect privacy, and `9 / 10` on `Fin 16`
  under `1 / 5`-statistical privacy), where `SingleServer.two_pow_card_le_card_answer` does not
  apply.
-/

namespace CslibFrontierTests.Crypto.PIRSmoothConverse

open scoped ENNReal BigOperators
open Cslib Cslib.Crypto.Protocols.PIR Cslib.BitString Cslib.Code Probability

/-! ### Exact rational `ProbComp` evaluation and Bernoulli sampling -/

example : ProbComp.evalRat (ProbComp.bernoulliRat (3 / 7)) true = 3 / 7 := by simp; norm_num

example : ProbComp.evalRat (ProbComp.bernoulliRat (3 / 7)) false = 4 / 7 := by simp; norm_num

example : ProbComp.evalRat (ProbComp.bernoulliRat (-1 / 3)) true = 0 := by simp; norm_num

example : ProbComp.evalRat (ProbComp.bernoulliRat (5 / 4)) true = 1 := by simp; norm_num

example : ProbComp.evalRat (ProbComp.uniform (Fin 5)) (2 : Fin 5) = 1 / 5 := by simp

example :
    ProbComp.evalRat (do
      let b ← ProbComp.bernoulliRat (1 / 3)
      if b then ProbComp.bernoulliRat (1 / 2) else pure false) true = 1 / 6 := by
  rw [ProbComp.evalRat_bind, Fintype.sum_bool]
  simp
  norm_num

example :
    (ProbComp.eval (ProbComp.bernoulliRat (3 / 7)) true).toReal = 3 / 7 := by
  rw [ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc (by norm_num) (by norm_num)]
  norm_num

/-! ### Perfectly private two-server XOR PIR → `(2, 3, 1 / 2)`-smooth linear code -/

theorem smoothCopies_twoServer_fin3 (sq : Bool × (Fin 3 → Bool)) :
    smoothCopies (twoServer (Fin 3)) 0 sq = 2 := by
  have heval : ProbComp.evalRat ((twoServer (Fin 3)).serverQuery sq.1 0) sq.2 = 1 / 8 := by
    rw [ProbComp.evalRat_eq_of_eval_eq (N := ProbComp.uniform (Fin 3 → Bool))
      (by rw [eval_serverQuery_twoServer, ProbComp.eval_uniform])]
    simp
  rw [smoothCopies_eq, heval]
  norm_num

/-- A deterministic query scheme assigns zero probability `p₀ = 0` to unqueried symbols, exercising
the `max 1 0 = 1` clamping branch of `smoothCopies`. -/
private noncomputable def deterministicQueryScheme : Scheme (Fin 2) Unit Unit Bool Bool where
  query _ := pure ((), fun _ => false)
  answer _ x _ := x 0
  reconstruct _ _ a := a ()

example : smoothCopies deterministicQueryScheme 0 ((), true) = 1 := by
  have heval : ProbComp.evalRat (deterministicQueryScheme.serverQuery () 0) true = 0 := by
    rw [ProbComp.evalRat_eq_of_eval_eq (N := pure false)
      (by simp [Scheme.eval_serverQuery, deterministicQueryScheme])]
    simp
  rw [smoothCopies_eq, heval]
  simp

example : Fintype.card (SmoothPos (twoServer (Fin 3)) 0) = 32 := by
  rw [Fintype.card_sigma]
  simp [smoothCopies_twoServer_fin3]

example : Fintype.card (SmoothPos (twoServer (Fin 3)) 0) ≤ 48 := by
  have h := card_smoothPos_le_six_mul (twoServer (Fin 3)) Fintype.card_bool 0
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h
  omega

/-- `twoServer (Fin 3)` has `GF(2)`-additive answers, so `smoothCodeAddHom` packages its smooth code
as an `AddMonoidHom` (GKST Lemma 7.1, item 1). -/
noncomputable def twoServerSmoothAddHom :
    (Fin 3 → Bool) →+ (SmoothPos (twoServer (Fin 3)) 0 → Bool) :=
  smoothCodeAddHom (twoServer (Fin 3))
    (fun _ q => by simp [twoServer, hadamardCode_apply])
    (fun _ x y q => by simp [twoServer, hadamardCode_apply, add_dotProduct])
    0

example (x y : Fin 3 → Bool) :
    twoServerSmoothAddHom (x + y) = twoServerSmoothAddHom x + twoServerSmoothAddHom y :=
  twoServerSmoothAddHom.map_add x y

example :
    IsSmoothDecoder (smoothCode (twoServer (Fin 3)) 0) 2 3 (1 / 2)
      (smoothDecoder (twoServer (Fin 3)) 0) := by
  have h := isSmoothDecoder_smoothDecoder_of_isCorrect (twoServer (Fin 3))
    isCorrect_twoServer isPrivate_twoServer 0
  rw [Fintype.card_bool] at h
  have hc : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
  rwa [hc] at h

example (x : Fin 3 → Bool) (i : Fin 3) :
    decodeLaw (smoothDecoder (twoServer (Fin 3)) 0 i) (smoothCode (twoServer (Fin 3)) 0 x) =
      PMF.pure (x i) := by
  rw [decodeLaw_smoothDecoder_of_isPrivate (twoServer (Fin 3)) isPrivate_twoServer 0 x i,
    (twoServer (Fin 3)).isCorrect_iff_eval_run.mp isCorrect_twoServer x i]

/-! ### Nonvacuity for `δ > 0` and `ε < 1 / 2`: noisy, statistically-private two-server PIR -/

/-- A two-server scheme on `Fin 2` that runs `twoServer (Fin 2)` with probability `7 / 8` and
otherwise leaks `eᵢ` to both servers while outputting `false`. It is neither perfectly private nor
perfectly correct, yet is `(1 - 1 / 8)`-statistically-private with recovery probability `≥ 7 / 8`
(`ε = 3 / 8`), giving a `(2, 3, 1 / 4)`-smooth code via GKST Lemma 7.1. -/
noncomputable def noisyTwoServer : Scheme (Fin 2) Bool Bool (Fin 2 → Bool) Bool where
  query i := do
    let honest ← ProbComp.bernoulliRat (7 / 8)
    if honest then
      let (_, q) ← (twoServer (Fin 2)).query i
      pure (true, q)
    else
      pure (false, fun _ => Pi.single i true)
  answer := (twoServer (Fin 2)).answer
  reconstruct _ honest a := if honest then a false + a true else false

private theorem serverQuery_noisyTwoServer_eval (s : Bool) (i : Fin 2) :
    ProbComp.eval (noisyTwoServer.serverQuery s i) =
      (ProbComp.eval (ProbComp.bernoulliRat (7 / 8))).bind fun honest =>
        if honest then PMF.uniformOfFintype (Fin 2 → Bool)
        else PMF.pure (Pi.single i true) := by
  rw [Scheme.eval_serverQuery]
  simp only [noisyTwoServer, ProbComp.eval_bind, PMF.map_bind]
  refine congrArg (ProbComp.eval (ProbComp.bernoulliRat (7 / 8))).bind (funext fun honest => ?_)
  cases honest
  · simp [ProbComp.eval_pure]
  · simp only [↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    rw [← eval_serverQuery_twoServer s i, Scheme.eval_serverQuery]
    rfl

private theorem run_noisyTwoServer_eval (x : Fin 2 → Bool) (i : Fin 2) :
    ProbComp.eval (noisyTwoServer.run x i) =
      (ProbComp.eval (ProbComp.bernoulliRat (7 / 8))).bind fun honest =>
        if honest then PMF.pure (x i) else PMF.pure false := by
  rw [Scheme.eval_run]
  simp only [noisyTwoServer, ProbComp.eval_bind, PMF.map_bind]
  refine congrArg (ProbComp.eval (ProbComp.bernoulliRat (7 / 8))).bind (funext fun honest => ?_)
  cases honest
  · simp [ProbComp.eval_pure]
  · simp only [↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    have hcorr := (twoServer (Fin 2)).isCorrect_iff_eval_run.mp isCorrect_twoServer x i
    rw [Scheme.eval_run] at hcorr
    exact hcorr

theorem not_isPrivate_noisyTwoServer : ¬ noisyTwoServer.IsPrivate := by
  intro hpriv
  have h := congrArg (fun μ => (μ (Pi.single (0 : Fin 2) true)).toReal)
    (hpriv.eval_serverQuery_eq false 0 1)
  have hne : (Pi.single (0 : Fin 2) true : Fin 2 → Bool) ≠ Pi.single 1 true := by decide
  simp only [serverQuery_noisyTwoServer_eval, PMF.bind_apply, tsum_fintype, Fintype.sum_bool,
    ↓reduceIte, Bool.false_eq_true, PMF.uniformOfFintype_apply, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, PMF.pure_apply, hne, mul_one, mul_zero, add_zero] at h
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (by simp))
    (PMF.apply_ne_top _ _), ENNReal.toReal_mul,
    ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc (by norm_num) (by norm_num),
    ProbComp.toReal_eval_bernoulliRat_false] at h
  norm_num at h

theorem not_isCorrect_noisyTwoServer : ¬ noisyTwoServer.IsCorrect := by
  intro hcorr
  have h := congrArg (fun μ => (μ false).toReal)
    (noisyTwoServer.isCorrect_iff_eval_run.mp hcorr (fun _ => true) 0)
  simp only [run_noisyTwoServer_eval, PMF.bind_apply, tsum_fintype, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true, PMF.pure_apply, mul_zero, mul_one, zero_add,
    ProbComp.toReal_eval_bernoulliRat_false, ENNReal.toReal_zero] at h
  norm_num at h

private theorem closeTo_noisyTwoServer (s : Bool) (i i' : Fin 2) :
    CloseTo (ProbComp.eval (noisyTwoServer.serverQuery s i))
      (ProbComp.eval (noisyTwoServer.serverQuery s i')) (ENNReal.ofReal (1 / 8)) := by
  intro E
  rw [serverQuery_noisyTwoServer_eval, serverQuery_noisyTwoServer_eval,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply, tsum_fintype, tsum_fintype,
    Fintype.sum_bool, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  have hfalse : ProbComp.eval (ProbComp.bernoulliRat (7 / 8)) false = ENNReal.ofReal (1 / 8) := by
    rw [← ENNReal.ofReal_toReal (PMF.apply_ne_top _ _), ProbComp.toReal_eval_bernoulliRat_false]
    norm_num
  rw [hfalse]
  have hle1 : (PMF.pure (Pi.single i true)).toOuterMeasure E ≤ 1 :=
    PMF.toOuterMeasure_le_one _ E
  calc ProbComp.eval (ProbComp.bernoulliRat (7 / 8)) true *
          (PMF.uniformOfFintype (Fin 2 → Bool)).toOuterMeasure E +
          ENNReal.ofReal (1 / 8) * (PMF.pure (Pi.single i true)).toOuterMeasure E
      ≤ ProbComp.eval (ProbComp.bernoulliRat (7 / 8)) true *
          (PMF.uniformOfFintype (Fin 2 → Bool)).toOuterMeasure E + ENNReal.ofReal (1 / 8) * 1 := by
        gcongr
    _ ≤ (ProbComp.eval (ProbComp.bernoulliRat (7 / 8)) true *
          (PMF.uniformOfFintype (Fin 2 → Bool)).toOuterMeasure E +
          ENNReal.ofReal (1 / 8) * (PMF.pure (Pi.single i' true)).toOuterMeasure E) +
          ENNReal.ofReal (1 / 8) := by
        rw [mul_one]
        gcongr
        exact le_self_add

private theorem recovery_noisyTwoServer (x : Fin 2 → Bool) (i : Fin 2) :
    1 / 2 + (3 / 8 : ℝ) ≤ (ProbComp.eval (noisyTwoServer.run x i) (x i)).toReal := by
  rw [run_noisyTwoServer_eval, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, PMF.pure_apply, mul_one]
  rw [ENNReal.toReal_add (PMF.apply_ne_top _ _)
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (by split_ifs <;> simp)),
    ProbComp.toReal_eval_bernoulliRat_true_of_mem_Icc (by norm_num) (by norm_num)]
  rw [show ((7 / 8 : ℚ) : ℝ) = 1 / 2 + 3 / 8 by norm_num]
  exact le_add_of_nonneg_right ENNReal.toReal_nonneg

/-- GKST Lemma 7.1 turns `noisyTwoServer` into a `(2, 3, 1 / 4)`-smooth decoder. -/
example :
    IsSmoothDecoder (smoothCode noisyTwoServer 0) 2 3 (1 / 4)
      (smoothDecoder noisyTwoServer 0) := by
  have h := isSmoothDecoder_smoothDecoder_two noisyTwoServer Fintype.card_bool 0
    (δ := 1 / 8) (ε := 3 / 8) (by norm_num)
    (fun s i => closeTo_noisyTwoServer s i 0)
    recovery_noisyTwoServer
  have hsub : (3 / 8 : ℝ) - 1 / 8 = 1 / 4 := by norm_num
  rwa [hsub] at h

/-! ### Predetermined answer coordinates (GKST Lemma 7.1, item 2) -/

/-- Two-server scheme returning `2`-bit answers (`Fin 2 → Bool`) whose reconstruction inspects only
coordinate `0` (`{0} : Finset (Fin 2)`), ignoring coordinate `1`. -/
noncomputable def paddedTwoServer : Scheme (Fin 3) Bool Unit (Fin 3 → Bool) (Fin 2 → Bool) where
  query := (twoServer (Fin 3)).query
  answer s x q := ![(twoServer (Fin 3)).answer s x q, x 0]
  reconstruct _ _ a := a false 0 + a true 0

example (i : Fin 3) :
    smoothDecoder paddedTwoServer 0 i = (do
      let st ← ProbOracleComp.sample (smoothCoins paddedTwoServer 0 i)
      if h : ∀ idx, (st.slots idx).isSome then
        let ans ← readAll fun idx => (st.slots idx).get (h idx)
        let masked : Bool → Fin 2 → Bool := fun s b =>
          if b ∈ ({0} : Finset (Fin 2)) then ans (Fintype.equivFin Bool s) b else false
        pure (paddedTwoServer.reconstruct i st.state masked)
      else
        pure st.guess) :=
  smoothDecoder_eq_of_predetermined paddedTwoServer 0 (fun _ _ _ => {0}) false
    (fun _ _ a a' h => by
      simp only [paddedTwoServer]
      rw [h false 0 (Finset.mem_singleton_self 0), h true 0 (Finset.mem_singleton_self 0)]) i

/-! ### Noisy and statistically-private single-server impossibility bounds -/

/-- No perfectly private one-server PIR scheme on `Fin 9` with `1`-bit (`Bool`) answers can recover
every bit with probability at least `9 / 10` (`1 / 2 + 2 / 5`). -/
example {R Q : Type} [Finite Q] (P : Scheme (Fin 9) Unit R Q Bool) (hpriv : P.IsPrivate) :
    ¬ ∀ x i, (9 / 10 : ℝ) ≤ (ProbComp.eval (P.run x i) (x i)).toReal := by
  intro hrec
  have hrec' : ∀ x i, 1 / 2 + (2 / 5 : ℝ) ≤ (ProbComp.eval (P.run x i) (x i)).toReal :=
    fun x i => by linarith [hrec x i]
  have h := card_mul_sq_le_card_answer_sub_one_of_isPrivate P hpriv
    (ε := 2 / 5) (by norm_num) hrec'
  rw [Fintype.card_fin, Fintype.card_bool] at h
  norm_num at h

/-- No `(1 - 1 / 5)`-statistically-private one-server PIR scheme on `Fin 16` with `1`-bit (`Bool`)
answers can recover every bit with probability at least `9 / 10` (`1 / 2 + 2 / 5`). -/
example {R Q : Type} [Finite Q] (P : Scheme (Fin 16) Unit R Q Bool)
    (hpriv : ∀ s i i',
      CloseTo (ProbComp.eval (P.serverQuery s i)) (ProbComp.eval (P.serverQuery s i'))
        (ENNReal.ofReal (1 / 5))) :
    ¬ ∀ x i, (9 / 10 : ℝ) ≤ (ProbComp.eval (P.run x i) (x i)).toReal := by
  intro hrec
  have hrec' : ∀ x i, 1 / 2 + (2 / 5 : ℝ) ≤ (ProbComp.eval (P.run x i) (x i)).toReal :=
    fun x i => by linarith [hrec x i]
  have h := card_mul_sq_le_card_answer_sub_one_of_statPrivate P (δ := 1 / 5) (ε := 2 / 5)
    (by norm_num) (by norm_num) hpriv hrec'
  rw [Fintype.card_fin, Fintype.card_bool] at h
  norm_num at h

end CslibFrontierTests.Crypto.PIRSmoothConverse
