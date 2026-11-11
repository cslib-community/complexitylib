/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.SIS.Module
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PPT

/-!
# Tests for General-Modulus SIS, Negacyclic Rings, Module-SIS and Module-LWE

Concrete evaluations and nonvacuity checks for:
1. General-modulus `GeneralSIS.isSISChallenge`, `GeneralSIS.decodeVec`, and Ajtai collision
   extraction `GeneralSIS.extractSISVector` over composite (`ZMod 6`) and prime (`ZMod 7`)
   moduli, plus nonvacuity of `GeneralSIS.Hard`.
2. Negacyclic convolution `negacyclicMul` and `rotMatrix` in `R[X] / (X^n + 1)`.
3. `ModuleSIS.IsSolution`, `expandModuleMatrix`, `flattenPolyVec`,
   `ModuleSIS.isSolution_expandModuleMatrix_iff`, `ModuleLWE.flattenPolyVec_sample`, and
   nonvacuity of `ModuleSIS.Hard`.
-/

namespace CslibFrontierTests.Crypto.ModuleSIS

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal _root_.Matrix

/-! ### 1. General-modulus SIS and Ajtai collision extraction -/

/-- Over composite modulus `q = 6`, `(1, 2, -1)` is a short solution for `[1, 2, 5]` with
`β = 2`, and its residue image satisfies `GeneralSIS.isSISChallenge`. -/
example : GeneralSIS.isSISChallenge !![(1 : ZMod 6), 2, 5] 2 ![1, 2, -1] := by decide

example : SIS.IsSolution !![(1 : ZMod 6), 2, 5] 2
    (GeneralSIS.liftCentered (![1, 2, -1] : Fin 3 → ZMod 6)) :=
  (GeneralSIS.isSISChallenge_iff_isSolution !![(1 : ZMod 6), 2, 5] 2 ![1, 2, -1]).mp (by decide)

/-- Framed signed-integer vector encoding and total decoding round-trip on negative, zero and
positive coordinates, while missing coordinates default to `0`. -/
example : GeneralSIS.decodeVec 3 (GeneralSIS.encodeVec ![1, -2, 0]) = ![1, -2, 0] :=
  GeneralSIS.decodeVec_encodeVec ![1, -2, 0]

example : GeneralSIS.decodeVec 2 [] = 0 := GeneralSIS.decodeVec_nil 2

/-- Over `ZMod 6`, the binary vectors `x = (1, 1, 0)` and `y = (0, 0, 1)` in `[0, 1]³` collide
under `ajtaiHashEval !![2, 4, 0]`, and `extractSISVector x y = (1, 1, -1)` is a short integer
solution with bound `1`. -/
abbrev ajtaiMat : Matrix (Fin 1) (Fin 3) (ZMod 6) := !![2, 4, 0]

example : GeneralSIS.isAjtaiCollision ajtaiMat 1 ![1, 1, 0] ![0, 0, 1] := by decide

example : GeneralSIS.extractSISVector (![1, 1, 0] : Fin 3 → ℤ) ![0, 0, 1] = ![1, 1, -1] := by
  decide

example : SIS.IsSolution ajtaiMat 1 (GeneralSIS.extractSISVector ![1, 1, 0] ![0, 0, 1]) :=
  GeneralSIS.isSolution_of_isAjtaiCollision (A := ajtaiMat) (β := 1) (by decide)

/-- Degenerate `GeneralSISParams` with `0` rows, `1` column, modulus `3` and bound `1`. -/
def zeroRowGeneralSIS : GeneralSISParams where
  n _ := 0
  m _ := 1
  q _ := 3
  β _ := 1
  hq _ := inferInstance

/-- With zero rows, outputting the encoded unit vector `![1]` always wins `GeneralSIS.sisGame`,
so `GeneralSIS.Hard` is not vacuous. -/
theorem not_hard_zeroRowGeneralSIS : ¬GeneralSIS.Hard zeroRowGeneralSIS := fun h => by
  let word := GeneralSIS.encodeVec (![1] : Fin 1 → ℤ)
  have hwin (security : ℕ) :
      GeneralSIS.sisGame zeroRowGeneralSIS (fun _ _ => pure word) security = PMF.pure true := by
    have hsol (A : Matrix (Fin 0) (Fin 1) (ZMod 3)) :
        SIS.IsSolution A 1 (GeneralSIS.decodeVec 1 word) := by
      rw [GeneralSIS.decodeVec_encodeVec]
      refine ⟨by decide, by decide, ?_⟩
      funext i
      exact i.elim0
    unfold GeneralSIS.sisGame zeroRowGeneralSIS
    dsimp only
    simp only [ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
      hsol, decide_true, PMF.bind_const]
  refine not_negligible_const one_ne_zero ?_
  simpa only [hwin, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one] using
    h (fun _ _ => pure word) (ComputableInPolyTime.const word).isPPTOn

/-! ### 2. Negacyclic polynomial arithmetic in `R[X] / (X^n + 1)` -/

/-- In `ℤ[X] / (X² + 1)`, `X · X = -1`. -/
example : negacyclicMul (![0, 1] : Fin 2 → ℤ) ![0, 1] = ![-1, 0] := by decide

/-- In `ℤ[X] / (X⁴ + 1)`, `(1 + X)(1 + X³) = 1 + X + X³ + X⁴ ≡ X + X³`. -/
example : negacyclicMul (![1, 1, 0, 0] : Fin 4 → ℤ) ![1, 0, 0, 1] = ![0, 1, 0, 1] := by
  decide

/-- The `2 × 2` negacyclic rotation matrix of `a₀ + a₁ X = 2 + 3 X` over `ℤ` is
`[[2, -3], [3, 2]]`. -/
example : rotMatrix (![2, 3] : Fin 2 → ℤ) = !![2, -3; 3, 2] := by decide

/-! ### 3. Module-SIS, block expansion and Module-LWE -/

/-- A `1 × 2` module matrix over `ℤ₅[X] / (X² + 1)` with entries `1 + 2 X` and `4 + 3 X = -1 - 2 X`,
for which `z = (1, 1)` is a short kernel vector with `β = 1`. -/
abbrev modMat : Matrix (Fin 1) (Fin 2) (Fin 2 → ZMod 5) :=
  !![![1, 2], ![4, 3]]

abbrev modSol : Fin 2 → Fin 2 → ℤ :=
  ![![1, 0], ![1, 0]]

example : ModuleSIS.IsSolution modMat 1 modSol := by decide

example : SIS.IsSolution (expandModuleMatrix modMat) 1 (flattenPolyVec modSol) :=
  (ModuleSIS.isSolution_expandModuleMatrix_iff modMat modSol).mpr (by decide)

/-- Flattening a Module-LWE sample agrees with the expanded matrix-vector product. -/
example :
    let s : Fin 2 → Fin 2 → ZMod 5 := ![![1, 2], ![0, 1]]
    let e : Fin 1 → Fin 2 → ZMod 5 := ![![3, 4]]
    flattenPolyVec (ModuleLWE.sample modMat s e) =
      expandModuleMatrix modMat *ᵥ flattenPolyVec s + flattenPolyVec e :=
  ModuleLWE.flattenPolyVec_sample modMat ![![1, 2], ![0, 1]] ![![3, 4]]

/-- Degenerate `ModuleSISParams` with `d = 0, k = 1, n = 1, q = 5, β = 1`. -/
def zeroRankModuleSIS : ModuleSISParams where
  n _ := 1
  d _ := 0
  k _ := 1
  q _ := 5
  β _ := 1
  hq _ := inferInstance

/-- With rank `d = 0`, a constant PPT adversary outputting the encoded unit polynomial vector
wins `ModuleSIS.moduleSISGame` with probability `1`, so `ModuleSIS.Hard` is not vacuous. -/
theorem not_hard_zeroRankModuleSIS : ¬ModuleSIS.Hard zeroRankModuleSIS := fun h => by
  let z0 : Fin 1 → Fin 1 → ℤ := fun _ _ => 1
  let word := ModuleSIS.encodeVec z0
  have hwin (security : ℕ) :
      ModuleSIS.moduleSISGame zeroRankModuleSIS (fun _ _ => pure word) security =
        PMF.pure true := by
    have hsol (A : Matrix (Fin 0) (Fin 1) (Fin 1 → ZMod 5)) :
        ModuleSIS.IsSolution A 1 (ModuleSIS.decodeVec 1 1 word) := by
      rw [ModuleSIS.decodeVec_encodeVec]
      refine ⟨by decide, by decide, ?_⟩
      funext i
      exact i.elim0
    unfold ModuleSIS.moduleSISGame zeroRankModuleSIS
    dsimp only
    simp only [ProbComp.eval_pure, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind,
      hsol, decide_true, PMF.bind_const]
  refine not_negligible_const one_ne_zero ?_
  simpa only [hwin, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one] using
    h (fun _ _ => pure word) (ComputableInPolyTime.const word).isPPTOn

/-- Zero polynomial noise for `n = 1`, `q = 2`. -/
noncomputable def moduleZeroNoise :
    (security : ℕ) → PMF (Fin ((fun _ : ℕ => 1) security) → ZMod ((fun _ : ℕ => 2) security)) :=
  fun _ => PMF.pure 0

/-- Test whether the fourth bit of the encoded Module-LWE sample is `false`. -/
def fourthBitFalse : Distinguisher :=
  fun _ word => pure (!(word.tail.tail.tail.headD true))

theorem fourthBitFalse_ppt : IsPPT encBool fourthBitFalse := by
  unfold fourthBitFalse
  ppt

/-- With `d = 0` and zero noise, every real Module-LWE sample encodes `(0, 0)` as
`[true, false, false, false]`. -/
theorem eq_of_mem_support_moduleLWEReal {security : ℕ} {word : List Bool}
    (h : word ∈ (ModuleLWE.realEnsemble (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2)
      moduleZeroNoise security).support) :
    word = [true, false, false, false] := by
  obtain ⟨pair, hpair, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  simp only [ModuleLWE.sampleLaw, moduleZeroNoise, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hpair
  obtain ⟨s, -, A, -, e, he, rfl⟩ := hpair
  have he0 : e 0 = 0 :=
    (PMF.mem_support_pure_iff _ _).mp ((PMF.mem_support_pi_iff _ _).mp he 0)
  have hA : A = 0 := Subsingleton.elim _ _
  have hs : s = 0 := Subsingleton.elim _ _
  have he' : e = 0 := funext fun i => by fin_cases i; exact he0
  subst hA hs he'
  change ModuleLWE.encodeSample
    ((0 : Matrix (Fin 1) (Fin 0) (Fin 1 → ZMod 2)), ModuleLWE.sample 0 0 0) =
      [true, false, false, false]
  decide

/-- The real `DecisionModuleLWE` experiment with `d = 0` and zero noise accepts with probability
`1`. -/
theorem distinguishingGame_moduleLWEReal (security : ℕ) :
    distinguishingGame
      (ModuleLWE.realEnsemble (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2)
        moduleZeroNoise security)
      (fourthBitFalse security) = PMF.pure true := by
  unfold distinguishingGame
  rw [PMF.monad_bind_eq_bind]
  trans (ModuleLWE.realEnsemble (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2)
    moduleZeroNoise security).bind fun _ => PMF.pure true
  · refine PMF.bind_congr_on_support _ _ _ fun word hword => ?_
    rw [eq_of_mem_support_moduleLWEReal hword]
    simp [fourthBitFalse]
  · exact PMF.bind_const _ _

/-- The uniform `DecisionModuleLWE` experiment with `m = 1, d = 0, n = 1, q = 2` accepts with
probability `1 / 2`. -/
theorem distinguishingGame_moduleLWEUniform_apply (security : ℕ) :
    distinguishingGame
      (ModuleLWE.uniformEnsemble (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2) security)
      (fourthBitFalse security) true = 2⁻¹ := by
  simp only [distinguishingGame, ModuleLWE.uniformEnsemble, fourthBitFalse,
    PMF.monad_bind_eq_bind, PMF.bind_map, Function.comp_def, ProbComp.eval_pure, PMF.bind_apply,
    tsum_fintype, PMF.uniformOfFintype_apply, PMF.pure_apply]
  rw [← Finset.mul_sum]
  have hcard :
      Fintype.card (Matrix (Fin 1) (Fin 0) (Fin 1 → ZMod 2) × (Fin 1 → Fin 1 → ZMod 2)) = 2 := by
    decide
  have hfilter :
      (Finset.univ.filter fun p :
          Matrix (Fin 1) (Fin 0) (Fin 1 → ZMod 2) × (Fin 1 → Fin 1 → ZMod 2) =>
        (ModuleLWE.encodeSample p)[3]?.getD true = false).card = 1 := by
    decide
  beta_reduce
  simp only [hcard]
  norm_num
  rw [hfilter]
  simp

/-- **Decision Module-LWE fails without secret coordinates and noise**: `fourthBitFalse`
distinguishes the real and uniform ensembles with constant advantage `1 / 2`. -/
theorem not_decisionModuleLWE_zeroNoise :
    ¬DecisionModuleLWE (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2) moduleZeroNoise := by
  intro h
  have hneg := h fourthBitFalse fourthBitFalse_ppt
  have hadv (security : ℕ) : Game.advantage
      (distinguishingGame
        (ModuleLWE.realEnsemble (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2)
          moduleZeroNoise security)
        (fourthBitFalse security))
      (distinguishingGame
        (ModuleLWE.uniformEnsemble (fun _ => 1) (fun _ => 0) (fun _ => 1) (fun _ => 2) security)
        (fourthBitFalse security)) = 2⁻¹ := by
    rw [Game.advantage, distinguishingGame_moduleLWEReal, Game.succProbability,
      Game.succProbability, distinguishingGame_moduleLWEUniform_apply]
    rw [PMF.pure_apply_self, ENNReal.toNNReal_one, ENNReal.toNNReal_inv, ENNReal.toNNReal_ofNat]
    apply NNReal.eq
    rw [coe_nndist, NNReal.dist_eq]
    norm_num
  have hc : Negligible (fun _ : ℕ => (2⁻¹ : ℝ≥0)) := hneg.congr hadv
  exact not_negligible_const (by norm_num) hc

end CslibFrontierTests.Crypto.ModuleSIS
