/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.RandomizedWordRAMBridge
import Complexity.DataStructure.HashFamily.WordRAM.DoubleTabulation
import Complexity.Foundations.Data.Finset.Expect

/-!
# Bridge for the high-independence Word-RAM hash-family formal abstract

`HashFamiliesAbstract.lean` states the self-contained formal abstract for the all-capacity
regime-switched Word-RAM hash family (`provableImpl` / `provableObliviousSequenceImpl` in
`Complexity/DataStructure/HashFamily/WordRAM/DoubleTabulation.lean`) specialized to polynomial
universe exponent `c_exp = 4` (`U ≤ max n_max 4 ^ 4`).

This bridge connects the self-contained primitive definitions in `HashFamiliesAbstract.lean` to the
library definitions and theorems over `Cslib.WordRAM.Basis.exact`:

1. **Resource and failure-probability correspondence**:
   Matches the self-contained definitions `regimeThreshold`, `chunkBits`, `charBits`,
   `trinomialStep`, `trinomialDeg`, `space`, `evalTimeBound`, `resampleTime`, `initTableSteps`,
   `initFreshTime`, `initClearTime`, `codeBound`, and `failureProbBound` with their library
   counterparts at `c_exp = 4`, and proves that `provableFailureProb 4 k n_max` is bounded by
   `failureProbBound k n_max` for every `k` and `n_max`.
2. **Exact compiled-program execution via `ExecRand.runRand_program`**:
   Combines `KWise.resampleCode_execRand` (`n_max < doubleTabThreshold c_exp`) and
   `DoubleTabulation.resampleCode_execRand` (`doubleTabThreshold c_exp ≤ n_max`) with
   `H.initTable_exec` and `H.eval_exec` to establish bounded-horizon `HaltsWithin`, `expectedTime`,
   and `evalRand` characterizations for the compiled programs `p_init`, `p_initClear`, and `p_op`
   of `(provableImpl c_exp k n_max U M ...).subroutineCode`.
3. **Multi-operation transcript and coupling transfer**:
   Transfers `evalOps_execSteps` and `provableObliviousSequenceImpl` across any presentation
   `(S, P)` satisfying `RandomizedWordRAMBridge.Laws S` and `HFLaws S P`.
-/

namespace ComplexityAbstracts.HashFamiliesBridge

open scoped ENNReal BigOperators
open Cslib
open Cslib.WordRAM
open Cslib.WordRAM.Randomized
open Cslib.Probability
open Cslib.DataStructure
open Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.DoubleTabulation
open Cslib.Algorithms.WordRAM.Hashing
open ComplexityAbstracts.RandomizedWordRAMBridge

/-! ## Part 1: Resource functions and failure-probability bounds at `c_exp = 4` -/

/-- Capacity threshold `2 ^ 320000` (`doubleTabThreshold 4`). -/
def regimeThreshold : ℕ :=
  2 ^ 320000

private lemma two_mul_doubleTabMinB_four : 2 * doubleTabMinB 4 = 320000 := rfl

private lemma provableC_four : provableC 4 = 8 := rfl

private lemma provableD_four : provableD 4 = 64 := rfl

private lemma provableCD_four : (provableC 4 + 1) * provableD 4 = 576 := rfl

private lemma provableSpaceFactor_four (k : ℕ) : provableSpaceFactor 4 k = k + 9232 := by
  dsimp only [provableSpaceFactor]
  rw [provableC_four, provableD_four]
  omega

theorem regimeThreshold_eq : regimeThreshold = doubleTabThreshold 4 := by
  unfold regimeThreshold doubleTabThreshold
  rw [two_mul_doubleTabMinB_four]

/-- Chunk bit-width `max 1 (Nat.log 2 (max n_max 2) / 3)` in the small-capacity regime. -/
def chunkBits (n_max : ℕ) : ℕ :=
  max 1 (Nat.log 2 (max n_max 2) / 3)

theorem chunkBits_eq (n_max : ℕ) : chunkBits n_max = KWise.chunkBits n_max := rfl

/-- Character bit-width `(1 + Nat.clog 2 (max n_max 4)) / 2` in the large-capacity regime. -/
def charBits (n_max : ℕ) : ℕ :=
  (1 + Nat.clog 2 (max n_max 4)) / 2

theorem charBits_eq (n_max : ℕ) : charBits n_max = provableB n_max := rfl

/-- Structural recursion helper computing `Cslib.Probability.trinomialStepAux`. -/
def trinomialStepLoop (fuel : ℕ) : ℕ → ℕ :=
  Nat.rec (fun _ => 0)
    (fun _ ih B => if B ≤ 2 then 0 else ih ((B + 2) / 3) + 1)
    fuel

theorem trinomialStepLoop_eq (fuel B : ℕ) (hB : B ≤ fuel) :
    trinomialStepLoop fuel B = Cslib.Probability.trinomialStepAux B := by
  induction fuel generalizing B with
  | zero =>
    have hle : B ≤ 2 := by omega
    change 0 = Cslib.Probability.trinomialStepAux B
    rw [Cslib.Probability.trinomialStepAux]
    simp [hle]
  | succ fuel ih =>
    change (if B ≤ 2 then 0 else trinomialStepLoop fuel ((B + 2) / 3) + 1) = _
    rw [Cslib.Probability.trinomialStepAux]
    split_ifs with hle
    · rfl
    · rw [ih ((B + 2) / 3) (by omega)]

/-- Selected trinomial parameter `t` for key universe `U` and output bit-width `M`. -/
def trinomialStep (U M : ℕ) : ℕ :=
  let B := max (Nat.clog 2 (max U 2)) (max M 1)
  trinomialStepLoop B B

theorem trinomialStep_eq (U M : ℕ) :
    trinomialStep U M = Cslib.Probability.trinomialStep U M :=
  trinomialStepLoop_eq _ _ le_rfl

/-- Selected binary trinomial field degree `2 * 3 ^ trinomialStep U M`. -/
def trinomialDeg (U M : ℕ) : ℕ :=
  2 * 3 ^ trinomialStep U M

theorem trinomialDeg_eq (U M : ℕ) :
    trinomialDeg U M = Cslib.Probability.trinomialDeg U M := by
  dsimp only [trinomialDeg, Cslib.Probability.trinomialDeg]
  rw [trinomialStep_eq]

/-- Exact memory footprint `provableSpace 4 k n_max` in machine words. -/
def space (k n_max : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    8 + k + 2 ^ (2 * chunkBits n_max)
  else
    576 * 2 ^ charBits n_max

theorem space_eq (k n_max : ℕ) : space k n_max = provableSpace 4 k n_max := by
  unfold space provableSpace KWise.space KWise.spaceFromB DoubleTabulation.space
  rw [regimeThreshold_eq, chunkBits_eq, charBits_eq, provableCD_four]

/-- Uniform linear space bound `space k n_max ≤ (k + 9232) * (n_max + 1)` across all `n_max`. -/
theorem space_le (k n_max : ℕ) : space k n_max ≤ (k + 9232) * (n_max + 1) := by
  rw [space_eq, ← provableSpaceFactor_four k]
  exact provableSpace_le 4 k n_max

/-- Uniform `O_k(1)` worst-case instruction bound for `.eval u` (including subroutine dispatch and
the final `halt` instruction). -/
def evalTimeBound (k : ℕ) : ℕ :=
  max (111230 * k + 19) 6858 + 4

theorem evalTimeBound_eq (k : ℕ) : evalTimeBound k = provableEvalBound 4 k + 4 := rfl

theorem evalTimeBound_le (k : ℕ) : evalTimeBound k ≤ 111230 * k + 6862 := by
  dsimp only [evalTimeBound]
  omega

/-- General worst-case instruction budget for `.resample` parameterized by `c_exp`. -/
def resampleTimeOf (c_exp k n_max : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    5 * k + 13
  else
    5 * ((provableC c_exp + 1) * provableD c_exp * 2 ^ provableB n_max) + 16

/-- Worst-case instruction budget for `.resample` at `c_exp = 4` (including subroutine dispatch and
the final `halt` instruction). -/
def resampleTime (k n_max : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    5 * k + 13
  else
    2880 * 2 ^ charBits n_max + 16

theorem resampleTime_eq (k n_max : ℕ) : resampleTime k n_max = resampleTimeOf 4 k n_max := by
  unfold resampleTime resampleTimeOf
  rw [regimeThreshold_eq, charBits_eq, provableCD_four, ← Nat.mul_assoc]

theorem resampleTime_eq_of_lt {k n_max : ℕ} (hlt : n_max < regimeThreshold) :
    resampleTime k n_max = 5 * k + 13 := by
  unfold resampleTime
  simp [hlt]

theorem resampleTime_le (k n_max : ℕ) :
    resampleTime k n_max ≤ (5 * k + 46096) * (n_max + 1) := by
  unfold resampleTime
  split_ifs with h
  · have hk : 5 * k + 13 ≤ (5 * k + 46096) * 1 := by omega
    exact hk.trans (Nat.mul_le_mul_left _ (by omega))
  · have hpow := two_pow_provableB_le n_max
    rw [← charBits_eq] at hpow
    have hpow' : 2 ^ charBits n_max ≤ 16 * (n_max + 1) := by omega
    calc 2880 * 2 ^ charBits n_max + 16
        ≤ 2880 * (16 * (n_max + 1)) + 16 * (n_max + 1) := by omega
      _ = 46096 * (n_max + 1) := by ring
      _ ≤ (5 * k + 46096) * (n_max + 1) := Nat.mul_le_mul_right _ (by omega)

/-- General deterministic table-construction step count parameterized by `c_exp`. -/
def initTableStepsOf (c_exp n_max U M : ℕ) : ℕ :=
  if n_max < doubleTabThreshold c_exp then
    19 * 2 ^ (2 * KWise.chunkBits n_max) +
      4 * Nat.log 2 (max n_max 2) +
      5 * Nat.clog 2 (max U 2) +
      5 * Cslib.Probability.trinomialStep U M + 69
  else
    1

/-- Deterministic table-construction step count `H.initTableSteps` at `c_exp = 4`. -/
def initTableSteps (n_max U M : ℕ) : ℕ :=
  if n_max < regimeThreshold then
    19 * 2 ^ (2 * chunkBits n_max) +
      4 * Nat.log 2 (max n_max 2) +
      5 * Nat.clog 2 (max U 2) +
      5 * trinomialStep U M + 69
  else
    1

theorem initTableSteps_eq (n_max U M : ℕ) :
    initTableSteps n_max U M = initTableStepsOf 4 n_max U M := by
  unfold initTableSteps initTableStepsOf
  rw [regimeThreshold_eq, chunkBits_eq, trinomialStep_eq]

/-- General worst-case instruction budget for `p_init` on fresh zeroed memory. -/
def initFreshTimeOf (c_exp k n_max U M : ℕ) : ℕ :=
  initTableStepsOf c_exp n_max U M + resampleTimeOf c_exp k n_max + 1

/-- Worst-case instruction budget for `p_init` on fresh zeroed memory at `c_exp = 4`. -/
def initFreshTime (k n_max U M : ℕ) : ℕ :=
  initTableSteps n_max U M + resampleTime k n_max + 1

theorem initFreshTime_eq (k n_max U M : ℕ) :
    initFreshTime k n_max U M = initFreshTimeOf 4 k n_max U M := by
  unfold initFreshTime initFreshTimeOf
  rw [initTableSteps_eq, resampleTime_eq]

/-- General worst-case instruction budget for `p_initClear` on arbitrary dirty memory. -/
def initClearTimeOf (c_exp k n_max U M : ℕ) : ℕ :=
  initFreshTimeOf c_exp k n_max U M + (4 * provableSpace c_exp k n_max + 6)

/-- Worst-case instruction budget for `p_initClear` on arbitrary dirty memory at `c_exp = 4`. -/
def initClearTime (k n_max U M : ℕ) : ℕ :=
  initFreshTime k n_max U M + (4 * space k n_max + 6)

theorem initClearTime_eq (k n_max U M : ℕ) :
    initClearTime k n_max U M = initClearTimeOf 4 k n_max U M := by
  unfold initClearTime initClearTimeOf
  rw [initFreshTime_eq, space_eq]

/-- Per-step code-counting factor `8 * ((8 * k) ^ 16 * 64) ^ 4` (`doubleTabCodeBound 8 64 4 k`). -/
def codeBound (k : ℕ) : ℕ :=
  8 * ((8 * k) ^ 16 * 64) ^ 4

theorem codeBound_eq (k : ℕ) :
    codeBound k = doubleTabCodeBound (provableC 4) (provableD 4) 4 k := rfl

/-- Closed-form per-epoch failure-probability bound proved for `provableObliviousSequenceImpl 4`. -/
noncomputable def failureProbBound (k n_max : ℕ) : ℝ≥0∞ :=
  if n_max < regimeThreshold then
    0
  else if 2 * codeBound k ≤ 2 ^ (3 * charBits n_max) then
    ((2 * (codeBound k) ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ (6 * charBits n_max) : ℕ) : ℝ≥0∞)
  else
    1

theorem failureProbBound_eq_zero_of_lt {k n_max : ℕ} (hlt : n_max < regimeThreshold) :
    failureProbBound k n_max = 0 := by
  unfold failureProbBound
  simp [hlt]

theorem failureProbBound_eq_of_ge {k n_max : ℕ} (hge : regimeThreshold ≤ n_max)
    (hk : 2 * codeBound k ≤ 2 ^ (3 * charBits n_max)) :
    failureProbBound k n_max =
      ((2 * (codeBound k) ^ 2 : ℕ) : ℝ≥0∞) / ((2 ^ (6 * charBits n_max) : ℕ) : ℝ≥0∞) := by
  have hnot : ¬(n_max < regimeThreshold) := not_lt.mpr hge
  unfold failureProbBound
  simp [hnot, hk]

theorem failureProbBound_le_inv_cube_of_ge {k n_max : ℕ} (hge : regimeThreshold ≤ n_max)
    (hk : 2 * codeBound k ≤ 2 ^ (3 * charBits n_max)) :
    failureProbBound k n_max ≤
      ((2 * (codeBound k) ^ 2 : ℕ) : ℝ≥0∞) / ((max n_max 4 ^ 3 : ℕ) : ℝ≥0∞) := by
  rw [failureProbBound_eq_of_ge hge hk]
  have hclog_le : Nat.clog 2 (max n_max 4) ≤ 2 * charBits n_max := by
    dsimp only [charBits]
    omega
  have hn_le : max n_max 4 ≤ 2 ^ (2 * charBits n_max) :=
    (Nat.le_pow_clog (by decide) (max n_max 4)).trans (Nat.pow_le_pow_right (by decide) hclog_le)
  have hcube : max n_max 4 ^ 3 ≤ 2 ^ (6 * charBits n_max) := by
    calc max n_max 4 ^ 3
        ≤ (2 ^ (2 * charBits n_max)) ^ 3 := Nat.pow_le_pow_left hn_le 3
      _ = 2 ^ (6 * charBits n_max) := by
          rw [← Nat.pow_mul]
          congr 1
          ring
  exact ENNReal.div_le_div_left (by exact_mod_cast hcube) _

private theorem provableFailureProb_le_aux (c_exp k n_max : ℕ)
    (hc : provableD c_exp = 2 * 4 * provableC c_exp) :
    provableFailureProb c_exp k n_max ≤
      if n_max < doubleTabThreshold c_exp then
        (0 : ℝ≥0∞)
      else if 2 * doubleTabCodeBound (provableC c_exp) (provableD c_exp) 4 k ≤
          2 ^ (3 * provableB n_max) then
        ((2 * (doubleTabCodeBound (provableC c_exp) (provableD c_exp) 4 k) ^ 2 : ℕ) : ℝ≥0∞) /
          ((2 ^ (6 * provableB n_max) : ℕ) : ℝ≥0∞)
      else
        (1 : ℝ≥0∞) := by
  by_cases hlt : n_max < doubleTabThreshold c_exp
  · simp [provableFailureProb_eq_zero_of_lt hlt, hlt]
  · rw [provableFailureProb_eq_of_ge (not_lt.mp hlt)]
    simp only [hlt, ↓reduceIte]
    split_ifs with hk
    · rw [hc] at hk ⊢
      exact doubleTabFailureProb_eight_mul_le (one_le_provableC c_exp) hk
    · dsimp only [doubleTabFailureProb]
      have hcard_le :
          (Finset.univ \
            doubleTabGoodTop (provableC c_exp) (provableD c_exp) (provableB n_max) k).card ≤
            Fintype.card (DoubleTabTopSeed (provableC c_exp) (provableD c_exp) (provableB n_max)) :=
        Finset.card_le_univ _
      have hne_zero :
          (Fintype.card (DoubleTabTopSeed (provableC c_exp) (provableD c_exp) (provableB n_max)) :
            ℝ≥0∞) ≠ 0 :=
        Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hne_top :
          (Fintype.card (DoubleTabTopSeed (provableC c_exp) (provableD c_exp) (provableB n_max)) :
            ℝ≥0∞) ≠ ⊤ :=
        ENNReal.natCast_ne_top _
      rw [ENNReal.div_le_iff_le_mul (Or.inl hne_zero) (Or.inl hne_top), one_mul]
      exact_mod_cast hcard_le

theorem provableFailureProb_le_failureProbBound (k n_max : ℕ) :
    provableFailureProb 4 k n_max ≤ failureProbBound k n_max := by
  unfold failureProbBound
  rw [regimeThreshold_eq, codeBound_eq, charBits_eq]
  exact provableFailureProb_le_aux 4 k n_max rfl

/-! ## Part 2: Exact `ExecRand` execution of `provableImpl c_exp` -/

private theorem coreReg_injective {r_core : ℕ} :
    Function.Injective (@coreReg r_core) := by
  intro i j h
  simpa [coreReg, Fin.ext_iff] using h

private theorem coreReg_ne_of_val_ge {r_core : ℕ} (i : Fin r_core) {r : Fin (r_core + 5)}
    (hr : r_core ≤ r.val) : coreReg i ≠ r := by
  intro h
  have hval := congrArg Fin.val h
  dsimp only [coreReg, Fin.val_castAdd] at hval
  omega

private theorem frontierReg_notMem_range_coreReg {r_core : ℕ} :
    frontierReg r_core ∉ Set.range (@coreReg r_core) := by
  rintro ⟨i, hi⟩
  exact coreReg_ne_of_val_ge i (by dsimp [frontierReg]; omega) hi

private theorem provableImpl_keyReg (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).keyReg = 1 := by
  dsimp only [provableImpl]
  split_ifs <;> rfl

private theorem provableImpl_outReg (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).outReg = 2 := by
  dsimp only [provableImpl]
  split_ifs <;> rfl

private theorem provableImpl_baseReg (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).baseReg = 0 := by
  dsimp only [provableImpl]
  split_ifs <;> rfl

private theorem provableImpl_initTableSteps_eq (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).initTableSteps =
      initTableStepsOf c_exp n_max U M := by
  dsimp only [provableImpl, initTableStepsOf]
  split_ifs <;> rfl

private theorem provableImpl_resampleSteps_eq (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    (provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U).resampleSteps + 3 =
      resampleTimeOf c_exp k n_max := by
  dsimp only [provableImpl, resampleTimeOf]
  split_ifs <;> rfl

private theorem provableImpl_eq_of_lt {c_exp k n_max U M w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (h : n_max < doubleTabThreshold c_exp) :
    provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U =
      kWiseImpl (k := k) hw (by simpa only [provableSpace, h, ↓reduceIte] using hfit_space)
        hfit_n hfit_U := by
  unfold provableImpl
  exact dite_eq_left_of_eq_true (eq_true h)

private theorem provableImpl_eq_of_not_lt {c_exp k n_max U M w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (h : ¬ n_max < doubleTabThreshold c_exp)
    (hsp : Fits w (base + DoubleTabulation.space (provableC c_exp) (provableD c_exp)
      (provableB n_max)))
    (hpow_b : Fits w (2 ^ provableB n_max))
    (hpow_M : Fits w (2 ^ M))
    (hkeys : ∀ u : Fin U, Fits w u.val) :
    provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U =
      impl18 ![n_max, U, M] hsp hpow_b hpow_M hkeys := by
  unfold provableImpl
  exact dite_eq_right_of_eq_false (eq_false h)

/-- Exact `ExecRand` characterization of `(provableImpl c_exp k n_max U M ...).resampleCode`:
on every path, `resampleCode` terminates within `H.resampleSteps` instructions and pushes forward
to the uniform distribution on `H.Seed`. -/
private theorem provableImpl_resample_execRand (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    ∀ {x : Data 18},
      x.Bounded w →
      x.regs H.baseReg = base →
      H.tableRep x.mem →
      ∃ (m_comp : ProbComp (Data 18 × ℕ)) (extract : (ℕ → ℕ) → H.Seed),
        ExecRand w H.resampleCode x m_comp ∧
        (m_comp.eval).map (fun z => extract z.1.mem) = PMF.uniformOfFintype H.Seed ∧
        ∀ z ∈ m_comp.support,
          z.1.regs H.baseReg = base ∧
          H.tableRep z.1.mem ∧
          H.seedRep (extract z.1.mem) z.1.mem ∧
          Modifies (Block.mk base H.space).footprint x.mem z.1.mem ∧
          z.2 ≤ H.resampleSteps := by
  intro H x _ hbase htab
  have hH_def : H = provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U := rfl
  clear_value H
  by_cases h : n_max < doubleTabThreshold c_exp
  · have hH := hH_def.trans (provableImpl_eq_of_lt hw hfit_space hfit_n hfit_U h)
    subst hH
    have hsp : Fits w (base + KWise.space n_max k) := by
      simpa only [provableSpace, h, ↓reduceIte] using hfit_space
    have hq_pos : 0 < Cslib.Probability.trinomialDeg U M := by
      dsimp only [Cslib.Probability.trinomialDeg]
      positivity
    have hfit_q : Fits w (2 ^ Cslib.Probability.trinomialDeg U M) :=
      Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hpow : 0 < 2 ^ (2 * KWise.chunkBits n_max) := by positivity
    have hfit_end : Fits w (base + 8 + k) :=
      hsp.of_le (by
        change base + 8 + k ≤ base + (8 + k + 2 ^ (2 * KWise.chunkBits n_max))
        omega)
    refine ⟨KWise.resampleComp base U M k x, KWise.extractSeeds base U M k,
      KWise.resampleCode_execRand htab hbase hfit_end hfit_q,
      KWise.map_extractSeeds_eval_resampleComp base U M k x, ?_⟩
    intro z hz
    obtain ⟨⟨⟨htab', hseed'⟩, hz0, hout⟩, hsteps⟩ :=
      KWise.mem_support_resampleComp htab hbase hz
    refine ⟨hz0, htab', hseed', ?_, hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    dsimp only [kWiseImpl, KWise.space, KWise.spaceFromB] at ha
    exact hout a (by omega)
  · have hsp : Fits w (base + DoubleTabulation.space (provableC c_exp) (provableD c_exp)
        (provableB n_max)) := by
      simpa only [provableSpace, h, ↓reduceIte] using hfit_space
    have hpow_b : Fits w (2 ^ provableB n_max) :=
      hsp.of_le (by
        have hc : 1 ≤ provableC c_exp := one_le_provableC c_exp
        have hd : 1 ≤ provableD c_exp := by dsimp only [provableD]; omega
        have hle : 1 * 2 ^ provableB n_max ≤
            ((provableC c_exp + 1) * provableD c_exp) * 2 ^ provableB n_max :=
          Nat.mul_le_mul_right _ (by nlinarith)
        dsimp only [DoubleTabulation.space]
        omega)
    have hpow_M : Fits w (2 ^ M) := by
      have hM_le : M ≤ Cslib.Probability.trinomialDeg U M := le_trinomialDeg U M
      have hdeg_pos : 0 < Cslib.Probability.trinomialDeg U M := by
        dsimp only [Cslib.Probability.trinomialDeg]
        positivity
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hkeys : ∀ u : Fin U, Fits w u.val :=
      fun u => hfit_U.of_le (by have := u.isLt; omega)
    have hH := hH_def.trans
      (provableImpl_eq_of_not_lt hw hfit_space hfit_n hfit_U h hsp hpow_b hpow_M hkeys)
    subst hH
    have hfit_mask_b : Fits w (2 ^ provableB n_max - 1) := hpow_b.of_le (Nat.pred_le _)
    have hfit_mask_M : Fits w (2 ^ M - 1) := hpow_M.of_le (Nat.pred_le _)
    have hfit_1 : Fits w 1 := hpow_b.of_le Nat.one_le_two_pow
    have hbase12 : (x.comap cast12To18).regs 0 = base := hbase
    have hex18 := (resampleCode_execRand hbase12 hsp hfit_mask_b hfit_mask_M hfit_1).rename
      injective_cast12To18
    have hunif18 :
        (((fun z : Data 12 × ℕ => (z.1.extend cast12To18 x, z.2)) <$>
            resampleComp base (provableC c_exp) (provableD c_exp) (provableB n_max) M
              (x.comap cast12To18)).eval).map
          (fun z =>
            extractSeed base (provableC c_exp) (provableD c_exp) (provableB n_max) M z.1.mem) =
        PMF.uniformOfFintype
          (DoubleTabTopSeed (provableC c_exp) (provableD c_exp) (provableB n_max) ×
            DoubleTabBotSeed (provableD c_exp) (provableB n_max) M) := by
      rw [ProbComp.eval_map, PMF.map_comp]
      exact map_extractSeed_eval_resampleComp base (provableC c_exp) (provableD c_exp)
        (provableB n_max) M (x.comap cast12To18)
    refine ⟨_, extractSeed base (provableC c_exp) (provableD c_exp) (provableB n_max) M,
      hex18, hunif18, ?_⟩
    intro z hz
    obtain ⟨z12, hz12, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨hz0, hseed, hframe, hsteps⟩ := mem_support_resampleComp hbase12 hz12
    have hreg0 : (z12.1.extend cast12To18 x).regs 0 = base := by
      change ((z12.1.extend cast12To18 x).comap cast12To18).regs 0 = base
      rw [Data.comap_extend injective_cast12To18]
      exact hz0
    refine ⟨hreg0, trivial, hseed, ?_, le_of_eq hsteps⟩
    intro a ha
    rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt] at ha
    exact hframe a ha

/-- General compilation helper from `ExecRand` on `Code .exact 23` to `S.HaltsWithin`,
`S.expectedTime`, and `S.evalRand`. -/
private theorem compile_execRand {S : Presentation} (hS : Laws S) {w T : ℕ}
    {c : Code .exact 23} {x : Data 23} {m : ProbComp (Data 23 × ℕ)}
    (hm : ExecRand w c x m) (hT : ∀ z ∈ m.support, z.2 + 1 ≤ T) :
    let p := S.programOf (c.program (coreReg 2))
    let s := S.state 0 x.regs x.mem
    S.HaltsWithin w p s T ∧
    S.expectedTime w p s ≤ (T : ℝ≥0∞) ∧
    S.evalRand w p T s =
      (m.eval).map (fun z => S.halted (z.1.regs (coreReg 2)) z.1.regs z.1.mem) := by
  intro p s
  have hrun := hm.runRand_program (coreReg 2) hT
  have hrhw : Cslib.WordRAM.RandHaltsWithin w (c.program (coreReg 2)) ⟨0, x⟩ T := by
    intro cfg hcfg
    rw [hrun] at hcfg
    obtain ⟨z, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hcfg
    exact ⟨z.1.regs (coreReg 2), z.1, rfl⟩
  have hhw : S.HaltsWithin w p s T :=
    (S.haltsWithin_iff hS w (c.program (coreReg 2)) T 0 x.regs x.mem).mpr hrhw
  have hexp : S.expectedTime w p s ≤ (T : ℝ≥0∞) := by
    rw [S.expectedTime_eq hS w (c.program (coreReg 2)) 0 x.regs x.mem]
    exact expectedTime_le_of_randHaltsWithin hrhw
  have heval : S.evalRand w p T s =
      (m.eval).map (fun z => S.halted (z.1.regs (coreReg 2)) z.1.regs z.1.mem) := by
    rw [S.evalRand_eq hS w (c.program (coreReg 2)) T 0 x.regs x.mem]
    change (Cslib.WordRAM.runRand w (c.program (coreReg 2)) T (.running ⟨0, x⟩)).eval.map
      S.cfgOf = _
    rw [hrun, ProbComp.eval_map, PMF.map_comp]
    rfl
  exact ⟨hhw, hexp, heval⟩

/-- General compilation helper from deterministic `ExecWithin` on `Code .exact 23` to
`S.HaltsWithin`, `S.expectedTime`, and `S.evalRand`. -/
private theorem compile_execWithin {S : Presentation} (hS : Laws S) {w T_bound T : ℕ}
    {c : Code .exact 23} {x y : Data 23}
    (he : ExecWithin w c x y T_bound) (hT : T_bound + 1 ≤ T) :
    let p := S.programOf (c.program (coreReg 2))
    let s := S.state 0 x.regs x.mem
    S.HaltsWithin w p s T ∧
    S.expectedTime w p s ≤ (T : ℝ≥0∞) ∧
    S.evalRand w p T s = PMF.pure (S.halted (y.regs (coreReg 2)) y.regs y.mem) := by
  intro p s
  obtain ⟨steps, hsteps, hex⟩ := he
  have hcomp := compile_execRand hS hex.execRand (T := T) fun z hz => by
    cases OracleComp.eq_of_mem_supportWith_pure hz
    omega
  refine ⟨hcomp.1, hcomp.2.1, ?_⟩
  simpa only [ProbComp.eval_pure, PMF.pure_map] using hcomp.2.2

/-- `ExecWithin` determinism: two `ExecWithin` derivations from the same initial state `x` produce
the exact same final state `y₁ = y₂`. -/
private theorem execWithin_unique {B : Basis} {r w T₁ T₂ : ℕ} {c : Code B r} {x y₁ y₂ : Data r}
    (h₁ : ExecWithin w c x y₁ T₁) (h₂ : ExecWithin w c x y₂ T₂) : y₁ = y₂ := by
  obtain ⟨n₁, -, he₁⟩ := h₁
  obtain ⟨n₂, -, he₂⟩ := h₂
  have heq := he₁.execRand.unique he₂.execRand
  have hsup : (y₁, n₁) ∈ (pure (y₂, n₂) : ProbComp (Data r × ℕ)).support := by
    rw [← heq]
    exact rfl
  exact Prod.mk.inj (OracleComp.eq_of_mem_supportWith_pure hsup) |>.1

/-- Executed after `allocSpan` (and optional `zeroFillCode`) once `[base, base + H.space)` is
zeroed: `P.initSetup` executes via `ExecRand` within `H.initTableSteps + H.resampleSteps`
instructions and produces an initial coupled distribution `ν₀` satisfying `H.initInv ν₀`. -/
private theorem provableImpl_initSetup_execRand (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    let P := H.subroutineCode
    ∀ {x₁ : Data 23},
      x₁.Bounded w →
      x₁.regs P.baseReg = base →
      x₁.regs P.frontierReg = base + H.space →
      (∀ j, x₁.regs (P.initParams j) = ![n_max, U, M] j) →
      (∀ a ∈ (Block.mk base H.space).footprint, x₁.mem a = 0) →
      ∃ (m_setup : ProbComp (Data 23 × ℕ)) (ν₀ : PMF (LatentState H.Seed 23)),
        ExecRand w P.initSetup x₁ m_setup ∧
        m_setup.eval.map Prod.fst = ν₀.map LatentState.data ∧
        (∀ z ∈ m_setup.support, z.2 ≤ H.initTableSteps + H.resampleSteps) ∧
        H.initInv ν₀ ∧
        ∀ t ∈ ν₀.support,
          t.data.Bounded w ∧
          t.data.regs P.baseReg = base ∧
          t.data.regs P.frontierReg = base + H.space ∧
          Modifies (Block.mk base H.space).footprint x₁.mem t.data.mem := by
  intro H P x₁ hx₁ hb hfr hpar hz
  obtain ⟨y_tab, he_tab, hy_base, hy_tab, hy_mod⟩ :=
    H.initTable_exec (hx₁.comap coreReg) hb hpar hz
  have hy_bdd : y_tab.Bounded w := he_tab.bounded (hx₁.comap coreReg)
  let x₂ : Data 23 := y_tab.extend coreReg x₁
  have hx₂_bdd : x₂.Bounded w := hy_bdd.extend coreReg_injective hx₁
  have he_tab_ren : ExecWithin w (H.initTableCode.rename coreReg) x₁ x₂ H.initTableSteps := by
    simpa [x₂] using he_tab.rename coreReg_injective
  obtain ⟨n_tab, hn_tab, hex_tab⟩ := he_tab_ren
  have hx₂_comap : x₂.comap coreReg = y_tab :=
    Data.comap_extend coreReg_injective y_tab x₁
  obtain ⟨m_res, extract, hex_res, hunif_res, hsupp_res⟩ :=
    provableImpl_resample_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
      (x := x₂.comap coreReg)
      (hx₂_bdd.comap coreReg)
      (by rw [hx₂_comap]; exact hy_base)
      (by rw [hx₂_comap]; exact hy_tab)
  have hex_res_ren : ExecRand w (H.resampleCode.rename coreReg) x₂
      ((fun z => (z.1.extend coreReg x₂, z.2)) <$> m_res) :=
    hex_res.rename coreReg_injective
  have hex_setup : ExecRand w P.initSetup x₁
      ((fun z => (z.1, n_tab + z.2)) <$>
        ((fun z => (z.1.extend coreReg x₂, z.2)) <$> m_res)) :=
    hex_tab.seqRand hex_res_ren
  let lift0 : Data 18 × ℕ → LatentState H.Seed 23 :=
    fun z => ⟨extract z.1.mem, z.1.extend coreReg x₂⟩
  let ν₀ : PMF (LatentState H.Seed 23) := m_res.eval.map lift0
  refine ⟨_, ν₀, hex_setup, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp, PMF.map_comp, PMF.map_comp]
    rfl
  · intro z hz
    obtain ⟨z', hz', rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz'
    have hsteps : z₀.2 ≤ H.resampleSteps := (hsupp_res z₀ hz₀).2.2.2.2
    omega
  · dsimp only [ν₀, lift0]
    rw [PMF.map_comp]
    exact hunif_res
  · intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [ProbComp.support_eval] at hz
    obtain ⟨hz_base, hz_tab, hz_seed, _, _⟩ := hsupp_res z hz
    have hz_bdd : z.1.Bounded w := hex_res.bounded (hx₂_bdd.comap coreReg) hz
    have hreg_base : (z.1.extend coreReg x₂).regs (coreReg H.baseReg) = base := by
      change ((z.1.extend coreReg x₂).comap coreReg).regs H.baseReg = base
      rw [Data.comap_extend coreReg_injective]
      exact hz_base
    exact ⟨hz_bdd.extend coreReg_injective hx₂_bdd, hreg_base, hz_tab, hz_seed⟩
  · intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨z, hz, rfl⟩ := ht
    rw [ProbComp.support_eval] at hz
    obtain ⟨hz_base, _, _, hz_mod, _⟩ := hsupp_res z hz
    have hz_bdd : z.1.Bounded w := hex_res.bounded (hx₂_bdd.comap coreReg) hz
    have hreg_base : (z.1.extend coreReg x₂).regs P.baseReg = base := by
      change ((z.1.extend coreReg x₂).comap coreReg).regs H.baseReg = base
      rw [Data.comap_extend coreReg_injective]
      exact hz_base
    have hfr_t : (z.1.extend coreReg x₂).regs P.frontierReg = base + H.space := by
      change (z.1.extend coreReg (y_tab.extend coreReg x₁)).regs (frontierReg 18) = base + H.space
      rw [Data.extend_regs_of_notMem _ _ frontierReg_notMem_range_coreReg,
        Data.extend_regs_of_notMem _ _ frontierReg_notMem_range_coreReg]
      exact hfr
    have hz_mod' : Modifies (Block.mk base H.space).footprint y_tab.mem z.1.mem := hz_mod
    have hmod_t : Modifies (Block.mk base H.space).footprint x₁.mem z.1.mem := by
      simpa only [Data.comap, Finset.union_idempotent] using hy_mod.trans hz_mod'
    exact ⟨hz_bdd.extend coreReg_injective hx₂_bdd, hreg_base, hfr_t, hmod_t⟩

/-- Single `.resample` operation execution on `P.code` via `ExecRand`. -/
private theorem provableImpl_step_resample_execRand (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    let P := H.subroutineCode
    ∀ (x : Data 23),
      x.Bounded w →
      x.regs (coreReg H.baseReg) = base →
      H.tableRep x.mem →
      ∃ (m_step : ProbComp (Data 23 × ℕ))
        (μ_x : PMF (StepOutcome H.Seed PUnit 23)),
        ExecRand w P.code
          ((P.toDynamicProgram H.encode H.decode).prepare .resample x) m_step ∧
        m_step.eval.map Prod.fst = μ_x.map StepOutcome.data ∧
        (∀ z ∈ m_step.support, z.2 ≤ H.resampleSteps + 2) ∧
        μ_x.map StepOutcome.latent = PMF.uniformOfFintype H.Seed ∧
        ∀ q ∈ μ_x.support,
          q.data.Bounded w ∧
          H.decode .resample q.data.regs = some q.result ∧
          Modifies (Block.mk base H.space).footprint x.mem q.data.mem ∧
          q.data.regs (coreReg H.baseReg) = base ∧
          H.tableRep q.data.mem ∧
          H.seedRep q.latent q.data.mem := by
  intro H P x hbdd hb htab
  let x_prep := (P.toDynamicProgram H.encode H.decode).prepare .resample x
  have hx_prep : x_prep.Bounded w :=
    (P.toDynamicProgram H.encode H.decode).prepare_bounded hbdd (H.arguments_fit .resample)
  let x_z := x_prep.set (zeroReg 18) 0
  have he_z : Exec (B := .exact) w (.op (.const (zeroReg 18) 0)) x_prep x_z 1 := by
    simpa [x_z] using Exec.const (H.fits_space.of_le (Nat.zero_le _))
  have hx_z : x_z.Bounded w := he_z.bounded hx_prep
  have hc_pos : (Cond.eq (opReg 18) (zeroReg 18)).Holds x_z := by
    have hne : opReg 18 ≠ zeroReg 18 := by simp [opReg, zeroReg, Fin.ext_iff]
    simp [Cond.Holds, x_z, x_prep, SubroutineCode.toDynamicProgram, DynamicProgram.prepare,
      P, Impl.subroutineCode, Impl.encode, Data.set, Function.update_of_ne hne]
  have hxz_base : (x_z.comap coreReg).regs H.baseReg = base := by
    have hne_z : coreReg H.baseReg ≠ zeroReg 18 :=
      coreReg_ne_of_val_ge H.baseReg (by simp [zeroReg])
    have hne_op : coreReg H.baseReg ≠ opReg 18 :=
      coreReg_ne_of_val_ge H.baseReg (by simp [opReg])
    have hne_key : coreReg H.baseReg ≠ coreReg H.keyReg :=
      fun h => H.key_ne_base (coreReg_injective h.symm)
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, P, Impl.subroutineCode,
      hne_op, hne_key, hb]
  obtain ⟨m_res, extract, hex_res, hunif_res, hsupp_res⟩ :=
    provableImpl_resample_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
      (x := x_z.comap coreReg) (hx_z.comap coreReg) hxz_base htab
  have hex_res_ren : ExecRand w (H.resampleCode.rename coreReg) x_z
      ((fun z => (z.1.extend coreReg x_z, z.2)) <$> m_res) :=
    hex_res.rename coreReg_injective
  have hex_branch : ExecRand w
      (.branch (.eq (opReg 18) (zeroReg 18))
        (H.resampleCode.rename coreReg)
        (H.evalCode.rename coreReg))
      x_z
      ((fun z => (z.1, z.2 + 1)) <$>
        ((fun z => (z.1.extend coreReg x_z, z.2)) <$> m_res)) :=
    ExecRand.branch_pos hc_pos hex_res_ren
  have hex_code : ExecRand w P.code x_prep
      ((fun z => (z.1, 1 + z.2)) <$>
        ((fun z => (z.1, z.2 + 1)) <$>
          ((fun z => (z.1.extend coreReg x_z, z.2)) <$> m_res))) :=
    he_z.seqRand hex_branch
  let liftStep : Data 18 × ℕ → StepOutcome H.Seed PUnit 23 :=
    fun z => ⟨extract z.1.mem, z.1.extend coreReg x_z, PUnit.unit⟩
  let μ_x : PMF (StepOutcome H.Seed PUnit 23) := m_res.eval.map liftStep
  refine ⟨_, μ_x, hex_code, ?_, ?_, ?_, ?_⟩
  · rw [ProbComp.eval_map, ProbComp.eval_map, ProbComp.eval_map,
      PMF.map_comp, PMF.map_comp, PMF.map_comp, PMF.map_comp]
    rfl
  · intro z hz
    obtain ⟨z₁, hz₁, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨z₂, hz₂, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz₁
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz₂
    have hsteps : z₀.2 ≤ H.resampleSteps := (hsupp_res z₀ hz₀).2.2.2.2
    omega
  · dsimp only [μ_x, liftStep]
    rw [PMF.map_comp]
    exact hunif_res
  · intro q hq
    rw [PMF.mem_support_map_iff] at hq
    obtain ⟨z, hz, rfl⟩ := hq
    rw [ProbComp.support_eval] at hz
    obtain ⟨hz_base, hz_tab, hz_seed, hz_mod, _⟩ := hsupp_res z hz
    have hz_bdd : z.1.Bounded w := hex_res.bounded (hx_z.comap coreReg) hz
    have hreg_base : (z.1.extend coreReg x_z).regs (coreReg H.baseReg) = base := by
      change ((z.1.extend coreReg x_z).comap coreReg).regs H.baseReg = base
      rw [Data.comap_extend coreReg_injective]
      exact hz_base
    exact ⟨hz_bdd.extend coreReg_injective hx_z, rfl, hz_mod, hreg_base, hz_tab, hz_seed⟩

/-- Single `.eval u` operation execution on `P.code` via deterministic `ExecWithin`. -/
private theorem provableImpl_step_eval_execWithin (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    let P := H.subroutineCode
    ∀ (θ : H.Seed) (u : Fin U) (x : Data 23),
      x.Bounded w →
      x.regs (coreReg H.baseReg) = base →
      H.tableRep x.mem →
      H.seedRep θ x.mem →
      ∃ y_ext : Data 23,
        ExecWithin w P.code
          ((P.toDynamicProgram H.encode H.decode).prepare (.eval u) x)
          y_ext (H.evalSteps + 3) ∧
        y_ext.Bounded w ∧
        H.decode (.eval u) y_ext.regs = some (H.eval θ u) ∧
        y_ext.mem = x.mem ∧
        y_ext.regs (coreReg H.baseReg) = base := by
  intro H P θ u x hbdd hb htab hseed
  let x_prep := (P.toDynamicProgram H.encode H.decode).prepare (.eval u) x
  have hx_prep : x_prep.Bounded w :=
    (P.toDynamicProgram H.encode H.decode).prepare_bounded hbdd (H.arguments_fit (.eval u))
  let x_z := x_prep.set (zeroReg 18) 0
  have he_z : ExecWithin (B := .exact) w (.op (.const (zeroReg 18) 0)) x_prep x_z 1 := by
    simpa [x_z] using (Exec.const (H.fits_space.of_le (Nat.zero_le _))).within
  have hx_z : x_z.Bounded w := he_z.bounded hx_prep
  have hc_neg : ¬(Cond.eq (opReg 18) (zeroReg 18)).Holds x_z := by
    have hne : opReg 18 ≠ zeroReg 18 := by simp [opReg, zeroReg, Fin.ext_iff]
    simp [Cond.Holds, x_z, x_prep, SubroutineCode.toDynamicProgram, DynamicProgram.prepare,
      P, Impl.subroutineCode, Impl.encode, Data.set, Function.update_of_ne hne]
  have hxz_base : (x_z.comap coreReg).regs H.baseReg = base := by
    have hne_z : coreReg H.baseReg ≠ zeroReg 18 :=
      coreReg_ne_of_val_ge H.baseReg (by simp [zeroReg])
    have hne_op : coreReg H.baseReg ≠ opReg 18 :=
      coreReg_ne_of_val_ge H.baseReg (by simp [opReg])
    have hne_key : coreReg H.baseReg ≠ coreReg H.keyReg :=
      fun h => H.key_ne_base (coreReg_injective h.symm)
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, P, Impl.subroutineCode,
      hne_op, hne_key, hb]
  have hxz_key : (x_z.comap coreReg).regs H.keyReg = u.val := by
    have hne_z : coreReg H.keyReg ≠ zeroReg 18 :=
      coreReg_ne_of_val_ge H.keyReg (by simp [zeroReg])
    have hne_op : coreReg H.keyReg ≠ opReg 18 :=
      coreReg_ne_of_val_ge H.keyReg (by simp [opReg])
    simp [x_z, x_prep, Data.comap, Data.set, Function.update_of_ne hne_z,
      SubroutineCode.toDynamicProgram, DynamicProgram.prepare, P, Impl.subroutineCode,
      Impl.encode, hne_op]
  obtain ⟨y_core, he_eval, hy_mem, hy_base, hy_out⟩ :=
    H.eval_exec θ u (hx_z.comap coreReg) hxz_base hxz_key htab hseed
  have hy_bdd : y_core.Bounded w := he_eval.bounded (hx_z.comap coreReg)
  let y_ext : Data 23 := y_core.extend coreReg x_z
  have hy_ext_bdd : y_ext.Bounded w := hy_bdd.extend coreReg_injective hx_z
  have he_eval_ren : ExecWithin w (H.evalCode.rename coreReg) x_z y_ext H.evalSteps := by
    simpa [y_ext] using he_eval.rename coreReg_injective
  have he_branch : ExecWithin w
      (.branch (.eq (opReg 18) (zeroReg 18))
        (H.resampleCode.rename coreReg)
        (H.evalCode.rename coreReg))
      x_z y_ext (H.evalSteps + 2) :=
    ExecWithin.branch_neg hc_neg he_eval_ren
  have hy_out_ext : y_ext.regs (coreReg H.outReg) = (H.eval θ u).val := by
    change (y_ext.comap coreReg).regs H.outReg = (H.eval θ u).val
    rw [Data.comap_extend coreReg_injective]
    exact hy_out
  have hy_base_ext : y_ext.regs (coreReg H.baseReg) = base := by
    change (y_ext.comap coreReg).regs H.baseReg = base
    rw [Data.comap_extend coreReg_injective]
    exact hy_base
  refine ⟨y_ext, ?_, hy_ext_bdd, ?_, hy_mem, hy_base_ext⟩
  · have hseq := he_z.seq he_branch
    have htime : 1 + (H.evalSteps + 2) = H.evalSteps + 3 := by omega
    rwa [htime] at hseq
  · simp [Impl.decode, hy_out_ext, (H.eval θ u).isLt]

/-! ## Part 3: Polymorphic hash-family presentation and laws -/

/-- Polymorphic signature of the hash-family operations, transcripts, and multi-operation execution
relation in `HashFamiliesAbstract.lean`. -/
structure HFPresentation (S : Presentation) where
  Op : ℕ → Type
  resample {U : ℕ} : Op U
  eval {U : ℕ} : Fin U → Op U
  op_induction {U : ℕ} {motive : Op U → Prop} :
    motive resample → (∀ u : Fin U, motive (eval u)) → ∀ o : Op U, motive o
  Label : ℕ → ℕ → Type
  labelResample {U m : ℕ} : Label U m
  labelEval {U m : ℕ} : Fin U → Fin m → Label U m
  labelOp {U m : ℕ} : Label U m → Op U
  epochKeys {U : ℕ} : List (Op U) → List (Finset (Fin U))
  epochCount {U : ℕ} : List (Op U) → ℕ
  idealTranscriptFrom {U m : ℕ} [NeZero m] :
    (Fin U → Fin m) → List (Op U) → PMF (List (Label U m))
  prepareRegs {U : ℕ} : Op U → (Fin 23 → ℕ) → (Fin 23 → ℕ)
  decodeLabel {U : ℕ} (m : ℕ) : Op U → (Fin 23 → ℕ) → Option (Label U m)
  SeqState : ℕ → ℕ → Type
  mkSeqState {U m : ℕ} : (Fin 23 → ℕ) → (ℕ → ℕ) → List (Label U m) → SeqState U m
  seqReg {U m : ℕ} : SeqState U m → (Fin 23 → ℕ)
  seqMem {U m : ℕ} : SeqState U m → (ℕ → ℕ)
  seqTranscript {U m : ℕ} : SeqState U m → List (Label U m)
  StepResult : ℕ → ℕ → Type
  mkStepResult {U m : ℕ} : (Fin 23 → ℕ) → (ℕ → ℕ) → Label U m → StepResult U m
  stepReg {U m : ℕ} : StepResult U m → (Fin 23 → ℕ)
  stepMem {U m : ℕ} : StepResult U m → (ℕ → ℕ)
  stepLabel {U m : ℕ} : StepResult U m → Label U m
  opBudget {U : ℕ} : ℕ → ℕ → Op U → ℕ
  RunsOps {U m : ℕ} :
    ℕ → List (S.Instr 23) → ℕ → ℕ → ℕ → ℕ →
      List (Op U) → PMF (SeqState U m) → PMF (SeqState U m) → Prop

namespace HFPresentation

variable {S : Presentation} (P : HFPresentation S)

/-- Word-boundedness of `(reg, mem)` at word width `w`. -/
def WordBounded {r : ℕ} (w : ℕ) (reg : Fin r → ℕ) (mem : ℕ → ℕ) : Prop :=
  (∀ i, reg i < 2 ^ w) ∧ ∀ a, mem a < 2 ^ w

/-- Memory preservation outside `[base, base + sp)`. -/
def UnchangedOutside (base sp : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ∀ a, (a < base ∨ base + sp ≤ a) → mem' a = mem a

/-- Append a completed step `q` to `t`. -/
def appendStep {U m : ℕ} (t : P.SeqState U m) (q : P.StepResult U m) : P.SeqState U m :=
  P.mkSeqState (P.stepReg q) (P.stepMem q) (P.seqTranscript t ++ [P.stepLabel q])

/-- `k`-bounded distinct queried keys per resampling epoch. -/
def BoundedEpochKeys {U : ℕ} (k : ℕ) (ops : List (P.Op U)) : Prop :=
  ∀ E ∈ P.epochKeys ops, E.card ≤ k

/-- Ideal uniform random-function transcript distribution on `ops`. -/
noncomputable def idealTranscriptPMF {U m : ℕ} [NeZero m] (ops : List (P.Op U)) :
    PMF (List (P.Label U m)) :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin U → Fin m)).bind fun f₀ =>
    P.idealTranscriptFrom f₀ ops

/-- Every label in `tr` matches the corresponding operation in `ops`. -/
def TranscriptMatches {U m : ℕ} (ops : List (P.Op U)) (tr : List (P.Label U m)) : Prop :=
  tr.map P.labelOp = ops

/-- Existence of a coupling `γ` with marginals `μ` and `ν` and disagreement probability `≤ ε`. -/
def CoupledWithin {α : Type} (μ ν : PMF α) (ε : ℝ≥0∞) : Prop :=
  ∃ γ : PMF (α × α),
    γ.map Prod.fst = μ ∧
    γ.map Prod.snd = ν ∧
    γ.toOuterMeasure {p : α × α | p.1 ≠ p.2} ≤ ε

/-- High-probability `k`-wise independence contract on `P.Label U m` transcripts. -/
def WhpKWiseContract {U m : ℕ} [NeZero m] (δ : ℝ≥0∞)
    (ops : List (P.Op U)) (μ : PMF (List (P.Label U m))) : Prop :=
  (∀ tr ∈ μ.support, P.TranscriptMatches ops tr) ∧
  CoupledWithin μ (P.idealTranscriptPMF (m := m) ops) ((P.epochCount ops : ℝ≥0∞) * δ)

end HFPresentation

/-- Equational and inductive laws connecting an `HFPresentation S` to the definitions in
`HashFamiliesAbstract.lean`. -/
structure HFLaws (S : Presentation) (P : HFPresentation S) : Prop where
  labelOp_resample : ∀ {U m : ℕ}, P.labelOp (P.labelResample (U := U) (m := m)) = P.resample
  labelOp_eval : ∀ {U m : ℕ} (u : Fin U) (y : Fin m), P.labelOp (P.labelEval u y) = P.eval u
  epochKeys_nil : ∀ {U : ℕ}, P.epochKeys ([] : List (P.Op U)) = [∅]
  epochKeys_resample : ∀ {U : ℕ} (ops : List (P.Op U)),
    P.epochKeys (P.resample :: ops) = ∅ :: P.epochKeys ops
  epochKeys_eval : ∀ {U : ℕ} (u : Fin U) (ops : List (P.Op U)),
    P.epochKeys (P.eval u :: ops) =
      match P.epochKeys ops with
      | [] => [{u}]
      | E :: rest => insert u E :: rest
  epochCount_nil : ∀ {U : ℕ}, P.epochCount ([] : List (P.Op U)) = 1
  epochCount_resample : ∀ {U : ℕ} (ops : List (P.Op U)),
    P.epochCount (P.resample :: ops) = P.epochCount ops + 1
  epochCount_eval : ∀ {U : ℕ} (u : Fin U) (ops : List (P.Op U)),
    P.epochCount (P.eval u :: ops) = P.epochCount ops
  idealTranscriptFrom_nil : ∀ {U m : ℕ} [NeZero m] (f : Fin U → Fin m),
    P.idealTranscriptFrom f ([] : List (P.Op U)) = PMF.pure []
  idealTranscriptFrom_eval : ∀ {U m : ℕ} [NeZero m] (f : Fin U → Fin m)
    (u : Fin U) (ops : List (P.Op U)),
    P.idealTranscriptFrom f (P.eval u :: ops) =
      (P.idealTranscriptFrom f ops).map fun rest => P.labelEval u (f u) :: rest
  idealTranscriptFrom_resample : ∀ {U m : ℕ} [NeZero m] (f : Fin U → Fin m)
    (ops : List (P.Op U)),
    P.idealTranscriptFrom f (P.resample :: ops) =
      (Cslib.Probability.PMF.uniformOfFintype (Fin U → Fin m)).bind fun f' =>
        (P.idealTranscriptFrom f' ops).map fun rest => P.labelResample :: rest
  prepareRegs_resample : ∀ {U : ℕ} (reg : Fin 23 → ℕ) (i : Fin 23),
    P.prepareRegs (P.resample (U := U)) reg i =
      if decide (i = ⟨18, by decide⟩ ∨ i = ⟨1, by decide⟩) then 0 else reg i
  prepareRegs_eval : ∀ {U : ℕ} (u : Fin U) (reg : Fin 23 → ℕ) (i : Fin 23),
    P.prepareRegs (P.eval u) reg i =
      if decide (i = ⟨18, by decide⟩ ∨ i = ⟨1, by decide⟩) then
        if i = ⟨18, by decide⟩ then 1
        else if i = ⟨1, by decide⟩ then u.val
        else 0
      else reg i
  decodeLabel_resample : ∀ {U m : ℕ} (reg : Fin 23 → ℕ),
    P.decodeLabel m (P.resample (U := U)) reg = some P.labelResample
  decodeLabel_eval : ∀ {U m : ℕ} (u : Fin U) (reg : Fin 23 → ℕ),
    P.decodeLabel m (P.eval u) reg =
      if h : reg ⟨2, by decide⟩ < m then some (P.labelEval u ⟨reg ⟨2, by decide⟩, h⟩) else none
  seqReg_mk : ∀ {U m : ℕ} (reg : Fin 23 → ℕ) (mem : ℕ → ℕ) (tr : List (P.Label U m)),
    P.seqReg (P.mkSeqState reg mem tr) = reg
  seqMem_mk : ∀ {U m : ℕ} (reg : Fin 23 → ℕ) (mem : ℕ → ℕ) (tr : List (P.Label U m)),
    P.seqMem (P.mkSeqState reg mem tr) = mem
  seqTranscript_mk : ∀ {U m : ℕ} (reg : Fin 23 → ℕ) (mem : ℕ → ℕ) (tr : List (P.Label U m)),
    P.seqTranscript (P.mkSeqState reg mem tr) = tr
  stepReg_mk : ∀ {U m : ℕ} (reg : Fin 23 → ℕ) (mem : ℕ → ℕ) (lbl : P.Label U m),
    P.stepReg (P.mkStepResult reg mem lbl) = reg
  stepMem_mk : ∀ {U m : ℕ} (reg : Fin 23 → ℕ) (mem : ℕ → ℕ) (lbl : P.Label U m),
    P.stepMem (P.mkStepResult reg mem lbl) = mem
  stepLabel_mk : ∀ {U m : ℕ} (reg : Fin 23 → ℕ) (mem : ℕ → ℕ) (lbl : P.Label U m),
    P.stepLabel (P.mkStepResult reg mem lbl) = lbl
  opBudget_resample : ∀ {U : ℕ} (t_eval t_res : ℕ),
    P.opBudget t_eval t_res (P.resample (U := U)) = t_res
  opBudget_eval : ∀ {U : ℕ} (t_eval t_res : ℕ) (u : Fin U),
    P.opBudget t_eval t_res (P.eval u) = t_eval
  runsOps_nil : ∀ {U m w : ℕ} {p_op : List (S.Instr 23)} {base sp t_eval t_res : ℕ}
    (ν : PMF (P.SeqState U m)),
    P.RunsOps w p_op base sp t_eval t_res [] ν ν
  runsOps_cons : ∀ {U m w : ℕ} {p_op : List (S.Instr 23)} {base sp t_eval t_res : ℕ}
    {o : P.Op U} {ops : List (P.Op U)} {ν ν_final : PMF (P.SeqState U m)}
    (μ_step : P.SeqState U m → PMF (P.StepResult U m)),
    (∀ t ∈ ν.support,
      let s_in := S.state 0 (P.prepareRegs o (P.seqReg t)) (P.seqMem t)
      let T := P.opBudget t_eval t_res o
      HFPresentation.WordBounded w (P.seqReg t) (P.seqMem t) ∧
      S.HaltsWithin w p_op s_in T ∧
      S.evalRand w p_op T s_in =
        (μ_step t).map (fun q =>
          S.halted (P.stepReg q ⟨2, by decide⟩) (P.stepReg q) (P.stepMem q)) ∧
      (∀ u, o = P.eval u → ∃ q, μ_step t = PMF.pure q ∧ P.stepMem q = P.seqMem t) ∧
      ∀ q ∈ (μ_step t).support,
        HFPresentation.WordBounded w (P.stepReg q) (P.stepMem q) ∧
        P.decodeLabel m o (P.stepReg q) = some (P.stepLabel q) ∧
        HFPresentation.UnchangedOutside base sp (P.seqMem t) (P.stepMem q)) →
    P.RunsOps w p_op base sp t_eval t_res ops
      (ν.bind fun t => (μ_step t).map (P.appendStep t))
      ν_final →
    P.RunsOps w p_op base sp t_eval t_res (o :: ops) ν ν_final

/-! ### Library epoch-key list correspondence and full-independence of `Fin U → Fin m` -/

/-- Structural list of per-epoch key sets on `HashFamily.Op U`. -/
private def libEpochKeys {U : ℕ} : List (HashFamily.Op U) → List (Finset (Fin U))
  | [] => [∅]
  | .resample :: ops => ∅ :: libEpochKeys ops
  | .eval u :: ops =>
      match libEpochKeys ops with
      | [] => [{u}]
      | E :: rest => insert u E :: rest

/-- Tail of `libEpochKeys ops` after the current epoch. -/
private def tailEpochKeys {U : ℕ} : List (HashFamily.Op U) → List (Finset (Fin U))
  | [] => []
  | .resample :: ops => libEpochKeys ops
  | .eval _ :: ops => tailEpochKeys ops

private theorem libEpochKeys_eq_cons {U : ℕ} (ops : List (HashFamily.Op U)) :
    libEpochKeys ops = HashFamily.currentEpochKeys ops :: tailEpochKeys ops := by
  induction ops with
  | nil => rfl
  | cons o os ih =>
    cases o with
    | resample => rfl
    | eval u =>
      dsimp only [libEpochKeys, HashFamily.currentEpochKeys, tailEpochKeys]
      rw [ih]

private theorem tailEpochKeys_eq_of_afterCurrentEpoch_eq_some {U : ℕ}
    {ops rest : List (HashFamily.Op U)}
    (hafter : HashFamily.afterCurrentEpoch ops = some rest) :
    tailEpochKeys ops = libEpochKeys rest := by
  induction ops with
  | nil => cases hafter
  | cons o os ih =>
    cases o with
    | resample =>
      injection hafter with hEq
      subst hEq
      rfl
    | eval _ =>
      exact ih hafter

private theorem boundedEpochKeys_of_libEpochKeys {U k : ℕ} (ops : List (HashFamily.Op U))
    (h : ∀ E ∈ libEpochKeys ops, E.card ≤ k) :
    HashFamily.BoundedEpochKeys k ops := by
  rw [HashFamily.BoundedEpochKeys]
  refine ⟨?_, ?_⟩
  · refine h (HashFamily.currentEpochKeys ops) ?_
    rw [libEpochKeys_eq_cons]
    exact List.mem_cons_self
  · cases hafter : HashFamily.afterCurrentEpoch ops with
    | none => trivial
    | some rest =>
      have hsub : ∀ E ∈ libEpochKeys rest, E.card ≤ k := by
        intro E hE
        refine h E ?_
        rw [libEpochKeys_eq_cons, tailEpochKeys_eq_of_afterCurrentEpoch_eq_some hafter]
        exact List.mem_cons_of_mem _ hE
      exact boundedEpochKeys_of_libEpochKeys rest hsub
termination_by ops.length
decreasing_by exact HashFamily.length_lt_of_afterCurrentEpoch_eq_some hafter

private theorem boundedEpochKeys_univ {U : ℕ} (ops : List (HashFamily.Op U)) :
    HashFamily.BoundedEpochKeys U ops := by
  refine boundedEpochKeys_of_libEpochKeys ops fun E _ => ?_
  simpa using Finset.card_le_univ E

private theorem isKWiseIndependentHash_id_two_pow (k U M : ℕ) :
    IsKWiseIndependentHash k (id : (Fin U → Fin (2 ^ M)) → Fin U → Fin (2 ^ M)) := by
  have hbits : IsKWiseIndependentHash k
      (fun (i : Fin U → BitString M) (u : Fin U) => i u) := by
    refine isKWiseIndependentHash_of_surjective (AddMonoidHom.id (Fin U → BitString M))
      fun T _ c => ?_
    refine ⟨fun u => if hu : u ∈ T then c ⟨u, hu⟩ else 0, funext fun ⟨u, hu⟩ => ?_⟩
    simp [Finset.restrict, hu]
  have hseed := (hbits.map_equiv (BitString.equivFin M)).comp_seedEquiv
    (Equiv.piCongrRight fun _ : Fin U => (BitString.equivFin M).symm)
  have hfn :
      (fun (i' : Fin U → Fin (2 ^ M)) (x : Fin U) =>
        (BitString.equivFin M)
          ((Equiv.piCongrRight fun _ : Fin U => (BitString.equivFin M).symm) i' x)) =
        (id : (Fin U → Fin (2 ^ M)) → Fin U → Fin (2 ^ M)) := by
    funext i' x
    exact (BitString.equivFin M).apply_symm_apply (i' x)
  rwa [hfn] at hseed

namespace HFPresentation

variable {S : Presentation} (P : HFPresentation S)

/-- Translate a library `HashFamily.Op U` to `P.Op U`. -/
def opOf {U : ℕ} : HashFamily.Op U → P.Op U
  | .resample => P.resample
  | .eval u => P.eval u

/-- Translate a library `HashFamily.Label U m` to `P.Label U m`. -/
def labelOf {U m : ℕ} : HashFamily.Label U m → P.Label U m
  | ⟨.resample, _⟩ => P.labelResample
  | ⟨.eval u, y⟩ => P.labelEval u y

/-- Translate a library `SeqOutcome Latent (HashFamily.Result m) 23` to `P.SeqState U m`. -/
def seqStateOf {Latent : Type} {U m : ℕ}
    (t : SeqOutcome Latent (@HashFamily.Result U m) 23) : P.SeqState U m :=
  P.mkSeqState t.data.regs t.data.mem (t.transcript.map P.labelOf)

/-- Translate a library `LatentState Latent 23` (with empty initial transcript) to
`P.SeqState U m`. -/
def initSeqStateOf {Latent : Type} {U m : ℕ}
    (t : LatentState Latent 23) : P.SeqState U m :=
  P.mkSeqState t.data.regs t.data.mem []

theorem opOf_surjective {U : ℕ} (o : P.Op U) : ∃ o_lib : HashFamily.Op U, P.opOf o_lib = o :=
  P.op_induction (motive := fun o => ∃ o_lib : HashFamily.Op U, P.opOf o_lib = o)
    ⟨.resample, rfl⟩ (fun u => ⟨.eval u, rfl⟩) o

theorem list_opOf_surjective {U : ℕ} (ops : List (P.Op U)) :
    ∃ ops_lib : List (HashFamily.Op U), ops_lib.map P.opOf = ops := by
  induction ops with
  | nil => exact ⟨[], rfl⟩
  | cons o os ih =>
    obtain ⟨o_lib, rfl⟩ := P.opOf_surjective o
    obtain ⟨os_lib, rfl⟩ := ih
    exact ⟨o_lib :: os_lib, rfl⟩

theorem epochKeys_map_opOf (hP : HFLaws S P) {U : ℕ} (ops : List (HashFamily.Op U)) :
    P.epochKeys (ops.map P.opOf) = libEpochKeys ops := by
  induction ops with
  | nil => exact hP.epochKeys_nil
  | cons o os ih =>
    cases o with
    | resample =>
      change P.epochKeys (P.resample :: os.map P.opOf) = ∅ :: libEpochKeys os
      rw [hP.epochKeys_resample, ih]
    | eval u =>
      change P.epochKeys (P.eval u :: os.map P.opOf) = _
      rw [hP.epochKeys_eval, ih]
      rfl

theorem epochCount_map_opOf (hP : HFLaws S P) {U : ℕ} (ops : List (HashFamily.Op U)) :
    P.epochCount (ops.map P.opOf) = HashFamily.epochCount ops := by
  induction ops with
  | nil => exact hP.epochCount_nil
  | cons o os ih =>
    cases o with
    | resample =>
      change P.epochCount (P.resample :: os.map P.opOf) = HashFamily.epochCount (.resample :: os)
      rw [hP.epochCount_resample, ih]
      dsimp only [HashFamily.epochCount, HashFamily.resampleCount]
      omega
    | eval u =>
      change P.epochCount (P.eval u :: os.map P.opOf) = HashFamily.epochCount (.eval u :: os)
      rw [hP.epochCount_eval, ih]
      rfl

theorem labelOp_labelOf (hP : HFLaws S P) {U m : ℕ} (lbl : HashFamily.Label U m) :
    P.labelOp (P.labelOf lbl) = P.opOf lbl.1 := by
  rcases lbl with ⟨_ | u, res⟩
  · exact hP.labelOp_resample
  · exact hP.labelOp_eval u res

theorem idealTranscriptFrom_map_opOf (hP : HFLaws S P) {U m : ℕ} [NeZero m]
    (f : Fin U → Fin m) (ops : List (HashFamily.Op U)) :
    P.idealTranscriptFrom f (ops.map P.opOf) =
      (HashFamily.evalOpsFromSeed (PMF.uniformOfFintype (Fin U → Fin m)) id f ops).map
        (List.map P.labelOf) := by
  induction ops generalizing f with
  | nil =>
    change P.idealTranscriptFrom f [] = _
    rw [hP.idealTranscriptFrom_nil, HashFamily.evalOpsFromSeed, PMF.pure_map]
    rfl
  | cons o os ih =>
    cases o with
    | eval u =>
      change P.idealTranscriptFrom f (P.eval u :: os.map P.opOf) = _
      rw [hP.idealTranscriptFrom_eval, ih f, HashFamily.evalOpsFromSeed, PMF.map_comp,
        PMF.map_comp]
      rfl
    | resample =>
      change P.idealTranscriptFrom f (P.resample :: os.map P.opOf) = _
      rw [hP.idealTranscriptFrom_resample, HashFamily.evalOpsFromSeed, PMF.map_bind]
      refine congrArg ((PMF.uniformOfFintype (Fin U → Fin m)).bind ·) (funext fun f' => ?_)
      rw [ih f', PMF.map_comp, PMF.map_comp]
      rfl

theorem idealTranscriptPMF_map_opOf (hP : HFLaws S P) {U M : ℕ}
    (ops : List (HashFamily.Op U)) :
    P.idealTranscriptPMF (m := 2 ^ M) (ops.map P.opOf) =
      (HashFamily.idealTranscriptPMF (2 ^ M) ops).map (List.map P.labelOf) := by
  have hid : HashFamily.evalOps (PMF.uniformOfFintype (Fin U → Fin (2 ^ M))) id ops =
      HashFamily.idealTranscriptPMF (2 ^ M) ops :=
    HashFamily.kWiseSpec_contract_evalOps (isKWiseIndependentHash_id_two_pow U U M)
      (boundedEpochKeys_univ ops)
  rw [← hid]
  dsimp only [idealTranscriptPMF, HashFamily.evalOps]
  rw [PMF.map_bind]
  refine congrArg ((PMF.uniformOfFintype (Fin U → Fin (2 ^ M))).bind ·) (funext fun f₀ => ?_)
  exact P.idealTranscriptFrom_map_opOf hP f₀ ops

/-- Pushing a coupling `PMF.CoupledWithin μ ν ε` forward along any map `f : α → β` preserves the
disagreement bound `ε`, and can be weakened to any `ε' ≥ ε`. -/
theorem coupledWithin_map_mono {α β : Type} {μ ν : PMF α} {ε ε' : ℝ≥0∞} (f : α → β)
    (h : PMF.CoupledWithin μ ν ε) (hle : ε ≤ ε') :
    HFPresentation.CoupledWithin (μ.map f) (ν.map f) ε' := by
  obtain ⟨γ, hfst, hsnd, hmeas⟩ := h
  refine ⟨γ.map (Prod.map f f), ?_, ?_, ?_⟩
  · rw [PMF.map_comp, ← hfst, PMF.map_comp]
    rfl
  · rw [PMF.map_comp, ← hsnd, PMF.map_comp]
    rfl
  · rw [PMF.toOuterMeasure_map_apply]
    have hsub : Prod.map f f ⁻¹' {q : β × β | q.1 ≠ q.2} ⊆ {p : α × α | p.1 ≠ p.2} :=
      fun p hp heq => hp (congrArg f heq)
    exact ((γ.toOuterMeasure.mono hsub).trans hmeas).trans hle

/-- Transfer `(HashFamily.whpKWiseSpec k U (2 ^ M) δ).Contract ops μ` along `P.opOf` and `P.labelOf`
to `P.WhpKWiseContract δ' (ops.map P.opOf) (μ.map (List.map P.labelOf))` whenever `δ ≤ δ'`. -/
theorem whpKWiseContract_map (hP : HFLaws S P) {U M k : ℕ} {δ δ' : ℝ≥0∞}
    {ops : List (HashFamily.Op U)} {μ : PMF (List (HashFamily.Label U (2 ^ M)))}
    (hc : (HashFamily.whpKWiseSpec k U (2 ^ M) δ).Contract ops μ) (hδ : δ ≤ δ') :
    P.WhpKWiseContract δ' (ops.map P.opOf) (μ.map (List.map P.labelOf)) := by
  refine ⟨?_, ?_⟩
  · intro tr_abs htr_abs
    rw [PMF.mem_support_map_iff] at htr_abs
    obtain ⟨tr, htr, rfl⟩ := htr_abs
    have hmatch : tr.map Sigma.fst = ops := hc.1 tr htr
    dsimp only [TranscriptMatches]
    rw [List.map_map]
    have hcomp : P.labelOp ∘ P.labelOf = P.opOf ∘ (@Sigma.fst (HashFamily.Op U)
        (@HashFamily.Result U (2 ^ M))) :=
      funext (P.labelOp_labelOf hP)
    rw [hcomp, ← List.map_map, hmatch]
  · rw [P.idealTranscriptPMF_map_opOf hP, P.epochCount_map_opOf hP]
    exact coupledWithin_map_mono (List.map P.labelOf) hc.2
      (mul_le_mul_right hδ (HashFamily.epochCount ops : ℝ≥0∞))

end HFPresentation

/-! ## Part 4: Multi-operation `RunsOps` induction for `provableImpl c_exp` -/

private theorem prepare_eq_prepareRegs {S : Presentation} {P : HFPresentation S} (hP : HFLaws S P)
    (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (o : HashFamily.Op U) (x : Data 23) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare o x).regs =
      P.prepareRegs (P.opOf o) x.regs := by
  intro H
  have hkey : H.keyReg = 1 :=
    provableImpl_keyReg c_exp k n_max U M hw hfit_space hfit_n hfit_U
  have hinput : H.subroutineCode.input =
      fun i : Fin 23 => decide (i = ⟨18, by decide⟩ ∨ i = ⟨1, by decide⟩) := by
    funext i
    dsimp only [Impl.subroutineCode]
    rw [hkey]
    rfl
  funext i
  cases o with
  | resample =>
    change (if H.subroutineCode.input i then H.encode .resample i else x.regs i) =
      P.prepareRegs P.resample x.regs i
    rw [hP.prepareRegs_resample, hinput]
    rfl
  | eval u =>
    change (if H.subroutineCode.input i then H.encode (.eval u) i else x.regs i) =
      P.prepareRegs (P.eval u) x.regs i
    rw [hP.prepareRegs_eval, hinput]
    have henc : H.encode (.eval u) i =
        if i = ⟨18, by decide⟩ then 1 else if i = ⟨1, by decide⟩ then u.val else 0 := by
      dsimp only [Impl.encode]
      rw [hkey]
      rfl
    rw [henc]

private theorem decode_eq_decodeLabel {S : Presentation} {P : HFPresentation S} (hP : HFLaws S P)
    (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (o : HashFamily.Op U) (reg : Fin 23 → ℕ) (res : HashFamily.Result (2 ^ M) o) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    H.decode o reg = some res →
    P.decodeLabel (2 ^ M) (P.opOf o) reg = some (P.labelOf ⟨o, res⟩) := by
  intro H hdec
  have hout : coreReg H.outReg = (⟨2, by decide⟩ : Fin 23) := by
    rw [provableImpl_outReg c_exp k n_max U M hw hfit_space hfit_n hfit_U]
    rfl
  cases o with
  | resample =>
    exact hP.decodeLabel_resample reg
  | eval u =>
    change P.decodeLabel (2 ^ M) (P.eval u) reg = some (P.labelEval u res)
    rw [hP.decodeLabel_eval]
    dsimp only [Impl.decode] at hdec
    rw [hout] at hdec
    split_ifs at hdec with hlt
    cases hdec
    exact dite_eq_left_of_eq_true (eq_true hlt)

/-- Multi-operation execution along `remOps : List (HashFamily.Op U)` from any state distribution
`ν` satisfying the representation invariant of `H := provableImpl c_exp k n_max U M ...`:
produces `ν_final` such that `P.RunsOps` holds on `ν.map P.seqStateOf` and
`ν_final.map P.seqStateOf` and the transcript marginal equals `ν.bind (... evalOpsFromSeed ...)`. -/
private theorem provableImpl_runsOps_aux {S : Presentation} {P : HFPresentation S}
    (hS : Laws S) (hP : HFLaws S P)
    (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5)
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1)) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    let p_op := S.programOf (H.subroutineCode.code.program (coreReg 2))
    ∀ (remOps : List (HashFamily.Op U))
      (ν : PMF (SeqOutcome H.Seed (@HashFamily.Result U (2 ^ M)) 23)),
      (∀ t ∈ ν.support,
        t.data.Bounded w ∧
        t.data.regs (coreReg H.baseReg) = base ∧
        H.tableRep t.data.mem ∧
        H.seedRep t.latent t.data.mem) →
      ∃ ν_final : PMF (SeqOutcome H.Seed (@HashFamily.Result U (2 ^ M)) 23),
        P.RunsOps w p_op base (provableSpace c_exp k n_max)
          (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
          (remOps.map P.opOf) (ν.map P.seqStateOf) (ν_final.map P.seqStateOf) ∧
        ν_final.map SeqOutcome.transcript =
          ν.bind (fun t =>
            (HashFamily.evalOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval t.latent
              remOps).map (fun suf => t.transcript ++ suf)) := by
  intro H p_op remOps
  have hsp_eq : H.space = provableSpace c_exp k n_max :=
    provableImpl_space c_exp k n_max U M hw hfit_space hfit_n hfit_U
  have heval_le : (H.evalSteps + 3) + 1 ≤ provableEvalBound c_exp k + 4 := by
    have hle : H.evalSteps ≤ provableEvalBound c_exp k :=
      provableImpl_evalSteps_le hU hM hw hfit_space hfit_n hfit_U
    omega
  have hres_le : (H.resampleSteps + 2) + 1 ≤ resampleTimeOf c_exp k n_max := by
    rw [← provableImpl_resampleSteps_eq c_exp k n_max U M hw hfit_space hfit_n hfit_U]
  induction remOps with
  | nil =>
    intro ν _
    refine ⟨ν, hP.runsOps_nil (ν.map P.seqStateOf), ?_⟩
    ext tr
    simp [HashFamily.evalOpsFromSeed]
  | cons o os ih =>
    intro ν hsupp
    cases o with
    | resample =>
      classical
      let hasInv (x : Data 23) : Prop :=
        x.Bounded w ∧ x.regs (coreReg H.baseReg) = base ∧ H.tableRep x.mem
      let θ₀ : H.Seed := Classical.arbitrary H.Seed
      let μ_data (x : Data 23) : PMF (StepOutcome H.Seed PUnit 23) :=
        if hx : hasInv x then
          (Classical.choose_spec
            (provableImpl_step_resample_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U x
              hx.1 hx.2.1 hx.2.2)).choose
        else
          PMF.pure ⟨θ₀, x, PUnit.unit⟩
      let μ_lib (t : SeqOutcome H.Seed (@HashFamily.Result U (2 ^ M)) 23) :
          PMF (StepOutcome H.Seed PUnit 23) :=
        μ_data t.data
      let stepResultOf (q : StepOutcome H.Seed PUnit 23) : P.StepResult U (2 ^ M) :=
        P.mkStepResult q.data.regs q.data.mem P.labelResample
      let μ_abs (t_abs : P.SeqState U (2 ^ M)) : PMF (P.StepResult U (2 ^ M)) :=
        (μ_data ⟨P.seqReg t_abs, P.seqMem t_abs⟩).map stepResultOf
      let ν₁ := ν.bind fun t => (μ_lib t).map (t.appendStep .resample)
      have hsupp₁ : ∀ q_seq ∈ ν₁.support,
          q_seq.data.Bounded w ∧
          q_seq.data.regs (coreReg H.baseReg) = base ∧
          H.tableRep q_seq.data.mem ∧
          H.seedRep q_seq.latent q_seq.data.mem := by
        intro q_seq hq_seq
        rw [PMF.mem_support_bind_iff] at hq_seq
        obtain ⟨t, ht, hq_map⟩ := hq_seq
        rw [PMF.mem_support_map_iff] at hq_map
        obtain ⟨q, hq, rfl⟩ := hq_map
        have ht_inv : hasInv t.data := ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1⟩
        have hμ_eq : μ_lib t =
            (Classical.choose_spec
              (provableImpl_step_resample_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
                t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2)).choose := by
          simp [μ_lib, μ_data, ht_inv]
        rw [hμ_eq] at hq
        have hspec := (Classical.choose_spec
          (Classical.choose_spec
            (provableImpl_step_resample_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
              t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2))).2.2.2.2 q hq
        exact ⟨hspec.1, hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩
      obtain ⟨ν_final, hruns_rest, htr_rest⟩ := ih ν₁ hsupp₁
      have hν₁_map :
          ((ν.map P.seqStateOf).bind fun t_abs => (μ_abs t_abs).map (P.appendStep t_abs)) =
            ν₁.map P.seqStateOf := by
        dsimp only [ν₁, μ_abs, μ_lib]
        rw [PMF.bind_map, PMF.map_bind]
        refine congrArg (ν.bind ·) (funext fun t => ?_)
        dsimp only [Function.comp_apply, HFPresentation.seqStateOf]
        rw [hP.seqReg_mk, hP.seqMem_mk, PMF.map_comp, PMF.map_comp]
        refine congrArg ((μ_data t.data).map ·) (funext fun q => ?_)
        dsimp only [Function.comp_apply, stepResultOf, HFPresentation.appendStep,
          SeqOutcome.appendStep, HFPresentation.seqStateOf]
        rw [hP.stepReg_mk, hP.stepMem_mk, hP.stepLabel_mk, hP.seqTranscript_mk, List.map_append]
        rfl
      rw [← hν₁_map] at hruns_rest
      have hruns_cons :
          P.RunsOps w p_op base (provableSpace c_exp k n_max)
            (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
            (P.resample :: os.map P.opOf) (ν.map P.seqStateOf) (ν_final.map P.seqStateOf) := by
        refine hP.runsOps_cons μ_abs (fun t_abs ht_abs => ?_) hruns_rest
        rw [PMF.mem_support_map_iff] at ht_abs
        obtain ⟨t, ht, rfl⟩ := ht_abs
        have hreg_t : P.seqReg (P.seqStateOf t) = t.data.regs :=
          hP.seqReg_mk t.data.regs t.data.mem (t.transcript.map P.labelOf)
        have hmem_t : P.seqMem (P.seqStateOf t) = t.data.mem :=
          hP.seqMem_mk t.data.regs t.data.mem (t.transcript.map P.labelOf)
        dsimp only
        rw [hreg_t, hmem_t]
        have ht_inv : hasInv t.data := ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1⟩
        have hEx := provableImpl_step_resample_execRand c_exp k n_max U M hw hfit_space hfit_n
          hfit_U t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2
        let m_step := Classical.choose hEx
        have hspec := Classical.choose_spec (Classical.choose_spec hEx)
        have hμ_eq : μ_abs (P.seqStateOf t) =
            (hEx.choose_spec.choose).map stepResultOf := by
          dsimp only [μ_abs, HFPresentation.seqStateOf]
          rw [hP.seqReg_mk, hP.seqMem_mk]
          simp [μ_data, ht_inv]
        have hprep_regs :
            P.prepareRegs (P.resample (U := U)) t.data.regs =
              ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare
                .resample t.data).regs :=
          (prepare_eq_prepareRegs hP c_exp k n_max U M hw hfit_space hfit_n hfit_U
            .resample t.data).symm
        have hbud : P.opBudget (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
            (P.resample (U := U)) = resampleTimeOf c_exp k n_max :=
          hP.opBudget_resample (U := U) _ _
        have hex_m : ExecRand w H.subroutineCode.code
            ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare .resample t.data)
            m_step := hspec.1
        have hcomp := compile_execRand hS hex_m (T := resampleTimeOf c_exp k n_max) fun z hz =>
          (Nat.add_le_add_right (hspec.2.2.1 z hz) 1).trans hres_le
        refine ⟨ht_inv.1, ?_, ?_, ?_, ?_⟩
        · rw [hprep_regs, hbud]
          exact hcomp.1
        · rw [hprep_regs, hbud, hμ_eq, PMF.map_comp]
          refine hcomp.2.2.trans ?_
          have hfst := hspec.2.1
          have hmap :
              (m_step.eval).map (fun z =>
                S.halted (z.1.regs (coreReg 2)) z.1.regs z.1.mem) =
              (m_step.eval.map Prod.fst).map (fun d : Data 23 =>
                S.halted (d.regs (coreReg 2)) d.regs d.mem) := by
            rw [PMF.map_comp]
            rfl
          rw [hmap]
          refine (congrArg
            (PMF.map fun d : Data 23 => S.halted (d.regs (coreReg 2)) d.regs d.mem) hfst).trans ?_
          rw [PMF.map_comp]
          refine congrArg ((hEx.choose_spec.choose).map ·) (funext fun q => ?_)
          dsimp only [Function.comp_apply, stepResultOf]
          rw [hP.stepReg_mk, hP.stepMem_mk]
          rfl
        · intro u heq
          exfalso
          have hcnt1 := congrArg (fun op => P.epochCount [op]) heq
          rw [hP.epochCount_resample, hP.epochCount_eval, hP.epochCount_nil] at hcnt1
          omega
        · intro q_abs hq_abs
          rw [hμ_eq, PMF.mem_support_map_iff] at hq_abs
          obtain ⟨q, hq, rfl⟩ := hq_abs
          have hq_spec := hspec.2.2.2.2 q hq
          dsimp only [stepResultOf]
          rw [hP.stepReg_mk, hP.stepMem_mk, hP.stepLabel_mk]
          refine ⟨hq_spec.1, hP.decodeLabel_resample q.data.regs, ?_⟩
          intro a ha
          rw [← hsp_eq] at ha
          have ha' : a ∉ (Block.mk base H.space).footprint := by
            rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
            exact ha
          exact hq_spec.2.2.1 a ha'
      refine ⟨ν_final, hruns_cons, ?_⟩
      rw [htr_rest]
      dsimp only [ν₁]
      rw [PMF.bind_bind]
      refine PMF.bind_congr_on_support _ _ _ fun t ht => ?_
      have ht_inv : hasInv t.data := ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1⟩
      have hEx := provableImpl_step_resample_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
        t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2
      have hμ_eq : μ_lib t = hEx.choose_spec.choose := by
        simp [μ_lib, μ_data, ht_inv]
      have hunif_t : (μ_lib t).map StepOutcome.latent = PMF.uniformOfFintype H.Seed := by
        rw [hμ_eq]
        exact (Classical.choose_spec (Classical.choose_spec hEx)).2.2.2.1
      rw [PMF.bind_map, HashFamily.evalOpsFromSeed, PMF.map_bind, ← hunif_t, PMF.bind_map]
      refine congrArg ((μ_lib t).bind ·) (funext fun q => ?_)
      rcases q with ⟨θ', x_q, ⟨⟩⟩
      dsimp only [Function.comp_apply, StepOutcome.latent]
      rw [PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun suf => ?_)
      simp [SeqOutcome.appendStep]
    | eval u =>
      classical
      let hasEvalInv (x : Data 23) : Prop :=
        x.Bounded w ∧ x.regs (coreReg H.baseReg) = base ∧ H.tableRep x.mem ∧
        ∃ θ : H.Seed, H.seedRep θ x.mem
      let θOf (x : Data 23) : H.Seed :=
        if hx : hasEvalInv x then Classical.choose hx.2.2.2 else Classical.arbitrary H.Seed
      let yOf (x : Data 23) : Data 23 :=
        if hx : hasEvalInv x then
          Classical.choose
            (provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
              (Classical.choose hx.2.2.2) u x hx.1 hx.2.1 hx.2.2.1
              (Classical.choose_spec hx.2.2.2))
        else
          x
      let μ_lib (t : SeqOutcome H.Seed (@HashFamily.Result U (2 ^ M)) 23) :
          PMF (StepOutcome H.Seed (Fin (2 ^ M)) 23) :=
        PMF.pure ⟨t.latent, yOf t.data, H.eval t.latent u⟩
      let μ_abs (t_abs : P.SeqState U (2 ^ M)) : PMF (P.StepResult U (2 ^ M)) :=
        let x : Data 23 := ⟨P.seqReg t_abs, P.seqMem t_abs⟩
        PMF.pure (P.mkStepResult (yOf x).regs (yOf x).mem (P.labelEval u (H.eval (θOf x) u)))
      let ν₁ := ν.bind fun t => (μ_lib t).map (t.appendStep (.eval u))
      have hsupp₁ : ∀ q_seq ∈ ν₁.support,
          q_seq.data.Bounded w ∧
          q_seq.data.regs (coreReg H.baseReg) = base ∧
          H.tableRep q_seq.data.mem ∧
          H.seedRep q_seq.latent q_seq.data.mem := by
        intro q_seq hq_seq
        rw [PMF.mem_support_bind_iff] at hq_seq
        obtain ⟨t, ht, hq_map⟩ := hq_seq
        rw [PMF.mem_support_map_iff] at hq_map
        obtain ⟨q, hq, rfl⟩ := hq_map
        dsimp only [μ_lib] at hq
        rw [PMF.support_pure, Set.mem_singleton_iff] at hq
        subst hq
        have ht_inv : hasEvalInv t.data :=
          ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1, t.latent, (hsupp t ht).2.2.2⟩
        have hy_eq : yOf t.data = Classical.choose
            (provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
              (Classical.choose ht_inv.2.2.2) u t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2.1
              (Classical.choose_spec ht_inv.2.2.2)) := by
          simp [yOf, ht_inv]
        have hspec := Classical.choose_spec
          (provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
            (Classical.choose ht_inv.2.2.2) u t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2.1
            (Classical.choose_spec ht_inv.2.2.2))
        dsimp only [SeqOutcome.appendStep]
        rw [hy_eq, hspec.2.2.2.1]
        exact ⟨hspec.2.1, hspec.2.2.2.2, (hsupp t ht).2.2.1, (hsupp t ht).2.2.2⟩
      obtain ⟨ν_final, hruns_rest, htr_rest⟩ := ih ν₁ hsupp₁
      have heval_θOf : ∀ t ∈ ν.support, H.eval (θOf t.data) u = H.eval t.latent u := by
        intro t ht
        have ht_inv : hasEvalInv t.data :=
          ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1, t.latent, (hsupp t ht).2.2.2⟩
        have hθ_eq : θOf t.data = Classical.choose ht_inv.2.2.2 := by
          simp [θOf, ht_inv]
        have hspec₁ := Classical.choose_spec
          (provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
            (Classical.choose ht_inv.2.2.2) u t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2.1
            (Classical.choose_spec ht_inv.2.2.2))
        obtain ⟨y₂, he₂, _, hdec₂, _, _⟩ :=
          provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
            t.latent u t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2.1 (hsupp t ht).2.2.2
        have hy_uniq := execWithin_unique hspec₁.1 he₂
        rw [hy_uniq] at hspec₁
        have hdec₁ := hspec₁.2.2.1
        rw [hdec₂] at hdec₁
        rw [hθ_eq]
        exact Option.some.inj hdec₁.symm
      have hν₁_map :
          ((ν.map P.seqStateOf).bind fun t_abs => (μ_abs t_abs).map (P.appendStep t_abs)) =
            ν₁.map P.seqStateOf := by
        dsimp only [ν₁]
        rw [PMF.bind_map, PMF.map_bind]
        refine PMF.bind_congr_on_support _ _ _ fun t ht => ?_
        dsimp only [Function.comp_apply, HFPresentation.seqStateOf, μ_abs, μ_lib]
        rw [hP.seqReg_mk, hP.seqMem_mk, PMF.pure_map, PMF.pure_map, PMF.pure_map]
        dsimp only [HFPresentation.appendStep, SeqOutcome.appendStep, HFPresentation.seqStateOf]
        rw [hP.stepReg_mk, hP.stepMem_mk, hP.stepLabel_mk, hP.seqTranscript_mk,
          List.map_append, heval_θOf t ht]
        rfl
      rw [← hν₁_map] at hruns_rest
      have hruns_cons :
          P.RunsOps w p_op base (provableSpace c_exp k n_max)
            (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
            (P.eval u :: os.map P.opOf) (ν.map P.seqStateOf) (ν_final.map P.seqStateOf) := by
        refine hP.runsOps_cons μ_abs (fun t_abs ht_abs => ?_) hruns_rest
        rw [PMF.mem_support_map_iff] at ht_abs
        obtain ⟨t, ht, rfl⟩ := ht_abs
        have hreg_t : P.seqReg (P.seqStateOf t) = t.data.regs :=
          hP.seqReg_mk t.data.regs t.data.mem (t.transcript.map P.labelOf)
        have hmem_t : P.seqMem (P.seqStateOf t) = t.data.mem :=
          hP.seqMem_mk t.data.regs t.data.mem (t.transcript.map P.labelOf)
        dsimp only
        rw [hreg_t, hmem_t]
        have ht_inv : hasEvalInv t.data :=
          ⟨(hsupp t ht).1, (hsupp t ht).2.1, (hsupp t ht).2.2.1, t.latent, (hsupp t ht).2.2.2⟩
        have hy_eq : yOf t.data = Classical.choose
            (provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
              (Classical.choose ht_inv.2.2.2) u t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2.1
              (Classical.choose_spec ht_inv.2.2.2)) := by
          simp [yOf, ht_inv]
        have hspec := Classical.choose_spec
          (provableImpl_step_eval_execWithin c_exp k n_max U M hw hfit_space hfit_n hfit_U
            (Classical.choose ht_inv.2.2.2) u t.data ht_inv.1 ht_inv.2.1 ht_inv.2.2.1
            (Classical.choose_spec ht_inv.2.2.2))
        have hμ_eq : μ_abs (P.seqStateOf t) =
            PMF.pure (P.mkStepResult (yOf t.data).regs (yOf t.data).mem
              (P.labelEval u (H.eval t.latent u))) := by
          dsimp only [μ_abs, HFPresentation.seqStateOf]
          rw [hP.seqReg_mk, hP.seqMem_mk, heval_θOf t ht]
        have hprep_regs :
            P.prepareRegs (P.eval u) t.data.regs =
              ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare
                (.eval u) t.data).regs :=
          (prepare_eq_prepareRegs hP c_exp k n_max U M hw hfit_space hfit_n hfit_U
            (.eval u) t.data).symm
        have hbud : P.opBudget (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
            (P.eval u) = provableEvalBound c_exp k + 4 :=
          hP.opBudget_eval _ _ u
        have he_y : ExecWithin w H.subroutineCode.code
            ((H.subroutineCode.toDynamicProgram H.encode H.decode).prepare (.eval u) t.data)
            (yOf t.data) (H.evalSteps + 3) := by
          rw [hy_eq]
          exact hspec.1
        have hcomp := compile_execWithin hS he_y heval_le
        refine ⟨ht_inv.1, ?_, ?_, ?_, ?_⟩
        · rw [hprep_regs, hbud]
          exact hcomp.1
        · rw [hprep_regs, hbud, hμ_eq, PMF.pure_map, hP.stepReg_mk, hP.stepMem_mk]
          exact hcomp.2.2
        · intro u' _
          refine ⟨P.mkStepResult (yOf t.data).regs (yOf t.data).mem
              (P.labelEval u (H.eval t.latent u)), hμ_eq, ?_⟩
          rw [hP.stepMem_mk, hy_eq]
          exact hspec.2.2.2.1
        · intro q_abs hq_abs
          rw [hμ_eq, PMF.support_pure, Set.mem_singleton_iff] at hq_abs
          subst hq_abs
          rw [hP.stepReg_mk, hP.stepMem_mk, hP.stepLabel_mk]
          have hdec_y : H.decode (.eval u) (yOf t.data).regs = some (H.eval t.latent u) := by
            have hθ_eq : θOf t.data = Classical.choose ht_inv.2.2.2 := by simp [θOf, ht_inv]
            rw [← heval_θOf t ht, hθ_eq, hy_eq]
            exact hspec.2.2.1
          refine ⟨by rw [hy_eq]; exact hspec.2.1,
            decode_eq_decodeLabel hP c_exp k n_max U M hw hfit_space hfit_n hfit_U
              (.eval u) (yOf t.data).regs (H.eval t.latent u) hdec_y, ?_⟩
          intro a _
          rw [hy_eq, hspec.2.2.2.1]
      refine ⟨ν_final, hruns_cons, ?_⟩
      rw [htr_rest]
      dsimp only [ν₁, μ_lib]
      rw [PMF.bind_bind]
      refine PMF.bind_congr_on_support _ _ _ fun t _ => ?_
      rw [PMF.pure_map, PMF.pure_bind, HashFamily.evalOpsFromSeed, PMF.map_comp]
      refine congrArg (PMF.map · _) (funext fun suf => ?_)
      simp [SeqOutcome.appendStep]

private theorem provableImpl_whpKWiseSpec_contract
    (c_exp k n_max U M : ℕ) {w base : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (ops : List (HashFamily.Op U))
    (hbk : HashFamily.BoundedEpochKeys k ops) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max)).Contract ops
      (HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval ops) := by
  intro H
  have hH_def : H = provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U := rfl
  clear_value H
  by_cases hreg : n_max < doubleTabThreshold c_exp
  · have hH := hH_def.trans (provableImpl_eq_of_lt hw hfit_space hfit_n hfit_U hreg)
    subst hH
    have hfp : provableFailureProb c_exp k n_max =
        (((Finset.univ \ ({()} : Finset Unit)).card : ℝ≥0∞) /
          (Fintype.card Unit : ℝ≥0∞)) := by
      unfold provableFailureProb
      simp only [hreg, ↓reduceIte]
    rw [hfp]
    exact HashFamily.whpKWiseSpec_contract_evalOps_equiv
      (trinomialPolyHash (Cslib.Probability.trinomialStep U M) k U M)
      (Equiv.punitProd (Fin k → Fin (2 ^ Cslib.Probability.trinomialDeg U M))).symm
      ({()} : Finset Unit)
      (fun _ _ =>
        isKWiseIndependentHash_trinomialPolyHash
          (le_two_pow_trinomialDeg U M) (le_trinomialDeg U M))
      hbk
  · have hsp : Fits w (base + DoubleTabulation.space (provableC c_exp) (provableD c_exp)
        (provableB n_max)) := by
      simpa only [provableSpace, hreg, ↓reduceIte] using hfit_space
    have hpow_b : Fits w (2 ^ provableB n_max) :=
      hsp.of_le (by
        have hc : 1 ≤ provableC c_exp := one_le_provableC c_exp
        have hd : 1 ≤ provableD c_exp := by dsimp only [provableD]; omega
        have hle : 1 * 2 ^ provableB n_max ≤
            ((provableC c_exp + 1) * provableD c_exp) * 2 ^ provableB n_max :=
          Nat.mul_le_mul_right _ (by nlinarith)
        dsimp only [DoubleTabulation.space]
        omega)
    have hpow_M : Fits w (2 ^ M) := by
      have hM_le : M ≤ Cslib.Probability.trinomialDeg U M := le_trinomialDeg U M
      have hdeg_pos : 0 < Cslib.Probability.trinomialDeg U M := by
        dsimp only [Cslib.Probability.trinomialDeg]
        positivity
      exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
    have hkeys : ∀ u : Fin U, Fits w u.val :=
      fun u => hfit_U.of_le (by have := u.isLt; omega)
    have hH := hH_def.trans
      (provableImpl_eq_of_not_lt hw hfit_space hfit_n hfit_U hreg hsp hpow_b hpow_M hkeys)
    subst hH
    rw [provableFailureProb_eq_of_ge (not_lt.mp hreg)]
    exact HashFamily.whpKWiseSpec_contract_evalOps_equiv
      (fun θ : DoubleTabTopSeed (provableC c_exp) (provableD c_exp) (provableB n_max) ×
          DoubleTabBotSeed (provableD c_exp) (provableB n_max) M =>
        doubleTabHash (provableC c_exp) (provableD c_exp) (provableB n_max) U M θ.1 θ.2)
      (Equiv.refl _)
      (doubleTabGoodTop (provableC c_exp) (provableD c_exp) (provableB n_max) k)
      (fun _ hT₁ =>
        isKWiseIndependentHash_doubleTabHash_of_isKUnique
          (le_two_pow_provableC_mul_provableB hU)
          (Finset.mem_filter.mp hT₁).2)
      hbk

/-- From any initial coupled distribution `ν₀` satisfying `H.initInv ν₀`, every operation sequence
`ops_abs : List (P.Op U)` executes via `P.RunsOps` to a final state distribution `ν_final` whose
transcript marginal satisfies `P.WhpKWiseContract δ ops_abs` whenever
`provableFailureProb c_exp k n_max ≤ δ` and `P.BoundedEpochKeys k ops_abs` holds. -/
private theorem provableImpl_runsOps_from_initInv {S : Presentation} {P : HFPresentation S}
    (hS : Laws S) (hP : HFLaws S P)
    (c_exp k n_max U M : ℕ) {w base : ℕ} {δ : ℝ≥0∞}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5)
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (hδ : provableFailureProb c_exp k n_max ≤ δ) :
    let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
    let p_op := S.programOf (H.subroutineCode.code.program (coreReg 2))
    ∀ (ν₀ : PMF (LatentState H.Seed 23)),
      H.initInv ν₀ →
      ∀ (ops_abs : List (P.Op U)),
        ∃ ν_final : PMF (P.SeqState U (2 ^ M)),
          P.RunsOps w p_op base (provableSpace c_exp k n_max)
            (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
            ops_abs (ν₀.map P.initSeqStateOf) ν_final ∧
          (P.BoundedEpochKeys k ops_abs →
            P.WhpKWiseContract δ ops_abs
              (ν_final.map P.seqTranscript)) := by
  intro H p_op ν₀ hinv ops_abs
  obtain ⟨ops, rfl⟩ := P.list_opOf_surjective ops_abs
  have hsupp_seq : ∀ t ∈ (ν₀.map (SeqOutcome.ofLatentState
      (Result := @HashFamily.Result U (2 ^ M)))).support,
      t.data.Bounded w ∧
      t.data.regs (coreReg H.baseReg) = base ∧
      H.tableRep t.data.mem ∧
      H.seedRep t.latent t.data.mem := by
    intro t ht
    rw [PMF.mem_support_map_iff] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact hinv.2 u hu
  obtain ⟨ν_lib_final, hruns, htr⟩ :=
    provableImpl_runsOps_aux hS hP c_exp k n_max U M hU hM hw hfit_space hfit_n hfit_U
      ops (ν₀.map SeqOutcome.ofLatentState) hsupp_seq
  have hinit_map :
      (ν₀.map (SeqOutcome.ofLatentState (Result := @HashFamily.Result U (2 ^ M)))).map
        P.seqStateOf = ν₀.map P.initSeqStateOf := by
    rw [PMF.map_comp]
    rfl
  rw [hinit_map] at hruns
  have htr_evalOps :
      ν_lib_final.map SeqOutcome.transcript =
        HashFamily.evalOps (PMF.uniformOfFintype H.Seed) H.eval ops := by
    rw [htr, PMF.bind_map]
    have hbind_eq :
        (ν₀.bind
          ((fun t : SeqOutcome H.Seed (@HashFamily.Result U (2 ^ M)) 23 =>
              (HashFamily.evalOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval t.latent
                ops).map fun suf => t.transcript ++ suf) ∘
            SeqOutcome.ofLatentState)) =
          (ν₀.map LatentState.latent).bind
            (fun θ₀ =>
              HashFamily.evalOpsFromSeed (PMF.uniformOfFintype H.Seed) H.eval θ₀ ops) := by
      rw [PMF.bind_map]
      refine congrArg (ν₀.bind ·) (funext fun u => ?_)
      dsimp only [Function.comp_apply, SeqOutcome.ofLatentState, List.nil_append]
      exact PMF.map_id _
    rw [hbind_eq, hinv.1]
    rfl
  refine ⟨ν_lib_final.map P.seqStateOf, hruns, fun hbk_abs => ?_⟩
  have hbk_lib : HashFamily.BoundedEpochKeys k ops := by
    refine boundedEpochKeys_of_libEpochKeys ops fun E hE => ?_
    rw [← P.epochKeys_map_opOf hP] at hE
    exact hbk_abs E hE
  have htr_abs :
      (ν_lib_final.map P.seqStateOf).map P.seqTranscript =
        (ν_lib_final.map SeqOutcome.transcript).map (List.map P.labelOf) := by
    rw [PMF.map_comp, PMF.map_comp]
    refine congrArg (ν_lib_final.map ·) (funext fun t => ?_)
    dsimp only [Function.comp_apply, HFPresentation.seqStateOf]
    rw [hP.seqTranscript_mk]
  have hcontract_evalOps :=
    provableImpl_whpKWiseSpec_contract c_exp k n_max U M hU hw hfit_space hfit_n hfit_U
      ops hbk_lib
  rw [htr_abs, htr_evalOps]
  exact P.whpKWiseContract_map hP hcontract_evalOps hδ

/-! ## Part 5: Exported headline bridge theorems (`highIndependenceHashFamily_fresh` and
`highIndependenceHashFamily_clear`) -/

/-- General `c_exp`-parameterized fresh-memory bridge theorem. -/
private theorem provableImpl_fresh_general (S : Presentation) (hS : Laws S)
    (P : HFPresentation S) (hP : HFLaws S P)
    (c_exp k n_max U M w base : ℕ) {δ : ℝ≥0∞}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5)
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (hδ : provableFailureProb c_exp k n_max ≤ δ) :
    ∃ (p_init p_op : List (S.Instr 23)),
      ∀ (reg₀ : Fin 23 → ℕ) (mem₀ : ℕ → ℕ),
        HFPresentation.WordBounded w reg₀ mem₀ →
        reg₀ ⟨22, by decide⟩ = base →
        reg₀ ⟨1, by decide⟩ = n_max →
        reg₀ ⟨2, by decide⟩ = U →
        reg₀ ⟨3, by decide⟩ = M →
        (∀ a, base ≤ a → a < base + provableSpace c_exp k n_max → mem₀ a = 0) →
        ∃ ν₀ : PMF (P.SeqState U (2 ^ M)),
          let s₀ := S.state 0 reg₀ mem₀
          let T_init := initFreshTimeOf c_exp k n_max U M
          S.HaltsWithin w p_init s₀ T_init ∧
          S.expectedTime w p_init s₀ ≤ (T_init : ℝ≥0∞) ∧
          S.evalRand w p_init T_init s₀ =
            ν₀.map (fun t =>
              S.halted (P.seqReg t ⟨2, by decide⟩) (P.seqReg t) (P.seqMem t)) ∧
          (∀ t ∈ ν₀.support,
            P.seqTranscript t = [] ∧
            HFPresentation.WordBounded w (P.seqReg t) (P.seqMem t) ∧
            P.seqReg t ⟨0, by decide⟩ = base ∧
            P.seqReg t ⟨22, by decide⟩ = base + provableSpace c_exp k n_max ∧
            HFPresentation.UnchangedOutside base (provableSpace c_exp k n_max) mem₀ (P.seqMem t)) ∧
          ∀ ops : List (P.Op U),
            ∃ ν_final : PMF (P.SeqState U (2 ^ M)),
              P.RunsOps w p_op base (provableSpace c_exp k n_max)
                (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
                ops ν₀ ν_final ∧
              (P.BoundedEpochKeys k ops →
                P.WhpKWiseContract δ ops
                  (ν_final.map P.seqTranscript)) := by
  let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
  let Sub := H.subroutineCode
  refine ⟨S.programOf (Sub.initFresh.program (coreReg 2)),
    S.programOf (Sub.code.program (coreReg 2)), ?_⟩
  intro reg₀ mem₀ hbdd₀ hfr₀ hpar1 hpar2 hpar3 hzero₀
  let x₀ : Data 23 := ⟨reg₀, mem₀⟩
  have hx₀_bdd : x₀.Bounded w := hbdd₀
  have hfr_sub : x₀.regs Sub.frontierReg = base := hfr₀
  have hpar_sub : ∀ j : Fin 3, x₀.regs (Sub.initParams j) = ![n_max, U, M] j := by
    have hp : Sub.initParams = fun j => coreReg (![1, 2, 3] j) :=
      provableImpl_subroutineCode_initParams c_exp k n_max U M hw hfit_space hfit_n hfit_U
    rw [hp]
    intro j
    fin_cases j
    · exact hpar1
    · exact hpar2
    · exact hpar3
  let hC := H.toObliviousSequenceImpl
    (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max)).ValidOpSeq
    (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max)).Contract
    (provableImpl_whpKWiseSpec_contract c_exp k n_max U M hU hw hfit_space hfit_n hfit_U)
  obtain ⟨x₁, he_span, hmem₁, hb₁, hfr₁, hpar₁⟩ :=
    hC.span_exec hx₀_bdd hfr_sub hpar_sub
  have hx₁_bdd : x₁.Bounded w := he_span.bounded hx₀_bdd
  have hsp_eq : H.space = provableSpace c_exp k n_max :=
    provableImpl_space c_exp k n_max U M hw hfit_space hfit_n hfit_U
  have hC_sp : hC.space = H.space := rfl
  rw [hC_sp] at hfr₁
  have hz₁ : ∀ a ∈ (Block.mk base H.space).footprint, x₁.mem a = 0 := by
    intro a ha
    rw [hmem₁]
    rw [Block.mem_footprint, Block.Owns, hsp_eq] at ha
    exact hzero₀ a ha.1 ha.2
  obtain ⟨n_span, hn_span, hex_span⟩ := he_span
  obtain ⟨m_setup, ν₀_lib, hex_setup, hfst_setup, hsteps_setup, hinv₀, hsupp₀⟩ :=
    provableImpl_initSetup_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
      hx₁_bdd hb₁ hfr₁ hpar₁ hz₁
  have hex_fresh : ExecRand w Sub.initFresh x₀
      ((fun z => (z.1, n_span + z.2)) <$> m_setup) :=
    hex_span.seqRand hex_setup
  have hspan_le : hC.spanTime = 3 := rfl
  have hT_fresh : ∀ z ∈ (((fun z => (z.1, n_span + z.2)) <$> m_setup)).support,
      z.2 + 1 ≤ initFreshTimeOf c_exp k n_max U M := by
    intro z hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    have hs₀ := hsteps_setup z₀ hz₀
    have htab_eq :=
      provableImpl_initTableSteps_eq c_exp k n_max U M hw hfit_space hfit_n hfit_U
    have hres_eq :=
      provableImpl_resampleSteps_eq c_exp k n_max U M hw hfit_space hfit_n hfit_U
    dsimp only [initFreshTimeOf]
    omega
  have hcomp := compile_execRand hS hex_fresh hT_fresh
  refine ⟨ν₀_lib.map P.initSeqStateOf, hcomp.1, hcomp.2.1, ?_, ?_, ?_⟩
  · rw [hcomp.2.2]
    have hmap :
        (((fun z => (z.1, n_span + z.2)) <$> m_setup).eval).map (fun z =>
          S.halted (z.1.regs (coreReg 2)) z.1.regs z.1.mem) =
        (m_setup.eval.map Prod.fst).map (fun d : Data 23 =>
          S.halted (d.regs (coreReg 2)) d.regs d.mem) := by
      rw [ProbComp.eval_map, PMF.map_comp, PMF.map_comp]
      rfl
    rw [hmap, hfst_setup, PMF.map_comp, PMF.map_comp]
    refine congrArg (ν₀_lib.map ·) (funext fun t => ?_)
    dsimp only [Function.comp_apply, HFPresentation.initSeqStateOf]
    rw [hP.seqReg_mk, hP.seqMem_mk]
    rfl
  · intro t_abs ht_abs
    rw [PMF.mem_support_map_iff] at ht_abs
    obtain ⟨t, ht, rfl⟩ := ht_abs
    obtain ⟨ht_bdd, ht_base, ht_fr, ht_mod⟩ := hsupp₀ t ht
    dsimp only [HFPresentation.initSeqStateOf]
    rw [hP.seqReg_mk, hP.seqMem_mk, hP.seqTranscript_mk]
    have hbase_reg : Sub.baseReg = (⟨0, by decide⟩ : Fin 23) := by
      dsimp only [Sub, Impl.subroutineCode]
      rw [provableImpl_baseReg c_exp k n_max U M hw hfit_space hfit_n hfit_U]
      rfl
    have hfr_reg : Sub.frontierReg = (⟨22, by decide⟩ : Fin 23) := rfl
    refine ⟨rfl, ht_bdd, by rw [← hbase_reg]; exact ht_base,
      by rw [← hfr_reg, ← hsp_eq]; exact ht_fr, ?_⟩
    intro a ha
    have hmem₁' : x₁.mem = mem₀ := hmem₁
    rw [← hmem₁']
    rw [← hsp_eq] at ha
    have ha' : a ∉ (Block.mk base H.space).footprint := by
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
      exact ha
    exact ht_mod a ha'
  · exact provableImpl_runsOps_from_initInv hS hP c_exp k n_max U M hU hM hw hfit_space
      hfit_n hfit_U hδ ν₀_lib hinv₀

/-- Headline bridge theorem for fresh zeroed memory `[base, base + space k n_max)`. -/
theorem highIndependenceHashFamily_fresh (S : Presentation) (hS : Laws S)
    (P : HFPresentation S) (hP : HFLaws S P) :
    ∀ (k n_max U M w base : ℕ),
      U ≤ max n_max 4 ^ 4 →
      M ≤ 4 * Nat.clog 2 (max n_max 4) + 5 →
      2 * trinomialDeg U M ≤ w →
      base + space k n_max < 2 ^ w →
      max n_max 2 < 2 ^ w →
      max U 2 + 1 < 2 ^ w →
      ∃ (p_init p_op : List (S.Instr 23)),
        ∀ (reg₀ : Fin 23 → ℕ) (mem₀ : ℕ → ℕ),
          HFPresentation.WordBounded w reg₀ mem₀ →
          reg₀ ⟨22, by decide⟩ = base →
          reg₀ ⟨1, by decide⟩ = n_max →
          reg₀ ⟨2, by decide⟩ = U →
          reg₀ ⟨3, by decide⟩ = M →
          (∀ a, base ≤ a → a < base + space k n_max → mem₀ a = 0) →
          ∃ ν₀ : PMF (P.SeqState U (2 ^ M)),
            let s₀ := S.state 0 reg₀ mem₀
            let T_init := initFreshTime k n_max U M
            S.HaltsWithin w p_init s₀ T_init ∧
            S.expectedTime w p_init s₀ ≤ (T_init : ℝ≥0∞) ∧
            S.evalRand w p_init T_init s₀ =
              ν₀.map (fun t =>
                S.halted (P.seqReg t ⟨2, by decide⟩) (P.seqReg t) (P.seqMem t)) ∧
            (∀ t ∈ ν₀.support,
              P.seqTranscript t = [] ∧
              HFPresentation.WordBounded w (P.seqReg t) (P.seqMem t) ∧
              P.seqReg t ⟨0, by decide⟩ = base ∧
              P.seqReg t ⟨22, by decide⟩ = base + space k n_max ∧
              HFPresentation.UnchangedOutside base (space k n_max) mem₀ (P.seqMem t)) ∧
            ∀ ops : List (P.Op U),
              ∃ ν_final : PMF (P.SeqState U (2 ^ M)),
                P.RunsOps w p_op base (space k n_max) (evalTimeBound k) (resampleTime k n_max)
                  ops ν₀ ν_final ∧
                (P.BoundedEpochKeys k ops →
                  P.WhpKWiseContract (failureProbBound k n_max) ops
                    (ν_final.map P.seqTranscript)) := by
  intro k n_max U M w base hU hM hw hfit_space hfit_n hfit_U
  rw [trinomialDeg_eq] at hw
  rw [space_eq] at hfit_space ⊢
  rw [initFreshTime_eq, evalTimeBound_eq, resampleTime_eq]
  exact provableImpl_fresh_general S hS P hP 4 k n_max U M w base hU hM hw hfit_space
    hfit_n hfit_U (provableFailureProb_le_failureProbBound k n_max)

/-- General `c_exp`-parameterized dirty-memory bridge theorem. -/
private theorem provableImpl_clear_general (S : Presentation) (hS : Laws S)
    (P : HFPresentation S) (hP : HFLaws S P)
    (c_exp k n_max U M w base : ℕ) {δ : ℝ≥0∞}
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hM : M ≤ max c_exp 1 * Nat.clog 2 (max n_max 4) + 5)
    (hw : 2 * Cslib.Probability.trinomialDeg U M ≤ w)
    (hfit_space : Fits w (base + provableSpace c_exp k n_max))
    (hfit_n : Fits w (max n_max 2))
    (hfit_U : Fits w (max U 2 + 1))
    (hδ : provableFailureProb c_exp k n_max ≤ δ) :
    ∃ (p_initClear p_op : List (S.Instr 23)),
      ∀ (reg₀ : Fin 23 → ℕ) (mem₀ : ℕ → ℕ),
        HFPresentation.WordBounded w reg₀ mem₀ →
        reg₀ ⟨22, by decide⟩ = base →
        reg₀ ⟨1, by decide⟩ = n_max →
        reg₀ ⟨2, by decide⟩ = U →
        reg₀ ⟨3, by decide⟩ = M →
        ∃ ν₀ : PMF (P.SeqState U (2 ^ M)),
          let s₀ := S.state 0 reg₀ mem₀
          let T_init := initClearTimeOf c_exp k n_max U M
          S.HaltsWithin w p_initClear s₀ T_init ∧
          S.expectedTime w p_initClear s₀ ≤ (T_init : ℝ≥0∞) ∧
          S.evalRand w p_initClear T_init s₀ =
            ν₀.map (fun t =>
              S.halted (P.seqReg t ⟨2, by decide⟩) (P.seqReg t) (P.seqMem t)) ∧
          (∀ t ∈ ν₀.support,
            P.seqTranscript t = [] ∧
            HFPresentation.WordBounded w (P.seqReg t) (P.seqMem t) ∧
            P.seqReg t ⟨0, by decide⟩ = base ∧
            P.seqReg t ⟨22, by decide⟩ = base + provableSpace c_exp k n_max ∧
            HFPresentation.UnchangedOutside base (provableSpace c_exp k n_max) mem₀ (P.seqMem t)) ∧
          ∀ ops : List (P.Op U),
            ∃ ν_final : PMF (P.SeqState U (2 ^ M)),
              P.RunsOps w p_op base (provableSpace c_exp k n_max)
                (provableEvalBound c_exp k + 4) (resampleTimeOf c_exp k n_max)
                ops ν₀ ν_final ∧
              (P.BoundedEpochKeys k ops →
                P.WhpKWiseContract δ ops
                  (ν_final.map P.seqTranscript)) := by
  let H := provableImpl c_exp k n_max U M hw hfit_space hfit_n hfit_U
  let Sub := H.subroutineCode
  refine ⟨S.programOf (Sub.initClear.program (coreReg 2)),
    S.programOf (Sub.code.program (coreReg 2)), ?_⟩
  intro reg₀ mem₀ hbdd₀ hfr₀ hpar1 hpar2 hpar3
  let x₀ : Data 23 := ⟨reg₀, mem₀⟩
  have hx₀_bdd : x₀.Bounded w := hbdd₀
  have hfr_sub : x₀.regs Sub.frontierReg = base := hfr₀
  have hpar_sub : ∀ j : Fin 3, x₀.regs (Sub.initParams j) = ![n_max, U, M] j := by
    have hp : Sub.initParams = fun j => coreReg (![1, 2, 3] j) :=
      provableImpl_subroutineCode_initParams c_exp k n_max U M hw hfit_space hfit_n hfit_U
    rw [hp]
    intro j
    fin_cases j
    · exact hpar1
    · exact hpar2
    · exact hpar3
  let hC := H.toObliviousSequenceImpl
    (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max)).ValidOpSeq
    (HashFamily.whpKWiseSpec k U (2 ^ M) (provableFailureProb c_exp k n_max)).Contract
    (provableImpl_whpKWiseSpec_contract c_exp k n_max U M hU hw hfit_space hfit_n hfit_U)
  obtain ⟨x₁, he_span, hmem₁, hb₁, hfr₁, hpar₁⟩ :=
    hC.span_exec hx₀_bdd hfr_sub hpar_sub
  have hx₁_bdd : x₁.Bounded w := he_span.bounded hx₀_bdd
  have hsp_eq : H.space = provableSpace c_exp k n_max :=
    provableImpl_space c_exp k n_max U M hw hfit_space hfit_n hfit_U
  have hC_sp : hC.space = H.space := rfl
  rw [hC_sp] at hfr₁
  obtain ⟨x_zero, he_zero, hx_zero_bdd, hb_zero, hfr_zero, hpar_zero, hzero_mem, hmod_zero⟩ :=
    Sub.zeroFillCode_exec hC.clear_nodup hC.params_not_clear hC.incCur_eval
      hx₁_bdd hb₁ hfr₁ hpar₁
  obtain ⟨n_span, hn_span, hex_span⟩ := he_span
  obtain ⟨n_zero, hn_zero, hex_zero⟩ := he_zero
  obtain ⟨m_setup, ν₀_lib, hex_setup, hfst_setup, hsteps_setup, hinv₀, hsupp₀⟩ :=
    provableImpl_initSetup_execRand c_exp k n_max U M hw hfit_space hfit_n hfit_U
      hx_zero_bdd hb_zero hfr_zero hpar_zero hzero_mem
  have hex_clear : ExecRand w Sub.initClear x₀
      ((fun z => (z.1, n_span + z.2)) <$>
        ((fun z => (z.1, n_zero + z.2)) <$> m_setup)) :=
    hex_span.seqRand (hex_zero.seqRand hex_setup)
  have hspan_le : hC.spanTime = 3 := rfl
  have hT_clear : ∀ z ∈ (((fun z => (z.1, n_span + z.2)) <$>
      ((fun z => (z.1, n_zero + z.2)) <$> m_setup))).support,
      z.2 + 1 ≤ initClearTimeOf c_exp k n_max U M := by
    intro z hz
    obtain ⟨z₁, hz₁, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz₁
    have hs₀ := hsteps_setup z₀ hz₀
    have htab_eq :=
      provableImpl_initTableSteps_eq c_exp k n_max U M hw hfit_space hfit_n hfit_U
    have hres_eq :=
      provableImpl_resampleSteps_eq c_exp k n_max U M hw hfit_space hfit_n hfit_U
    dsimp only [initClearTimeOf, initFreshTimeOf]
    omega
  have hcomp := compile_execRand hS hex_clear hT_clear
  refine ⟨ν₀_lib.map P.initSeqStateOf, hcomp.1, hcomp.2.1, ?_, ?_, ?_⟩
  · rw [hcomp.2.2]
    have hmap :
        (((fun z => (z.1, n_span + z.2)) <$>
            ((fun z => (z.1, n_zero + z.2)) <$> m_setup)).eval).map (fun z =>
          S.halted (z.1.regs (coreReg 2)) z.1.regs z.1.mem) =
        (m_setup.eval.map Prod.fst).map (fun d : Data 23 =>
          S.halted (d.regs (coreReg 2)) d.regs d.mem) := by
      rw [ProbComp.eval_map, ProbComp.eval_map, PMF.map_comp, PMF.map_comp, PMF.map_comp]
      rfl
    rw [hmap, hfst_setup, PMF.map_comp, PMF.map_comp]
    refine congrArg (ν₀_lib.map ·) (funext fun t => ?_)
    dsimp only [Function.comp_apply, HFPresentation.initSeqStateOf]
    rw [hP.seqReg_mk, hP.seqMem_mk]
    rfl
  · intro t_abs ht_abs
    rw [PMF.mem_support_map_iff] at ht_abs
    obtain ⟨t, ht, rfl⟩ := ht_abs
    obtain ⟨ht_bdd, ht_base, ht_fr, ht_mod⟩ := hsupp₀ t ht
    dsimp only [HFPresentation.initSeqStateOf]
    rw [hP.seqReg_mk, hP.seqMem_mk, hP.seqTranscript_mk]
    have hbase_reg : Sub.baseReg = (⟨0, by decide⟩ : Fin 23) := by
      dsimp only [Sub, Impl.subroutineCode]
      rw [provableImpl_baseReg c_exp k n_max U M hw hfit_space hfit_n hfit_U]
      rfl
    have hfr_reg : Sub.frontierReg = (⟨22, by decide⟩ : Fin 23) := rfl
    have ht_mod' : Modifies (Block.mk base H.space).footprint x_zero.mem t.data.mem := ht_mod
    have hmod_all : Modifies (Block.mk base H.space).footprint x₁.mem t.data.mem := by
      simpa only [Finset.union_idempotent] using hmod_zero.trans ht_mod'
    refine ⟨rfl, ht_bdd, by rw [← hbase_reg]; exact ht_base,
      by rw [← hfr_reg, ← hsp_eq]; exact ht_fr, ?_⟩
    intro a ha
    have hmem₁' : x₁.mem = mem₀ := hmem₁
    rw [← hmem₁']
    rw [← hsp_eq] at ha
    have ha' : a ∉ (Block.mk base H.space).footprint := by
      rw [Block.mem_footprint, Block.Owns, not_and_or, not_le, not_lt]
      exact ha
    exact hmod_all a ha'
  · exact provableImpl_runsOps_from_initInv hS hP c_exp k n_max U M hU hM hw hfit_space
      hfit_n hfit_U hδ ν₀_lib hinv₀

/-- Headline bridge theorem for arbitrary dirty memory (`p_initClear`). -/
theorem highIndependenceHashFamily_clear (S : Presentation) (hS : Laws S)
    (P : HFPresentation S) (hP : HFLaws S P) :
    ∀ (k n_max U M w base : ℕ),
      U ≤ max n_max 4 ^ 4 →
      M ≤ 4 * Nat.clog 2 (max n_max 4) + 5 →
      2 * trinomialDeg U M ≤ w →
      base + space k n_max < 2 ^ w →
      max n_max 2 < 2 ^ w →
      max U 2 + 1 < 2 ^ w →
      ∃ (p_initClear p_op : List (S.Instr 23)),
        ∀ (reg₀ : Fin 23 → ℕ) (mem₀ : ℕ → ℕ),
          HFPresentation.WordBounded w reg₀ mem₀ →
          reg₀ ⟨22, by decide⟩ = base →
          reg₀ ⟨1, by decide⟩ = n_max →
          reg₀ ⟨2, by decide⟩ = U →
          reg₀ ⟨3, by decide⟩ = M →
          ∃ ν₀ : PMF (P.SeqState U (2 ^ M)),
            let s₀ := S.state 0 reg₀ mem₀
            let T_init := initClearTime k n_max U M
            S.HaltsWithin w p_initClear s₀ T_init ∧
            S.expectedTime w p_initClear s₀ ≤ (T_init : ℝ≥0∞) ∧
            S.evalRand w p_initClear T_init s₀ =
              ν₀.map (fun t =>
                S.halted (P.seqReg t ⟨2, by decide⟩) (P.seqReg t) (P.seqMem t)) ∧
            (∀ t ∈ ν₀.support,
              P.seqTranscript t = [] ∧
              HFPresentation.WordBounded w (P.seqReg t) (P.seqMem t) ∧
              P.seqReg t ⟨0, by decide⟩ = base ∧
              P.seqReg t ⟨22, by decide⟩ = base + space k n_max ∧
              HFPresentation.UnchangedOutside base (space k n_max) mem₀ (P.seqMem t)) ∧
            ∀ ops : List (P.Op U),
              ∃ ν_final : PMF (P.SeqState U (2 ^ M)),
                P.RunsOps w p_op base (space k n_max) (evalTimeBound k) (resampleTime k n_max)
                  ops ν₀ ν_final ∧
                (P.BoundedEpochKeys k ops →
                  P.WhpKWiseContract (failureProbBound k n_max) ops
                    (ν_final.map P.seqTranscript)) := by
  intro k n_max U M w base hU hM hw hfit_space hfit_n hfit_U
  rw [trinomialDeg_eq] at hw
  rw [space_eq] at hfit_space ⊢
  rw [initClearTime_eq, evalTimeBound_eq, resampleTime_eq]
  exact provableImpl_clear_general S hS P hP 4 k n_max U M w base hU hM hw hfit_space
    hfit_n hfit_U (provableFailureProb_le_failureProbBound k n_max)

end ComplexityAbstracts.HashFamiliesBridge
