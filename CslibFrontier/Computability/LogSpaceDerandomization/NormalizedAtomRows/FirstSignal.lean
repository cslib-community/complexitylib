/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.Moment
public import CslibFrontier.Computability.LogSpaceDerandomization.RootMetric.Stationarity
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyRawMoment

/-!
# Telescoping first signals on the full terminal slice

The increments start from zero and retain the same full environment in every prefix.
Stationarity identifies their actual conditional mean, including empty slices.
Structural request size `q` stays fixed as statistical precision and walk length vary.
The second coordinate is arbitrary. This does not supply its separate moment bridge.
The telescoping proof pattern is adapted from Samuel Schlesinger's compression API.

## Main results

* `actualPrefix_firstSignalIncrement`: the genuine prefix telescoping identity.
* `actualNoiseEntry_firstSignalIncrement`: the exact centered first-noise identity.
* `actualFirstSignal_noise_le_lower`: actual endpoint row noise from lower-child moments.
-/

public section

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators

variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- Completed raw child used by the first signal: the actual full-terminal H4 walk
of the signed incoming sample. No preparation cutoff is applied inside this walk. -/
@[expose] noncomputable def completedRawChild {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (l bin ks km k kb : ℕ) (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → ZMod P → ℝ)
    (steps : ℕ) (σ : Environment P J) (x y : ZMod P) : ℝ :=
  conditionalWalk (retainedMask R.source (side P ks) D ss)
    (retainedMask R.terminal (side P k) D st)
    (graph R.source R.terminal R.source_terminal (side P ks) (side P k)
      (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps)
    (rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff raw prep maximum) σ x y

/-- Genuine differences of successive first signals, starting from zero.
The second signal is left unchanged. -/
@[expose] noncomputable def firstSignalIncrement
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (k : ℕ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ) :=
  fun σ x i y (ν : Fin 2) => if ν = 0 then
    (F (i + 1) σ x y - (if i = 0 then 0 else F i σ x y)) / rate k else second σ x i y

omit [Fact P.Prime] in
/-- The actual prefix telescopes, without any relation between successive children. -/
theorem actualPrefix_firstSignalIncrement
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (k : ℕ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, raw σ x y 0 = 0) (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    actualPrefix (firstSignalIncrement F k second) raw i σ x y 0 = F (i + 1) σ x y / rate k := by
  unfold actualPrefix
  induction i with
  | zero => simp [uncompressedRow_succ, firstSignalIncrement, hz]
  | succ i ih =>
    rw [uncompressedRow_succ, ih]
    simp only [firstSignalIncrement, Fin.isValue, ↓reduceIte, Nat.succ_ne_zero]
    ring

omit [Fact P.Prime] in
/-- Recover the matrix-unit child from the normalized first prefix. Preparing the prefix
without this factor would divide by the rate twice. Literal-zero initialization is retained. -/
lemma firstSignal_raw_error
    (F : ℕ → Environment P J → ZMod P → ZMod P → ℝ) (k : ℕ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    |F (i + 1) σ x y - G x y| = rate k *
      |actualPrefix (firstSignalIncrement F k second) (fun _ _ _ _ => 0) i σ x y 0 -
        G x y / rate k| := by
  rw [actualPrefix_firstSignalIncrement _ _ _ _ (by intros; rfl), ← sub_div, abs_div,
    abs_of_pos (rate_pos k), mul_div_cancel₀ _ (rate_pos k).ne']

open Classical in
/-- Exact centered-noise identity for actual full-terminal-rank walk prefixes. -/
theorem actualNoiseEntry_firstSignalIncrement {E : Type*} [Fintype E] [Nonempty E]
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t La D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, raw σ x y 0 = 0) (i : ℕ) (σ : Environment P J) (x y : ZMod P) :
    let F := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t La D st)
      (graphs j) (times j) (input j)
    actualNoiseEntry s t Ls La Lt D ss st k G (firstSignalIncrement F k second) raw 0 i σ x y =
      |F (i + 1) σ x y - rowSliceMean (retainedMask s Ls D ss) (retainedMask t La D st)
        (input (i + 1)) x y| / (rate k * (1 + G x y / rate k)) := by
  dsimp only
  unfold actualNoiseEntry twoMaskMean
  simp only [Fin.isValue, ↓reduceIte, actualPrefix_firstSignalIncrement _ _ _ _ hz]
  unfold rowSliceMean
  rw [← expect_div]
  change |(_ - rowSliceMean (retainedMask s Ls D ss) (retainedMask t La D st)
    (conditionalWalk _ _ (graphs (i + 1)) (times (i + 1)) (input (i + 1))) x y / rate k)| /
    (1 + G x y / rate k) = _
  rw [rowSliceMean_conditionalWalk, ← sub_div, abs_div, abs_of_pos (rate_pos k), div_div]
  rfl

open Classical in
/-- Relative first noise costs exactly the explicit inverse fourth power of the
sampling rate, with no width factor or conversion through a maximum entry. -/
theorem actualNoiseEntry_firstSignal_row_le {E : Type*} [Fintype E] [Nonempty E]
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (ss st : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D ss) (retainedMask t La D st) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (input : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, raw σ x y 0 = 0) (i : ℕ) {N u : ℝ} (hNu : 0 ≤ N * u) :
    let F := fun j => conditionalWalk (retainedMask s Ls D ss) (retainedMask t La D st)
      (graphs j) (times j) (input j)
    rowNormPow 4 N u (retainedMask s Ls D ss) (retainedMask t La D st)
      (actualNoiseEntry s t Ls La Lt D ss st k G (firstSignalIncrement F k second) raw 0 i) ≤
      (rate k)⁻¹ ^ 4 * rowNormPow 4 N u (retainedMask s Ls D ss) (retainedMask t La D st)
        (fun σ x y => F (i + 1) σ x y - rowSliceMean (retainedMask s Ls D ss)
          (retainedMask t La D st) (input (i + 1)) x y) := by
  dsimp only
  apply rowNormPow_le_mul hNu
  intro σ x y _ _
  rw [actualNoiseEntry_firstSignalIncrement s t Ls La Lt D ss st graphs times input k G
    second raw hz]
  have hr := rate_pos k
  have hd : 0 ≤ G x y / rate k := div_nonneg (hG x y) hr.le
  have hden : rate k ≤ rate k * (1 + G x y / rate k) := by nlinarith
  rw [abs_of_nonneg (div_nonneg (abs_nonneg _) (by positivity))]
  calc
    _ ≤ (|_ - _| / rate k) ^ 4 := pow_le_pow_left₀ (by positivity)
      (div_le_div_of_nonneg_left (abs_nonneg _) hr hden) 4
    _ = _ := by rw [div_eq_mul_inv, mul_pow]; ring

open Classical in
/-- Actual first/full-rank endpoint noise, paid by the explicit lower-child incoming
moment budget. The positive structural size is independent of precision.
Children can be arbitrarily correlated on the full environment.
This establishes no preparatory second-signal or recursive budget estimate. -/
theorem actualFirstSignal_noise_le_lower {q : ℕ} (hq : 0 < q)
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (l bin ks km k kb Lt : ℕ)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    (raw prep : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ → ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0)
    {N u : ℝ} (hN : 0 < N) (hu : 0 < u) (i : ℕ) :
    let F := fun j σ x y => completedRawChild HP D R l bin ks km k kb ss sm st Kc
      binCutoff (raw j) (prep j) (maximum j) (steps j) σ x y
    rowNormPow 4 N u (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) Lt D ss st k G
        (firstSignalIncrement F k second) initial 0 i) ≤
      (rate k)⁻¹ ^ 4 * (32 *
        (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        incomingMomentBudget HP D id R l bin ks km k kb ss sm st Kc binCutoff
          (raw (i + 1)) (prep (i + 1)) (maximum (i + 1)) N u) := by
  dsimp only
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have hb := rawIncomingNormalized_noise_le_lower HP hK D (id : ZMod P → ZMod P) R
    l bin ks km k kb ss sm st Kc hKc binCutoff (raw (i + 1)) (prep (i + 1))
    (maximum (i + 1)) hN hu (steps (i + 1))
  exact (actualNoiseEntry_firstSignal_row_le R.source R.terminal (side P ks) (side P k)
    Lt D ss st (fun _ => graph R.source R.terminal R.source_terminal (side P ks) (side P k)
      (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y)) (fun j _ _ => steps j)
    (fun j => rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff (raw j) (prep j) (maximum j))
    k G hG second initial hz i (mul_pos hN hu).le).trans
      (mul_le_mul_of_nonneg_left hb (by positivity))

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
