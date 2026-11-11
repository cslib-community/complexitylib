/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.WeightedAdversary
public import CslibFrontier.Computability.QueryComplexity.Quantum.SpectralAdversary
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.EuclideanOpNorm
public import CslibFrontierTests.QuantumAmbainisAdversary
public import CslibFrontierTests.QuantumAdversary

/-! Kernel-checked clients for `WeightedAdversary` and `SpectralAdversary`:
- recovery of the unweighted adversary bound via `WeightScheme.ofUnweighted`;
- Ambainis's 4-bit base function (`ambainis4`), proving `λ(f) ≤ s(f) ≤ 2 < 5/2 ≤ ADV(f)` via
  `WeightScheme.le_spectralAdversary` and `BitString.spectralSensitivity_le_sensitivity`;
- Høyer–Lee–Špalek's 6-bit Hamming-weight-3 partial function separating nonnegative and
  negative-weight adversaries (`ADV ≤ 3 < 16/5 ≤ ADV±`);
- a non-Boolean `Fin 3` instance of `one_sub_mul_generalAdversary_le` and `generalAdversary`. -/

namespace CslibFrontierTests.QuantumGeneralAdversary

open Cslib Cslib.Quantum Cslib.BitString Finset Function
open CslibFrontierTests.QuantumPolynomial
open scoped Matrix

public section

/-! ### Unweighted adversary recovery on `readBit` -/

private def bitPair1 : Finset (BitString 1 × BitString 1) :=
  {(fun _ => true, fun _ => false)}

example : (1 - 2 * √((0 : ℝ) * (1 - 0))) * √((1 : ℕ) * (1 : ℕ)) ≤ 2 * (1 : ℕ) * √(1 : ℕ) := by
  have hL : ∀ p ∈ bitPair1, ∀ i, p.1 i ≠ p.2 i →
      #{q ∈ bitPair1 | q.1 i ≠ q.2 i ∧ q.1 = p.1} *
        #{q ∈ bitPair1 | q.1 i ≠ q.2 i ∧ q.2 = p.2} ≤ 1 := by
    intro p hp i hne
    rcases mem_singleton.1 hp with rfl
    revert i hne
    decide
  let S := WeightScheme.ofUnweighted bitPair1 1 hL
  have hW : 0 < S.weightSum := by
    simp [S, WeightScheme.weightSum, WeightScheme.ofUnweighted, bitPair1]
  have hbd := S.one_sub_mul_sqrt_le_of_load_le readBit norm_ψ₀ 1 hW
    (δ := 2 * √((0 : ℝ) * (1 - 0))) (mA := 1) (mB := 1)
    (fun p hp => norm_inner_le_two_mul_sqrt_of_measureProb (by rw [norm_run, norm_ψ₀])
      (by rw [norm_run, norm_ψ₀])
      (by rcases mem_singleton.1 hp with rfl; rw [measureProb_readBit]; simp [bitVal])
      (by rcases mem_singleton.1 hp with rfl; rw [measureProb_readBit]; simp [bitVal])
      (by norm_num))
    zero_le_one zero_le_one
    (fun x hx i => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hx
      have hl := WeightScheme.ofUnweighted_loadFst_le hL p.1 i
      have hw : S.wtFst p.1 = 1 := by
        rw [WeightScheme.ofUnweighted_wtFst]
        rcases mem_singleton.1 hp with rfl
        rw [bitPair1, filter_singleton, ite_eq_left rfl, card_singleton, Nat.cast_one]
      simpa [S, hw] using hl)
    (fun y hy i => by
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hy
      have hl := WeightScheme.ofUnweighted_loadSnd_le hL p.2 i
      have hw : S.wtSnd p.2 = 1 := by
        rw [WeightScheme.ofUnweighted_wtSnd]
        rcases mem_singleton.1 hp with rfl
        rw [bitPair1, filter_singleton, ite_eq_left rfl, card_singleton, Nat.cast_one]
      simpa [S, hw] using hl)
  simpa only [Nat.cast_one, Real.sqrt_one, mul_one] using hbd

/-! ### Ambainis's 4-bit function: `λ(f) ≤ s(f) ≤ 2 < 5/2 ≤ ADV(f)` ([Ambainis2006], §4.3) -/

/-- Ambainis's 4-bit base function: queries `x 0` and `x 2`, then outputs `x 0 ⊕ x 1` if `x 0 = x 2`
and `x 0 ⊕ x 3` otherwise ([Ambainis2006], Section 4.3, Figure 1). -/
def ambainis4 (x : BitString 4) : Bool :=
  if x 0 == x 2 then xor (x 0) (x 1) else xor (x 0) (x 3)

/-- Boolean sensitivity indicator at coordinate `i` of `ambainis4`. -/
def sens4 (x : BitString 4) (i : Fin 4) : Bool :=
  ambainis4 (fun k => if k = i then !x k else x k) != ambainis4 x

private theorem isSensitiveCoord_ambainis4_iff (x : BitString 4) (i : Fin 4) :
    IsSensitiveCoord ambainis4 x i ↔ sens4 x i = true := by
  have heq : Function.update x i (!x i) = (fun k => if k = i then !x k else x k) := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp [IsSensitiveCoord, sens4, heq]

theorem sensitivity_ambainis4_le_two : sensitivity ambainis4 ≤ 2 := by
  refine Finset.sup_le fun x _ => ?_
  have hcongr : sensitiveCoords ambainis4 x = univ.filter (fun i => sens4 x i = true) := by
    ext i
    simp only [mem_sensitiveCoords, isSensitiveCoord_ambainis4_iff, mem_filter, mem_univ, true_and]
  simp only [sensitivityAt, hcongr]
  have hdec : ∀ x : BitString 4, #{i : Fin 4 | sens4 x i = true} ≤ 2 := by decide
  exact hdec x

theorem spectralSensitivity_ambainis4_le_two : spectralSensitivity ambainis4 ≤ 2 :=
  (spectralSensitivity_le_sensitivity ambainis4).trans
    (by exact_mod_cast sensitivity_ambainis4_le_two)

/-- Boolean predicate cutting out Ambainis's 32 related `(0, 1)`-pairs for `ambainis4`: differing
in one sensitive coordinate, both sensitive coordinates, or both insensitive coordinates. -/
def amb4PairPred (p : BitString 4 × BitString 4) : Bool :=
  (!ambainis4 p.1) && ambainis4 p.2 &&
    (decide (∀ i : Fin 4, p.1 i ≠ p.2 i → sens4 p.1 i = true) ||
      decide (∀ i : Fin 4, p.1 i ≠ p.2 i → sens4 p.1 i = false))

def amb4R : Finset (BitString 4 × BitString 4) :=
  univ.filter fun p => amb4PairPred p = true

def amb4WInt (p : BitString 4 × BitString 4) : ℤ :=
  if #{i : Fin 4 | p.1 i ≠ p.2 i} = 1 then 3 else 2

def amb4UInt (p : BitString 4 × BitString 4) (i : Fin 4) : ℤ :=
  if #{i : Fin 4 | p.1 i ≠ p.2 i} = 1 then 3
  else if sens4 p.1 i then 1 else 4

def amb4VInt (p : BitString 4 × BitString 4) (i : Fin 4) : ℤ :=
  if #{i : Fin 4 | p.1 i ≠ p.2 i} = 1 then 3
  else if sens4 p.2 i then 1 else 4

private def bits4 (b0 b1 b2 b3 : Bool) : BitString 4 := fun i =>
  match i with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3

private def vec4 (j : Fin 16) : BitString 4 :=
  bits4 (j.val.testBit 0) (j.val.testBit 1) (j.val.testBit 2) (j.val.testBit 3)

private theorem vec4_inj_dec : ∀ j₁ j₂ : Fin 16, vec4 j₁ = vec4 j₂ → j₁ = j₂ := by
  decide

private theorem vec4_surj_dec : ∀ x : BitString 4, ∃ j : Fin 16, vec4 j = x := by
  decide

private theorem vec4_image_univ : image vec4 univ = univ :=
  eq_univ_of_forall fun x =>
    let ⟨j, hj⟩ := vec4_surj_dec x
    mem_image.2 ⟨j, mem_univ _, hj⟩

private theorem amb4_sq_le_dec :
    ∀ j k : Fin 16, amb4PairPred (vec4 j, vec4 k) = true → ∀ i : Fin 4,
      vec4 j i ≠ vec4 k i →
        amb4WInt (vec4 j, vec4 k) ^ 2 ≤
          amb4UInt (vec4 j, vec4 k) i * amb4VInt (vec4 j, vec4 k) i := by
  decide

private theorem amb4_nonempty_dec :
    amb4PairPred (fun _ => false, fun i => decide (i = 0)) = true := by
  decide

private theorem amb4_fst_load_dec :
    ∀ j : Fin 16, ∀ i : Fin 4,
      5 * (∑ k : Fin 16,
        if amb4PairPred (vec4 j, vec4 k) = true ∧ vec4 j i ≠ vec4 k i then
          amb4UInt (vec4 j, vec4 k) i else 0) ≤
        2 * (∑ k : Fin 16,
          if amb4PairPred (vec4 j, vec4 k) = true then amb4WInt (vec4 j, vec4 k) else 0) := by
  decide

private theorem amb4_snd_load_dec :
    ∀ k : Fin 16, ∀ i : Fin 4,
      5 * (∑ j : Fin 16,
        if amb4PairPred (vec4 j, vec4 k) = true ∧ vec4 j i ≠ vec4 k i then
          amb4VInt (vec4 j, vec4 k) i else 0) ≤
        2 * (∑ j : Fin 16,
          if amb4PairPred (vec4 j, vec4 k) = true then amb4WInt (vec4 j, vec4 k) else 0) := by
  decide

private theorem amb4_ne_dec :
    ∀ j k : Fin 16, amb4PairPred (vec4 j, vec4 k) = true →
      ambainis4 (vec4 j) ≠ ambainis4 (vec4 k) := by
  decide

noncomputable def ambainis4WeightScheme : WeightScheme 4 where
  R := amb4R
  w p := (amb4WInt p : ℝ) / 3
  u p i := (amb4UInt p i : ℝ) / 3
  v p i := (amb4VInt p i : ℝ) / 3
  w_nonneg p _ := by
    simp only [amb4WInt]
    split_ifs <;> norm_num
  u_nonneg p _ i _ := by
    simp only [amb4UInt]
    split_ifs <;> norm_num
  v_nonneg p _ i _ := by
    simp only [amb4VInt]
    split_ifs <;> norm_num
  sq_le p hp i hi := by
    have hmem : amb4PairPred p = true := (mem_filter.1 hp).2
    obtain ⟨j, hj⟩ := vec4_surj_dec p.1
    obtain ⟨k, hk⟩ := vec4_surj_dec p.2
    have hjk : p = (vec4 j, vec4 k) := Prod.ext hj.symm hk.symm
    rw [hjk] at hmem hi ⊢
    have hmul : (amb4WInt (vec4 j, vec4 k) : ℝ) ^ 2 ≤
        (amb4UInt (vec4 j, vec4 k) i : ℝ) * (amb4VInt (vec4 j, vec4 k) i : ℝ) := by
      exact_mod_cast amb4_sq_le_dec j k hmem i hi
    calc ((amb4WInt (vec4 j, vec4 k) : ℝ) / 3) ^ 2
        = (amb4WInt (vec4 j, vec4 k) : ℝ) ^ 2 / 9 := by ring
      _ ≤ ((amb4UInt (vec4 j, vec4 k) i : ℝ) * (amb4VInt (vec4 j, vec4 k) i : ℝ)) / 9 :=
          div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((amb4UInt (vec4 j, vec4 k) i : ℝ) / 3) * ((amb4VInt (vec4 j, vec4 k) i : ℝ) / 3) := by
          ring

private theorem ambainis4WeightScheme_weightSum_pos : 0 < ambainis4WeightScheme.weightSum := by
  let p₀ : BitString 4 × BitString 4 := (fun _ => false, fun i => decide (i = 0))
  have hp₀ : p₀ ∈ amb4R := mem_filter.2 ⟨mem_univ _, amb4_nonempty_dec⟩
  have hsingle : ambainis4WeightScheme.w p₀ ≤ ambainis4WeightScheme.weightSum :=
    single_le_sum (fun q hq => ambainis4WeightScheme.w_nonneg q hq) hp₀
  have hw0 : (0 : ℝ) < ambainis4WeightScheme.w p₀ := by
    simp only [ambainis4WeightScheme, amb4WInt]
    split_ifs <;> norm_num
  exact lt_of_lt_of_le hw0 hsingle

private theorem ambainis4WeightScheme_loadFst_le (x : BitString 4) (i : Fin 4) :
    (5 / 2 : ℝ) * ambainis4WeightScheme.loadFst x i ≤ ambainis4WeightScheme.wtFst x := by
  obtain ⟨j, rfl⟩ := vec4_surj_dec x
  have hload_int :
      (∑ p ∈ amb4R with p.1 i ≠ p.2 i ∧ p.1 = vec4 j, amb4UInt p i) =
        ∑ k : Fin 16,
          if amb4PairPred (vec4 j, vec4 k) = true ∧ vec4 j i ≠ vec4 k i then
            amb4UInt (vec4 j, vec4 k) i else 0 := by
    rw [amb4R, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (vec4 j)]
    · rw [← vec4_image_univ, sum_image (fun k₁ _ k₂ _ hk => vec4_inj_dec k₁ k₂ hk)]
      refine sum_congr rfl fun k _ => ?_
      by_cases hp : amb4PairPred (vec4 j, vec4 k) = true <;>
        by_cases hi : vec4 j i ≠ vec4 k i <;> simp [hp, hi]
    · intro a _ hax
      refine sum_eq_zero fun y _ => ?_
      have hne : a ≠ vec4 j := hax
      simp [hne]
    · intro hx; exact absurd (mem_univ (vec4 j)) hx
  have hwt_int :
      (∑ p ∈ amb4R with p.1 = vec4 j, amb4WInt p) =
        ∑ k : Fin 16, if amb4PairPred (vec4 j, vec4 k) = true then
          amb4WInt (vec4 j, vec4 k) else 0 := by
    rw [amb4R, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single (vec4 j)]
    · rw [← vec4_image_univ, sum_image (fun k₁ _ k₂ _ hk => vec4_inj_dec k₁ k₂ hk)]
      refine sum_congr rfl fun k _ => ?_
      by_cases hp : amb4PairPred (vec4 j, vec4 k) = true <;> simp [hp]
    · intro a _ hax
      refine sum_eq_zero fun y _ => ?_
      have hne : a ≠ vec4 j := hax
      simp [hne]
    · intro hx; exact absurd (mem_univ (vec4 j)) hx
  have hload : ambainis4WeightScheme.loadFst (vec4 j) i =
      ((∑ p ∈ amb4R with p.1 i ≠ p.2 i ∧ p.1 = vec4 j, amb4UInt p i : ℤ) : ℝ) / 3 := by
    simp only [WeightScheme.loadFst, ambainis4WeightScheme, Int.cast_sum, sum_div]
  have hwt : ambainis4WeightScheme.wtFst (vec4 j) =
      ((∑ p ∈ amb4R with p.1 = vec4 j, amb4WInt p : ℤ) : ℝ) / 3 := by
    simp only [WeightScheme.wtFst, ambainis4WeightScheme, Int.cast_sum, sum_div]
  have hdec : (5 : ℝ) *
      ((∑ p ∈ amb4R with p.1 i ≠ p.2 i ∧ p.1 = vec4 j, amb4UInt p i : ℤ) : ℝ) ≤
      2 * ((∑ p ∈ amb4R with p.1 = vec4 j, amb4WInt p : ℤ) : ℝ) := by
    rw [hload_int, hwt_int]
    exact_mod_cast amb4_fst_load_dec j i
  rw [hload, hwt]
  linarith

private theorem ambainis4WeightScheme_loadSnd_le (y : BitString 4) (i : Fin 4) :
    (5 / 2 : ℝ) * ambainis4WeightScheme.loadSnd y i ≤ ambainis4WeightScheme.wtSnd y := by
  obtain ⟨k, rfl⟩ := vec4_surj_dec y
  have hload_int :
      (∑ p ∈ amb4R with p.1 i ≠ p.2 i ∧ p.2 = vec4 k, amb4VInt p i) =
        ∑ j : Fin 16,
          if amb4PairPred (vec4 j, vec4 k) = true ∧ vec4 j i ≠ vec4 k i then
            amb4VInt (vec4 j, vec4 k) i else 0 := by
    rw [amb4R, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
    rw [← vec4_image_univ, sum_image (fun j₁ _ j₂ _ hj => vec4_inj_dec j₁ j₂ hj)]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (vec4 k)]
    · by_cases hp : amb4PairPred (vec4 j, vec4 k) = true <;>
        by_cases hi : vec4 j i ≠ vec4 k i <;> simp [hp, hi]
    · intro b _ hby
      have hne : b ≠ vec4 k := hby
      simp [hne]
    · intro hy; exact absurd (mem_image_of_mem vec4 (mem_univ k)) hy
  have hwt_int :
      (∑ p ∈ amb4R with p.2 = vec4 k, amb4WInt p) =
        ∑ j : Fin 16, if amb4PairPred (vec4 j, vec4 k) = true then
          amb4WInt (vec4 j, vec4 k) else 0 := by
    rw [amb4R, Finset.sum_filter, Finset.sum_filter, Fintype.sum_prod_type]
    rw [← vec4_image_univ, sum_image (fun j₁ _ j₂ _ hj => vec4_inj_dec j₁ j₂ hj)]
    refine sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single (vec4 k)]
    · by_cases hp : amb4PairPred (vec4 j, vec4 k) = true <;> simp [hp]
    · intro b _ hby
      have hne : b ≠ vec4 k := hby
      simp [hne]
    · intro hy; exact absurd (mem_image_of_mem vec4 (mem_univ k)) hy
  have hload : ambainis4WeightScheme.loadSnd (vec4 k) i =
      ((∑ p ∈ amb4R with p.1 i ≠ p.2 i ∧ p.2 = vec4 k, amb4VInt p i : ℤ) : ℝ) / 3 := by
    simp only [WeightScheme.loadSnd, ambainis4WeightScheme, Int.cast_sum, sum_div]
  have hwt : ambainis4WeightScheme.wtSnd (vec4 k) =
      ((∑ p ∈ amb4R with p.2 = vec4 k, amb4WInt p : ℤ) : ℝ) / 3 := by
    simp only [WeightScheme.wtSnd, ambainis4WeightScheme, Int.cast_sum, sum_div]
  have hdec : (5 : ℝ) *
      ((∑ p ∈ amb4R with p.1 i ≠ p.2 i ∧ p.2 = vec4 k, amb4VInt p i : ℤ) : ℝ) ≤
      2 * ((∑ p ∈ amb4R with p.2 = vec4 k, amb4WInt p : ℤ) : ℝ) := by
    rw [hload_int, hwt_int]
    exact_mod_cast amb4_snd_load_dec k i
  rw [hload, hwt]
  linarith

/-- **Ambainis's 4-bit separation** ([Ambainis2006], Lemma 3):
`λ(ambainis4) ≤ 2 < 5/2 ≤ ADV(ambainis4)`. -/
theorem five_halves_le_spectralAdversary_ambainis4 :
    (5 / 2 : ℝ) ≤ spectralAdversary (fun _ => True) ambainis4 := by
  have hbd := ambainis4WeightScheme.le_spectralAdversary (P := fun _ => True) (f := ambainis4)
    ambainis4WeightScheme_weightSum_pos
    (fun p hp => by
      obtain ⟨j, hj⟩ := vec4_surj_dec p.1
      obtain ⟨k, hk⟩ := vec4_surj_dec p.2
      have hmem : amb4PairPred (vec4 j, vec4 k) = true := by
        simpa [hj, hk] using (mem_filter.1 hp).2
      exact ⟨trivial, trivial, by simpa [hj, hk] using amb4_ne_dec j k hmem⟩)
    (mA := 5 / 2) (mB := 5 / 2) (by norm_num) (by norm_num)
    (fun x _ i => ambainis4WeightScheme_loadFst_le x i)
    (fun y _ i => ambainis4WeightScheme_loadSnd_le y i)
  have hsqrt : √((5 / 2 : ℝ) * (5 / 2)) = 5 / 2 := by
    rw [← sq, Real.sqrt_sq (by norm_num)]
  rwa [hsqrt] at hbd

example :
    spectralSensitivity ambainis4 < spectralAdversary (fun _ => True) ambainis4 :=
  lt_of_le_of_lt spectralSensitivity_ambainis4_le_two
    (lt_of_lt_of_le (by norm_num) five_halves_le_spectralAdversary_ambainis4)

/-! ### Negative-weight separation `ADV ≤ 3 < 16/5 ≤ ADV±` ([HoyerLeeSpalek2007], §7.2) -/

def bits6 (b0 b1 b2 b3 b4 b5 : Bool) : BitString 6 := fun i =>
  match i with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5

/-- The ten zero inputs of weight `3` in [HoyerLeeSpalek2007], Section 7.2. -/
def hlsZeroVec (j : Fin 10) : BitString 6 :=
  match j with
  | 0 => bits6 true true true false false false
  | 1 => bits6 false true true true false false
  | 2 => bits6 false false true true true false
  | 3 => bits6 true false false true true false
  | 4 => bits6 true true false false true false
  | 5 => bits6 true false true false false true
  | 6 => bits6 false true false true false true
  | 7 => bits6 false false true false true true
  | 8 => bits6 true false false true false true
  | 9 => bits6 false true false false true true

/-- The ten one inputs of weight `3` in [HoyerLeeSpalek2007], Section 7.2. -/
def hlsOneVec (k : Fin 10) : BitString 6 :=
  match k with
  | 0 => bits6 false false false true true true
  | 1 => bits6 true false false false true true
  | 2 => bits6 true true false false false true
  | 3 => bits6 false true true false false true
  | 4 => bits6 false false true true false true
  | 5 => bits6 false true false true true false
  | 6 => bits6 true false true false true false
  | 7 => bits6 true true false true false false
  | 8 => bits6 false true true false true false
  | 9 => bits6 true false true true false false

/-- Promise on `BitString 6`: Hamming weight equals `3`. -/
def hlsPromiseBool (x : BitString 6) : Bool :=
  decide (#{i : Fin 6 | x i = true} = 3)

def hlsPromise (x : BitString 6) : Prop :=
  hlsPromiseBool x = true

/-- Boolean function equal to `1` on `hlsOneVec` and `0` elsewhere ([HoyerLeeSpalek2007], §7.2). -/
def hlsFun (x : BitString 6) : Bool :=
  decide (∃ k : Fin 10, hlsOneVec k = x)

private theorem hls_zero_wt_dec : ∀ j : Fin 10, #{i : Fin 6 | hlsZeroVec j i = true} = 3 := by
  decide

private theorem hls_one_wt_dec : ∀ k : Fin 10, #{i : Fin 6 | hlsOneVec k i = true} = 3 := by
  decide

private theorem hls_zero_inj_dec : ∀ j₁ j₂ : Fin 10, hlsZeroVec j₁ = hlsZeroVec j₂ → j₁ = j₂ := by
  decide

private theorem hls_one_inj_dec : ∀ k₁ k₂ : Fin 10, hlsOneVec k₁ = hlsOneVec k₂ → k₁ = k₂ := by
  decide

private theorem hls_disjoint_dec : ∀ j k : Fin 10, hlsZeroVec j ≠ hlsOneVec k := by
  decide

private theorem hls_partition_dec :
    ∀ x : BitString 6, hlsPromiseBool x = true →
      (∃ j : Fin 10, hlsZeroVec j = x) ∨ (∃ k : Fin 10, hlsOneVec k = x) := by
  decide

private theorem hls_dist_dec :
    ∀ j k : Fin 10, 2 ≤ #{i : Fin 6 | hlsZeroVec j i ≠ hlsOneVec k i} := by
  decide

/-- Positive-weight spectral adversary upper bound `ADV(f_hw3) ≤ 3` by the Hamming-distance
barrier (`k = 2`, `N = 6`). -/
theorem spectralAdversary_hls_le_three : spectralAdversary hlsPromise hlsFun ≤ 3 := by
  have hhd : ∀ x y : BitString 6, hlsPromise x → hlsPromise y → hlsFun x ≠ hlsFun y →
      2 ≤ #{i : Fin 6 | x i ≠ y i} := by
    intro x y hx hy hne
    rcases hls_partition_dec x hx with ⟨j, rfl⟩ | ⟨k, rfl⟩ <;>
      rcases hls_partition_dec y hy with ⟨j', rfl⟩ | ⟨k', rfl⟩
    · have h0x : hlsFun (hlsZeroVec j) = false := by
        simp only [hlsFun, decide_eq_false_iff_not]
        rintro ⟨k0, hk0⟩
        exact hls_disjoint_dec j k0 hk0.symm
      have h0y : hlsFun (hlsZeroVec j') = false := by
        simp only [hlsFun, decide_eq_false_iff_not]
        rintro ⟨k0, hk0⟩
        exact hls_disjoint_dec j' k0 hk0.symm
      exact absurd (h0x.trans h0y.symm) hne
    · exact hls_dist_dec j k'
    · have hswap : #{i : Fin 6 | hlsOneVec k i ≠ hlsZeroVec j' i} =
          #{i : Fin 6 | hlsZeroVec j' i ≠ hlsOneVec k i} := by
        congr 1; ext i; simp only [mem_filter, mem_univ, true_and, ne_comm]
      rw [hswap]
      exact hls_dist_dec j' k
    · have h1x : hlsFun (hlsOneVec k) = true := decide_eq_true ⟨k, rfl⟩
      have h1y : hlsFun (hlsOneVec k') = true := decide_eq_true ⟨k', rfl⟩
      exact absurd (h1x.trans h1y.symm) hne
  have hbd := spectralAdversary_le_div_of_hammingDist_ge (by decide : 0 < 2) hhd
  linarith

/-- Integer-scaled entries `(5 * Γ)[x, y]` with `(a, b, c) = (3, -1, 1) / 5` on distinguishing pairs
of Hamming weight `3` ([HoyerLeeSpalek2007], Theorem 21 rational choice). -/
def hlsPairInt (x y : BitString 6) : ℤ :=
  if hlsPromiseBool x && hlsPromiseBool y && (hlsFun x != hlsFun y) then
    let d := #{i : Fin 6 | x i ≠ y i}
    if d = 2 then 3 else if d = 4 then -1 else if d = 6 then 1 else 0
  else 0

def hlsBlockInt : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun j k => hlsPairInt (hlsZeroVec j) (hlsOneVec k)

def hlsDiffBlockInt (i : Fin 6) : Matrix (Fin 10) (Fin 10) ℤ :=
  Matrix.of fun j k => if hlsZeroVec j i ≠ hlsOneVec k i then hlsBlockInt j k else 0

private theorem hlsBlockInt_row_sum_dec : ∀ j : Fin 10, ∑ k : Fin 10, hlsBlockInt j k = 16 := by
  decide

private theorem hlsBlockInt_col_sum_dec : ∀ k : Fin 10, ∑ j : Fin 10, hlsBlockInt j k = 16 := by
  decide

private theorem hlsDiffBlockInt_tmul_row_dec :
    ∀ i : Fin 6, ∀ j : Fin 10,
      ∑ k : Fin 10, |((hlsDiffBlockInt i)ᵀ * hlsDiffBlockInt i) j k| ≤ 25 := by
  decide

private theorem hlsDiffBlockInt_tmul_col_dec :
    ∀ i : Fin 6, ∀ k : Fin 10,
      ∑ j : Fin 10, |((hlsDiffBlockInt i)ᵀ * hlsDiffBlockInt i) j k| ≤ 25 := by
  decide

private theorem hlsDiffBlockInt_mul_t_row_dec :
    ∀ i : Fin 6, ∀ j : Fin 10,
      ∑ k : Fin 10, |(hlsDiffBlockInt i * (hlsDiffBlockInt i)ᵀ) j k| ≤ 25 := by
  decide

private theorem hlsDiffBlockInt_mul_t_col_dec :
    ∀ i : Fin 6, ∀ k : Fin 10,
      ∑ j : Fin 10, |(hlsDiffBlockInt i * (hlsDiffBlockInt i)ᵀ) j k| ≤ 25 := by
  decide

noncomputable def hlsMatrix : Matrix (BitString 6) (BitString 6) ℝ :=
  Matrix.of fun x y => (hlsPairInt x y : ℝ) / 5

private theorem hlsPairInt_symm (x y : BitString 6) : hlsPairInt x y = hlsPairInt y x := by
  have hd : #{i : Fin 6 | x i ≠ y i} = #{i : Fin 6 | y i ≠ x i} := by
    congr 1; ext i; simp only [mem_filter, mem_univ, true_and, ne_comm]
  simp only [hlsPairInt, hd]
  have hne : (hlsFun x != hlsFun y) = (hlsFun y != hlsFun x) := by
    cases hlsFun x <;> cases hlsFun y <;> rfl
  rw [Bool.and_comm (hlsPromiseBool x), hne]

theorem hlsMatrix_isSymm : hlsMatrix.IsSymm := by
  ext x y
  simp only [Matrix.transpose_apply, hlsMatrix, Matrix.of_apply, hlsPairInt_symm]

theorem hlsMatrix_isAdversary : IsAdversaryMatrix hlsPromise hlsFun hlsMatrix := by
  intro x y hne
  by_cases hcond : (hlsPromiseBool x && hlsPromiseBool y && (hlsFun x != hlsFun y)) = true
  · simp only [Bool.and_eq_true, bne_iff_ne] at hcond
    exact ⟨hcond.1.1, hcond.1.2, hcond.2⟩
  · have hcondf : (hlsPromiseBool x && hlsPromiseBool y && (hlsFun x != hlsFun y)) = false :=
      Bool.eq_false_iff.2 hcond
    rw [hlsMatrix, Matrix.of_apply, hlsPairInt, hcondf] at hne
    simp at hne

private noncomputable def hlsDiffBlockReal (i : Fin 6) : Matrix (Fin 10) (Fin 10) ℝ :=
  Matrix.of fun j k => (hlsDiffBlockInt i j k : ℝ) / 5

private theorem opNorm_toEuclideanCLM_le_one_of_int_bounds
    (B : Matrix (Fin 10) (Fin 10) ℤ)
    (hrow : ∀ j : Fin 10, ∑ k : Fin 10, |(Bᵀ * B) j k| ≤ 25)
    (hcol : ∀ k : Fin 10, ∑ j : Fin 10, |(Bᵀ * B) j k| ≤ 25) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Matrix.of fun j k => (B j k : ℝ) / 5)‖ ≤ 1 := by
  let M : Matrix (Fin 10) (Fin 10) ℝ := Matrix.of fun j k => (B j k : ℝ) / 5
  have hent (j k : Fin 10) : (Mᵀ * M) j k = (((Bᵀ * B) j k : ℤ) : ℝ) / 25 := by
    simp only [M, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    calc ∑ l : Fin 10, (B l j : ℝ) / 5 * ((B l k : ℝ) / 5)
        = (∑ l : Fin 10, (B l j : ℝ) * (B l k : ℝ)) / 25 := by
            rw [sum_div]
            refine sum_congr rfl fun l _ => by ring
      _ = (((∑ l : Fin 10, B l j * B l k : ℤ) : ℝ)) / 25 := by
            simp only [Int.cast_sum, Int.cast_mul]
  have hsum_le (s : Finset (Fin 10)) (g : Fin 10 → ℤ) (hg : ∑ x ∈ s, |g x| ≤ 25) :
      ∑ x ∈ s, |(g x : ℝ) / 25| ≤ 1 := by
    calc ∑ x ∈ s, |(g x : ℝ) / 25|
        = (∑ x ∈ s, |(g x : ℝ)|) / 25 := by
            rw [sum_div]
            refine sum_congr rfl fun x _ => by
              rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 25)]
      _ ≤ 25 / 25 := div_le_div_of_nonneg_right (by exact_mod_cast hg) (by norm_num)
      _ = 1 := by norm_num
  have hMtM : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (Mᵀ * M)‖ ≤ 1 := by
    refine (Matrix.opNorm_toEuclideanCLM_le_sqrt (Mᵀ * M) zero_le_one zero_le_one
      (fun j => ?_) (fun k => ?_)).trans (by simp)
    · simpa only [hent j] using hsum_le univ (fun k => (Bᵀ * B) j k) (hrow j)
    · simpa only [hent] using hsum_le univ (fun j => (Bᵀ * B) j k) (hcol k)
  open scoped Matrix.Norms.L2Operator in
  exact by
    have hsq : ‖M‖ ^ 2 ≤ 1 := by
      rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self M,
        Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.l2_opNorm_toEuclideanCLM (Mᵀ * M)]
      exact hMtM
    rw [Matrix.l2_opNorm_toEuclideanCLM]
    exact (sq_le_one_iff₀ (norm_nonneg M)).1 hsq

private theorem hls_disjoint : Disjoint (image hlsZeroVec univ) (image hlsOneVec univ) := by
  refine Finset.disjoint_left.2 fun x hx hy => ?_
  obtain ⟨j, _, rfl⟩ := mem_image.1 hx
  obtain ⟨k, _, hk⟩ := mem_image.1 hy
  exact hls_disjoint_dec j k hk.symm

private theorem hls_union :
    image hlsZeroVec univ ∪ image hlsOneVec univ =
      univ.filter (fun x => hlsPromiseBool x = true) := by
  ext x
  simp only [mem_union, mem_image, mem_univ, true_and, mem_filter]
  constructor
  · rintro (⟨j, rfl⟩ | ⟨k, rfl⟩)
    · exact decide_eq_true (hls_zero_wt_dec j)
    · exact decide_eq_true (hls_one_wt_dec k)
  · exact hls_partition_dec x

theorem hlsMatrix_maxDiffNorm_le_one : maxDiffNorm hlsMatrix ≤ 1 := by
  refine (maxDiffNorm_le_iff zero_le_one).2 fun i => ?_
  let M := hlsDiffBlockReal i
  have hM : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ ≤ 1 :=
    opNorm_toEuclideanCLM_le_one_of_int_bounds (hlsDiffBlockInt i)
      (hlsDiffBlockInt_tmul_row_dec i) (hlsDiffBlockInt_tmul_col_dec i)
  have hMt : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Mᵀ‖ ≤ 1 := by
    have heq : Mᵀ = Matrix.of fun j k => (((hlsDiffBlockInt i)ᵀ j k : ℤ) : ℝ) / 5 := by
      ext j k; simp [M, hlsDiffBlockReal]
    rw [heq]
    exact opNorm_toEuclideanCLM_le_one_of_int_bounds (hlsDiffBlockInt i)ᵀ
      (by simpa [Matrix.transpose_transpose] using hlsDiffBlockInt_mul_t_row_dec i)
      (by simpa [Matrix.transpose_transpose] using hlsDiffBlockInt_mul_t_col_dec i)
  refine (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_).trans (by simp)
  rw [one_mul, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
  let vZ : EuclideanSpace ℝ (Fin 10) := WithLp.toLp 2 fun j => v.ofLp (hlsZeroVec j)
  let vO : EuclideanSpace ℝ (Fin 10) := WithLp.toLp 2 fun k => v.ofLp (hlsOneVec k)
  let A := hlsMatrix.hadamard (diffMatrix i)
  have hA_zero_row (j : Fin 10) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A v).ofLp (hlsZeroVec j) =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) M vO).ofLp j := by
    change ∑ y : BitString 6, A (hlsZeroVec j) y * v.ofLp y = ∑ k : Fin 10, M j k * vO.ofLp k
    have hsplit : ∀ y : BitString 6,
        (if y ∈ image hlsOneVec univ then A (hlsZeroVec j) y * v.ofLp y else 0) =
          A (hlsZeroVec j) y * v.ofLp y := by
      intro y
      split_ifs with hy
      · rfl
      · suffices h0 : hlsPairInt (hlsZeroVec j) y = 0 by
          simp [A, Matrix.hadamard_apply, hlsMatrix, h0]
        by_cases hpy : hlsPromiseBool y = true
        · rcases hls_partition_dec y hpy with ⟨j', rfl⟩ | ⟨k, rfl⟩
          · have hfalse : hlsFun (hlsZeroVec j) = false := by
              simp only [hlsFun, decide_eq_false_iff_not]
              rintro ⟨k, hk⟩
              exact hls_disjoint_dec j k hk.symm
            have hfalse' : hlsFun (hlsZeroVec j') = false := by
              simp only [hlsFun, decide_eq_false_iff_not]
              rintro ⟨k, hk⟩
              exact hls_disjoint_dec j' k hk.symm
            simp [hlsPairInt, hfalse, hfalse']
          · exact absurd (mem_image_of_mem hlsOneVec (mem_univ k)) hy
        · simp [hlsPairInt, hpy]
    calc ∑ y : BitString 6, A (hlsZeroVec j) y * v.ofLp y
        = ∑ y : BitString 6,
            if y ∈ image hlsOneVec univ then A (hlsZeroVec j) y * v.ofLp y else 0 :=
          sum_congr rfl fun y _ => (hsplit y).symm
      _ = ∑ y ∈ image hlsOneVec univ, A (hlsZeroVec j) y * v.ofLp y := by rw [← sum_filter]; simp
      _ = ∑ k : Fin 10, A (hlsZeroVec j) (hlsOneVec k) * v.ofLp (hlsOneVec k) :=
          sum_image fun k₁ _ k₂ _ hk => hls_one_inj_dec k₁ k₂ hk
      _ = ∑ k : Fin 10, M j k * vO.ofLp k := by
          refine sum_congr rfl fun k _ => ?_
          simp only [A, Matrix.hadamard_apply, diffMatrix_apply, hlsMatrix, Matrix.of_apply,
            M, hlsDiffBlockReal, hlsDiffBlockInt, hlsBlockInt, vO]
          split_ifs <;> simp
  have hA_one_row (k : Fin 10) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A v).ofLp (hlsOneVec k) =
        (Matrix.toEuclideanCLM (𝕜 := ℝ) Mᵀ vZ).ofLp k := by
    change ∑ y : BitString 6, A (hlsOneVec k) y * v.ofLp y = ∑ j : Fin 10, Mᵀ k j * vZ.ofLp j
    have hsplit : ∀ y : BitString 6,
        (if y ∈ image hlsZeroVec univ then A (hlsOneVec k) y * v.ofLp y else 0) =
          A (hlsOneVec k) y * v.ofLp y := by
      intro y
      split_ifs with hy
      · rfl
      · suffices h0 : hlsPairInt (hlsOneVec k) y = 0 by
          simp [A, Matrix.hadamard_apply, hlsMatrix, h0]
        by_cases hpy : hlsPromiseBool y = true
        · rcases hls_partition_dec y hpy with ⟨j, rfl⟩ | ⟨k', rfl⟩
          · exact absurd (mem_image_of_mem hlsZeroVec (mem_univ j)) hy
          · have h1 : hlsFun (hlsOneVec k) = true := decide_eq_true ⟨k, rfl⟩
            have h1' : hlsFun (hlsOneVec k') = true := decide_eq_true ⟨k', rfl⟩
            simp [hlsPairInt, h1, h1']
        · simp [hlsPairInt, hpy]
    calc ∑ y : BitString 6, A (hlsOneVec k) y * v.ofLp y
        = ∑ y : BitString 6,
            if y ∈ image hlsZeroVec univ then A (hlsOneVec k) y * v.ofLp y else 0 :=
          sum_congr rfl fun y _ => (hsplit y).symm
      _ = ∑ y ∈ image hlsZeroVec univ, A (hlsOneVec k) y * v.ofLp y := by rw [← sum_filter]; simp
      _ = ∑ j : Fin 10, A (hlsOneVec k) (hlsZeroVec j) * v.ofLp (hlsZeroVec j) :=
          sum_image fun j₁ _ j₂ _ hj => hls_zero_inj_dec j₁ j₂ hj
      _ = ∑ j : Fin 10, Mᵀ k j * vZ.ofLp j := by
          refine sum_congr rfl fun j _ => ?_
          have hpair : hlsPairInt (hlsOneVec k) (hlsZeroVec j) =
              hlsPairInt (hlsZeroVec j) (hlsOneVec k) :=
            hlsPairInt_symm _ _
          have hne_iff : hlsOneVec k i ≠ hlsZeroVec j i ↔ hlsZeroVec j i ≠ hlsOneVec k i := ne_comm
          simp only [A, Matrix.hadamard_apply, diffMatrix_apply, hlsMatrix, Matrix.transpose_apply,
            Matrix.of_apply, hpair, M, hlsDiffBlockReal, hlsDiffBlockInt, hlsBlockInt, vZ, hne_iff]
          split_ifs <;> simp
  have hA_other (x : BitString 6) (hx : hlsPromiseBool x = false) :
      (Matrix.toEuclideanCLM (𝕜 := ℝ) A v).ofLp x = 0 := by
    change ∑ y : BitString 6, A x y * v.ofLp y = 0
    refine sum_eq_zero fun y _ => ?_
    have h0 : hlsPairInt x y = 0 := by simp [hlsPairInt, hx]
    simp [A, Matrix.hadamard_apply, hlsMatrix, h0]
  have hdisj : Disjoint (image hlsZeroVec univ) (image hlsOneVec univ) := hls_disjoint
  have hunion : image hlsZeroVec univ ∪ image hlsOneVec univ =
      univ.filter (fun x => hlsPromiseBool x = true) := hls_union
  have hsum_A : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ ^ 2 =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M vO‖ ^ 2 +
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Mᵀ vZ‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    have hsplit_all : ∑ x : BitString 6, (Matrix.toEuclideanCLM (𝕜 := ℝ) A v).ofLp x ^ 2 =
        ∑ x ∈ image hlsZeroVec univ ∪ image hlsOneVec univ,
          (Matrix.toEuclideanCLM (𝕜 := ℝ) A v).ofLp x ^ 2 := by
      symm
      refine sum_subset (subset_univ _) fun x _ hx => ?_
      rw [hunion, mem_filter] at hx
      have hfalse : hlsPromiseBool x = false := by
        cases hb : hlsPromiseBool x
        · rfl
        · exact absurd ⟨mem_univ _, hb⟩ hx
      simp [hA_other x hfalse]
    rw [hsplit_all, sum_union hdisj,
      sum_image (fun j₁ _ j₂ _ hj => hls_zero_inj_dec j₁ j₂ hj),
      sum_image (fun k₁ _ k₂ _ hk => hls_one_inj_dec k₁ k₂ hk)]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact sum_congr rfl fun j _ => by rw [hA_zero_row j]
    · exact sum_congr rfl fun k _ => by rw [hA_one_row k]
  have hsum_v : ‖vO‖ ^ 2 + ‖vZ‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq, add_comm]
    dsimp only [vZ, vO]
    calc ∑ j : Fin 10, v.ofLp (hlsZeroVec j) ^ 2 + ∑ k : Fin 10, v.ofLp (hlsOneVec k) ^ 2
        = ∑ x ∈ image hlsZeroVec univ, v.ofLp x ^ 2 + ∑ x ∈ image hlsOneVec univ, v.ofLp x ^ 2 := by
            rw [sum_image (fun j₁ _ j₂ _ hj => hls_zero_inj_dec j₁ j₂ hj),
              sum_image (fun k₁ _ k₂ _ hk => hls_one_inj_dec k₁ k₂ hk)]
      _ = ∑ x ∈ image hlsZeroVec univ ∪ image hlsOneVec univ, v.ofLp x ^ 2 :=
            (sum_union hdisj).symm
      _ ≤ ∑ x : BitString 6, v.ofLp x ^ 2 := sum_le_univ_sum_of_nonneg fun x => sq_nonneg _
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A v‖ ^ 2
      = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) M vO‖ ^ 2 +
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Mᵀ vZ‖ ^ 2 := hsum_A
    _ ≤ (‖Matrix.toEuclideanCLM (𝕜 := ℝ) M‖ * ‖vO‖) ^ 2 +
          (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Mᵀ‖ * ‖vZ‖) ^ 2 := by
        refine add_le_add ?_ ?_
        · exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
        · exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.le_opNorm _ _) 2
    _ ≤ (1 * ‖vO‖) ^ 2 + (1 * ‖vZ‖) ^ 2 := by
        refine add_le_add ?_ ?_
        · refine pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_right hM (norm_nonneg _)) 2
        · refine pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_right hMt (norm_nonneg _)) 2
    _ = ‖vO‖ ^ 2 + ‖vZ‖ ^ 2 := by ring
    _ ≤ ‖v‖ ^ 2 := hsum_v

theorem hlsMatrix_opNorm_ge : (16 / 5 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix‖ := by
  let u : EuclideanSpace ℝ (BitString 6) :=
    WithLp.toLp 2 fun x => if hlsPromiseBool x then 1 / √20 else 0
  have hcard : #(univ.filter fun x => hlsPromiseBool x = true) = 20 := by
    rw [← hls_union, card_union_of_disjoint hls_disjoint,
      card_image_of_injective _ (fun j₁ j₂ hj => hls_zero_inj_dec j₁ j₂ hj),
      card_image_of_injective _ (fun k₁ k₂ hk => hls_one_inj_dec k₁ k₂ hk)]
    norm_num
  have hu_sq : ‖u‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsplit : ∑ x : BitString 6, u.ofLp x ^ 2 =
        ∑ _x ∈ univ.filter (fun x => hlsPromiseBool x = true), (1 / √20 : ℝ) ^ 2 := by
      have hterm : ∀ x : BitString 6,
          u.ofLp x ^ 2 = if hlsPromiseBool x = true then (1 / √20 : ℝ) ^ 2 else 0 := by
        intro x
        simp only [u]
        split_ifs <;> simp
      simp_rw [hterm, ← sum_filter]
    rw [hsplit, sum_const, hcard, nsmul_eq_mul, one_div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hu : ‖u‖ = 1 := by nlinarith [norm_nonneg u]
  have hsum_all : ∑ x : BitString 6, ∑ y : BitString 6, (hlsPairInt x y : ℝ) = 320 := by
    have hfst : ∀ x : BitString 6, hlsPromiseBool x = false →
        ∑ y : BitString 6, (hlsPairInt x y : ℝ) = 0 := fun x hx =>
      sum_eq_zero fun y _ => by simp [hlsPairInt, hx]
    have hz_row : ∀ j : Fin 10, ∑ y : BitString 6, (hlsPairInt (hlsZeroVec j) y : ℝ) = 16 := by
      intro j
      have hsub : ∑ y : BitString 6, (hlsPairInt (hlsZeroVec j) y : ℝ) =
          ∑ y ∈ image hlsOneVec univ, (hlsPairInt (hlsZeroVec j) y : ℝ) := by
        symm
        refine sum_subset (subset_univ _) fun y _ hy => ?_
        by_cases hpy : hlsPromiseBool y = true
        · rcases hls_partition_dec y hpy with ⟨j', rfl⟩ | ⟨k, rfl⟩
          · have h0 : hlsFun (hlsZeroVec j) = false := by
              simp only [hlsFun, decide_eq_false_iff_not]
              rintro ⟨k, hk⟩; exact hls_disjoint_dec j k hk.symm
            have h0' : hlsFun (hlsZeroVec j') = false := by
              simp only [hlsFun, decide_eq_false_iff_not]
              rintro ⟨k, hk⟩; exact hls_disjoint_dec j' k hk.symm
            simp [hlsPairInt, h0, h0']
          · exact absurd (mem_image_of_mem hlsOneVec (mem_univ k)) hy
        · simp [hlsPairInt, hpy]
      rw [hsub, sum_image (fun k₁ _ k₂ _ hk => hls_one_inj_dec k₁ k₂ hk)]
      exact_mod_cast hlsBlockInt_row_sum_dec j
    have ho_row : ∀ k : Fin 10, ∑ y : BitString 6, (hlsPairInt (hlsOneVec k) y : ℝ) = 16 := by
      intro k
      have hsub : ∑ y : BitString 6, (hlsPairInt (hlsOneVec k) y : ℝ) =
          ∑ y ∈ image hlsZeroVec univ, (hlsPairInt (hlsOneVec k) y : ℝ) := by
        symm
        refine sum_subset (subset_univ _) fun y _ hy => ?_
        by_cases hpy : hlsPromiseBool y = true
        · rcases hls_partition_dec y hpy with ⟨j, rfl⟩ | ⟨k', rfl⟩
          · exact absurd (mem_image_of_mem hlsZeroVec (mem_univ j)) hy
          · have h1 : hlsFun (hlsOneVec k) = true := decide_eq_true ⟨k, rfl⟩
            have h1' : hlsFun (hlsOneVec k') = true := decide_eq_true ⟨k', rfl⟩
            simp [hlsPairInt, h1, h1']
        · simp [hlsPairInt, hpy]
      rw [hsub, sum_image (fun j₁ _ j₂ _ hj => hls_zero_inj_dec j₁ j₂ hj)]
      have heq : ∑ j : Fin 10, hlsPairInt (hlsOneVec k) (hlsZeroVec j) =
          ∑ j : Fin 10, hlsBlockInt j k :=
        sum_congr rfl fun j _ => by simp only [hlsBlockInt, Matrix.of_apply, hlsPairInt_symm]
      exact_mod_cast heq.trans (hlsBlockInt_col_sum_dec k)
    have hsplit_x : ∑ x : BitString 6, ∑ y : BitString 6, (hlsPairInt x y : ℝ) =
        ∑ x ∈ image hlsZeroVec univ ∪ image hlsOneVec univ,
          ∑ y : BitString 6, (hlsPairInt x y : ℝ) := by
      symm
      refine sum_subset (subset_univ _) fun x _ hx => ?_
      rw [hls_union, mem_filter] at hx
      cases hb : hlsPromiseBool x
      · exact hfst x hb
      · exact absurd ⟨mem_univ _, hb⟩ hx
    rw [hsplit_x, sum_union hls_disjoint,
      sum_image (fun j₁ _ j₂ _ hj => hls_zero_inj_dec j₁ j₂ hj),
      sum_image (fun k₁ _ k₂ _ hk => hls_one_inj_dec k₁ k₂ hk)]
    simp only [hz_row, ho_row, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  have hray : inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix u) = 16 / 5 := by
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, mul_sum, u]
    have heach : ∀ x y : BitString 6,
        (if hlsPromiseBool x then 1 / √20 else 0) *
          (hlsMatrix x y * (if hlsPromiseBool y then 1 / √20 else 0)) =
          (hlsPairInt x y : ℝ) / 100 := by
      intro x y
      by_cases hx : hlsPromiseBool x = true <;> by_cases hy : hlsPromiseBool y = true
      · simp only [hx, hy, ↓reduceIte, hlsMatrix, Matrix.of_apply]
        calc (1 / √20) * (((hlsPairInt x y : ℝ) / 5) * (1 / √20))
            = (hlsPairInt x y : ℝ) / (5 * (√20 * √20)) := by ring
          _ = (hlsPairInt x y : ℝ) / 100 := by rw [Real.mul_self_sqrt (by norm_num)]; norm_num
      · have hyf : hlsPromiseBool y = false := Bool.eq_false_iff.2 hy
        simp [hyf, hlsMatrix, hlsPairInt]
      · have hxf : hlsPromiseBool x = false := Bool.eq_false_iff.2 hx
        simp [hxf, hlsMatrix, hlsPairInt]
      · have hxf : hlsPromiseBool x = false := Bool.eq_false_iff.2 hx
        simp [hxf, hlsMatrix, hlsPairInt]
    simp_rw [heach, ← sum_div, hsum_all]
    norm_num
  calc (16 / 5 : ℝ) = inner ℝ u (Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix u) := hray.symm
    _ ≤ ‖u‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix u‖ := real_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix‖ := by rw [hu, mul_one, one_mul]

/-- **Strict separation of nonnegative and negative-weight adversaries**
([HoyerLeeSpalek2007], §7.2): `ADV(f_hw3) ≤ 3 < 16/5 ≤ ADV±(f_hw3)`. -/
theorem sixteen_fifths_le_generalAdversary_hls :
    (16 / 5 : ℝ) ≤ generalAdversary hlsPromise hlsFun := by
  have hm_pos : 0 < maxDiffNorm hlsMatrix := by
    by_contra hle
    have hm0 : maxDiffNorm hlsMatrix = 0 := le_antisymm (not_lt.1 hle) (maxDiffNorm_nonneg _)
    have h0 := eq_zero_of_maxDiffNorm_eq_zero hlsMatrix_isAdversary hm0
    have hnorm := hlsMatrix_opNorm_ge
    rw [h0, map_zero, norm_zero] at hnorm
    linarith
  calc (16 / 5 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix‖ / 1 := by
        simpa using hlsMatrix_opNorm_ge
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) hlsMatrix‖ / maxDiffNorm hlsMatrix :=
        div_le_div_of_nonneg_left (norm_nonneg _) hm_pos hlsMatrix_maxDiffNorm_le_one
    _ ≤ generalAdversary hlsPromise hlsFun :=
        le_generalAdversary hlsMatrix_isSymm hlsMatrix_isAdversary

theorem spectralAdversary_lt_generalAdversary_hls :
    spectralAdversary hlsPromise hlsFun < generalAdversary hlsPromise hlsFun :=
  lt_of_le_of_lt spectralAdversary_hls_le_three
    (lt_of_lt_of_le (by norm_num) sixteen_fifths_le_generalAdversary_hls)

/-! ### Non-Boolean finite alphabet `Fin 3` instance of the general adversary bound -/

def ternary1 (x : BitString 1) : Fin 3 :=
  if x 0 then 1 else 2

def ternary1Out : Fin 3 → Finset (Fin 1 × Bool × Unit)
  | 0 => ∅
  | 1 => {(0, true, ())}
  | 2 => {(0, false, ())}

private theorem pairwise_disjoint_ternary1Out : Pairwise (Disjoint on ternary1Out) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | decide

example :
    (1 - 2 * √((0 : ℝ) * (1 - 0)) - 0) * generalAdversary (fun _ => True) ternary1 ≤ 2 * (1 : ℕ) :=
  one_sub_mul_generalAdversary_le readBit norm_ψ₀ 1 ternary1Out pairwise_disjoint_ternary1Out
    le_rfl (by norm_num) fun x _ => by
      cases hx : x 0
      · have hc : ternary1Out (ternary1 x) = acceptᶜ := by
          simp only [ternary1, ternary1Out, hx]
          decide
        rw [hc, measureProb_compl, norm_run, norm_ψ₀, one_pow, measureProb_readBit, hx,
          bitVal_false]
      · have ha : ternary1Out (ternary1 x) = accept := by simp [ternary1, ternary1Out, hx, accept]
        rw [ha, measureProb_readBit, hx, bitVal_true]
        norm_num

/-- Surjective 2-bit function into `Fin 3` (`00 ↦ 0, 01 ↦ 0, 10 ↦ 1, 11 ↦ 2`). -/
def ternary2 (x : BitString 2) : Fin 3 :=
  if x 0 then (if x 1 then 2 else 1) else 0

def ternary2Mat : Matrix (BitString 2) (BitString 2) ℝ :=
  Matrix.of fun x y => if ternary2 x ≠ ternary2 y ∧ #{i : Fin 2 | x i ≠ y i} = 1 then 1 else 0

theorem generalAdversary_ternary2_ge_one : 1 ≤ generalAdversary (fun _ => True) ternary2 := by
  have hsym : ternary2Mat.IsSymm := by
    ext x y
    have hd : #{i : Fin 2 | x i ≠ y i} = #{i : Fin 2 | y i ≠ x i} := by
      congr 1; ext i; simp only [mem_filter, mem_univ, true_and, ne_comm]
    simp only [Matrix.transpose_apply, ternary2Mat, Matrix.of_apply, hd]
    by_cases h : ternary2 x ≠ ternary2 y <;> simp [h, ne_comm]
  have hΓ : IsAdversaryMatrix (fun _ => True) ternary2 ternary2Mat := by
    intro x y hne
    have hcond : ternary2 x ≠ ternary2 y ∧ #{i : Fin 2 | x i ≠ y i} = 1 := by
      by_contra h
      exact hne (by simp [ternary2Mat, h])
    exact ⟨trivial, trivial, hcond.1⟩
  have hmax : maxDiffNorm ternary2Mat ≤ 1 := by
    refine (maxDiffNorm_le_iff zero_le_one).2 fun i => ?_
    have hrow (x : BitString 2) :
        ∑ y : BitString 2, |(ternary2Mat.hadamard (diffMatrix i)) x y| ≤ 1 := by
      rw [Finset.sum_eq_single (Function.update x i (!x i))]
      · simp only [Matrix.hadamard_apply, ternary2Mat, Matrix.of_apply, diffMatrix_apply]
        split_ifs <;> norm_num
      · intro y _ hyne
        by_cases hxi : x i = y i
        · simp [Matrix.hadamard_apply, diffMatrix_apply, hxi]
        · have hgt : #{j : Fin 2 | x j ≠ y j} ≠ 1 := by
            intro h1
            have heq : y = Function.update x i (!x i) := by
              ext j
              by_cases hj : j = i
              · subst hj; cases hxv : x j <;> simp_all
              · by_contra hdiff
                have hne_j : x j ≠ y j := by
                  simpa [Function.update_of_ne hj, eq_comm] using hdiff
                have h2 : 2 ≤ #{k : Fin 2 | x k ≠ y k} := by
                  have hsub : ({i, j} : Finset (Fin 2)) ⊆
                      (univ : Finset (Fin 2)).filter (fun k => x k ≠ y k) := by
                    intro k hk
                    simp only [mem_insert, mem_singleton] at hk
                    rcases hk with rfl | rfl
                    · exact mem_filter.2 ⟨mem_univ _, hxi⟩
                    · exact mem_filter.2 ⟨mem_univ _, hne_j⟩
                  have hcard2 : ({i, j} : Finset (Fin 2)).card = 2 := card_pair (Ne.symm hj)
                  exact hcard2.symm.trans_le (card_le_card hsub)
                omega
            exact hyne heq
          simp [Matrix.hadamard_apply, ternary2Mat, hgt]
      · intro hm; exact absurd (mem_univ _) hm
    refine (Matrix.opNorm_toEuclideanCLM_le_sqrt _ zero_le_one zero_le_one hrow fun y => ?_).trans
      (by simp)
    have heq (x : BitString 2) : |(ternary2Mat.hadamard (diffMatrix i)) x y| =
        |(ternary2Mat.hadamard (diffMatrix i)) y x| := by
      have h1 : ternary2Mat x y = ternary2Mat y x := hsym.apply y x
      have h2 : diffMatrix i x y = diffMatrix i y x := by
        simp only [diffMatrix_apply, ne_comm]
      simp only [Matrix.hadamard_apply, h1, h2]
    simpa only [heq] using hrow y
  have hge1 : 1 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ternary2Mat‖ := by
    let x0 : BitString 2 := fun _ => false
    let y0 : BitString 2 := fun i => decide (i = 0)
    have hne : x0 ≠ y0 := fun h => by
      have : x0 0 = y0 0 := congrFun h 0
      simp [x0, y0] at this
    have hent : |ternary2Mat x0 y0| = 1 := by
      have hcard : #{i : Fin 2 | x0 i ≠ y0 i} = 1 := by decide
      have hfn : ternary2 x0 ≠ ternary2 y0 := by decide
      simp [ternary2Mat, hfn, hcard]
    exact hent ▸ Matrix.abs_entry_le_norm_toEuclideanCLM ternary2Mat x0 y0
  by_cases hm0 : maxDiffNorm ternary2Mat = 0
  · have h0 := eq_zero_of_maxDiffNorm_eq_zero hΓ hm0
    rw [h0, map_zero, norm_zero] at hge1
    linarith
  · have hm_pos : 0 < maxDiffNorm ternary2Mat := lt_of_le_of_ne (maxDiffNorm_nonneg _) (Ne.symm hm0)
    calc (1 : ℝ) ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ternary2Mat‖ / 1 := by simpa using hge1
      _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) ternary2Mat‖ / maxDiffNorm ternary2Mat :=
          div_le_div_of_nonneg_left (norm_nonneg _) hm_pos hmax
      _ ≤ generalAdversary (fun _ => True) ternary2 := le_generalAdversary hsym hΓ


end
end CslibFrontierTests.QuantumGeneralAdversary
