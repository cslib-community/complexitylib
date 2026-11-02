/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PolynomialAtomRows.NoOverflow
public import Complexity.Foundations.Probability.PolynomialAtomRows.FirstOverflow
public import Complexity.Foundations.Probability.PolynomialAtomFalseOverflow
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Actual compression comparison and fourth-moment assembly

The final output of the actual compression recursion is compared with truth on every run
outside false first overflows. A least actual overflow is selected when one exists; the
selected tail retains both that first-overflow event and the caller's chosen heavy-event
predicate. No bound on the final output discrepancy is assumed.

The final-prefix and tail coefficient is fixed before the compression scale; only the
weighted preloss coefficient depends on that scale. The heavy predicate is a parameter of
this deterministic partition, not a claim about its probability. Clients can instantiate it
with the concrete heavy-count event and separately charge false overflows.

These are bounded assembly steps toward the fourth-moment adaptation of
[OpenAI2026LogSpace, Section 8.4, Proposition 8.5]. The integrated estimate also charges
false first overflows by their actual raw-prefix moments. Mean/noise decomposition and
convergent parameter schedules remain separate. The budget hypotheses control every raw prefix
pointwise; this module does not yet derive these budgets from estimator input moments.

## Main results

* `Cslib.PolynomialAtomRow.exists_compression_root_bound`: actual row comparison outside
  false first overflows, preserving the selected event mask.
* `Cslib.PolynomialAtomRow.exists_compression_rowNormPow_le`: the unconditional integrated
  fourth-moment estimate, including the actual false-overflow charge.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, proof of Proposition 8.5, source labels `buf-no-overflow`, `buf-false-sum`
  and `buf-true-sum` (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Cslib.PolynomialAtomRow

open Finset RowCompression Probability
open scoped BigOperators

variable (kind : PolynomialAtomRow) {θ : ℝ}

open Classical in
/-- Outside false first overflows, the actual output has a weighted prefix contribution,
a no-overflow final contribution, and the tail at the actual true first overflow.
The final and tail coefficient is chosen before the compression scale. -/
theorem exists_compression_root_bound (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ θ / 10000 →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ {ι : Type*} (S : Finset ι) (n : ℕ → ℕ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (a : State ι) (truth : ι → Fin 2 → ℝ)
        (K m : ℕ) (heavy : ℕ → Prop),
        0 < K → a.defaultValue = 0 →
        (∀ y ∈ S, 0 ≤ truth y 0) → (∀ y ∈ S, |truth y 1| ≤ η / 2) →
        (∀ i < m, K ≤ n i) → ∀ (ε : ℕ → ℝ),
        (∀ i < m, 0 ≤ ε i) →
        (∀ i < m, ∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row (i + 1) y) ≤ ε i) →
        ∀ εfinal : ℝ, 0 ≤ εfinal →
        (∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ a.row m y) ≤ εfinal) →
        (¬ ∃ j < m, IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j ∧ ¬heavy j) →
        ∀ y ∈ S,
        |kind.stateRootError θ S K
          (iterate S n (fun _ => K) (dyadicFloor η m) Δ a m) ⟨0, truth⟩ y| ≤
          A * (∑ i ∈ range m, dyadicFloor η m i * ε i) +
          C * (if ∀ i < m, stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ a i ≤
            dyadicFloor η m i then εfinal else 0) +
          C * (∑ j ∈ range m,
            if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j ∧ heavy j then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0) := by
  classical
  obtain ⟨Cf, hCf, hno⟩ := kind.exists_noOverflow_root_bound hθ
  obtain ⟨Ct, hCt, hover⟩ := kind.exists_firstOverflow_truth_root_bound hθ
  refine ⟨max Cf Ct, le_trans hCf (le_max_left _ _), ?_⟩
  intro η hη hmargin
  obtain ⟨An, hAn, hn⟩ := hno η hη hmargin
  obtain ⟨At, hAt, ht⟩ := hover η hη hmargin
  refine ⟨max An At, le_trans hAn (le_max_left _ _), ?_⟩
  intro ι S n Δ a truth K m heavy hK ha hfirst hsecond hcapacity ε hε herr
    εfinal hεfinal herrfinal hfalse y hy
  have hpre0 : 0 ≤ ∑ i ∈ range m, dyadicFloor η m i * ε i :=
    sum_nonneg fun i hi => mul_nonneg (dyadicFloor_nonneg hη.le _ _) (hε i (mem_range.mp hi))
  have htail0 : 0 ≤ ∑ j ∈ range m,
      if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j ∧ heavy j then
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0 := by
    refine sum_nonneg fun j _ => ?_
    split_ifs
    · exact sum_nonneg fun i hi => mul_nonneg (by positivity) (hε i (mem_Ico.mp hi).2)
    · exact le_rfl
  by_cases hnone : ∀ i < m, stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ a i ≤
      dyadicFloor η m i
  · rw [ite_eq_left hnone]
    have hbound := hn S n Δ a truth K hK ha m hnone hfirst hsecond ε hε
      (fun i hi z hz _ => herr i hi z hz) εfinal hεfinal herrfinal y hy
    have hp := mul_le_mul_of_nonneg_right (le_max_left An At) hpre0
    have hf := mul_le_mul_of_nonneg_right (le_max_left Cf Ct) hεfinal
    have htail := mul_nonneg (hCf.trans (le_max_left Cf Ct)) htail0
    linarith
  · have hex : ∃ j, j < m ∧ dyadicFloor η m j <
        stepThreshold S n (fun _ => K) (dyadicFloor η m) Δ a j := by
      push Not at hnone
      exact hnone
    let j := Nat.find hex
    have hj := Nat.find_spec hex
    have hjm : j < m := hj.1
    have hjover : IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j := by
      refine ⟨?_, hj.2⟩
      intro i hi
      exact le_of_not_gt fun h => Nat.find_min hex hi ⟨by omega, h⟩
    have hheavy : heavy j := by
      by_contra h
      exact hfalse ⟨j, hjm, hjover, h⟩
    have hbound := ht S n Δ a truth K hK ha m j hjm hjover hfirst hsecond
      (fun i _ hi => hcapacity i hi) ε hε
      (fun i hi z hz _ => herr i (hi.trans hjm) z hz)
      (fun i _ hi z hz => herr i hi z hz) y hy
    have hprefix : (∑ i ∈ range j, dyadicFloor η m i * ε i) ≤
        ∑ i ∈ range m, dyadicFloor η m i * ε i := by
      apply sum_le_sum_of_subset_of_nonneg (range_mono hjm.le)
      intro i hi _
      exact mul_nonneg (dyadicFloor_nonneg hη.le _ _) (hε i (mem_range.mp hi))
    have hselected : (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i) ≤
        ∑ j ∈ range m,
          if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j ∧ heavy j then
            ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0 := by
      have h := single_le_sum (s := range m)
        (f := fun j => if IsFirstOverflow S n (fun _ => K) (dyadicFloor η m) Δ a j ∧
          heavy j then ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0)
        (fun i _ => by
          split_ifs
          · exact sum_nonneg fun z hz => mul_nonneg (by positivity) (hε z (mem_Ico.mp hz).2)
          · exact le_rfl) (mem_range.mpr hjm)
      simpa only [hjover, hheavy, and_self, ↓reduceIte] using h
    rw [ite_eq_right hnone, mul_zero, add_zero]
    have hp := (mul_le_mul_of_nonneg_left hprefix hAt).trans
      (mul_le_mul_of_nonneg_right (le_max_right An At) hpre0)
    have htail := (mul_le_mul_of_nonneg_left hselected hCt).trans
      (mul_le_mul_of_nonneg_right (le_max_right Cf Ct) htail0)
    linarith

private theorem add_add_pow_four_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a + b + c) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4) := by
  have h := add_pow_le ha hb 4
  have h' := add_pow_le (add_nonneg ha hb) hc 4
  norm_num at h h'
  nlinarith [pow_nonneg hc 4]

open Classical in
/-- The actual final output is bounded by weighted prefix, no-overflow final and true-overflow
budgets, plus the existing false-overflow raw-prefix charge. The masks and all errors may be
correlated. No final-output error premise or factor counting endpoints or groups is introduced. -/
theorem exists_compression_rowNormPow_le (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ θ / 10000 → η ≤ 1 →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ {Ω V : Type*} [Fintype Ω] [Fintype V]
        (N u : ℝ), 0 ≤ N * u → ∀ (X Y : Ω → V → Prop)
        [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
        (n : ℕ → ℕ) (K m : ℕ), 0 < K → (∀ i < m, K ≤ n i) →
        ∀ (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (a : Ω → V → State V)
        (truth : Ω → V → V → Fin 2 → ℝ),
        (∀ σ x, X σ x → (a σ x).defaultValue = 0) →
        (∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0) →
        (∀ σ x y, X σ x → Y σ y → |truth σ x y 1| ≤ η / 2) →
        (∀ j < m, ∀ σ x y, X σ x → Y σ y →
          truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) →
        ∀ (ε : ℕ → Ω → V → ℝ) (εfinal : Ω → V → ℝ),
        (∀ i < m, ∀ σ x, X σ x → 0 ≤ ε i σ x) →
        (∀ σ x, X σ x → 0 ≤ εfinal σ x) →
        (∀ i < m, ∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (a σ x).row (i + 1) y) ≤ ε i σ x) →
        (∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (a σ x).row m y) ≤ εfinal σ x) →
        let S := fun σ => ({y | Y σ y} : Finset V)
        let actual := fun σ x => iterate (S σ) n (fun _ => K)
          (dyadicFloor η m) (Δ σ x) (a σ x) m
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor η m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) i ≤
            dyadicFloor η m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rowNormPow 4 N u X Y (fun σ x y =>
          kind.stateRootError θ (S σ) K (actual σ x) ⟨0, truth σ x⟩ y) ≤
          128 * (K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
            C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
          ∑ j ∈ range m, (64 * (K : ℝ) / ((n j : ℝ) * dyadicFloor η m j ^ 4)) *
            rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (a σ x).row (j + 1) y)) := by
  classical
  obtain ⟨C, hC, hscales⟩ := kind.exists_compression_root_bound hθ
  refine ⟨C, hC, ?_⟩
  intro η hη hmargin hη1
  obtain ⟨A, hA, hbound⟩ := hscales η hη hmargin
  refine ⟨A, hA, ?_⟩
  intro Ω V _ _ N u hNu X Y _ _ n K m hK hcapacity Δ a truth ha hfirst hsecond
    hvanish ε εfinal hε hεfinal herr herrfinal
  dsimp only
  let S := fun σ => ({y | Y σ y} : Finset V)
  let actual := fun σ x => iterate (S σ) n (fun _ => K)
    (dyadicFloor η m) (Δ σ x) (a σ x) m
  let D := fun σ x y => kind.stateRootError θ (S σ) K (actual σ x) ⟨0, truth σ x⟩ y
  let heavy := fun j σ x =>
    heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ
  let F := fun σ x => ∃ j < m,
    IsFirstOverflow (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) j ∧ ¬heavy j σ x
  let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor η m i * ε i σ x
  let No := fun σ x => if ∀ i < m,
      stepThreshold (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) i ≤
        dyadicFloor η m i then εfinal σ x else 0
  let Tail := fun σ x => ∑ j ∈ range m,
    if IsFirstOverflow (S σ) n (fun _ => K) (dyadicFloor η m) (Δ σ x) (a σ x) j ∧
      heavy j σ x then ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
  have hpre0 (σ : Ω) (x : V) (hx : X σ x) : 0 ≤ Pre σ x :=
    sum_nonneg fun i hi => mul_nonneg (dyadicFloor_nonneg hη.le _ _) (hε i (mem_range.mp hi) σ x hx)
  have hno0 (σ : Ω) (x : V) (hx : X σ x) : 0 ≤ No σ x := by
    dsimp only [No]
    split_ifs
    · exact hεfinal σ x hx
    · exact le_rfl
  have htail0 (σ : Ω) (x : V) (hx : X σ x) : 0 ≤ Tail σ x := by
    refine sum_nonneg fun j _ => ?_
    split_ifs
    · exact sum_nonneg fun i hi => mul_nonneg (by positivity) (hε i (mem_Ico.mp hi).2 σ x hx)
    · exact le_rfl
  have hrow (σ : Ω) (x : V) (hx : X σ x) :
      (∑ y ∈ S σ, |D σ x y| ^ 4) ≤
        128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
          C ^ 4 * |Tail σ x| ^ 4) +
        ∑ y ∈ S σ, |if F σ x then D σ x y else 0| ^ 4 := by
    have hb0 : 0 ≤ 128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
        C ^ 4 * |Tail σ x| ^ 4) := by positivity
    by_cases hf : F σ x
    · simp only [hf, ↓reduceIte]
      linarith
    · have hlocal : ∀ y ∈ S σ, |D σ x y| ≤
          A * Pre σ x + C * No σ x + C * Tail σ x :=
        hbound (S σ) n (Δ σ x) (a σ x) (truth σ x) K m (fun j => heavy j σ x)
          hK (ha σ x hx) (fun y hy => hfirst σ x y hx (mem_filter.mp hy).2)
          (fun y hy => hsecond σ x y hx (mem_filter.mp hy).2) hcapacity
          (fun i => ε i σ x) (fun i hi => hε i hi σ x hx)
          (fun i hi y hy => herr i hi σ x y hx (mem_filter.mp hy).2)
          (εfinal σ x) (hεfinal σ x hx)
          (fun y hy => herrfinal σ x y hx (mem_filter.mp hy).2) hf
      have hs := kind.sum_stateRootError_pow_four_le_of_bound hθ (S σ) hK
        (actual σ x) ⟨0, truth σ x⟩ hlocal
      have hp := add_add_pow_four_le (mul_nonneg hA (hpre0 σ x hx))
        (mul_nonneg hC (hno0 σ x hx)) (mul_nonneg hC (htail0 σ x hx))
      have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * (K : ℝ) by positivity)
      simp only [abs_of_nonneg (hpre0 σ x hx), abs_of_nonneg (hno0 σ x hx),
        abs_of_nonneg (htail0 σ x hx), hf, ↓reduceIte, abs_zero,
        zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero, add_zero]
      exact hs.trans (by nlinarith only [hh])
  have hintegrated : rowNormPow 4 N u X Y D ≤
      128 * (K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
        C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
      rowNormPow 4 N u X Y (fun σ x y => if F σ x then D σ x y else 0) := by
    unfold rowNormPow vertexNormPow
    calc
      _ ≤ (N * u)⁻¹ * 𝔼 σ, ∑ x ∈ ({x | X σ x} : Finset V),
          (128 * (K : ℝ) * (A ^ 4 * |Pre σ x| ^ 4 + C ^ 4 * |No σ x| ^ 4 +
            C ^ 4 * |Tail σ x| ^ 4) +
            ∑ y ∈ ({y | Y σ y} : Finset V), |if F σ x then D σ x y else 0| ^ 4) := by
        refine mul_le_mul_of_nonneg_left (expect_le_expect fun σ _ => ?_) (inv_nonneg.mpr hNu)
        exact sum_le_sum fun x hx => hrow σ x (mem_filter.mp hx).2
      _ = _ := by
        simp only [sum_add_distrib, ← mul_sum, expect_add_distrib, ← mul_expect]
        ring
  have hfalse := kind.rowNormPow_falseFirstOverflowBefore_le hθ hη hη1 hNu X Y n K hK m
    (fun i hi => hK.trans_le (hcapacity i hi)) Δ a truth ha hfirst hvanish
  exact hintegrated.trans (add_le_add_right hfalse _)

end Cslib.PolynomialAtomRow
