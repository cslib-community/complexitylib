/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.LinearAlgebra.Matrix.FactorialTruncation

/-!
# The pilot correction with step-dependent multipliers

In the correction-and-copy hierarchy of the OpenAI preprint (2026-09-23), Section 4.2, idea 3 in
issue #474 [OpenAI2026LogSpace], the column multiplier of the cutoff correction is chosen by a
*pilot*: a run of the correction recursion in which the multiplier may decrease from step to
step. At step `i + 1` the pilot forms its input `G = C + Ê_i C`, evaluates a column number
`U G y` on it (in the preprint a detector, see `Complexity.Foundations.Probability.ColumnDetector`),
takes the running maximum `M_(i+1) = M_i ⊔ U G`, and sets
`Ê_(i+1) x y = c (G x y) * γ (M_(i+1) y)` for a base cutoff `c` and a nonincreasing `γ`
(`Matrix.pilotCorrection`, `Matrix.pilotMax`, `Matrix.pilotInput`). The actual correction then
runs the fixed-multiplier recursion `Matrix.cutoffCorrectionIter` with the final multiplier
`γ (M_k y)`.

All bounds of [OpenAI2026LogSpace, Lemma 4.2] hold for any sequence of corrections that starts at
zero and stays between zero and its input, `0 ≤ F (i + 1) ≤ C + F i C`
(`Matrix.IsCorrectionSeq`). Both the pilot (`Matrix.isCorrectionSeq_pilotCorrection`) and the
fixed-multiplier recursion (`Matrix.isCorrectionSeq_cutoffCorrectionIter`) are of this form. For
a substochastic `C` with entries at most `f`, the `i`-th correction and the input of step `i + 1`
have row sums at most `i` and `i + 1` and entries at most `i f` and `(i + 1) f`; they are
supported within any cover of the support of `C`, and strictly upper triangular when `C` is.
Since the running maximum only grows and `γ` is nonincreasing, the actual correction and its inputs
are bounded by those of the pilot (`Matrix.cutoffCorrectionIter_le_pilotCorrection`).

## Main definitions

* `Matrix.IsCorrectionSeq`: corrections starting at zero and dominated by their inputs.
* `Matrix.pilotCorrection`, `Matrix.pilotMax`, `Matrix.pilotInput`: the pilot.

## Main results

* `Matrix.IsCorrectionSeq.sum_le`, `Matrix.IsCorrectionSeq.sum_input_le`,
  `Matrix.IsCorrectionSeq.le_mul`, `Matrix.IsCorrectionSeq.input_le_mul`: row-sum and entry
  bounds.
* `Matrix.IsCorrectionSeq.mem`, `Matrix.IsCorrectionSeq.input_mem`: supports.
* `Matrix.IsCorrectionSeq.isStrictUpperTriangular`,
  `Matrix.IsCorrectionSeq.input_isStrictUpperTriangular`: strict forwardness.
* `Matrix.isCorrectionSeq_cutoffCorrectionIter`, `Matrix.isCorrectionSeq_pilotCorrection`: the
  actual correction and the pilot are correction sequences.
* `Matrix.cutoffCorrectionIter_le_of_isCorrectionSeq`: comparison with a dominating sequence.
* `Matrix.pilotMax_mono`, `Matrix.exists_lt_pilotInput_of_lt_pilotMax`: the running maximum.
* `Matrix.cutoffCorrectionIter_le_pilotCorrection`: the actual correction is at most the pilot.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 4.2 and Lemma 4.2 (preprint, not peer reviewed)
-/

public section

open Finset

namespace Matrix

variable {V : Type*} [Fintype V] {F : ℕ → Matrix V V ℝ} {f : ℝ}

/-- `F` is a **correction sequence** for `C`: it starts at zero, and each correction lies between
zero and its input, `0 ≤ F (i + 1) ≤ C + F i * C` entrywise. The pilot of the preprint, with
step-dependent multipliers, and the actual correction, with a fixed multiplier, are both of this
form [OpenAI2026LogSpace, Lemma 4.2]. -/
structure IsCorrectionSeq (C : Matrix V V ℝ) (F : ℕ → Matrix V V ℝ) : Prop where
  zero : F 0 = 0
  nonneg_succ : ∀ i x y, 0 ≤ F (i + 1) x y
  le_input : ∀ i x y, F (i + 1) x y ≤ (C + F i * C) x y

section Sequence

variable {C : Matrix V V ℝ}

namespace IsCorrectionSeq

variable (hF : IsCorrectionSeq C F)
include hF

theorem nonneg (i : ℕ) (x y : V) : 0 ≤ F i x y := by
  cases i with
  | zero => simp [hF.zero]
  | succ i => exact hF.nonneg_succ i x y

theorem input_nonneg (hC0 : ∀ x y, 0 ≤ C x y) (i : ℕ) (x y : V) : 0 ≤ (C + F i * C) x y :=
  add_nonneg (hC0 x y) (sum_nonneg fun z _ => mul_nonneg (hF.nonneg i x z) (hC0 z y))

/-- **Row sums of the corrections**: the `i`-th correction of a substochastic `C` has row sums at
most `i`, and the input of step `i + 1` at most `i + 1` [OpenAI2026LogSpace, Lemma 4.2]. -/
theorem sum_input_le (hC1 : C *ᵥ 1 ≤ 1) :
    ∀ i x, ∑ y, (C + F i * C) x y ≤ i + 1 ∧ ∑ y, F i x y ≤ i := by
  have hrow : ∀ z, ∑ y, C z y ≤ 1 := fun z => by simpa [mulVec, dotProduct] using hC1 z
  have hinput : ∀ i x, ∑ y, F i x y ≤ i → ∑ y, (C + F i * C) x y ≤ i + 1 := fun i x hi => by
    calc ∑ y, (C + F i * C) x y = ∑ y, C x y + ∑ z, F i x z * ∑ y, C z y := by
          simp only [Matrix.add_apply, Matrix.mul_apply, sum_add_distrib, mul_sum]
          rw [sum_comm]
      _ ≤ 1 + ∑ z, F i x z * 1 := add_le_add (hrow x) (sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (hrow z) (hF.nonneg i x z))
      _ ≤ i + 1 := by simp only [mul_one]; linarith
  intro i
  induction i with
  | zero => intro x; simpa [hF.zero] using hinput 0 x (by simp [hF.zero])
  | succ i ih =>
    intro x
    have hsum : ∑ y, F (i + 1) x y ≤ (i + 1 : ℕ) := by
      push_cast
      exact (sum_le_sum fun y _ => hF.le_input i x y).trans (ih x).1
    exact ⟨hinput _ x hsum, hsum⟩

theorem sum_le (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ) (x : V) : ∑ y, F i x y ≤ i :=
  (hF.sum_input_le hC1 i x).2

/-- **Entries of the inputs**: the input of step `i + 1` has entries at most `(i + 1) f`
[OpenAI2026LogSpace, Lemma 4.2]. -/
theorem input_le_mul (hCf : ∀ x y, C x y ≤ f) (hf : 0 ≤ f) (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ)
    (x y : V) : (C + F i * C) x y ≤ (i + 1) * f := by
  have hsum := hF.sum_le hC1 i x
  calc (C + F i * C) x y = C x y + ∑ z, F i x z * C z y := rfl
    _ ≤ f + ∑ z, F i x z * f := add_le_add (hCf x y)
        (sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hCf z y) (hF.nonneg i x z))
    _ ≤ (i + 1) * f := by rw [← sum_mul]; nlinarith

/-- **Entries of the corrections**: the `i`-th correction has entries at most `i f`
[OpenAI2026LogSpace, Lemma 4.2]. -/
theorem le_mul (hCf : ∀ x y, C x y ≤ f) (hf : 0 ≤ f) (hC1 : C *ᵥ 1 ≤ 1) (i : ℕ) (x y : V) :
    F i x y ≤ i * f := by
  cases i with
  | zero => simp [hF.zero]
  | succ i =>
    push_cast
    exact (hF.le_input i x y).trans (hF.input_le_mul hCf hf hC1 i x y)

variable {A : Finset V}

/-- The corrections and the inputs are supported within any set `A` covering the support of `C`
[OpenAI2026LogSpace, Lemma 4.2]. -/
theorem input_mem_and_mem (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) :
    ∀ i x y, ((C + F i * C) x y ≠ 0 → x ∈ A ∧ y ∈ A) ∧ (F i x y ≠ 0 → x ∈ A ∧ y ∈ A) := by
  have hinput : ∀ i, (∀ x y, F i x y ≠ 0 → x ∈ A ∧ y ∈ A) →
      ∀ x y, (C + F i * C) x y ≠ 0 → x ∈ A ∧ y ∈ A := fun i hi x y h => by
    by_contra hxy
    apply h
    have hCxy : C x y = 0 := by by_contra h'; exact hxy (hA x y h')
    simp only [Matrix.add_apply, Matrix.mul_apply, hCxy, zero_add]
    refine sum_eq_zero fun z _ => ?_
    by_cases hE : F i x z = 0
    · rw [hE, zero_mul]
    by_cases hCz : C z y = 0
    · rw [hCz, mul_zero]
    exact absurd ⟨(hi x z hE).1, (hA z y hCz).2⟩ hxy
  intro i
  induction i with
  | zero =>
    have h0 : ∀ x y, F 0 x y ≠ 0 → x ∈ A ∧ y ∈ A := fun x y h => by simp [hF.zero] at h
    exact fun x y => ⟨hinput 0 h0 x y, h0 x y⟩
  | succ i ih =>
    have hi : ∀ x y, F (i + 1) x y ≠ 0 → x ∈ A ∧ y ∈ A := fun x y h =>
      (ih x y).1 fun h' => h (le_antisymm (h' ▸ hF.le_input i x y) (hF.nonneg_succ i x y))
    exact fun x y => ⟨hinput _ hi x y, hi x y⟩

theorem mem (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) (i : ℕ) (x y : V) (h : F i x y ≠ 0) :
    x ∈ A ∧ y ∈ A :=
  (hF.input_mem_and_mem hA i x y).2 h

theorem input_mem (hA : ∀ x y, C x y ≠ 0 → x ∈ A ∧ y ∈ A) (i : ℕ) (x y : V)
    (h : (C + F i * C) x y ≠ 0) : x ∈ A ∧ y ∈ A :=
  (hF.input_mem_and_mem hA i x y).1 h

/-- The corrections of a strictly upper triangular `C` are strictly upper triangular
[OpenAI2026LogSpace, Lemma 4.2]. -/
theorem isStrictUpperTriangular [Preorder V] (hC : C.IsStrictUpperTriangular) (i : ℕ) :
    (F i).IsStrictUpperTriangular := by
  induction i with
  | zero => intro x y _; simp [hF.zero]
  | succ i ih =>
    intro x y hxy
    have h := hF.le_input i x y
    rw [(hC.add (ih.mul hC)) hxy] at h
    exact le_antisymm h (hF.nonneg_succ i x y)

theorem input_isStrictUpperTriangular [Preorder V] (hC : C.IsStrictUpperTriangular) (i : ℕ) :
    (C + F i * C).IsStrictUpperTriangular :=
  hC.add ((hF.isStrictUpperTriangular hC i).mul hC)

end IsCorrectionSeq

/-- The fixed-multiplier recursion `Matrix.cutoffCorrectionIter` is a correction sequence when
the cutoffs satisfy `0 ≤ φ y t ≤ max (t - θ f) 0` with `0 ≤ θ f`. -/
theorem isCorrectionSeq_cutoffCorrectionIter {φ : V → ℝ → ℝ} {θ : ℝ} (hC0 : ∀ x y, 0 ≤ C x y)
    (hφ0 : ∀ y t, 0 ≤ φ y t) (hφθ : ∀ y t, φ y t ≤ max (t - θ * f) 0) (hθf : 0 ≤ θ * f) :
    IsCorrectionSeq C (cutoffCorrectionIter φ C) where
  zero := rfl
  nonneg_succ i x y := cutoffCorrectionIter_nonneg hφ0 (i + 1) x y
  le_input i x y := by
    rw [cutoffCorrectionIter_succ]
    refine (hφθ y _).trans (max_le (by linarith) ?_)
    exact add_nonneg (hC0 x y) (sum_nonneg fun z _ =>
      mul_nonneg (cutoffCorrectionIter_nonneg hφ0 i x z) (hC0 z y))

/-- **Comparison with a dominating sequence**: if the cutoffs `φ y` are monotone and the first
`k` steps of `F` dominate the cutoffs of their own inputs, then the first `k` iterates of the
fixed-multiplier recursion, and their inputs, are at most those of `F`
[OpenAI2026LogSpace, Lemma 4.2]. -/
theorem cutoffCorrectionIter_le_of_isCorrectionSeq {φ : V → ℝ → ℝ} (hC0 : ∀ x y, 0 ≤ C x y)
    (hφm : ∀ y, Monotone (φ y)) {k : ℕ}
    (hφF : ∀ i < k, ∀ x y, φ y ((C + F i * C) x y) ≤ F (i + 1) x y) (hF : IsCorrectionSeq C F) :
    ∀ i ≤ k, ∀ x y, cutoffCorrectionIter φ C i x y ≤ F i x y ∧
      (C + cutoffCorrectionIter φ C i * C) x y ≤ (C + F i * C) x y := by
  have hinput : ∀ i, (∀ x y, cutoffCorrectionIter φ C i x y ≤ F i x y) →
      ∀ x y, (C + cutoffCorrectionIter φ C i * C) x y ≤ (C + F i * C) x y :=
    fun i hi x y => add_le_add_right (sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_right (hi x z) (hC0 z y)) _
  intro i
  induction i with
  | zero =>
    have h0 : ∀ x y, cutoffCorrectionIter φ C 0 x y ≤ F 0 x y := fun x y => by
      simp [cutoffCorrectionIter, hF.zero]
    exact fun _ x y => ⟨h0 x y, hinput 0 h0 x y⟩
  | succ i ih =>
    intro hik
    have hi : ∀ x y, cutoffCorrectionIter φ C (i + 1) x y ≤ F (i + 1) x y := fun x y => by
      rw [cutoffCorrectionIter_succ]
      exact (hφm y ((ih (by omega) x y).2)).trans (hφF i (by omega) x y)
    exact fun x y => ⟨hi x y, hinput _ hi x y⟩

end Sequence

/-! ### The pilot -/

section Pilot

variable (c γ : ℝ → ℝ) (U : Matrix V V ℝ → V → ℝ) (C : Matrix V V ℝ)

/-- The **pilot** as a pair of the current correction and the running maximum of the column
numbers. Step `i + 1` forms the input `G = C + Ê_i C`, updates the running maximum to
`M_(i+1) = M_i ⊔ U G`, and sets `Ê_(i+1) x y = c (G x y) * γ (M_(i+1) y)`
[OpenAI2026LogSpace, (4.10)–(4.13)]. -/
noncomputable def pilot : ℕ → Matrix V V ℝ × (V → ℝ)
  | 0 => (0, 0)
  | i + 1 =>
    let G := C + (pilot i).1 * C
    let M := (pilot i).2 ⊔ U G
    (of fun x y => c (G x y) * γ (M y), M)

/-- The `i`-th pilot correction `Ê_i`. -/
noncomputable def pilotCorrection (i : ℕ) : Matrix V V ℝ := (pilot c γ U C i).1

/-- The input `G = C + Ê_i C` of pilot step `i + 1`; the preprint's `G_(i+1)`. -/
@[expose] noncomputable def pilotInput (i : ℕ) : Matrix V V ℝ := C + pilotCorrection c γ U C i * C

/-- The running maximum `M_i = max (0, U G_1, …, U G_i)` of the column numbers after `i` pilot
steps. The pilot multiplier of step `i` is `γ (M_i y)`. -/
noncomputable def pilotMax (i : ℕ) : V → ℝ := (pilot c γ U C i).2

variable {c γ U C}

@[simp] theorem pilotCorrection_zero : pilotCorrection c γ U C 0 = 0 := by rfl

@[simp] theorem pilotMax_zero : pilotMax c γ U C 0 = 0 := by rfl

theorem pilotMax_succ (i : ℕ) :
    pilotMax c γ U C (i + 1) = pilotMax c γ U C i ⊔ U (pilotInput c γ U C i) := by rfl

theorem pilotCorrection_succ_apply (i : ℕ) (x y : V) :
    pilotCorrection c γ U C (i + 1) x y =
      c (pilotInput c γ U C i x y) * γ (pilotMax c γ U C (i + 1) y) := by rfl

/-- The running maximum grows. -/
theorem pilotMax_mono {i j : ℕ} (hij : i ≤ j) (y : V) :
    pilotMax c γ U C i y ≤ pilotMax c γ U C j y := by
  induction hij with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (by rw [pilotMax_succ]; exact le_sup_left)

/-- If the running maximum after `k` steps exceeds `a ≥ 0`, some column number `U G_(i+1)`,
`i < k`, does. -/
theorem exists_lt_pilotInput_of_lt_pilotMax {a : ℝ} (ha : 0 ≤ a) {k : ℕ} {y : V}
    (h : a < pilotMax c γ U C k y) : ∃ i < k, a < U (pilotInput c γ U C i) y := by
  induction k with
  | zero => exact absurd h (not_lt.mpr ha)
  | succ k ih =>
    rw [pilotMax_succ, Pi.sup_apply, lt_sup_iff] at h
    rcases h with h | h
    · obtain ⟨i, hi, hU⟩ := ih h
      exact ⟨i, by omega, hU⟩
    · exact ⟨k, by omega, h⟩

/-- **The pilot is a correction sequence** when the base cutoff satisfies `0 ≤ c t ≤ t` for
`t ≥ 0` and the multipliers lie in `[0, 1]` [OpenAI2026LogSpace, Lemma 4.2]. -/
theorem isCorrectionSeq_pilotCorrection (hC0 : ∀ x y, 0 ≤ C x y) (hc0 : ∀ t, 0 ≤ c t)
    (hct : ∀ t, 0 ≤ t → c t ≤ t) (hγ0 : ∀ t, 0 ≤ γ t) (hγ1 : ∀ t, γ t ≤ 1) :
    IsCorrectionSeq C (pilotCorrection c γ U C) := by
  have hnonneg : ∀ i x y, 0 ≤ pilotCorrection c γ U C (i + 1) x y := fun i x y => by
    rw [pilotCorrection_succ_apply]; exact mul_nonneg (hc0 _) (hγ0 _)
  have hall : ∀ i x y, 0 ≤ pilotCorrection c γ U C i x y := fun i x y => by
    cases i with
    | zero => simp
    | succ i => exact hnonneg i x y
  refine ⟨rfl, hnonneg, fun i x y => ?_⟩
  rw [pilotCorrection_succ_apply]
  have hG : 0 ≤ pilotInput c γ U C i x y :=
    add_nonneg (hC0 x y) (sum_nonneg fun z _ => mul_nonneg (hall i x z) (hC0 z y))
  exact (mul_le_of_le_one_right (hc0 _) (hγ1 _)).trans (hct _ hG)

/-- **The actual correction is at most the pilot.** Run the fixed-multiplier recursion with the
cutoffs `φ y t = c t * γ (M_k y)`, the final pilot multiplier. For a monotone nonnegative `c` and
a nonincreasing `γ`, its first `k` iterates and their inputs are at most the pilot corrections and
pilot inputs [OpenAI2026LogSpace, Lemma 4.2]. -/
theorem cutoffCorrectionIter_le_pilotCorrection (hC0 : ∀ x y, 0 ≤ C x y) (hc0 : ∀ t, 0 ≤ c t)
    (hct : ∀ t, 0 ≤ t → c t ≤ t) (hcm : Monotone c) (hγ0 : ∀ t, 0 ≤ γ t) (hγ1 : ∀ t, γ t ≤ 1)
    (hγm : Antitone γ) {k i : ℕ} (hik : i ≤ k) (x y : V) :
    cutoffCorrectionIter (fun y t => c t * γ (pilotMax c γ U C k y)) C i x y ≤
        pilotCorrection c γ U C i x y ∧
      (C + cutoffCorrectionIter (fun y t => c t * γ (pilotMax c γ U C k y)) C i * C) x y ≤
        pilotInput c γ U C i x y := by
  refine cutoffCorrectionIter_le_of_isCorrectionSeq hC0
    (fun y => hcm.mul_const (hγ0 _)) (fun j hj x y => ?_)
    (isCorrectionSeq_pilotCorrection hC0 hc0 hct hγ0 hγ1) i hik x y
  rw [pilotCorrection_succ_apply]
  exact mul_le_mul_of_nonneg_left (hγm (pilotMax_mono (by omega) y)) (hc0 _)

end Pilot

end Matrix
