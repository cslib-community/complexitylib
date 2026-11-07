/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Privacy.DifferentialPrivacy.Composition
public import Complexity.Privacy.DifferentialPrivacy.DiscreteLaplace

/-!
# AboveThreshold and the sparse vector technique with discrete Laplace noise

AboveThreshold [DworkRoth2014, Algorithm 1] answers a stream of sensitivity-`Δ` queries
`f₁, f₂, …` against a public threshold `T`. It draws a noisy threshold `T̂ = T + ρ` once, then for
each query draws fresh noise `νᵢ` and halts at the first `i` with `fᵢ(D) + νᵢ ≥ T̂`, reporting
`⊤` there and `⊥` before. Its privacy cost does not grow with the number of queries
[DworkRoth2014, Theorem 3.23].

Here the noise is integer-valued: with the discrete Laplace distribution
[CanonneKamathSteinke2020, Definition 28] of scales `2 Δ / ε` and `4 Δ / ε` in place of Dwork and
Roth's continuous `Lap (2 / ε)` and `Lap (4 / ε)`, AboveThreshold is `(ε, 0)`-differentially
private for integer `Δ ≥ 1` (`differentiallyPrivate_aboveThreshold_discreteLaplace`), and it is
`α`-accurate except with probability `β` for `α = 8 (ln (k + 1) + ln (2 / β)) / ε` on `k`
queries (`aboveThreshold_discreteLaplace_toOuterMeasure_not_thresholdAccurate_le`); these are the
discrete-noise analogues of [DworkRoth2014, Theorem 3.23] and [DworkRoth2014, Theorem 3.24]
(`k + 1` replaces Dwork and Roth's `k` because the discrete tails carry a factor `2`). The
queries and threshold are real-valued; only the noise is discrete. The privacy proof follows
Dwork and Roth's change of variables, with the shift of the noisy threshold by an integer `Δ`.

The output is the index of the first reported `⊤` (`some i`), or `none` when no query is reported;
this is equivalent to Dwork and Roth's stream `⊥ ⋯ ⊥ ⊤`. Because the stream of answers before
halting is always `⊥ ⋯ ⊥`, an analyst choosing the next query adaptively from the answers so far
fixes the queries in advance, so a fixed list of queries loses no generality.

Sparse [DworkRoth2014, Algorithm 2] restarts AboveThreshold on the remaining stream after each
reported `⊤`, `c` times. It is `c`-fold adaptive composition of AboveThreshold (`sparse`), so
discrete Laplace noise of scales `2 c Δ / ε` and `4 c Δ / ε` makes it `(ε, 0)`-private
(`differentiallyPrivate_sparse_discreteLaplace`), the `δ = 0` case of [DworkRoth2014,
Theorem 3.25].

## Main definitions

* `Cslib.Privacy.aboveThreshold`: AboveThreshold on a list of query answers with threshold noise
  `ρ` and query noise `ν`.
* `Cslib.Privacy.aboveThresholdMechanism`: AboveThreshold as a mechanism on datasets.
* `Cslib.Privacy.ThresholdAccurate`: the accuracy condition [DworkRoth2014, Definition 3.9].
* `Cslib.Privacy.sparse`: Sparse as `c`-fold adaptive composition of AboveThreshold.

## Main results

* `Cslib.Privacy.DifferentiallyPrivate.aboveThresholdMechanism`: privacy for any noise whose
  masses change by bounded factors under integer shifts.
* `Cslib.Privacy.differentiallyPrivate_aboveThreshold_discreteLaplace`: `(ε, 0)`-privacy.
* `Cslib.Privacy.aboveThreshold_discreteLaplace_toOuterMeasure_not_thresholdAccurate_le`:
  accuracy.
* `Cslib.Privacy.differentiallyPrivate_sparse_discreteLaplace`: `(ε, 0)`-privacy of Sparse.

## References

* [CanonneKamathSteinke2020]
* [DworkRoth2014]
-/

open scoped ENNReal

public section

namespace Cslib.Privacy

private theorem PMF.map_apply_le_mul {α β : Type*} {p q : PMF α} {c : ℝ≥0∞}
    (h : ∀ a, p a ≤ c * q a) (f : α → β) (b : β) : p.map f b ≤ c * q.map f b := by
  classical
  rw [PMF.map_apply, PMF.map_apply, ← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun a => ?_
  split_ifs
  · exact h a
  · simp

private theorem PMF.tsum_mul_indicator_one {α : Type*} (p : PMF α) (S : Set α) :
    ∑' a, p a * S.indicator 1 a = p.toOuterMeasure S := by
  classical
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ S <;> simp [ha]

/-- AboveThreshold against a fixed noisy threshold `T̂`: draw `ν` for the first answer `a`,
report index `0` if `a + ν ≥ T̂`, and otherwise continue with the remaining answers. -/
noncomputable def aboveThresholdAux (ν : PMF ℤ) (T : ℝ) : List ℝ → PMF (Option ℕ)
  | [] => PMF.pure none
  | a :: as => ν.bind fun v =>
      if T ≤ a + v then PMF.pure (some 0) else (aboveThresholdAux ν T as).map (Option.map Nat.succ)

/-- AboveThreshold [DworkRoth2014, Algorithm 1] on the list of query answers `as` with public
threshold `T`: draw `ρ` once, compare each noisy answer `a + ν` with `T + ρ`, and return the index
of the first answer reported above threshold, or `none`. -/
noncomputable def aboveThreshold (ρ ν : PMF ℤ) (T : ℝ) (as : List ℝ) : PMF (Option ℕ) :=
  ρ.bind fun r => aboveThresholdAux ν (T + r) as

/-- AboveThreshold as a mechanism: on dataset `x` it runs on the answers `f x` of the queries
`fs`. -/
noncomputable def aboveThresholdMechanism {D : Type*} (ρ ν : PMF ℤ) (T : ℝ) (fs : List (D → ℝ))
    (x : D) : PMF (Option ℕ) :=
  aboveThreshold ρ ν T (fs.map fun f => f x)

/-- The change of variables in [DworkRoth2014, Theorem 3.23], for a fixed noisy threshold: if each
answer in `bs` is at least the corresponding answer in `as` minus `s`, and shifting the query noise
by `2 s` changes its masses by at most `c ≥ 1`, then raising the threshold by `s` changes each
output probability by at most `c`. -/
theorem aboveThresholdAux_apply_le {ν : PMF ℤ} {c : ℝ≥0∞} {s : ℤ} (hc : 1 ≤ c)
    (hν : ∀ v, ν v ≤ c * ν (v + 2 * s)) {as bs : List ℝ}
    (hab : List.Forall₂ (fun a b : ℝ => a - s ≤ b ∧ b ≤ a + s) as bs) (T : ℝ) (o : Option ℕ) :
    aboveThresholdAux ν T as o ≤ c * aboveThresholdAux ν (T + s) bs o := by
  induction hab generalizing o with
  | nil =>
    calc aboveThresholdAux ν T [] o = 1 * aboveThresholdAux ν (T + s) [] o := by
          rw [one_mul]; rfl
      _ ≤ c * aboveThresholdAux ν (T + s) [] o := by gcongr
  | @cons a b as bs hab' _ ih =>
    classical
    have hsplit (U x : ℝ) (l : List ℝ) (v : ℤ) :
        (if U ≤ x + v then PMF.pure (some 0) else
          (aboveThresholdAux ν U l).map (Option.map Nat.succ)) o =
        (if U ≤ x + v then PMF.pure (some 0) o else 0) +
          (if U ≤ x + v then 0 else (aboveThresholdAux ν U l).map (Option.map Nat.succ) o) := by
      split_ifs <;> simp
    simp only [aboveThresholdAux, PMF.bind_apply, hsplit, mul_add]
    rw [tsum_add, tsum_add, mul_add]
    gcongr ?_ + ?_
    · conv_rhs => rw [← (Equiv.addRight (2 * s)).tsum_eq]
      rw [← ENNReal.tsum_mul_left]
      refine tsum_le_tsum fun v => ?_
      simp only [Equiv.coe_addRight]
      by_cases hv : T ≤ a + v
      · have hv' : T + s ≤ b + ((v + 2 * s : ℤ) : ℝ) := by
          push_cast
          linarith [hab'.1]
        simp only [hv, hv', ↓reduceIte]
        calc ν v * PMF.pure (some 0) o ≤ (c * ν (v + 2 * s)) * PMF.pure (some 0) o := by
              gcongr; exact hν v
          _ = c * (ν (v + 2 * s) * PMF.pure (some 0) o) := by ring
      · simp [hv]
    · rw [← ENNReal.tsum_mul_left]
      refine tsum_le_tsum fun v => ?_
      by_cases hv : T ≤ a + v
      · simp [hv]
      · have hv' : ¬ T + s ≤ b + v := by
          intro h
          linarith [hab'.2]
        simp only [hv, hv', ↓reduceIte]
        calc ν v * (aboveThresholdAux ν T as).map (Option.map Nat.succ) o
            ≤ ν v * (c * (aboveThresholdAux ν (T + s) bs).map (Option.map Nat.succ) o) := by
              gcongr; exact PMF.map_apply_le_mul ih _ o
          _ = c * (ν v * (aboveThresholdAux ν (T + s) bs).map (Option.map Nat.succ) o) := by ring

/-- AboveThreshold is `(ε₁ + ε₂, 0)`-differentially private for queries of sensitivity `s`
whenever shifting the threshold noise by `s` changes its masses by at most `exp ε₁` and shifting
the query noise by `2 s` changes them by at most `exp ε₂` [DworkRoth2014, Theorem 3.23]. -/
theorem DifferentiallyPrivate.aboveThresholdMechanism {D : Type*} {Adj : D → D → Prop}
    {ρ ν : PMF ℤ} {T : ℝ} {fs : List (D → ℝ)} {s : ℤ} {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂)
    (hfs : ∀ f ∈ fs, ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ s)
    (hρ : ∀ r, ρ r ≤ ENNReal.ofReal (Real.exp ε₁) * ρ (r + s))
    (hν : ∀ v, ν v ≤ ENNReal.ofReal (Real.exp ε₂) * ν (v + 2 * s)) :
    DifferentiallyPrivate Adj (Privacy.aboveThresholdMechanism ρ ν T fs) (ε₁ + ε₂) 0 := by
  refine DifferentiallyPrivate.of_apply_le fun x y hxy o => ?_
  have hc : 1 ≤ ENNReal.ofReal (Real.exp ε₂) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp hε₂)
  have hab : List.Forall₂ (fun a b : ℝ => a - s ≤ b ∧ b ≤ a + s) (fs.map fun f => f x)
      (fs.map fun f => f y) := by
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
    intro f hf
    have := abs_le.mp (hfs f hf hxy)
    constructor <;> linarith [this.1, this.2]
  simp only [Privacy.aboveThresholdMechanism, aboveThreshold, PMF.bind_apply]
  rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  conv_rhs => rw [← (Equiv.addRight s).tsum_eq]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_le_tsum fun r => ?_
  simp only [Equiv.coe_addRight]
  have haux := aboveThresholdAux_apply_le hc hν hab (T + r) o
  have hT : T + ((r + s : ℤ) : ℝ) = T + r + s := by push_cast; ring
  rw [hT]
  calc ρ r * aboveThresholdAux ν (T + r) (fs.map fun f => f x) o
      ≤ (ENNReal.ofReal (Real.exp ε₁) * ρ (r + s)) *
          (ENNReal.ofReal (Real.exp ε₂) * aboveThresholdAux ν (T + r + s)
            (fs.map fun f => f y) o) := by
        exact mul_le_mul' (hρ r) haux
    _ = ENNReal.ofReal (Real.exp ε₁) * ENNReal.ofReal (Real.exp ε₂) *
          (ρ (r + s) * aboveThresholdAux ν (T + r + s) (fs.map fun f => f y) o) := by ring

/-- AboveThreshold with discrete Laplace noise: for queries of sensitivity `Δ ≥ 1` (an integer),
threshold noise of scale `2 Δ / ε` and query noise of scale `4 Δ / ε` give `(ε, 0)`-differential
privacy, however many queries are asked. This is the discrete-noise analogue of
[DworkRoth2014, Theorem 3.23]. -/
theorem differentiallyPrivate_aboveThreshold_discreteLaplace {D : Type*} {Adj : D → D → Prop}
    {T : ℝ} {fs : List (D → ℝ)} {Δ : ℕ} (hΔ : 0 < Δ)
    (hfs : ∀ f ∈ fs, ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ Δ) {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate Adj
      (aboveThresholdMechanism (discreteLaplace (2 * Δ / ε) (by positivity))
        (discreteLaplace (4 * Δ / ε) (by positivity)) T fs) ε 0 := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have h₁ : (Δ : ℝ) / (2 * Δ / ε) = ε / 2 := by field_simp
  have h₂ : (2 * Δ : ℝ) / (4 * Δ / ε) = ε / 2 := by field_simp; ring
  have := DifferentiallyPrivate.aboveThresholdMechanism (Adj := Adj) (T := T) (fs := fs)
    (s := Δ) (ε₁ := ε / 2) (ε₂ := ε / 2) (by positivity) (by exact_mod_cast hfs)
    (fun r => by
      have := discreteLaplace_apply_le (2 * Δ / ε) (by positivity) (Δ := Δ) r Δ (by simp)
      rwa [h₁] at this)
    (fun v => by
      have := discreteLaplace_apply_le (4 * Δ / ε) (by positivity) (Δ := 2 * Δ) v (2 * Δ)
        (by push_cast; rw [abs_of_nonneg (by positivity)])
      rwa [h₂] at this)
  rwa [add_halves] at this

/-- The accuracy condition of [DworkRoth2014, Definition 3.9] for the answers `as`, threshold `T`
and slack `α`: every answer reported below threshold is at most `T + α`, and the answer reported
above threshold, if any, is at least `T - α`. -/
def ThresholdAccurate (T α : ℝ) : List ℝ → Option ℕ → Prop
  | [], _ => True
  | a :: _, some 0 => T - α ≤ a
  | a :: as, some (n + 1) => a ≤ T + α ∧ ThresholdAccurate T α as (some n)
  | a :: as, none => a ≤ T + α ∧ ThresholdAccurate T α as none

/-- An accurate output does not halt early [DworkRoth2014, proof of Theorem 3.24]: if every answer
before the last is below `T - α`, a reported index is the last one. -/
theorem ThresholdAccurate.length_le {T α : ℝ} {as : List ℝ} {i : ℕ}
    (h : ThresholdAccurate T α as (some i)) (has : ∀ j (hj : j + 1 < as.length), as[j] < T - α) :
    as.length ≤ i + 1 := by
  induction as generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [ThresholdAccurate] at h
      by_contra hlt
      have := has 0 (by simp only [List.length_cons] at hlt ⊢; omega)
      simp only [List.getElem_cons_zero] at this
      linarith
    | succ i =>
      simp only [ThresholdAccurate] at h
      have := ih h.2 fun j hj => by
        have := has (j + 1) (by simp only [List.length_cons]; omega)
        simpa using this
      simp only [List.length_cons]
      omega

/-- For a noisy threshold within `α₁` of `T`, AboveThreshold fails to be `(α₁ + α₂)`-accurate with
probability at most `k · Pr[|ν| > α₂]` on `k` answers. -/
theorem aboveThresholdAux_toOuterMeasure_not_thresholdAccurate_le (ν : PMF ℤ) {T r α₁ α₂ : ℝ}
    (hr : |r| ≤ α₁) (as : List ℝ) :
    (aboveThresholdAux ν (T + r) as).toOuterMeasure {o | ¬ ThresholdAccurate T (α₁ + α₂) as o} ≤
      as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
  classical
  induction as with
  | nil =>
    simp [aboveThresholdAux, ThresholdAccurate]
  | cons a as ih =>
    rw [aboveThresholdAux, PMF.toOuterMeasure_bind_apply]
    have hterm (v : ℤ) :
        (if T + r ≤ a + v then PMF.pure (some 0) else
          (aboveThresholdAux ν (T + r) as).map (Option.map Nat.succ)).toOuterMeasure
            {o | ¬ ThresholdAccurate T (α₁ + α₂) (a :: as) o} ≤
          {v : ℤ | α₂ < |(v : ℝ)|}.indicator 1 v +
            as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
      have habs := abs_le.mp hr
      split_ifs with hv
      · rw [PMF.toOuterMeasure_pure_apply]
        split_ifs with hbad
        · simp only [Set.mem_ofPred_eq, ThresholdAccurate, not_le] at hbad
          have hbig : α₂ < |(v : ℝ)| := by
            rw [lt_abs]
            left
            linarith [habs.1, habs.2]
          rw [Set.indicator_of_mem (by exact hbig)]
          exact le_self_add
        · exact zero_le
      · by_cases ha : a ≤ T + (α₁ + α₂)
        · rw [PMF.toOuterMeasure_map_apply]
          refine le_trans (MeasureTheory.measure_mono fun o ho => ?_) (ih.trans le_add_self)
          simp only [Set.mem_preimage, Set.mem_ofPred_eq] at ho ⊢
          intro hacc
          apply ho
          cases o with
          | none => exact ⟨ha, hacc⟩
          | some n => exact ⟨ha, hacc⟩
        · have hbig : α₂ < |(v : ℝ)| := by
            rw [lt_abs]
            right
            linarith [habs.1, habs.2]
          rw [Set.indicator_of_mem (by exact hbig)]
          exact (Probability.PMF.toOuterMeasure_le_one _ _).trans le_self_add
    calc ∑' v, ν v * (if T + r ≤ a + v then PMF.pure (some 0) else
          (aboveThresholdAux ν (T + r) as).map (Option.map Nat.succ)).toOuterMeasure
            {o | ¬ ThresholdAccurate T (α₁ + α₂) (a :: as) o}
        ≤ ∑' v, ν v * ({v : ℤ | α₂ < |(v : ℝ)|}.indicator 1 v +
            as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|}) :=
          tsum_le_tsum fun v => by gcongr; exact hterm v
      _ = ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} +
            as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
          simp only [mul_add]
          rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.tsum_mul_indicator_one]
      _ = (a :: as).length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
          rw [List.length_cons, Nat.cast_succ, add_mul, one_mul, add_comm]

/-- AboveThreshold on `k` answers fails to be `(α₁ + α₂)`-accurate with probability at most
`Pr[|ρ| > α₁] + k · Pr[|ν| > α₂]` [DworkRoth2014, proof of Theorem 3.24]. -/
theorem aboveThreshold_toOuterMeasure_not_thresholdAccurate_le (ρ ν : PMF ℤ) (T : ℝ)
    {α₁ α₂ : ℝ} (as : List ℝ) :
    (aboveThreshold ρ ν T as).toOuterMeasure {o | ¬ ThresholdAccurate T (α₁ + α₂) as o} ≤
      ρ.toOuterMeasure {r | α₁ < |(r : ℝ)|} +
        as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
  classical
  rw [aboveThreshold, PMF.toOuterMeasure_bind_apply]
  have hterm (r : ℤ) :
      (aboveThresholdAux ν (T + r) as).toOuterMeasure
          {o | ¬ ThresholdAccurate T (α₁ + α₂) as o} ≤
        {r : ℤ | α₁ < |(r : ℝ)|}.indicator 1 r +
          as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
    by_cases hr : α₁ < |(r : ℝ)|
    · rw [Set.indicator_of_mem (by exact hr)]
      exact (Probability.PMF.toOuterMeasure_le_one _ _).trans le_self_add
    · exact (aboveThresholdAux_toOuterMeasure_not_thresholdAccurate_le ν (not_lt.mp hr) as).trans
        le_add_self
  calc ∑' r, ρ r * (aboveThresholdAux ν (T + r) as).toOuterMeasure
        {o | ¬ ThresholdAccurate T (α₁ + α₂) as o}
      ≤ ∑' r, ρ r * ({r : ℤ | α₁ < |(r : ℝ)|}.indicator 1 r +
          as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|}) :=
        tsum_le_tsum fun r => by gcongr; exact hterm r
    _ = ρ.toOuterMeasure {r | α₁ < |(r : ℝ)|} +
          as.length * ν.toOuterMeasure {v | α₂ < |(v : ℝ)|} := by
        simp only [mul_add]
        rw [tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          PMF.tsum_mul_indicator_one]

/-- Accuracy of AboveThreshold with discrete Laplace noise (scales `2 / ε` and `4 / ε`): on `k`
answers it is `α`-accurate except with probability at most `β`, for
`α = 8 (ln (k + 1) + ln (2 / β)) / ε` and `0 < β ≤ 1`. This is the discrete-noise analogue of
[DworkRoth2014, Theorem 3.24], with `k + 1` in place of `k`. -/
theorem aboveThreshold_discreteLaplace_toOuterMeasure_not_thresholdAccurate_le {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (T : ℝ) (as : List ℝ) :
    (aboveThreshold (discreteLaplace (2 / ε) (by positivity))
        (discreteLaplace (4 / ε) (by positivity)) T as).toOuterMeasure
      {o | ¬ ThresholdAccurate T
        (8 * (Real.log (as.length + 1) + Real.log (2 / β)) / ε) as o} ≤ ENNReal.ofReal β := by
  set k := as.length
  set L := Real.log (k + 1) + Real.log (2 / β) with hL
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hL0 : 0 ≤ L := add_nonneg (Real.log_nonneg (by simp)) (Real.log_nonneg (by
    rw [le_div_iff₀ hβ]; linarith))
  have hsplit : 8 * L / ε = 4 * L / ε + 4 * L / ε := by ring
  rw [hsplit]
  refine (aboveThreshold_toOuterMeasure_not_thresholdAccurate_le _ _ T as).trans ?_
  have h₁ := discreteLaplace_toOuterMeasure_lt_abs_le (2 / ε) (by positivity)
    (a := 4 * L / ε) (by positivity)
  have h₂ := discreteLaplace_toOuterMeasure_lt_abs_le (4 / ε) (by positivity)
    (a := 4 * L / ε) (by positivity)
  have he₁ : -(4 * L / ε) / (2 / ε) = -(2 * L) := by field_simp; ring
  have he₂ : -(4 * L / ε) / (4 / ε) = -L := by field_simp
  rw [he₁] at h₁
  rw [he₂] at h₂
  have hexpL : Real.exp (-L) = β / (2 * (k + 1)) := by
    rw [hL, neg_add, Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hk,
      Real.exp_log (by positivity)]
    field_simp
  have h2L : Real.exp (-(2 * L)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
  calc _ ≤ ENNReal.ofReal (2 * Real.exp (-(2 * L))) +
        (k : ℝ≥0∞) * ENNReal.ofReal (2 * Real.exp (-L)) := by gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-(2 * L)) + k * (2 * Real.exp (-L))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg k), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal β := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc 2 * Real.exp (-(2 * L)) + k * (2 * Real.exp (-L))
            ≤ 2 * Real.exp (-L) + k * (2 * Real.exp (-L)) := by gcongr
          _ = 2 * (k + 1) * Real.exp (-L) := by ring
          _ = β := by rw [hexpL]; field_simp

section Sparse

variable {D : Type*}

/-- The number of queries consumed by a run of AboveThreshold on `n` remaining queries that
returned `o`. -/
def aboveThresholdConsumed (n : ℕ) : Option ℕ → ℕ
  | some i => i + 1
  | none => n

/-- The position in the query stream after the AboveThreshold runs recorded in `history`
(most recent first). -/
def sparseOffset (n : ℕ) : List (Option ℕ) → ℕ
  | [] => 0
  | o :: history => sparseOffset n history + aboveThresholdConsumed (n - sparseOffset n history) o

/-- Sparse [DworkRoth2014, Algorithm 2] with cutoff `c`, as `c`-fold adaptive composition of
AboveThreshold: each round restarts AboveThreshold, with fresh threshold noise, on the queries not
yet consumed. The transcript lists the index reported by each round, most recent first. -/
noncomputable def sparse (ρ ν : PMF ℤ) (T : ℝ) (fs : List (D → ℝ)) (c : ℕ) :
    D → PMF (List (Option ℕ)) :=
  adaptiveComposition
    (fun history => aboveThresholdMechanism ρ ν T (fs.drop (sparseOffset fs.length history))) c

/-- Sparse with cutoff `c` is `(c (ε₁ + ε₂), 0)`-private when each AboveThreshold round is
`(ε₁ + ε₂, 0)`-private, by basic adaptive composition [DworkRoth2014, Theorem 3.25]. -/
theorem DifferentiallyPrivate.sparse {Adj : D → D → Prop} {ρ ν : PMF ℤ} {T : ℝ}
    {fs : List (D → ℝ)} {s : ℤ} {ε₁ ε₂ : ℝ} (hε₂ : 0 ≤ ε₂)
    (hfs : ∀ f ∈ fs, ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ s)
    (hρ : ∀ r, ρ r ≤ ENNReal.ofReal (Real.exp ε₁) * ρ (r + s))
    (hν : ∀ v, ν v ≤ ENNReal.ofReal (Real.exp ε₂) * ν (v + 2 * s)) (c : ℕ) :
    DifferentiallyPrivate Adj (Privacy.sparse ρ ν T fs c) (c * (ε₁ + ε₂)) 0 := by
  have := DifferentiallyPrivate.adaptiveComposition (Adj := Adj)
    (M := fun history =>
      Privacy.aboveThresholdMechanism ρ ν T (fs.drop (sparseOffset fs.length history)))
    (ε := fun _ => ε₁ + ε₂) (δ := fun _ => 0)
    (fun history => DifferentiallyPrivate.aboveThresholdMechanism hε₂
      (fun f hf => hfs f (List.mem_of_mem_drop hf)) hρ hν) c
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const_zero] at this
  exact this

/-- Sparse with cutoff `c ≥ 1` and discrete Laplace noise of scales `2 c Δ / ε` and `4 c Δ / ε` is
`(ε, 0)`-differentially private for queries of sensitivity `Δ ≥ 1`; the `δ = 0` case of
[DworkRoth2014, Theorem 3.25], with discrete noise. -/
theorem differentiallyPrivate_sparse_discreteLaplace {Adj : D → D → Prop} {T : ℝ}
    {fs : List (D → ℝ)} {Δ : ℕ} (hΔ : 0 < Δ)
    (hfs : ∀ f ∈ fs, ∀ ⦃x y⦄, Adj x y → |f x - f y| ≤ Δ) {c : ℕ} (hc : 0 < c) {ε : ℝ}
    (hε : 0 < ε) :
    DifferentiallyPrivate Adj
      (sparse (discreteLaplace (2 * c * Δ / ε) (by positivity))
        (discreteLaplace (4 * c * Δ / ε) (by positivity)) T fs c) ε 0 := by
  have hΔ' : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  have h₁ : (Δ : ℝ) / (2 * c * Δ / ε) = ε / (2 * c) := by field_simp
  have h₂ : (2 * Δ : ℝ) / (4 * c * Δ / ε) = ε / (2 * c) := by field_simp; ring
  have := DifferentiallyPrivate.sparse (Adj := Adj) (T := T) (fs := fs)
    (s := Δ) (ε₁ := ε / (2 * c)) (ε₂ := ε / (2 * c)) (by positivity) (by exact_mod_cast hfs)
    (fun r => by
      have := discreteLaplace_apply_le (2 * c * Δ / ε) (by positivity) (Δ := Δ) r Δ (by simp)
      rwa [h₁] at this)
    (fun v => by
      have := discreteLaplace_apply_le (4 * c * Δ / ε) (by positivity) (Δ := 2 * Δ) v (2 * Δ)
        (by push_cast; rw [abs_of_nonneg (by positivity)])
      rwa [h₂] at this) c
  have hε' : (c : ℝ) * (ε / (2 * c) + ε / (2 * c)) = ε := by field_simp; ring
  rwa [hε'] at this

end Sparse

end Cslib.Privacy
