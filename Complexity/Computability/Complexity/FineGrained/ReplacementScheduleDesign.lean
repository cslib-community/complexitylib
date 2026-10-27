/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.ReplacementParams
public import Complexity.Foundations.Combinatorics.ReplacementDesignBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Instantiating Section 3–4 replacement designs at the concrete Lemma 4.8 parameter schedule

Section 4.7 of `[OpenAI2026ETH]` (Lemma 4.8, equations (4.17)–(4.18), pp. 34–35) chooses the
concrete polylogarithmic parameter schedule `(numGroups n, numNodes n, rowBound β n, auxDim n,
tau n, intervalStart β n)` so that all numerical hypotheses of Lemma 4.7 hold for sufficiently
large `n` and the three-term counting-cost rate
$$
\frac{R}{Q} \log \frac{2Q}{R} + \tau \log(2D + 1) + \frac{1}{r}
$$
is bounded by $O_\beta(\nu^2 / \sqrt{\lambda}) = o(1)$.

This module connects `Cslib.Complexity.SubexponentialSAT.ReplacementParams` with the concrete
algebraic replacement design construction `Cslib.LinearAlgebra.ReplacementDesign` (Lemma 4.7) and
the shared-summary counting design interface `Cslib.ReplacementCounting.Design` (Definition 3.1 and
Proposition 3.4):

1. **Exact rational-to-real alignment of the schedule parameters:**
   - `tauRat n : ℚ := 1 / ((numGroups n : ℚ) * Nat.clog 2 n)` casts to `tau n : ℝ`.
   - When `1 ≤ numGroups n` and `1 ≤ rowBound β n`, the rational binomial tail probability
     `binomTailProb (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n)` casts to
     `binomTail β n : ℝ` (`cast_binomTailProb_eq_binomTail`).
   - `Cslib.ReplacementCounting.threeTermExponent (numGroups n) (numNodes n) (rowBound β n)
     (auxDim n) (tau n)` is definitionally equal to `rowCost β n`
     (`threeTermExponent_eq_rowCost`).

2. **From `Feasible` to concrete and counting replacement designs:**
   - `Feasible.exists_replacementDesign`: any `Feasible β n b w (∑ f, #(scope f))` instance on a
     factor scope family `scope : F → Finset (Fin n)` with `1 ≤ b, w`, per-variable degree `≤ b`,
     per-factor width `≤ w`, and total incidence `∑ f, #(scope f) ≤ b * n` yields a concrete
     `Cslib.LinearAlgebra.ReplacementDesign` at the Lemma 4.8 schedule.
   - `Feasible.toCountingDesign` and `Feasible.domainExaminationBound_le_mul_exp_rowCost`: converts
     any concrete schedule design into a `Cslib.ReplacementCounting.Design` whose Proposition 3.4
     domain-examination count is bounded by
     `2 * numNodes n * numGroups n * exp ((c + 4) * n * rowCost β n)` and hence by the explicit
     `O_β(n * ν² / √λ)` subexponential bound of Lemma 4.8.
   - `exists_schedule_replacementDesign`: combines `exists_feasible` (Lemma 4.8) with
     `Feasible.exists_replacementDesign` (Lemma 4.7) to give the uniform `n₀ ≥ 20` threshold for
     the polylogarithmic regime `1 ≤ b, w ≤ (Nat.clog 2 n) ^ β` and `n ≤ M ≤ b * n`.

## Main definitions

* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.tauRat`: rational step scale
  `1 / (numGroups n * Nat.clog 2 n) : ℚ`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible.toCountingDesign`: canonical
  `Cslib.ReplacementCounting.Design` attached to a concrete schedule `ReplacementDesign`.

## Main results

* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.cast_binomTailProb_eq_binomTail`:
  `((binomTailProb (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n) : ℚ) : ℝ) =
  binomTail β n`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.threeTermExponent_eq_rowCost`:
  `threeTermExponent` at the Lemma 4.8 schedule equals `rowCost β n`.
* `Cslib.Complexity.SubexponentialSAT.ReplacementParams.Feasible.exists_replacementDesign`,
  `Cslib.Complexity.SubexponentialSAT.ReplacementParams. exists_schedule_replacementDesign`:
  end-to-end Lemma 4.7 + Lemma 4.8 + Proposition 3.4 mathematical assembly.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 3.5, Proposition 3.4,
  pp. 25–26; Section 4.6, Lemma 4.7, pp. 33–34; Section 4.7, Lemma 4.8, pp. 34–35.
-/

@[expose] public noncomputable section

namespace Cslib.Complexity.SubexponentialSAT.ReplacementParams

open Finset
open scoped BigOperators
open Cslib.LinearAlgebra Cslib.ReplacementCounting

/-! ### 1. Rational parameter alignment with Lemma 4.7 -/

/-- Rational measurement step scale `τ = 1 / (r λ) ∈ ℚ` of equation (4.17)
([OpenAI2026ETH], p. 34). -/
def tauRat (n : ℕ) : ℚ :=
  1 / ((numGroups n : ℚ) * Nat.clog 2 n)

/-- Casting `tauRat n` to `ℝ` recovers `tau n`. -/
@[simp]
theorem cast_tauRat (n : ℕ) : (tauRat n : ℝ) = tau n := by
  simp only [tauRat, tau, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]

/-- When `1 ≤ rowBound β n`, membership in `interval β n` is equivalent to lying in
`[intervalStart β n, intervalStart β n + rowBound β n)`. -/
theorem notMem_interval_iff {β n k : ℕ} (hR : 1 ≤ rowBound β n) :
    k ∉ interval β n ↔ k < intervalStart β n ∨ intervalStart β n + rowBound β n ≤ k := by
  simp only [interval, mem_Icc]
  omega

/-- When `1 ≤ numGroups n` and `1 ≤ rowBound β n`, casting the rational binomial tail probability
`binomTailProb (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n)` to `ℝ` gives
`binomTail β n`. -/
theorem cast_binomTailProb_eq_binomTail {β n : ℕ} (hr : 1 ≤ numGroups n)
    (hR : 1 ≤ rowBound β n) :
    (binomTailProb (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n) : ℝ) =
      binomTail β n := by
  unfold binomTailProb binomTail
  have hfilt :
      (range (numNodes n + 1)).filter
          (fun j => j < intervalStart β n ∨ intervalStart β n + rowBound β n ≤ j) =
        (range (numNodes n + 1)).filter (fun k => k ∉ interval β n) := by
    ext k
    simp only [mem_filter, notMem_interval_iff hR]
  rw [hfilt, Rat.cast_sum]
  refine sum_congr rfl fun k _ => ?_
  have hr0 : (numGroups n : ℝ) ≠ 0 := by positivity
  have hprob : ((numGroups n : ℝ) - 1) / (2 * (numGroups n : ℝ)) = binomProb n := rfl
  have hcomp : ((numGroups n : ℝ) + 1) / (2 * (numGroups n : ℝ)) = 1 - binomProb n := by
    unfold binomProb
    field_simp [hr0]
    ring
  push_cast
  rw [hprob, hcomp]

/-- The three-term counting-cost rate `threeTermExponent` instantiated at the Lemma 4.8 schedule
is definitionally equal to `rowCost β n`. -/
@[simp]
theorem threeTermExponent_eq_rowCost (β n : ℕ) :
    threeTermExponent (numGroups n) (numNodes n) (rowBound β n) (auxDim n) (tau n) =
      rowCost β n :=
  rfl

/-! ### 2. Extracting Lemma 4.7 hypotheses and designs from `Feasible` -/

namespace Feasible

variable {β n b w M : ℕ}

/-- `1 ≤ n` holds under `Feasible β n b w M`. -/
theorem one_le_n (hF : Feasible β n b w M) : 1 ≤ n := by
  have := hF.twenty_le
  omega

/-- `1 ≤ rowBound β n` holds under `Feasible β n b w M`. -/
theorem one_le_rowBound (hF : Feasible β n b w M) : 1 ≤ rowBound β n := by
  have := hF.thirtyTwo_le_rowBound
  omega

/-- `rowBound β n < numNodes n` holds under `Feasible β n b w M`. -/
theorem rowBound_lt_numNodes (hF : Feasible β n b w M) : rowBound β n < numNodes n := by
  have h1 := hF.thirtyTwo_le_rowBound
  have h2 := hF.six_mul_rowBound_le_numNodes
  omega

/-- `0 < tauRat n` holds under `Feasible β n b w M`. -/
theorem tauRat_pos (hF : Feasible β n b w M) : 0 < tauRat n := by
  have h : (0 : ℝ) < (tauRat n : ℝ) := by
    rw [cast_tauRat]
    exact hF.tau_pos
  exact_mod_cast h

/-- `tauRat n ≤ 1 / 2` holds under `Feasible β n b w M`. -/
theorem tauRat_le_half (hF : Feasible β n b w M) : tauRat n ≤ 1 / 2 := by
  have h : (tauRat n : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by
    rw [cast_tauRat]
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hF.tau_le_half
  exact_mod_cast h

/-- Every shift `intervalStart β n + a` for `a < rowBound β n` lies in `[0, numNodes n]`. -/
theorem intervalStart_add_le_numNodes (hF : Feasible β n b w M) {a : ℕ}
    (ha : a < rowBound β n) :
    intervalStart β n + a ≤ numNodes n := by
  have hmem : intervalStart β n + a ∈ interval β n := by
    simp only [interval, mem_Icc]
    omega
  have hrng := mem_range.mp (hF.interval_subset hmem)
  omega

/-- Under `Feasible β n b w M`, the rational binomial tail probability satisfies Lemma 4.7's
strict threshold `binomTailProb < tauRat n / (numGroups n * b)`. -/
theorem binomTailProb_lt (hF : Feasible β n b w M) :
    binomTailProb (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n) <
      tauRat n / ((numGroups n : ℚ) * b) := by
  have hr1 : 1 ≤ numGroups n := by
    have := hF.two_le_numGroups
    omega
  have hlt :
      (binomTailProb (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n) : ℝ) <
        ((tauRat n / ((numGroups n : ℚ) * b) : ℚ) : ℝ) := by
    rw [cast_binomTailProb_eq_binomTail hr1 hF.one_le_rowBound]
    have hrhs :
        ((tauRat n / ((numGroups n : ℚ) * b) : ℚ) : ℝ) = tailBudget b n := by
      rw [tailBudget_eq_tau_div, ← cast_tauRat]
      push_cast
      rfl
    rw [hrhs]
    exact hF.binomTail_lt
  exact_mod_cast hlt

/-- **Lemma 4.7 + Lemma 4.8 concrete replacement design existence**:
Given `hF : Feasible β n b w (∑ f, #(scope f))` on a factor scope family
`scope : F → Finset (Fin n)` with `1 ≤ b`, `1 ≤ w`, per-variable occurrence `≤ b`, per-factor
scope size `≤ w`, and total incidence `∑ f, #(scope f) ≤ b * n`, there exists a concrete
Section 4
`ReplacementDesign scope (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n) (tauRat n)`.
-/
theorem exists_replacementDesign {F : Type*} [Fintype F]
    (scope : F → Finset (Fin n)) (hF : Feasible β n b w (∑ f : F, #(scope f)))
    (hb_pos : 1 ≤ b) (hw_pos : 1 ≤ w)
    (hb : ∀ v : Fin n, #{f : F | v ∈ scope f} ≤ b)
    (hw : ∀ f : F, #(scope f) ≤ w)
    (hM_le : (∑ f : F, #(scope f)) ≤ b * n) :
    Nonempty
      (ReplacementDesign scope (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n)
        (tauRat n)) :=
  Cslib.LinearAlgebra.exists_replacementDesign scope hF.one_le_n hb_pos hw_pos
    hF.two_le_numGroups hF.one_le_rowBound hF.rowBound_lt_numNodes hF.tauRat_pos.le
    (fun _ ha => hF.intervalStart_add_le_numNodes (by omega))
    hb hw hM_le hF.aux_balance hF.var_balance hF.binomTailProb_lt.le

/-- Converts any concrete `ReplacementDesign` at the Lemma 4.8 schedule into a Section 3
`Cslib.ReplacementCounting.Design` for an active factor subset `s : Finset F`. -/
def toCountingDesign {F : Type*} [Fintype F] {scope : F → Finset (Fin n)}
    (hF : Feasible β n b w M)
    (D : ReplacementDesign scope (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n)
      (tauRat n))
    (s : Finset F) :
    Cslib.ReplacementCounting.Design (Fin n) s (fun f => {v : Fin n // v ∈ scope f})
      (fun _ v => v.1) (numGroups n) (numNodes n) (rowBound β n) (auxDim n) (tau n) :=
  cast (by rw [cast_tauRat]; rfl)
    (D.toCountingDesign s hF.two_le_numGroups hF.one_le_rowBound hF.rowBound_lt_numNodes
      hF.tauRat_pos hF.tauRat_le_half)

/-- **Proposition 3.4 + Lemma 4.8 domain-examination bound in terms of `rowCost β n`**:
For any `Feasible β n b w M` and concrete schedule design `D`, the induced counting design
`hF.toCountingDesign D s` examines at most
`2 * numNodes n * numGroups n * exp ((c + 4) * n * rowCost β n)` local Boolean assignments across
all `numNodes n` nodes and all subset pairs `(E, U)` with `#E ≤ q` (`(q : ℝ) ≤ c * n * (R / Q)`),
which in turn is bounded by
`2 * numNodes n * numGroups n * exp ((c + 4) * n * (1028 * (β + 3) * ν² / √λ))`. -/
theorem domainExaminationBound_le_mul_exp_rowCost {F : Type*} [Fintype F]
    {scope : F → Finset (Fin n)} (hF : Feasible β n b w M)
    (D : ReplacementDesign scope (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n)
      (tauRat n))
    (s : Finset F) {q : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hq : (q : ℝ) ≤ c * (n : ℝ) * ((rowBound β n : ℝ) / numNodes n)) :
    let C := hF.toCountingDesign D s
    (∑ t : Fin (numNodes n),
        (#{p : Finset (Fin n) × Finset (Fin n) | #p.1 ≤ q ∧ p.2 ⊆ p.1} : ℝ) *
          (2 * (#(C.measurementBox t) : ℝ) *
            ∑ g : Fin (numGroups n), (Fintype.card (C.LocalCube t g) : ℝ))) ≤
      2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
        Real.exp ((c + 4) * (n : ℝ) * rowCost β n) ∧
    2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
        Real.exp ((c + 4) * (n : ℝ) * rowCost β n) ≤
      2 * (numNodes n : ℝ) * (numGroups n : ℝ) *
        Real.exp ((c + 4) * (n : ℝ) *
          (1028 * ((β : ℝ) + 3) * (Nat.clog 2 (Nat.clog 2 n) : ℝ) ^ 2 /
            Real.sqrt (Nat.clog 2 n))) := by
  intro C
  have hq' :
      (q : ℝ) ≤ c * (Fintype.card (Fin n) : ℝ) * ((rowBound β n : ℝ) / numNodes n) := by
    simpa only [Fintype.card_fin] using hq
  have h1 := C.domainExaminationBound_le_mul_exp_threeTermExponent hc hq'
  simp only [Fintype.card_fin, threeTermExponent_eq_rowCost] at h1
  refine ⟨h1, ?_⟩
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  exact mul_le_mul_of_nonneg_left hF.rowCost_bound (by positivity)

end Feasible

/-- **Uniform Lemma 4.7 + Lemma 4.8 schedule design existence**:
For every integer `1 ≤ β`, there exists `n₀ ≥ 20` such that for all `n ≥ n₀`,
`1 ≤ b, w ≤ (Nat.clog 2 n) ^ β`, and any factor scope family `scope : F → Finset (Fin n)` with
`n ≤ ∑ f, #(scope f) ≤ b * n`, per-variable occurrence `≤ b`, and per-factor width `≤ w`, the
schedule (4.17) is `Feasible` and admits both a concrete `ReplacementDesign` and an induced
`Cslib.ReplacementCounting.Design`. -/
theorem exists_schedule_replacementDesign {β : ℕ} (hβ : 1 ≤ β) :
    ∃ n₀ : ℕ, 20 ≤ n₀ ∧ ∀ ⦃n b w : ℕ⦄ {F : Type*} [Fintype F]
      (scope : F → Finset (Fin n)),
      n₀ ≤ n →
      1 ≤ b → b ≤ Nat.clog 2 n ^ β →
      1 ≤ w → w ≤ Nat.clog 2 n ^ β →
      n ≤ ∑ f : F, #(scope f) →
      (∑ f : F, #(scope f)) ≤ b * n →
      (∀ v : Fin n, #{f : F | v ∈ scope f} ≤ b) →
      (∀ f : F, #(scope f) ≤ w) →
      Feasible β n b w (∑ f : F, #(scope f)) ∧
        Nonempty
          (ReplacementDesign scope (numNodes n) (numGroups n) (intervalStart β n) (rowBound β n)
            (tauRat n)) := by
  obtain ⟨n₀, hn₀20, hfeas⟩ := exists_feasible hβ
  refine ⟨n₀, hn₀20, fun {n b w F _} scope hn hb₁ hb₂ hw₁ hw₂ hnM hMbn hb hw => ?_⟩
  have hF := hfeas hn hb₁ hb₂ hw₁ hw₂ hnM hMbn
  exact ⟨hF, hF.exists_replacementDesign scope hb₁ hw₁ hb hw hMbn⟩

end Cslib.Complexity.SubexponentialSAT.ReplacementParams
