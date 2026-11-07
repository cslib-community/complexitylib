/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Privacy.DifferentialPrivacy.AboveThreshold
import Complexity.Privacy.DifferentialPrivacy.ExponentialMechanism
import ComplexityTests.Privacy.DifferentialPrivacy

/-!
# Exponential mechanism, AboveThreshold and Sparse: instances and clients

* The exponential mechanism on a count-valued utility is private, and in Dwork and Roth's
  "best of two" example (Example 3.6) it returns the wrong condition with probability at most
  `2 exp (-c ε / 2)`.
* AboveThreshold and Sparse with discrete Laplace noise on count queries are `(ε, 0)`-private,
  however many queries are asked.
* AboveThreshold on no queries reports nothing; the accuracy condition holds and fails on concrete
  answers.
* The full accuracy statement of [DworkRoth2014, Theorem 3.24] for discrete noise: if every answer
  before the last is below `T - α`, then except with probability `β` the output is accurate and
  does not halt early.
-/

namespace ComplexityTests.Privacy.SparseVector

open Cslib Cslib.Privacy ComplexityTests.Privacy.DifferentialPrivacy
open scoped ENNReal

/-! ### The exponential mechanism -/

/-- Selecting a row value by a count utility: utility `#{i | x i = b}` has sensitivity one. -/
noncomputable def countUtility {n : ℕ} (x : Fin n → Bool) (b : Bool) : ℝ :=
  countTrue (fun i => x i == b)

example {n : ℕ} {ε : ℝ} (hε : 0 ≤ ε) :
    DifferentiallyPrivate HammingAdjacent (exponentialMechanism (countUtility (n := n)) 1 ε) ε 0 :=
  differentiallyPrivate_exponentialMechanism one_pos hε fun x y h b => by
    refine abs_countTrue_sub_le fun i hi j hj => h (fun hxy => hi ?_) (fun hxy => hj ?_)
    · simp only [hxy]
    · simp only [hxy]

/-- Dwork and Roth's "best of two" (Example 3.6): with counts `0` for condition `A` (`false`) and
`c` for `B` (`true`), utility the count and `Δ = 1`, the exponential mechanism outputs the wrong
condition `A` with probability at most `2 exp (-c ε / 2)`. (Dwork and Roth take `c > 0`; the bound
holds for every `c`.) -/
example {c ε : ℝ} (hε : 0 < ε) :
    (exponentialMechanism (fun (_ : Unit) (b : Bool) => if b then c else 0) 1 ε ()).toOuterMeasure
        {false} ≤ ENNReal.ofReal (2 * Real.exp (-(c * ε / 2))) := by
  set u : Unit → Bool → ℝ := fun _ b => if b then c else 0
  have hopt : c ≤ optUtility u () := le_optUtility u () true
  have h := exponentialMechanism_toOuterMeasure_utility_le_opt_sub_log_card (u := u) one_pos hε ()
    (c * ε / 2 - Real.log 2)
  have hcard : (Fintype.card Bool : ℝ) = 2 := by simp
  rw [hcard] at h
  have hexp : Real.exp (-(c * ε / 2 - Real.log 2)) = 2 * Real.exp (-(c * ε / 2)) := by
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log two_pos]
  rw [hexp] at h
  refine le_trans (MeasureTheory.measure_mono fun b hb => ?_) h
  rw [Set.mem_singleton_iff] at hb
  subst hb
  simp only [Set.mem_ofPred_eq, u, Bool.false_eq_true, ↓reduceIte]
  have : 2 * 1 / ε * (Real.log 2 + (c * ε / 2 - Real.log 2)) = c := by field_simp; ring
  linarith

/-! ### AboveThreshold and Sparse on count queries -/

/-- AboveThreshold with discrete Laplace noise on any list of count queries is `(ε, 0)`-private. -/
example {n : ℕ} (qs : List ((Fin n → Bool) → ℝ))
    (hqs : ∀ q ∈ qs, ∀ ⦃x y⦄, HammingAdjacent x y → |q x - q y| ≤ 1) (T : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    DifferentiallyPrivate HammingAdjacent
      (aboveThresholdMechanism (discreteLaplace (2 * (1 : ℕ) / ε) (by positivity))
        (discreteLaplace (4 * (1 : ℕ) / ε) (by positivity)) T qs) ε 0 :=
  differentiallyPrivate_aboveThreshold_discreteLaplace one_pos (by exact_mod_cast hqs) hε

/-- Two copies of the count query: the privacy cost does not double. -/
example {n : ℕ} (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    DifferentiallyPrivate HammingAdjacent
      (aboveThresholdMechanism (discreteLaplace (2 * (1 : ℕ) / ε) (by positivity))
        (discreteLaplace (4 * (1 : ℕ) / ε) (by positivity)) T
        [fun x => (countTrue (n := n) x : ℝ), fun x => (countTrue (n := n) x : ℝ)]) ε 0 :=
  differentiallyPrivate_aboveThreshold_discreteLaplace one_pos
    (fun q hq x y h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl <;>
        simpa only [Nat.cast_one] using abs_countTrue_sub_le h) hε

/-- Sparse with cutoff `2` on count queries is `(ε, 0)`-private. -/
example {n : ℕ} (qs : List ((Fin n → Bool) → ℝ))
    (hqs : ∀ q ∈ qs, ∀ ⦃x y⦄, HammingAdjacent x y → |q x - q y| ≤ 1) (T : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    DifferentiallyPrivate HammingAdjacent
      (sparse (discreteLaplace (2 * (2 : ℕ) * (1 : ℕ) / ε) (by positivity))
        (discreteLaplace (4 * (2 : ℕ) * (1 : ℕ) / ε) (by positivity)) T qs 2) ε 0 :=
  differentiallyPrivate_sparse_discreteLaplace one_pos (by exact_mod_cast hqs) two_pos hε

/-! ### Concrete behaviour and the accuracy condition -/

/-- On no queries, AboveThreshold reports nothing. -/
example (ρ ν : PMF ℤ) (T : ℝ) : aboveThreshold ρ ν T [] = PMF.pure none := by
  simp [aboveThreshold, aboveThresholdAux]

/-- Reporting the second of the answers `0, 7` against `T = 4` is `1`-accurate. -/
example : ThresholdAccurate 4 1 [0, 7] (some 1) := by
  simp only [ThresholdAccurate]; norm_num

/-- Reporting the first answer `0` against `T = 4` is not `1`-accurate. -/
example : ¬ ThresholdAccurate 4 1 [0, 7] (some 0) := by
  simp only [ThresholdAccurate]; norm_num

/-- Reporting nothing on the answers `0, 7` against `T = 4` is not `1`-accurate, since
`7 > 4 + 1`. -/
example : ¬ ThresholdAccurate 4 1 [0, 7] none := by
  simp only [ThresholdAccurate]; norm_num

/-- The accuracy theorem of [DworkRoth2014, Theorem 3.24] for discrete Laplace noise: if every
answer before the last is below `T - α`, then except with probability `β` the output is accurate
and, if it reports an index, reports the last one. -/
example {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (T : ℝ) (as : List ℝ)
    (has : ∀ j (hj : j + 1 < as.length),
      as[j] < T - 8 * (Real.log (as.length + 1) + Real.log (2 / β)) / ε) :
    (aboveThreshold (discreteLaplace (2 / ε) (by positivity))
        (discreteLaplace (4 / ε) (by positivity)) T as).toOuterMeasure
      {o | ¬ (ThresholdAccurate T (8 * (Real.log (as.length + 1) + Real.log (2 / β)) / ε) as o ∧
        ∀ i, o = some i → as.length ≤ i + 1)} ≤ ENNReal.ofReal β := by
  refine le_trans (MeasureTheory.measure_mono fun o ho => ?_)
    (aboveThreshold_discreteLaplace_toOuterMeasure_not_thresholdAccurate_le hε hβ hβ1 T as)
  simp only [Set.mem_ofPred_eq] at ho ⊢
  intro hacc
  exact ho ⟨hacc, fun i hi => (hi ▸ hacc).length_le has⟩

end ComplexityTests.Privacy.SparseVector
