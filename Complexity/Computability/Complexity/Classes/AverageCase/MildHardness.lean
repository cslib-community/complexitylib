/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.AverageCase
public import Complexity.Computability.Complexity.Classes.AverageCase.Distributional
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Probability.PMF.Bool
import Complexity.Tactic.PolyTime

/-!
# Heuristic schemes against mild average-case hardness

This file connects the distributional classes of
`Complexity.Computability.Complexity.Classes.AverageCase.Distributional` with the mild
average-case hardness notions of `Complexity.Computability.Complexity.AverageCase`, which follow
[Y. Liu and R. Pass][LiuPass2020]. Those notions measure the success of polynomial-time heuristics
for a function `f : List Bool → ℕ` on the uniform distribution on `{0,1}^n`, that is, under the
uniform ensemble `Cslib.Complexity.Ensemble.uniform`.

For a Boolean function `b`, a heuristic scheme for the distributional problem
`({x | b x = true}, U)` contradicts mild hardness of `b`: running the scheme with confidence
parameter `2 p(n)` gives a deterministic polynomial-time heuristic that errs with probability at
most `1/(2 p(n) + 1) < 1/p(n)`, for every polynomial `p`.

## Main results

* `Cslib.Complexity.exists_heuristic_of_mem_HeurP`: a heuristic scheme yields, for every positive
  polynomial `p`, a deterministic polynomial-time heuristic succeeding with probability above
  `1 - 1/p(n)` at every length.
* `Cslib.Complexity.not_mildlyHardOnAverageDet_of_mem_HeurP`: if `({x | b x = true}, U) ∈ HeurP`,
  then `b` (as a `0/1`-valued function) is not mildly hard on average against deterministic
  polynomial-time heuristics; `Cslib.Complexity.not_mildlyHardOnAverageIO_of_mem_HeurP` rules out
  even infinitely-often hardness.
* `Cslib.Complexity.not_mildlyHardOnAverage_of_mem_HeurP`: the same against strict PPT heuristics.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
* [Y. Liu and R. Pass, *On One-Way Functions and Kolmogorov Complexity*][LiuPass2020]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-- If `({x | b x = true}, U) ∈ HeurP`, then for every positive polynomial `p` some deterministic
polynomial-time heuristic computes `b` with success probability above `1 - 1/p(n)` at **every**
length `n`. -/
theorem exists_heuristic_of_mem_HeurP (b : List Bool → Bool)
    (h : (⟨{x | b x = true}, Ensemble.uniform⟩ : DistProblem) ∈ HeurP) (p : Polynomial ℕ)
    (hp : ∀ n, 0 < p.eval n) :
    ∃ H : List Bool → ℕ, ComputableInPolyTime H encBits encNat ∧ ∀ n,
      1 - 1 / ((p.eval n : ℕ) : ℝ) <
        (((BitString.uniformList n).map fun x => decide (H x = (b x).toNat)) true).toReal := by
  obtain ⟨A, hA⟩ := h
  have hpt := hA.polyTime
  refine ⟨fun x => (A (x, 2 * p.eval x.length)).toNat, by polytime, fun n => ?_⟩
  have hfalse : ((BitString.uniformList n).map fun x =>
      decide ((A (x, 2 * p.eval x.length)).toNat = (b x).toNat)) false ≤
      ((2 * p.eval n + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    have herr := hA.error_le n (2 * p.eval n)
    rw [Ensemble.uniform_dist] at herr
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) herr
    rintro x ⟨hx, hsupp⟩
    have hlen : x.length = n := BitString.length_of_mem_support_uniformList hsupp
    simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_false_iff_not, hlen] at hx
    simp only [Set.mem_ofPred_eq]
    cases hAx : A (x, 2 * p.eval n) <;> cases hbx : b x <;> simp_all
  have hreal := ENNReal.toReal_mono (by simp) hfalse
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast] at hreal
  rw [Probability.PMF.toReal_true_eq_one_sub]
  have hp0 : (0 : ℝ) < (p.eval n : ℕ) := by exact_mod_cast hp n
  have hlt : ((2 * p.eval n + 1 : ℕ) : ℝ)⁻¹ < 1 / ((p.eval n : ℕ) : ℝ) := by
    rw [← one_div]
    apply one_div_lt_one_div_of_lt hp0
    push_cast
    linarith
  linarith

/-- A Boolean function whose distributional problem under the uniform ensemble is in `HeurP` is not
mildly hard on average against deterministic polynomial-time heuristics. -/
theorem not_mildlyHardOnAverageDet_of_mem_HeurP (b : List Bool → Bool)
    (h : (⟨{x | b x = true}, Ensemble.uniform⟩ : DistProblem) ∈ HeurP) :
    ¬ MildlyHardOnAverageDet (fun x => (b x).toNat) := by
  rintro ⟨p, hp, hhard⟩
  obtain ⟨H, hH, hsucc⟩ := exists_heuristic_of_mem_HeurP b h p hp
  obtain ⟨n, hn⟩ := (hhard H hH).exists
  exact absurd hn (not_le.mpr (hsucc n))

/-- A Boolean function whose distributional problem under the uniform ensemble is in `HeurP` is not
even infinitely-often mildly hard on average against deterministic polynomial-time heuristics. -/
theorem not_mildlyHardOnAverageIO_of_mem_HeurP (b : List Bool → Bool)
    (h : (⟨{x | b x = true}, Ensemble.uniform⟩ : DistProblem) ∈ HeurP) :
    ¬ MildlyHardOnAverageIO (fun x => (b x).toNat) := by
  rintro ⟨p, hp, hhard⟩
  obtain ⟨H, hH, hsucc⟩ := exists_heuristic_of_mem_HeurP b h p hp
  obtain ⟨n, hn⟩ := (hhard H hH).exists
  exact absurd hn (not_le.mpr (hsucc n))

/-- A Boolean function whose distributional problem under the uniform ensemble is in `HeurP` is not
mildly hard on average against strict PPT heuristics
([Liu and Pass, Definition 2.4][LiuPass2020]). -/
theorem not_mildlyHardOnAverage_of_mem_HeurP (b : List Bool → Bool)
    (h : (⟨{x | b x = true}, Ensemble.uniform⟩ : DistProblem) ∈ HeurP) :
    ¬ MildlyHardOnAverage (fun x => (b x).toNat) :=
  fun hhard => not_mildlyHardOnAverageDet_of_mem_HeurP b h hhard.mildlyHardOnAverageDet

end Cslib.Complexity
