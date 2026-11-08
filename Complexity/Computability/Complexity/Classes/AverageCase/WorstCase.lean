/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.AverageCase.Collapse
public import Complexity.Computability.Complexity.Classes.AverageCase.Distributional
public import Complexity.Computability.Complexity.Classes.Padding
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Tactic.PolyTime

/-!
# Worst-case consequences of easy-on-average `NP`

If every distributional problem in `DistNP` has a polynomial-time heuristic scheme, then
`NE = E`. This is a length-indexed form of the theorem of Ben-David, Chor, Goldreich and Luby for
`AvgP` [Ben-David, Chor, Goldreich and Luby][BenDavidChorGoldreichLuby1992] (see *Scope*). The
attribution is taken from
[Bläser and Manthey, §5][BlaserManthey2015]. The proof is padding with a polynomial-time computable
ensemble that puts mass `1/poly` on every padded instance.

## Heavy instances

A heuristic scheme run with confidence parameter `k` errs with probability at most `1/(k+1)` on
each length. So it cannot err on an instance of larger probability
(`Cslib.Complexity.DistProblem.IsHeuristicScheme.correct_of_lt`). An errorless scheme likewise
answers every such instance (`Cslib.Complexity.DistProblem.IsErrorlessScheme.correct_of_lt`). Run
with confidence `q(|x|)`, a heuristic scheme becomes a single polynomial-time decider that is
correct on every instance of probability at least `1/q(|x|)`
(`Cslib.Complexity.exists_agree_of_mem_HeurP`). When every instance in the support is that heavy,
the decider is correct on the whole support
(`Cslib.Complexity.exists_agree_on_support_of_mem_HeurP`).

Under the uniform ensemble a word `x` has probability `2^{-|x|}`. With confidence `2^{|x|}` the
scheme decides `L` exactly, in time polynomial in `2^{|x|}`. So `(L, U) ∈ HeurP` implies `L ∈ E`
(`Cslib.Complexity.mem_E_of_mem_HeurP_uniform`).

## Padded instances

`Cslib.Complexity.PaddedFrame.ensemble` collapses the uniform ensemble at the prefix code of framed
words (`Cslib.Complexity.HeaderParser.ensemble`). The padded word `frame u ++ 1^m` gets probability
exactly `2^{-(2|u|+1)}` (`Cslib.Complexity.PaddedFrame.ensemble_dist_frame_append`), and the
ensemble is polynomial-time computable. If `2^{|u|} ≤ m` and `N = 2|u| + 1 + m`, this probability
is at least `1/(2N²)`. So under `DistNP ⊆ HeurP`, every problem in `NP` paired with this ensemble
has a polynomial-time decider that is correct on all exponentially padded instances. That is the
hypothesis `Cslib.Complexity.ExpPaddedNPEasy` of the padding argument
(`Cslib.Complexity.expPaddedNPEasy_of_DistNP_subset_HeurP`), which gives `NE ⊆ E` and
`NEXP ⊆ EXP`.

## Scope

[Ben-David, Chor, Goldreich and Luby][BenDavidChorGoldreichLuby1992] state the theorem for
`DistNP ⊆ AvgP` in Levin's model, with a single distribution on all words. The statements here use
the length-indexed ensembles and the scheme classes `AvgP` and `HeurP` of
[Bogdanov and Trevisan][BogdanovTrevisan2006]; no bridge between the two models is formalized. The
`HeurP` form is stronger than the `AvgP` form `Cslib.Complexity.NE_subset_E_of_DistNP_subset_AvgP`
because `AvgP ⊆ HeurP` (`Cslib.Complexity.AvgP_subset_HeurP`). The primary text has not been
inspected, so its theorem number and the details of its proof are unverified. The proof here is a
standard padding argument, and the `HeurP` strengthening is not claimed as new.

## Main results

* `Cslib.Complexity.DistProblem.IsHeuristicScheme.correct_of_lt`,
  `Cslib.Complexity.DistProblem.IsErrorlessScheme.correct_of_lt`: schemes are correct on instances
  heavier than their failure bound.
* `Cslib.Complexity.exists_agree_of_mem_HeurP`: one polynomial-time decider is correct on all
  instances of probability at least `1/q(|x|)`.
* `Cslib.Complexity.mem_E_of_mem_HeurP_uniform`, `Cslib.Complexity.mem_E_of_mem_AvgP_uniform`:
  `(L, U) ∈ HeurP` or `(L, U) ∈ AvgP` implies `L ∈ E`.
* `Cslib.Complexity.PaddedFrame.ensemble_pComp`,
  `Cslib.Complexity.PaddedFrame.ensemble_dist_frame_append`: the padded ensemble.
* `Cslib.Complexity.NE_subset_E_of_DistNP_subset_HeurP`,
  `Cslib.Complexity.E_eq_NE_of_DistNP_subset_HeurP`: if `DistNP ⊆ HeurP`, then `E = NE`, and
  likewise `EXP = NEXP`; the `AvgP` corollaries
  `Cslib.Complexity.NE_subset_E_of_DistNP_subset_AvgP` and
  `Cslib.Complexity.E_eq_NE_of_DistNP_subset_AvgP`.

## References

* [S. Ben-David, B. Chor, O. Goldreich, M. Luby, *On the theory of average case
  complexity*][BenDavidChorGoldreichLuby1992]
* [M. Bläser, B. Manthey, *Smoothed Complexity Theory*][BlaserManthey2015]
* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-! ### Heavy instances -/

namespace DistProblem

/-- **A heuristic scheme is correct on heavy instances.** Run with confidence parameter `k`, it
errs with probability at most `1/(k+1)` on each length. So it answers correctly on every instance
of larger probability. -/
theorem IsHeuristicScheme.correct_of_lt {L : DistProblem} {A : List Bool × ℕ → Bool}
    (hA : L.IsHeuristicScheme A) {x : List Bool} {k : ℕ}
    (hx : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < L.ens.dist x.length x) :
    A (x, k) = true ↔ x ∈ L.lang := by
  by_contra hne
  have hle : L.ens.dist x.length x ≤
      (L.ens.dist x.length).toOuterMeasure {y | ¬(A (y, k) = true ↔ y ∈ L.lang)} := by
    rw [← PMF.toOuterMeasure_apply_singleton]
    exact PMF.toOuterMeasure_mono _ fun y hy => by
      obtain ⟨rfl, -⟩ := hy
      exact hne
  exact absurd (hle.trans (hA.error_le x.length k)) (not_le.mpr hx)

/-- **An errorless scheme answers heavy instances.** Run with confidence parameter `k`, it fails
with probability at most `1/(k+1)` on each length. So it answers every instance of larger
probability, and correctly. -/
theorem IsErrorlessScheme.correct_of_lt {L : DistProblem} {A : List Bool × ℕ → Option Bool}
    (hA : L.IsErrorlessScheme A) {x : List Bool} {k : ℕ}
    (hx : ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ < L.ens.dist x.length x) :
    ∃ b, A (x, k) = some b ∧ (b = true ↔ x ∈ L.lang) := by
  have hsupp : x ∈ (L.ens.dist x.length).support :=
    (PMF.mem_support_iff _ _).mpr (lt_of_le_of_lt zero_le hx).ne'
  cases hAx : A (x, k) with
  | some b => exact ⟨b, rfl, hA.correct _ x k b hsupp hAx⟩
  | none =>
    have hle : L.ens.dist x.length x ≤
        (L.ens.dist x.length).toOuterMeasure {y | A (y, k) = none} := by
      rw [← PMF.toOuterMeasure_apply_singleton]
      exact PMF.toOuterMeasure_mono _ fun y hy => by
        obtain ⟨rfl, -⟩ := hy
        exact hAx
    exact absurd (hle.trans (hA.failure_le x.length k)) (not_le.mpr hx)

end DistProblem

/-- **Heavy instances are decided in polynomial time.** If `L ∈ HeurP`, then for every polynomial
`q` a single polynomial-time decider is correct on every instance `x` of probability at least
`1/q(|x|)`: run the heuristic scheme with confidence parameter `q(|x|)`. -/
theorem exists_agree_of_mem_HeurP {L : DistProblem} (hL : L ∈ HeurP) (q : Polynomial ℕ) :
    ∃ f : List Bool → Bool, ComputableInPolyTime f encBits encBool ∧
      ∀ x, ((q.eval x.length : ℕ) : ℝ≥0∞)⁻¹ ≤ L.ens.dist x.length x →
        (f x = true ↔ x ∈ L.lang) := by
  obtain ⟨A, hA⟩ := hL
  have hpt := hA.polyTime
  refine ⟨fun x => A (x, q.eval x.length), by polytime, fun x hx => hA.correct_of_lt ?_⟩
  refine lt_of_lt_of_le (ENNReal.inv_lt_inv' ?_) hx
  exact_mod_cast Nat.lt_succ_self _

/-- **Exact decision on the support.** If `L ∈ HeurP` and every instance in the support of the
ensemble has probability at least `1/q(|x|)`, then a polynomial-time decider agrees with `L` on
the support. -/
theorem exists_agree_on_support_of_mem_HeurP {L : DistProblem} (hL : L ∈ HeurP)
    {q : Polynomial ℕ}
    (hq : ∀ n x, x ∈ (L.ens.dist n).support → ((q.eval n : ℕ) : ℝ≥0∞)⁻¹ ≤ L.ens.dist n x) :
    ∃ f : List Bool → Bool, ComputableInPolyTime f encBits encBool ∧
      ∀ n x, x ∈ (L.ens.dist n).support → (f x = true ↔ x ∈ L.lang) := by
  obtain ⟨f, hf, hagree⟩ := exists_agree_of_mem_HeurP hL q
  refine ⟨f, hf, fun n x hx => hagree x ?_⟩
  rw [L.ens.length_eq n x hx]
  exact hq n x hx

/-- **`(L, U) ∈ HeurP` implies `L ∈ E`.** A word `x` has probability `2^{-|x|}` under the uniform
ensemble, so the heuristic scheme run with confidence parameter `2^{|x|}` decides `L` exactly, in
time polynomial in `2^{|x|}`. -/
theorem mem_E_of_mem_HeurP_uniform {L : Set (List Bool)}
    (h : (⟨L, Ensemble.uniform⟩ : DistProblem) ∈ HeurP) : L ∈ E encBits := by
  obtain ⟨A, hA⟩ := h
  convert setOf_mem_E_of_computableInPolyTime_pad hA.polyTime using 1
  ext x
  refine (hA.correct_of_lt (x := x) (k := 2 ^ x.length) ?_).symm
  change _ < Ensemble.uniform.dist x.length x
  rw [Ensemble.uniform_apply]
  refine ENNReal.inv_lt_inv' ?_
  exact_mod_cast Nat.lt_succ_self _

/-- **`(L, U) ∈ AvgP` implies `L ∈ E`.** -/
theorem mem_E_of_mem_AvgP_uniform {L : Set (List Bool)}
    (h : (⟨L, Ensemble.uniform⟩ : DistProblem) ∈ AvgP) : L ∈ E encBits :=
  mem_E_of_mem_HeurP_uniform (AvgP_subset_HeurP h)

/-! ### The padded ensemble -/

namespace PaddedFrame

/-- The framed word at the start of `r`, framed again: `frame (unframe r)`. -/
def header (r : List Bool) : List Bool := frame (unframe r)

/-- A word **begins with a framed word** if `header r` is a prefix of it. -/
def valid (r : List Bool) : Bool := decide (r.take (header r).length = header r)

theorem valid_iff (r : List Bool) : valid r = true ↔ header r <+: r := by
  rw [valid, decide_eq_true_eq, List.prefix_iff_eq_take, eq_comm]

theorem header_frame_append (u s : List Bool) : header (frame u ++ s) = frame u := by
  rw [header, unframe_frame_append]

theorem valid_frame_append (u s : List Bool) : valid (frame u ++ s) = true := by
  rw [valid_iff, header_frame_append]
  exact List.prefix_append _ _

/-- A word begins with a framed word exactly when it is `frame u ++ s` for some `u` and `s`. -/
theorem valid_iff_exists (r : List Bool) : valid r = true ↔ ∃ u s, r = frame u ++ s := by
  refine ⟨fun h => ?_, fun ⟨u, s, h⟩ => h ▸ valid_frame_append u s⟩
  obtain ⟨s, hs⟩ := (valid_iff r).mp h
  exact ⟨unframe r, s, hs.symm⟩

/-- The prefix code of framed words. -/
def parser : HeaderParser where
  valid := valid
  header := header
  header_isPrefix r hr := (valid_iff r).mp hr
  valid_of_isPrefix r r' hr hp := by
    obtain ⟨s, rfl⟩ := hp
    exact ⟨valid_frame_append _ _, header_frame_append _ _⟩

theorem header_polyTime : ComputableInPolyTime header encBits encBits :=
  ComputableInPolyTime.frame.comp ComputableInPolyTime.unframe

theorem valid_polyTime : ComputableInPolyTime valid encBits encBool := by
  have hh := header_polyTime
  unfold valid
  polytime

/-- **The padded ensemble**: flip uniform bits until a framed word has been read, then pad it with
ones. -/
noncomputable def ensemble : Ensemble := parser.ensemble

/-- The padded ensemble is polynomial-time computable. -/
theorem ensemble_pComp : ensemble.PComp :=
  parser.pComp_ensemble valid_polyTime header_polyTime

/-- **A padded word `frame u ++ 1^m` has probability `2^{-(2|u|+1)}`** under the padded
ensemble. -/
theorem ensemble_dist_frame_append (u : List Bool) (m : ℕ) :
    ensemble.dist (frame u ++ List.replicate m true).length (frame u ++ List.replicate m true) =
      (2 ^ (2 * u.length + 1) : ℝ≥0∞)⁻¹ := by
  have hv : parser.valid (frame u ++ List.replicate m true) = true := valid_frame_append _ _
  have hc : parser.collapse (frame u ++ List.replicate m true) =
      frame u ++ List.replicate m true := by
    rw [HeaderParser.collapse_of_valid _ hv]
    change header _ ++ List.replicate (_ - (header _).length) true = _
    rw [header_frame_append, List.length_append, List.length_replicate, Nat.add_sub_cancel_left]
  have h := parser.ensemble_dist_collapse hv
  rw [hc] at h
  rw [ensemble, h]
  change (2 ^ (header _).length : ℝ≥0∞)⁻¹ = _
  rw [header_frame_append, length_frame]

end PaddedFrame

/-! ### `NE = E` -/

/-- **If `DistNP ⊆ HeurP`, then `NP` is easy on exponentially padded instances.** For `B ∈ NP`,
the distributional problem `(B, PaddedFrame.ensemble)` is in `DistNP`. A word `frame u ++ 1^m` of
length `N` with `2^{|u|} ≤ m` has probability `2^{-(2|u|+1)} ≥ 1/(2N²)`, so the heuristic scheme run
with confidence `2N²` decides `B` on it. -/
theorem expPaddedNPEasy_of_DistNP_subset_HeurP (h : DistNP ⊆ HeurP) : ExpPaddedNPEasy := by
  intro B hB
  have hD : (⟨B, PaddedFrame.ensemble⟩ : DistProblem) ∈ DistNP :=
    mem_DistNP.mpr ⟨hB, PaddedFrame.ensemble_pComp⟩
  obtain ⟨f, hf, hagree⟩ := exists_agree_of_mem_HeurP (h hD) (2 * Polynomial.X ^ 2)
  refine ⟨{x | f x = true}, ⟨f, hf, fun _ => Iff.rfl⟩, fun u m hm => hagree _ ?_⟩
  change _ ≤ PaddedFrame.ensemble.dist _ _
  rw [PaddedFrame.ensemble_dist_frame_append]
  refine ENNReal.inv_le_inv' ?_
  simp only [List.length_append, length_frame, List.length_replicate, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat]
  have h2 : 2 ^ (2 * u.length + 1) ≤ 2 * (2 * u.length + 1 + m) ^ 2 := by
    have hsq : 2 ^ (2 * u.length + 1) = 2 * (2 ^ u.length) ^ 2 := by ring
    rw [hsq]
    exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hm.trans (by omega)) 2)
  exact_mod_cast h2

/-- **If `DistNP ⊆ HeurP`, then `NE ⊆ E`** [Ben-David, Chor, Goldreich and
Luby][BenDavidChorGoldreichLuby1992]. -/
theorem NE_subset_E_of_DistNP_subset_HeurP {α : Type} {enc : α ↪ List Bool}
    (h : DistNP ⊆ HeurP) : NE enc ⊆ E enc :=
  NE_subset_E_of_expPaddedNPEasy (expPaddedNPEasy_of_DistNP_subset_HeurP h)

/-- **If `DistNP ⊆ HeurP`, then `E = NE`** [Ben-David, Chor, Goldreich and
Luby][BenDavidChorGoldreichLuby1992]. -/
theorem E_eq_NE_of_DistNP_subset_HeurP {α : Type} {enc : α ↪ List Bool}
    (h : DistNP ⊆ HeurP) : E enc = NE enc :=
  E_subset_NE.antisymm (NE_subset_E_of_DistNP_subset_HeurP h)

/-- **If `DistNP ⊆ HeurP`, then `EXP = NEXP`**, by the same padding. -/
theorem EXP_eq_NEXP_of_DistNP_subset_HeurP {α : Type} {enc : α ↪ List Bool}
    (h : DistNP ⊆ HeurP) : EXP enc = NEXP enc :=
  EXP_subset_NEXP.antisymm
    (NEXP_subset_EXP_of_expPaddedNPEasy (expPaddedNPEasy_of_DistNP_subset_HeurP h))

/-- **If `DistNP ⊆ AvgP`, then `NE ⊆ E`**: the `AvgP` form of the theorem of Ben-David, Chor,
Goldreich and Luby [Ben-David, Chor, Goldreich and Luby][BenDavidChorGoldreichLuby1992], for
length-indexed ensembles rather than Levin's single distribution. -/
theorem NE_subset_E_of_DistNP_subset_AvgP {α : Type} {enc : α ↪ List Bool}
    (h : DistNP ⊆ AvgP) : NE enc ⊆ E enc :=
  NE_subset_E_of_DistNP_subset_HeurP (h.trans AvgP_subset_HeurP)

/-- **If `DistNP ⊆ AvgP`, then `E = NE`** [Ben-David, Chor, Goldreich and
Luby][BenDavidChorGoldreichLuby1992]. -/
theorem E_eq_NE_of_DistNP_subset_AvgP {α : Type} {enc : α ↪ List Bool}
    (h : DistNP ⊆ AvgP) : E enc = NE enc :=
  E_eq_NE_of_DistNP_subset_HeurP (h.trans AvgP_subset_HeurP)

/-- **If `E ≠ NE`, then some distributional problem in `DistNP` has no polynomial-time heuristic
scheme**: `NP` is hard on average under some polynomial-time computable ensemble. -/
theorem not_DistNP_subset_HeurP_of_E_ne_NE {α : Type} {enc : α ↪ List Bool}
    (h : E enc ≠ NE enc) : ¬DistNP ⊆ HeurP :=
  fun hD => h (E_eq_NE_of_DistNP_subset_HeurP hD)

end Cslib.Complexity
