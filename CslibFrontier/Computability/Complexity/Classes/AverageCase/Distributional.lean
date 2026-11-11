/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Ensemble
public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Tactic.PolyTime

/-!
# Distributional problems and the classes `AvgP`, `HeurP` and `DistNP`

A distributional problem `L : Cslib.Complexity.DistProblem` pairs a language of binary words with
an ensemble (`Cslib.Complexity.Ensemble`) [Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006].
This file defines the deterministic average-case classes of [Bogdanov and Trevisan,
§2.2][BogdanovTrevisan2006].

* An **errorless heuristic scheme** (`Cslib.Complexity.DistProblem.IsErrorlessScheme`,
  [Bogdanov and Trevisan, Definition 6][BogdanovTrevisan2006]) receives an instance `x` and a
  unary confidence parameter `k`, outputs `some b` or the failure symbol `none`, never answers
  wrongly on the support of the ensemble, and fails with probability at most `1/(k+1)` on every
  length. `AvgP` is the class of distributional problems with a polynomial-time errorless scheme
  [Bogdanov and Trevisan, Definition 8][BogdanovTrevisan2006].
* A **heuristic scheme** (`Cslib.Complexity.DistProblem.IsHeuristicScheme`) may answer wrongly,
  with probability at most `1/(k+1)`; `HeurP` is the class of distributional problems with a
  polynomial-time heuristic scheme [Bogdanov and Trevisan, Definition 11][BogdanovTrevisan2006].
* For a failure bound `δ : ℕ → ℝ≥0∞`, `AvgDeltaP δ` and `HeurDeltaP δ` are the classes
  `Avg_δ P` and `Heur_δ P` of problems solved by a single polynomial-time errorless, respectively
  heuristic, algorithm with failure probability at most `δ n` on length `n`
  [Bogdanov and Trevisan, Definitions 9 and 11][BogdanovTrevisan2006]; heuristic algorithms are
  [Bogdanov and Trevisan, Definition 10][BogdanovTrevisan2006].
* `DistNP` pairs `NP` languages with polynomial-time computable ensembles and `SampNP` with
  polynomial-time samplable ensembles [Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006].

## Conventions

The source parameterizes a scheme by a failure bound `δ > 0` and allows running time polynomial in
`n / δ`. Here `δ = 1/(k+1)` with `k` written in unary, so "polynomial in `n` and `k`" is the same
resource bound up to polynomial change. Schemes are total functions computed in polynomial time on
all inputs, the standard convention after clocking. Correctness is required only on the support of
the ensemble: an instance of probability zero carries no constraint, as in the source.

The source's `AvgP` is the errorless-heuristic class; Levin's original formulation through the
moments `E[t(x)^ε]` of a running time is equivalent to it on instances of positive probability
[Bogdanov and Trevisan, Proposition 7][BogdanovTrevisan2006], and is not formalized here.

## Main definitions

* `Cslib.Complexity.DistProblem`, with the predicates
  `Cslib.Complexity.DistProblem.IsErrorlessScheme`,
  `Cslib.Complexity.DistProblem.IsHeuristicScheme`,
  `Cslib.Complexity.DistProblem.IsErrorlessAlgorithm` and
  `Cslib.Complexity.DistProblem.IsHeuristicAlgorithm`.
* `Cslib.Complexity.AvgP`, `Cslib.Complexity.HeurP`, `Cslib.Complexity.AvgDeltaP`,
  `Cslib.Complexity.HeurDeltaP`, `Cslib.Complexity.DistNP`, `Cslib.Complexity.SampNP`.

## Main results

* `Cslib.Complexity.mem_AvgP_of_mem_P`: a language in `P` is in `AvgP` under every ensemble.
* `Cslib.Complexity.AvgP_subset_HeurP`: errorless schemes yield heuristic schemes.
* `Cslib.Complexity.AvgP_subset_AvgDeltaP`: an errorless scheme run with confidence `q(n)` is an
  errorless algorithm with failure `1/(q(n)+1)`; similarly
  `Cslib.Complexity.HeurP_subset_HeurDeltaP`.
* `Cslib.Complexity.AvgDeltaP_subset_HeurDeltaP`.

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-- A distributional problem: a language of binary words together with an ensemble of
distributions on instances [Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006]. -/
structure DistProblem where
  /-- The language to decide. -/
  lang : Set (List Bool)
  /-- The distribution of instances of each length. -/
  ens : Ensemble

namespace DistProblem

/-- `A` is a polynomial-time **errorless heuristic scheme** for `L`
[Bogdanov and Trevisan, Definition 6][BogdanovTrevisan2006], with failure bound `δ = 1/(k+1)`
for the unary parameter `k`: on the support it never answers wrongly, and on every length it fails
(outputs `none`) with probability at most `1/(k+1)`. -/
structure IsErrorlessScheme (L : DistProblem) (A : List Bool × ℕ → Option Bool) : Prop where
  /-- The scheme runs in time polynomial in `|x|` and `k`. -/
  polyTime : ComputableInPolyTime A (encPair encBits encUnary) (encOption encBool)
  /-- Every answer given on the support is correct. -/
  correct : ∀ n x k b, x ∈ (L.ens.dist n).support → A (x, k) = some b → (b = true ↔ x ∈ L.lang)
  /-- The failure probability on length `n` is at most `1/(k+1)`. -/
  failure_le : ∀ n k,
    (L.ens.dist n).toOuterMeasure {x | A (x, k) = none} ≤ ((k + 1 : ℕ) : ℝ≥0∞)⁻¹

/-- `A` is a polynomial-time **heuristic scheme** for `L`
[Bogdanov and Trevisan, Definition 11][BogdanovTrevisan2006]: on every length it answers wrongly
with probability at most `1/(k+1)` for the unary parameter `k`. -/
structure IsHeuristicScheme (L : DistProblem) (A : List Bool × ℕ → Bool) : Prop where
  /-- The scheme runs in time polynomial in `|x|` and `k`. -/
  polyTime : ComputableInPolyTime A (encPair encBits encUnary) encBool
  /-- The error probability on length `n` is at most `1/(k+1)`. -/
  error_le : ∀ n k,
    (L.ens.dist n).toOuterMeasure {x | ¬(A (x, k) = true ↔ x ∈ L.lang)} ≤
      ((k + 1 : ℕ) : ℝ≥0∞)⁻¹

/-- `A` is a polynomial-time **errorless heuristic algorithm** for `L` with failure probability `δ`
[Bogdanov and Trevisan, Definition 9][BogdanovTrevisan2006]. -/
structure IsErrorlessAlgorithm (L : DistProblem) (δ : ℕ → ℝ≥0∞)
    (A : List Bool → Option Bool) : Prop where
  /-- The algorithm runs in polynomial time. -/
  polyTime : ComputableInPolyTime A encBits (encOption encBool)
  /-- Every answer given on the support is correct. -/
  correct : ∀ n x b, x ∈ (L.ens.dist n).support → A x = some b → (b = true ↔ x ∈ L.lang)
  /-- The failure probability on length `n` is at most `δ n`. -/
  failure_le : ∀ n, (L.ens.dist n).toOuterMeasure {x | A x = none} ≤ δ n

/-- `A` is a polynomial-time **heuristic algorithm** for `L` with error probability `δ`
[Bogdanov and Trevisan, Definition 10][BogdanovTrevisan2006]. -/
structure IsHeuristicAlgorithm (L : DistProblem) (δ : ℕ → ℝ≥0∞) (A : List Bool → Bool) :
    Prop where
  /-- The algorithm runs in polynomial time. -/
  polyTime : ComputableInPolyTime A encBits encBool
  /-- The error probability on length `n` is at most `δ n`. -/
  error_le : ∀ n, (L.ens.dist n).toOuterMeasure {x | ¬(A x = true ↔ x ∈ L.lang)} ≤ δ n

end DistProblem

open DistProblem

/-- **`AvgP`**: distributional problems with a polynomial-time errorless heuristic scheme
[Bogdanov and Trevisan, Definition 8][BogdanovTrevisan2006]. -/
@[expose] def AvgP : Set DistProblem := {L | ∃ A, L.IsErrorlessScheme A}

/-- **`HeurP`**: distributional problems with a polynomial-time heuristic scheme
[Bogdanov and Trevisan, Definition 11][BogdanovTrevisan2006]. -/
@[expose] def HeurP : Set DistProblem := {L | ∃ A, L.IsHeuristicScheme A}

/-- **`Avg_δ P`**: distributional problems with a polynomial-time errorless heuristic algorithm of
failure probability `δ` [Bogdanov and Trevisan, Definition 9][BogdanovTrevisan2006]. -/
@[expose] def AvgDeltaP (δ : ℕ → ℝ≥0∞) : Set DistProblem :=
  {L | ∃ A, L.IsErrorlessAlgorithm δ A}

/-- **`Heur_δ P`**: distributional problems with a polynomial-time heuristic algorithm of error
probability `δ` [Bogdanov and Trevisan, Definition 11][BogdanovTrevisan2006]. -/
@[expose] def HeurDeltaP (δ : ℕ → ℝ≥0∞) : Set DistProblem :=
  {L | ∃ A, L.IsHeuristicAlgorithm δ A}

/-- **`DistNP`**: `NP` languages with polynomial-time computable ensembles
[Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006]. -/
@[expose] def DistNP : Set DistProblem := {L | L.lang ∈ NP encBits ∧ L.ens.PComp}

/-- **`SampNP`**: `NP` languages with polynomial-time samplable ensembles
[Bogdanov and Trevisan, §2.1][BogdanovTrevisan2006]. -/
@[expose] def SampNP : Set DistProblem := {L | L.lang ∈ NP encBits ∧ L.ens.PSamp}

theorem mem_AvgP {L : DistProblem} : L ∈ AvgP ↔ ∃ A, L.IsErrorlessScheme A := Iff.rfl

theorem mem_HeurP {L : DistProblem} : L ∈ HeurP ↔ ∃ A, L.IsHeuristicScheme A := Iff.rfl

theorem mem_AvgDeltaP {L : DistProblem} {δ : ℕ → ℝ≥0∞} :
    L ∈ AvgDeltaP δ ↔ ∃ A, L.IsErrorlessAlgorithm δ A := Iff.rfl

theorem mem_HeurDeltaP {L : DistProblem} {δ : ℕ → ℝ≥0∞} :
    L ∈ HeurDeltaP δ ↔ ∃ A, L.IsHeuristicAlgorithm δ A := Iff.rfl

theorem mem_DistNP {L : DistProblem} : L ∈ DistNP ↔ L.lang ∈ NP encBits ∧ L.ens.PComp := Iff.rfl

theorem mem_SampNP {L : DistProblem} : L ∈ SampNP ↔ L.lang ∈ NP encBits ∧ L.ens.PSamp :=
  Iff.rfl

/-- A language decidable in polynomial time is in `AvgP` under every ensemble. -/
theorem mem_AvgP_of_mem_P {L : DistProblem} (h : L.lang ∈ P encBits) : L ∈ AvgP := by
  obtain ⟨g, hg, hL⟩ := h
  refine ⟨fun q => some (g q.1), ⟨?_, ?_, ?_⟩⟩
  · polytime
  · intro n x k b _ hb
    cases hb
    exact (hL x).symm
  · intro n k
    simp

/-- Errorless heuristic schemes yield heuristic schemes: answer `false` on failure. -/
theorem AvgP_subset_HeurP : AvgP ⊆ HeurP := by
  rintro L ⟨A, hA⟩
  have hpt := hA.polyTime
  refine ⟨fun q => (A q).getD false, ⟨?_, ?_⟩⟩
  · polytime
  · intro n k
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (hA.failure_le n k)
    rintro x ⟨hx, hsupp⟩
    simp only [Set.mem_ofPred_eq] at hx ⊢
    cases hAx : A (x, k) with
    | none => rfl
    | some b =>
      rw [hAx, Option.getD_some] at hx
      exact absurd (hA.correct n x k b hsupp hAx) hx

/-- An errorless heuristic scheme run with confidence parameter `q(n)` on length `n` is an
errorless heuristic algorithm with failure probability `1/(q(n)+1)`. -/
theorem AvgP_subset_AvgDeltaP (q : Polynomial ℕ) :
    AvgP ⊆ AvgDeltaP (fun n => ((q.eval n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
  rintro L ⟨A, hA⟩
  have hpt := hA.polyTime
  refine ⟨fun x => A (x, q.eval x.length), ⟨?_, ?_, ?_⟩⟩
  · polytime
  · intro n x b hx hb
    exact hA.correct n x _ b hx hb
  · intro n
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (hA.failure_le n (q.eval n))
    rintro x ⟨hx, hsupp⟩
    simpa only [Set.mem_ofPred_eq, L.ens.length_eq n x hsupp] using hx

/-- A heuristic scheme run with confidence parameter `q(n)` on length `n` is a heuristic algorithm
with error probability `1/(q(n)+1)`. -/
theorem HeurP_subset_HeurDeltaP (q : Polynomial ℕ) :
    HeurP ⊆ HeurDeltaP (fun n => ((q.eval n + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
  rintro L ⟨A, hA⟩
  have hpt := hA.polyTime
  refine ⟨fun x => A (x, q.eval x.length), ⟨?_, ?_⟩⟩
  · polytime
  · intro n
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (hA.error_le n (q.eval n))
    rintro x ⟨hx, hsupp⟩
    simpa only [Set.mem_ofPred_eq, L.ens.length_eq n x hsupp] using hx

/-- Errorless heuristic algorithms yield heuristic algorithms with the same failure bound. -/
theorem AvgDeltaP_subset_HeurDeltaP (δ : ℕ → ℝ≥0∞) : AvgDeltaP δ ⊆ HeurDeltaP δ := by
  rintro L ⟨A, hA⟩
  have hpt := hA.polyTime
  refine ⟨fun x => (A x).getD false, ⟨?_, ?_⟩⟩
  · polytime
  · intro n
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (hA.failure_le n)
    rintro x ⟨hx, hsupp⟩
    simp only [Set.mem_ofPred_eq] at hx ⊢
    cases hAx : A x with
    | none => rfl
    | some b =>
      rw [hAx, Option.getD_some] at hx
      exact absurd (hA.correct n x b hsupp hAx) hx

end Cslib.Complexity
