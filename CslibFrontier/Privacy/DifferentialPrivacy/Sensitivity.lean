/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic

/-!
# Sensitivity of queries

The sensitivity of a real-valued query `q : D → ℝ` with respect to an adjacency relation `Adj` on
datasets is the largest change `|q x - q y|` between adjacent datasets [DworkRoth2014,
Definition 3.1], the `ℓ₁`-sensitivity of a one-dimensional query. Privacy mechanisms take an upper
bound on it as a hypothesis: `Sensitivity Adj q Δ` says that `|q x - q y| ≤ Δ` whenever
`Adj x y`. For an integer-valued query, apply it to the cast `fun x => (q x : ℝ)`.

The exponential mechanism scores each outcome `r` with a utility `u x r` and needs a bound that
holds for every outcome at once, the sensitivity `Δu` of [DworkRoth2014, §3.4]:
`PointwiseSensitivity Adj u Δ` says that `|u x r - u y r| ≤ Δ` whenever `Adj x y`, for every `r`.
`pointwiseSensitivity_iff` restates it as a bound on each section `fun x => u x r`. Read with
`R = Fin k`, it bounds a vector-valued query `F : D → Fin k → ℝ` coordinatewise, its
`ℓ∞`-sensitivity; Dwork and Roth's Definition 3.1 measures vector-valued queries in `ℓ₁` instead.

As with `Cslib.Privacy.DifferentiallyPrivate`, the adjacency relation is a parameter, and the
definitions quantify over ordered pairs.

## Main definitions

* `Cslib.Privacy.Sensitivity`: the query `q` has sensitivity at most `Δ`.
* `Cslib.Privacy.PointwiseSensitivity`: the utility `u` has sensitivity at most `Δ` in the
  dataset, uniformly in the outcome.

## Main results

* `Cslib.Privacy.Sensitivity.mono`, `Cslib.Privacy.PointwiseSensitivity.mono`: a sensitivity bound
  may be raised.
* `Cslib.Privacy.pointwiseSensitivity_iff`: pointwise sensitivity is sensitivity of every section.

## References

* [DworkRoth2014]
-/

public section

namespace Cslib.Privacy

universe u v

variable {D : Type u} {R : Type v}

/-- The query `q` has sensitivity at most `Δ` with respect to the adjacency relation `Adj`:
`|q x - q y| ≤ Δ` for all adjacent datasets `x`, `y` [DworkRoth2014, Definition 3.1]. -/
@[expose] def Sensitivity (Adj : D → D → Prop) (q : D → ℝ) (Δ : ℝ) : Prop :=
  ∀ ⦃x y⦄, Adj x y → |q x - q y| ≤ Δ

/-- The utility score `u` has sensitivity at most `Δ` in the dataset, uniformly in the outcome:
`|u x r - u y r| ≤ Δ` for all adjacent datasets `x`, `y` and every outcome `r`. This is the
sensitivity `Δu` of the exponential mechanism [DworkRoth2014, §3.4]. -/
@[expose] def PointwiseSensitivity (Adj : D → D → Prop) (u : D → R → ℝ) (Δ : ℝ) : Prop :=
  ∀ ⦃x y⦄, Adj x y → ∀ r, |u x r - u y r| ≤ Δ

variable {Adj : D → D → Prop} {Δ Δ' : ℝ}

/-- A sensitivity bound may be raised. -/
theorem Sensitivity.mono {q : D → ℝ} (h : Sensitivity Adj q Δ) (hΔ : Δ ≤ Δ') :
    Sensitivity Adj q Δ' :=
  fun _ _ hxy => (h hxy).trans hΔ

/-- A pointwise sensitivity bound may be raised. -/
theorem PointwiseSensitivity.mono {u : D → R → ℝ} (h : PointwiseSensitivity Adj u Δ)
    (hΔ : Δ ≤ Δ') : PointwiseSensitivity Adj u Δ' :=
  fun _ _ hxy r => (h hxy r).trans hΔ

/-- A utility score has pointwise sensitivity at most `Δ` exactly when each of its sections
`fun x => u x r` has sensitivity at most `Δ`. -/
theorem pointwiseSensitivity_iff {u : D → R → ℝ} :
    PointwiseSensitivity Adj u Δ ↔ ∀ r, Sensitivity Adj (fun x => u x r) Δ :=
  ⟨fun h r _ _ hxy => h hxy r, fun h _ _ hxy r => h r hxy⟩

end Cslib.Privacy
