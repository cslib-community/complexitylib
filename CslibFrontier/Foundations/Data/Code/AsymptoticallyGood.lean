/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Asymptotically good code families

A family of codes `C s : Set (ι s → α)` over a finite nontrivial alphabet `α` is *asymptotically
good* (`Cslib.Code.IsAsymptoticallyGood`) if its block lengths `|ι s|` grow without bound while its
rates and relative minimum distances stay bounded away from zero [Justesen1972],
[GuruswamiRudraSudan2019], [MacWilliams and Sloane, Chapter 17][MacWilliamsSloane1977]. In integer
form, there are positive natural numbers `R` and `Δ` such that every code `C s` in the family has at
least `|α| ^ k` codewords for some `k` with `|ι s| ≤ R * k` (rate `k / |ι s| ≥ 1 / R`) and minimum
distance `d` with `|ι s| ≤ Δ * d` (relative distance `d / |ι s| ≥ 1 / Δ`).

## Main definitions

* `Cslib.Code.IsAsymptoticallyGood`: asymptotically good code families.

## References

* [J. Justesen, *Class of constructive asymptotically good algebraic codes*][Justesen1972]
* [V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*][GuruswamiRudraSudan2019]
* [F. J. MacWilliams, N. J. A. Sloane, *The Theory of Error-Correcting Codes*]
  [MacWilliamsSloane1977]
-/

@[expose] public section

namespace Cslib.Code

/-- A family of codes `C s : Set (ι s → α)` over a nontrivial alphabet `α` is *asymptotically good*
if its block lengths `|ι s|` grow without bound and its rates and relative distances are bounded
away from zero: for some positive natural numbers `R` and `Δ`, every `C s` has at least `|α| ^ k`
codewords for a dimension `k` with `|ι s| ≤ R * k` (rate at least `1 / R`) and minimum distance `d`
with `|ι s| ≤ Δ * d` (relative distance at least `1 / Δ`). -/
structure IsAsymptoticallyGood {σ : Type*} {ι : σ → Type*} [∀ s, Fintype (ι s)]
    {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α] (C : ∀ s, Set (ι s → α)) : Prop where
  /-- The block lengths grow without bound. -/
  exists_le_card : ∀ N, ∃ s, N ≤ Fintype.card (ι s)
  /-- The rate is bounded away from zero: for some `R : ℕ` with `0 < R`, every code in the family
  has at least `|α| ^ k` codewords for a dimension `k` with `|ι s| ≤ R * k`. -/
  exists_rate : ∃ R : ℕ, 0 < R ∧ ∀ s, ∃ k, Fintype.card (ι s) ≤ R * k ∧
    Fintype.card α ^ k ≤ Nat.card (C s)
  /-- The relative distance is bounded away from zero: for some `Δ : ℕ` with `0 < Δ`, every code in
  the family has minimum distance `d` with `|ι s| ≤ Δ * d`. -/
  exists_minDist : ∃ Δ : ℕ, 0 < Δ ∧ ∀ s, (Fintype.card (ι s) : ℕ∞) ≤ Δ * minDist (C s)

end Cslib.Code
