/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Extractor.TwoSource
public import Mathlib.Algebra.Ring.BooleanRing
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Raz's Extractor

Raz's two-source extractor for one source with min-entropy > n/2 and a second source with
logarithmic min-entropy.

## Main definitions

* `Cslib.Probability.razExtractor`: The Raz extractor function.
* `Cslib.Probability.IsRazMatrixFamily`: The rank condition on the matrix family.

## Main theorem statement

* `Cslib.Probability.RazExtractorTheorem`: The correctness statement of Raz's extractor,
  formulated as a `Prop` to avoid `sorry` while the proof is being developed.
-/

public section

namespace Cslib.Probability

open Finset Cslib.Probability.PMF Matrix

variable {ι Y : Type*} [Fintype ι] [Fintype Y] [DecidableEq ι]

/-- The condition on the matrix family for Raz's extractor: any non-trivial XOR sum
of up to `2 * t` matrices has rank at least `(1 - δ) * n`. -/
def IsRazMatrixFamily (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (δ : ℝ) : Prop :=
  ∀ s : Finset Y, 0 < s.card → s.card ≤ 2 * t →
    (1 - δ) * Fintype.card ι ≤ (∑ y ∈ s, M y).rank

/-- The Raz extractor function. -/
def razExtractor (M : Y → Matrix ι ι (ZMod 2)) (x : (ι → ZMod 2) × (ι → ZMod 2))
    (y : Y) : ZMod 2 :=
  x.1 ⬝ᵥ (M y *ᵥ x.2)

/-- The statement that Raz's extractor is a two-source extractor.
Defined as a `Prop` to avoid `sorry` before the proof is complete. -/
def RazExtractorTheorem (M : Y → Matrix ι ι (ZMod 2)) (t : ℕ) (δ : ℝ) (C : ℝ) (ε : ℝ)
    (_hM : IsRazMatrixFamily M t δ) (k₁ k₂ : ℝ)
    (_hk₁ : (1 / 2 + δ) * Fintype.card ι ≤ k₁)
    (_hk₂ : C * Real.log (Fintype.card ι) ≤ k₂) : Prop :=
  IsTwoSourceExtractor (fun x y => razExtractor M x y) k₁ k₂ ε

end Cslib.Probability
