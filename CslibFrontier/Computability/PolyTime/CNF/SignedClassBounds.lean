/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PolyTime.CNF.IndependentDominationInterval

/-!
# Binary signed class-interval normalization

Normalize every labeled class interval, retaining order and contradictions. A negative upper
bound becomes the impossible natural interval [1,0]. No magnitude is expanded into unary.
This is a frontend stage for [ChenJiangZhu2027], Theorem 7.3 (PDF p.25), not a complete signed
partition counter or its resource composition.

## Main definitions

* `normalize`: actual binary list traversal for varying signed intervals.

## Main results

* `normalize_polytime`: native binary construction, including all output writes.
* `normalize_ofFn`: exact original label order for canonical inputs.
* `bounds_iff`: simultaneous equivalence for arbitrary nonnegative class cardinalities.
-/

public section

namespace Cslib.Logic.PL.SignedClassBounds

open Turing.MultiTapeTM

/-- A signed binary lower/upper pair, with the lower integer framed. -/
abbrev encInterval : (ℤ × ℤ) ↪ List Bool := encPair encIntBin encIntBin
/-- Original ordered list of signed binary class-bound pairs. -/
abbrev encInput : List (ℤ × ℤ) ↪ List Bool := encList encInterval
/-- Ordered list of natural binary lower/upper pairs, each pair and list element framed. -/
abbrev encOutput : List (ℕ × ℕ) ↪ List Bool := encList (encPair encNat encNat)
/-- Normalize one actual signed interval without assuming either bound is nonnegative. -/
@[expose] def pair (p : ℤ × ℤ) : ℕ × ℕ :=
  (IndependentDominationInterval.Signed.lowerNat p.1 p.2,
    IndependentDominationInterval.Signed.upperNat p.2)
/-- Actual ordered traversal, accepting empty lists and arbitrarily large binary integers. -/
@[expose] def normalize (xs : List (ℤ × ℤ)) : List (ℕ × ℕ) := xs.map pair

/-- Reuse the actual scalar signed normalizer, including its sign tests and binary conversions. -/
theorem pair_polytime : ComputableInPolyTime pair encInterval (encPair encNat encNat) := by
  have hprep : ComputableInPolyTime
      (fun p : ℤ × ℤ => ((0, []), p.1, p.2)) encInterval
      IndependentDominationInterval.Signed.encInput := by
    unfold encInterval IndependentDominationInterval.Signed.encInput
    fun_prop
  have h := IndependentDominationInterval.Signed.normalize_polytime.comp hprep
  exact h.snd'

/-- List traversal and all framed binary output writes have a native polynomial-time certificate. -/
theorem normalize_polytime : ComputableInPolyTime normalize encInput encOutput :=
  ComputableInPolyTime.map pair_polytime

/-- Every original label remains in exactly its original position. -/
theorem normalize_ofFn {q : ℕ} (lo hi : Fin q → ℤ) :
    normalize (List.ofFn fun i => (lo i, hi i)) = List.ofFn fun i =>
      (IndependentDominationInterval.Signed.lowerNat (lo i) (hi i),
        IndependentDominationInterval.Signed.upperNat (hi i)) := by
  simp only [normalize, List.map_ofFn, Function.comp_def, pair]

/-- Preserve every class-size condition, including empty classes and contradictions. -/
theorem bounds_iff {q : ℕ} (lo hi : Fin q → ℤ) (size : Fin q → ℕ) :
    (∀ i, (pair (lo i, hi i)).1 ≤ size i ∧ size i ≤ (pair (lo i, hi i)).2) ↔
      ∀ i, lo i ≤ (size i : ℤ) ∧ (size i : ℤ) ≤ hi i :=
  forall_congr' fun i => IndependentDominationInterval.Signed.bounds_iff (lo i) (hi i) (size i)

end Cslib.Logic.PL.SignedClassBounds
