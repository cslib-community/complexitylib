/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF

/-!
# Universal and Δ-universal hash families

A keyed hash family is a function `h : ι → X → Y` together with a law `seed : PMF ι` of its key,
or seed. Two collision properties of such families are defined here, for an arbitrary seed law:

* `IsUniversalHash seed h ε`: distinct inputs collide with probability at most `ε`. This is an
  `ε`-bounded universal hash function, or `ε`-UHF ([BonehShoup2023], Definition 7.2); for
  `ε = 1 / |Y|` it is the universal family of Carter and Wegman [CarterWegman1979]
  (`Cslib.Probability.IsTwoUniversal`).
* `IsDeltaUniversalHash seed h ε`, for an additive group `Y`: for distinct inputs, every
  difference of their hashes has probability at most `ε`. This is an `ε`-almost-Δ-universal
  family; it is `ε`-almost-XOR-universal (`ε`-AXU) when `Y` is a space of bit strings, and an
  `ε`-bounded difference unpredictable function, or `ε`-DUF ([BonehShoup2023], Definition 7.5).

A Δ-universal family is universal, taking the difference `0`
(`IsDeltaUniversalHash.isUniversalHash`). Strongly universal, that is pairwise independent,
families with uniform seeds are `Cslib.Probability.IsPairwiseIndependentHash`; they are universal
and Δ-universal with `ε = 1 / |Y|` (`CslibFrontier.Probability.PairwiseIndependentHash.Universal`).
A uniformly distributed difference gives the optimal `ε = 1 / |Y|`
(`IsDeltaUniversalHash.of_map_sub_eq_uniform`). Further families are Carter–Wegman polynomial
evaluation (`CslibFrontier.Probability.HashFamily.Polynomial`) and multiply-shift hashing
(`CslibFrontier.Probability.HashFamily.MultiplyShift`).

Probabilities are taken with `PMF.toOuterMeasure` and bounds are extended nonnegative reals.
These are information-theoretic properties; efficient evaluation is a separate matter.

## Main definitions

* `Cslib.Probability.IsUniversalHash`: `ε`-universal families.
* `Cslib.Probability.IsDeltaUniversalHash`: `ε`-almost-Δ-universal families.

## Main results

* `Cslib.Probability.IsDeltaUniversalHash.isUniversalHash`: Δ-universal families are universal.
* `Cslib.Probability.IsUniversalHash.precompose`,
  `Cslib.Probability.IsUniversalHash.precompose_seed`: injective input encodings and
  pushed-forward seeds.
* `Cslib.Probability.IsUniversalHash.sum_ite_toReal_le`: the collision bound as a finite sum.
* `Cslib.Probability.IsDeltaUniversalHash.of_map_sub_eq_uniform`: uniform differences.
* `Cslib.Probability.IsUniversalHash.of_card_le`,
  `Cslib.Probability.IsDeltaUniversalHash.of_card_le`: counting bad seeds of a uniform seed.

## References

* [J. L. Carter, M. N. Wegman, *Universal Classes of Hash Functions*][CarterWegman1979]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.1 and 7.4.
-/

@[expose] public section

namespace Cslib.Probability

open scoped ENNReal

variable {ι ι' X X' Y : Type*}

/-- An `ε`-universal hash family ([BonehShoup2023], Definition 7.2): for distinct inputs `x` and
`x'`, the seed `i` gives `hash i x = hash i x'` with probability at most `ε`. -/
def IsUniversalHash (seed : PMF ι) (hash : ι → X → Y) (ε : ℝ≥0∞) : Prop :=
  ∀ x x', x ≠ x' → seed.toOuterMeasure {i | hash i x = hash i x'} ≤ ε

/-- An `ε`-almost-Δ-universal hash family ([BonehShoup2023], Definition 7.5, where it is called an
`ε`-DUF; `ε`-AXU when the difference is XOR): for distinct inputs `x` and `x'` and every `d`, the
seed `i` gives `hash i x - hash i x' = d` with probability at most `ε`. -/
def IsDeltaUniversalHash [AddGroup Y] (seed : PMF ι) (hash : ι → X → Y) (ε : ℝ≥0∞) :
    Prop :=
  ∀ x x', x ≠ x' → ∀ d, seed.toOuterMeasure {i | hash i x - hash i x' = d} ≤ ε

namespace IsUniversalHash

variable {seed : PMF ι} {hash : ι → X → Y} {ε ε' : ℝ≥0∞}

/-- A family that is `ε`-universal is `ε'`-universal for every `ε' ≥ ε`. -/
theorem mono (hh : IsUniversalHash seed hash ε) (hε : ε ≤ ε') : IsUniversalHash seed hash ε' :=
  fun x x' hx => (hh x x' hx).trans hε

/-- An injective input encoding preserves universality. -/
theorem precompose (hh : IsUniversalHash seed hash ε) {encode : X' → X}
    (hencode : Function.Injective encode) :
    IsUniversalHash seed (fun i x => hash i (encode x)) ε :=
  fun _ _ hx => hh _ _ (hencode.ne hx)

/-- Universality for a pushed-forward seed law is universality of the precomposed family. -/
theorem precompose_seed (seed : PMF ι') (prepare : ι' → ι)
    (hh : IsUniversalHash (seed.map prepare) hash ε) :
    IsUniversalHash seed (fun i => hash (prepare i)) ε := fun x x' hx => by
  have := hh x x' hx
  rwa [PMF.toOuterMeasure_map_apply] at this

open Classical in
/-- On a finite seed space, the collision probability of distinct inputs is a sum of seed masses
bounded by `ε`. -/
theorem sum_ite_toReal_le [Fintype ι] (hh : IsUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    {x x' : X}
    (hx : x ≠ x') : (∑ i, if hash i x = hash i x' then (seed i).toReal else 0) ≤ ε.toReal := by
  classical
  have h := ENNReal.toReal_mono hε (hh x x' hx)
  rw [PMF.toOuterMeasure_apply_toReal] at h
  simpa only [Set.mem_ofPred_eq] using h

open Classical in
/-- A collision bound stated as a finite sum of seed masses gives universality. -/
theorem of_sum_ite_toReal_le [Fintype ι] {ε : ℝ}
    (hh : ∀ x x', x ≠ x' → (∑ i, if hash i x = hash i x' then (seed i).toReal else 0) ≤ ε) :
    IsUniversalHash seed hash (ENNReal.ofReal ε) := fun x x' hx => by
  classical
  rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top seed _),
    PMF.toOuterMeasure_apply_toReal]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Set.mem_ofPred_eq] using hh x x' hx)

/-- With a uniform seed, a bound `c` on the number of seeds on which two distinct inputs
collide gives `c / |ι|`-universality. -/
theorem of_card_le [Fintype ι] [Nonempty ι] [DecidableEq Y] {c : ℕ}
    (hc : ∀ x x', x ≠ x' → (Finset.univ.filter fun i => hash i x = hash i x').card ≤ c) :
    IsUniversalHash (PMF.uniformOfFintype ι) hash (c / Fintype.card ι) := fun x x' hx => by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
  gcongr
  convert hc x x' hx

end IsUniversalHash

namespace IsDeltaUniversalHash

variable [AddGroup Y] {seed : PMF ι} {hash : ι → X → Y} {ε ε' : ℝ≥0∞}

/-- A Δ-universal family is universal with the same bound: take the difference `0`. -/
theorem isUniversalHash (hh : IsDeltaUniversalHash seed hash ε) : IsUniversalHash seed hash ε :=
  fun x x' hx => by
    simpa only [sub_eq_zero] using hh x x' hx 0

/-- A family that is `ε`-Δ-universal is `ε'`-Δ-universal for every `ε' ≥ ε`. -/
theorem mono (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≤ ε') :
    IsDeltaUniversalHash seed hash ε' :=
  fun x x' hx d => (hh x x' hx d).trans hε

/-- An injective input encoding preserves Δ-universality. -/
theorem precompose (hh : IsDeltaUniversalHash seed hash ε) {encode : X' → X}
    (hencode : Function.Injective encode) :
    IsDeltaUniversalHash seed (fun i x => hash i (encode x)) ε :=
  fun _ _ hx => hh _ _ (hencode.ne hx)

/-- Δ-universality for a pushed-forward seed law is Δ-universality of the precomposed family. -/
theorem precompose_seed (seed : PMF ι') (prepare : ι' → ι)
    (hh : IsDeltaUniversalHash (seed.map prepare) hash ε) :
    IsDeltaUniversalHash seed (fun i => hash (prepare i)) ε := fun x x' hx d => by
  have := hh x x' hx d
  rwa [PMF.toOuterMeasure_map_apply] at this

/-- If distinct inputs always have a uniformly distributed difference of hashes, the family is
`1 / |Y|`-Δ-universal, the least possible bound. -/
theorem of_map_sub_eq_uniform [Fintype Y] [Nonempty Y]
    (hh : ∀ x x', x ≠ x' → seed.map (fun i => hash i x - hash i x') = PMF.uniformOfFintype Y) :
    IsDeltaUniversalHash seed hash (Fintype.card Y : ℝ≥0∞)⁻¹ := fun x x' hx d => by
  have hpre : {i | hash i x - hash i x' = d} = (fun i => hash i x - hash i x') ⁻¹' {d} := rfl
  rw [hpre, ← PMF.toOuterMeasure_map_apply, hh x x' hx, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply]

/-- With a uniform seed, a bound `c` on the number of seeds giving any one difference of the
hashes of two distinct inputs gives `c / |ι|`-Δ-universality. -/
theorem of_card_le [Fintype ι] [Nonempty ι] [DecidableEq Y] {c : ℕ}
    (hc : ∀ x x', x ≠ x' → ∀ d,
      (Finset.univ.filter fun i => hash i x - hash i x' = d).card ≤ c) :
    IsDeltaUniversalHash (PMF.uniformOfFintype ι) hash (c / Fintype.card ι) :=
  fun x x' hx d => by
    classical
    rw [PMF.toOuterMeasure_uniformOfFintype, div_eq_mul_inv]
    gcongr
    convert hc x x' hx d

end IsDeltaUniversalHash

end Cslib.Probability
