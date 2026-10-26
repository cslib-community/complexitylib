/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.CorrelatedSampling
import Complexity.Probability.PMF.Event
import Complexity.Probability.StatisticalDistance
import Complexity.Probability.StatisticalDistance.Coupling

/-!
# Local embedding by correlated sampling

Alice holds `x`, Bob holds `y`, and `(x, y)` is drawn from `P`. They want to extend `(x, y)` by a
common value `s` drawn from the kernel `K (x, y)`, but Alice only knows a kernel `KX x` and Bob only
knows `KY y`. Using correlated sampling, each samples from his own kernel with shared randomness
(`Cslib.Probability.CorrelatedSampling.localSample`). The result `(x, y, s_A, s_B)` is within
statistical distance `2 ε₁ + 2 ε₂` of `(x, y, s, s)`, where `ε₁` and `ε₂` are the average distances
of `KX x` and `KY y` from `K (x, y)` (`dist_embed_le`). With `K` the conditional distribution of
`S` given `(X, Y)` and `KX`, `KY` the conditional distributions given `X` and `Y`, this is
Holenstein's embedding lemma [Holenstein, Lemma 8][Holenstein2009]: `(X, Y)` is
`1 - 2ε₁ - 2ε₂`-embeddable in `(XS, YS)`.

## Main definitions

* `Cslib.Probability.CorrelatedSampling.localSample`: Alice and Bob sample from their own kernels
  with shared randomness.

## Main results

* `Cslib.Probability.CorrelatedSampling.dist_localSample_le`: for fixed inputs, the two local
  samples are within `2 δ₁ + 2 δ₂` of a common sample of `K (x, y)`.
* `Cslib.Probability.CorrelatedSampling.dist_embed_le`: Holenstein's embedding lemma.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.Probability.CorrelatedSampling

open Finset
open scoped Cslib.Probability.PMF

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

/-- The distributions of the embedding: Alice's kernel, Bob's kernel, and the target kernel. -/
def embedFamily (KX : X → PMF S) (KY : Y → PMF S) (K : X × Y → PMF S) :
    X ⊕ Y ⊕ (X × Y) → PMF S
  | .inl x => KX x
  | .inr (.inl y) => KY y
  | .inr (.inr xy) => K xy

/-- Alice samples from `KX x` and Bob from `KY y`, with shared randomness. The target kernel `K`
only shapes the shared randomness; neither party needs to know the other's input. -/
noncomputable def localSample (KX : X → PMF S) (KY : Y → PMF S) (K : X × Y → PMF S) (x : X)
    (y : Y) : PMF (S × S) :=
  (shared (embedFamily KX KY K)).map fun l =>
    (sample (embedFamily KX KY K) (.inl x) l, sample (embedFamily KX KY K) (.inr (.inl y)) l)

/-- For fixed inputs, the two local samples are within `2 δ₁ + 2 δ₂` of a common sample of
`K (x, y)`, where `δ₁` and `δ₂` are the distances of `KX x` and `KY y` from `K (x, y)`. -/
theorem dist_localSample_le (KX : X → PMF S) (KY : Y → PMF S) (K : X × Y → PMF S) (x : X)
    (y : Y) :
    dist (localSample KX KY K x y) ((K (x, y)).map fun s => (s, s)) ≤
      2 * dist (KX x) (K (x, y)) + 2 * dist (KY y) (K (x, y)) := by
  classical
  set F := embedFamily KX KY K
  set sA := sample F (.inl x)
  set sB := sample F (.inr (.inl y))
  set sAB := sample F (.inr (.inr (x, y)))
  have hK : (K (x, y)).map (fun s => (s, s)) = (shared F).map fun l => (sAB l, sAB l) :=
    calc (K (x, y)).map (fun s => (s, s))
        = (F (.inr (.inr (x, y)))).map (fun s => (s, s)) := rfl
      _ = ((shared F).map sAB).map (fun s => (s, s)) := by rw [map_sample]
      _ = (shared F).map fun l => (sAB l, sAB l) := PMF.map_comp _ _ _
  rw [hK, localSample]
  refine (Cslib.Probability.PMF.dist_map_map_le _ _ _).trans ?_
  have hsub : {l | (sA l, sB l) ≠ (sAB l, sAB l)} ⊆
      {l | sample F (.inl x) l ≠ sample F (.inr (.inr (x, y))) l} ∪
        {l | sample F (.inr (.inl y)) l ≠ sample F (.inr (.inr (x, y))) l} := by
    intro l hl
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hl (Prod.ext h.1 h.2)
  have hA := disagree_le (P := F) (.inl x) (.inr (.inr (x, y)))
  have hB := disagree_le (P := F) (.inr (.inl y)) (.inr (.inr (x, y)))
  exact (ENNReal.toReal_le_add
    ((MeasureTheory.measure_mono (μ := (shared F).toOuterMeasure) hsub).trans
      (MeasureTheory.measure_union_le _ _))
    (PMF.toOuterMeasure_ne_top _ _) (PMF.toOuterMeasure_ne_top _ _)).trans
      (add_le_add hA hB)

/-- **Holenstein's embedding lemma** [Holenstein, Lemma 8][Holenstein2009]. Draw `(x, y)` from `P`.
If Alice and Bob sample from their own kernels with shared randomness, the result `(x, y, s_A, s_B)`
is within statistical distance `2 ε₁ + 2 ε₂` of `(x, y, s, s)` with `s` drawn from `K (x, y)`, where
`ε₁` and `ε₂` are the distances of `P ⊗ KX` and `P ⊗ KY` from `P ⊗ K`. -/
theorem dist_embed_le (P : PMF (X × Y)) (KX : X → PMF S) (KY : Y → PMF S) (K : X × Y → PMF S) :
    dist (P.bind fun xy => (localSample KX KY K xy.1 xy.2).map (xy, ·))
        (P.bind fun xy => ((K xy).map fun s => (s, s)).map (xy, ·)) ≤
      2 * dist (P.bind fun xy => (KX xy.1).map (xy, ·)) (P.bind fun xy => (K xy).map (xy, ·)) +
        2 * dist (P.bind fun xy => (KY xy.2).map (xy, ·))
          (P.bind fun xy => (K xy).map (xy, ·)) := by
  rw [Cslib.Probability.PMF.dist_bind_pair, Cslib.Probability.PMF.dist_bind_pair,
    Cslib.Probability.PMF.dist_bind_pair, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun xy _ => ?_
  have h := dist_localSample_le KX KY K xy.1 xy.2
  have hp := ENNReal.toReal_nonneg (a := P xy)
  calc (P xy).toReal * dist (localSample KX KY K xy.1 xy.2) ((K xy).map fun s => (s, s))
      ≤ (P xy).toReal * (2 * dist (KX xy.1) (K xy) + 2 * dist (KY xy.2) (K xy)) :=
        mul_le_mul_of_nonneg_left h hp
    _ = _ := by ring

end Cslib.Probability.CorrelatedSampling
