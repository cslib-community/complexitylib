/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.CorrelatedSampling.Embedding
public import Complexity.Probability.Conditioning
public import Complexity.Probability.Product
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Map
import Complexity.Probability.StatisticalDistance

/-!
# Local embeddings

A distribution `P₀` of pairs `(x, y)` is `ε`-*embeddable* in a distribution `P₁` of
`((x, y), (s, t))` [Holenstein, Definition 5.1][Holenstein2009] if Alice, who holds `x`, and Bob,
who holds `y`, can use shared randomness, but no communication, to produce `s` and `t` so that
`((x, y), (s, t))` is within statistical distance `ε` of `P₁`
(`Cslib.Probability.CorrelatedSampling.IsEmbeddable`).

* **Lemma 5.2** (`isEmbeddable_diag`): a joint distribution `J` of `((x, y), s)` embeds its marginal
  in `((x, y), (s, s))` with error `2 ε₁ + 2 ε₂`, where `ε₁` and `ε₂` are the distances of `J`
  from `P_{XY} P_{S | X}` and `P_{XY} P_{S | Y}`. This is the local embedding lemma of
  `Complexity/Probability/CorrelatedSampling/Embedding.lean` with the conditional distributions of
  `J` as kernels.
* **Corollary 5.3** (`isEmbeddable_diag_of_dist_le`): the same holds for another input distribution
  `P₀`, measured by the distances of `J` from `P₀ P_{S | X}` and `P₀ P_{S | Y}`, with error
  `7 ε₁ + 2 ε₂`. Holenstein states the constant `3 ε₁ + 2 ε₂`; the proof here goes through the
  triangle inequality and the constant is this file's own.
* **Lemma 5.4** (`isEmbeddable_bind_prod`): if `s` depends only on `x` and `t` only on `y`, the
  embedding is exact, by private randomness simulated with shared randomness.
* **Claim 6.1** (`dist_filter_le_two_mul`): conditioning two distributions on an event of
  probability `1 / 2` under both at most doubles their distance.

## Main definitions

* `Cslib.Probability.CorrelatedSampling.IsEmbeddable`: local embeddability.

## Main results

* `Cslib.Probability.CorrelatedSampling.isEmbeddable_diag`: Lemma 5.2.
* `Cslib.Probability.CorrelatedSampling.isEmbeddable_diag_of_dist_le`: Corollary 5.3.
* `Cslib.Probability.CorrelatedSampling.isEmbeddable_bind_prod`: Lemma 5.4.
* `Cslib.Probability.CorrelatedSampling.dist_filter_le_two_mul`: Claim 6.1.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.Probability.CorrelatedSampling

open Finset
open Cslib.Probability.PMF (conditionalSnd bind_conditionalSnd dist_bind_le dist_map_le)
open scoped Cslib.Probability.PMF

variable {X Y S T : Type} [Fintype X] [Fintype Y] [Fintype S] [Fintype T]

/-- **Local embeddability** [Holenstein, Definition 5.1][Holenstein2009]: from `(x, y)` drawn from
`P₀`, Alice and Bob produce `s = fA x r` and `t = fB y r` from shared randomness `r ~ ρ` so that
`((x, y), (s, t))` is within statistical distance `ε` of `P₁`. -/
def IsEmbeddable (P₀ : PMF (X × Y)) (P₁ : PMF ((X × Y) × (S × T))) (ε : ℝ) : Prop :=
  ∃ (R : Type) (ρ : PMF R) (fA : X → R → S) (fB : Y → R → T),
    dist (P₀.bind fun xy => ρ.map fun r => (xy, (fA xy.1 r, fB xy.2 r))) P₁ ≤ ε

/-- The conditional law of `s` given `x` under a joint law `J` of `((x, y), s)`. -/
noncomputable def condX (J : PMF ((X × Y) × S)) : X → PMF S :=
  conditionalSnd (J.map fun z => (z.1.1, z.2))

/-- The conditional law of `s` given `y` under a joint law `J` of `((x, y), s)`. -/
noncomputable def condY (J : PMF ((X × Y) × S)) : Y → PMF S :=
  conditionalSnd (J.map fun z => (z.1.2, z.2))

/-- The joint law `P ⊗ K` of `((x, y), s)` with `(x, y) ~ P` and `s ~ K (x, y)`. -/
noncomputable abbrev withKernel (P : PMF (X × Y)) (K : X × Y → PMF S) : PMF ((X × Y) × S) :=
  P.bind fun xy => (K xy).map (xy, ·)

/-- The protocol of the local embedding lemma, run on inputs drawn from `P₀`, is a local strategy
with shared randomness. -/
private theorem localSample_eq (P₀ : PMF (X × Y)) (KX : X → PMF S) (KY : Y → PMF S)
    (K : X × Y → PMF S) :
    P₀.bind (fun xy => (localSample KX KY K xy.1 xy.2).map (xy, ·)) =
      P₀.bind fun xy => (shared (embedFamily KX KY K)).map fun l =>
        (xy, (sample (embedFamily KX KY K) (.inl xy.1) l,
          sample (embedFamily KX KY K) (.inr (.inl xy.2)) l)) := by
  simp only [localSample, PMF.map_comp, Function.comp_def]

omit [Fintype X] [Fintype Y] [Fintype S] in
private theorem diag_eq (J : PMF ((X × Y) × S)) :
    J.map (fun z => (z.1, (z.2, z.2))) =
      (J.map Prod.fst).bind fun xy => ((conditionalSnd J xy).map fun s => (s, s)).map (xy, ·) := by
  conv_lhs => rw [← bind_conditionalSnd J]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- **The local embedding protocol** on inputs from any `P₀`: its output is within
`2 d(P₀ ⊗ KX, P₀ ⊗ K) + 2 d(P₀ ⊗ KY, P₀ ⊗ K)` of `P₀ ⊗ (K, K)`. -/
theorem isEmbeddable_withKernel (P₀ : PMF (X × Y)) (KX : X → PMF S) (KY : Y → PMF S)
    (K : X × Y → PMF S) :
    IsEmbeddable P₀ (P₀.bind fun xy => ((K xy).map fun s => (s, s)).map (xy, ·))
      (2 * dist (withKernel P₀ fun xy => KX xy.1) (withKernel P₀ K) +
        2 * dist (withKernel P₀ fun xy => KY xy.2) (withKernel P₀ K)) := by
  refine ⟨_, shared (embedFamily KX KY K), fun x => sample (embedFamily KX KY K) (.inl x),
    fun y => sample (embedFamily KX KY K) (.inr (.inl y)), ?_⟩
  rw [← localSample_eq]
  exact dist_embed_le P₀ KX KY K

/-- **Holenstein's Lemma 5.2** [Holenstein, Lemma 5.2][Holenstein2009]: a joint law `J` of
`((x, y), s)` embeds its marginal in `((x, y), (s, s))` with error `2 ε₁ + 2 ε₂`, where `ε₁` and
`ε₂` are the distances of `J` from `P_{XY} P_{S | X}` and `P_{XY} P_{S | Y}`. -/
theorem isEmbeddable_diag (J : PMF ((X × Y) × S)) :
    IsEmbeddable (J.map Prod.fst) (J.map fun z => (z.1, (z.2, z.2)))
      (2 * dist J (withKernel (J.map Prod.fst) fun xy => condX J xy.1) +
        2 * dist J (withKernel (J.map Prod.fst) fun xy => condY J xy.2)) := by
  have h := isEmbeddable_withKernel (J.map Prod.fst) (condX J) (condY J) (conditionalSnd J)
  have hJ : withKernel (J.map Prod.fst) (conditionalSnd J) = J := bind_conditionalSnd J
  rw [hJ, ← diag_eq, dist_comm (withKernel _ _) J, dist_comm (withKernel _ _) J] at h
  exact h

/-- **Holenstein's Corollary 5.3** [Holenstein, Corollary 5.3][Holenstein2009], with the constant
`7 ε₁ + 2 ε₂` of this proof: if `J` is within `ε₁` of `P₀ P_{S | X}` and within `ε₂` of
`P₀ P_{S | Y}`, then `P₀` embeds in `((x, y), (s, s))` under `J` with error `7 ε₁ + 2 ε₂`. -/
theorem isEmbeddable_diag_of_dist_le (J : PMF ((X × Y) × S)) (P₀ : PMF (X × Y)) {ε₁ ε₂ : ℝ}
    (h₁ : dist J (withKernel P₀ fun xy => condX J xy.1) ≤ ε₁)
    (h₂ : dist J (withKernel P₀ fun xy => condY J xy.2) ≤ ε₂) :
    IsEmbeddable P₀ (J.map fun z => (z.1, (z.2, z.2))) (7 * ε₁ + 2 * ε₂) := by
  obtain ⟨R, ρ, fA, fB, hemb⟩ :=
    isEmbeddable_withKernel P₀ (condX J) (condY J) (conditionalSnd J)
  refine ⟨R, ρ, fA, fB, ?_⟩
  set P := J.map Prod.fst
  set K := conditionalSnd J
  have hJ : withKernel P K = J := bind_conditionalSnd J
  -- The input laws are within `ε₁`.
  have hP : dist P P₀ ≤ ε₁ := by
    simpa only [withKernel, Cslib.Probability.PMF.map_fst_bind_pair] using
      (dist_map_le J (withKernel P₀ fun xy => condX J xy.1) Prod.fst).trans h₁
  have hK : dist J (withKernel P₀ K) ≤ ε₁ := by
    rw [← hJ]
    exact (dist_bind_le P P₀ _).trans hP
  set A := withKernel P₀ fun xy => condX J xy.1
  set B := withKernel P₀ fun xy => condY J xy.2
  set C := withKernel P₀ K
  have hX := dist_triangle_left A C J
  have hY := dist_triangle_left B C J
  set E := P₀.bind fun xy => ((K xy).map fun s => (s, s)).map (xy, ·)
  set Out := P₀.bind fun xy => ρ.map fun r => (xy, (fA xy.1 r, fB xy.2 r))
  set Tgt := J.map fun z => (z.1, (z.2, z.2))
  have hdiag : dist E Tgt ≤ ε₁ := by
    change dist E (J.map fun z => (z.1, (z.2, z.2))) ≤ ε₁
    rw [diag_eq, dist_comm]
    exact (dist_bind_le P P₀ _).trans hP
  have := dist_triangle Out E Tgt
  have hemb' : dist Out E ≤ 2 * dist A C + 2 * dist B C := hemb
  linarith

/-- **Holenstein's Lemma 5.4** [Holenstein, Lemma 5.4][Holenstein2009], for the factorized law it
characterizes: if `s` is drawn from `KS x` and `t` from `KT y`, independently, then `P₀` embeds
exactly. Shared randomness simulates the private coins: it draws a random function for each party.
-/
theorem isEmbeddable_bind_prod (P₀ : PMF (X × Y)) (KS : X → PMF S) (KT : Y → PMF T) :
    IsEmbeddable P₀ (P₀.bind fun xy => (KS xy.1).bind fun s => (KT xy.2).map fun t => (xy, (s, t)))
      0 := by
  refine ⟨(X → S) × (Y → T),
    (Cslib.Probability.PMF.pi KS).bind fun a => (Cslib.Probability.PMF.pi KT).map fun b => (a, b),
    fun x r => r.1 x, fun y r => r.2 y, le_of_eq ?_⟩
  rw [dist_eq_zero]
  congr 1
  funext xy
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [← Cslib.Probability.PMF.pi_map_eval KS xy.1, PMF.bind_map,
    ← Cslib.Probability.PMF.pi_map_eval KT xy.2]
  simp only [PMF.map_comp, Function.comp_def]

/-- **Holenstein's Claim 6.1** [Holenstein, Claim 6.1][Holenstein2009]: conditioning two
distributions on an event of probability `1 / 2` under both at most doubles their statistical
distance. -/
theorem dist_filter_le_two_mul {Z : Type*} [Fintype Z] (p q : PMF Z) (E : Set Z)
    (hp : (p.toOuterMeasure E).toReal = 1 / 2) (hq : (q.toOuterMeasure E).toReal = 1 / 2)
    (hpE : ∃ a ∈ E, a ∈ p.support) (hqE : ∃ a ∈ E, a ∈ q.support) :
    dist (p.filter E hpE) (q.filter E hqE) ≤ 2 * dist p q := by
  classical
  rw [Cslib.Probability.PMF.dist_eq, Cslib.Probability.PMF.dist_eq,
    ← mul_div_assoc, Finset.mul_sum]
  gcongr with a
  rw [Cslib.Probability.PMF.filter_apply_toReal, Cslib.Probability.PMF.filter_apply_toReal,
    hp, hq]
  split_ifs
  · rw [← sub_div, abs_div]
    norm_num [div_eq_mul_inv, mul_comm]
  · simp only [sub_self, abs_zero]
    positivity

end Cslib.Probability.CorrelatedSampling
