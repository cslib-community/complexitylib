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
  embedding is exact, by private randomness simulated with shared randomness. A law whose masses
  factor as `c x y · f x s · g y t` has this form (`isEmbeddable_map_fst_of_apply_eq_mul`).
* **Claim 6.1** (`dist_filter_le_two_mul`): conditioning two distributions on an event of
  probability `1 / 2` under both at most doubles their distance.
* **The hypotheses of Corollary 5.3 from a redrawn input** (`dist_withKernel_condY_le`,
  `dist_withKernel_condX_le`): if `J` is close to the law that keeps `(y, s)` and redraws `x` from
  `P₀` given `y`, and the `y`-marginals of `J` and `P₀` are close, then `J` is close to
  `P₀ P_{S | Y}`. This is the triangle step of Holenstein's (6.13)–(6.15).

Embeddings compose, adding their errors (`IsEmbeddable.trans`); the parties may post-process their
outputs locally (`IsEmbeddable.map`); and the error may be weakened (`IsEmbeddable.mono`).
Shared randomness from any type, in any universe, witnesses an embedding
(`IsEmbeddable.of_dist_le`).

## Main definitions

* `Cslib.Probability.CorrelatedSampling.IsEmbeddable`: local embeddability.

## Main results

* `Cslib.Probability.CorrelatedSampling.isEmbeddable_diag`: Lemma 5.2.
* `Cslib.Probability.CorrelatedSampling.isEmbeddable_diag_of_dist_le`: Corollary 5.3.
* `Cslib.Probability.CorrelatedSampling.isEmbeddable_bind_prod`,
  `Cslib.Probability.CorrelatedSampling.isEmbeddable_map_fst_of_apply_eq_mul`: Lemma 5.4.
* `Cslib.Probability.CorrelatedSampling.IsEmbeddable.of_dist_le`,
  `Cslib.Probability.CorrelatedSampling.IsEmbeddable.mono`,
  `Cslib.Probability.CorrelatedSampling.IsEmbeddable.map`,
  `Cslib.Probability.CorrelatedSampling.IsEmbeddable.trans`: introduction, weakening, local
  post-processing and composition.
* `Cslib.Probability.CorrelatedSampling.dist_filter_le_two_mul`: Claim 6.1.
* `Cslib.Probability.CorrelatedSampling.dist_withKernel_condY_le`,
  `Cslib.Probability.CorrelatedSampling.dist_withKernel_condX_le`: the hypotheses of
  Corollary 5.3 from a redrawn input.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.Probability.CorrelatedSampling

open Finset
open Cslib.Probability.PMF (conditionalSnd bind_conditionalSnd dist_bind_le dist_map_le)
open scoped Cslib.Probability.PMF

universe u₁ u₂ u₃ u₄

variable {X : Type u₁} {Y : Type u₂} {S : Type u₃} {T : Type u₄}
  [Fintype X] [Fintype Y] [Fintype S] [Fintype T]

/-- **Local embeddability** [Holenstein, Definition 5.1][Holenstein2009]: from `(x, y)` drawn from
`P₀`, Alice and Bob produce `s = fA x r` and `t = fB y r` from shared randomness `r ~ ρ` so that
`((x, y), (s, t))` is within statistical distance `ε` of `P₁`. The randomness ranges over a type in
the universe of `X`, `Y`, `S` and `T`; `IsEmbeddable.of_dist_le` accepts randomness from any
type. -/
def IsEmbeddable (P₀ : PMF (X × Y)) (P₁ : PMF ((X × Y) × (S × T))) (ε : ℝ) : Prop :=
  ∃ (R : Type (max u₁ u₂ u₃ u₄)) (ρ : PMF R) (fA : X → R → S) (fB : Y → R → T),
    dist (P₀.bind fun xy => ρ.map fun r => (xy, (fA xy.1 r, fB xy.2 r))) P₁ ≤ ε

/-- Shared randomness from any type, in any universe, witnesses local embeddability: it can be
replaced by the pair of strategies `(fA · r, fB · r)` that it selects. -/
theorem IsEmbeddable.of_dist_le {R : Type*} {P₀ : PMF (X × Y)} {P₁ : PMF ((X × Y) × (S × T))}
    {ε : ℝ} (ρ : PMF R) (fA : X → R → S) (fB : Y → R → T)
    (h : dist (P₀.bind fun xy => ρ.map fun r => (xy, (fA xy.1 r, fB xy.2 r))) P₁ ≤ ε) :
    IsEmbeddable P₀ P₁ ε := by
  refine ⟨(X → S) × (Y → T), ρ.map fun r => (fun x => fA x r, fun y => fB y r),
    fun x g => g.1 x, fun y g => g.2 y, ?_⟩
  simpa only [PMF.map_comp, Function.comp_def] using h

/-- Local embeddability is monotone in the error. -/
theorem IsEmbeddable.mono {P₀ : PMF (X × Y)} {P₁ : PMF ((X × Y) × (S × T))} {ε ε' : ℝ}
    (h : IsEmbeddable P₀ P₁ ε) (hε : ε ≤ ε') : IsEmbeddable P₀ P₁ ε' := by
  obtain ⟨R, ρ, fA, fB, hd⟩ := h
  exact ⟨R, ρ, fA, fB, hd.trans hε⟩

/-- **Local post-processing.** If `P₀` embeds in `P₁`, Alice and Bob can apply local maps `gA` and
`gB` to their outputs, for instance to forget part of them, with the same error. -/
theorem IsEmbeddable.map {S' T' : Type*} [Fintype S'] [Fintype T'] {P₀ : PMF (X × Y)}
    {P₁ : PMF ((X × Y) × (S × T))} {ε : ℝ} (h : IsEmbeddable P₀ P₁ ε) (gA : X → S → S')
    (gB : Y → T → T') :
    IsEmbeddable P₀ (P₁.map fun ((x, y), (s, t)) => ((x, y), (gA x s, gB y t))) ε := by
  obtain ⟨R, ρ, fA, fB, hd⟩ := h
  refine IsEmbeddable.of_dist_le ρ (fun x r => gA x (fA x r)) (fun y r => gB y (fB y r))
    (le_trans (le_of_eq ?_) ((dist_map_le _ P₁ fun ((x, y), (s, t)) =>
      ((x, y), (gA x s, gB y t))).trans hd))
  congr 1
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- **Composition of local embeddings.** Suppose `P₀` embeds in a law `P₁` of `((x, y), (s, t))`
with error `ε₁`, and the law of `((x, s), (y, t))` under `P₁` embeds in `P₂` with error `ε₂`. Then
`P₀` embeds in `P₂`, regrouped as `((x, y), ((s, u), (t, v)))`, with error `ε₁ + ε₂`: Alice runs
both protocols on her side, and the shared randomness is a pair of independent strings. -/
theorem IsEmbeddable.trans {U V : Type*} [Fintype U] [Fintype V] {P₀ : PMF (X × Y)}
    {P₁ : PMF ((X × Y) × (S × T))} {P₂ : PMF (((X × S) × (Y × T)) × (U × V))} {ε₁ ε₂ : ℝ}
    (h₁ : IsEmbeddable P₀ P₁ ε₁)
    (h₂ : IsEmbeddable (P₁.map fun ((x, y), (s, t)) => ((x, s), (y, t))) P₂ ε₂) :
    IsEmbeddable P₀ (P₂.map fun (((x, s), (y, t)), (u, v)) => ((x, y), ((s, u), (t, v))))
      (ε₁ + ε₂) := by
  obtain ⟨R₁, ρ₁, fA, fB, hd₁⟩ := h₁
  obtain ⟨R₂, ρ₂, gA, gB, hd₂⟩ := h₂
  -- The second protocol, run on an output of the first.
  let Φ : (X × Y) × (S × T) → PMF (((X × S) × (Y × T)) × (U × V)) := fun z =>
    ρ₂.map fun r => (((z.1.1, z.2.1), (z.1.2, z.2.2)),
      (gA (z.1.1, z.2.1) r, gB (z.1.2, z.2.2) r))
  let M₁ := P₀.bind fun xy => ρ₁.map fun r => (xy, (fA xy.1 r, fB xy.2 r))
  have hM₂ : ((P₁.map fun ((x, y), (s, t)) => ((x, s), (y, t))).bind fun w =>
      ρ₂.map fun r => (w, (gA w.1 r, gB w.2 r))) = P₁.bind Φ := by
    rw [PMF.bind_map]
    rfl
  -- Independent shared strings for the two protocols; each party runs both.
  let ρ := ρ₁.bind fun r₁ => ρ₂.map (r₁, ·)
  let hA : X → R₁ × R₂ → S × U := fun x r => (fA x r.1, gA (x, fA x r.1) r.2)
  let hB : Y → R₁ × R₂ → T × V := fun y r => (fB y r.1, gB (y, fB y r.1) r.2)
  refine IsEmbeddable.of_dist_le ρ hA hB ?_
  have hO : (P₀.bind fun xy => ρ.map fun r => (xy, (hA xy.1 r, hB xy.2 r))) =
      (M₁.bind Φ).map fun (((x, s), (y, t)), (u, v)) => ((x, y), ((s, u), (t, v))) := by
    simp only [ρ, hA, hB, M₁, Φ, PMF.map_bind, PMF.bind_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]
  rw [hO]
  calc _ ≤ dist (M₁.bind Φ) P₂ := dist_map_le _ _ _
    _ ≤ dist (M₁.bind Φ) (P₁.bind Φ) + dist (P₁.bind Φ) P₂ := dist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add ((dist_bind_le _ _ _).trans hd₁) (hM₂ ▸ hd₂)

/-- The conditional law of `s` given `x` under a joint law `J` of `((x, y), s)`. -/
noncomputable def condX (J : PMF ((X × Y) × S)) : X → PMF S :=
  conditionalSnd (J.map (Prod.map Prod.fst id))

/-- The conditional law of `s` given `y` under a joint law `J` of `((x, y), s)`. -/
noncomputable def condY (J : PMF ((X × Y) × S)) : Y → PMF S :=
  conditionalSnd (J.map (Prod.map Prod.snd id))

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
  refine IsEmbeddable.of_dist_le (shared (embedFamily KX KY K))
    (fun x => sample (embedFamily KX KY K) (.inl x))
    (fun y => sample (embedFamily KX KY K) (.inr (.inl y))) ?_
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

omit [Fintype X] [Fintype Y] [Fintype S] [Fintype T] in
/-- The mass of the factorized law of Lemma 5.4. -/
private theorem bind_prod_apply (P₀ : PMF (X × Y)) (KS : X → PMF S) (KT : Y → PMF T) (x : X)
    (y : Y) (s : S) (t : T) :
    (P₀.bind fun xy => (KS xy.1).bind fun s => (KT xy.2).map fun t => (xy, (s, t)))
      ((x, y), (s, t)) = P₀ (x, y) * (KS x s * KT y t) := by
  have h : (fun xy : X × Y => (KS xy.1).bind fun s => (KT xy.2).map fun t => (xy, (s, t))) =
      fun xy => ((KS xy.1).bind fun s => (KT xy.2).map (s, ·)).map (xy, ·) := by
    funext xy
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rw [h, Cslib.Probability.PMF.bind_map_prodMk_apply, Cslib.Probability.PMF.bind_map_prodMk_apply]

open scoped ENNReal in
/-- **Holenstein's Lemma 5.4** [Holenstein, Lemma 5.4][Holenstein2009] for a law `J` of
`((x, y), (s, t))` whose masses factor as `c x y · f x s · g y t`. Such a law has the form (5.5)
of the proof of Lemma 5.4, `P_{XY} P_{S | X} P_{T | Y}`, so its input marginal embeds in it
exactly. -/
theorem isEmbeddable_map_fst_of_apply_eq_mul (J : PMF ((X × Y) × (S × T)))
    (c : X → Y → ℝ≥0∞) (f : X → S → ℝ≥0∞) (g : Y → T → ℝ≥0∞) (hf : ∀ x s, f x s ≠ ∞)
    (hg : ∀ y t, g y t ≠ ∞) (hJ : ∀ x y s t, J ((x, y), (s, t)) = c x y * f x s * g y t) :
    IsEmbeddable (J.map Prod.fst) J 0 := by
  classical
  have hF (x : X) : ∑' s, f x s ≠ ∞ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun s _ => hf x s
  have hG (y : Y) : ∑' t, g y t ≠ ∞ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.mpr fun t _ => hg y t
  -- Normalize `f x` and `g y`. Where a normalizer vanishes, `J` has no mass and any law works.
  let KS : X → PMF S := fun x =>
    if h : ∑' s, f x s = 0 then J.map fun z => z.2.1 else PMF.normalize (f x) h (hF x)
  let KT : Y → PMF T := fun y =>
    if h : ∑' t, g y t = 0 then J.map fun z => z.2.2 else PMF.normalize (g y) h (hG y)
  have hmarg (x : X) (y : Y) :
      (J.map Prod.fst) (x, y) = c x y * (∑' s, f x s) * ∑' t, g y t := by
    rw [Cslib.Probability.PMF.map_fst_apply, tsum_fintype, tsum_fintype, tsum_fintype,
      Fintype.sum_prod_type]
    simp only [hJ, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_comm
  have hfactor : (J.map Prod.fst).bind (fun xy =>
      (KS xy.1).bind fun s => (KT xy.2).map fun t => (xy, (s, t))) = J := by
    ext ⟨⟨x, y⟩, s, t⟩
    rw [bind_prod_apply, hmarg, hJ]
    by_cases hF0 : ∑' s, f x s = 0
    · rw [tsum_eq_zero_iff.mp hF0 s, hF0]
      simp only [mul_zero, zero_mul]
    by_cases hG0 : ∑' t, g y t = 0
    · rw [tsum_eq_zero_iff.mp hG0 t, hG0]
      simp only [mul_zero, zero_mul]
    simp only [KS, KT, dite_eq_right hF0, dite_eq_right hG0, PMF.normalize_apply]
    calc c x y * (∑' s, f x s) * (∑' t, g y t) *
          (f x s * (∑' s, f x s)⁻¹ * (g y t * (∑' t, g y t)⁻¹))
        = c x y * f x s * g y t * ((∑' s, f x s) * (∑' s, f x s)⁻¹) *
          ((∑' t, g y t) * (∑' t, g y t)⁻¹) := by ring
      _ = c x y * f x s * g y t := by
        rw [ENNReal.mul_inv_cancel hF0 (hF x), ENNReal.mul_inv_cancel hG0 (hG y), mul_one,
          mul_one]
  have h := isEmbeddable_bind_prod (J.map Prod.fst) KS KT
  rwa [hfactor] at h

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

/-! ### The hypotheses of Corollary 5.3 from a redrawn input -/

section RedrawnInput

/-- **The triangle step of Holenstein's (6.13)–(6.15)** [Holenstein, proof of Lemma 6.4,
(6.13)–(6.15)][Holenstein2009]. Let `K` draw `x` given `y` under `P₀`, so that `P₀ = P_Y K`. A
joint law `J` of `((x, y), s)` is within `ε₁ + ε₂` of `P₀ P_{S | Y}`, the left side of the second
hypothesis of Corollary 5.3, if it is within `ε₁` of the law that keeps `(y, s)` from `J` and
redraws `x` from `K y`, and its `y`-marginal is within `ε₂` of that of `P₀`. -/
theorem dist_withKernel_condY_le (J : PMF ((X × Y) × S)) (P₀ : PMF (X × Y)) (K : Y → PMF X)
    (hK : (P₀.map Prod.snd).bind (fun y => (K y).map (·, y)) = P₀) :
    dist J (withKernel P₀ fun xy => condY J xy.2) ≤
      dist J ((J.map (Prod.map Prod.snd id)).bind fun (y, s) => (K y).map fun x => ((x, y), s)) +
        dist ((J.map Prod.fst).map Prod.snd) (P₀.map Prod.snd) := by
  set M := J.map (Prod.map Prod.snd id)
  -- Both laws draw `y` and then `x` and `s` independently, from `K y` and `P_{S | Y = y}`.
  set Λ : Y → PMF ((X × Y) × S) := fun y =>
    (condY J y).bind fun s => (K y).map fun x => ((x, y), s)
  have hR : (M.bind fun (y, s) => (K y).map fun x => ((x, y), s)) = (M.map Prod.fst).bind Λ := by
    conv_lhs => rw [← bind_conditionalSnd M]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, Λ, condY, M]
  have hT : withKernel P₀ (fun xy => condY J xy.2) = (P₀.map Prod.snd).bind Λ := by
    conv_lhs => rw [← hK]
    simp only [withKernel, PMF.bind_bind, PMF.bind_map, Function.comp_def, Λ]
    congr 1
    funext y
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm _ _ _
  have hM : M.map Prod.fst = (J.map Prod.fst).map Prod.snd := by
    simp only [M, PMF.map_comp]
    rfl
  rw [hR, hT]
  calc _ ≤ dist J ((M.map Prod.fst).bind Λ) +
        dist ((M.map Prod.fst).bind Λ) ((P₀.map Prod.snd).bind Λ) := dist_triangle _ _ _
    _ ≤ _ := by
      gcongr
      rw [hM]
      exact dist_bind_le _ _ _

/-- **The triangle step of Holenstein's (6.16)** [Holenstein, proof of Lemma 6.4,
(6.16)][Holenstein2009], the mirror image of `dist_withKernel_condY_le`. Let `K` draw `y` given
`x` under `P₀`. A joint law `J` of `((x, y), s)` is within `ε₁ + ε₂` of `P₀ P_{S | X}`, the left
side of the first hypothesis of Corollary 5.3, if it is within `ε₁` of the law that keeps `(x, s)`
from `J` and redraws `y` from `K x`, and its `x`-marginal is within `ε₂` of that of `P₀`. -/
theorem dist_withKernel_condX_le (J : PMF ((X × Y) × S)) (P₀ : PMF (X × Y)) (K : X → PMF Y)
    (hK : (P₀.map Prod.fst).bind (fun x => (K x).map (x, ·)) = P₀) :
    dist J (withKernel P₀ fun xy => condX J xy.1) ≤
      dist J ((J.map (Prod.map Prod.fst id)).bind fun (x, s) => (K x).map fun y => ((x, y), s)) +
        dist ((J.map Prod.fst).map Prod.fst) (P₀.map Prod.fst) := by
  set M := J.map (Prod.map Prod.fst id)
  -- Both laws draw `x` and then `y` and `s` independently, from `K x` and `P_{S | X = x}`.
  set Λ : X → PMF ((X × Y) × S) := fun x =>
    (condX J x).bind fun s => (K x).map fun y => ((x, y), s)
  have hR : (M.bind fun (x, s) => (K x).map fun y => ((x, y), s)) = (M.map Prod.fst).bind Λ := by
    conv_lhs => rw [← bind_conditionalSnd M]
    simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, Λ, condX, M]
  have hT : withKernel P₀ (fun xy => condX J xy.1) = (P₀.map Prod.fst).bind Λ := by
    conv_lhs => rw [← hK]
    simp only [withKernel, PMF.bind_bind, PMF.bind_map, Function.comp_def, Λ]
    congr 1
    funext x
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm _ _ _
  have hM : M.map Prod.fst = (J.map Prod.fst).map Prod.fst := by
    simp only [M, PMF.map_comp]
    rfl
  rw [hR, hT]
  calc _ ≤ dist J ((M.map Prod.fst).bind Λ) +
        dist ((M.map Prod.fst).bind Λ) ((P₀.map Prod.fst).bind Λ) := dist_triangle _ _ _
    _ ≤ _ := by
      gcongr
      rw [hM]
      exact dist_bind_le _ _ _

end RedrawnInput

end Cslib.Probability.CorrelatedSampling
