/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Density
public import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.GLAmpDecode
public import CslibFrontier.MachineLearning.UniformLearning.Reduction
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Probability.TwoStage

/-!
# Reconstruction for the amplification `(f^k)^GL`

The amplification of Carmosino, Impagliazzo, Kabanets and Kolokolova for `p = 2` is
`Amp(f) = (f^k)^GL = glAmp f k`. Its reconstruction turns a membership-query learner `A` for
`Amp(f)` into one for `f` [Carmosino, Impagliazzo, Kabanets and Kolokolova, Theorem 4.3 and its
proof, pp. 10:15–10:16] [CarmosinoImpagliazzoKabanetsKolokolova2016]. Here it is the black-box
reduction `Cslib.MachineLearning.UniformLearning.QueryLearner.reduce` with these parts:

* each query of `A` to `Amp(f)` is answered with `k` queries to `f`
  (`Cslib.MachineLearning.UniformLearning.glAmpQuery`);
* the hypothesis `h` of `A` goes through Goldreich–Levin decoding
  (`Cslib.Circuits.Boolean.glAmpCandidate`, Claim 4.4);
* the result goes through the direct-product decoder
  (`Cslib.Circuits.Boolean.DirectProduct.dpDecode`, CIKK's Theorem 4.1).

The extra seed (`Cslib.MachineLearning.UniformLearning.AmpSeed`) holds the masks and parity guess
of the first decoder and the seed `(P, b₀, v)` of the second. `ampLearner A s m K` is the
reduction, and `ampSeed μ k s m K` is its seed distribution.

**Reconstruction, library form** (`Cslib.MachineLearning.UniformLearning.learns_ampLearner`).
Suppose `A` learns `{glAmp f k | f ∈ C}` with error `1/2 - γ` and success probability `p`. Put
`δ₀ = γ / 2^(K+3)`, and assume:

* `k ≤ 2 (γ/2)² (2^K - 1)`;
* `2 s ≤ k`;
* `s ≥ (64/ε) log (512 / (ε δ₀²))`;
* `m ≥ (16/δ₀) log (8/ε)`.

Then `ampLearner A s m K` learns `C` with error `ε` and success probability `p δ₀² / 8`. It makes
`k` queries for each query of `A`
(`Cslib.MachineLearning.UniformLearning.queriesAtMost_ampLearner`).

Four deviations from the source are labelled:

* **(a) List loss.** The Goldreich–Levin decoder is the corrected-majority decoder of
  [GoldreichLevin1989], which decodes the `k` coordinates separately. Its list has
  `2^K = O(k / γ²)` entries, where the source's Goldreich–Rubinfeld–Sudan decoder has `O(1 / γ²)`.
* **(b) A deterministic decoder per seed.** The source outputs a random element of the list, with
  expected agreement `Ω(γ³)`. Here each choice of masks and guess is a fixed function, and a
  `δ₀` fraction of the choices has agreement at least `δ₀` (by reverse Markov). That is at least
  `γ³ / (36 k)` for the least admissible `K` when `γ ≤ 1 / 2`.
* **(c) Success probability.** The success probability `p δ₀² / 8` and the constants of the
  direct-product step are ours, from the tuple formulation of the decoder; they are not IJKW's.
  With the least admissible `K`, `δ₀² / 8 ≥ γ⁶ / (10368 k²)`, which is polynomial.
* **(d) Choice of `k`.** Since `δ₀` depends on `k`, the condition `2 s ≤ k` is a fixed point in
  `k`. Here the four conditions are hypotheses. The source fixes `k = ⌈3c (1/ε) ln (1/γ)⌉ + 1`.

Two interface choices are not in the source. `ampLearner A s m K` takes the size `s` of `P`
explicitly, since the seed type contains `P`. `ampSeed` needs `[NeZero k]`, since a trial picks a
position in `Fin k` and the extra seed is empty when `k = 0`.

The learning guarantee and the number of queries are certified, and the circuit size of the
hypotheses is bounded in `CslibFrontier.MachineLearning.UniformLearning.CIKK.Complexity`
(`Cslib.MachineLearning.UniformLearning.complexity_eval_ampLearner_le`); running time is not
certified.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.glAmpQuery`: the `k` queries to `f` that compute
  `glAmp f k` at a point.
* `Cslib.MachineLearning.UniformLearning.AmpSeed`: the extra seed of the reconstruction.
* `Cslib.MachineLearning.UniformLearning.ampLearner`: the reconstruction.
* `Cslib.MachineLearning.UniformLearning.ampSeed`: its seed distribution.

## Main results

* `Cslib.MachineLearning.UniformLearning.eval_ampLearner`: the output of the reconstruction.
* `Cslib.MachineLearning.UniformLearning.queriesAtMost_ampLearner`: `k` queries per query of `A`.
* `Cslib.MachineLearning.UniformLearning.learns_ampLearner`: the reconstruction, library form.

## References

* [M. L. Carmosino, R. Impagliazzo, V. Kabanets and A. Kolokolova,
  *Learning Algorithms from Natural Proofs*][CarmosinoImpagliazzoKabanetsKolokolova2016]
* [ImpagliazzoJaiswalKabanetsWigderson2010]
* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
-/

public section

namespace Cslib.MachineLearning.UniformLearning

open Finset PACLearning Cslib.Circuits.Boolean Cslib.Circuits.Boolean.DirectProduct

variable {n k : ℕ} {Ω : Type*}

/-- **`Amp(f)` is computed with `k` queries to `f`.** At the point `(x, r)`, query `f` at the
`k` blocks of `x`, and output the inner product of the answers with `r`. -/
def glAmpQuery (k : ℕ) (y : BitString (k * n + k)) : DecisionTree (BitString n) Bool :=
  DecisionTree.queryAll
    (fun v => (fun i => v (BitString.block (fun a => y (Fin.castAdd k a)) i)) ⬝ᵥ
      fun j => y (Fin.natAdd (k * n) j))
    (List.ofFn fun i => BitString.block (fun a => y (Fin.castAdd k a)) i) fun _ => false

theorem eval_glAmpQuery (f : BooleanFunction n) (y : BitString (k * n + k)) :
    (glAmpQuery k y).eval f = glAmp f k y := by
  simp [glAmpQuery, glAmp, DecisionTree.eval_queryAll]

theorem depth_glAmpQuery_le (y : BitString (k * n + k)) : (glAmpQuery (n := n) k y).depth ≤ k :=
  (DecisionTree.depth_queryAll_le _ _ _).trans (by simp)

/-- The extra seed of the reconstruction: Goldreich–Levin masks and a guess of their parities,
then a direct-product seed, with a set `P` of `s` positions, a tuple `b₀` of `k` blocks and `m`
trials. -/
abbrev AmpSeed (n k s m K : ℕ) : Type :=
  ((Fin K → BitString k) × BitString K) ×
    (↥(univ.powersetCard s : Finset (Finset (Fin k))) × (Fin k → BitString n) ×
      (Fin m → Trial (BitString n) k))

/-- The extra seed is nonempty when `0 < k` and `s ≤ k`. -/
theorem nonempty_ampSeed (n k s m K : ℕ) [NeZero k] [Fact (s ≤ k)] :
    Nonempty (AmpSeed n k s m K) := by
  have hs : s ≤ (univ : Finset (Fin k)).card := by simpa using (Fact.out : s ≤ k)
  obtain ⟨P, hP⟩ := powersetCard_nonempty.2 hs
  exact ⟨((fun _ _ => false, fun _ => false), ⟨P, hP⟩, fun _ _ => false,
    fun _ => (0, fun _ _ => false))⟩

/-- **The reconstruction of `Amp(f) = glAmp f k`.** Run `A`, answering its queries with
`glAmpQuery`. Decode its hypothesis `h` with the Goldreich–Levin candidate for the masks and guess
of the seed, then with the direct-product decoder for the rest of the seed. The size `s` of the set
`P` is explicit because the seed type contains `P`; the source leaves it implicit. -/
def ampLearner (A : QueryLearner (Fin (k * n + k)) Ω) (s m K : ℕ) :
    QueryLearner (Fin n) (Ω × AmpSeed n k s m K) :=
  QueryLearner.reduce A (glAmpQuery k) fun h ((masks, guess), P, b₀, v) =>
    dpDecode (glAmpCandidate h masks guess) false P b₀ v

/-- The seed distribution of `ampLearner`: a seed of `A` drawn from `μ`, and an independent uniform
extra seed. It needs `[NeZero k]` and `[Fact (s ≤ k)]` because the extra seed is empty otherwise:
a trial picks a position in `Fin k`, and `P` is an `s`-subset of `Fin k`. -/
noncomputable def ampSeed (μ : PMF Ω) (k s m K : ℕ) [NeZero k] [Fact (s ≤ k)] :
    PMF (Ω × AmpSeed n k s m K) :=
  haveI := nonempty_ampSeed n k s m K
  QueryLearner.reduceSeed μ (AmpSeed n k s m K)

/-- Run on `f`, the reconstruction decodes the hypothesis of `A` run on `glAmp f k`. -/
theorem eval_ampLearner (A : QueryLearner (Fin (k * n + k)) Ω) (s m K : ℕ) (f : BooleanFunction n)
    (ω : Ω) (masks : Fin K → BitString k) (guess : BitString K)
    (P : ↥(univ.powersetCard s : Finset (Finset (Fin k)))) (b₀ : Fin k → BitString n)
    (v : Fin m → Trial (BitString n) k) :
    (ampLearner A s m K (ω, (masks, guess), P, b₀, v)).eval f =
      dpDecode (glAmpCandidate ((A ω).eval (glAmp f k)) masks guess) false P b₀ v :=
  QueryLearner.eval_reduce A _ (eval_glAmpQuery f) _

/-- The reconstruction makes `k` queries to `f` for each query of `A`. -/
theorem queriesAtMost_ampLearner {A : QueryLearner (Fin (k * n + k)) Ω} {q : ℕ}
    (hA : A.QueriesAtMost q) (s m K : ℕ) : (ampLearner A s m K).QueriesAtMost (q * k) :=
  QueryLearner.queriesAtMost_reduce _ hA depth_glAmpQuery_le

/-- A hypothesis that differs from `f` on at most `ε 2^n` points has error at most `ε`. -/
private theorem uniformError_le_iff (f h : BooleanFunction n) (ε : ℝ) :
    uniformError f h ≤ ε ↔ (#{x | h x ≠ f x} : ℝ) ≤ ε * Fintype.card (BitString n) := by
  rw [uniformError, hammingDist, BitString.card, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
    div_le_iff₀ (by positivity)]

/-- **Direct-product decoding, seed density form.** If `C'` agrees with the direct product of `f`
on a `δ` fraction of the tuples, then a `δ / 8` fraction of the direct-product seeds decode `f`
with error at most `ε`. -/
private theorem dens_filter_dpDecode_uniformError_le {s m : ℕ} [NeZero k]
    (C' : (Fin k → BitString n) → Fin k → Bool) (f : BooleanFunction n) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) (hε1 : ε ≤ 1) (hδ1 : δ ≤ 1)
    (hG : δ * (2 : ℝ) ^ (k * n) ≤ #{y : Fin k → BitString n | ∀ j, C' y j = f (y j)})
    (hsk : 2 * s ≤ k) (hs : 64 / ε * Real.log (512 / (ε * δ ^ 2)) ≤ s)
    (hm : 16 / δ * Real.log (8 / ε) ≤ m) :
    δ / 8 ≤ (dens {τ : ↥(univ.powersetCard s : Finset (Finset (Fin k))) × (Fin k → BitString n) ×
      (Fin m → Trial (BitString n) k) |
        uniformError f (dpDecode C' false τ.1 τ.2.1 τ.2.2) ≤ ε} : ℝ) := by
  have : Fact (s ≤ k) := ⟨by omega⟩
  obtain ⟨τ₀⟩ := nonempty_ampSeed n k s m 0
  have hT : (0 : ℝ) < Fintype.card (↥(univ.powersetCard s : Finset (Finset (Fin k))) ×
      (Fin k → BitString n) × (Fin m → Trial (BitString n) k)) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨τ₀.2⟩
  have hG' : δ * (Fintype.card (BitString n) : ℝ) ^ k ≤ #(agreeing C' f) := by
    have hag : agreeing C' f = ({y | ∀ j, C' y j = f (y j)} : Finset (Fin k → BitString n)) := by
      ext y
      simp
    rw [hag, BitString.card, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm n k]
    exact hG
  have hhead := card_filter_seed_dpDecode_err_le_ge C' f false hε hδ hε1 hδ1 hG' hsk hs hm
  have hbij : #{τ : ↥(univ.powersetCard s : Finset (Finset (Fin k))) × (Fin k → BitString n) ×
        (Fin m → Trial (BitString n) k) | uniformError f (dpDecode C' false τ.1 τ.2.1 τ.2.2) ≤ ε} =
      #((univ.powersetCard s ×ˢ
        (univ : Finset ((Fin k → BitString n) × (Fin m → Trial (BitString n) k)))).filter
          fun (P, b₀, v) => (#{x | dpDecode C' false P b₀ v x ≠ f x} : ℝ) ≤
            ε * Fintype.card (BitString n)) := by
    refine card_bij (fun τ _ => ((τ.1 : Finset (Fin k)), τ.2)) ?_ ?_ ?_
    · rintro ⟨⟨P, hP⟩, b₀, v⟩ hτ
      simp only [mem_filter, mem_univ, true_and, mem_product, and_true] at hτ ⊢
      exact ⟨hP, (uniformError_le_iff _ _ _).1 hτ⟩
    · rintro ⟨⟨P, hP⟩, b₀, v⟩ _ ⟨⟨P', hP'⟩, b₀', v'⟩ _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
    · rintro ⟨P, b₀, v⟩ hτ
      simp only [mem_filter, mem_univ, mem_product, and_true] at hτ
      exact ⟨(⟨P, hτ.1⟩, b₀, v), by simpa using (uniformError_le_iff _ _ _).2 hτ.2, rfl⟩
  rw [nnratCast_dens, le_div_iff₀ hT, hbij]
  refine le_trans (le_of_eq ?_) hhead
  simp only [Fintype.card_prod, Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_mul, Nat.cast_pow]
  ring

/-- **Reconstruction for `Amp(f) = (f^k)^GL`** [Carmosino, Impagliazzo, Kabanets and Kolokolova,
Theorem 4.3 and Claim 4.4, pp. 10:15–10:16], library form. Suppose `A` learns
`{glAmp f k | f ∈ C}` with error `1/2 - γ` and success probability `p`. Put
`δ₀ = γ / 2^(K+3)`, and assume `k ≤ 2 (γ/2)² (2^K - 1)`, `2 s ≤ k`,
`s ≥ (64/ε) log (512 / (ε δ₀²))` and `m ≥ (16/δ₀) log (8/ε)`. Then `ampLearner A s m K` learns
`C` with error `ε` and success probability `p δ₀² / 8`. The list loss, the per-seed decoder, the
constants and the choice of `k` are labelled in the module docstring. -/
theorem learns_ampLearner {s : ℕ} [NeZero k] [Fact (s ≤ k)] {A : QueryLearner (Fin (k * n + k)) Ω}
    {μ : PMF Ω} {C : ConceptClass (BitString n) Bool} {m K : ℕ} {γ ε p : ℝ}
    (hA : A.Learns μ ((glAmp · k) '' C) (1 / 2 - γ) (1 - p)) (hp : p ≤ 1) (hγ : 0 < γ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (k : ℝ) ≤ 2 * (γ / 2) ^ 2 * ((2 ^ K - 1 : ℕ) : ℝ))
    (hsk : 2 * s ≤ k) (hs : 64 / ε * Real.log (512 / (ε * (γ / 2 ^ (K + 3)) ^ 2)) ≤ s)
    (hm : 16 / (γ / 2 ^ (K + 3)) * Real.log (8 / ε) ≤ m) :
    (ampLearner A s m K).Learns (ampSeed μ k s m K) C ε (1 - p * ((γ / 2 ^ (K + 3)) ^ 2 / 8)) := by
  have := nonempty_ampSeed n k s m K
  -- `0 < K`, since `K = 0` makes the size condition force `k = 0`
  have hK : 0 < K := by
    refine Nat.pos_of_ne_zero fun hK => NeZero.ne k ?_
    subst hK
    simpa using hsize
  have hδ₀ : 0 < γ / 2 ^ (K + 3) := by positivity
  refine QueryLearner.learns_reduce (fun f _ y => eval_glAmpQuery f y) hA hp (by positivity)
    fun f _ h hh => ?_
  have hh' : uniformError (glAmp f k) h ≤ 1 / 2 - γ := hh
  have hγ1 : γ ≤ 1 / 2 := by linarith [uniformError_nonneg (glAmp f k) h]
  have hδ₀1 : γ / 2 ^ (K + 3) ≤ 1 :=
    (div_le_self hγ.le (one_le_pow₀ (by norm_num))).trans (by linarith)
  -- `h` agrees with `glAmp f k` on a `1/2 + γ` fraction of the inputs
  have hagree : (1 / 2 + γ) * 2 ^ (k * n + k) ≤ (#{y | h y = glAmp f k y} : ℝ) := by
    rw [uniformError_eq_one_sub_dens, nnratCast_dens] at hh'
    have hc : (Fintype.card (Fin (k * n + k) → Bool) : ℝ) = 2 ^ (k * n + k) := by simp
    rw [hc] at hh'
    have h3 : 1 / 2 + γ ≤ (#{y | h y = glAmp f k y} : ℝ) / 2 ^ (k * n + k) := by linarith
    rwa [le_div_iff₀ (by positivity)] at h3
  -- Goldreich–Levin decoding (Claim 4.4), then direct-product decoding for each good pair
  have hgl := dens_filter_glAmpCandidate_agree f h hγ hagree hK hsize
  have hprod := Cslib.Probability.mul_le_dens_filter_prod
    (fun mg : (Fin K → BitString k) × BitString K => γ / 2 ^ (K + 3) * 2 ^ (k * n) ≤
      (#{y : Fin k → BitString n | ∀ i, glAmpCandidate h mg.1 mg.2 y i = f (y i)} : ℝ))
    (fun mg (τ : ↥(univ.powersetCard s : Finset (Finset (Fin k))) × (Fin k → BitString n) ×
      (Fin m → Trial (BitString n) k)) =>
        uniformError f (dpDecode (glAmpCandidate h mg.1 mg.2) false τ.1 τ.2.1 τ.2.2) ≤ ε)
    (by positivity) hgl fun mg hmg =>
      dens_filter_dpDecode_uniformError_le _ f hε hδ₀ hε1 hδ₀1 hmg hsk hs hm
  calc (γ / 2 ^ (K + 3)) ^ 2 / 8 = γ / 2 ^ (K + 3) * (γ / 2 ^ (K + 3) / 8) := by ring
    _ ≤ _ := hprod

end Cslib.MachineLearning.UniformLearning
