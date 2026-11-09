/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.GoldreichLevin.Decoding
public import Complexity.Foundations.Data.BitString.Enumeration
import Complexity.Probability.PMF.Event
import Complexity.Crypto.Game

/-!
# Finite Goldreich–Levin inversion reduction

A seeded predictor sees an image and a parity query. The inverter samples one private seed,
reuses that seed for every predictor call, enumerates the decoder's candidates, and checks their
images. Thus the deterministic decoding theorem applies to each fixed image and seed, even when
the predictor's answers to different queries are correlated through its randomness.

If average prediction success is at least `1 / 2 + ε`, `invert_success_ge` gives inversion
success at least `ε / 4`. A fixed random choice between the predictor and its complement handles
either sign of the bias: `invertSigned_success_ge` gives success at least `ε / 8` from absolute
bias `ε`. Neither inverter receives the hidden preimage or chooses a sign based on it.

The image may have any type with decidable equality, and its length need not equal the input
length. The finite seed type and its distribution may depend on the image; they are fixed before
the independent parity query is sampled. For a strict PPT predictor,
the coin-tape representation in `Cslib.Computability.Probabilistic.CoinTape` supplies the
appropriate seeded behavior with a polynomial-time deterministic evaluator; the uniform inverter
built on this argument is proved PPT in `Cslib.Crypto.GoldreichLevin.isPPT_wordInverter`. This
module contains the finite distributional argument, adapted from cslib `crypto` at `5ff69ca`.

## Main definitions

* `candidateList`, `checkCandidates`: ordered candidate generation and first valid preimage.
* `invertFixed`, `invert`, `invertSigned`: decoding with a fixed predictor, a saved seed, and
  a random sign respectively.
* `predictionExperiment`, `inversionExperiment`: the finite prediction and inversion games.

## Main results

* `checkCandidates_correct`: any listed preimage suffices, without injectivity.
* `invert_success_ge`, `invertSigned_success_ge`: positive and absolute bias give inversion
  success of at least `ε / 4` and `ε / 8`, under the stated mask-count bounds.

## References

* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [L. Trevisan, *CS276 Lecture 12: Goldreich–Levin*][Trevisan2009GL]

-/

@[expose] public section

namespace Cslib.Crypto.GoldreichLevin

open Probability MeasureTheory
open scoped ENNReal

variable {Image : Type*} [DecidableEq Image]

/-- Generate one candidate for each parity guess, retaining duplicates. -/
def candidateList {n k : ℕ} (predictor : BitString n → Bool)
    (masks : Fin k → BitString n) : List (BitString n) :=
  (BitString.enum k).map (candidate predictor masks)

/-- The list has one entry per guess, whether or not candidates coincide. -/
@[simp] theorem length_candidateList {n k : ℕ} (predictor : BitString n → Bool)
    (masks : Fin k → BitString n) : (candidateList predictor masks).length = 2 ^ k := by
  simp [candidateList]

/-- The ordered enumeration contains exactly the candidates in the finite decoder. -/
@[simp] theorem mem_candidateList {n k : ℕ} (predictor : BitString n → Bool)
    (masks : Fin k → BitString n) (x : BitString n) :
    x ∈ candidateList predictor masks ↔ x ∈ candidates predictor masks := by
  simp [candidateList, candidates]

/-- Return the first candidate with the requested image, defaulting to zero if none matches. -/
def checkCandidates {n : ℕ} (f : BitString n → Image) (image : Image)
    (list : List (BitString n)) : BitString n :=
  (list.find? (fun candidate => f candidate == image)).getD 0

/-- If the original preimage is listed, checking finds a valid preimage.
Injectivity is not needed. -/
theorem checkCandidates_correct {n : ℕ} (f : BitString n → Image)
    (x : BitString n) (list : List (BitString n)) (hx : x ∈ list) :
    f (checkCandidates f (f x) list) = f x := by
  unfold checkCandidates
  cases hfind : list.find? (fun candidate => f candidate == f x) with
  | none =>
    have h := List.find?_eq_none.mp hfind x hx
    simp at h
  | some z =>
    have h := List.find?_some hfind
    simpa using h

/-- Decode a fixed predictor and check its candidate list against the given image. -/
noncomputable def invertFixed {n : ℕ} (f : BitString n → Image)
    (predictor : BitString n → Bool) (k : ℕ) (image : Image) : PMF (BitString n) :=
  (PMF.uniformOfFintype (Fin k → BitString n)).map
    (fun masks => checkCandidates f image (candidateList predictor masks))

/-- An injective representation of images preserves every candidate check and the decoder's
entire output distribution, including its default output. -/
theorem invertFixed_comp_injective {n : ℕ} {Encoded : Type*} [DecidableEq Encoded]
    (f : BitString n → Image) (encode : Image → Encoded) (hencode : Function.Injective encode)
    (predictor : BitString n → Bool) (k : ℕ) (image : Image) :
    invertFixed (encode ∘ f) predictor k (encode image) = invertFixed f predictor k image := by
  simp only [invertFixed, checkCandidates, Function.comp_apply, beq_eq_decide, hencode.eq_iff]

/-- A correlated predictor yields a valid preimage with probability at least one half when
there are enough masks. The algorithm receives only the image; `x` occurs only in the guarantee. -/
theorem invertFixed_success_ge_half {n k : ℕ} (f : BitString n → Image)
    (predictor : BitString n → Bool) (x : BitString n) (ε : ℝ)
    (hε : 0 < ε) (hk : 0 < k) (h : 1 / 2 + ε ≤ agreement predictor x)
    (hsize : (n : ℝ) ≤ 2 * ε ^ 2 * (2 ^ k - 1 : ℕ)) :
    1 / 2 ≤ (((invertFixed f predictor k (f x)).map (fun z => f z == f x)) true).toReal := by
  let p := (invertFixed f predictor k (f x)).map (fun z => f z == f x)
  have hmiss := decode_failure_le_half predictor x ε hε hk h hsize
  rw [decode, PMF.toOuterMeasure_map_apply] at hmiss
  have hfalse : p false ≤ 1 / 2 := by
    rw [← PMF.toOuterMeasure_apply_singleton p false]
    dsimp [p, invertFixed]
    rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
    apply le_trans (measure_mono ?_) hmiss
    intro masks hfail
    change (f (checkCandidates f (f x) (candidateList predictor masks)) == f x) = false at hfail
    change x ∉ candidates predictor masks
    intro hx
    have hc := checkCandidates_correct f x (candidateList predictor masks)
      ((mem_candidateList predictor masks x).mpr hx)
    simp [hc] at hfail
  have hfalseReal : (p false).toReal ≤ 1 / 2 := by
    have := ENNReal.toReal_mono (by simp : (1 / 2 : ℝ≥0∞) ≠ ⊤) hfalse
    simpa using this
  have hsum := PMF.toReal_true_add_toReal_false p
  change 1 / 2 ≤ (p true).toReal
  linarith

/-- Sample the predictor's seed once and reuse it throughout the decoder. -/
noncomputable def invert {n : ℕ} {Coins : Image → Type*} (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) (k : ℕ) (image : Image) : PMF (BitString n) :=
  (coins image).bind fun seed => invertFixed f (predictor image seed) k image

/-- Average parity-prediction success over a uniform preimage, the seed, and a uniform query. -/
noncomputable def predictionExperiment {n : ℕ} {Coins : Image → Type*}
    (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) : PMF Bool := do
  let x ← PMF.uniformOfFintype (BitString n)
  (coins (f x)).bind fun seed =>
    (PMF.uniformOfFintype (BitString n)).map (fun r => predictor (f x) seed r == x ⬝ᵥ r)

/-- Challenge the inverter with the image of a uniform input and accept any valid preimage. -/
noncomputable def inversionExperiment {n : ℕ} (f : BitString n → Image)
    (inverter : Image → PMF (BitString n)) : PMF Bool := do
  let x ← PMF.uniformOfFintype (BitString n)
  (inverter (f x)).map (fun z => f z == f x)

/-- Independent private randomness may be sampled before or after the inversion challenge. -/
theorem inversionExperiment_bind {n : ℕ} {Coins : Type*} (f : BitString n → Image)
    (coins : PMF Coins) (inverter : Coins → Image → PMF (BitString n)) :
    inversionExperiment f (fun image => coins.bind (fun seed => inverter seed image)) =
      coins.bind (fun seed => inversionExperiment f (inverter seed)) := by
  simp only [inversionExperiment, PMF.monad_bind_eq_bind, PMF.map_bind]
  rw [PMF.bind_comm]

/-- Positive prediction bias `ε` gives inversion success at least `ε / 4`.
For each fixed input and seed, either agreement is below `1 / 2 + ε / 2`, or decoding succeeds
with probability at least one half. Averaging this dichotomy proves the reduction. -/
theorem invert_success_ge {n k : ℕ} {Coins : Image → Type*} [∀ image, Finite (Coins image)]
    (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : 1 / 2 + ε ≤ (predictionExperiment f predictor coins true).toReal)
    (hsize : (n : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ k - 1 : ℕ)) :
    ε / 4 ≤ (inversionExperiment f (invert f predictor coins k) true).toReal := by
  classical
  let (image : Image) := Fintype.ofFinite (Coins image)
  let success (x : BitString n) (seed : Coins (f x)) : ℝ :=
    (((invertFixed f (predictor (f x) seed) k (f x)).map
      (fun z => f z == f x)) true).toReal
  have hpoint (x : BitString n) (seed : Coins (f x)) :
      agreement (predictor (f x) seed) x ≤ 1 / 2 + ε / 2 + 2 * success x seed := by
    by_cases hgood : 1 / 2 + ε / 2 ≤ agreement (predictor (f x) seed) x
    · have hs : 1 / 2 ≤ success x seed :=
        invertFixed_success_ge_half f _ x (ε / 2) (by positivity) hk hgood hsize
      have ha := agreement_le_one (predictor (f x) seed) x
      linarith
    · have hs : 0 ≤ success x seed := ENNReal.toReal_nonneg
      linarith
  have hbound :
      (predictionExperiment f predictor coins true).toReal ≤
        1 / 2 + ε / 2 +
          2 * (inversionExperiment f (invert f predictor coins k) true).toReal := by
    simp only [predictionExperiment, inversionExperiment, invert, PMF.monad_bind_eq_bind,
      PMF.map_bind,
      PMF.bind_apply_toReal, ← agreement_eq_probability]
    exact PMF.sum_le_affine _ fun x => PMF.sum_le_affine _ (hpoint x)
  linarith

/-- A fixed inverter for either sign of prediction bias. One independent fair bit chooses
whether to complement the predictor; no advice about its bias is required. -/
noncomputable def invertSigned {n : ℕ} {Coins : Image → Type*} (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) (k : ℕ) (image : Image) : PMF (BitString n) := do
  let flip ← PMF.uniformOfFintype Bool
  invert f (fun y seed r => predictor y seed r ^^ flip) coins k image

omit [DecidableEq Image] in
private theorem predictionExperiment_not {n : ℕ} {Coins : Image → Type*}
    (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) :
    predictionExperiment f (fun y seed r => !(predictor y seed r)) coins =
      (predictionExperiment f predictor coins).map Bool.not := by
  have h (a b : Bool) : ((!a) == b) = !(a == b) := by cases a <;> cases b <;> rfl
  simp only [predictionExperiment, PMF.monad_bind_eq_bind, PMF.map_bind, PMF.map_comp,
    Function.comp_def, h]

private theorem invertSigned_probability {n k : ℕ} {Coins : Image → Type*}
    (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) :
    (inversionExperiment f (invertSigned f predictor coins k) true).toReal =
      (1 / 2) * (inversionExperiment f (invert f predictor coins k) true).toReal +
      (1 / 2) * (inversionExperiment f
        (invert f (fun y seed r => !(predictor y seed r)) coins k) true).toReal := by
  unfold invertSigned
  simp only [PMF.monad_bind_eq_bind]
  rw [inversionExperiment_bind, PMF.bind_apply_toReal]
  simp [PMF.uniformOfFintype_apply, add_comm, one_div]

/-- Absolute prediction bias `ε` gives inversion success at least `ε / 8` using one fixed
reduction for both signs. This is a finite probability bound, without a machine-time claim. -/
theorem invertSigned_success_ge {n k : ℕ} {Coins : Image → Type*} [∀ image, Finite (Coins image)]
    (f : BitString n → Image)
    (predictor : (image : Image) → Coins image → BitString n → Bool)
    (coins : (image : Image) → PMF (Coins image)) (ε : ℝ) (hε : 0 < ε) (hk : 0 < k)
    (h : ε ≤ |(predictionExperiment f predictor coins true).toReal - 1 / 2|)
    (hsize : (n : ℝ) ≤ 2 * (ε / 2) ^ 2 * (2 ^ k - 1 : ℕ)) :
    ε / 8 ≤ (inversionExperiment f (invertSigned f predictor coins k) true).toReal := by
  rw [invertSigned_probability]
  rcases (le_abs.mp h).symm with hnegative | hpositive
  · have hcomplement :
        (predictionExperiment f (fun y seed r => !(predictor y seed r)) coins true).toReal =
          1 - (predictionExperiment f predictor coins true).toReal := by
      rw [predictionExperiment_not]
      change (Game.succProbability ((predictionExperiment f predictor coins).map Bool.not) : ℝ) = _
      rw [Game.succProbability_not, Game.failProbability_eq,
        NNReal.coe_sub (Game.succProbability_le_one _)]
      rfl
    have hs := invert_success_ge f (fun y seed r => !(predictor y seed r)) coins ε hε hk
      (by rw [hcomplement]; linarith) hsize
    have hn := ENNReal.toReal_nonneg
      (a := inversionExperiment f (invert f predictor coins k) true)
    linarith
  · have hs := invert_success_ge f predictor coins ε hε hk (by linarith) hsize
    have hn := ENNReal.toReal_nonneg
      (a := inversionExperiment f
        (invert f (fun y seed r => !(predictor y seed r)) coins k) true)
    linarith

end Cslib.Crypto.GoldreichLevin
