/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
public import CslibFrontier.Probability.IID
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import CslibFrontier.Probability.IID.Event
import CslibFrontier.Probability.PMF.Event
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Locality-sensitive hashing and AND/OR amplification

A keyed hash family `hash : ι → X → Y` with seed law `seed : PMF ι` makes `x` and `x'` collide
with probability `collisionProb seed hash x x'`. The family is *locality sensitive* for a pair
of relations `near` and `far` when near pairs collide with probability at least `p₁` and far pairs
with probability at most `p₂` (`Cslib.Probability.IsLocalitySensitive`). With
`near x x' := d x x' ≤ r₁` and `far x x' := r₂ ≤ d x x'` for a distance `d`, this is the
`(r₁, r₂, p₁, p₂)`-sensitive family of Indyk and Motwani [IndykMotwani1998]
(`(r, cr, p₁, p₂)` in [HarPeledIndykMotwani2012];
`(d₁, d₂, p₁, p₂)` in [LeskovecRajaramanUllman2020], Section 3.6.1). Universal hashing is the
case `near := (· = ·)`, `far := (· ≠ ·)`, `p₁ = 1`
(`Cslib.Probability.IsUniversalHash.isLocalitySensitive`).

Collision probabilities of independent repetitions are exact:

* the AND construction (`andHash`), concatenating `k` independently keyed hashes, collides with
  probability `p ^ k` (`collisionProb_andHash`);
* the OR construction, declaring a collision when one of `L` independent hashes collides, does so
  with probability `1 - (1 - p) ^ L` (`orCollisionProb_eq`);
* their composition, `L` bands of `k` rows, collides with probability
  `sCurve k L p = 1 - (1 - p ^ k) ^ L` (`orCollisionProb_andHash`). This is the S-curve of the
  banding technique ([LeskovecRajaramanUllman2020], Sections 3.4.2 and 3.6.3).

Both constructions preserve sensitivity with the transformed probabilities. If
`0 ≤ p₂ < p₁ ≤ 1`, then for all `δ > 0` and `δ' > 0` some `k` and `L = ⌈log (1/δ) / p₁ ^ k⌉₊`
make near pairs collide with probability at least `1 - δ` and far pairs with probability at most
`δ'` (`IsLocalitySensitive.exists_banded`). The explicit bounds behind it are `le_sCurve`
(near pairs: `1 - δ ≤ sCurve k L p` once `log (1/δ) ≤ L p₁ ^ k`) and `sCurve_le` (far pairs:
`sCurve k L p ≤ L p₂ ^ k`, a union bound over the bands).

Charikar's observation ([Charikar2002], Lemma 1) that `1 - collisionProb` satisfies the triangle
inequality is `collisionProb_triangle`.

Probabilities are real numbers, the `toReal` of `PMF.toOuterMeasure`, so that the S-curve can be
manipulated by ordinary real analysis. No finiteness of the seed space is assumed; independent
draws use `Cslib.Probability.PMF.iid`. These are information-theoretic statements. The
`(c, r)`-approximate near-neighbour structure built from them, with its failure bound and
parameters, is in `CslibFrontier.DataStructure.NearNeighbor.LSH`; its `n ^ ρ` query time and the
cost of evaluating the hashes are not formalized.

## Main definitions

* `Cslib.Probability.collisionProb`: the collision probability of two inputs.
* `Cslib.Probability.IsLocalitySensitive`: `(near, far, p₁, p₂)`-sensitive families.
* `Cslib.Probability.andHash`: the AND construction (concatenation of `k` hashes).
* `Cslib.Probability.orCollisionProb`: collision probability of the OR construction.
* `Cslib.Probability.sCurve`: the banding curve `1 - (1 - p ^ k) ^ L`.

## Main results

* `Cslib.Probability.collisionProb_andHash`, `Cslib.Probability.orCollisionProb_eq`,
  `Cslib.Probability.orCollisionProb_andHash`: exact AND, OR and banded collision laws.
* `Cslib.Probability.IsLocalitySensitive.and`, `Cslib.Probability.IsLocalitySensitive.or`,
  `Cslib.Probability.IsLocalitySensitive.banded`: amplified sensitivity.
* `Cslib.Probability.le_sCurve`, `Cslib.Probability.sCurve_le`,
  `Cslib.Probability.exists_sCurve_gap`: the S-curve gap with explicit parameters.
* `Cslib.Probability.IsLocalitySensitive.exists_banded`: banded amplification to error `δ` on near
  pairs and `δ'` on far pairs.
* `Cslib.Probability.collisionProb_triangle`: Charikar's triangle inequality.
* `Cslib.Probability.IsUniversalHash.isLocalitySensitive`: universal families are locality
  sensitive.

## References

* [P. Indyk, R. Motwani, *Approximate nearest neighbors: towards removing the curse of
  dimensionality*][IndykMotwani1998]
* [S. Har-Peled, P. Indyk, R. Motwani, *Approximate nearest neighbor: towards removing the curse
  of dimensionality*][HarPeledIndykMotwani2012]
* [J. Leskovec, A. Rajaraman, J. D. Ullman,
  *Mining of Massive Datasets*][LeskovecRajaramanUllman2020], Chapter 3.
* [M. S. Charikar, *Similarity estimation techniques from rounding algorithms*][Charikar2002]
-/

public section

namespace Cslib.Probability

open scoped ENNReal

variable {ι X Y : Type*}

/-! ### Collision probability -/

/-- The probability that `x` and `x'` collide under the keyed family `hash` with seed law
`seed`. Not to be confused with `Cslib.Probability.PMF.collisionProbability`, the probability
that two independent samples of one law agree. -/
@[expose] noncomputable def collisionProb (seed : PMF ι) (hash : ι → X → Y) (x x' : X) : ℝ :=
  (seed.toOuterMeasure {i | hash i x = hash i x'}).toReal

theorem collisionProb_nonneg (seed : PMF ι) (hash : ι → X → Y) (x x' : X) :
    0 ≤ collisionProb seed hash x x' :=
  ENNReal.toReal_nonneg

theorem collisionProb_le_one (seed : PMF ι) (hash : ι → X → Y) (x x' : X) :
    collisionProb seed hash x x' ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one
    (ENNReal.ofReal_one.symm ▸ PMF.toOuterMeasure_le_one _ _)

@[simp]
theorem collisionProb_self (seed : PMF ι) (hash : ι → X → Y) (x : X) :
    collisionProb seed hash x x = 1 := by
  simp only [collisionProb, Set.ofPred_true]
  rw [(PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _), ENNReal.toReal_one]

theorem collisionProb_comm (seed : PMF ι) (hash : ι → X → Y) (x x' : X) :
    collisionProb seed hash x x' = collisionProb seed hash x' x := by
  simp only [collisionProb, eq_comm]

/-- **Charikar's triangle inequality** ([Charikar2002], Lemma 1): the non-collision probability
`1 - collisionProb` of any keyed family satisfies the triangle inequality. If `x` and `z` are
separated, then `x` and `y`, or `y` and `z`, are separated. -/
theorem collisionProb_triangle (seed : PMF ι) (hash : ι → X → Y) (x y z : X) :
    1 - collisionProb seed hash x z ≤
      (1 - collisionProb seed hash x y) + (1 - collisionProb seed hash y z) := by
  have hcompl (a b : X) : 1 - collisionProb seed hash a b =
      (seed.toOuterMeasure {i | hash i a ≠ hash i b}).toReal := by
    have h := PMF.toOuterMeasure_toReal_add_compl seed {i | hash i a = hash i b}
    rw [collisionProb]
    have hset : {i | hash i a = hash i b}ᶜ = {i | hash i a ≠ hash i b} := rfl
    rw [hset] at h
    linarith
  rw [hcompl, hcompl, hcompl]
  refine ENNReal.toReal_le_add ?_ (PMF.toOuterMeasure_ne_top _ _) (PMF.toOuterMeasure_ne_top _ _)
  have hsub : {i | hash i x ≠ hash i z} ⊆
      {i | hash i x ≠ hash i y} ∪ {i | hash i y ≠ hash i z} := by
    intro i hi
    by_contra hno
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hi hno
    exact hi (hno.1.trans hno.2)
  exact (MeasureTheory.measure_mono hsub).trans (MeasureTheory.measure_union_le _ _)

/-! ### Locality-sensitive families -/

/-- A collision-probability function `prob` is `(near, far, p₁, p₂)`-sensitive when near pairs
collide with probability at least `p₁` and far pairs with probability at most `p₂`
([IndykMotwani1998]; [LeskovecRajaramanUllman2020], Section 3.6.1). For a keyed family, take
`prob := collisionProb seed hash`; for a distance `d`, take `near x x' := d x x' ≤ r₁` and
`far x x' := r₂ ≤ d x x'`. The function is left abstract so that the OR construction, which is a
collision rule rather than a hash, is covered too. -/
structure IsLocalitySensitive (prob : X → X → ℝ) (near far : X → X → Prop) (p₁ p₂ : ℝ) :
    Prop where
  /-- Near pairs collide with probability at least `p₁`. -/
  le_of_near : ∀ x x', near x x' → p₁ ≤ prob x x'
  /-- Far pairs collide with probability at most `p₂`. -/
  le_of_far : ∀ x x', far x x' → prob x x' ≤ p₂

/-- An `ε`-universal family is locality sensitive for equality and inequality with `p₁ = 1` and
`p₂ = ε`. -/
theorem IsUniversalHash.isLocalitySensitive {seed : PMF ι} {hash : ι → X → Y} {ε : ℝ≥0∞}
    (hh : IsUniversalHash seed hash ε) (hε : ε ≠ ⊤) :
    IsLocalitySensitive (collisionProb seed hash) (· = ·) (· ≠ ·) 1 ε.toReal where
  le_of_near x x' h := by rw [h, collisionProb_self]
  le_of_far x x' h := ENNReal.toReal_mono hε (hh x x' h)

/-- A near pair is not far when `p₂ < p₁`. -/
theorem IsLocalitySensitive.not_far {prob : X → X → ℝ} {near far : X → X → Prop} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive prob near far p₁ p₂) (hp : p₂ < p₁) {x x' : X} (hx : near x x') :
    ¬ far x x' := fun hf => by
  have := (h.le_of_near x x' hx).trans (h.le_of_far x x' hf)
  linarith

/-! ### The AND construction -/

/-- The AND construction: concatenate `k` hashes keyed by independent seeds. -/
@[expose] def andHash (hash : ι → X → Y) (k : ℕ) (seeds : Fin k → ι) (x : X) : Fin k → Y :=
  fun j => hash (seeds j) x

/-- `k` independently keyed hashes all collide with probability `p ^ k`. -/
theorem collisionProb_andHash (seed : PMF ι) (hash : ι → X → Y) (k : ℕ) (x x' : X) :
    collisionProb (PMF.iid seed k) (andHash hash k) x x' = collisionProb seed hash x x' ^ k := by
  have hset : {s : Fin k → ι | andHash hash k s x = andHash hash k s x'} =
      {s | ∀ j, s j ∈ {i | hash i x = hash i x'}} := by
    ext s
    simp only [andHash, funext_iff, Set.mem_ofPred_eq]
  rw [collisionProb, hset, PMF.toOuterMeasure_iid_forall, ENNReal.toReal_pow, collisionProb]

/-- The AND construction turns a `(p₁, p₂)`-sensitive family into a `(p₁ ^ k, p₂ ^ k)`-sensitive
one. -/
theorem IsLocalitySensitive.and {seed : PMF ι} {hash : ι → X → Y} {near far : X → X → Prop}
    {p₁ p₂ : ℝ} (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂)
    (hp₁ : 0 ≤ p₁) (k : ℕ) :
    IsLocalitySensitive (collisionProb (PMF.iid seed k) (andHash hash k))
      near far (p₁ ^ k) (p₂ ^ k) where
  le_of_near x x' hx := by
    rw [collisionProb_andHash]
    exact pow_le_pow_left₀ hp₁ (h.le_of_near x x' hx) k
  le_of_far x x' hx := by
    rw [collisionProb_andHash]
    exact pow_le_pow_left₀ (collisionProb_nonneg _ _ _ _) (h.le_of_far x x' hx) k

/-! ### The OR construction -/

/-- The OR construction: the probability that at least one of `L` hashes, keyed by independent
seeds, makes `x` and `x'` collide. -/
noncomputable def orCollisionProb (seed : PMF ι) (hash : ι → X → Y) (L : ℕ) (x x' : X) : ℝ :=
  ((PMF.iid seed L).toOuterMeasure {s | ∃ j, hash (s j) x = hash (s j) x'}).toReal

/-- One of `L` independently keyed hashes collides with probability `1 - (1 - p) ^ L`. -/
theorem orCollisionProb_eq (seed : PMF ι) (hash : ι → X → Y) (L : ℕ) (x x' : X) :
    orCollisionProb seed hash L x x' = 1 - (1 - collisionProb seed hash x x') ^ L := by
  have h := PMF.toOuterMeasure_iid_exists seed {i | hash i x = hash i x'} L
  simp only [Set.mem_ofPred_eq] at h
  rw [orCollisionProb, h, ENNReal.toReal_sub_of_le, ENNReal.toReal_pow,
    ENNReal.toReal_sub_of_le, ENNReal.toReal_one, collisionProb]
  · exact PMF.toOuterMeasure_le_one _ _
  · exact ENNReal.one_ne_top
  · exact pow_le_one₀ (by positivity) tsub_le_self
  · exact ENNReal.one_ne_top

/-- `p ↦ 1 - (1 - p) ^ L` is monotone on probabilities. -/
theorem one_sub_one_sub_pow_le_one_sub_one_sub_pow {p q : ℝ} (hpq : p ≤ q) (hq : q ≤ 1)
    (L : ℕ) : 1 - (1 - p) ^ L ≤ 1 - (1 - q) ^ L :=
  sub_le_sub_left (pow_le_pow_left₀ (by linarith) (by linarith) L) 1

/-- The OR construction turns a `(p₁, p₂)`-sensitive family into a
`(1 - (1 - p₁) ^ L, 1 - (1 - p₂) ^ L)`-sensitive one. -/
theorem IsLocalitySensitive.or {seed : PMF ι} {hash : ι → X → Y} {near far : X → X → Prop}
    {p₁ p₂ : ℝ} (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂)
    (hp₂ : p₂ ≤ 1) (L : ℕ) :
    IsLocalitySensitive (orCollisionProb seed hash L) near far (1 - (1 - p₁) ^ L)
      (1 - (1 - p₂) ^ L) where
  le_of_near x x' hx := by
    rw [orCollisionProb_eq]
    exact one_sub_one_sub_pow_le_one_sub_one_sub_pow (h.le_of_near x x' hx)
      (collisionProb_le_one _ _ _ _) L
  le_of_far x x' hx := by
    rw [orCollisionProb_eq]
    exact one_sub_one_sub_pow_le_one_sub_one_sub_pow (h.le_of_far x x' hx) hp₂ L

/-! ### Banding and the S-curve -/

/-- The S-curve of banding: `L` bands of `k` rows each collide in some band with probability
`1 - (1 - p ^ k) ^ L` when one row collides with probability `p`. -/
@[expose] def sCurve (k L : ℕ) (p : ℝ) : ℝ :=
  1 - (1 - p ^ k) ^ L

/-- `L` bands of `k` independently keyed rows collide in some band with probability
`sCurve k L p`. -/
theorem orCollisionProb_andHash (seed : PMF ι) (hash : ι → X → Y) (k L : ℕ) (x x' : X) :
    orCollisionProb (PMF.iid seed k) (andHash hash k) L x x' =
      sCurve k L (collisionProb seed hash x x') := by
  rw [orCollisionProb_eq, collisionProb_andHash, sCurve]

/-- The S-curve is monotone on probabilities. -/
theorem sCurve_mono {k L : ℕ} {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    sCurve k L p ≤ sCurve k L q :=
  one_sub_one_sub_pow_le_one_sub_one_sub_pow (pow_le_pow_left₀ hp hpq k)
    (pow_le_one₀ (hp.trans hpq) hq) L

/-- Banding turns a `(p₁, p₂)`-sensitive family into a `(sCurve k L p₁, sCurve k L p₂)`-sensitive
one. -/
theorem IsLocalitySensitive.banded {seed : PMF ι} {hash : ι → X → Y} {near far : X → X → Prop}
    {p₁ p₂ : ℝ} (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂)
    (hp₁ : 0 ≤ p₁) (hp₂ : p₂ ≤ 1) (k L : ℕ) :
    IsLocalitySensitive (orCollisionProb (PMF.iid seed k) (andHash hash k) L) near far
      (sCurve k L p₁) (sCurve k L p₂) where
  le_of_near x x' hx := by
    rw [orCollisionProb_andHash]
    exact sCurve_mono hp₁ (h.le_of_near x x' hx) (collisionProb_le_one _ _ _ _)
  le_of_far x x' hx := by
    rw [orCollisionProb_andHash]
    exact sCurve_mono (collisionProb_nonneg _ _ _ _) (h.le_of_far x x' hx) hp₂

/-- **Near pairs.** If `p₁ ≤ p ≤ 1` and `log (1/δ) ≤ L p₁ ^ k`, banding misses with probability
at most `δ`: `(1 - p ^ k) ^ L ≤ exp (-L p ^ k) ≤ δ`. -/
theorem le_sCurve {k L : ℕ} {p p₁ δ : ℝ} (hp₁ : 0 ≤ p₁) (hp₁p : p₁ ≤ p) (hp : p ≤ 1)
    (hδ : 0 < δ) (hL : Real.log δ⁻¹ ≤ L * p₁ ^ k) :
    1 - δ ≤ sCurve k L p := by
  have hpk : p₁ ^ k ≤ p ^ k := pow_le_pow_left₀ hp₁ hp₁p k
  have hpk1 : p ^ k ≤ 1 := pow_le_one₀ (hp₁.trans hp₁p) hp
  have hmiss : (1 - p ^ k) ^ L ≤ δ := by
    calc (1 - p ^ k) ^ L ≤ Real.exp (-p ^ k) ^ L :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) L
      _ = Real.exp (-(L * p ^ k)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-Real.log δ⁻¹) := by
          gcongr
          exact hL.trans (mul_le_mul_of_nonneg_left hpk (Nat.cast_nonneg L))
      _ = δ := by rw [Real.log_inv, neg_neg, Real.exp_log hδ]
  rw [sCurve]
  linarith

/-- **Far pairs.** If `0 ≤ p ≤ p₂ ≤ 1`, banding collides with probability at most `L p₂ ^ k`, by
Bernoulli's inequality `1 - L p ^ k ≤ (1 - p ^ k) ^ L`. -/
theorem sCurve_le {k L : ℕ} {p p₂ : ℝ} (hp : 0 ≤ p) (hpp₂ : p ≤ p₂) (hp₂ : p₂ ≤ 1) :
    sCurve k L p ≤ L * p₂ ^ k := by
  have hpk1 : p ^ k ≤ 1 := pow_le_one₀ hp (hpp₂.trans hp₂)
  have hb := one_add_mul_le_pow (a := -p ^ k) (by linarith) L
  have hpk : p ^ k ≤ p₂ ^ k := pow_le_pow_left₀ hp hpp₂ k
  rw [← sub_eq_add_neg, mul_neg, ← sub_eq_add_neg] at hb
  rw [sCurve]
  nlinarith [Nat.cast_nonneg (α := ℝ) L]

/-- **The S-curve gap.** If `0 ≤ p₂ < p₁ ≤ 1`, then for all `δ > 0` and `δ' > 0` there is a
number of rows `k` such that `L = ⌈log (1/δ) / p₁ ^ k⌉₊` bands give `1 - δ ≤ sCurve k L p` for
every `p ∈ [p₁, 1]` and `sCurve k L p ≤ δ'` for every `p ∈ [0, p₂]`. The proof takes `k` with
`(p₂ / p₁) ^ k ≤ δ' / (2 (c + 1))` and `p₂ ^ k ≤ δ' / 2`, where `c = max 0 (log (1/δ))`. -/
theorem exists_sCurve_gap {p₁ p₂ δ δ' : ℝ} (hp₂ : 0 ≤ p₂) (hp₁₂ : p₂ < p₁) (hp₁ : p₁ ≤ 1)
    (hδ : 0 < δ) (hδ' : 0 < δ') :
    ∃ k : ℕ, ∃ L : ℕ, L = ⌈Real.log δ⁻¹ / p₁ ^ k⌉₊ ∧
      (∀ p, p₁ ≤ p → p ≤ 1 → 1 - δ ≤ sCurve k L p) ∧
      (∀ p, 0 ≤ p → p ≤ p₂ → sCurve k L p ≤ δ') := by
  have hp₁0 : 0 < p₁ := hp₂.trans_lt hp₁₂
  set c := max 0 (Real.log δ⁻¹)
  have hc : 0 ≤ c := le_max_left _ _
  have hr0 : 0 ≤ p₂ / p₁ := div_nonneg hp₂ hp₁0.le
  have hr1 : p₂ / p₁ < 1 := (div_lt_one hp₁0).2 hp₁₂
  have hp₂1 : p₂ < 1 := hp₁₂.trans_le hp₁
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (show 0 < δ' / (2 * (c + 1)) by positivity) hr1
  obtain ⟨k₂, hk₂⟩ := exists_pow_lt_of_lt_one (show 0 < δ' / 2 by positivity) hp₂1
  set k := max k₁ k₂
  have hrk : (p₂ / p₁) ^ k ≤ δ' / (2 * (c + 1)) :=
    (pow_le_pow_of_le_one hr0 hr1.le (le_max_left _ _)).trans hk₁.le
  have hp₂k : p₂ ^ k ≤ δ' / 2 :=
    (pow_le_pow_of_le_one hp₂ hp₂1.le (le_max_right _ _)).trans hk₂.le
  have hp₁k : 0 < p₁ ^ k := pow_pos hp₁0 k
  refine ⟨k, ⌈Real.log δ⁻¹ / p₁ ^ k⌉₊, rfl, fun p hp hp1 => ?_, fun p hp hp2 => ?_⟩
  · refine le_sCurve hp₁0.le hp hp1 hδ ?_
    rw [← div_le_iff₀ hp₁k]
    exact Nat.le_ceil _
  · refine (sCurve_le hp hp2 hp₂1.le).trans ?_
    have hL : (⌈Real.log δ⁻¹ / p₁ ^ k⌉₊ : ℝ) ≤ c / p₁ ^ k + 1 := by
      have h1 : ⌈Real.log δ⁻¹ / p₁ ^ k⌉₊ ≤ ⌈c / p₁ ^ k⌉₊ :=
        Nat.ceil_le_ceil (div_le_div_of_nonneg_right (le_max_right _ _) hp₁k.le)
      exact (Nat.cast_le.2 h1).trans (Nat.ceil_lt_add_one (div_nonneg hc hp₁k.le)).le
    have hdiv : c / p₁ ^ k * p₂ ^ k = c * (p₂ / p₁) ^ k := by
      rw [div_pow]
      field_simp
    calc (⌈Real.log δ⁻¹ / p₁ ^ k⌉₊ : ℝ) * p₂ ^ k ≤ (c / p₁ ^ k + 1) * p₂ ^ k := by gcongr
      _ = c * (p₂ / p₁) ^ k + p₂ ^ k := by rw [add_mul, one_mul, hdiv]
      _ ≤ c * (δ' / (2 * (c + 1))) + δ' / 2 := by gcongr
      _ ≤ δ' / 2 + δ' / 2 := by
          gcongr
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
      _ = δ' := by ring

/-- **Banded amplification.** A `(near, far, p₁, p₂)`-sensitive family with `0 ≤ p₂ < p₁ ≤ 1`
can be amplified by banding with `k` rows and `L = ⌈log (1/δ) / p₁ ^ k⌉₊` bands so that near
pairs collide with probability at least `1 - δ` and far pairs with probability at most `δ'`. -/
theorem IsLocalitySensitive.exists_banded {seed : PMF ι} {hash : ι → X → Y}
    {near far : X → X → Prop} {p₁ p₂ δ δ' : ℝ}
    (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂) (hp₂ : 0 ≤ p₂)
    (hp₁₂ : p₂ < p₁) (hp₁ : p₁ ≤ 1) (hδ : 0 < δ) (hδ' : 0 < δ') :
    ∃ k : ℕ, ∃ L : ℕ, L = ⌈Real.log δ⁻¹ / p₁ ^ k⌉₊ ∧
      IsLocalitySensitive (orCollisionProb (PMF.iid seed k) (andHash hash k) L) near far
        (1 - δ) δ' := by
  obtain ⟨k, L, hL, hnear, hfar⟩ := exists_sCurve_gap hp₂ hp₁₂ hp₁ hδ hδ'
  refine ⟨k, L, hL, fun x x' hx => ?_, fun x x' hx => ?_⟩
  · rw [orCollisionProb_andHash]
    exact hnear _ (h.le_of_near x x' hx) (collisionProb_le_one _ _ _ _)
  · rw [orCollisionProb_andHash]
    exact hfar _ (collisionProb_nonneg _ _ _ _) (h.le_of_far x x' hx)

end Cslib.Probability
