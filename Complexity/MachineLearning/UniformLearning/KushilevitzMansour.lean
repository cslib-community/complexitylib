/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Leaves
public import Complexity.MachineLearning.UniformLearning.LowDegree
public import Complexity.MachineLearning.UniformLearning.MembershipQuery
public import Complexity.Foundations.BooleanAnalysis.BucketWeight
import Complexity.Probability.PMF.Event
import Complexity.Computability.DecisionTree.SpectralNorm
import Complexity.Probability.Concentration
import Complexity.Probability.PMF
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Kushilevitz–Mansour algorithm

The **Kushilevitz–Mansour algorithm** [KushilevitzMansour1993]
[O'Donnell, Section 3.5][ODonnell2014] learns, with membership queries, every Boolean function of
small spectral norm `∑_S |f̂(S)|` (`UniformLearning.spectralNormClass`); for instance every function
computed by a small decision tree (`UniformLearning.decisionTreeClass`). It finds the large Fourier
coefficients by the bucket search of Goldreich and Levin [GoldreichLevin1989]: the bucket of a set
`S ⊆ J` is the family of the sets `U` with `U ∩ J = S`, and its weight is the bucket weight
(`BitString.bucketWeight`, O'Donnell's `W^{S | J̄}` with `J̄` the complement of `J`). Starting from
the bucket of all sets, the search adds the coordinates one at a time, splitting each surviving
bucket `S` of `J` into the buckets `S` and `insert i S` of `insert i J`, and keeps the buckets whose
estimated weight is at least `θ² / 2` (`UniformLearning.bucketSearch`). A set `U` with `|f̂(U)| ≥ θ`
contributes `θ²` to each of its buckets and is never discarded
(`UniformLearning.inter_mem_bucketSearch`), while every surviving bucket weighs at least `θ² / 4`,
so at most `4 / θ²` buckets survive at each level (`UniformLearning.mul_card_bucketSearch_le_one`).

The weights are estimated from samples `(x, y, z)` of three independent uniform points, as the
average of `f (x, z) χ_S(x) f (y, z) χ_S(y)` (`UniformLearning.bucketEstimate`,
`BitString.bucketWeight_eq_expect_sample`), where `(x, z)` takes the coordinates in `J` from `x` and
the others from `z`. Here the same `m` samples serve every bucket of every level, so the queries are
non-adaptive: the learner queries `f` at `x` and at the points `(x, z)`, `(y, z)` of every sample
and every level, `m (2 n + 3)` queries for `n` coordinates
(`UniformLearning.kmLearner_queriesAtMost`), and then runs the search on the answers. The analysis
takes a union bound over all `2 ^ n` buckets of each level, which costs a factor `n` in the number
of samples compared with fresh samples for each weighing. The hypothesis is the sign of the
expansion on the found sets with coefficients estimated from the points `x`
(`UniformLearning.kmHypothesis`, `UniformLearning.kmLearner`).

If all estimates are within `θ² / 4` of their values, the hypothesis has error at most
`θ² / 4 + θ L` for a function of spectral norm at most `L`
(`UniformLearning.uniformError_kmHypothesis_le`): the found sets carry all coefficients of absolute
value at least `θ`, and the others weigh at most `θ L`. Hoeffding's inequality and the union bound
make the estimates accurate except with probability at most `2 (n + 2) 2 ^ n exp (-m θ⁴ / 32)`
(`UniformLearning.uniform_not_accurate_le`). With `θ = ε / (2 L)` this gives the
**Kushilevitz–Mansour theorem**: the functions of spectral norm at most `L` are learned with error
`ε` and confidence `1 - δ` from `m ≥ (512 L⁴ / ε⁴) log (2 (n + 2) 2 ^ n / δ)` samples, hence
`m (2 n + 3)` membership queries, polynomial in `n`, `L`, `1 / ε` and `log (1 / δ)`
(`UniformLearning.kmLearner_learns`) [O'Donnell, Theorem 3.38][ODonnell2014]. By the spectral
norm bound for decision trees (`DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount`), this
applies to the functions computed by decision trees with at most `L` leaves
(`UniformLearning.kmLearner_learns_decisionTree`).

**Cost.** Only the number of queries is certified. On accurate samples the search computes at most
`8 / θ²` bucket estimates at each level, each from the `m` samples, and estimates at most `4 / θ²`
coefficients; this count of arithmetic operations is informal, and the running time is not
certified by a machine model.

## Main definitions

* `Cslib.MachineLearning.UniformLearning.spectralNormClass`,
  `Cslib.MachineLearning.UniformLearning.decisionTreeClass`: the functions of bounded spectral
  norm, and those computed by decision trees with few leaves.
* `Cslib.MachineLearning.UniformLearning.bucketSearch`: the bucket search of Goldreich–Levin and
  Kushilevitz–Mansour.
* `Cslib.MachineLearning.UniformLearning.bucketEstimate`,
  `Cslib.MachineLearning.UniformLearning.sampleCoeff`: the empirical bucket weights and Fourier
  coefficients of the samples.
* `Cslib.MachineLearning.UniformLearning.kmHypothesis`,
  `Cslib.MachineLearning.UniformLearning.kmLearner`: the Kushilevitz–Mansour algorithm.
* `Cslib.MachineLearning.UniformLearning.KMAccurate`: accurate samples.

## Main results

* `Cslib.MachineLearning.UniformLearning.inter_mem_bucketSearch`,
  `Cslib.MachineLearning.UniformLearning.mul_card_bucketSearch_le_one`: the bucket search finds the
  heavy sets and keeps few buckets.
* `Cslib.MachineLearning.UniformLearning.uniformError_kmHypothesis_le`: the error on accurate
  samples.
* `Cslib.MachineLearning.UniformLearning.uniform_not_accurate_le`: the samples are accurate with
  high probability.
* `Cslib.MachineLearning.UniformLearning.kmLearner_learns`,
  `Cslib.MachineLearning.UniformLearning.kmLearner_learns_and_queriesAtMost`: the
  Kushilevitz–Mansour theorem.
* `Cslib.MachineLearning.UniformLearning.kmLearner_learns_decisionTree`,
  `Cslib.MachineLearning.UniformLearning.kmLearner_learns_decisionTree_and_queriesAtMost`: learning
  decision trees with membership queries.

## References

* [E. Kushilevitz and Y. Mansour, *Learning decision trees using the Fourier
  spectrum*][KushilevitzMansour1993]
* [O. Goldreich, L. Levin, *A Hard-Core Predicate for All One-Way Functions*][GoldreichLevin1989]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
* [W. Hoeffding, *Probability inequalities for sums of bounded random
  variables*][Hoeffding1963]
-/

@[expose] public section

namespace Cslib.MachineLearning.UniformLearning

open BitString Finset PACLearning Cslib.Probability
open scoped BigOperators ENNReal

variable {ι : Type*} {m : ℕ}

/-! ### The bucket search -/

section BucketSearch

variable [DecidableEq ι]

/-- The sets of coordinates weighed by the bucket search over the list `l`: the sets of
coordinates of the suffixes of `l`, from `l` itself down to the empty list. -/
def searchLevels : List ι → List (Finset ι)
  | [] => [∅]
  | i :: l => insert i l.toFinset :: searchLevels l

@[simp] theorem length_searchLevels (l : List ι) : (searchLevels l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [searchLevels, ih]

/-- The coordinates of `l` are its first level. -/
theorem toFinset_mem_searchLevels (l : List ι) : l.toFinset ∈ searchLevels l := by
  cases l with
  | nil => simp [searchLevels]
  | cons i l => simp [searchLevels]

/-- **The bucket search** of Goldreich–Levin and Kushilevitz–Mansour over the list `l` of
coordinates, given estimates `est J S` of the bucket weights `W^{S | J}` and a threshold `τ`.
Starting from the bucket of all sets, it adds the coordinates of `l` from the last to the first,
splits each surviving bucket `S` of `J` into the buckets `S` and `insert i S` of `insert i J`, and
keeps the buckets whose estimated weight is at least `τ`. -/
noncomputable def bucketSearch (est : Finset ι → Finset ι → ℝ) (τ : ℝ) :
    List ι → Finset (Finset ι)
  | [] => ({∅} : Finset (Finset ι)).filter fun S => τ ≤ est ∅ S
  | i :: l => (bucketSearch est τ l ∪ (bucketSearch est τ l).image (insert i)).filter
      fun S => τ ≤ est (insert i l.toFinset) S

/-- The bucket search reads the estimates only at its levels. -/
theorem bucketSearch_congr {est est' : Finset ι → Finset ι → ℝ} {τ : ℝ} {l : List ι}
    (h : ∀ J ∈ searchLevels l, ∀ S, est J S = est' J S) :
    bucketSearch est τ l = bucketSearch est' τ l := by
  induction l with
  | nil =>
    simp only [searchLevels, List.mem_singleton, forall_eq] at h
    simp only [bucketSearch, h]
  | cons i l ih =>
    simp only [searchLevels, List.mem_cons, forall_eq_or_imp] at h
    simp only [bucketSearch, ih h.2, h.1]

/-- Every bucket kept by the search over `l` has estimated weight at least `τ` at the level of
the coordinates of `l`. -/
theorem le_of_mem_bucketSearch {est : Finset ι → Finset ι → ℝ} {τ : ℝ} {l : List ι}
    {S : Finset ι} (hS : S ∈ bucketSearch est τ l) : τ ≤ est l.toFinset S := by
  cases l with
  | nil => exact (mem_filter.1 hS).2
  | cons i l =>
    rw [List.toFinset_cons]
    exact (mem_filter.1 hS).2

/-- **Completeness of the bucket search**: if at every level `J` the bucket of `U ∩ J` has
estimated weight at least `τ`, then the search over `l` keeps the bucket `U ∩ l`. -/
theorem inter_mem_bucketSearch {est : Finset ι → Finset ι → ℝ} {τ : ℝ} {l : List ι}
    {U : Finset ι} (h : ∀ J ∈ searchLevels l, τ ≤ est J (U ∩ J)) :
    U ∩ l.toFinset ∈ bucketSearch est τ l := by
  induction l with
  | nil =>
    simp only [searchLevels, List.mem_singleton, forall_eq, inter_empty] at h
    simp [bucketSearch, h]
  | cons i l ih =>
    simp only [searchLevels, List.mem_cons, forall_eq_or_imp] at h
    rw [List.toFinset_cons]
    refine mem_filter.2 ⟨?_, h.1⟩
    by_cases hi : i ∈ U
    · rw [inter_insert_of_mem hi]
      exact mem_union_right _ (mem_image_of_mem _ (ih h.2))
    · rw [inter_insert_of_notMem hi]
      exact mem_union_left _ (ih h.2)

variable [Fintype ι]

/-- **Few buckets survive**: if the estimates at the level of the coordinates of `l` are within
`θ² / 4` of the bucket weights of a Boolean function, then the search over `l` with threshold
`θ² / 2` keeps at most `4 / θ²` buckets. -/
theorem mul_card_bucketSearch_le_one (f : (ι → Bool) → Bool) {θ : ℝ} (est : Finset ι → Finset ι → ℝ)
    (l : List ι)
    (hW : ∀ S, |est l.toFinset S - bucketWeight (fun x => signVal (f x)) l.toFinset S| <
      θ ^ 2 / 4) :
    θ ^ 2 / 4 * #(bucketSearch est (θ ^ 2 / 2) l) ≤ 1 := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  have hS (S : Finset ι) (hS : S ∈ bucketSearch est (θ ^ 2 / 2) l) :
      θ ^ 2 / 4 ≤ bucketWeight F l.toFinset S := by
    have h₁ := le_of_mem_bucketSearch hS
    have h₂ := (abs_lt.1 (hW S)).2
    linarith
  calc θ ^ 2 / 4 * #(bucketSearch est (θ ^ 2 / 2) l)
      = ∑ _S ∈ bucketSearch est (θ ^ 2 / 2) l, θ ^ 2 / 4 := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ S ∈ bucketSearch est (θ ^ 2 / 2) l, bucketWeight F l.toFinset S := sum_le_sum hS
    _ ≤ ∑ U, fourierCoeff F U ^ 2 := sum_bucketWeight_le F _ _
    _ = 1 := sum_fourierCoeff_sq_signVal f

end BucketSearch

/-! ### The algorithm -/

variable [Fintype ι] [DecidableEq ι]

variable (ι) in
/-- The Boolean functions whose spectral norm `∑_S |f̂(S)|`, read as signs, is at most `L`. -/
def spectralNormClass (L : ℝ) : ConceptClass (ι → Bool) Bool :=
  {f | ∑ S, |fourierCoeff (fun x => signVal (f x)) S| ≤ L}

variable (ι) in
/-- The functions computed by decision trees with at most `L` leaves. -/
def decisionTreeClass (L : ℕ) : ConceptClass (ι → Bool) Bool :=
  {f | ∃ t : DecisionTree ι Bool, t.Computes f ∧ t.leafCount ≤ L}

/-- The empirical estimate of the bucket weight `W^{S | J}` of `g`, read as signs, from the
samples `ω j = (x, y, z)`: the average of `g (x, z) χ_S(x) g (y, z) χ_S(y)`, where `(x, z)` takes
the coordinates in `J` from `x` and the others from `z`. -/
noncomputable def bucketEstimate (g : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (J S : Finset ι) : ℝ :=
  (∑ j,
    let (x, y, z) := ω j
    signVal (g (J.piecewise x z)) * chi ℝ S x *
      (signVal (g (J.piecewise y z)) * chi ℝ S y)) / m

/-- The empirical Fourier coefficient of `g` on `S` from the first points of the samples. -/
noncomputable def sampleCoeff (g : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (S : Finset ι) : ℝ :=
  empiricalCoeff (examples g fun j => (ω j).1) S

/-- The sets found by the Kushilevitz–Mansour algorithm with threshold `θ`: the bucket search over
all coordinates, keeping the buckets with estimated weight at least `θ² / 2`. -/
noncomputable def kmCandidates (g : (ι → Bool) → Bool) (θ : ℝ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) : Finset (Finset ι) :=
  bucketSearch (bucketEstimate g ω) (θ ^ 2 / 2) (univ : Finset ι).toList

/-- The hypothesis of the Kushilevitz–Mansour algorithm: the sign of the expansion on the found
sets, with the empirical coefficients of the samples. -/
noncomputable def kmHypothesis (g : (ι → Bool) → Bool) (θ : ℝ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) : (ι → Bool) → Bool :=
  signRound fun x => ∑ S ∈ kmCandidates g θ ω, sampleCoeff g ω S * chi ℝ S x

/-- The points queried by the Kushilevitz–Mansour algorithm: the first point `x` of each sample,
and the points `(x, z)` and `(y, z)` of each sample `(x, y, z)` at every level `J` of the
search. -/
noncomputable def kmQueries (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    List (ι → Bool) :=
  (List.finRange m).map (fun j => (ω j).1) ++
    (searchLevels (univ : Finset ι).toList).flatMap fun J =>
      (List.finRange m).flatMap fun j =>
        let (x, y, z) := ω j
        [J.piecewise x z, J.piecewise y z]

/-- The algorithm queries `m (2 n + 3)` points for `n` coordinates. -/
theorem length_kmQueries (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    (kmQueries ω).length = m * (2 * Fintype.card ι + 3) := by
  have hlen (J : Finset ι) :
      ((List.finRange m).map fun j =>
        (let (x, y, z) := ω j; [J.piecewise x z, J.piecewise y z]).length) =
      (List.finRange m).map fun _ => 2 :=
    List.map_congr_left fun j _ => by rcases ω j with ⟨x, y, z⟩; rfl
  simp only [kmQueries, List.length_append, List.length_map, List.length_finRange,
    List.length_flatMap, hlen, List.map_const', List.sum_replicate, smul_eq_mul,
    length_searchLevels, length_toList, card_univ]
  ring

/-- The hypothesis depends only on the answers at the queried points. -/
theorem kmHypothesis_congr (θ : ℝ) (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))
    {g g' : (ι → Bool) → Bool} (h : ∀ x ∈ kmQueries ω, g x = g' x) :
    kmHypothesis g θ ω = kmHypothesis g' θ ω := by
  have hx (j : Fin m) : g (ω j).1 = g' (ω j).1 :=
    h _ (List.mem_append_left _ (List.mem_map.2 ⟨j, List.mem_finRange j, rfl⟩))
  have hcoeff : sampleCoeff g ω = sampleCoeff g' ω := by
    funext S
    simp only [sampleCoeff, empiricalCoeff, examples_apply, hx]
  have hmem (J : Finset ι) (hJ : J ∈ searchLevels (univ : Finset ι).toList) (j : Fin m)
      (p : ι → Bool)
      (hp : p ∈ (let (x, y, z) := ω j; [J.piecewise x z, J.piecewise y z])) :
      g p = g' p :=
    h p (List.mem_append_right _ (List.mem_flatMap.2
      ⟨J, hJ, List.mem_flatMap.2 ⟨j, List.mem_finRange j, hp⟩⟩))
  have hcand : kmCandidates g θ ω = kmCandidates g' θ ω := by
    refine bucketSearch_congr fun J hJ S => ?_
    simp only [bucketEstimate]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases hωj : ω j with ⟨x, y, z⟩
    have h₁ : g (J.piecewise x z) = g' (J.piecewise x z) :=
      hmem J hJ j _ (by simp [hωj])
    have h₂ : g (J.piecewise y z) = g' (J.piecewise y z) :=
      hmem J hJ j _ (by simp [hωj])
    simp only [h₁, h₂]
  simp only [kmHypothesis, hcoeff, hcand]

variable (ι m) in
/-- **The Kushilevitz–Mansour algorithm** with threshold `θ` from `m` samples: draw `m`
independent samples of three uniform points, query the target at the points `kmQueries`, run the
bucket search with threshold `θ² / 2` on the estimated bucket weights, and output the sign of the
expansion on the found sets with estimated coefficients. Its queries are non-adaptive. -/
noncomputable def kmLearner (θ : ℝ) :
    QueryLearner ι (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :=
  QueryLearner.ofNonadaptive kmQueries fun g ω => kmHypothesis g θ ω

/-- Run on the target `f`, the algorithm outputs `kmHypothesis f θ ω`. -/
theorem eval_kmLearner (θ : ℝ) (f : (ι → Bool) → Bool)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) :
    (kmLearner ι m θ ω).eval f = kmHypothesis f θ ω :=
  QueryLearner.eval_ofNonadaptive (fun ω _ _ h => kmHypothesis_congr θ ω h) f ω

/-- **The Kushilevitz–Mansour algorithm makes `m (2 n + 3)` membership queries** for `n`
coordinates. -/
theorem kmLearner_queriesAtMost (θ : ℝ) :
    (kmLearner ι m θ).QueriesAtMost (m * (2 * Fintype.card ι + 3)) := fun ω =>
  (QueryLearner.depth_ofNonadaptive_le _ _ ω).trans_eq (length_kmQueries ω)

/-! ### The analysis -/

/-- The samples `ω` are *accurate* for `f` at precision `γ`: every bucket estimate at every level
of the search over all coordinates, and every sample coefficient, is within `γ` of its value. -/
def KMAccurate (f : (ι → Bool) → Bool) (γ : ℝ)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) : Prop :=
  (∀ J ∈ searchLevels (univ : Finset ι).toList, ∀ S,
      |bucketEstimate f ω J S - bucketWeight (fun x => signVal (f x)) J S| < γ) ∧
    ∀ S, |sampleCoeff f ω S - fourierCoeff (fun x => signVal (f x)) S| < γ

/-- **The Kushilevitz–Mansour algorithm on accurate samples.** Let the spectral norm of `f`, read
as signs, be at most `L`, and let `θ > 0`. If the samples are accurate at precision `θ² / 4`, then
the hypothesis has error at most `θ² / 4 + θ L`. -/
theorem uniformError_kmHypothesis_le (f : (ι → Bool) → Bool) {L θ : ℝ} (hθ : 0 < θ)
    (hL : ∑ S, |fourierCoeff (fun x => signVal (f x)) S| ≤ L)
    (ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool)) (hω : KMAccurate f (θ ^ 2 / 4) ω) :
    uniformError f (kmHypothesis f θ ω) ≤ θ ^ 2 / 4 + θ * L := by
  obtain ⟨hW, hc⟩ := hω
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set T := kmCandidates f θ ω
  have huniv : ((univ : Finset ι).toList).toFinset = univ := toList_toFinset _
  -- few sets are found
  have hlev : univ ∈ searchLevels (univ : Finset ι).toList := by
    have h := toFinset_mem_searchLevels (univ : Finset ι).toList
    rwa [huniv] at h
  have hcard : θ ^ 2 / 4 * #T ≤ 1 :=
    mul_card_bucketSearch_le_one f _ _ fun S => by
      rw [huniv]
      exact hW univ hlev S
  -- every set with a coefficient of absolute value at least `θ` is found
  have hheavy (U : Finset ι) (hU : θ ^ 2 ≤ fourierCoeff F U ^ 2) : U ∈ T := by
    have h := inter_mem_bucketSearch (est := bucketEstimate f ω) (τ := θ ^ 2 / 2)
      (l := (univ : Finset ι).toList) (U := U) fun J hJ => by
        have h₁ := (abs_lt.1 (hW J hJ (U ∩ J))).1
        have h₂ := sq_fourierCoeff_le_bucketWeight F J U
        nlinarith
    rwa [huniv, inter_univ] at h
  have herr := hammingDist_signRound_sum_mul_chi_div_le f T (sampleCoeff f ω)
  have hin : ∑ S ∈ T, (fourierCoeff F S - sampleCoeff f ω S) ^ 2 ≤ θ ^ 2 / 4 :=
    calc ∑ S ∈ T, (fourierCoeff F S - sampleCoeff f ω S) ^ 2
        ≤ ∑ _S ∈ T, (θ ^ 2 / 4) ^ 2 := sum_le_sum fun S _ => by
          rw [← sq_abs, abs_sub_comm]
          exact pow_le_pow_left₀ (abs_nonneg _) (hc S).le 2
      _ = θ ^ 2 / 4 * #T * (θ ^ 2 / 4) := by rw [sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 * (θ ^ 2 / 4) := by gcongr
      _ = θ ^ 2 / 4 := one_mul _
  have hout : ∑ S ∈ Tᶜ, fourierCoeff F S ^ 2 ≤ θ * L :=
    calc ∑ S ∈ Tᶜ, fourierCoeff F S ^ 2 ≤ ∑ S ∈ Tᶜ, θ * |fourierCoeff F S| :=
          sum_le_sum fun S hS => by
            have hlt : fourierCoeff F S ^ 2 < θ ^ 2 :=
              lt_of_not_ge fun h => mem_compl.1 hS (hheavy S h)
            have habs : |fourierCoeff F S| < θ := abs_lt_of_sq_lt_sq hlt hθ.le
            rw [← sq_abs, sq]
            exact mul_le_mul_of_nonneg_right habs.le (abs_nonneg _)
      _ ≤ ∑ S, θ * |fourierCoeff F S| :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => by positivity
      _ = θ * ∑ S, |fourierCoeff F S| := (mul_sum _ _ _).symm
      _ ≤ θ * L := by gcongr
  have : uniformError f (kmHypothesis f θ ω) ≤
      ∑ S ∈ T, (fourierCoeff F S - sampleCoeff f ω S) ^ 2 + ∑ S ∈ Tᶜ, fourierCoeff F S ^ 2 :=
    herr
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- A product of two signs and two characters has absolute value at most one. -/
private theorem abs_signVal_mul_chi_mul_le_one (a b : Bool) (S : Finset ι) (x y : ι → Bool) :
    |signVal a * chi ℝ S x * (signVal b * chi ℝ S y)| ≤ 1 := by
  rw [abs_mul, abs_mul, abs_mul, abs_signVal, abs_signVal, abs_chi, abs_chi]
  norm_num

/-- **The samples are accurate with high probability**: `m` samples fail to be accurate at
precision `θ² / 4` with probability at most `2 (n + 2) 2 ^ n exp (-m θ⁴ / 32)` for `n`
coordinates. -/
theorem uniform_not_accurate_le (f : (ι → Bool) → Bool) (θ : ℝ) (m : ℕ) :
    (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
      {ω | ¬ KMAccurate f (θ ^ 2 / 4) ω} ≤
      ENNReal.ofReal (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι *
        Real.exp (-(m * θ ^ 4) / 32)) := by
  set F : (ι → Bool) → ℝ := fun x => signVal (f x)
  set n := Fintype.card ι
  set μ := (PMF.uniformOfFintype (Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool))).toOuterMeasure
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- without samples, the bound is at least one
    refine (PMF.toOuterMeasure_le_one _ _).trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [Nat.cast_zero, zero_mul, neg_zero, zero_div, Real.exp_zero, mul_one]
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  set c : ℝ := 2 * Real.exp (-(m * θ ^ 4) / 32) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hγ : (0 : ℝ) ≤ θ ^ 2 / 4 := by positivity
  have hexp : -(m * (θ ^ 2 / 4) ^ 2) / 2 = -(m * θ ^ 4) / 32 := by ring
  -- one bucket estimate
  have hbucket (J S : Finset ι) :
      μ {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|} ≤ ENNReal.ofReal c := by
    have h := PMF.uniform_abs_sum_div_sub_expect_ge_le
      (fun ((x, y, z) : (ι → Bool) × (ι → Bool) × (ι → Bool)) =>
        F (J.piecewise x z) * chi ℝ S x * (F (J.piecewise y z) * chi ℝ S y))
      (fun (x, y, z) => abs_signVal_mul_chi_mul_le_one _ _ S _ _) hm hγ
    rw [show (𝔼 p : (ι → Bool) × (ι → Bool) × (ι → Bool),
        let (x, y, z) := p
        F (J.piecewise x z) * chi ℝ S x * (F (J.piecewise y z) * chi ℝ S y)) =
        bucketWeight F J S by
      rw [bucketWeight_eq_expect_sample], hexp] at h
    exact h
  -- one sample coefficient
  have hcoeff (S : Finset ι) :
      μ {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|} ≤ ENNReal.ofReal c := by
    have h := PMF.uniform_abs_sum_div_sub_expect_ge_le
      (fun p : (ι → Bool) × (ι → Bool) × (ι → Bool) => F p.1 * chi ℝ S p.1)
      (fun p => by rw [abs_mul, abs_signVal, abs_chi, one_mul]) hm hγ
    have hmean : 𝔼 p : (ι → Bool) × (ι → Bool) × (ι → Bool), F p.1 * chi ℝ S p.1 =
        fourierCoeff F S := by
      rw [← univ_product_univ, expect_product]
      exact expect_congr rfl fun x _ => expect_const univ_nonempty (F x * chi ℝ S x)
    rw [hmean, hexp] at h
    exact h
  -- the union bound
  clear_value c
  set A := (searchLevels (univ : Finset ι).toList).toFinset
  have hA : (#A : ℝ) ≤ n + 1 := by
    have := List.toFinset_card_le (searchLevels (univ : Finset ι).toList)
    rw [length_searchLevels, length_toList, card_univ] at this
    exact_mod_cast this
  have hsub : {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool) |
      ¬ KMAccurate f (θ ^ 2 / 4) ω} ⊆
      (⋃ J ∈ A, ⋃ S ∈ (univ : Finset (Finset ι)),
        {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|}) ∪
      ⋃ S ∈ (univ : Finset (Finset ι)),
        {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, KMAccurate, not_and_or, not_forall, not_lt] at hω
    rcases hω with ⟨J, hJ, S, hS⟩ | ⟨S, hS⟩
    · exact Or.inl (Set.mem_biUnion (List.mem_toFinset.2 hJ)
        (Set.mem_biUnion (mem_univ S) hS))
    · exact Or.inr (Set.mem_biUnion (mem_univ S) hS)
  have hpow : ((#(univ : Finset (Finset ι)) : ℕ) : ℝ) = 2 ^ n := by
    rw [card_univ, Fintype.card_finset]
    push_cast
    rfl
  calc μ _ ≤ μ ((⋃ J ∈ A, ⋃ S ∈ (univ : Finset (Finset ι)),
          {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|}) ∪
        ⋃ S ∈ (univ : Finset (Finset ι)),
          {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|}) := μ.mono hsub
    _ ≤ ∑ J ∈ A, ∑ S ∈ (univ : Finset (Finset ι)),
          μ {ω | θ ^ 2 / 4 ≤ |bucketEstimate f ω J S - bucketWeight F J S|} +
        ∑ S ∈ (univ : Finset (Finset ι)),
          μ {ω | θ ^ 2 / 4 ≤ |sampleCoeff f ω S - fourierCoeff F S|} := by
        refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_)
        · refine (MeasureTheory.measure_biUnion_finset_le A _).trans (sum_le_sum fun J _ => ?_)
          exact MeasureTheory.measure_biUnion_finset_le _ _
        · exact MeasureTheory.measure_biUnion_finset_le _ _
    _ ≤ ∑ _J ∈ A, ∑ _S ∈ (univ : Finset (Finset ι)), ENNReal.ofReal c +
        ∑ _S ∈ (univ : Finset (Finset ι)), ENNReal.ofReal c :=
        add_le_add (sum_le_sum fun J _ => sum_le_sum fun S _ => hbucket J S)
          (sum_le_sum fun S _ => hcoeff S)
    _ = ENNReal.ofReal (∑ _J ∈ A, ∑ _S ∈ (univ : Finset (Finset ι)), c +
          ∑ _S ∈ (univ : Finset (Finset ι)), c) := by
        rw [ENNReal.ofReal_add (sum_nonneg fun _ _ => sum_nonneg fun _ _ => hc0)
          (sum_nonneg fun _ _ => hc0),
          ENNReal.ofReal_sum_of_nonneg fun _ _ => sum_nonneg fun _ _ => hc0,
          ENNReal.ofReal_sum_of_nonneg fun _ _ => hc0]
    _ ≤ ENNReal.ofReal (2 * (n + 2) * 2 ^ n * Real.exp (-(m * θ ^ 4) / 32)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [sum_const, nsmul_eq_mul, hpow]
        have h2n : (0 : ℝ) ≤ 2 ^ n * c := by positivity
        calc (#A : ℝ) * (2 ^ n * c) + 2 ^ n * c = (#A + 1) * (2 ^ n * c) := by ring
          _ ≤ (n + 1 + 1) * (2 ^ n * c) := by gcongr
          _ = 2 * (n + 2) * 2 ^ n * Real.exp (-(m * θ ^ 4) / 32) := by rw [hcdef]; ring

/-- **The Kushilevitz–Mansour theorem** [KushilevitzMansour1993]
[O'Donnell, Theorem 3.38][ODonnell2014]: for `n` coordinates, the Kushilevitz–Mansour algorithm
with threshold `ε / (2 L)` from `m ≥ (512 L⁴ / ε⁴) log (2 (n + 2) 2 ^ n / δ)` samples, hence
`m (2 n + 3)` membership queries (`kmLearner_queriesAtMost`), learns the Boolean functions whose
spectral norm, read as signs, is at most `L`, with error `ε` and confidence `1 - δ`. -/
theorem kmLearner_learns {L ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * L ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (spectralNormClass ι L) ε δ := by
  rw [QueryLearner.learns_iff]
  intro f hf
  simp only [eval_kmLearner]
  set n := Fintype.card ι
  have hL1 : 1 ≤ L := (one_le_sum_abs_fourierCoeff_signVal f).trans hf
  have hL : 0 < L := one_pos.trans_le hL1
  rcases le_or_gt 1 ε with hε1 | hε1
  · -- an error above `ε ≥ 1` is impossible
    have hempty : {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool) |
        ε < uniformError f (kmHypothesis f (ε / (2 * L)) ω)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω =>
        absurd ((uniformError_le_one _ _).trans hε1) (not_le.2 hω)
    rw [hempty, MeasureTheory.measure_empty]
    exact zero_le
  set θ := ε / (2 * L)
  have hθ : 0 < θ := by positivity
  -- on accurate samples the error is at most `ε`
  have hsub : {ω : Fin m → (ι → Bool) × (ι → Bool) × (ι → Bool) |
      ε < uniformError f (kmHypothesis f θ ω)} ⊆ {ω | ¬ KMAccurate f (θ ^ 2 / 4) ω} := by
    intro ω hω hgood
    have hω' : ε < uniformError f (kmHypothesis f θ ω) := hω
    have h := uniformError_kmHypothesis_le f hθ hf ω hgood
    have hθL : θ * L = ε / 2 := by simp only [θ]; field_simp
    have hθ2 : θ ^ 2 / 4 ≤ ε / 16 := by
      have : θ ^ 2 = ε ^ 2 / (4 * L ^ 2) := by simp only [θ]; ring
      rw [this, div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg L, mul_le_mul_of_nonneg_left hL1 hL.le]
    linarith
  refine ((PMF.uniformOfFintype _).toOuterMeasure.mono hsub).trans
    ((uniform_not_accurate_le f θ m).trans (ENNReal.ofReal_le_ofReal ?_))
  -- the sample size makes the failure probability at most `δ`
  set K : ℝ := 2 * (n + 2) * 2 ^ n
  have hK : 0 < K := by positivity
  have hθ4 : θ ^ 4 / 32 = ε ^ 4 / (512 * L ^ 4) := by simp only [θ]; ring
  have hlog : Real.log (K / δ) ≤ m * ε ^ 4 / (512 * L ^ 4) := by
    rw [le_div_iff₀ (by positivity)]
    have := (div_mul_eq_mul_div (512 * L ^ 4) (ε ^ 4) (Real.log (K / δ))).symm.trans_le hm
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hexp : Real.exp (-(m * θ ^ 4) / 32) ≤ δ / K := by
    calc Real.exp (-(m * θ ^ 4) / 32) = Real.exp (-(m * (θ ^ 4 / 32))) := by ring_nf
      _ = Real.exp (-(m * ε ^ 4 / (512 * L ^ 4))) := by rw [hθ4, mul_div_assoc]
      _ ≤ Real.exp (-Real.log (K / δ)) := Real.exp_le_exp.2 (neg_le_neg hlog)
      _ = δ / K := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  calc K * Real.exp (-(m * θ ^ 4) / 32) ≤ K * (δ / K) := by gcongr
    _ = δ := by field_simp

/-- **Learning decision trees with membership queries** [KushilevitzMansour1993]
[O'Donnell, Theorem 3.38][ODonnell2014]: for `n` coordinates, the Kushilevitz–Mansour algorithm
with threshold `ε / (2 L)` from `m ≥ (512 L⁴ / ε⁴) log (2 (n + 2) 2 ^ n / δ)` samples, hence
`m (2 n + 3)` membership queries, learns the functions computed by decision trees with at most
`L` leaves, with error `ε` and confidence `1 - δ`. -/
theorem kmLearner_learns_decisionTree {L : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * (L : ℝ) ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (decisionTreeClass ι L) ε δ := by
  refine (kmLearner_learns hε hδ hm).mono (fun f ⟨t, ht, hL⟩ => ?_) le_rfl le_rfl
  have hf : f = t.eval := (DecisionTree.computes_iff.1 ht).symm
  subst hf
  exact (DecisionTree.sum_abs_fourierCoeff_signVal_le_leafCount id t).trans
    (by exact_mod_cast hL)

/-- **The Kushilevitz–Mansour theorem with its query count**: under the hypotheses of
`kmLearner_learns`, the algorithm learns the functions of spectral norm at most `L` with
`m (2 n + 3)` membership queries for `n` coordinates. -/
theorem kmLearner_learns_and_queriesAtMost {L ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * L ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (spectralNormClass ι L) ε δ ∧
      (kmLearner ι m (ε / (2 * L))).QueriesAtMost (m * (2 * Fintype.card ι + 3)) :=
  ⟨kmLearner_learns hε hδ hm, kmLearner_queriesAtMost _⟩

/-- **Learning decision trees with membership queries, with the query count**: under the
hypotheses of `kmLearner_learns_decisionTree`, the algorithm learns the functions computed by
decision trees with at most `L` leaves with `m (2 n + 3)` membership queries for `n`
coordinates. -/
theorem kmLearner_learns_decisionTree_and_queriesAtMost {L : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) {m : ℕ}
    (hm : 512 * (L : ℝ) ^ 4 / ε ^ 4 *
      Real.log (2 * (Fintype.card ι + 2) * 2 ^ Fintype.card ι / δ) ≤ m) :
    (kmLearner ι m (ε / (2 * L))).Learns (PMF.uniformOfFintype _) (decisionTreeClass ι L) ε δ ∧
      (kmLearner ι m (ε / (2 * L))).QueriesAtMost (m * (2 * Fintype.card ι + 3)) :=
  ⟨kmLearner_learns_decisionTree hε hδ hm, kmLearner_queriesAtMost _⟩

end Cslib.MachineLearning.UniformLearning
