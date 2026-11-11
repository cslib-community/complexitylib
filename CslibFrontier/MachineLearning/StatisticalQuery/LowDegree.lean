/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.SignApproximation
public import CslibFrontier.Foundations.Data.BitString.Parity
public import CslibFrontier.MachineLearning.StatisticalQuery.Basic
public import CslibFrontier.MachineLearning.UniformLearning.Basic
import CslibFrontier.Foundations.BooleanAnalysis.LowDegree
import CslibFrontier.Probability.PMF

/-!
# The low-degree algorithm from statistical queries

The low-degree algorithm of Linial, Mansour and Nisan [LinialMansourNisan1993] estimates the
Fourier coefficients `f̂(S) = E_x [f(x) χ_S(x)]` of the target, read as signs, on the sets `S` of
at most `t` coordinates, and outputs the sign of the truncated expansion `∑_{#S ≤ t} c_S χ_S`.
Each coefficient is the expectation of the statistical query `(x, y) ↦ y χ_S(x)` under the
uniform distribution (`StatisticalQuery.expect_uniformOfFintype_charQuery`), so the algorithm
is a non-adaptive statistical query learner (`StatisticalQuery.lowDegree`) making one query for
each of the `N` sets of at most `t` coordinates; Kearns notes that it falls into the statistical
query model without modification [Kearns1998, Section 1] and lists it among the applications of
Section 6. With tolerance `τ` every estimate is within `τ` of its coefficient, so the hypothesis has
error at most `N τ² + κ` for every target whose Fourier weight above degree `t` is at most `κ`
(`StatisticalQuery.learns_lowDegree`). In particular the parities on at most `t` coordinates,
whose weight above degree `t` is zero, are learned with error `N τ²`
(`StatisticalQuery.learns_lowDegree_parityOn`), in contrast to the parities on all coordinates
(`StatisticalQuery.LearnsStateless.two_pow_card_le_of_parityOn_mem`).

The queries are asked through `StatisticalQuery.askAll`, which asks a list of indexed queries in
order and returns the answers as a function of the index.

## Main definitions

* `Cslib.MachineLearning.StatisticalQuery.askAll`: asking a list of queries.
* `Cslib.MachineLearning.StatisticalQuery.charQuery`: the query whose expectation is a Fourier
  coefficient.
* `Cslib.MachineLearning.StatisticalQuery.lowDegree`: the low-degree algorithm.

## Main results

* `Cslib.MachineLearning.StatisticalQuery.disagreement_uniformOfFintype`: under the uniform
  distribution the disagreement is the uniform error.
* `Cslib.MachineLearning.StatisticalQuery.isQueryBounded_lowDegree`: the low-degree algorithm makes
  one query for each set of at most `t` coordinates.
* `Cslib.MachineLearning.StatisticalQuery.learns_lowDegree`: the low-degree algorithm learns the
  functions with Fourier weight at most `κ` above degree `t` with error `N τ² + κ`.
* `Cslib.MachineLearning.StatisticalQuery.learns_lowDegree_parityOn`: it learns the parities on at
  most `t` coordinates with error `N τ²`.

## References

* [N. Linial, Y. Mansour, N. Nisan, *Constant depth circuits, Fourier transform, and
  learnability*][LinialMansourNisan1993]
* [M. Kearns, *Efficient noise-tolerant learning from statistical queries*][Kearns1998]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

namespace Cslib.MachineLearning.StatisticalQuery

open BitString Finset PACLearning Cslib.Probability
open scoped BigOperators

/-! ### Asking a list of queries -/

section AskAll

variable {X κ : Type} [DecidableEq κ]

/-- Ask the queries `Q k` for the indices `k` of the list `ks`, in order, and return the answers as
a function of the index; the indices not in the list get `0`. -/
def askAll (Q : κ → Query X) : List κ → OracleComp (spec X) (κ → ℝ)
  | [] => pure fun _ => 0
  | k :: ks => do
    let a ← OracleComp.query (Q k)
    let rest ← askAll Q ks
    pure (Function.update rest k a)

/-- Asking a list of queries makes one call for each entry. -/
theorem isQueryBounded_askAll (Q : κ → Query X) (ks : List κ) :
    OracleComp.IsQueryBounded (askAll Q ks) ks.length := by
  induction ks with
  | nil => exact .pure _ 0
  | cons k ks ih =>
    have h := (OracleComp.IsCostBounded.query (cost := fun _ => 1) (spec := spec X) (Q k)).bind
      fun a => ih.bind fun rest => .pure (Function.update rest k a) 0
    rw [List.length_cons, Nat.add_comm]
    exact h

/-- Every answer returned by `askAll` is a possible answer to its query. -/
theorem apply_mem_of_mem_supportWith_askAll {Q : κ → Query X} {possible : Query X → Set ℝ}
    {ks : List κ} {r : κ → ℝ} (hr : r ∈ OracleComp.supportWith possible (askAll Q ks)) :
    ∀ k ∈ ks, r k ∈ possible (Q k) := by
  induction ks generalizing r with
  | nil => simp
  | cons k ks ih =>
    simp only [askAll, OracleComp.mem_supportWith_bind_iff, OracleComp.supportWith_query,
      OracleComp.supportWith_pure, Set.mem_singleton_iff] at hr
    obtain ⟨a, ha, rest, hrest, rfl⟩ := hr
    intro k' hk'
    by_cases hkk : k' = k
    · subst hkk
      rw [Function.update_self]
      exact ha
    · rw [Function.update_of_ne hkk]
      exact ih hrest k' ((List.mem_cons.1 hk').resolve_left hkk)

end AskAll

/-! ### The low-degree algorithm -/

variable {ι : Type}

/-- The statistical query `(x, y) ↦ y χ_S(x)` reading the label `y` as a sign: its expectation
under the uniform distribution is the Fourier coefficient of the target on `S`. -/
noncomputable def charQuery (S : Finset ι) : Query (ι → Bool) where
  toFun x y := signVal y * chi ℝ S x
  abs_le_one' x y := by rw [abs_mul, abs_signVal, abs_chi, one_mul]

@[simp] theorem charQuery_apply (S : Finset ι) (x : ι → Bool) (y : Bool) :
    charQuery S x y = signVal y * chi ℝ S x :=
  rfl

variable [Fintype ι] [DecidableEq ι]

/-- Under the uniform distribution the expectation of `charQuery S` is the Fourier coefficient on
`S` of the target read as signs. -/
theorem expect_uniformOfFintype_charQuery (c : (ι → Bool) → Bool) (S : Finset ι) :
    expect (PMF.uniformOfFintype (ι → Bool)) c (charQuery S) =
      fourierCoeff (fun x => signVal (c x)) S := by
  simp only [expect, charQuery_apply, fourierCoeff, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Fintype.expect_eq_sum_div_card, ← mul_sum, div_eq_inv_mul]

/-- Under the uniform distribution the disagreement of `f` and `g` is the fraction of the points
where they differ, the uniform error of `g` for the target `f`. -/
theorem disagreement_uniformOfFintype (f g : (ι → Bool) → Bool) :
    disagreement (PMF.uniformOfFintype (ι → Bool)) f g = UniformLearning.uniformError f g := by
  rw [UniformLearning.uniformError, disagreement, hammingDist, div_eq_inv_mul]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ← mul_sum,
    Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]
  congr 1
  rw [Finset.card_filter, Nat.cast_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases h : f x = g x
  · simp [h]
  · simp [h, Ne.symm h]

variable (ι) in
/-- **The low-degree algorithm** of degree `t` from statistical queries: ask the correlation with
`χ_S` for every set `S` of at most `t` coordinates, and output the sign of the truncated expansion
`∑_{#S ≤ t} c_S χ_S` with the answers `c_S`. -/
noncomputable def lowDegree (t : ℕ) : OracleComp (spec (ι → Bool)) ((ι → Bool) → Bool) :=
  (fun c : Finset ι → ℝ => signRound fun x : ι → Bool => ∑ S with #S ≤ t, c S * chi ℝ S x) <$>
    askAll charQuery ({S : Finset ι | #S ≤ t} : Finset (Finset ι)).toList

/-- The low-degree algorithm makes one query for each set of at most `t` coordinates. -/
theorem isQueryBounded_lowDegree (t : ℕ) :
    OracleComp.IsQueryBounded (lowDegree ι t) #{S : Finset ι | #S ≤ t} := by
  unfold lowDegree
  refine (OracleComp.isCostBounded_map_iff _ _ _).2 ?_
  rw [← Finset.length_toList]
  exact isQueryBounded_askAll _ _

/-- **The low-degree algorithm learns from statistical queries** [LinialMansourNisan1993]
[Kearns1998, Section 6]. Let `N` be the number of sets of at most `t` coordinates. Under the
uniform distribution with tolerance `τ`, the low-degree algorithm of degree `t` learns, with error
`N τ² + κ`, every class of Boolean functions whose Fourier weight, read as signs, on the sets of
more than `t` coordinates is at most `κ`. -/
theorem learns_lowDegree (t : ℕ) {C : ConceptClass (ι → Bool) Bool} {τ κ : ℝ}
    (hC : ∀ c ∈ C, ∑ S with t < #S, fourierCoeff (fun x => signVal (c x)) S ^ 2 ≤ κ) :
    Learns (lowDegree ι t) (PMF.uniformOfFintype (ι → Bool)) C τ
      (#{S : Finset ι | #S ≤ t} * τ ^ 2 + κ) := by
  intro c hc h hh
  unfold lowDegree at hh
  set T : Finset (Finset ι) := {S : Finset ι | #S ≤ t} with hT
  obtain ⟨a, ha, rfl⟩ := OracleComp.mem_supportWith_map_iff.1 hh
  have hvalid := apply_mem_of_mem_supportWith_askAll ha
  rw [disagreement_uniformOfFintype, UniformLearning.uniformError]
  refine (hammingDist_signRound_sum_mul_chi_div_le c T a).trans ?_
  have hcompl : Tᶜ = ({S : Finset ι | t < #S} : Finset (Finset ι)) := by
    rw [hT, compl_filter]
    simp only [not_le]
  rw [hcompl]
  refine add_le_add ?_ (hC c hc)
  calc ∑ S ∈ T, (fourierCoeff (fun x => signVal (c x)) S - a S) ^ 2 ≤ ∑ _S ∈ T, τ ^ 2 :=
        sum_le_sum fun S hS => by
          have h := hvalid S (Finset.mem_toList.2 hS)
          rw [valid, Set.mem_ofPred_eq, expect_uniformOfFintype_charQuery] at h
          rw [← sq_abs, abs_sub_comm]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = #T * τ ^ 2 := by rw [sum_const, nsmul_eq_mul]

/-- **Parities on at most `t` coordinates are learnable from statistical queries.** Under the
uniform distribution with tolerance `τ`, the low-degree algorithm of degree `t` learns the parities
on at most `t` coordinates with error `N τ²`, where `N` is the number of sets of at most `t`
coordinates: about `n ^ t` queries of tolerance about `n ^ {-t/2}` suffice, whereas the parities on
all `n` coordinates need `2 ^ {Ω(n)}` queries or tolerance `2 ^ {-Ω(n)}`
(`LearnsStateless.two_pow_card_le_of_parityOn_mem`). -/
theorem learns_lowDegree_parityOn (t : ℕ) {τ : ℝ} :
    Learns (lowDegree ι t) (PMF.uniformOfFintype (ι → Bool))
      {c | ∃ S : Finset ι, #S ≤ t ∧ c = parityOn S} τ (#{S : Finset ι | #S ≤ t} * τ ^ 2) := by
  have h := learns_lowDegree t (κ := 0) (τ := τ)
    (C := {c | ∃ S : Finset ι, #S ≤ t ∧ c = parityOn S}) fun c hc => by
      obtain ⟨S, hS, rfl⟩ := hc
      refine (sum_eq_zero fun U hU => ?_).le
      have hUS : U ≠ S := by
        rintro rfl
        exact absurd hS (not_le.2 (mem_filter.1 hU).2)
      rw [fourierCoeff_signVal_parityOn, ite_eq_right hUS]
      norm_num
  simpa only [add_zero] using h

end Cslib.MachineLearning.StatisticalQuery
