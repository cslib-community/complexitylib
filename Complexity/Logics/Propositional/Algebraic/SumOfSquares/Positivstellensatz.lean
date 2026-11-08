/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.Algebraic.SumOfSquares.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Positivstellensatz refutations with inequalities

A **Positivstellensatz refutation** of the inequality constraints `f ≥ 0`, `f ∈ I`, and the
equations `g = 0`, `g ∈ E`, over an ordered commutative ring `R` is an identity

`∑ⱼ hⱼ gⱼ + ∑ₖ cₖ sₖ ² ∏_{f ∈ Sₖ} f = -1`

with `gⱼ ∈ E`, finite sets `Sₖ ⊆ I` and weights `cₖ ≥ 0`. No common solution of the constraints
can exist, since the left-hand side is nonnegative there
(`Psatz.RefutableInDegree.not_exists_eval`). Degree is counted per summand: a refutation has
**degree at most `d`** (`Psatz.Refutation I E d`) when every `hⱼ gⱼ` has total degree at most `d`
and every summand has formal degree `2 deg sₖ + ∑_{f ∈ Sₖ} deg f` at most `d`
(`Psatz.Summand.degree`). The formal degree bounds the total degree
(`Psatz.Summand.totalDegree_toPoly_le`), and over a domain it is the total degree of every nonzero
summand (`Psatz.Summand.totalDegree_toPoly`).

This is the degree-`d` sum-of-squares refutation of [Barak and Steurer, lecture "The sos
algorithm over general domains", Definition 1 and the remark after Theorem 2][BarakSteurer2016],
with each sum of squares `p_S` written as a sum of weighted squares, and with equations added. That
definition has inequalities only. Writing `g = 0` there as the pair `g ≥ 0`, `-g ≥ 0`, every
summand that contains one of the two is a multiple `h g` of degree at most `d`, an equation term
here. Equation terms allow a multiplier `h` of any sign, as in `SOS.Refutation`, and a
sum-of-squares refutation of equations is the case without inequality factors
(`SOS.RefutableInDegree.psatz`, `Psatz.refutableInDegree_empty_iff`). The degree bound of Barak
and Steurer is on the total degree of `p_S ∏_{f ∈ S} f`. The formal degree here is at least that,
and the two agree on nonzero summands over a domain.

The dual objects are **pseudo-expectations** (`Psatz.PseudoExpectation I E d`): linear maps `Ẽ`
with `Ẽ 1 = 1`, `Ẽ (s ^ 2 ∏_{f ∈ S} f) ≥ 0` for finite `S ⊆ I` of formal degree at most `d`,
and `Ẽ (q g) = 0` for `g ∈ E` whenever `deg (q g) ≤ d`. This is the formal expectation of a
degree-`d` pseudo-distribution that satisfies the constraints [Barak and Steurer, lecture "The sos
algorithm over general domains", Definitions 5 and 7 with `ℓ = 0`][BarakSteurer2016], given
directly as a linear functional. Applying `Ẽ` to a refutation gives `0 + (nonnegative) = -1`, so
**a degree-`d` pseudo-expectation rules out degree-`d` refutations**
(`Psatz.PseudoExpectation.not_refutableInDegree`). This is the easy direction of the duality
[Barak and Steurer, lecture "The sos algorithm over general domains", Theorem 8, case
`f = -1`][BarakSteurer2016]. Evaluation at a point that satisfies the inequalities and makes the
equations vanish is a pseudo-expectation (`Psatz.PseudoExpectation.ofEval`). The converse of the
duality is not formalized.

## Main definitions

* `Cslib.Logic.PL.SOS.Psatz.Summand`: a summand `c · s ^ 2 · ∏_{f ∈ S} f`.
* `Cslib.Logic.PL.SOS.Psatz.Refutation`: Positivstellensatz refutations of degree at most `d`.
* `Cslib.Logic.PL.SOS.Psatz.RefutableInDegree`: a refutation of degree at most `d` exists.
* `Cslib.Logic.PL.SOS.Psatz.PseudoExpectation`: pseudo-expectations of degree `d`.

## Main results

* `Cslib.Logic.PL.SOS.Psatz.PseudoExpectation.not_refutableInDegree`: a degree-`d`
  pseudo-expectation rules out refutations of degree at most `d`.
* `Cslib.Logic.PL.SOS.Psatz.RefutableInDegree.not_exists_eval`: soundness.
* `Cslib.Logic.PL.SOS.Psatz.RefutableInDegree.of_sum`: building refutations from finite
  families.
* `Cslib.Logic.PL.SOS.RefutableInDegree.psatz`,
  `Cslib.Logic.PL.SOS.Psatz.refutableInDegree_empty_iff`: sum-of-squares refutations of equations
  are the refutations without inequality factors.

## References

* [B. Barak, D. Steurer, *Proofs, beliefs, and algorithms through the lens of sum-of-squares*,
  lecture notes][BarakSteurer2016]
-/

public section

namespace Cslib.Logic.PL.SOS.Psatz

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- One **summand** `c · s ^ 2 · ∏_{f ∈ S} f` of a Positivstellensatz refutation: a finite set `S`
of inequality constraints, a weight `c` and a polynomial `s`. -/
structure Summand (σ R : Type*) [CommRing R] where
  /-- The set `S` of inequality constraints multiplied together. -/
  factors : Finset (MvPolynomial σ R)
  /-- The weight `c`, nonnegative in a refutation. -/
  weight : R
  /-- The polynomial `s` that is squared. -/
  base : MvPolynomial σ R

namespace Summand

/-- The polynomial `c · s ^ 2 · ∏_{f ∈ S} f` of a summand. -/
noncomputable def toPoly (t : Summand σ R) : MvPolynomial σ R :=
  C t.weight * t.base ^ 2 * ∏ f ∈ t.factors, f

theorem toPoly_def (t : Summand σ R) :
    t.toPoly = C t.weight * t.base ^ 2 * ∏ f ∈ t.factors, f := by
  rw [toPoly]

/-- The formal degree `2 deg s + ∑_{f ∈ S} deg f` of a summand. -/
def degree (t : Summand σ R) : ℕ :=
  2 * t.base.totalDegree + ∑ f ∈ t.factors, f.totalDegree

theorem degree_def (t : Summand σ R) :
    t.degree = 2 * t.base.totalDegree + ∑ f ∈ t.factors, f.totalDegree := by
  rw [degree]

/-- The formal degree of a summand bounds the total degree of its polynomial. -/
theorem totalDegree_toPoly_le (t : Summand σ R) : t.toPoly.totalDegree ≤ t.degree := by
  rw [toPoly, degree]
  refine (totalDegree_mul _ _).trans (add_le_add ?_ (totalDegree_finsetProd _ _))
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact totalDegree_pow _ _

/-- Over a domain, the formal degree of a summand with nonzero weight, base and factors is the total
degree of its polynomial. -/
theorem totalDegree_toPoly [IsDomain R] (t : Summand σ R) (hc : t.weight ≠ 0) (hs : t.base ≠ 0)
    (hS : (0 : MvPolynomial σ R) ∉ t.factors) : t.toPoly.totalDegree = t.degree := by
  classical
  have hprod (S : Finset (MvPolynomial σ R)) (h0 : (0 : MvPolynomial σ R) ∉ S) :
      (∏ f ∈ S, f).totalDegree = ∑ f ∈ S, f.totalDegree := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.mem_insert, not_or] at h0
      rw [Finset.prod_insert ha, Finset.sum_insert ha, totalDegree_mul_of_isDomain (Ne.symm h0.1)
        (Finset.prod_ne_zero_iff.2 fun f hf h => h0.2 (h ▸ hf)), ih h0.2]
  have hc' : (C t.weight : MvPolynomial σ R) ≠ 0 := C_ne_zero.2 hc
  rw [toPoly, degree, totalDegree_mul_of_isDomain (mul_ne_zero hc' (pow_ne_zero 2 hs))
    (Finset.prod_ne_zero_iff.2 fun f hf h => hS (h ▸ hf)), totalDegree_mul_of_isDomain hc'
    (pow_ne_zero 2 hs), totalDegree_C, sq, totalDegree_mul_of_isDomain hs hs, hprod _ hS]
  ring

end Summand

variable [LinearOrder R]

/-- A **Positivstellensatz refutation of degree at most `d`** of the constraints `f ≥ 0`, `f ∈ I`,
and `g = 0`, `g ∈ E`: equation terms, pairs `(h, g)` with `g ∈ E` standing for `h * g`, and
summands `c · s ^ 2 · ∏_{f ∈ S} f` with `S ⊆ I` and `c ≥ 0`, such that
`∑ h * g + ∑ c · s ^ 2 · ∏_{f ∈ S} f = -1`, with every `h * g` of total degree at most `d` and every
summand of formal degree `2 deg s + ∑_{f ∈ S} deg f` at most `d`. -/
structure Refutation (I E : Set (MvPolynomial σ R)) (d : ℕ) where
  /-- The equation terms: a pair `(h, g)` stands for `h * g`. -/
  eqTerms : List (MvPolynomial σ R × MvPolynomial σ R)
  /-- The summands `c · s ^ 2 · ∏_{f ∈ S} f`. -/
  summands : List (Summand σ R)
  /-- The refutation identity. -/
  eq : (eqTerms.map fun p => p.1 * p.2).sum + (summands.map Summand.toPoly).sum = -1
  /-- Every equation term multiplies a member of `E`. -/
  eqTerm_mem : ∀ p ∈ eqTerms, p.2 ∈ E
  /-- Every equation term has total degree at most `d`. -/
  totalDegree_eqTerm_le : ∀ p ∈ eqTerms, (p.1 * p.2).totalDegree ≤ d
  /-- Every summand multiplies members of `I`. -/
  factors_subset : ∀ t ∈ summands, ↑t.factors ⊆ I
  /-- Every weight is nonnegative. -/
  weight_nonneg : ∀ t ∈ summands, 0 ≤ t.weight
  /-- Every summand has formal degree at most `d`. -/
  degree_le : ∀ t ∈ summands, t.degree ≤ d

/-- The constraints have a Positivstellensatz refutation of degree at most `d`. -/
def RefutableInDegree (I E : Set (MvPolynomial σ R)) (d : ℕ) : Prop :=
  Nonempty (Refutation I E d)

/-- `RefutableInDegree I E d` holds exactly when a refutation of degree at most `d` exists. -/
theorem refutableInDegree_iff {I E : Set (MvPolynomial σ R)} {d : ℕ} :
    RefutableInDegree I E d ↔ Nonempty (Refutation I E d) :=
  Iff.rfl

/-- A refutation of degree at most `d` witnesses `RefutableInDegree I E d`. -/
theorem Refutation.refutableInDegree {I E : Set (MvPolynomial σ R)} {d : ℕ}
    (r : Refutation I E d) : RefutableInDegree I E d :=
  ⟨r⟩

/-- Refutability is monotone in the constraints and in the degree. -/
theorem RefutableInDegree.mono {I I' E E' : Set (MvPolynomial σ R)} {d d' : ℕ}
    (h : RefutableInDegree I E d) (hI : I ⊆ I') (hE : E ⊆ E') (hd : d ≤ d') :
    RefutableInDegree I' E' d' :=
  let ⟨r⟩ := h
  ⟨{ r with
    eqTerm_mem := fun p hp => hE (r.eqTerm_mem p hp)
    totalDegree_eqTerm_le := fun p hp => (r.totalDegree_eqTerm_le p hp).trans hd
    factors_subset := fun t ht => (r.factors_subset t ht).trans hI
    degree_le := fun t ht => (r.degree_le t ht).trans hd }⟩

/-- **Building a refutation from finite families**: equation terms `h i * g i` and summands
`t k`. -/
theorem RefutableInDegree.of_sum {I E : Set (MvPolynomial σ R)} {d : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] (h g : ι → MvPolynomial σ R) (t : κ → Summand σ R)
    (hg : ∀ i, g i ∈ E) (hgd : ∀ i, (h i * g i).totalDegree ≤ d)
    (ht : ∀ k, ↑(t k).factors ⊆ I) (hw : ∀ k, 0 ≤ (t k).weight) (hd : ∀ k, (t k).degree ≤ d)
    (heq : ∑ i, h i * g i + ∑ k, (t k).toPoly = -1) : RefutableInDegree I E d := by
  refine ⟨⟨Finset.univ.toList.map fun i => (h i, g i), Finset.univ.toList.map t, ?_, ?_, ?_, ?_,
    ?_, ?_⟩⟩
  · rw [List.map_map, List.map_map, ← heq]
    simp only [Function.comp_def, Finset.sum_map_toList]
  all_goals simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  all_goals rintro _ ⟨i, rfl⟩
  exacts [hg i, hgd i, ht i, hw i, hd i]

/-- A **pseudo-expectation of degree `d`** for the constraints `f ≥ 0`, `f ∈ I`, and `g = 0`,
`g ∈ E`: a linear map `Ẽ` from polynomials to `R` with `Ẽ 1 = 1`, `Ẽ (s ^ 2 ∏_{f ∈ S} f) ≥ 0`
for finite `S ⊆ I` with `2 deg s + ∑_{f ∈ S} deg f ≤ d`, and `Ẽ (q g) = 0` for `g ∈ E` whenever
`deg (q g) ≤ d`. -/
structure PseudoExpectation (I E : Set (MvPolynomial σ R)) (d : ℕ) where
  /-- The pseudo-expectation, as a linear map. -/
  toLinearMap : MvPolynomial σ R →ₗ[R] R
  /-- `Ẽ 1 = 1`. -/
  map_one : toLinearMap 1 = 1
  /-- `Ẽ (s ^ 2 ∏_{f ∈ S} f) ≥ 0` for `S ⊆ I` when the formal degree is at most `d`. -/
  map_sq_mul_prod_nonneg : ∀ (S : Finset (MvPolynomial σ R)) (s : MvPolynomial σ R), ↑S ⊆ I →
    2 * s.totalDegree + ∑ f ∈ S, f.totalDegree ≤ d → 0 ≤ toLinearMap (s ^ 2 * ∏ f ∈ S, f)
  /-- `Ẽ (q g) = 0` for `g ∈ E` when `q g` has total degree at most `d`. -/
  map_mul_eq_zero : ∀ g ∈ E, ∀ q : MvPolynomial σ R, (q * g).totalDegree ≤ d →
    toLinearMap (q * g) = 0

namespace PseudoExpectation

variable {I E : Set (MvPolynomial σ R)} {d : ℕ}

/-- Evaluation at a point that satisfies the inequalities, and at which the multiples of the
equations of total degree at most `d` vanish, is a pseudo-expectation of degree `d`. -/
noncomputable def ofEval [IsOrderedRing R] (x : σ → R) (hI : ∀ f ∈ I, 0 ≤ eval x f)
    (hE : ∀ g ∈ E, ∀ q : MvPolynomial σ R, (q * g).totalDegree ≤ d → eval x (q * g) = 0) :
    PseudoExpectation I E d where
  toLinearMap := (aeval x).toLinearMap
  map_one := by simp
  map_sq_mul_prod_nonneg S s hS _ := by
    simp only [AlgHom.toLinearMap_apply, map_mul, map_pow, map_prod]
    exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg fun f hf => hI f (hS hf))
  map_mul_eq_zero g hg q hq := hE g hg q hq

/-- The pseudo-expectation `ofEval x hI hE` is evaluation at `x`. -/
@[simp] theorem ofEval_apply [IsOrderedRing R] (x : σ → R) (hI : ∀ f ∈ I, 0 ≤ eval x f)
    (hE : ∀ g ∈ E, ∀ q : MvPolynomial σ R, (q * g).totalDegree ≤ d → eval x (q * g) = 0)
    (p : MvPolynomial σ R) : (ofEval x hI hE).toLinearMap p = eval x p := by
  simp [ofEval]

/-- **Pseudo-expectations rule out refutations**: over a strictly ordered ring, if a
pseudo-expectation of degree `d` exists, there is no Positivstellensatz refutation of degree at
most `d`. -/
theorem not_refutableInDegree [IsStrictOrderedRing R] (P : PseudoExpectation I E d) :
    ¬ RefutableInDegree I E d := by
  rintro ⟨r⟩
  have h := congrArg P.toLinearMap r.eq
  rw [map_add, map_list_sum, map_list_sum, List.map_map, List.map_map, map_neg, P.map_one] at h
  have h1 : (r.eqTerms.map (P.toLinearMap ∘ fun p => p.1 * p.2)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact P.map_mul_eq_zero _ (r.eqTerm_mem p hp) _ (r.totalDegree_eqTerm_le p hp)
  have h2 : 0 ≤ (r.summands.map (P.toLinearMap ∘ Summand.toPoly)).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      rw [Function.comp_apply, Summand.toPoly, mul_assoc, C_mul', map_smul, smul_eq_mul]
      exact mul_nonneg (r.weight_nonneg t ht)
        (P.map_sq_mul_prod_nonneg _ _ (r.factors_subset t ht) (r.degree_le t ht))
  rw [h1, zero_add] at h
  have h3 : (0 : R) < 1 := zero_lt_one
  linarith

end PseudoExpectation

/-- **Soundness of Positivstellensatz refutations**: over a strictly ordered ring, refutable
constraints have no common solution. -/
theorem RefutableInDegree.not_exists_eval [IsStrictOrderedRing R] {I E : Set (MvPolynomial σ R)}
    {d : ℕ} (h : RefutableInDegree I E d) :
    ¬ ∃ x : σ → R, (∀ f ∈ I, 0 ≤ eval x f) ∧ ∀ g ∈ E, eval x g = 0 := by
  rintro ⟨x, hI, hE⟩
  exact (PseudoExpectation.ofEval (d := d) x hI fun g hg q _ => by
    rw [map_mul, hE g hg, mul_zero]).not_refutableInDegree h

/-! ### Equations only -/

/-- A **sum-of-squares refutation of equations is a Positivstellensatz refutation** without
inequality factors, for any set `I` of inequality constraints. -/
theorem _root_.Cslib.Logic.PL.SOS.RefutableInDegree.psatz {F : List (MvPolynomial σ R)} {d : ℕ}
    (I : Set (MvPolynomial σ R)) (h : SOS.RefutableInDegree F d) :
    RefutableInDegree I {g | g ∈ F} d := by
  obtain ⟨r⟩ := SOS.refutableInDegree_iff.1 h
  refine ⟨⟨(List.finRange F.length).map fun i => (r.mult i, F.get i),
    r.squares.map fun p => ⟨∅, p.1, p.2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [List.map_map, List.map_map, ← r.eq, Fin.sum_univ_def]
    simp [Function.comp_def, Summand.toPoly]
  · simp
  · simp only [List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨i, rfl⟩
    exact r.totalDegree_mul_le i
  · simp only [List.mem_map]
    rintro _ ⟨p, -, rfl⟩
    simp
  · simp only [List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    exact r.weight_nonneg p hp
  · simp only [List.mem_map]
    rintro _ ⟨p, hp, rfl⟩
    simpa [Summand.degree] using r.two_mul_totalDegree_le p hp

/-- Without inequality constraints, Positivstellensatz refutations of the equations `F` are
sum-of-squares refutations. -/
theorem refutableInDegree_empty_iff {F : List (MvPolynomial σ R)} {d : ℕ} :
    RefutableInDegree ∅ {g | g ∈ F} d ↔ SOS.RefutableInDegree F d := by
  refine ⟨fun ⟨r⟩ => ?_, SOS.RefutableInDegree.psatz ∅⟩
  have hfac (t) (ht : t ∈ r.summands) : t.factors = ∅ :=
    Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 (r.factors_subset t ht))
  refine SOS.RefutableInDegree.of_list r.eqTerms (fun p hp => ⟨r.eqTerm_mem p hp,
    r.totalDegree_eqTerm_le p hp⟩) (r.summands.map fun t => (t.weight, t.base)) ?_ ?_ ?_
  · simp only [List.mem_map]
    rintro _ ⟨t, ht, rfl⟩
    exact r.weight_nonneg t ht
  · simp only [List.mem_map]
    rintro _ ⟨t, ht, rfl⟩
    simpa [Summand.degree, hfac t ht] using r.degree_le t ht
  · rw [← r.eq, List.map_map]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    simp [Summand.toPoly, hfac t ht]

/-- A pseudo-expectation for the equations `F` is a pseudo-expectation for the same equations and
no inequality constraints. -/
def _root_.Cslib.Logic.PL.SOS.PseudoExpectation.psatz {F : List (MvPolynomial σ R)} {d : ℕ}
    (P : SOS.PseudoExpectation F d) : PseudoExpectation ∅ {g | g ∈ F} d where
  toLinearMap := P.toLinearMap
  map_one := P.map_one
  map_sq_mul_prod_nonneg S s hS hd := by
    obtain rfl := Finset.coe_eq_empty.1 (Set.subset_empty_iff.1 hS)
    rw [Finset.prod_empty, mul_one]
    exact P.map_sq_nonneg s (by simpa using hd)
  map_mul_eq_zero g hg q hq := P.map_mul_eq_zero g hg q hq

end Cslib.Logic.PL.SOS.Psatz
