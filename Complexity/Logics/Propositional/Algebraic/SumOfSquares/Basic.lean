/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Sum-of-squares refutations and pseudo-expectations

The **sum-of-squares** (Positivstellensatz) proof system refutes a system of polynomial equations
`f = 0`, `f ∈ F`, over an ordered commutative ring `R` by exhibiting multipliers `gᵢ` and
polynomials `s₁, …, sᵣ` with

`∑ᵢ gᵢ fᵢ + ∑ₖ sₖ ² = -1`.

No common real zero of `F` can exist, since the left-hand side is nonnegative there
(`SOS.RefutableInDegree.not_exists_eval_eq_zero`). A refutation has **degree at most `d`**
(`SOS.Refutation F d`) when every product `gᵢ fᵢ` has total degree at most `d` and every square
`sₖ ²` has total degree at most `d`, that is `2 deg sₖ ≤ d`. Boolean or `±1` axioms such as
`xᵢ ² - 1` are not built in: they are members of `F`, as in the algebraic encodings of parity
systems (`Cslib.Logic.PL.ParitySystem.toPolys`). This is the degree-`d` sum-of-squares proof
in the style of [Barak and Steurer, Definition 2][BarakSteurer2016], with the axioms used through
multipliers.

The dual objects are **pseudo-expectations** (`SOS.PseudoExpectation F d`): linear maps `Ẽ` from
polynomials to `R` with `Ẽ 1 = 1`, `Ẽ (s ^ 2) ≥ 0` whenever `2 deg s ≤ d`, and `Ẽ (q f) = 0`
for `f ∈ F` whenever `deg (q f) ≤ d`; compare [Barak and Steurer, Definition 12][BarakSteurer2016].
Evaluation at a common zero is one (`SOS.PseudoExpectation.ofEval`). Applying `Ẽ` to a refutation
of degree at most `d` gives `0 + (nonnegative) = -1`, so **a degree-`d` pseudo-expectation rules
out degree-`d` refutations** (`SOS.PseudoExpectation.not_refutableInDegree`). This is the easy
direction of the duality [Barak and Steurer, Theorem 19][BarakSteurer2016], and the one used by
degree lower bounds. The converse, by hyperplane separation, is not formalized.

## Main definitions

* `Cslib.Logic.PL.SOS.Refutation`: sum-of-squares refutations of degree at most `d`.
* `Cslib.Logic.PL.SOS.RefutableInDegree`: a refutation of degree at most `d` exists.
* `Cslib.Logic.PL.SOS.PseudoExpectation`: pseudo-expectations of degree `d`.

## Main results

* `Cslib.Logic.PL.SOS.PseudoExpectation.not_refutableInDegree`: a degree-`d` pseudo-expectation
  rules out refutations of degree at most `d`.
* `Cslib.Logic.PL.SOS.RefutableInDegree.not_exists_eval_eq_zero`: soundness, a refutable system has
  no common zero.
* `Cslib.Logic.PL.SOS.RefutableInDegree.of_sum`, `Cslib.Logic.PL.SOS.RefutableInDegree.of_list`:
  building refutations from combinations of members of `F` in any order.

## References

* [B. Barak, D. Steurer, *Proofs, beliefs, and algorithms through the lens of sum-of-squares*,
  lecture notes][BarakSteurer2016]
-/

public section

namespace Cslib.Logic.PL.SOS

open MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- A **sum-of-squares refutation of degree at most `d`** of the polynomial equations `f = 0`,
`f ∈ F`: multipliers `mult i` for the members of `F` and polynomials `squares` with
`∑ᵢ mult i * F[i] + ∑ₖ squares[k] ^ 2 = -1`, every product `mult i * F[i]` of total degree at
most `d` and every square of total degree at most `d`. -/
structure Refutation (F : List (MvPolynomial σ R)) (d : ℕ) where
  /-- The multiplier of each member of `F`. -/
  mult : Fin F.length → MvPolynomial σ R
  /-- The polynomials whose squares are summed. -/
  squares : List (MvPolynomial σ R)
  /-- The refutation identity. -/
  eq : ∑ i, mult i * F.get i + (squares.map (· ^ 2)).sum = -1
  /-- Every product of a multiplier with its member of `F` has total degree at most `d`. -/
  totalDegree_mul_le : ∀ i, (mult i * F.get i).totalDegree ≤ d
  /-- Every square has total degree at most `d`. -/
  two_mul_totalDegree_le : ∀ s ∈ squares, 2 * s.totalDegree ≤ d

/-- The system `F` has a sum-of-squares refutation of degree at most `d`. -/
def RefutableInDegree (F : List (MvPolynomial σ R)) (d : ℕ) : Prop :=
  Nonempty (Refutation F d)

/-- A refutation of degree at most `d` has degree at most `d'` for `d ≤ d'`. -/
theorem RefutableInDegree.mono {F : List (MvPolynomial σ R)} {d d' : ℕ}
    (h : RefutableInDegree F d) (hd : d ≤ d') : RefutableInDegree F d' :=
  let ⟨r⟩ := h
  ⟨{ r with
    totalDegree_mul_le := fun i => (r.totalDegree_mul_le i).trans hd
    two_mul_totalDegree_le := fun s hs => (r.two_mul_totalDegree_le s hs).trans hd }⟩

/-- **Building a refutation from a combination of members of `F`**, indexed by any finite type:
members may repeat and appear in any order. -/
theorem RefutableInDegree.of_sum {F : List (MvPolynomial σ R)} {d : ℕ} {ι : Type*} [Fintype ι]
    (g f : ι → MvPolynomial σ R) (hf : ∀ i, f i ∈ F) (hdeg : ∀ i, (g i * f i).totalDegree ≤ d)
    (squares : List (MvPolynomial σ R)) (hsq : ∀ s ∈ squares, 2 * s.totalDegree ≤ d)
    (h : ∑ i, g i * f i + (squares.map (· ^ 2)).sum = -1) : RefutableInDegree F d := by
  classical
  choose idx hidx using fun i => List.mem_iff_get.1 (hf i)
  let mult : Fin F.length → MvPolynomial σ R :=
    fun j => ∑ i ∈ Finset.univ.filter (idx · = j), g i
  have hmul (j : Fin F.length) :
      mult j * F.get j = ∑ i ∈ Finset.univ.filter (idx · = j), g i * f i := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [← (Finset.mem_filter.1 hi).2, hidx i]
  refine ⟨⟨mult, squares, ?_, fun j => ?_, hsq⟩⟩
  · rw [Finset.sum_congr rfl fun j _ => hmul j, Finset.sum_fiberwise]
    exact h
  · rw [hmul]
    exact totalDegree_finsetSum_le fun i _ => hdeg i

/-- **Building a refutation from a list of pairs `(g, f)`** with `f ∈ F` and
`deg (g f) ≤ d`. -/
theorem RefutableInDegree.of_list {F : List (MvPolynomial σ R)} {d : ℕ}
    (L : List (MvPolynomial σ R × MvPolynomial σ R))
    (hL : ∀ p ∈ L, p.2 ∈ F ∧ (p.1 * p.2).totalDegree ≤ d)
    (squares : List (MvPolynomial σ R)) (hsq : ∀ s ∈ squares, 2 * s.totalDegree ≤ d)
    (h : (L.map fun p => p.1 * p.2).sum + (squares.map (· ^ 2)).sum = -1) :
    RefutableInDegree F d := by
  refine of_sum (fun i : Fin L.length => (L.get i).1) (fun i => (L.get i).2)
    (fun i => (hL _ (List.get_mem L i)).1) (fun i => (hL _ (List.get_mem L i)).2) squares hsq ?_
  rw [← h, ← Fin.sum_univ_fun_getElem L fun p => p.1 * p.2]
  rfl

variable [LinearOrder R]

/-- A **pseudo-expectation of degree `d`** for the polynomial equations `f = 0`, `f ∈ F`: a linear
map `Ẽ` from polynomials to `R` with `Ẽ 1 = 1`, `Ẽ (s ^ 2) ≥ 0` whenever `2 deg s ≤ d`, and
`Ẽ (q f) = 0` for `f ∈ F` whenever `deg (q f) ≤ d`. -/
structure PseudoExpectation (F : List (MvPolynomial σ R)) (d : ℕ) where
  /-- The pseudo-expectation, as a linear map. -/
  toLinearMap : MvPolynomial σ R →ₗ[R] R
  /-- `Ẽ 1 = 1`. -/
  map_one : toLinearMap 1 = 1
  /-- `Ẽ (s ^ 2) ≥ 0` when `s ^ 2` has degree at most `d`. -/
  map_sq_nonneg : ∀ s : MvPolynomial σ R, 2 * s.totalDegree ≤ d → 0 ≤ toLinearMap (s ^ 2)
  /-- `Ẽ (q f) = 0` for `f ∈ F` when `q f` has degree at most `d`. -/
  map_mul_eq_zero : ∀ f ∈ F, ∀ q : MvPolynomial σ R, (q * f).totalDegree ≤ d →
    toLinearMap (q * f) = 0

namespace PseudoExpectation

variable {F : List (MvPolynomial σ R)} {d : ℕ}

/-- Evaluation at a common zero of `F` is a pseudo-expectation of every degree, over a linearly
ordered ring. -/
noncomputable def ofEval [IsOrderedRing R] (x : σ → R) (hx : ∀ f ∈ F, eval x f = 0) :
    PseudoExpectation F d where
  toLinearMap := (aeval x).toLinearMap
  map_one := by simp
  map_sq_nonneg s _ := by simp [sq_nonneg]
  map_mul_eq_zero f hf q _ := by simp [hx f hf]

/-- The pseudo-expectation `ofEval x hx` is evaluation at `x`. -/
@[simp] theorem ofEval_apply [IsOrderedRing R] (x : σ → R) (hx : ∀ f ∈ F, eval x f = 0)
    (p : MvPolynomial σ R) : (ofEval (d := d) x hx).toLinearMap p = eval x p := by
  simp [ofEval]

/-- **Pseudo-expectations rule out refutations**: over a strictly ordered ring, if a
pseudo-expectation of degree `d` exists, there is no sum-of-squares refutation of degree at
most `d`. -/
theorem not_refutableInDegree [IsStrictOrderedRing R] (E : PseudoExpectation F d) :
    ¬ RefutableInDegree F d := by
  rintro ⟨r⟩
  have h := congrArg E.toLinearMap r.eq
  rw [map_add, map_sum, map_list_sum, List.map_map, map_neg, E.map_one] at h
  have h1 : ∑ i, E.toLinearMap (r.mult i * F.get i) = 0 :=
    Finset.sum_eq_zero fun i _ =>
      E.map_mul_eq_zero _ (List.get_mem F i) _ (r.totalDegree_mul_le i)
  have h2 : 0 ≤ (r.squares.map (E.toLinearMap ∘ (· ^ 2))).sum :=
    List.sum_nonneg fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      exact E.map_sq_nonneg s (r.two_mul_totalDegree_le s hs)
  rw [h1, zero_add] at h
  have h3 : (0 : R) < 1 := zero_lt_one
  linarith

end PseudoExpectation

/-- **Soundness of sum-of-squares refutations**: over a strictly ordered ring, a system with a
refutation of some degree has no common zero. -/
theorem RefutableInDegree.not_exists_eval_eq_zero [IsStrictOrderedRing R]
    {F : List (MvPolynomial σ R)} {d : ℕ} (h : RefutableInDegree F d) :
    ¬ ∃ x : σ → R, ∀ f ∈ F, eval x f = 0 := by
  rintro ⟨x, hx⟩
  exact (PseudoExpectation.ofEval (d := d) x hx).not_refutableInDegree h

end Cslib.Logic.PL.SOS
