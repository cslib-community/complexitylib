/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.MultilinearExtension
public import CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.Combination
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Invariant
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Nullstellensatz
public import CslibFrontier.Logics.Propositional.Algebraic.SumOfSquares.CNF
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Combinatorics.Nullstellensatz

/-!
# Refuting polynomial systems over the Boolean cube

A system of polynomial equations `f = 0`, `f ∈ F`, has a **Boolean solution** at a point
`x : σ → Bool` of the cube, read in `R` by `Cslib.BitString.bitPoint`, when every `f` vanishes
there (`Cslib.Logic.PL.Algebraic.IsBoolSolution`). Algebraic proof systems refute such a system by
adding the **Boolean axioms** `X i ^ 2 - X i` (`Cslib.Logic.PL.Algebraic.boolAxiom`) to the inputs
[BeameEtAl1996], [CleggEdmondsImpagliazzo1996]. Here they are a list of inputs,
`F ++ Cslib.Logic.PL.Algebraic.boolAxioms σ R`, for the Nullstellensatz and polynomial calculus
proofs `Cslib.Logic.PL.NS.IsProof` and `Cslib.Logic.PL.PC.IsProof` of
`CslibFrontier.Logics.Propositional.Algebraic.Nullstellensatz.Proof` and
`CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Proof` (#2887).

* **Soundness**, over any nontrivial commutative ring: a refutation of `F ++ boolAxioms σ R`
  leaves `F` without Boolean solutions (`Cslib.Logic.PL.NS.IsProof.not_isBoolSolution`,
  `Cslib.Logic.PL.PC.IsProof.not_isBoolSolution`).
* **Completeness**, over a field: if every `f ∈ F` has total degree at most `D` in the `n`
  variables of a finite type `σ`, and `F` has no Boolean solution, then `F ++ boolAxioms σ R` has
  a Nullstellensatz refutation of degree at most `n + D`
  (`Cslib.Logic.PL.NS.refutableInDegree_of_forall_not_isBoolSolution`). Polynomial calculus then
  has one too, by the simulation `Cslib.Logic.PL.PC.RefutableInDegree.of_ns`.

The proof of completeness picks, for every point `x` of the cube, an input `f x` that does not
vanish at `x`, and scales the indicator polynomial of `x` so that `∑ₓ gₓ f x` is `1` on the cube.
The Combinatorial Nullstellensatz (`combinatorial_nullstellensatz_exists_linearCombination`)
writes `1 - ∑ₓ gₓ f x` as a combination of the Boolean axioms, with every product of degree at
most `n + D`. The source states the existence of refutations: Impagliazzo, Pudlák and Sgall note
in Section 2 that polynomial calculus refutes exactly the systems without `0/1` solutions
[ImpagliazzoPudlakSgall1999]. The bound `n + D` comes from this argument and is not optimized.
For polynomial calculus, Lemma 4.1 of the same paper gives `max(D, n + 1)`, which is not
formalized here.

## Main definitions

* `Cslib.Logic.PL.Algebraic.boolAxiom`, `Cslib.Logic.PL.Algebraic.boolAxioms`: the Boolean axioms.
* `Cslib.Logic.PL.Algebraic.IsBoolSolution`: a point of the cube at which every input vanishes.

## Main results

* `Cslib.Logic.PL.Algebraic.setOf_mem_boolAxioms`: the members of `boolAxioms σ R` are exactly
  the Boolean axioms `Cslib.Logic.PL.SOS.Psatz.booleanAxioms σ R` of Positivstellensatz
  refutations.
* `Cslib.Logic.PL.NS.IsProof.not_isBoolSolution`, `Cslib.Logic.PL.PC.IsProof.not_isBoolSolution`:
  soundness.
* `Cslib.Logic.PL.NS.refutableInDegree_of_forall_not_isBoolSolution`: completeness of
  Nullstellensatz in degree `card σ + D`.
* `Cslib.Logic.PL.NS.refutableInDegree_iff`, `Cslib.Logic.PL.PC.refutableInDegree_iff`:
  refutability in degree `card σ + D` exactly when there is no Boolean solution.
* `Cslib.Logic.PL.NS.exists_refutableInDegree_iff`,
  `Cslib.Logic.PL.PC.exists_refutableInDegree_iff`: refutability in some degree exactly when
  there is no Boolean solution.

## References

* [P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi, P. Pudlák, *Lower bounds on Hilbert's
  Nullstellensatz and propositional proofs*][BeameEtAl1996]
* [M. Clegg, J. Edmonds, R. Impagliazzo, *Using the Groebner basis algorithm to find proofs of
  unsatisfiability*][CleggEdmondsImpagliazzo1996]
* [R. Impagliazzo, P. Pudlák, J. Sgall, *Lower bounds for the polynomial calculus and the Gröbner
  basis algorithm*][ImpagliazzoPudlakSgall1999]
-/

public section

open MvPolynomial Cslib.BitString

namespace Cslib.Logic.PL

namespace Algebraic

variable {σ R : Type*} [CommRing R]

/-- The **Boolean axiom** `X i ^ 2 - X i` of the variable `i`, whose zeros are `0` and `1`. -/
@[expose] noncomputable def boolAxiom (i : σ) : MvPolynomial σ R := X i ^ 2 - X i

variable (σ R) in
/-- The list of the Boolean axioms of all variables of a finite type. -/
@[expose] noncomputable def boolAxioms [Fintype σ] : List (MvPolynomial σ R) :=
  Finset.univ.toList.map boolAxiom

/-- A point `x` of the cube is a **Boolean solution** of the system `f = 0`, `f ∈ F`, when every
`f ∈ F` vanishes at `x`, read in `R`. -/
@[expose] def IsBoolSolution (F : List (MvPolynomial σ R)) (x : σ → Bool) : Prop :=
  ∀ f ∈ F, eval (bitPoint x) f = 0

/-- The Boolean axioms vanish at every point of the cube. -/
@[simp] theorem eval_boolAxiom (x : σ → Bool) (i : σ) :
    eval (bitPoint x) (boolAxiom i : MvPolynomial σ R) = 0 := by
  rw [boolAxiom, map_sub, map_pow, eval_X, bitVal_pow _ two_ne_zero, sub_self]

/-- The members of `boolAxioms σ R` are the Boolean axioms. -/
theorem mem_boolAxioms [Fintype σ] {p : MvPolynomial σ R} :
    p ∈ boolAxioms σ R ↔ ∃ i, boolAxiom i = p := by
  simp [boolAxioms]

/-- The Boolean axiom of every variable is a member of `boolAxioms σ R`. -/
theorem boolAxiom_mem_boolAxioms [Fintype σ] (i : σ) :
    (boolAxiom i : MvPolynomial σ R) ∈ boolAxioms σ R :=
  mem_boolAxioms.2 ⟨i, rfl⟩

/-- The members of the list `boolAxioms σ R` form the set `SOS.Psatz.booleanAxioms σ R`, the
Boolean axioms that Positivstellensatz refutations take as equations: the two encodings of the
Boolean axioms agree. -/
theorem setOf_mem_boolAxioms [Fintype σ] :
    {p | p ∈ boolAxioms σ R} = SOS.Psatz.booleanAxioms σ R :=
  Set.ext fun _ => mem_boolAxioms.trans SOS.Psatz.mem_booleanAxioms.symm

/-- A Boolean axiom has total degree at most two. -/
theorem totalDegree_boolAxiom_le (i : σ) : (boolAxiom i : MvPolynomial σ R).totalDegree ≤ 2 := by
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · rw [X_pow_eq_monomial]
    exact (totalDegree_monomial_le _ _).trans (by simp)
  · exact (totalDegree_monomial_le _ _).trans (by simp)

/-- Over a nontrivial ring, a Boolean axiom is nonzero: its coefficient at `X i ^ 2` is `1`. -/
theorem boolAxiom_ne_zero [Nontrivial R] (i : σ) : (boolAxiom i : MvPolynomial σ R) ≠ 0 := by
  classical
  intro h
  have := congrArg (fun p : MvPolynomial σ R => p.coeff (Finsupp.single i 2)) h
  simp [boolAxiom, coeff_X, coeff_X_pow, Finsupp.single_eq_single_iff] at this

/-- A system has a Boolean solution at `x` together with the Boolean axioms exactly when it has
one without them. -/
theorem isBoolSolution_append_boolAxioms [Fintype σ] (F : List (MvPolynomial σ R))
    (x : σ → Bool) : IsBoolSolution (F ++ boolAxioms σ R) x ↔ IsBoolSolution F x := by
  simp only [IsBoolSolution, List.mem_append, or_imp, forall_and, and_iff_left_iff_imp]
  intro _ p hp
  obtain ⟨i, rfl⟩ := mem_boolAxioms.1 hp
  exact eval_boolAxiom x i

end Algebraic

open Algebraic

variable {σ R : Type*} [CommRing R] [Nontrivial R] [Fintype σ]

/-- **Soundness of Nullstellensatz.** A Nullstellensatz refutation of `F` together with the
Boolean axioms, over a nontrivial commutative ring, leaves `F` without Boolean solutions. -/
theorem NS.IsProof.not_isBoolSolution {F : List (MvPolynomial σ R)}
    {P : Fin (F ++ boolAxioms σ R).length → MvPolynomial σ R}
    (h : NS.IsProof (F ++ boolAxioms σ R) P 1) (x : σ → Bool) : ¬ IsBoolSolution F x := by
  intro hx
  obtain ⟨f, hf, hne⟩ := h.exists_eval_ne_zero (bitPoint x)
  exact hne ((isBoolSolution_append_boolAxioms F x).2 hx f hf)

/-- **Soundness of polynomial calculus.** A polynomial calculus refutation of `F` together with
the Boolean axioms, over a nontrivial commutative ring, leaves `F` without Boolean solutions. -/
theorem PC.IsProof.not_isBoolSolution {F ls : List (MvPolynomial σ R)}
    (h : PC.IsProof (F ++ boolAxioms σ R) ls) (h1 : 1 ∈ ls) (x : σ → Bool) :
    ¬ IsBoolSolution F x := by
  intro hx
  obtain ⟨f, hf, hne⟩ := h.exists_eval_ne_zero h1 (bitPoint x)
  exact hne ((isBoolSolution_append_boolAxioms F x).2 hx f hf)

/-- Soundness of Nullstellensatz, for refutability in some degree. -/
theorem NS.RefutableInDegree.not_isBoolSolution {F : List (MvPolynomial σ R)} {d : ℕ}
    (h : NS.RefutableInDegree (F ++ boolAxioms σ R) d) (x : σ → Bool) : ¬ IsBoolSolution F x :=
  let ⟨_, hP, _⟩ := h
  hP.not_isBoolSolution x

/-- Soundness of polynomial calculus, for refutability in some degree. -/
theorem PC.RefutableInDegree.not_isBoolSolution {F : List (MvPolynomial σ R)} {d : ℕ}
    (h : PC.RefutableInDegree (F ++ boolAxioms σ R) d) (x : σ → Bool) : ¬ IsBoolSolution F x :=
  let ⟨_, hls, h1, _⟩ := h
  hls.not_isBoolSolution h1 x

section Field

variable {K : Type*} [Field K]

omit [Fintype σ] in
private theorem prod_bool_eq_boolAxiom [DecidableEq K] (i : σ) :
    ∏ r ∈ ({0, 1} : Finset K), (X i - C r : MvPolynomial σ K) = boolAxiom i := by
  rw [Finset.prod_pair zero_ne_one, boolAxiom, C_0, C_1, sub_zero]
  ring

omit [Fintype σ] in
private theorem exists_bitPoint_eq [DecidableEq K] {z : σ → K}
    (hz : ∀ i, z i ∈ ({0, 1} : Finset K)) : ∃ x : σ → Bool, bitPoint x = z := by
  refine ⟨fun i => decide (z i = 1), funext fun i => ?_⟩
  have h := hz i
  rw [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> simp [bitVal, h]

/-- **Completeness of Nullstellensatz.** Over a field, if every input has total degree at most `D`
in the finitely many variables `σ` and there is no Boolean solution, then the inputs together
with the Boolean axioms have a Nullstellensatz refutation of degree at most `card σ + D`. -/
theorem NS.refutableInDegree_of_forall_not_isBoolSolution {F : List (MvPolynomial σ K)} {D : ℕ}
    (hF : ∀ f ∈ F, f.totalDegree ≤ D) (h : ∀ x, ¬ IsBoolSolution F x) :
    NS.RefutableInDegree (F ++ boolAxioms σ K) (Fintype.card σ + D) := by
  classical
  have hk : ∀ x : σ → Bool, ∃ f ∈ F, eval (bitPoint x) f ≠ 0 := fun x => by
    simpa [IsBoolSolution] using h x
  choose f hfF hf using hk
  -- `g x * f x` is `1` at `x` and `0` at the other points of the cube
  let g : (σ → Bool) → MvPolynomial σ K :=
    fun x => C (eval (bitPoint x) (f x))⁻¹ * indicatorPoly x
  have hG : ∀ z : σ → K, (∀ i, z i ∈ ({0, 1} : Finset K)) →
      eval z (1 - ∑ x, f x * g x) = 0 := by
    intro z hz
    obtain ⟨y, rfl⟩ := exists_bitPoint_eq hz
    simp only [g, map_sub, map_one, map_sum, map_mul, eval_C, eval_indicatorPoly, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [mul_inv_cancel₀ (hf y), sub_self]
  obtain ⟨b, hb, hbeq⟩ := combinatorial_nullstellensatz_exists_linearCombination
    (fun _ => ({0, 1} : Finset K)) (fun _ => Finset.insert_nonempty _ _) _ hG
  simp only [prod_bool_eq_boolAxiom] at hb hbeq
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hbeq
  have hgdeg : ∀ x, (g x).totalDegree ≤ Fintype.card σ := fun x =>
    (totalDegree_mul _ _).trans (by
      rw [totalDegree_C, zero_add]; exact totalDegree_indicatorPoly_le x)
  have hGdeg : (1 - ∑ x, f x * g x).totalDegree ≤ Fintype.card σ + D :=
    (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_one]; omega)
      ((totalDegree_finsetSum _ _).trans (Finset.sup_le fun x _ =>
        (totalDegree_mul _ _).trans (by have := hF _ (hfF x); have := hgdeg x; omega))))
  have hsum : ∑ t : (σ → Bool) ⊕ σ, Sum.elim f boolAxiom t * Sum.elim g b t = 1 := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, smul_eq_mul] at hbeq ⊢
    rw [show ∑ i, boolAxiom i * b i = ∑ i, b i * boolAxiom i from
      Finset.sum_congr rfl fun i _ => mul_comm _ _, ← hbeq]
    ring
  have hmem : ∀ t ∈ (Finset.univ : Finset ((σ → Bool) ⊕ σ)),
      Sum.elim f boolAxiom t ∈ F ++ boolAxioms σ K := by
    rintro (x | i) _
    · exact List.mem_append_left _ (hfF x)
    · exact List.mem_append_right _ (boolAxiom_mem_boolAxioms i)
  have hdeg : ∀ t ∈ (Finset.univ : Finset ((σ → Bool) ⊕ σ)), Sum.elim g b t ≠ 0 →
      (Sum.elim f boolAxiom t).totalDegree + (Sum.elim g b t).totalDegree ≤
        Fintype.card σ + D := by
    rintro (x | i) _ hne
    · have := hF _ (hfF x)
      have := hgdeg x
      simp only [Sum.elim_inl]
      omega
    · simp only [Sum.elim_inr] at hne ⊢
      rw [← totalDegree_mul_of_isDomain (boolAxiom_ne_zero i) hne]
      exact (hb i).trans hGdeg
  obtain ⟨P, hP, hPd⟩ := NS.exists_isProof_of_sum Finset.univ _ _ hmem hdeg
  exact ⟨P, hsum ▸ hP, hPd⟩

/-- Over a field, inputs of total degree at most `D` in the variables `σ`, together with the
Boolean axioms, have a Nullstellensatz refutation of degree at most `card σ + D` exactly when
they have no Boolean solution. -/
theorem NS.refutableInDegree_iff {F : List (MvPolynomial σ K)} {D : ℕ}
    (hF : ∀ f ∈ F, f.totalDegree ≤ D) :
    NS.RefutableInDegree (F ++ boolAxioms σ K) (Fintype.card σ + D) ↔
      ∀ x, ¬ IsBoolSolution F x :=
  ⟨fun h x => h.not_isBoolSolution x, refutableInDegree_of_forall_not_isBoolSolution hF⟩

/-- **Completeness of polynomial calculus**, through the simulation of Nullstellensatz: over a
field, inputs of total degree at most `D` in the variables `σ`, together with the Boolean axioms,
have a polynomial calculus refutation of degree at most `card σ + D` exactly when they have no
Boolean solution. -/
theorem PC.refutableInDegree_iff {F : List (MvPolynomial σ K)} {D : ℕ}
    (hF : ∀ f ∈ F, f.totalDegree ≤ D) :
    PC.RefutableInDegree (F ++ boolAxioms σ K) (Fintype.card σ + D) ↔
      ∀ x, ¬ IsBoolSolution F x :=
  ⟨fun h x => h.not_isBoolSolution x,
    fun h => .of_ns (NS.refutableInDegree_of_forall_not_isBoolSolution hF h)⟩

/-- Over a field, inputs in finitely many variables, together with the Boolean axioms, are
refutable by Nullstellensatz in some degree exactly when they have no Boolean solution. -/
theorem NS.exists_refutableInDegree_iff {F : List (MvPolynomial σ K)} :
    (∃ d, NS.RefutableInDegree (F ++ boolAxioms σ K) d) ↔ ∀ x, ¬ IsBoolSolution F x :=
  ⟨fun ⟨_, h⟩ x => h.not_isBoolSolution x, fun h =>
    ⟨_, (refutableInDegree_iff (D := PC.degree F) (PC.degree_le_iff.1 le_rfl)).2 h⟩⟩

/-- Over a field, inputs in finitely many variables, together with the Boolean axioms, are
refutable by polynomial calculus in some degree exactly when they have no Boolean solution. -/
theorem PC.exists_refutableInDegree_iff {F : List (MvPolynomial σ K)} :
    (∃ d, PC.RefutableInDegree (F ++ boolAxioms σ K) d) ↔ ∀ x, ¬ IsBoolSolution F x :=
  ⟨fun ⟨_, h⟩ x => h.not_isBoolSolution x, fun h =>
    ⟨_, (refutableInDegree_iff (D := PC.degree F) (PC.degree_le_iff.1 le_rfl)).2 h⟩⟩

end Field

end Cslib.Logic.PL
