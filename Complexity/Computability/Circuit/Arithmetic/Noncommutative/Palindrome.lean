/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.Noncommutative.ABP
public import Complexity.Computability.Circuit.Arithmetic.Noncommutative.Circuit
public import Complexity.Computability.Circuit.Formula

/-!
# The palindrome: non-commutative ABPs versus circuits

Nisan's explicit hard polynomials ([Nisan1991NonCommutative], §4.2, Theorem 4, over two
variables; [Saptharishi2026Survey], §11.1.1, over `n` variables) are, over the variables `X`,

* the *palindrome* `Pal_{2m} = ∑_{|w| = m} w · reverse(w)` (`Cslib.Circuits.Arithmetic.palindrome`);
* the *double* `Doub_{2m} = ∑_{|w| = m} w · w` (`Cslib.Circuits.Arithmetic.doubled`).

Both are instances of `pairedWordPoly σ = ∑_u u · σ(u)`, where `u` ranges over the `m`-tuples and
`σ` maps `m`-tuples to `m`-tuples. The middle Nisan matrix `M_m` of `pairedWordPoly σ` is the
identity matrix with its rows permuted by `σ` (`nisanMatrix_pairedWordPoly`). For a bijection
`σ` its rank is therefore `|X| ^ m` (`rank_nisanMatrix_pairedWordPoly`).

* **Nisan's lower bound** ([Nisan1991NonCommutative], Theorem 4 (2), for the two-variable
  palindrome; [Saptharishi2026Survey], Theorem 11.4, for `Pal` and `Doub` over `n` variables, by
  Nisan's rank method). Every homogeneous layered ABP computing
  `Pal_{2m}` or `Doub_{2m}` over `n` variables has at least `n ^ m` vertices in its middle layer
  (`NoncommABP.pow_le_width_of_polynomial_eq_palindrome`,
  `NoncommABP.pow_le_width_of_polynomial_eq_doubled`), hence size at least `n ^ m`.
* **Small circuits for the palindrome** ([Nisan1991NonCommutative], proof of Theorem 4;
  [Saptharishi2026Survey], remark after Theorem 11.4). Nisan's recursion
  `f_d = x₀ f_{d-1} x₀ + x₁ f_{d-1} x₁`, extended to `n` variables as
  `Pal_{2m+2} = ∑_x x · Pal_{2m} · x` (`palindrome_succ`), gives an arithmetic circuit
  `palCircuit K n m` with exactly `(3n + 1) m + 1` gates (`size_palCircuit`). Its non-commutative
  polynomial is `Pal_{2m}` (`noncommPolynomial_palCircuit`).
* **Separation** (`palindrome_separation`). For `n ≥ 2` variables, non-commutative circuits are
  exponentially more powerful than homogeneous layered non-commutative ABPs: `O(nm)` gates
  against `n ^ m` vertices.

**Scope.** The ABP lower bound concerns the homogeneous layered model `NoncommABP`. The reduction
from general non-commutative ABPs ([Saptharishi2026Survey], Exercise 11.1) is not formalized.
The survey states the bound as `n^Ω(d)` for `d = 2m`. Here it is the explicit middle-layer bound
`n ^ m = n ^ (d / 2)`. The circuit size is exact. The survey only claims `poly(n, d)`.

## Main definitions

* `Cslib.Circuits.Arithmetic.pairedWordPoly`, `Cslib.Circuits.Arithmetic.palindrome`,
  `Cslib.Circuits.Arithmetic.doubled`.
* `Cslib.Circuits.Arithmetic.palCircuit`: the palindrome circuit.

## Main results

* `Cslib.Circuits.Arithmetic.palindrome_eq_pairedWordPoly`,
  `Cslib.Circuits.Arithmetic.doubled_eq_pairedWordPoly`: the defining equations, with the
  corollaries `coeff_palindrome`, `isHomogeneous_palindrome`, `palindrome_ne_zero` and their
  `doubled` versions.
* `Cslib.Circuits.Arithmetic.rank_nisanMatrix_pairedWordPoly`: the middle rank is `|X| ^ m`.
* `Cslib.Circuits.Arithmetic.NoncommABP.pow_le_width_of_polynomial_eq_palindrome`: Theorem 11.4.
* `Cslib.Circuits.Arithmetic.size_palCircuit`, `noncommPolynomial_palCircuit`: the circuit.
* `Cslib.Circuits.Arithmetic.palindrome_separation`: the separation.

## References

* [N. Nisan, *Lower bounds for non-commutative computation*][Nisan1991NonCommutative], §4.2,
  Theorem 4: the two-variable palindrome `f_d = ∑_{w ∈ {0,1}^d} x_w x_{w^R}` of degree `2d`, its
  linear-size circuit through `f_d = x₀ f_{d-1} x₀ + x₁ f_{d-1} x₁`, and `B(f_d) = 2^Θ(d)` from
  the diagonal matrix `M_d(f_d)`.
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], §11.1.1 (Theorem 11.4 and the remark after it), for the
  `n`-variable palindrome and the double; the section is unchanged from release v9.0.3.
-/

public section

namespace Cslib.Circuits.Arithmetic

open FreeAlgebra

section Paired

variable {K : Type*} [CommSemiring K] {X : Type*} [Fintype X] {m : ℕ}

/-- `∑_u u · σ(u)`, summed over the `m`-tuples `u`. -/
noncomputable def pairedWordPoly (σ : (Fin m → X) → (Fin m → X)) : FreeAlgebra K X :=
  ∑ u, FreeMonoid.lift (ι K) (FreeMonoid.ofFn u * FreeMonoid.ofFn (σ u))

variable (K X) in
/-- The palindrome `Pal_{2m} = ∑_{|w| = m} w · reverse(w)` ([Saptharishi2026Survey], §11.1.1). -/
noncomputable def palindrome (m : ℕ) : FreeAlgebra K X :=
  pairedWordPoly fun u : Fin m → X => u ∘ Fin.rev

variable (K X) in
/-- The double `Doub_{2m} = ∑_{|w| = m} w · w` ([Saptharishi2026Survey], §11.1.1). -/
noncomputable def doubled (m : ℕ) : FreeAlgebra K X :=
  pairedWordPoly fun u : Fin m → X => u

/-- `Pal_{2m}` is `∑_u u · σ(u)` for `σ` the reversal of `m`-tuples. -/
theorem palindrome_eq_pairedWordPoly (m : ℕ) :
    palindrome K X m = pairedWordPoly fun u : Fin m → X => u ∘ Fin.rev := by
  rw [palindrome]

/-- `Doub_{2m}` is `∑_u u · σ(u)` for `σ` the identity. -/
theorem doubled_eq_pairedWordPoly (m : ℕ) :
    doubled K X m = pairedWordPoly fun u : Fin m → X => u := by
  rw [doubled]

/-- The coefficient of `a b` in `∑_u u · σ(u)` is `1` if `σ a = b` and `0` otherwise. -/
theorem coeff_pairedWordPoly [DecidableEq X] (σ : (Fin m → X) → (Fin m → X)) (a b : Fin m → X) :
    coeff (FreeMonoid.ofFn a * FreeMonoid.ofFn b) (pairedWordPoly (K := K) σ) =
      if σ a = b then 1 else 0 := by
  rw [pairedWordPoly, map_sum, Finset.sum_eq_single a]
  · rw [coeff_lift_ι]
    by_cases h : σ a = b
    · simp [h]
    · rw [Finsupp.single_eq_of_ne' fun h' => h (FreeMonoid.ofFn_mul_ofFn_injective h').2,
        ite_eq_right_iff.mpr fun h' => absurd h' h]
  · intro u _ hu
    rw [coeff_lift_ι,
      Finsupp.single_eq_of_ne' fun h' => hu (FreeMonoid.ofFn_mul_ofFn_injective h').1]
  · simp

/-- `∑_u u · σ(u)` is homogeneous of degree `2m`. -/
theorem isHomogeneous_pairedWordPoly (σ : (Fin m → X) → (Fin m → X)) :
    (pairedWordPoly (K := K) σ).IsHomogeneous (m + m) :=
  IsHomogeneous.sum _ _ fun u _ => by
    simpa using isHomogeneous_lift_ι (R := K) (FreeMonoid.ofFn u * FreeMonoid.ofFn (σ u))

/-- Over a nonempty alphabet, `∑_u u · σ(u)` is nonzero. -/
theorem pairedWordPoly_ne_zero [Nontrivial K] [Nonempty X] (σ : (Fin m → X) → (Fin m → X)) :
    pairedWordPoly (K := K) σ ≠ 0 := by
  classical
  intro h
  have := coeff_pairedWordPoly (K := K) σ (fun _ => Classical.arbitrary X)
    (σ fun _ => Classical.arbitrary X)
  simp [h] at this

/-- The coefficient of `a b` in `Pal_{2m}` is `1` if `b` is the reverse of `a` and `0`
otherwise. -/
theorem coeff_palindrome [DecidableEq X] (a b : Fin m → X) :
    coeff (FreeMonoid.ofFn a * FreeMonoid.ofFn b) (palindrome K X m) =
      if a ∘ Fin.rev = b then 1 else 0 := by
  rw [palindrome_eq_pairedWordPoly, coeff_pairedWordPoly]

/-- The coefficient of `a b` in `Doub_{2m}` is `1` if `a = b` and `0` otherwise. -/
theorem coeff_doubled [DecidableEq X] (a b : Fin m → X) :
    coeff (FreeMonoid.ofFn a * FreeMonoid.ofFn b) (doubled K X m) = if a = b then 1 else 0 := by
  rw [doubled_eq_pairedWordPoly, coeff_pairedWordPoly]

/-- `Pal_{2m}` is homogeneous of degree `2m`. -/
theorem isHomogeneous_palindrome : (palindrome K X m).IsHomogeneous (m + m) := by
  rw [palindrome_eq_pairedWordPoly]
  exact isHomogeneous_pairedWordPoly _

/-- `Doub_{2m}` is homogeneous of degree `2m`. -/
theorem isHomogeneous_doubled : (doubled K X m).IsHomogeneous (m + m) := by
  rw [doubled_eq_pairedWordPoly]
  exact isHomogeneous_pairedWordPoly _

/-- Over a nonempty alphabet, `Pal_{2m}` is nonzero. -/
theorem palindrome_ne_zero [Nontrivial K] [Nonempty X] : palindrome K X m ≠ 0 := by
  rw [palindrome_eq_pairedWordPoly]
  exact pairedWordPoly_ne_zero _

/-- Over a nonempty alphabet, `Doub_{2m}` is nonzero. -/
theorem doubled_ne_zero [Nontrivial K] [Nonempty X] : doubled K X m ≠ 0 := by
  rw [doubled_eq_pairedWordPoly]
  exact pairedWordPoly_ne_zero _

/-- The middle Nisan matrix of `∑_u u · σ(u)` is the identity with its rows permuted by `σ`. -/
theorem nisanMatrix_pairedWordPoly [DecidableEq X] (σ : (Fin m → X) → (Fin m → X)) :
    nisanMatrix m m (pairedWordPoly (K := K) σ) =
      (1 : Matrix (Fin m → X) (Fin m → X) K).submatrix σ id := by
  ext a b
  rw [nisanMatrix_apply, coeff_pairedWordPoly, Matrix.submatrix_apply, Matrix.one_apply]
  rfl

/-- The empty palindrome is `1`. -/
theorem palindrome_zero : palindrome K X 0 = 1 := by
  simp [palindrome, pairedWordPoly]

/-- The palindrome recursion `Pal_{2m+2} = ∑_x x · Pal_{2m} · x`, Nisan's recursion
`f_d = x₀ f_{d-1} x₀ + x₁ f_{d-1} x₁` ([Nisan1991NonCommutative], proof of Theorem 4) over `X`. -/
theorem palindrome_succ (m : ℕ) :
    palindrome K X (m + 1) = ∑ x, ι K x * palindrome K X m * ι K x := by
  rw [palindrome_eq_pairedWordPoly, palindrome_eq_pairedWordPoly, pairedWordPoly,
    pairedWordPoly]
  rw [← (Fin.consEquiv fun _ => X).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Fin.consEquiv_apply, FreeMonoid.ofFn_cons, FreeMonoid.ofFn_cons_comp_rev, map_mul,
    FreeMonoid.lift_eval_of, mul_assoc]

end Paired

section Rank

variable {K : Type*} [Field K] {X : Type*} [Fintype X] {m : ℕ}

/-- For a bijection `σ`, the middle Nisan matrix of `∑_u u · σ(u)` has full rank `|X| ^ m`. -/
theorem rank_nisanMatrix_pairedWordPoly (σ : (Fin m → X) ≃ (Fin m → X)) :
    (nisanMatrix m m (pairedWordPoly (K := K) σ)).rank = Fintype.card X ^ m := by
  classical
  rw [nisanMatrix_pairedWordPoly]
  have h := Matrix.rank_submatrix (1 : Matrix (Fin m → X) (Fin m → X) K) σ (Equiv.refl _)
  rw [Equiv.coe_refl] at h
  rw [h, Matrix.rank_one, Fintype.card_fun, Fintype.card_fin]

omit [Fintype X] in
private theorem involutive_comp_rev :
    Function.Involutive fun u : Fin m → X => u ∘ Fin.rev :=
  fun u => funext fun i => by simp

/-- `rank M_m(Pal_{2m}) = |X| ^ m`. -/
theorem rank_nisanMatrix_palindrome :
    (nisanMatrix m m (palindrome K X m)).rank = Fintype.card X ^ m := by
  rw [palindrome_eq_pairedWordPoly]
  exact rank_nisanMatrix_pairedWordPoly (Function.Involutive.toPerm _ involutive_comp_rev)

/-- `rank M_m(Doub_{2m}) = |X| ^ m`. -/
theorem rank_nisanMatrix_doubled :
    (nisanMatrix m m (doubled K X m)).rank = Fintype.card X ^ m := by
  rw [doubled_eq_pairedWordPoly]
  exact rank_nisanMatrix_pairedWordPoly (Equiv.refl _)

/-- **Nisan's lower bound for the palindrome** ([Nisan1991NonCommutative], Theorem 4;
[Saptharishi2026Survey], Theorem 11.4). The middle layer of a homogeneous layered ABP computing
`Pal_{2m}` has at least `|X| ^ m` vertices. -/
theorem NoncommABP.pow_le_width_of_polynomial_eq_palindrome (A : NoncommABP K X (m + m))
    (hA : A.polynomial = palindrome K X m) : Fintype.card X ^ m ≤ A.width m := by
  have h := A.rank_nisanMatrix_le_width m m rfl
  rwa [hA, rank_nisanMatrix_palindrome] at h

/-- **Lower bound for the double** ([Saptharishi2026Survey], Theorem 11.4, by Nisan's rank method
[Nisan1991NonCommutative]). The middle layer of a homogeneous layered ABP computing `Doub_{2m}`
has at least `|X| ^ m` vertices. -/
theorem NoncommABP.pow_le_width_of_polynomial_eq_doubled (A : NoncommABP K X (m + m))
    (hA : A.polynomial = doubled K X m) : Fintype.card X ^ m ≤ A.width m := by
  have h := A.rank_nisanMatrix_le_width m m rfl
  rwa [hA, rank_nisanMatrix_doubled] at h

end Rank

section Circuit

variable {K : Type*} [CommSemiring K]

/-- One step of the palindrome circuit, on the inputs `P, x₀, …, x_{n-1}`, the first one being
`P`: the formula `∑_{i < k} (x_{sel i} · P) · x_{sel i}`, accumulated from the left starting at
the constant `0`. -/
private def palStepFormula (n : ℕ) :
    {k : ℕ} → (Fin k → Fin n) → Formula (arithSignature K) (1 + n)
  | 0, _ => .gate (.const 0) Fin.elim0
  | k + 1, sel => .gate₂ .add rfl (palStepFormula n (sel ∘ Fin.castSucc))
      (.gate₂ .mul rfl (.gate₂ .mul rfl (.input (Fin.natAdd 1 (sel (Fin.last k))))
        (.input (Fin.castAdd n 0))) (.input (Fin.natAdd 1 (sel (Fin.last k)))))

private theorem eval_palStepFormula {R : Type*} [Semiring R] (c : K → R) (hc : c 0 = 0)
    (n : ℕ) {k : ℕ} (sel : Fin k → Fin n) (y : Fin (1 + n) → R) :
    (palStepFormula n sel).eval (arithInterpretationWith K c) y =
      ∑ i, y (Fin.natAdd 1 (sel i)) * y (Fin.castAdd n 0) * y (Fin.natAdd 1 (sel i)) := by
  induction k with
  | zero => simp [palStepFormula, arithInterpretationWith, hc]
  | succ k ih =>
    rw [palStepFormula, Formula.eval_gate₂, Formula.eval_gate₂, Formula.eval_gate₂,
      Fin.sum_univ_castSucc]
    simp [arithInterpretationWith, ih, Function.comp_def]

private theorem size_palStepFormula (n : ℕ) {k : ℕ} (sel : Fin k → Fin n) :
    (palStepFormula (K := K) n sel).size = 3 * k + 1 := by
  induction k with
  | zero => simp [palStepFormula]
  | succ k ih =>
    rw [palStepFormula, Formula.size_gate₂, Formula.size_gate₂, Formula.size_gate₂, ih]
    simp only [Formula.size_input]
    omega

variable (K) in
/-- The palindrome circuit over `n` variables: the constant `1`, followed by `m` applications of
`P ↦ ∑_i (x_i · P) · x_i`. -/
def palCircuit (n : ℕ) : ℕ → Circuit (arithSignature K) n 1
  | 0 => Circuit.oneGate (.const 1) Fin.elim0
  | m + 1 => (palStepFormula n id).toCircuit.comp ((palCircuit n m).append (Circuit.id _ n))

/-- The palindrome circuit has exactly `(3n + 1) m + 1` gates. -/
theorem size_palCircuit (n m : ℕ) : (palCircuit K n m).size = (3 * n + 1) * m + 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [palCircuit, Circuit.size_comp, Circuit.size_append, ih, Formula.size_toCircuit,
      size_palStepFormula, Circuit.size_wiring]
    ring

/-- Evaluated in a `K`-algebra, commutative or not, the palindrome circuit substitutes its inputs
into `Pal_{2m}`. -/
theorem eval_palCircuit {R : Type*} [Semiring R] [Algebra K R] (n m : ℕ) (x : Fin n → R) :
    (palCircuit K n m).eval (arithInterpretationWith K (algebraMap K R)) x 0 =
      FreeAlgebra.lift K x (palindrome K (Fin n) m) := by
  induction m with
  | zero => simp [palCircuit, palindrome_zero, arithInterpretationWith]
  | succ m ih =>
    rw [palCircuit, Circuit.eval_comp, Formula.eval_toCircuit, eval_palStepFormula _ (map_zero _),
      palindrome_succ, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [ih, Fin.append_left, Fin.append_right]

/-- The palindrome circuit computes `Pal_{2m}` as a non-commutative polynomial. -/
theorem noncommPolynomial_palCircuit (n m : ℕ) :
    (palCircuit K n m).noncommPolynomial 0 = palindrome K (Fin n) m := by
  rw [Circuit.noncommPolynomial_eq_eval, eval_palCircuit]
  exact DFunLike.congr_fun (lift_comp_ι (AlgHom.id K (FreeAlgebra K (Fin n)))) _

end Circuit

/-- **Non-commutative ABPs versus circuits** ([Nisan1991NonCommutative], Theorem 4;
[Saptharishi2026Survey], Theorem 11.4 and the remark after it). Over `n` variables, `Pal_{2m}`
is computed by a non-commutative arithmetic circuit with `(3n + 1) m + 1` gates, while every
homogeneous layered non-commutative ABP computing it has at least `n ^ m` vertices. For `n ≥ 2`
this is an exponential separation in `m`. -/
theorem palindrome_separation {K : Type*} [Field K] (n m : ℕ) :
    (∃ c : Circuit (arithSignature K) n 1, c.size = (3 * n + 1) * m + 1 ∧
        c.noncommPolynomial 0 = palindrome K (Fin n) m) ∧
      ∀ A : NoncommABP K (Fin n) (m + m), A.polynomial = palindrome K (Fin n) m →
        n ^ m ≤ A.size := by
  refine ⟨⟨palCircuit K n m, size_palCircuit n m, noncommPolynomial_palCircuit n m⟩,
    fun A hA => ?_⟩
  have h := A.pow_le_width_of_polynomial_eq_palindrome hA
  rw [Fintype.card_fin] at h
  exact h.trans (A.width_le_size (Nat.le_add_right m m))

end Cslib.Circuits.Arithmetic
