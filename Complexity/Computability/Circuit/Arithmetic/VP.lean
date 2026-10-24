/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic
public import Complexity.Computability.Circuit.Pi
public import Cslib.Computability.Circuit.Synthesis
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Algebra.MvPolynomial.Degrees
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# p-families, p-projections and Valiant's class VP

Valiant's algebraic analogue of `P` [Valiant1979Algebra], in the form of
[Bürgisser, Chapter 2][Burgisser2000]. A *family of polynomials* over `K` has, for every `n`, a
polynomial `poly n` in `vars n` variables. It is a *p-family* when the number of variables and the
total degree are polynomially bounded in `n`. A p-family is in `VP K` when it is computed by
arithmetic circuits of polynomially bounded size.

Arithmetic circuits are the library's circuits over `Cslib.Circuits.arithSignature K`: addition
and multiplication of fan-in two and a constant gate for each element of `K`. A circuit computes a
polynomial *formally*: it is evaluated in `MvPolynomial (Fin n) K` at the variables
(`Cslib.Circuits.Circuit.polynomial`). Over a finite field this is stronger than computing the
polynomial function. Size counts every gate, constant gates included, and there is no subtraction
gate. Bürgisser counts arithmetic operations, subtraction among them, with constants free;
translating between the two conventions changes sizes by at most a constant factor and does not
change the class (a remark, not formalized here).

The definitions are those of the literature, with three points made explicit.

* **Degree.** The degree bound is part of the definition of `VP`, as in Valiant's. Small circuits
  alone do not suffice: `X ^ 2 ^ n` has circuits with at most `n` gates but is not in `VP`
  (`exists_circuit_pow_two_pow`, `powTwoPowFamily_not_mem_VP`).
* **Uniformity.** `VP` is nonuniform. Nothing relates the circuits for different `n`, and no
  machine is required to construct them.
* **Coefficients.** Valiant works over a field. The definitions make sense over every commutative
  semiring `K`, and are stated there. Hypotheses on `K`, such as its characteristic, appear only
  in the theorems that need them.

A polynomial `P` is a *projection* of `Q` when `P` arises from `Q` by substituting for each
variable of `Q` a variable of `P` or a constant. A family `f` is a *p-projection* of `g` when each
`f n` is a projection of `g (t n)` for a polynomially bounded `t`. Projections are Valiant's
reductions; `VP` is closed under them.

## Main definitions

* `Cslib.Circuits.Circuit.polynomial`: the formal polynomial computed by an arithmetic circuit.
* `Cslib.Circuits.Arithmetic.PolynomialFamily`, `PolynomialFamily.IsPFamily`: families of
  polynomials and p-families.
* `Cslib.Circuits.Arithmetic.projection`, `Cslib.Circuits.Arithmetic.IsProjection`: substitution
  of variables and constants, and projections.
* `Cslib.Circuits.Arithmetic.PolynomialFamily.IsPProjection`: p-projections.
* `Cslib.Circuits.Arithmetic.projectionCircuit`: the circuit supplying a projection's
  substitution.
* `Cslib.Circuits.Arithmetic.VP`: Valiant's class `VP`.
* `Cslib.Circuits.Arithmetic.powTwoPowFamily`: the family `X ^ 2 ^ n`.

## Main results

* `Cslib.Circuits.Circuit.aeval_polynomial`: evaluating the computed polynomial in a commutative
  algebra is evaluating the circuit there; `Cslib.Circuits.Circuit.eval_polynomial` is the case of
  the base ring.
* `Cslib.Circuits.Arithmetic.IsProjection.trans`,
  `Cslib.Circuits.Arithmetic.PolynomialFamily.IsPProjection.trans`: projections compose.
* `Cslib.Circuits.Arithmetic.totalDegree_projection_le`: projections do not raise the degree.
* `Cslib.Circuits.Synthesis.arith_const`, `Cslib.Circuits.Synthesis.arith_add`,
  `Cslib.Circuits.Synthesis.arith_mul`, `Cslib.Circuits.Synthesis.arith_sum`: synthesis rules for
  arithmetic circuits.
* `Cslib.Circuits.Synthesis.exists_circuit_polynomial`: a synthesis bound gives a circuit computing
  the polynomial.
* `Cslib.Circuits.Arithmetic.VP.of_isPProjection`: `VP` is closed under p-projections.
* `Cslib.Circuits.Arithmetic.VP.of_synthesis`: p-families synthesized within a polynomial budget
  are in `VP`.
* `Cslib.Circuits.Arithmetic.exists_circuit_pow_two_pow`,
  `Cslib.Circuits.Arithmetic.powTwoPowFamily_not_mem_VP`: repeated squaring has small circuits but
  is not in `VP`, whose definition bounds the degree.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra]
* [P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*][Burgisser2000],
  Chapter 2
-/

@[expose] public section

namespace Cslib.Circuits

open MvPolynomial

universe u

variable {K : Type u} [CommSemiring K] {n m p : ℕ}

/-- The formal polynomial computed at output `j` of an arithmetic circuit with constants from `K`:
the circuit evaluated in `MvPolynomial (Fin n) K` at the variables, the constant symbol `a`
denoting the constant polynomial `C a`. -/
noncomputable def Circuit.polynomial (c : Circuit (arithSignature K) n m) (j : Fin m) :
    MvPolynomial (Fin n) K :=
  c.eval (arithInterpretationWith K C) X j

/-- Evaluating the polynomial computed by a circuit at a point of a commutative `K`-algebra is
evaluating the circuit at that point. -/
theorem Circuit.aeval_polynomial {R : Type*} [CommSemiring R] [Algebra K R]
    (c : Circuit (arithSignature K) n m) (x : Fin n → R) (j : Fin m) :
    aeval x (c.polynomial j) = c.eval (arithInterpretationWith K (algebraMap K R)) x j := by
  let h : Homomorphism (arithInterpretationWith K (C : K → MvPolynomial (Fin n) K))
      (arithInterpretationWith K (algebraMap K R)) :=
    ⟨aeval x, fun op args => by cases op <;> simp [arithInterpretationWith]⟩
  refine (congrFun (c.map_eval h X) j).trans ?_
  congr 1
  funext i
  exact aeval_X x i

/-- Substituting polynomials for the variables of the polynomial computed by a circuit is
evaluating the circuit at those polynomials. -/
private theorem Circuit.aeval_polynomial_mvPolynomial {σ : Type*}
    (c : Circuit (arithSignature K) n m)
    (x : Fin n → MvPolynomial σ K) (j : Fin m) :
    aeval x (c.polynomial j) = c.eval (arithInterpretationWith K C) x j := by
  rw [c.aeval_polynomial, algebraMap_eq]

/-- Evaluating the formal polynomial computed by an arithmetic circuit at `x : Fin n → K` agrees
with evaluating the circuit under `arithInterpretation K`. -/
@[simp] theorem Circuit.eval_polynomial (c : Circuit (arithSignature K) n m) (x : Fin n → K)
    (j : Fin m) :
    MvPolynomial.eval x (c.polynomial j) = c.eval (arithInterpretation K) x j := by
  simpa [MvPolynomial.aeval_def, MvPolynomial.eval₂_id, arithInterpretation] using
    c.aeval_polynomial x j

/-! ### Synthesis of arithmetic circuits -/

section Synthesis

variable {R : Type*} {constant : K → R} {s : Set ((Fin n → R) → R)} {f g : (Fin n → R) → R}

omit [CommSemiring K] in
/-- A constant costs one gate. -/
theorem Synthesis.arith_const [Add R] [Mul R] (a : K) :
    Synthesis (arithInterpretationWith K constant) s {fun _ => constant a} 1 :=
  Synthesis.gate (σ := arithSignature K) (.const a) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

omit [CommSemiring K] in
/-- The sum of two available functions costs one gate. -/
theorem Synthesis.arith_add [Add R] [Mul R] (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (arithInterpretationWith K constant) s {fun x => f x + g x} 1 :=
  Synthesis.gate (σ := arithSignature K) .add ![f, g] fun i => by fin_cases i <;> assumption

omit [CommSemiring K] in
/-- The product of two available functions costs one gate. -/
theorem Synthesis.arith_mul [Add R] [Mul R] (hf : f ∈ s) (hg : g ∈ s) :
    Synthesis (arithInterpretationWith K constant) s {fun x => f x * g x} 1 :=
  Synthesis.gate (σ := arithSignature K) .mul ![f, g] fun i => by fin_cases i <;> assumption

omit [CommSemiring K] in
/-- A finite sum costs its summands and one addition each, when zero is available. -/
theorem Synthesis.arith_sum {ι : Type*} [AddCommMonoid R] [Mul R] (indices : Finset ι)
    (summand : ι → (Fin n → R) → R) (cost : ι → ℕ) (hzero : (fun _ => 0) ∈ s)
    (h : ∀ i ∈ indices, Synthesis (arithInterpretationWith K constant) s {summand i} (cost i)) :
    Synthesis (arithInterpretationWith K constant) s {fun x => ∑ i ∈ indices, summand i x}
      (∑ i ∈ indices, (cost i + 1)) := by
  have := Synthesis.finset_fold (· + ·) 1 (fun f g => Synthesis.arith_add (Set.mem_insert f {g})
    (Set.mem_insert_of_mem f rfl)) indices (Synthesis.of_mem hzero) h
  simpa only [Finset.sum_eq_fold, Nat.add_zero] using this

/-- A synthesis bound on a function `F` from the inputs gives a circuit, within the bound,
computing the polynomial `F X`. -/
theorem Synthesis.exists_circuit_polynomial
    {F : (Fin n → MvPolynomial (Fin n) K) → MvPolynomial (Fin n) K} {cost : ℕ}
    (h : Synthesis (arithInterpretationWith K C) (inputs n) {F} cost) :
    ∃ c : Circuit (arithSignature K) n 1, c.polynomial 0 = F X ∧ c.size ≤ cost := by
  obtain ⟨c, hc, hsize⟩ := h.exists_circuit
  exact ⟨c, congrFun (hc X) 0, hsize⟩

end Synthesis

namespace Arithmetic

/-- A family of polynomials over `K`: for every `n`, a polynomial `poly n` in `vars n`
variables. -/
structure PolynomialFamily (K : Type u) [CommSemiring K] where
  /-- The number of variables of each member. -/
  vars : ℕ → ℕ
  /-- The members of the family. -/
  poly (n : ℕ) : MvPolynomial (Fin (vars n)) K

namespace PolynomialFamily

/-- A *p-family* [Bürgisser, Chapter 2][Burgisser2000]: the number of variables and the total
degree are polynomially bounded. -/
def IsPFamily (f : PolynomialFamily K) : Prop :=
  PolynomiallyBounded f.vars ∧ PolynomiallyBounded fun n => (f.poly n).totalDegree

end PolynomialFamily

/-! ### Projections -/

section Projection

variable {σ τ υ : Type*}

/-- Substitute for each variable `i` of a polynomial over `τ` the variable `X k` when
`ρ i = Sum.inl k`, and the constant `C a` when `ρ i = Sum.inr a`. -/
noncomputable def projection (ρ : τ → σ ⊕ K) : MvPolynomial τ K →ₐ[K] MvPolynomial σ K :=
  aeval fun i => Sum.elim X (fun a => C a) (ρ i)

/-- A projection substitutes `X k` or `C a` for the variable `X i` according to `ρ i`. -/
@[simp] theorem projection_X (ρ : τ → σ ⊕ K) (i : τ) :
    projection ρ (X i) = Sum.elim X (fun a => C a) (ρ i) :=
  aeval_X _ i

/-- A projection fixes every constant polynomial. -/
theorem projection_C (ρ : τ → σ ⊕ K) (a : K) :
    projection ρ (C a : MvPolynomial τ K) = C a :=
  aeval_C _ a

/-- Substituting every variable for itself changes nothing. -/
@[simp] theorem projection_inl : projection (Sum.inl : σ → σ ⊕ K) = AlgHom.id K _ :=
  algHom_ext fun i => by simp

/-- Two successive projections are one projection: a variable substituted for a variable is
substituted in turn, and a constant stays. -/
theorem projection_projection (ρ : σ → υ ⊕ K) (ρ' : τ → σ ⊕ K) (P : MvPolynomial τ K) :
    projection ρ (projection ρ' P) = projection (fun i => Sum.elim ρ Sum.inr (ρ' i)) P := by
  change ((projection ρ).comp (projection ρ')) P = _
  congr 1
  refine algHom_ext fun i => ?_
  rcases h : ρ' i with k | a <;> simp [h]

/-- `P` is a *projection* of `Q` [Valiant1979Algebra]: substituting for each variable of `Q` a
variable of `P` or a constant of `K` gives `P`. -/
def IsProjection (P : MvPolynomial σ K) (Q : MvPolynomial τ K) : Prop :=
  ∃ ρ : τ → σ ⊕ K, projection ρ Q = P

/-- Every polynomial is a projection of itself. -/
theorem IsProjection.refl (P : MvPolynomial σ K) : IsProjection P P :=
  ⟨Sum.inl, by simp⟩

/-- A projection of a projection is a projection. -/
theorem IsProjection.trans {P : MvPolynomial υ K} {Q : MvPolynomial σ K} {R : MvPolynomial τ K}
    (hPQ : IsProjection P Q) (hQR : IsProjection Q R) : IsProjection P R := by
  obtain ⟨ρ, rfl⟩ := hPQ
  obtain ⟨ρ', rfl⟩ := hQR
  exact ⟨_, (projection_projection ρ ρ' R).symm⟩

private theorem totalDegree_X_le (i : σ) : (X i : MvPolynomial σ K).totalDegree ≤ 1 :=
  (totalDegree_monomial_le _ _).trans (by simp)

/-- Substituting polynomials of degree at most one does not raise the degree. -/
private theorem totalDegree_aeval_le {g : τ → MvPolynomial σ K}
    (hg : ∀ i, (g i).totalDegree ≤ 1) (P : MvPolynomial τ K) :
    (aeval g P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine totalDegree_finsetSum_le fun s hs => ?_
  rw [aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ((Finset.sum_le_sum fun i _ => ?_).trans
    (le_totalDegree hs))
  exact (totalDegree_pow _ _).trans ((Nat.mul_le_mul_left _ (hg i)).trans (Nat.mul_one _).le)

/-- Projections do not raise the total degree. -/
theorem totalDegree_projection_le (ρ : τ → σ ⊕ K) (P : MvPolynomial τ K) :
    (projection ρ P).totalDegree ≤ P.totalDegree :=
  totalDegree_aeval_le (fun i => by
    rcases ρ i with k | a
    · exact totalDegree_X_le k
    · simp) P

end Projection

namespace PolynomialFamily

/-- `f` is a *p-projection* of `g` [Valiant1979Algebra; Bürgisser, Chapter 2][Burgisser2000]:
for a polynomially bounded `t`, every `f.poly n` is a projection of `g.poly (t n)`. -/
def IsPProjection (f g : PolynomialFamily K) : Prop :=
  ∃ t : ℕ → ℕ, PolynomiallyBounded t ∧ ∀ n, IsProjection (f.poly n) (g.poly (t n))

/-- Every family is a p-projection of itself. -/
theorem IsPProjection.refl (f : PolynomialFamily K) : f.IsPProjection f :=
  ⟨fun n => n, PolynomiallyBounded.id, fun _ => IsProjection.refl _⟩

/-- A p-projection of a p-projection is a p-projection. -/
theorem IsPProjection.trans {f g h : PolynomialFamily K} (hfg : f.IsPProjection g)
    (hgh : g.IsPProjection h) : f.IsPProjection h := by
  obtain ⟨t, ht, hf⟩ := hfg
  obtain ⟨t', ht', hg⟩ := hgh
  exact ⟨fun n => t' (t n), ht'.comp ht, fun n => (hf n).trans (hg (t n))⟩

end PolynomialFamily

/-! ### Circuits for projections -/

/-- The circuit supplying the substitution of a projection: output `i` is input `k` when
`ρ i = Sum.inl k`, and a constant gate for `a` when `ρ i = Sum.inr a`. -/
def projectionCircuit (ρ : Fin m → Fin n ⊕ K) : Circuit (arithSignature K) n m :=
  Circuit.pi fun i => Sum.elim (fun k => Circuit.wiring _ fun _ => k)
    (fun a => Circuit.oneGate (σ := arithSignature K) (.const a) Fin.elim0) (ρ i)

omit [CommSemiring K] in
/-- Output `i` of `projectionCircuit ρ` evaluates to `x k` when `ρ i = Sum.inl k` and to
`constant a` when `ρ i = Sum.inr a`. -/
@[simp] theorem eval_projectionCircuit {R : Type*} [Add R] [Mul R] (constant : K → R)
    (ρ : Fin m → Fin n ⊕ K) (x : Fin n → R) (i : Fin m) :
    (projectionCircuit ρ).eval (arithInterpretationWith K constant) x i =
      Sum.elim x constant (ρ i) := by
  rw [projectionCircuit, Circuit.eval_pi]
  dsimp only
  rcases ρ i with k | a <;> rfl

omit [CommSemiring K] in
/-- The substitution of a projection needs at most one gate per substituted variable. -/
theorem size_projectionCircuit_le (ρ : Fin m → Fin n ⊕ K) : (projectionCircuit ρ).size ≤ m := by
  rw [projectionCircuit, Circuit.size_pi]
  calc _ ≤ ∑ _i : Fin m, 1 := Finset.sum_le_sum fun i _ => by rcases ρ i with k | a <;> simp
    _ = m := by simp

/-- Feeding the substitution of a projection to a circuit computes the projection of its
polynomial. -/
private theorem polynomial_comp_projectionCircuit (c : Circuit (arithSignature K) m p)
    (ρ : Fin m → Fin n ⊕ K) (j : Fin p) :
    (c.comp (projectionCircuit ρ)).polynomial j = projection ρ (c.polynomial j) := by
  rw [projection, Circuit.aeval_polynomial_mvPolynomial, Circuit.polynomial, Circuit.eval_comp]
  congr 1
  funext i
  exact eval_projectionCircuit _ ρ X i

/-! ### The class VP -/

/-- Valiant's class `VP` over `K` [Valiant1979Algebra; Bürgisser, Chapter 2][Burgisser2000]:
the p-families computed, for some polynomially bounded size function, by arithmetic circuits of
that size. Nothing relates the circuits for different `n`: the class is nonuniform. The circuits
compute the members as formal polynomials, and their degrees are bounded by the p-family
condition. -/
def VP (K : Type u) [CommSemiring K] : Set (PolynomialFamily K) :=
  {f | f.IsPFamily ∧ ∃ c : ∀ n, Circuit (arithSignature K) (f.vars n) 1,
    PolynomiallyBounded (fun n => (c n).size) ∧ ∀ n, (c n).polynomial 0 = f.poly n}

/-- Every family in `VP` is a p-family. -/
theorem VP.isPFamily {f : PolynomialFamily K} (hf : f ∈ VP K) : f.IsPFamily :=
  hf.1

/-- `VP` is closed under p-projections [Bürgisser, Chapter 2][Burgisser2000]. A projection
cannot raise the degree, but `f` may have arbitrarily many variables that it does not use, so the
number of variables of `f` is required to be polynomially bounded. -/
theorem VP.of_isPProjection {f g : PolynomialFamily K} (hg : g ∈ VP K)
    (hfg : f.IsPProjection g) (hvars : PolynomiallyBounded f.vars) : f ∈ VP K := by
  obtain ⟨⟨hgvars, hgdeg⟩, c, hc, hcg⟩ := hg
  obtain ⟨t, ht, hproj⟩ := hfg
  choose ρ hρ using hproj
  refine ⟨⟨hvars, (hgdeg.comp ht).mono_of_le fun n => ?_⟩,
    fun n => (c (t n)).comp (projectionCircuit (ρ n)),
    ((hgvars.comp ht).add (hc.comp ht)).mono_of_le fun n => ?_, fun n => ?_⟩
  · rw [← hρ n]
    exact totalDegree_projection_le _ _
  · rw [Circuit.size_comp]
    exact Nat.add_le_add_right (size_projectionCircuit_le _) _
  · rw [polynomial_comp_projectionCircuit, hcg, hρ]

/-- A p-family is in `VP` when, within a polynomially bounded budget, each member `f.poly n` is
`F n X` for a function `F n` synthesized from the inputs. -/
theorem VP.of_synthesis {f : PolynomialFamily K} (hf : f.IsPFamily) {cost : ℕ → ℕ}
    (hcost : PolynomiallyBounded cost)
    (F : ∀ n, (Fin (f.vars n) → MvPolynomial (Fin (f.vars n)) K) → MvPolynomial (Fin (f.vars n)) K)
    (hF : ∀ n, F n X = f.poly n)
    (h : ∀ n, Synthesis (arithInterpretationWith K C) (inputs (f.vars n)) {F n} (cost n)) :
    f ∈ VP K := by
  choose c hc hsize using fun n => (h n).exists_circuit_polynomial
  exact ⟨hf, c, hcost.mono_of_le hsize, fun n => (hc n).trans (hF n)⟩

/-! ### Degree is part of the definition -/

/-- The family `X ^ 2 ^ n` of powers of one variable. -/
noncomputable def powTwoPowFamily (K : Type u) [CommSemiring K] : PolynomialFamily K where
  vars _ := 1
  poly n := X 0 ^ 2 ^ n

/-- Repeated squaring computes `X ^ 2 ^ n` with at most `n` gates. -/
theorem exists_circuit_pow_two_pow (n : ℕ) : ∃ c : Circuit (arithSignature K) 1 1,
    c.polynomial 0 = (powTwoPowFamily K).poly n ∧ c.size ≤ n := by
  have h : ∀ t, Synthesis (arithInterpretationWith K C) (inputs 1)
      {fun x : Fin 1 → MvPolynomial (Fin 1) K => x 0 ^ 2 ^ t} t := by
    intro t
    induction t with
    | zero =>
      simpa using Synthesis.of_mem (I := arithInterpretationWith K C)
        (show (fun x : Fin 1 → MvPolynomial (Fin 1) K => x 0) ∈ inputs 1 from ⟨0, rfl⟩)
    | succ t ih =>
      have hsq : (fun x : Fin 1 → MvPolynomial (Fin 1) K => x 0 ^ 2 ^ (t + 1)) =
          fun x => x 0 ^ 2 ^ t * x 0 ^ 2 ^ t := by
        funext x
        rw [pow_succ, pow_mul, sq]
      rw [hsq]
      exact ih.trans (Synthesis.arith_mul (Set.mem_union_right _ rfl) (Set.mem_union_right _ rfl))
  exact (h n).exists_circuit_polynomial

/-- **VP bounds the degree.** Over a nontrivial `K`, the family `X ^ 2 ^ n` has circuits with `n`
gates (`exists_circuit_pow_two_pow`) but is not in `VP`: its degree `2 ^ n` is not polynomially
bounded. -/
theorem powTwoPowFamily_not_mem_VP [Nontrivial K] : powTwoPowFamily K ∉ VP K := by
  rintro ⟨⟨-, hdeg⟩, -⟩
  obtain ⟨n, hn⟩ := hdeg.eventually_lt_two_pow.exists
  simp [powTwoPowFamily, totalDegree_X_pow] at hn

end Arithmetic

end Cslib.Circuits
