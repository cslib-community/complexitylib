/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import CslibFrontier.Crypto.Computational.LWE.Basic
public import CslibFrontier.Crypto.Computational.SIS.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Negacyclic Polynomial Rings, Module-SIS and Module-LWE

This module states structured lattice problems over the negacyclic polynomial ring
`R_q = ℤ_q[X] / (X^n + 1)` ([Lyubashevsky2012], [DucasEtAl2018]). The unstructured short integer
solution problem is in `CslibFrontier.Crypto.Computational.SIS.Basic`.

1. **Negacyclic polynomial rings (`rotMatrix`, `negacyclicMul`)**:
   Elements of `R[X] / (X^n + 1)` are represented by their coefficient vectors `Fin n → R`.
   Multiplication by `a : Fin n → R` is the linear action of its `n × n` negacyclic
   (anticirculant) matrix `rotMatrix a`, so `negacyclicMul a b = rotMatrix a *ᵥ b`.
2. **Module-SIS, Ring-SIS and the structured-to-unstructured embedding (`ModuleSIS`, `RingSIS`)**:
   A `d × k` module matrix `A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)` defines the linear map
   `moduleSISMap A z i = ∑ j, negacyclicMul (A i j) (z j)` (`RingSIS` is the rank-`1` case).
   Replacing each polynomial entry `A i j` by its `n × n` block `rotMatrix (A i j)` gives an
   unstructured `(d * n) × (k * n)` matrix `expandModuleMatrix A` over `ZMod q` that preserves
   the linear relation (`expandModuleMatrix_mulVec`), non-zeroness and the `ℓ_∞` norm bound under
   coefficient flattening `flattenPolyVec`. Consequently, `ModuleSIS.IsSolution` is equivalent to
   `SIS.IsSolution` on `expandModuleMatrix A` (`isSolution_expandModuleMatrix_iff`).
   `moduleSISExperiment` draws a uniform module matrix and tests the solver's answer as
   `sisExperiment` does, and `ModuleSIS M` asserts that every PPT solver has negligible
   advantage for the parameter family `M`. Solver machines read a module matrix through its
   expansion (`ModuleSIS.encodeMatrix`). This module proves no relation between `ModuleSIS` and
   `SIS`, whose experiment draws a uniform unstructured matrix.
3. **Module-LWE (`ModuleLWE`, `DecisionModuleLWE`)**:
   Samples `(A, A · s + e)` over `R_q` expand via `expandModuleMatrix` and `flattenPolyVec` into
   standard LWE relations `(expandModuleMatrix A) *ᵥ flattenPolyVec s + flattenPolyVec e`
   (`ModuleLWE.flattenPolyVec_sample`), and `DecisionModuleLWE` states computational
   indistinguishability of encoded Module-LWE samples from uniform module samples.

## Main definitions

* `Cslib.Crypto.rotMatrix`, `Cslib.Crypto.negacyclicMul`: the `n × n` negacyclic multiplication
  matrix and convolution in `R[X] / (X^n + 1)`.
* `Cslib.Crypto.moduleSISMap`, `Cslib.Crypto.ringSISMap`: the Module-SIS and Ring-SIS linear maps.
* `Cslib.Crypto.ModuleSISParams`, `Cslib.Crypto.RingSISParams`,
  `Cslib.Crypto.RingSISParams.toModuleSISParams`: Module-SIS and Ring-SIS parameter families.
* `Cslib.Crypto.ModuleSIS.IsSolution`, `Cslib.Crypto.ModuleSIS.inInfNormBound`,
  `Cslib.Crypto.ModuleSIS.IsResidueSolution`: short solutions for Module-SIS.
* `Cslib.Crypto.expandModuleMatrix`, `Cslib.Crypto.flattenPolyVec`,
  `Cslib.Crypto.unflattenPolyVec`: block-anticirculant matrix expansion and coefficient
  flattening.
* `Cslib.Crypto.ModuleSIS.encodeMatrix`, `Cslib.Crypto.ModuleSIS.encodeVec`: module matrix and
  integer polynomial vector encodings.
* `Cslib.Crypto.moduleSISExperiment`, `Cslib.Crypto.moduleSISAdvantage`: the fixed-instance
  Module-SIS experiment and its success probability.
* `Cslib.Crypto.ModuleSISParams.Input`, `Cslib.Crypto.ModuleSISParams.encInput`,
  `Cslib.Crypto.ModuleSISParams.Solver`, `Cslib.Crypto.ModuleSISParams.Solver.IsPPT`: solver
  inputs and their encoding, and efficient solvers.
* `Cslib.Crypto.ModuleSIS`, `Cslib.Crypto.RingSIS`: the Module-SIS and Ring-SIS hardness
  hypotheses.
* `Cslib.Crypto.ModuleLWE.sample`, `Cslib.Crypto.ModuleLWE.encodeSample`,
  `Cslib.Crypto.ModuleLWE.sampleLaw`, `Cslib.Crypto.ModuleLWE.realEnsemble`,
  `Cslib.Crypto.ModuleLWE.uniformEnsemble`, `Cslib.Crypto.DecisionModuleLWE`: Module-LWE sample
  law, ensembles and decision hardness hypothesis.

## Main results

* `Cslib.Crypto.negacyclicMul_add`, `Cslib.Crypto.add_negacyclicMul`,
  `Cslib.Crypto.map_negacyclicMul`, `Cslib.Crypto.abs_negacyclicMul_le`: bilinearity, ring-map
  compatibility and `ℓ_∞` norm bound for negacyclic polynomial multiplication.
* `Cslib.Crypto.expandModuleMatrix_mulVec`,
  `Cslib.Crypto.expandModuleMatrix_mulVec_eq_zero_iff`: block-anticirculant matrix-vector
  product agrees with `moduleSISMap` after coefficient flattening.
* `Cslib.Crypto.expandModuleMatrix_injective`: a module matrix is determined by its expansion.
* `Cslib.Crypto.ModuleSIS.isSolution_expandModuleMatrix_iff`,
  `Cslib.Crypto.ModuleSIS.isResidueSolution_expandModuleMatrix_iff`: `ModuleSIS` solutions are
  characterized by `SIS` solutions of `expandModuleMatrix A`.
* `Cslib.Crypto.ModuleLWE.flattenPolyVec_sample`: Module-LWE samples flatten to standard LWE
  matrix-vector relations under `expandModuleMatrix`.

## References

* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal ENNReal

/-! ### Part 1: Negacyclic Polynomial Ring `R[X] / (X^n + 1)` -/

/-- The `n × n` negacyclic (anticirculant) multiplication matrix of a degree-`< n` polynomial
`a : Fin n → R` in `R[X] / (X^n + 1)`. Column `j` represents `X^j · a(X) mod (X^n + 1)`. -/
def rotMatrix {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if h : j.val ≤ i.val then
      a ⟨i.val - j.val, by omega⟩
    else
      -a ⟨n + i.val - j.val, by omega⟩

/-- Negacyclic polynomial multiplication `a * b mod (X^n + 1)` on coefficient vectors
`Fin n → R`, defined as the matrix-vector product `rotMatrix a *ᵥ b`. -/
def negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) : Fin n → R :=
  rotMatrix a *ᵥ b

/-- Negacyclic multiplication is the matrix-vector product with `rotMatrix a`. -/
@[simp] theorem rotMatrix_mulVec {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    rotMatrix a *ᵥ b = negacyclicMul a b :=
  rfl

/-- The negacyclic matrix of the zero polynomial is the zero matrix. -/
@[simp] theorem rotMatrix_zero {n : ℕ} {R : Type*} [Ring R] :
    rotMatrix (0 : Fin n → R) = 0 := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.zero_apply, Matrix.zero_apply]
  split_ifs <;> simp

/-- `rotMatrix` preserves addition of coefficient vectors. -/
theorem rotMatrix_add {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    rotMatrix (a + b) = rotMatrix a + rotMatrix b := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> abel

/-- `rotMatrix` commutes with negation of coefficient vectors. -/
theorem rotMatrix_neg {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) :
    rotMatrix (-a) = -rotMatrix a := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.neg_apply, Matrix.neg_apply]
  split_ifs <;> abel

/-- `rotMatrix` commutes with subtraction of coefficient vectors. -/
theorem rotMatrix_sub {n : ℕ} {R : Type*} [Ring R] (a b : Fin n → R) :
    rotMatrix (a - b) = rotMatrix a - rotMatrix b := by
  ext i j
  simp only [rotMatrix, Matrix.of_apply, Pi.sub_apply, Matrix.sub_apply]
  split_ifs <;> abel

/-- `rotMatrix` commutes with ring homomorphisms. -/
theorem map_rotMatrix {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (a : Fin n → R) :
    (rotMatrix a).map f = rotMatrix (f ∘ a) := by
  ext i j
  simp only [Matrix.map_apply, rotMatrix, Matrix.of_apply, Function.comp_apply]
  split_ifs <;> simp

/-- Negacyclic multiplication distributes over addition on the right. -/
theorem negacyclicMul_add {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul a (b + c) = negacyclicMul a b + negacyclicMul a c :=
  Matrix.mulVec_add (rotMatrix a) b c

/-- Negacyclic multiplication distributes over addition on the left. -/
theorem add_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a b c : Fin n → R) :
    negacyclicMul (a + b) c = negacyclicMul a c + negacyclicMul b c := by
  simp only [negacyclicMul, rotMatrix_add, Matrix.add_mulVec]

/-- Negacyclic multiplication with zero on the right is zero. -/
@[simp] theorem negacyclicMul_zero {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) :
    negacyclicMul a 0 = 0 :=
  Matrix.mulVec_zero (rotMatrix a)

/-- Negacyclic multiplication with zero on the left is zero. -/
@[simp] theorem zero_negacyclicMul {n : ℕ} {R : Type*} [Ring R] (a : Fin n → R) :
    negacyclicMul 0 a = 0 := by
  simp only [negacyclicMul, rotMatrix_zero, Matrix.zero_mulVec]

/-- Negacyclic multiplication commutes with ring homomorphisms applied to coefficients. -/
theorem map_negacyclicMul {n : ℕ} {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (a b : Fin n → R) :
    f ∘ negacyclicMul a b = negacyclicMul (f ∘ a) (f ∘ b) := by
  funext i
  have h := RingHom.map_mulVec f (rotMatrix a) b i
  rw [map_rotMatrix] at h
  exact h

/-- Entrywise absolute-value bound for `rotMatrix` over `ℤ`. -/
theorem abs_rotMatrix_le {n α : ℕ} {a : Fin n → ℤ} (ha : ∀ i, |a i| ≤ α) (i j : Fin n) :
    |rotMatrix a i j| ≤ α := by
  simp only [rotMatrix, Matrix.of_apply]
  split_ifs with h
  · exact ha ⟨i.val - j.val, by omega⟩
  · rw [abs_neg]
    exact ha ⟨n + i.val - j.val, by omega⟩

/-- **Infinity-norm bound for negacyclic multiplication**: if `‖a‖_∞ ≤ α` and `‖b‖_∞ ≤ β`, then
every coefficient of `negacyclicMul a b` has absolute value at most `n * α * β`. -/
theorem abs_negacyclicMul_le {n α β : ℕ} {a b : Fin n → ℤ}
    (ha : ∀ i, |a i| ≤ α) (hb : ∀ j, |b j| ≤ β) (i : Fin n) :
    |negacyclicMul a b i| ≤ n * α * β := by
  calc |negacyclicMul a b i|
      = |∑ j : Fin n, rotMatrix a i j * b j| := rfl
    _ ≤ ∑ j : Fin n, |rotMatrix a i j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin n, ((α : ℤ) * β) := Finset.sum_le_sum fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (abs_rotMatrix_le ha i j) (hb j) (abs_nonneg _) (by positivity)
    _ = n * α * β := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-! ### Part 2: Module-SIS, Ring-SIS and Structured-to-Unstructured Expansion -/

/-- The Module-SIS linear map `A · z` over `ℤ_q[X] / (X^n + 1)`: the `i`-th output polynomial
is `∑ j : Fin k, negacyclicMul (A i j) (z j)`. -/
def moduleSISMap {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (z : Fin k → Fin n → ZMod q) : Fin d → Fin n → ZMod q :=
  fun i => ∑ j : Fin k, negacyclicMul (A i j) (z j)

/-- The Ring-SIS linear map `∑ j : Fin k, negacyclicMul (a j) (z j)` over `ℤ_q[X] / (X^n + 1)`
(the rank `d = 1` specialization of `moduleSISMap`). -/
def ringSISMap {k n q : ℕ}
    (a : Fin k → Fin n → ZMod q)
    (z : Fin k → Fin n → ZMod q) : Fin n → ZMod q :=
  ∑ j : Fin k, negacyclicMul (a j) (z j)

/-- `moduleSISMap` on a `1 × k` row matrix agrees with `ringSISMap`. -/
@[simp] theorem moduleSISMap_one_apply {k n q : ℕ}
    (a : Fin k → Fin n → ZMod q) (z : Fin k → Fin n → ZMod q) :
    moduleSISMap (Matrix.of fun (_ : Fin 1) j => a j) z 0 = ringSISMap a z :=
  rfl

/-- `moduleSISMap` is linear in `z`: it maps zero to zero. -/
@[simp] theorem moduleSISMap_zero {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) :
    moduleSISMap A 0 = 0 := by
  funext i
  simp [moduleSISMap]

/-- `moduleSISMap` distributes over addition of module vectors. -/
theorem moduleSISMap_add {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (y z : Fin k → Fin n → ZMod q) :
    moduleSISMap A (y + z) = moduleSISMap A y + moduleSISMap A z := by
  funext i
  simp only [moduleSISMap, Pi.add_apply, negacyclicMul_add, Finset.sum_add_distrib]

/-- Parameter family for Module-SIS over `ℤ_q[X] / (X^n + 1)` ([Lyubashevsky2012],
[DucasEtAl2018]). -/
structure ModuleSISParams where
  /-- Degree `n` of the quotient polynomial `X^n + 1`. -/
  n : ℕ → ℕ
  /-- Module rank `d` (number of rows over `R_q`). -/
  d : ℕ → ℕ
  /-- Number of module columns `k` (number of ring elements in a solution vector). -/
  k : ℕ → ℕ
  /-- Modulus `q` at each security parameter. -/
  q : ℕ → ℕ
  /-- Infinity-norm bound `β` on polynomial coefficients. -/
  β : ℕ → ℕ
  /-- Every modulus is nonzero. -/
  hq : ∀ security, NeZero (q security)

attribute [instance] ModuleSISParams.hq

/-- Parameter family for Ring-SIS over `ℤ_q[X] / (X^n + 1)` (rank `d = 1`). -/
structure RingSISParams where
  /-- Degree `n` of the quotient polynomial `X^n + 1`. -/
  n : ℕ → ℕ
  /-- Number of ring elements `k` in a solution vector. -/
  k : ℕ → ℕ
  /-- Modulus `q` at each security parameter. -/
  q : ℕ → ℕ
  /-- Infinity-norm bound `β` on polynomial coefficients. -/
  β : ℕ → ℕ
  /-- Every modulus is nonzero. -/
  hq : ∀ security, NeZero (q security)

attribute [instance] RingSISParams.hq

/-- View `RingSISParams` as `ModuleSISParams` of module rank `d = 1`. -/
def RingSISParams.toModuleSISParams (R : RingSISParams) : ModuleSISParams where
  n := R.n
  d _ := 1
  k := R.k
  q := R.q
  β := R.β
  hq := R.hq

/-- Flatten a module vector `z : Fin k → Fin n → α` of `k` degree-`< n` polynomials into a flat
vector `Fin (k * n) → α` via `finProdFinEquiv`. -/
def flattenPolyVec {k n : ℕ} {α : Type*} (z : Fin k → Fin n → α) : Fin (k * n) → α :=
  Function.uncurry z ∘ finProdFinEquiv.symm

/-- Unflatten a vector `v : Fin (k * n) → α` into a module vector `Fin k → Fin n → α` via
`finProdFinEquiv`. -/
def unflattenPolyVec {k n : ℕ} {α : Type*} (v : Fin (k * n) → α) : Fin k → Fin n → α :=
  fun j s => v (finProdFinEquiv (j, s))

@[simp] theorem unflattenPolyVec_flattenPolyVec {k n : ℕ} {α : Type*} (z : Fin k → Fin n → α) :
    unflattenPolyVec (flattenPolyVec z) = z := by
  funext j s
  simp only [unflattenPolyVec, flattenPolyVec, Function.comp_apply, Equiv.symm_apply_apply,
    Function.uncurry_apply_pair]

@[simp] theorem flattenPolyVec_unflattenPolyVec {k n : ℕ} {α : Type*} (v : Fin (k * n) → α) :
    flattenPolyVec (unflattenPolyVec v) = v := by
  funext c
  simp only [unflattenPolyVec, flattenPolyVec, Function.comp_apply, Function.uncurry,
    Prod.mk.eta, Equiv.apply_symm_apply]

@[simp] theorem flattenPolyVec_apply {k n : ℕ} {α : Type*} (z : Fin k → Fin n → α)
    (j : Fin k) (s : Fin n) :
    flattenPolyVec z (finProdFinEquiv (j, s)) = z j s := by
  simp only [flattenPolyVec, Function.comp_apply, Equiv.symm_apply_apply,
    Function.uncurry_apply_pair]

@[simp] theorem flattenPolyVec_zero {k n : ℕ} {α : Type*} [Zero α] :
    flattenPolyVec (0 : Fin k → Fin n → α) = 0 :=
  rfl

@[simp] theorem flattenPolyVec_add {k n : ℕ} {α : Type*} [Add α] (y z : Fin k → Fin n → α) :
    flattenPolyVec (y + z) = flattenPolyVec y + flattenPolyVec z :=
  rfl

/-- `flattenPolyVec` is injective. -/
theorem flattenPolyVec_injective {k n : ℕ} {α : Type*} :
    Function.Injective (flattenPolyVec (k := k) (n := n) (α := α)) :=
  Function.LeftInverse.injective unflattenPolyVec_flattenPolyVec

/-- Flattening preserves equality with zero. -/
@[simp] theorem flattenPolyVec_eq_zero_iff {k n : ℕ} {α : Type*} [Zero α]
    (z : Fin k → Fin n → α) :
    flattenPolyVec z = 0 ↔ z = 0 :=
  ⟨fun h => flattenPolyVec_injective (by simpa using h), fun h => by subst h; rfl⟩

/-- Flattening preserves non-zeroness. -/
theorem flattenPolyVec_ne_zero_iff {k n : ℕ} {α : Type*} [Zero α]
    (z : Fin k → Fin n → α) :
    flattenPolyVec z ≠ 0 ↔ z ≠ 0 :=
  not_congr (flattenPolyVec_eq_zero_iff z)

/-- Flattening commutes with coordinatewise casting `Int.cast`. -/
theorem intCast_comp_flattenPolyVec {k n q : ℕ} (z : Fin k → Fin n → ℤ) :
    (Int.cast ∘ flattenPolyVec z : Fin (k * n) → ZMod q) =
      flattenPolyVec (fun j s => (z j s : ZMod q)) :=
  rfl

/-- Expand a `d × k` module matrix `A` over `ℤ_q[X] / (X^n + 1)` into a `(d * n) × (k * n)`
scalar matrix over `ℤ_q` by replacing each polynomial entry `A i j` with its `n × n` negacyclic
multiplication block `rotMatrix (A i j)`. -/
def expandModuleMatrix {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) :
    Matrix (Fin (d * n)) (Fin (k * n)) (ZMod q) :=
  Matrix.of fun p c =>
    rotMatrix (A (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm c).1)
      (finProdFinEquiv.symm p).2 (finProdFinEquiv.symm c).2

@[simp] theorem expandModuleMatrix_apply {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (i : Fin d) (r : Fin n) (j : Fin k) (s : Fin n) :
    expandModuleMatrix A (finProdFinEquiv (i, r)) (finProdFinEquiv (j, s)) =
      rotMatrix (A i j) r s := by
  simp only [expandModuleMatrix, Matrix.of_apply, Equiv.symm_apply_apply]

/-- A module matrix is determined by its expansion: column `0` of the block `rotMatrix (A i j)`
is the coefficient vector of `A i j`. -/
theorem expandModuleMatrix_injective {d k n q : ℕ} :
    Function.Injective (expandModuleMatrix (d := d) (k := k) (n := n) (q := q)) := by
  intro A B h
  ext i j r
  have col0 (a : Fin n → ZMod q) : rotMatrix a r ⟨0, r.pos⟩ = a r := by
    simp only [rotMatrix, Matrix.of_apply, Nat.zero_le, ↓reduceDIte, Nat.sub_zero, Fin.eta]
  have hr := congrFun (congrFun h (finProdFinEquiv (i, r)))
    (finProdFinEquiv (j, ⟨0, r.pos⟩))
  rwa [expandModuleMatrix_apply, expandModuleMatrix_apply, col0, col0] at hr

/-- **Structured-to-unstructured multiplication identity**: multiplying `expandModuleMatrix A` by
`flattenPolyVec z` equals flattening `moduleSISMap A z`. -/
theorem expandModuleMatrix_mulVec {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (z : Fin k → Fin n → ZMod q) :
    expandModuleMatrix A *ᵥ flattenPolyVec z = flattenPolyVec (moduleSISMap A z) := by
  funext p
  obtain ⟨⟨i, r⟩, rfl⟩ := finProdFinEquiv.surjective p
  simp only [Matrix.mulVec, dotProduct, flattenPolyVec_apply]
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, expandModuleMatrix_apply, flattenPolyVec_apply]
  simp only [moduleSISMap, Finset.sum_apply, negacyclicMul, Matrix.mulVec, dotProduct]

/-- `expandModuleMatrix A *ᵥ flattenPolyVec z = 0` if and only if `moduleSISMap A z = 0`. -/
@[simp] theorem expandModuleMatrix_mulVec_eq_zero_iff {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q))
    (z : Fin k → Fin n → ZMod q) :
    expandModuleMatrix A *ᵥ flattenPolyVec z = 0 ↔ moduleSISMap A z = 0 := by
  rw [expandModuleMatrix_mulVec, flattenPolyVec_eq_zero_iff]

namespace ModuleSIS

/-- An integer polynomial vector `z : Fin k → Fin n → ℤ` is a short solution for a module matrix
`A` with bound `β` when `z ≠ 0`, every coefficient lies in `[-β, β]`, and
`moduleSISMap A (fun j s => (z j s : ZMod q)) = 0`. -/
def IsSolution {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (β : ℕ)
    (z : Fin k → Fin n → ℤ) : Prop :=
  z ≠ 0 ∧ (∀ j s, |z j s| ≤ β) ∧ moduleSISMap A (fun j s => (z j s : ZMod q)) = 0

instance {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (β : ℕ)
    (z : Fin k → Fin n → ℤ) : Decidable (IsSolution A β z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A residue polynomial vector `z : Fin k → Fin n → ZMod q` satisfies the `ℓ_∞` norm bound `β`
when every coefficient's centered representative has absolute value at most `β`. -/
def inInfNormBound {k n q : ℕ} (β : ℕ) (z : Fin k → Fin n → ZMod q) : Prop :=
  ∀ j s, |(z j s).valMinAbs| ≤ β

instance {k n q : ℕ} (β : ℕ) (z : Fin k → Fin n → ZMod q) :
    Decidable (inInfNormBound β z) :=
  inferInstanceAs (Decidable (∀ _ _, _))

/-- Residue-level Module-SIS solution predicate: `z ≠ 0`, `inInfNormBound β z`, and
`moduleSISMap A z = 0`. -/
def IsResidueSolution {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (β : ℕ)
    (z : Fin k → Fin n → ZMod q) : Prop :=
  z ≠ 0 ∧ inInfNormBound β z ∧ moduleSISMap A z = 0

instance {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (β : ℕ)
    (z : Fin k → Fin n → ZMod q) : Decidable (IsResidueSolution A β z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Flattening preserves the `ℓ_∞` bound on integer polynomial vectors. -/
@[simp] theorem forall_abs_flattenPolyVec_le_iff {k n β : ℕ} (z : Fin k → Fin n → ℤ) :
    (∀ c, |flattenPolyVec z c| ≤ β) ↔ ∀ j s, |z j s| ≤ β :=
  ⟨fun h j s => by simpa using h (finProdFinEquiv (j, s)),
   fun h c => by
     obtain ⟨⟨j, s⟩, rfl⟩ := finProdFinEquiv.surjective c
     simpa using h j s⟩

/-- Flattening preserves `inInfNormBound` on residue polynomial vectors. -/
@[simp] theorem inInfNormBound_flattenPolyVec_iff {k n q β : ℕ} (z : Fin k → Fin n → ZMod q) :
    SIS.inInfNormBound β (flattenPolyVec z) ↔ inInfNormBound β z :=
  ⟨fun h j s => by simpa [SIS.inInfNormBound] using h (finProdFinEquiv (j, s)),
   fun h c => by
     obtain ⟨⟨j, s⟩, rfl⟩ := finProdFinEquiv.surjective c
     simpa [SIS.inInfNormBound] using h j s⟩

/-- **Equivalence of Module-SIS and unstructured SIS on `expandModuleMatrix`**: an integer
polynomial vector `z` is a `ModuleSIS.IsSolution` for `A` if and only if `flattenPolyVec z` is
an `SIS.IsSolution` for `expandModuleMatrix A`. -/
theorem isSolution_expandModuleMatrix_iff {d k n q β : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (z : Fin k → Fin n → ℤ) :
    SIS.IsSolution (expandModuleMatrix A) β (flattenPolyVec z) ↔ IsSolution A β z := by
  simp only [SIS.IsSolution, IsSolution, flattenPolyVec_ne_zero_iff,
    forall_abs_flattenPolyVec_le_iff, intCast_comp_flattenPolyVec,
    expandModuleMatrix_mulVec_eq_zero_iff]

/-- **Equivalence of residue-level Module-SIS and unstructured SIS on `expandModuleMatrix`**:
`flattenPolyVec z` is a `SIS.IsResidueSolution` for `expandModuleMatrix A` if and only if `z` is a
`ModuleSIS.IsResidueSolution` for `A`. -/
theorem isResidueSolution_expandModuleMatrix_iff {d k n q β : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (z : Fin k → Fin n → ZMod q) :
    SIS.IsResidueSolution (expandModuleMatrix A) β (flattenPolyVec z) ↔
      IsResidueSolution A β z := by
  simp only [IsResidueSolution, SIS.IsResidueSolution, flattenPolyVec_ne_zero_iff,
    inInfNormBound_flattenPolyVec_iff, expandModuleMatrix_mulVec_eq_zero_iff]

/-- Encode a module matrix `A` over `ℤ_q[X] / (X^n + 1)` by encoding its expanded block matrix
`expandModuleMatrix A`. -/
def encodeMatrix {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) : List Bool :=
  SIS.encodeMatrix (expandModuleMatrix A)

/-- Module matrices of fixed shape are determined by their encodings when `q ≠ 0`. -/
theorem encodeMatrix_injective {d k n q : ℕ} [NeZero q] :
    Function.Injective (encodeMatrix (d := d) (k := k) (n := n) (q := q)) :=
  SIS.encodeMatrix_injective.comp expandModuleMatrix_injective

/-- Encode an integer polynomial vector `z : Fin k → Fin n → ℤ` by encoding `flattenPolyVec z`. -/
def encodeVec {k n : ℕ} (z : Fin k → Fin n → ℤ) : List Bool :=
  SIS.encodeVec (flattenPolyVec z)

/-- Integer polynomial vectors of fixed shape are determined by their encodings. -/
theorem encodeVec_injective {k n : ℕ} : Function.Injective (encodeVec (k := k) (n := n)) :=
  SIS.encodeVec_injective.comp flattenPolyVec_injective

end ModuleSIS

/-! #### The fixed-instance experiment -/

section Experiment

variable (q : ℕ) [NeZero q] {d k n : ℕ}

/-- The Module-SIS experiment over `ℤ_q[X] / (X^n + 1)` with a `d × k` module matrix and bound `β`
([Lyubashevsky2012], [DucasEtAl2018]): the challenger draws a uniform module matrix `A`; the
solver wins when it returns a short solution for `A`. -/
noncomputable def moduleSISExperiment (β : ℕ)
    (S : Matrix (Fin d) (Fin k) (Fin n → ZMod q) → ProbComp (Fin k → Fin n → ℤ)) :
    ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin d) (Fin k) (Fin n → ZMod q))
  let z ← S A
  return decide (ModuleSIS.IsSolution A β z)

/-- The Module-SIS advantage of `S`: its success probability in `moduleSISExperiment`. -/
noncomputable def moduleSISAdvantage (β : ℕ)
    (S : Matrix (Fin d) (Fin k) (Fin n → ZMod q) → ProbComp (Fin k → Fin n → ℤ)) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (moduleSISExperiment q β S))

end Experiment

/-! #### Parameter families -/

namespace ModuleSISParams

variable (M : ModuleSISParams)

/-- The input of a Module-SIS solver for the family `M`: the security parameter and a module
matrix of the shape, degree and modulus that `M` assigns to it. -/
structure Input where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public module matrix. -/
  matrix :
    Matrix (Fin (M.d secParam)) (Fin (M.k secParam)) (Fin (M.n secParam) → ZMod (M.q secParam))

variable {M}

/-- The words a machine reads for a Module-SIS input: the security parameter and the encoded
module matrix. -/
def Input.words (x : M.Input) : ℕ × List Bool :=
  (x.secParam, ModuleSIS.encodeMatrix x.matrix)

/-- A Module-SIS input is determined by its words. -/
theorem Input.words_injective : Function.Injective (Input.words (M := M)) := by
  rintro ⟨κ, A⟩ ⟨κ', B⟩ h
  simp only [Input.words, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [ModuleSIS.encodeMatrix_injective h]

variable (M)

/-- The encoding of a Module-SIS input: the framed unary security parameter followed by the
encoded module matrix (`encInput_apply`). -/
def encInput : M.Input ↪ List Bool :=
  (⟨Input.words, Input.words_injective⟩ : M.Input ↪ _).trans (encPair encUnary encBits)

/-- The Module-SIS input layout. -/
theorem encInput_apply (x : M.Input) :
    M.encInput x = frame (encUnary x.secParam) ++ ModuleSIS.encodeMatrix x.matrix := by
  simp [encInput, Input.words, encPair, encBits]

/-- A Module-SIS solver for the family `M`: given the security parameter `κ` and a module matrix
of the shape, degree and modulus of `M` at `κ`, it returns an integer polynomial vector.
`Solver.IsPPT` states its efficiency on encodings. -/
abbrev Solver : Type :=
  (κ : ℕ) → Matrix (Fin (M.d κ)) (Fin (M.k κ)) (Fin (M.n κ) → ZMod (M.q κ)) →
    ProbComp (Fin (M.k κ) → Fin (M.n κ) → ℤ)

variable {M} in
/-- A Module-SIS solver is PPT when one uniform strict PPT machine reads `encInput` and writes
the encoding of the solver's answer. -/
def Solver.IsPPT (S : M.Solver) : Prop :=
  IsPPTOn M.encInput encBits fun x => ModuleSIS.encodeVec <$> S x.secParam x.matrix

end ModuleSISParams

/-- The Module-SIS hardness hypothesis for a parameter family `M`: every PPT solver has
negligible advantage in `moduleSISExperiment` at the parameters `M` assigns to each security
parameter. This is a hypothesis against classical adversaries, not a theorem of hardness. -/
def ModuleSIS (M : ModuleSISParams) : Prop :=
  ∀ S : M.Solver, S.IsPPT → Negligible fun κ => moduleSISAdvantage (M.q κ) (M.β κ) (S κ)

/-- The Ring-SIS hardness hypothesis is `ModuleSIS` at module rank `1`. -/
abbrev RingSIS (R : RingSISParams) : Prop :=
  ModuleSIS R.toModuleSISParams

/-! ### Part 3: Module-LWE and Structured Expansion -/

namespace ModuleLWE

/-- Deterministic Module-LWE noisy linear map `A · s + e` over `ℤ_q[X] / (X^n + 1)`. -/
def sample {m d n q : ℕ}
    (A : Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (s : Fin d → Fin n → ZMod q)
    (e : Fin m → Fin n → ZMod q) : Fin m → Fin n → ZMod q :=
  moduleSISMap A s + e

/-- **Structured-to-unstructured Module-LWE identity**: flattening `ModuleLWE.sample A s e` gives
the standard LWE vector `expandModuleMatrix A *ᵥ flattenPolyVec s + flattenPolyVec e`. -/
theorem flattenPolyVec_sample {m d n q : ℕ}
    (A : Matrix (Fin m) (Fin d) (Fin n → ZMod q))
    (s : Fin d → Fin n → ZMod q)
    (e : Fin m → Fin n → ZMod q) :
    flattenPolyVec (sample A s e) =
      expandModuleMatrix A *ᵥ flattenPolyVec s + flattenPolyVec e := by
  rw [sample, flattenPolyVec_add, expandModuleMatrix_mulVec]

/-- Encode a Module-LWE public pair `(A, b)` as a framed pair of the encoded module matrix `A`
and the framed list of natural residue coefficients of `b`. -/
def encodeSample {m d n q : ℕ}
    (pair : Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q)) : List Bool :=
  encPair encBits (encList encNat)
    (ModuleSIS.encodeMatrix pair.1,
      List.ofFn fun c : Fin (m * n) => (flattenPolyVec pair.2 c).val)

/-- Draw a Module-LWE sample `(A, A · s + e)` with uniform `A`, uniform secret `s`, and
independent polynomial errors drawn from `noise`. -/
noncomputable def sampleLaw (m d n q : ℕ) [NeZero q] (noise : PMF (Fin n → ZMod q)) :
    PMF (Matrix (Fin m) (Fin d) (Fin n → ZMod q) × (Fin m → Fin n → ZMod q)) := do
  let secret ← PMF.uniformOfFintype (Fin d → Fin n → ZMod q)
  let A ← PMF.uniformOfFintype (Matrix (Fin m) (Fin d) (Fin n → ZMod q))
  let error ← PMF.pi (fun _ : Fin m => noise)
  return (A, sample A secret error)

/-- Encoded real Module-LWE ensemble at each security parameter. -/
noncomputable def realEnsemble (m d n q : ℕ → ℕ)
    [∀ security, NeZero (q security)]
    (noise : (security : ℕ) → PMF (Fin (n security) → ZMod (q security)))
    (security : ℕ) : PMF (List Bool) :=
  (sampleLaw (m security) (d security) (n security) (q security) (noise security)).map
    encodeSample

/-- Encoded uniform comparison ensemble `(A, u)` with independent uniform `A` and `u`. -/
noncomputable def uniformEnsemble (m d n q : ℕ → ℕ)
    [∀ security, NeZero (q security)]
    (security : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype
    (Matrix (Fin (m security)) (Fin (d security)) (Fin (n security) → ZMod (q security)) ×
      (Fin (m security) → Fin (n security) → ZMod (q security)))).map encodeSample

end ModuleLWE

/-- The Decision Module-LWE hardness hypothesis over `ℤ_q[X] / (X^n + 1)`: encoded samples
`(A, A · s + e)` are computationally indistinguishable from uniform pairs `(A, u)` against
uniform classical strict PPT distinguishers. -/
def DecisionModuleLWE (m d n q : ℕ → ℕ)
    [∀ security, NeZero (q security)]
    (noise : (security : ℕ) → PMF (Fin (n security) → ZMod (q security))) : Prop :=
  ComputationallyIndistinguishable
    (ModuleLWE.realEnsemble m d n q noise)
    (ModuleLWE.uniformEnsemble m d n q)

end Cslib.Crypto
