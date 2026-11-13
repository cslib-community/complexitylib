/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import CslibFrontier.Crypto.Computational.SIS.Basic
public import CslibFrontier.Foundations.Algebra.Negacyclic

/-!
# Module-SIS

This module states the short integer solution problem over the negacyclic polynomial ring
`R_q = ℤ_q[X] / (X^n + 1)` ([Lyubashevsky2012], [DucasEtAl2018]). The unstructured short integer
solution problem is in `CslibFrontier.Crypto.Computational.SIS.Basic`, and Module-LWE over the same
ring is in `CslibFrontier.Crypto.Computational.LWE.Module`. Elements of `R_q` are represented by
their coefficient vectors `Fin n → ZMod q`, multiplied by `negacyclicMul a b = rotMatrix a *ᵥ b`;
these operations and the ring `Negacyclic R n` are in
`CslibFrontier.Foundations.Algebra.Negacyclic`.

A `d × k` module matrix `A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)` defines the linear map
`moduleSISMap A z i = ∑ j, negacyclicMul (A i j) (z j)` (`RingSIS` is the rank-`1` case).
Replacing each polynomial entry `A i j` by its `n × n` block `rotMatrix (A i j)` gives an
unstructured `(d * n) × (k * n)` matrix `expandModuleMatrix A` over `ZMod q` that preserves the
linear relation (`expandModuleMatrix_mulVec`), non-zeroness and the `ℓ_∞` norm bound under
coefficient flattening `flattenPolyVec`. Consequently, `ModuleSIS.IsSolution` is equivalent to
`SIS.IsSolution` on `expandModuleMatrix A` (`isSolution_expandModuleMatrix_iff`).
`moduleSISExperiment` draws a uniform module matrix and tests the solver's answer as
`sisExperiment` does, and `ModuleSIS M` asserts that every PPT solver has negligible advantage for
the parameter family `M`. Solver machines read a module matrix through its expansion
(`ModuleSIS.encodeMatrix`). This module proves no relation between `ModuleSIS` and `SIS`, whose
experiment draws a uniform unstructured matrix.

## Main definitions

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

## Main results

* `Cslib.Crypto.ofCoeffs_comp_moduleSISMap`, `Cslib.Crypto.moduleSISMap_eq_zero_iff`: the
  Module-SIS map and its zero equation as `A *ᵥ z` over the ring `Negacyclic (ZMod q) n`.
* `Cslib.Crypto.expandModuleMatrix_mulVec`,
  `Cslib.Crypto.expandModuleMatrix_mulVec_eq_zero_iff`: block-anticirculant matrix-vector
  product agrees with `moduleSISMap` after coefficient flattening.
* `Cslib.Crypto.expandModuleMatrix_injective`: a module matrix is determined by its expansion.
* `Cslib.Crypto.ModuleSIS.isSolution_expandModuleMatrix_iff`,
  `Cslib.Crypto.ModuleSIS.isResidueSolution_expandModuleMatrix_iff`: `ModuleSIS` solutions are
  characterized by `SIS` solutions of `expandModuleMatrix A`.

## References

* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal ENNReal

/-! ### Module-SIS, Ring-SIS and Structured-to-Unstructured Expansion -/

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

/-- The coefficient-level Module-SIS map is the matrix-vector product `A *ᵥ z` over
`Negacyclic (ZMod q) n`. -/
theorem ofCoeffs_comp_moduleSISMap {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (z : Fin k → Fin n → ZMod q) :
    Negacyclic.ofCoeffs ∘ moduleSISMap A z =
      A.map Negacyclic.ofCoeffs *ᵥ (Negacyclic.ofCoeffs ∘ z) :=
  funext fun i => Negacyclic.ofCoeffs_innerPoly (A i) z

/-- A coefficient-level Module-SIS zero equation is the zero equation of `A *ᵥ z` over
`Negacyclic (ZMod q) n`. -/
theorem moduleSISMap_eq_zero_iff {d k n q : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (z : Fin k → Fin n → ZMod q) :
    moduleSISMap A z = 0 ↔ A.map Negacyclic.ofCoeffs *ᵥ (Negacyclic.ofCoeffs ∘ z) = 0 := by
  rw [← ofCoeffs_comp_moduleSISMap]
  simp only [funext_iff, Function.comp_apply, Pi.zero_apply, Negacyclic.ext_iff,
    Negacyclic.coeffs_zero]

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

end Cslib.Crypto
