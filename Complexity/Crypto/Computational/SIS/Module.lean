/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
public import Complexity.Crypto.Computational.LWE.Basic
public import Complexity.Crypto.Computational.SIS.Basic
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF
import Complexity.Tactic.PPT
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# General-Modulus SIS, Negacyclic Polynomial Rings, Module-SIS and Module-LWE

This module extends the power-of-two short integer solution formulation in
`Complexity.Crypto.Computational.SIS.Basic` to arbitrary nonzero moduli `q` and to structured
lattice problems over the negacyclic polynomial ring `R_q = ℤ_q[X] / (X^n + 1)`
([Ajtai1996], [Lyubashevsky2009], [Lyubashevsky2012], [DucasEtAl2018]):

1. **General-modulus SIS (`GeneralSISParams`, `SISParams`, `GeneralSIS`)**:
   Whereas power-of-two SIS uses fixed-width bit slicing (`Matrix.toBinary`), general-modulus SIS
   parameterizes over any nonzero modulus schedule `q : ℕ → ℕ` (`[NeZero (q security)]`),
   including prime moduli (`SISParams`), composite moduli and powers of two
   (`GeneralSISParams.ofPowerOfTwo`). Matrices over `ZMod q` are serialized row by row with
   framed binary natural residues (`GeneralSIS.encodeMatrix`), and candidate integer vectors are
   decoded from framed binary sign-magnitude words (`GeneralSIS.decodeVec`). Ajtai's linear hash
   function `GeneralSIS.ajtaiHashEval` and collision extraction `GeneralSIS.extractSISVector`
   require no primality assumption on `q`.
2. **Negacyclic polynomial rings (`rotMatrix`, `negacyclicMul`)**:
   Elements of `R[X] / (X^n + 1)` are represented by their coefficient vectors `Fin n → R`.
   Multiplication by `a : Fin n → R` is the linear action of its `n × n` negacyclic
   (anticirculant) matrix `rotMatrix a`, so `negacyclicMul a b = rotMatrix a *ᵥ b`.
3. **Module-SIS, Ring-SIS and the structured-to-unstructured embedding (`ModuleSIS`, `RingSIS`)**:
   A `d × k` module matrix `A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)` defines the linear map
   `moduleSISMap A z i = ∑ j, negacyclicMul (A i j) (z j)` (`RingSIS` is the rank-`1` case).
   Replacing each polynomial entry `A i j` by its `n × n` block `rotMatrix (A i j)` gives an
   unstructured `(d * n) × (k * n)` matrix `expandModuleMatrix A` over `ZMod q` that preserves
   the linear relation (`expandModuleMatrix_mulVec`), non-zeroness and the `ℓ_∞` norm bound under
   coefficient flattening `flattenPolyVec`. Consequently, `ModuleSIS.IsSolution` is equivalent to
   `SIS.IsSolution` on `expandModuleMatrix A` (`isSolution_expandModuleMatrix_iff`), and any
   solver for the induced structured `GeneralSIS` game solves `ModuleSIS` with identical success
   probability (`succProbability_structuredSISGame`).
4. **Module-LWE (`ModuleLWE`, `DecisionModuleLWE`)**:
   Samples `(A, A · s + e)` over `R_q` expand via `expandModuleMatrix` and `flattenPolyVec` into
   standard LWE relations `(expandModuleMatrix A) *ᵥ flattenPolyVec s + flattenPolyVec e`
   (`ModuleLWE.flattenPolyVec_sample`), and `DecisionModuleLWE` states computational
   indistinguishability of encoded Module-LWE samples from uniform module samples.

## Main definitions

* `Cslib.Crypto.GeneralSISParams`: SIS parameters for arbitrary nonzero moduli `q`.
* `Cslib.Crypto.SISParams`, `Cslib.Crypto.SISParams.toGeneralSISParams`: prime-modulus SIS
  parameters and their projection to `GeneralSISParams`.
* `Cslib.Crypto.GeneralSISParams.ofPowerOfTwo`: power-of-two moduli `q = 2 ^ w` as
  `GeneralSISParams`.
* `Cslib.Crypto.GeneralSIS.inInfNormBound`, `Cslib.Crypto.GeneralSIS.isSISChallenge`,
  `Cslib.Crypto.GeneralSIS.liftCentered`: residue-level `ℓ_∞` norm bound, SIS predicate and
  centered integer lift.
* `Cslib.Crypto.GeneralSIS.encodeMatrix`, `Cslib.Crypto.GeneralSIS.encodeVec`,
  `Cslib.Crypto.GeneralSIS.decodeVec`: general-modulus matrix and integer-vector encodings.
* `Cslib.Crypto.GeneralSIS.sisGame`, `Cslib.Crypto.GeneralSIS.Hard`: the general-modulus SIS
  experiment and hardness hypothesis.
* `Cslib.Crypto.GeneralSIS.ajtaiHashEval`, `Cslib.Crypto.GeneralSIS.extractSISVector`,
  `Cslib.Crypto.GeneralSIS.isAjtaiCollision`, `Cslib.Crypto.GeneralSIS.ajtaiCollisionGame`,
  `Cslib.Crypto.GeneralSIS.extractSISWord`: Ajtai's hash function, collision extraction and
  collision experiment for arbitrary moduli.
* `Cslib.Crypto.rotMatrix`, `Cslib.Crypto.negacyclicMul`: the `n × n` negacyclic multiplication
  matrix and convolution in `R[X] / (X^n + 1)`.
* `Cslib.Crypto.moduleSISMap`, `Cslib.Crypto.ringSISMap`: the Module-SIS and Ring-SIS linear maps.
* `Cslib.Crypto.ModuleSISParams`, `Cslib.Crypto.RingSISParams`,
  `Cslib.Crypto.RingSISParams.toModuleSISParams`,
  `Cslib.Crypto.ModuleSISParams.toGeneralSISParams`: Module-SIS and Ring-SIS parameter bundles.
* `Cslib.Crypto.ModuleSIS.IsSolution`, `Cslib.Crypto.ModuleSIS.inInfNormBound`,
  `Cslib.Crypto.ModuleSIS.isModuleSISChallenge`: short solutions for Module-SIS.
* `Cslib.Crypto.expandModuleMatrix`, `Cslib.Crypto.flattenPolyVec`,
  `Cslib.Crypto.unflattenPolyVec`: block-anticirculant matrix expansion and coefficient
  flattening.
* `Cslib.Crypto.ModuleSIS.encodeMatrix`, `Cslib.Crypto.ModuleSIS.encodeVec`,
  `Cslib.Crypto.ModuleSIS.decodeVec`, `Cslib.Crypto.ModuleSIS.moduleSISGame`,
  `Cslib.Crypto.ModuleSIS.structuredSISGame`, `Cslib.Crypto.ModuleSIS.Hard`,
  `Cslib.Crypto.RingSIS.Hard`: Module-SIS and Ring-SIS games and hardness hypotheses.
* `Cslib.Crypto.ModuleLWE.sample`, `Cslib.Crypto.ModuleLWE.encodeSample`,
  `Cslib.Crypto.ModuleLWE.sampleLaw`, `Cslib.Crypto.ModuleLWE.realEnsemble`,
  `Cslib.Crypto.ModuleLWE.uniformEnsemble`, `Cslib.Crypto.DecisionModuleLWE`: Module-LWE sample
  law, ensembles and decision hardness hypothesis.

## Main results

* `Cslib.Crypto.GeneralSIS.isSISChallenge_iff_isSolution`: residue-level `isSISChallenge` is
  equivalent to `SIS.IsSolution` on centered integer lifts for any `[NeZero q]`.
* `Cslib.Crypto.GeneralSIS.decodeVec_encodeVec`, `Cslib.Crypto.GeneralSIS.decodeVec_nil`: exact
  roundtrip and empty-word fallback for integer-vector encoding.
* `Cslib.Crypto.GeneralSIS.sisGame_toGeneralSISParams`,
  `Cslib.Crypto.GeneralSIS.hard_toGeneralSISParams_iff`: `SISParams.toGeneralSISParams` preserves
  the SIS experiment and hardness predicate identically.
* `Cslib.Crypto.GeneralSIS.isSolution_extractSISVector_of_Icc`,
  `Cslib.Crypto.GeneralSIS.isSolution_extractSISVector_of_abs_le`,
  `Cslib.Crypto.GeneralSIS.isSolution_of_isAjtaiCollision`,
  `Cslib.Crypto.GeneralSIS.succProbability_ajtaiCollisionGame_le`: collision extraction and game
  reduction for Ajtai's hash function over arbitrary moduli.
* `Cslib.Crypto.negacyclicMul_add`, `Cslib.Crypto.add_negacyclicMul`,
  `Cslib.Crypto.map_negacyclicMul`, `Cslib.Crypto.abs_negacyclicMul_le`: bilinearity, ring-map
  compatibility and `ℓ_∞` norm bound for negacyclic polynomial multiplication.
* `Cslib.Crypto.expandModuleMatrix_mulVec`,
  `Cslib.Crypto.expandModuleMatrix_mulVec_eq_zero_iff`: block-anticirculant matrix-vector
  product agrees with `moduleSISMap` after coefficient flattening.
* `Cslib.Crypto.ModuleSIS.isSolution_expandModuleMatrix_iff`,
  `Cslib.Crypto.ModuleSIS.isModuleSISChallenge_iff_isSISChallenge`: `ModuleSIS` solutions are
  characterized by `SIS` solutions of `expandModuleMatrix A`.
* `Cslib.Crypto.ModuleSIS.succProbability_structuredSISGame`,
  `Cslib.Crypto.ModuleSIS.hard_of_structuredGeneralSIS`: structured-to-unstructured reduction from
  `ModuleSIS` to `GeneralSIS`.
* `Cslib.Crypto.ModuleLWE.flattenPolyVec_sample`: Module-LWE samples flatten to standard LWE
  matrix-vector relations under `expandModuleMatrix`.

## References

* [M. Ajtai, *Generating Hard Instances of Lattice Problems*][Ajtai1996]
* [V. Lyubashevsky, *Fiat-Shamir with Aborts: Applications to Lattice and Factoring-Based
  Signatures*][Lyubashevsky2009]
* [V. Lyubashevsky, *Lattice Signatures without Trapdoors*][Lyubashevsky2012]
* [L. Ducas et al., *CRYSTALS-Dilithium: A Lattice-Based Digital Signature
  Scheme*][DucasEtAl2018]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal ENNReal

/-! ### Part 1: General-Modulus SIS and Ajtai Collision Extraction -/

/-- Parameter family for the short integer solution problem over an arbitrary nonzero modulus
schedule `q`, without restricting `q` to primes or powers of two. -/
structure GeneralSISParams where
  /-- Number of rows of the public matrix. -/
  n : ℕ → ℕ
  /-- Number of columns of the public matrix. -/
  m : ℕ → ℕ
  /-- Modulus at each security parameter. -/
  q : ℕ → ℕ
  /-- Infinity-norm bound on solution coordinates. -/
  β : ℕ → ℕ
  /-- Every modulus is nonzero. -/
  hq : ∀ security, NeZero (q security)

attribute [instance] GeneralSISParams.hq

/-- Parameter family for prime-modulus SIS. Every prime-modulus parameter family projects to
`GeneralSISParams` via `SISParams.toGeneralSISParams`. -/
structure SISParams where
  /-- Number of rows of the public matrix. -/
  n : ℕ → ℕ
  /-- Number of columns of the public matrix. -/
  m : ℕ → ℕ
  /-- Prime modulus at each security parameter. -/
  q : ℕ → ℕ
  /-- Infinity-norm bound on solution coordinates. -/
  β : ℕ → ℕ
  /-- Every modulus is prime. -/
  hq_prime : ∀ security, Fact (Nat.Prime (q security))

attribute [instance] SISParams.hq_prime

/-- Project prime-modulus SIS parameters to general-modulus SIS parameters, forgetting primality
while retaining `[NeZero (q security)]`. -/
def SISParams.toGeneralSISParams (P : SISParams) : GeneralSISParams where
  n := P.n
  m := P.m
  q := P.q
  β := P.β
  hq security := ⟨(P.hq_prime security).out.ne_zero⟩

/-- Power-of-two moduli `q = 2 ^ w` form a `GeneralSISParams` family for every width function
`w : ℕ → ℕ`. -/
def GeneralSISParams.ofPowerOfTwo (n m w β : ℕ → ℕ) : GeneralSISParams where
  n := n
  m := m
  q security := 2 ^ w security
  β := β
  hq _ := inferInstance

namespace GeneralSIS

/-- A residue vector `z : ι → ZMod q` has centered representatives bounded by `β` in `ℓ_∞` norm
when `|(z i).valMinAbs| ≤ β` for every coordinate `i`. -/
def inInfNormBound {q : ℕ} {ι : Type*} (β : ℕ) (z : ι → ZMod q) : Prop :=
  ∀ i, |(z i).valMinAbs| ≤ β

instance {q : ℕ} {ι : Type*} [Fintype ι] (β : ℕ) (z : ι → ZMod q) :
    Decidable (inInfNormBound β z) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A residue vector `z : ι → ZMod q` is a short solution for `A` when it is nonzero, its
centered representatives lie in `[-β, β]`, and `A *ᵥ z = 0`. -/
def isSISChallenge {q : ℕ} {ρ ι : Type*} [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ZMod q) : Prop :=
  z ≠ 0 ∧ inInfNormBound β z ∧ A *ᵥ z = 0

instance {q : ℕ} {ρ ι : Type*} [Fintype ρ] [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ZMod q) : Decidable (isSISChallenge A β z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Lift a residue vector `z : ι → ZMod q` to its centered integer representatives in
`(-q/2, q/2]`. -/
def liftCentered {q : ℕ} {ι : Type*} (z : ι → ZMod q) : ι → ℤ :=
  fun i => (z i).valMinAbs

/-- Reducing the centered integer lift modulo `q` recovers the original residue vector. -/
@[simp] theorem intCast_comp_liftCentered {q : ℕ} {ι : Type*} (z : ι → ZMod q) :
    (Int.cast ∘ liftCentered z : ι → ZMod q) = z := by
  funext i
  exact ZMod.coe_valMinAbs (z i)

/-- The centered integer lift is nonzero if and only if the residue vector is nonzero. -/
@[simp] theorem liftCentered_ne_zero_iff {q : ℕ} {ι : Type*} (z : ι → ZMod q) :
    liftCentered z ≠ 0 ↔ z ≠ 0 := by
  refine not_iff_not.mpr ⟨fun h => ?_, fun h => ?_⟩
  · rw [← intCast_comp_liftCentered z, h]
    exact funext fun _ => Int.cast_zero
  · subst h
    funext i
    exact ZMod.valMinAbs_zero q

/-- A residue vector satisfies `isSISChallenge` if and only if its centered integer lift satisfies
`SIS.IsSolution`. -/
theorem isSISChallenge_iff_isSolution {q : ℕ} {ρ ι : Type*} [Fintype ι]
    (A : Matrix ρ ι (ZMod q)) (β : ℕ) (z : ι → ZMod q) :
    isSISChallenge A β z ↔ SIS.IsSolution A β (liftCentered z) := by
  simp only [isSISChallenge, SIS.IsSolution, inInfNormBound, liftCentered_ne_zero_iff,
    intCast_comp_liftCentered]
  rfl

/-- Row-major framed binary encoding of a matrix over `ZMod q`, encoding each entry's canonical
representative in `[0, q)` with `encNat`. -/
def encodeMatrix {rows cols q : ℕ} (A : Matrix (Fin rows) (Fin cols) (ZMod q)) : List Bool :=
  encList (encList encNat) (List.ofFn fun i => List.ofFn fun j => (A i j).val)

/-- Encode an integer vector `Fin m → ℤ` as a framed list of binary sign-magnitude words. -/
def encodeVec {m : ℕ} (z : Fin m → ℤ) : List Bool :=
  encList encIntBin (List.ofFn z)

/-- Decode a word as an integer vector `Fin m → ℤ` by reading framed binary sign-magnitude
integers, padding missing coordinates with `0` and ignoring excess entries. -/
def decodeVec (m : ℕ) (word : List Bool) : Fin m → ℤ :=
  let coords := (frames word).map decodeIntBin
  fun i => coords.getD i.val 0

/-- Decoding the empty word returns the zero integer vector. -/
@[simp] theorem decodeVec_nil (m : ℕ) : decodeVec m [] = 0 := by
  funext i
  simp [decodeVec]

/-- Every canonical encoded integer vector decodes to itself. -/
@[simp] theorem decodeVec_encodeVec {m : ℕ} (z : Fin m → ℤ) :
    decodeVec m (encodeVec z) = z := by
  funext i
  simp only [decodeVec, encodeVec, frames_encList, List.map_map, Function.comp_def,
    decodeIntBin_encIntBin, List.getD_eq_getElem?_getD]
  simp

/-- The general-modulus SIS experiment: draw a uniform `A ∈ ℤ_q^{n×m}`, give the adversary the
unary security parameter and the framed binary encoding of `A`, and accept when its answer
decodes to a short integer solution with bound `β`. -/
noncomputable def sisGame (P : GeneralSISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) : Game := do
  let A ← PMF.uniformOfFintype
    (Matrix (Fin (P.n security)) (Fin (P.m security)) (ZMod (P.q security)))
  let word ← ProbComp.eval (adversary security (encodeMatrix A))
  return decide (SIS.IsSolution A (P.β security) (decodeVec (P.m security) word))

/-- The general-modulus SIS hardness hypothesis for parameter family `P`: every uniform strict
PPT adversary finds a short integer solution with negligible probability. -/
def Hard (P : GeneralSISParams) : Prop :=
  ∀ adversary : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits adversary →
    Negligible fun security => Game.succProbability (sisGame P adversary security)

/-- The prime-modulus SIS game is the general-modulus SIS game on `P.toGeneralSISParams`. -/
noncomputable abbrev _root_.Cslib.Crypto.SISParams.sisGame (P : SISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) : Game :=
  GeneralSIS.sisGame P.toGeneralSISParams adversary security

/-- Prime-modulus SIS hardness is general-modulus SIS hardness on `P.toGeneralSISParams`. -/
abbrev _root_.Cslib.Crypto.SISParams.Hard (P : SISParams) : Prop :=
  GeneralSIS.Hard P.toGeneralSISParams

/-- Projecting `SISParams` to `GeneralSISParams` preserves `sisGame` identically. -/
@[simp] theorem sisGame_toGeneralSISParams (P : SISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) :
    GeneralSIS.sisGame P.toGeneralSISParams adversary security = P.sisGame adversary security :=
  rfl

/-- Projecting `SISParams` to `GeneralSISParams` preserves the hardness predicate identically. -/
@[simp] theorem hard_toGeneralSISParams_iff (P : SISParams) :
    GeneralSIS.Hard P.toGeneralSISParams ↔ P.Hard :=
  Iff.rfl

/-- Ajtai's linear hash function `f_A(x) = A *ᵥ (Int.cast ∘ x) mod q` on integer vectors
([Ajtai1996]). Requires no primality assumption on `q`. -/
def ajtaiHashEval {n m q : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (x : Fin m → ℤ) :
    Fin n → ZMod q :=
  A *ᵥ (Int.cast ∘ x)

/-- Extract a short integer kernel vector from a colliding pair `(x, y)` by taking their
difference `x - y`. -/
def extractSISVector {m : ℕ} (x y : Fin m → ℤ) : Fin m → ℤ :=
  x - y

/-- Subtraction of distinct inputs gives a nonzero vector. -/
theorem extractSISVector_ne_zero {m : ℕ} {x y : Fin m → ℤ} (hxy : x ≠ y) :
    extractSISVector x y ≠ 0 :=
  sub_ne_zero.mpr hxy

/-- If `x` and `y` collide under `ajtaiHashEval A`, their difference lies in the kernel of `A`
modulo `q` for any modulus `q`. -/
theorem ajtaiHashEval_extractSISVector {n m q : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q))
    {x y : Fin m → ℤ} (hcoll : ajtaiHashEval A x = ajtaiHashEval A y) :
    A *ᵥ (Int.cast ∘ extractSISVector x y) = 0 := by
  have hcast : (Int.cast ∘ extractSISVector x y : Fin m → ZMod q) =
      (Int.cast ∘ x) - (Int.cast ∘ y) :=
    funext fun i => Int.cast_sub (x i) (y i)
  rw [hcast, Matrix.mulVec_sub, sub_eq_zero]
  exact hcoll

/-- **Collision extraction from `[0, β]^m`**: any distinct `x, y ∈ [0, β]^m` with
`ajtaiHashEval A x = ajtaiHashEval A y` yield a short integer solution `x - y` with bound `β`,
for any modulus `q`. -/
theorem isSolution_extractSISVector_of_Icc {n m q β : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q))
    {x y : Fin m → ℤ} (hxy : x ≠ y)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ β) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ β)
    (hcoll : ajtaiHashEval A x = ajtaiHashEval A y) :
    SIS.IsSolution A β (extractSISVector x y) := by
  refine ⟨extractSISVector_ne_zero hxy, fun i => ?_, ajtaiHashEval_extractSISVector A hcoll⟩
  have hxi := hx i
  have hyi := hy i
  simp only [extractSISVector, Pi.sub_apply, abs_le]
  omega

/-- **Collision extraction from `[-β, β]^m`**: any distinct `x, y ∈ [-β, β]^m` with
`ajtaiHashEval A x = ajtaiHashEval A y` yield a short integer solution `x - y` with bound
`2 * β`, for any modulus `q`. -/
theorem isSolution_extractSISVector_of_abs_le {n m q β : ℕ}
    (A : Matrix (Fin n) (Fin m) (ZMod q)) {x y : Fin m → ℤ} (hxy : x ≠ y)
    (hx : ∀ i, |x i| ≤ β) (hy : ∀ i, |y i| ≤ β)
    (hcoll : ajtaiHashEval A x = ajtaiHashEval A y) :
    SIS.IsSolution A (2 * β) (extractSISVector x y) := by
  refine ⟨extractSISVector_ne_zero hxy, fun i => ?_, ajtaiHashEval_extractSISVector A hcoll⟩
  have hxi := abs_le.mp (hx i)
  have hyi := abs_le.mp (hy i)
  simp only [extractSISVector, Pi.sub_apply, Nat.cast_mul, Nat.cast_ofNat, abs_le]
  omega

/-- A pair `(x, y)` of integer vectors in `[0, β]^m` is an Ajtai hash collision for `A` when
`x ≠ y`, both lie in `[0, β]^m`, and `ajtaiHashEval A x = ajtaiHashEval A y`. -/
def isAjtaiCollision {n m q : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ)
    (x y : Fin m → ℤ) : Prop :=
  x ≠ y ∧ (∀ i, 0 ≤ x i ∧ x i ≤ β) ∧ (∀ i, 0 ≤ y i ∧ y i ≤ β) ∧
    ajtaiHashEval A x = ajtaiHashEval A y

instance {n m q : ℕ} (A : Matrix (Fin n) (Fin m) (ZMod q)) (β : ℕ) (x y : Fin m → ℤ) :
    Decidable (isAjtaiCollision A β x y) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Every valid Ajtai collision in `[0, β]^m` extracts to a short integer solution with bound
`β`. -/
theorem isSolution_of_isAjtaiCollision {n m q β : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod q)}
    {x y : Fin m → ℤ} (h : isAjtaiCollision A β x y) :
    SIS.IsSolution A β (extractSISVector x y) :=
  isSolution_extractSISVector_of_Icc A h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The Ajtai collision experiment: draw a uniform `A ∈ ℤ_q^{n×m}`, run `finder` on the encoded
matrix, decode the output pair `(x, y)` of `m`-vectors, and accept when `(x, y)` is a valid
Ajtai collision in `[0, β]^m`. -/
noncomputable def ajtaiCollisionGame (P : GeneralSISParams)
    (finder : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) : Game := do
  let A ← PMF.uniformOfFintype
    (Matrix (Fin (P.n security)) (Fin (P.m security)) (ZMod (P.q security)))
  let word ← ProbComp.eval (finder security (encodeMatrix A))
  let x := decodeVec (P.m security) (unframe word)
  let y := decodeVec (P.m security) (dropFrame word)
  return decide (isAjtaiCollision A (P.β security) x y)

/-- Postprocess a candidate collision word into a candidate SIS solution word by decoding both
halves and encoding their difference. -/
def extractSISWord (m : ℕ) (word : List Bool) : List Bool :=
  encodeVec (extractSISVector (decodeVec m (unframe word)) (decodeVec m (dropFrame word)))

/-- Monotonicity of `true`-probability across a common `PMF.bind` prefix. -/
private theorem bind_true_le {α : Type*} (d : PMF α) (f g : α → Game)
    (h : ∀ a, f a true ≤ g a true) :
    (d.bind f) true ≤ (d.bind g) true := by
  rw [PMF.bind_apply, PMF.bind_apply]
  exact tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (h a) zero_le

/-- Postprocessing any collision finder's output with `extractSISWord` yields a `GeneralSIS`
adversary whose success probability is at least the collision-finding probability, for any
nonzero modulus `q`. -/
theorem succProbability_ajtaiCollisionGame_le (P : GeneralSISParams)
    (finder : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) :
    Game.succProbability (ajtaiCollisionGame P finder security) ≤
      Game.succProbability
        (sisGame P (fun s w => extractSISWord (P.m s) <$> finder s w) security) := by
  unfold ajtaiCollisionGame sisGame
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ProbComp.eval_map, PMF.bind_map,
    Function.comp_def, extractSISWord, decodeVec_encodeVec]
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
    (bind_true_le _ _ _ fun A => bind_true_le _ _ _ fun word => ?_)
  by_cases h : isAjtaiCollision A (P.β security)
      (decodeVec (P.m security) (unframe word))
      (decodeVec (P.m security) (dropFrame word))
  · simp [h, isSolution_of_isAjtaiCollision h]
  · simp [h]

end GeneralSIS

/-! ### Part 2: Negacyclic Polynomial Ring `R[X] / (X^n + 1)` -/

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

/-! ### Part 3: Module-SIS, Ring-SIS and Structured-to-Unstructured Expansion -/

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

/-- The unstructured `GeneralSISParams` with `d * n` rows and `k * n` columns associated to
`M : ModuleSISParams` under `expandModuleMatrix`. -/
def ModuleSISParams.toGeneralSISParams (M : ModuleSISParams) : GeneralSISParams where
  n security := M.d security * M.n security
  m security := M.k security * M.n security
  q := M.q
  β := M.β
  hq := M.hq

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
def isModuleSISChallenge {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (β : ℕ)
    (z : Fin k → Fin n → ZMod q) : Prop :=
  z ≠ 0 ∧ inInfNormBound β z ∧ moduleSISMap A z = 0

instance {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (β : ℕ)
    (z : Fin k → Fin n → ZMod q) : Decidable (isModuleSISChallenge A β z) :=
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
    GeneralSIS.inInfNormBound β (flattenPolyVec z) ↔ inInfNormBound β z :=
  ⟨fun h j s => by simpa [GeneralSIS.inInfNormBound] using h (finProdFinEquiv (j, s)),
   fun h c => by
     obtain ⟨⟨j, s⟩, rfl⟩ := finProdFinEquiv.surjective c
     simpa [GeneralSIS.inInfNormBound] using h j s⟩

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
`z` satisfies `isModuleSISChallenge A β z` if and only if `flattenPolyVec z` satisfies
`GeneralSIS.isSISChallenge (expandModuleMatrix A) β (flattenPolyVec z)`. -/
theorem isModuleSISChallenge_iff_isSISChallenge {d k n q β : ℕ}
    (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) (z : Fin k → Fin n → ZMod q) :
    isModuleSISChallenge A β z ↔
      GeneralSIS.isSISChallenge (expandModuleMatrix A) β (flattenPolyVec z) := by
  simp only [isModuleSISChallenge, GeneralSIS.isSISChallenge, flattenPolyVec_ne_zero_iff,
    inInfNormBound_flattenPolyVec_iff, expandModuleMatrix_mulVec_eq_zero_iff]

/-- Encode a module matrix `A` over `ℤ_q[X] / (X^n + 1)` by encoding its expanded block matrix
`expandModuleMatrix A`. -/
def encodeMatrix {d k n q : ℕ} (A : Matrix (Fin d) (Fin k) (Fin n → ZMod q)) : List Bool :=
  GeneralSIS.encodeMatrix (expandModuleMatrix A)

/-- Encode an integer polynomial vector `z : Fin k → Fin n → ℤ` by encoding `flattenPolyVec z`. -/
def encodeVec {k n : ℕ} (z : Fin k → Fin n → ℤ) : List Bool :=
  GeneralSIS.encodeVec (flattenPolyVec z)

/-- Decode a word as an integer polynomial vector `Fin k → Fin n → ℤ` by decoding `k * n`
signed integers and unflattening. -/
def decodeVec (k n : ℕ) (word : List Bool) : Fin k → Fin n → ℤ :=
  unflattenPolyVec (GeneralSIS.decodeVec (k * n) word)

/-- Every canonical encoded integer polynomial vector decodes to itself. -/
@[simp] theorem decodeVec_encodeVec {k n : ℕ} (z : Fin k → Fin n → ℤ) :
    decodeVec k n (encodeVec z) = z := by
  simp [decodeVec, encodeVec]

/-- The Module-SIS experiment: draw a uniform `d × k` module matrix `A` over `ℤ_q[X] / (X^n + 1)`,
give the adversary the unary security parameter and the encoded matrix, and accept when its
answer decodes to a `ModuleSIS.IsSolution` with bound `β`. -/
noncomputable def moduleSISGame (M : ModuleSISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) : Game := do
  let A ← PMF.uniformOfFintype
    (Matrix (Fin (M.d security)) (Fin (M.k security)) (Fin (M.n security) → ZMod (M.q security)))
  let word ← ProbComp.eval (adversary security (encodeMatrix A))
  return decide (IsSolution A (M.β security) (decodeVec (M.k security) (M.n security) word))

/-- The structured `GeneralSIS` experiment induced by `M : ModuleSISParams`: draw a uniform
module matrix `A`, expand it to `expandModuleMatrix A`, and check the unstructured
`SIS.IsSolution` predicate on `expandModuleMatrix A`. -/
noncomputable def structuredSISGame (M : ModuleSISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) : Game := do
  let A ← PMF.uniformOfFintype
    (Matrix (Fin (M.d security)) (Fin (M.k security)) (Fin (M.n security) → ZMod (M.q security)))
  let word ← ProbComp.eval (adversary security (GeneralSIS.encodeMatrix (expandModuleMatrix A)))
  return decide
    (SIS.IsSolution (expandModuleMatrix A) (M.β security)
      (GeneralSIS.decodeVec (M.k security * M.n security) word))

/-- The structured `GeneralSIS` experiment and `moduleSISGame` are identical as `PMF Bool`
distributions for every adversary and security parameter. -/
@[simp] theorem structuredSISGame_eq_moduleSISGame (M : ModuleSISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) :
    structuredSISGame M adversary security = moduleSISGame M adversary security := by
  unfold structuredSISGame moduleSISGame encodeMatrix decodeVec
  congr 1 with A : 1
  congr 1 with word : 1
  have h := isSolution_expandModuleMatrix_iff (β := M.β security) A
    (unflattenPolyVec (GeneralSIS.decodeVec (M.k security * M.n security) word))
  rw [flattenPolyVec_unflattenPolyVec] at h
  simp only [h]

/-- Every adversary achieves the same success probability in `structuredSISGame` and
`moduleSISGame`. -/
theorem succProbability_structuredSISGame (M : ModuleSISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) :
    Game.succProbability (structuredSISGame M adversary security) =
      Game.succProbability (moduleSISGame M adversary security) := by
  rw [structuredSISGame_eq_moduleSISGame]

/-- The Module-SIS hardness hypothesis for parameter family `M`: every uniform strict PPT
adversary wins `moduleSISGame` with negligible probability. -/
def Hard (M : ModuleSISParams) : Prop :=
  ∀ adversary : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits adversary →
    Negligible fun security => Game.succProbability (moduleSISGame M adversary security)

/-- **Structured-to-unstructured reduction**: `ModuleSIS.Hard M` holds if and only if every
uniform strict PPT adversary has negligible success probability in `structuredSISGame M`. -/
theorem hard_of_structuredGeneralSIS (M : ModuleSISParams)
    (h : ∀ adversary : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits adversary →
      Negligible fun security => Game.succProbability (structuredSISGame M adversary security)) :
    Hard M := by
  intro adversary hadv
  simpa using h adversary hadv

end ModuleSIS

namespace RingSIS

/-- The Ring-SIS experiment is the rank-`1` specialization of `ModuleSIS.moduleSISGame`. -/
noncomputable abbrev ringSISGame (R : RingSISParams)
    (adversary : ℕ → List Bool → ProbComp (List Bool)) (security : ℕ) : Game :=
  ModuleSIS.moduleSISGame R.toModuleSISParams adversary security

/-- The Ring-SIS hardness hypothesis is `ModuleSIS.Hard` on `R.toModuleSISParams`. -/
abbrev Hard (R : RingSISParams) : Prop :=
  ModuleSIS.Hard R.toModuleSISParams

end RingSIS

/-! ### Part 4: Module-LWE and Structured Expansion -/

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
