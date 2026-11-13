/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.ValMinAbs

/-!
# The short integer solution problem

A short integer solution ([Ajtai1996]) for a matrix `A ∈ ℤ_q^{n×m}` and a bound `β` is a nonzero
integer vector `z` with every coordinate in `[-β, β]` and `A z ≡ 0 (mod q)` (`SIS.IsSolution`).
It is a predicate for any modulus and index types, so that protocols can extract solutions for
matrices such as `[A | T]`.

`sisExperiment q β S` is the SIS experiment for one modulus, dimension and bound: the challenger
draws a uniform `A ∈ ℤ_q^{n×m}`, and the solver `S` wins when it returns a short integer solution
for `A`. The solver receives and returns typed values; there are no encodings or security
parameter. The experiment tests the integer answer itself and assumes no relation between `β` and
`q`. When `q ≤ β` and `m ≠ 0`, the vector with one coordinate `q` and all others `0` is a short
solution for every matrix, so for such parameters winning does not depend on the matrix.

The asymptotic hypothesis `SIS P` fixes a parameter family `P : SISParams` (dimensions, nonzero
modulus and bound for each security parameter) and asserts that every solver that is uniform
strict PPT on encodings (`SISParams.Solver.IsPPT`) has negligible advantage. A solver machine reads
`SISParams.encInput`, the unary security parameter followed by the row-major framed residues of
`A` (`SIS.encodeMatrix`), and writes the framed binary sign-magnitude coordinates of its answer
(`SIS.encodeVec`).

`SIS` is an explicit computational hardness hypothesis against uniform classical strict PPT
programs, not a theorem. It asserts hardness for no particular parameters, and no worst-case
lattice reduction is formalized.

## Main definitions

* `Cslib.Crypto.SIS.IsSolution`: short nonzero integer kernel vectors modulo `q`.
* `Cslib.Crypto.SIS.inInfNormBound`, `Cslib.Crypto.SIS.IsResidueSolution`,
  `Cslib.Crypto.SIS.liftCentered`: residue-level `ℓ_∞` bound, the residue form of a short solution
  and the centered integer lift.
* `Cslib.Crypto.SIS.encodeMatrix`, `Cslib.Crypto.SIS.encodeVec`: the matrix and integer-vector
  encodings read and written by machines.
* `Cslib.Crypto.sisExperiment`, `Cslib.Crypto.sisAdvantage`: the fixed-instance SIS experiment and
  its success probability.
* `Cslib.Crypto.SISParams`, `Cslib.Crypto.SISParams.Input`, `Cslib.Crypto.SISParams.encInput`,
  `Cslib.Crypto.SISParams.Solver`, `Cslib.Crypto.SISParams.Solver.IsPPT`: parameter families,
  solver inputs and their encoding, and efficient solvers.
* `Cslib.Crypto.SIS`: the SIS hardness hypothesis for a parameter family.

## Main results

* `Cslib.Crypto.SIS.isResidueSolution_iff_isSolution`: a residue vector is a short solution exactly
  when its centered integer lift is one.
* `Cslib.Crypto.SIS.encodeMatrix_injective`, `Cslib.Crypto.SIS.encodeVec_injective`: the encodings
  are injective (for matrices, when `q ≠ 0`).
* `Cslib.Crypto.SISParams.encInput_apply`: the solver input layout.

## References

* [M. Ajtai, *Generating Hard Instances of Lattice Problems*][Ajtai1996]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix NNReal

namespace SIS

/-- `z` is a short integer solution for `A`: it is nonzero, every coordinate lies in
`[-β, β]`, and `A z ≡ 0 (mod q)`. -/
def IsSolution {q : ℕ} {ρ ι : Type*} [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ℤ) : Prop :=
  z ≠ 0 ∧ (∀ i, |z i| ≤ β) ∧ A *ᵥ (Int.cast ∘ z) = 0

instance {q : ℕ} {ρ ι : Type*} [Fintype ρ] [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ℤ) : Decidable (IsSolution A β z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Residue vectors -/

/-- A residue vector `z : ι → ZMod q` has centered representatives bounded by `β` in `ℓ_∞` norm
when `|(z i).valMinAbs| ≤ β` for every coordinate `i`. -/
def inInfNormBound {q : ℕ} {ι : Type*} (β : ℕ) (z : ι → ZMod q) : Prop :=
  ∀ i, |(z i).valMinAbs| ≤ β

instance {q : ℕ} {ι : Type*} [Fintype ι] (β : ℕ) (z : ι → ZMod q) :
    Decidable (inInfNormBound β z) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- A residue vector `z : ι → ZMod q` is a short solution for `A` when it is nonzero, its
centered representatives lie in `[-β, β]`, and `A *ᵥ z = 0`. -/
def IsResidueSolution {q : ℕ} {ρ ι : Type*} [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ZMod q) : Prop :=
  z ≠ 0 ∧ inInfNormBound β z ∧ A *ᵥ z = 0

instance {q : ℕ} {ρ ι : Type*} [Fintype ρ] [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ZMod q) : Decidable (IsResidueSolution A β z) :=
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

/-- A residue vector is a short solution if and only if its centered integer lift is a short
integer solution. -/
theorem isResidueSolution_iff_isSolution {q : ℕ} {ρ ι : Type*} [Fintype ι]
    (A : Matrix ρ ι (ZMod q)) (β : ℕ) (z : ι → ZMod q) :
    IsResidueSolution A β z ↔ IsSolution A β (liftCentered z) := by
  simp only [IsResidueSolution, IsSolution, inInfNormBound, liftCentered_ne_zero_iff,
    intCast_comp_liftCentered]
  rfl

/-! ### Encodings -/

/-- Row-major framed binary encoding of a matrix over `ZMod q`, encoding each entry's canonical
representative in `[0, q)` with `encNat`. -/
def encodeMatrix {rows cols q : ℕ} (A : Matrix (Fin rows) (Fin cols) (ZMod q)) : List Bool :=
  encList (encList encNat) (List.ofFn fun i => List.ofFn fun j => (A i j).val)

/-- Matrices of fixed shape over `ZMod q` are determined by their encodings when `q ≠ 0`. -/
theorem encodeMatrix_injective {rows cols q : ℕ} [NeZero q] :
    Function.Injective (encodeMatrix (rows := rows) (cols := cols) (q := q)) := by
  intro A B h
  have hrows := List.ofFn_injective ((encList (encList encNat)).injective h)
  ext i j
  exact ZMod.val_injective q (congrFun (List.ofFn_injective (congrFun hrows i)) j)

/-- Encode an integer vector `Fin m → ℤ` as a framed list of binary sign-magnitude words. -/
def encodeVec {m : ℕ} (z : Fin m → ℤ) : List Bool :=
  encList encIntBin (List.ofFn z)

/-- Integer vectors of fixed length are determined by their encodings. -/
theorem encodeVec_injective {m : ℕ} : Function.Injective (encodeVec (m := m)) :=
  fun _ _ h => List.ofFn_injective ((encList encIntBin).injective h)

end SIS

/-! ### The fixed-instance experiment -/

section Experiment

variable (q : ℕ) [NeZero q] {n m : ℕ}

/-- The SIS experiment ([Ajtai1996]) for modulus `q`, dimensions `n × m` and bound `β`: the
challenger draws a uniform `A ∈ ℤ_q^{n×m}`; the solver wins when it returns a short integer
solution for `A`. -/
noncomputable def sisExperiment (β : ℕ)
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) : ProbComp Bool := do
  let A ← ProbComp.uniform (Matrix (Fin n) (Fin m) (ZMod q))
  let z ← S A
  return decide (SIS.IsSolution A β z)

/-- The SIS advantage of `S`: its success probability in `sisExperiment`. -/
noncomputable def sisAdvantage (β : ℕ)
    (S : Matrix (Fin n) (Fin m) (ZMod q) → ProbComp (Fin m → ℤ)) : ℝ≥0 :=
  Game.succProbability (ProbComp.eval (sisExperiment q β S))

end Experiment

/-! ### Parameter families -/

/-- Parameter family for the short integer solution problem over an arbitrary nonzero modulus
schedule `q`, including primes, powers of two and other composites. -/
structure SISParams where
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

attribute [instance] SISParams.hq

namespace SISParams

variable (P : SISParams)

/-- The input of a SIS solver for the family `P`: the security parameter and a public matrix of
the dimensions and modulus that `P` assigns to it. -/
structure Input where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public matrix. -/
  matrix : Matrix (Fin (P.n secParam)) (Fin (P.m secParam)) (ZMod (P.q secParam))

variable {P}

/-- The words a machine reads for a SIS input: the security parameter and the encoded matrix. -/
def Input.words (x : P.Input) : ℕ × List Bool :=
  (x.secParam, SIS.encodeMatrix x.matrix)

/-- A SIS input is determined by its words. -/
theorem Input.words_injective : Function.Injective (Input.words (P := P)) := by
  rintro ⟨κ, A⟩ ⟨κ', B⟩ h
  simp only [Input.words, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  rw [SIS.encodeMatrix_injective h]

variable (P)

/-- The encoding of a SIS input: the framed unary security parameter followed by the encoded
matrix (`encInput_apply`). -/
def encInput : P.Input ↪ List Bool :=
  (⟨Input.words, Input.words_injective⟩ : P.Input ↪ _).trans (encPair encUnary encBits)

/-- The SIS input layout. -/
theorem encInput_apply (x : P.Input) :
    P.encInput x = frame (encUnary x.secParam) ++ SIS.encodeMatrix x.matrix := by
  simp [encInput, Input.words, encPair, encBits]

/-- A SIS solver for the family `P`: given the security parameter `κ` and a matrix of the
dimensions and modulus of `P` at `κ`, it returns an integer vector. `Solver.IsPPT` states its
efficiency on encodings. -/
abbrev Solver : Type :=
  (κ : ℕ) → Matrix (Fin (P.n κ)) (Fin (P.m κ)) (ZMod (P.q κ)) → ProbComp (Fin (P.m κ) → ℤ)

variable {P} in
/-- A SIS solver is PPT when one uniform strict PPT machine reads `encInput` and writes the
encoding of the solver's answer. -/
def Solver.IsPPT (S : P.Solver) : Prop :=
  IsPPTOn P.encInput encBits fun x => SIS.encodeVec <$> S x.secParam x.matrix

end SISParams

/-- The SIS hardness hypothesis for a parameter family `P`: every PPT solver has negligible
advantage in `sisExperiment` at the parameters `P` assigns to each security parameter. This is a
hypothesis against classical adversaries, not a theorem of hardness. -/
def SIS (P : SISParams) : Prop :=
  ∀ S : P.Solver, S.IsPPT → Negligible fun κ => sisAdvantage (P.q κ) (P.β κ) (S κ)

end Cslib.Crypto
