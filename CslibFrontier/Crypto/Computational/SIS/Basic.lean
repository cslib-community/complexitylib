/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Foundations.Data.Matrix.Binary
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.ValMinAbs
import CslibFrontier.Probability.PMF

/-!
# The short integer solution problem with power-of-two moduli

A short integer solution ([Ajtai1996]) for a matrix `A ∈ ℤ_q^{n×ι}` and a bound `β` is a nonzero
integer vector `z` with every coordinate in `[-β, β]` and `A z ≡ 0 (mod q)`
(`SIS.IsSolution`). It is a predicate for any modulus and index types, so that protocols can
extract solutions for matrices such as `[A | T]`.

The SIS experiment draws a uniform `A ∈ ℤ_q^{n×m}` with `q = 2 ^ w`, and gives a program the
unary security parameter and the row-major binary word of `A`, as for `DecisionLWE`. The program
answers with `m` residues of `w` bits each, read through their centered representatives in
`(-q/2, q/2]` (`SIS.decode`), and wins when these form a short integer solution. `SIS n m w β`
asserts that every uniform strict PPT program wins with negligible probability.

The centered reading loses nothing when `2 β < q`: every short integer solution is decoded from
the word of its own residues (`SIS.decode_toBinary`). For positive width `w > 0`, bounds at
least `2 ^ (w - 1)` make the experiment easy once `m > n`: every centered nonzero kernel vector
modulo `q` then qualifies, and `2 ^ (w - 1)` times a nonzero kernel vector modulo `2` is one.
At width zero the decoder always returns the zero integer vector, so the experiment always
rejects, even when nonzero integer SIS solutions exist modulo `1`.

`SIS` is an explicit computational hardness hypothesis against uniform classical strict PPT
programs, not a theorem. It asserts hardness for no particular parameters, and no worst-case
lattice reduction is formalized. Moduli that are not powers of two and module SIS need other
encodings and are not covered.

## Main definitions

* `Cslib.Crypto.SIS.IsSolution`: short nonzero integer kernel vectors modulo `q`.
* `Cslib.Crypto.SIS.decode`: read a word as centered residues.
* `Cslib.Crypto.SIS.game`: the SIS experiment.
* `Cslib.Crypto.SIS`: the SIS hardness hypothesis for the given parameter functions.

## Main results

* `Cslib.Crypto.SIS.decode_toBinary`: when `2 β < q`, the word of a vector's residues decodes
  to the vector.

## References

* [M. Ajtai, *Generating Hard Instances of Lattice Problems*][Ajtai1996]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

namespace SIS

/-- `z` is a short integer solution for `A`: it is nonzero, every coordinate lies in
`[-β, β]`, and `A z ≡ 0 (mod q)`. -/
def IsSolution {q : ℕ} {ρ ι : Type*} [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ℤ) : Prop :=
  z ≠ 0 ∧ (∀ i, |z i| ≤ β) ∧ A *ᵥ (Int.cast ∘ z) = 0

instance {q : ℕ} {ρ ι : Type*} [Fintype ρ] [Fintype ι] (A : Matrix ρ ι (ZMod q)) (β : ℕ)
    (z : ι → ℤ) : Decidable (IsSolution A β z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Read a word as `m` residues modulo `2 ^ w`, of `w` low-order-first bits each, lifted to their
centered representatives. Missing bits are `false`, and excess bits are ignored. -/
def decode (m w : ℕ) (word : List Bool) : Fin m → ℤ :=
  fun i => (Matrix.ofBinary 1 m w word 0 i).valMinAbs

/-- When `2 β < 2 ^ w`, a vector with coordinates in `[-β, β]` is decoded from the word of its
residues. In particular the SIS experiment loses no integer solution for such bounds. -/
theorem decode_toBinary {m w β : ℕ} (hβ : 2 * β < 2 ^ w) {z : Fin m → ℤ}
    (hz : ∀ i, |z i| ≤ β) :
    decode m w (Matrix.toBinary (Matrix.of fun (_ : Fin 1) i => (z i : ZMod (2 ^ w)))) = z := by
  funext i
  rw [decode, Matrix.ofBinary_toBinary, Matrix.of_apply, ZMod.valMinAbs_spec]
  have hq : (2 * β : ℤ) < ((2 ^ w : ℕ) : ℤ) := by exact_mod_cast hβ
  have hzi := abs_le.mp (hz i)
  exact ⟨rfl, by omega, by omega⟩

/-- The SIS experiment: draw a uniform `A ∈ ℤ_q^{n×m}` with `q = 2 ^ w`, give the adversary the
unary security parameter and the binary word of `A`, and accept when its answer decodes to a
short integer solution with bound `β`. -/
noncomputable def game (n m w β : ℕ → ℕ) (adversary : ℕ → List Bool → ProbComp (List Bool))
    (security : ℕ) : Game := do
  let A ← PMF.uniformOfFintype
    (Matrix (Fin (n security)) (Fin (m security)) (ZMod (2 ^ w security)))
  let word ← ProbComp.eval (adversary security (Matrix.toBinary A))
  return decide (IsSolution A (β security) (decode (m security) (w security) word))

end SIS

/-- The SIS hardness hypothesis for the exact dimension, number of columns, binary modulus
width and bound: every uniform strict PPT program, given the unary security parameter and the
encoded uniform matrix, finds a short integer solution with negligible probability. This is a
hypothesis against classical adversaries, not a theorem of hardness. -/
def SIS (n m w β : ℕ → ℕ) : Prop :=
  ∀ adversary : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits adversary →
    Negligible fun security => Game.succProbability (SIS.game n m w β adversary security)

end Cslib.Crypto
