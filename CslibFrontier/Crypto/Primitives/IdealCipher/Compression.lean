/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.IdealCipher
public import CslibFrontier.Crypto.Primitives.Hash.BlockCipherCompression

/-!
# Collision Resistance in the Ideal Cipher Model

We define the collision resistance game for a compression function built from an ideal cipher.
We formalize Exercise 7.23(a) from Katz-Lindell, showing that `cipherOutput` is not collision
resistant, by providing an explicit adversary that finds a collision with probability 1.

## Main definitions

* `Cslib.IdealCipher.collisionGame`: The collision resistance game in the Ideal Cipher Model.
* `Cslib.IdealCipher.cipherOutputAdversary`: An adversary that finds a collision in `cipherOutput`.

## Main results

* `Cslib.IdealCipher.cipherOutputAdversary_wins`: The adversary wins the collision game with
  probability 1.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1,
  Figure 7.11, Theorem 7.5, Exercises 7.23 and 7.24.
-/

public section

namespace Cslib.IdealCipher

open OracleComp Cslib.Crypto.BlockCipherCompression Cslib.Probability

variable {Key Block : Type} [DecidableEq Key] [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block]

/-- The collision-resistance game for a compression function `H` built from a block cipher.
The adversary has oracle access to the ideal cipher and its inverse, and must output two distinct
inputs that hash to the same value under `H`. -/
@[expose]
noncomputable def collisionGame
    (H : (Key → Equiv.Perm Block) → Key × Block → Block)
    (A : OracleComp (Spec Key Block) ((Key × Block) × (Key × Block))) : PMF Bool :=
  (PMF.pi (fun _ : Key => Cslib.RandomPermutation.complete ([] : Cslib.RandomPermutation.Cache Block))).bind fun E =>
    (interpret lazyEvalPerm A (fun k => E k)).map fun (res, _) =>
      res.1 ≠ res.2 ∧ H E res.1 = H E res.2

/-- An adversary that finds a collision in `cipherOutput` using two inverse queries. -/
@[expose]
def cipherOutputAdversary (k1 k2 : Key) (y : Block) :
    OracleComp (Spec Key Block) ((Key × Block) × (Key × Block)) := do
  let x1 ← query (k1, Cslib.RandomPermutation.PermQuery.inverse y)
  let x2 ← query (k2, Cslib.RandomPermutation.PermQuery.inverse y)
  return ((k1, x1), (k2, x2))

omit [Nonempty Block] in
theorem cipherOutputAdversary_wins {k1 k2 : Key} (hk : k1 ≠ k2) (y : Block) :
    collisionGame (cipherOutput (B := Block)) (cipherOutputAdversary k1 k2 y) = PMF.pure true := by
  unfold collisionGame cipherOutputAdversary lazyEvalPerm
  simp only [interpret_bind, interpret_query, interpret_pure]
  simp [bind, StateT.bind, pure, StateT.pure, Cslib.RandomPermutation.evalPerm, cipherOutput_symm, hk]

end Cslib.IdealCipher
