/-
Copyright (c) 2026 Samuel Schlesinger, real-roots. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, real-roots
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Crypto.Computational.Basic
public import CslibFrontier.Foundations.Data.Matrix.Binary
public import CslibFrontier.Probability.Product
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Notation
import CslibFrontier.Tactic.PPT

/-!
# Search and Decision LWE with prime moduli

The real experiment draws a uniform secret `s`, a uniform matrix `A`, and independent errors
with a specified residue distribution. Its public sample is the binary encoding of
`[A * s + e | A]`. The comparison experiment draws an entirely uniform matrix of the same shape.

`SearchLWE` requires the adversary to find the secret `s` given `[A * s + e | A]`.
`DecisionLWE` requires the adversary to distinguish `[A * s + e | A]` from a uniform matrix.

## Main definitions

* `Cslib.Crypto.PrimeLWE.encMatrix`: binary encoding of `ZMod q` matrices.
* `Cslib.Crypto.PrimeLWE.searchGame`: the search experiment for `ZMod q`.
* `Cslib.Crypto.PrimeLWE.DecisionLWE`: the decision experiment for `ZMod q`.

## References

* [O. Regev, *On lattices, learning with errors, random linear codes, and cryptography*][Regev2009]
* [C. Peikert, *A Decade of Lattice Cryptography*][Peikert2016]
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped _root_.Matrix

namespace PrimeLWE

/-- Encode a `ZMod q` element. -/
def encZMod (q : ℕ) : ZMod q ↪ List Bool :=
  ⟨fun a => encIntBin (ZMod.cast a),
    encIntBin.injective.comp (Function.LeftInverse.injective ZMod.intCast_zmod_cast)⟩

/-- Encode a `ZMod q` vector. -/
def encZModVec (n q : ℕ) : (Fin n → ZMod q) ↪ List Bool :=
  ⟨fun v => encList (encZMod q) (List.ofFn v), by
    intro u v huv
    have hlist := (encList (encZMod q)).injective huv
    funext i
    have hi := congrArg (fun l : List (ZMod q) => l.getD i.val 0) hlist
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
      Option.getD_some] at hi
    exact hi⟩

/-- Encode a matrix over `ZMod q`. -/
def encMatrix (n m q : ℕ) : Matrix (Fin n) (Fin m) (ZMod q) ↪ List Bool :=
  ⟨fun M => encList (encList (encZMod q))
      (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => M i j), by
    intro M N hMN
    have hrows := (encList (encList (encZMod q))).injective hMN
    ext i j
    have hij := congrArg (fun r : List (List (ZMod q)) => (r.getD i.val []).getD j.val 0) hrows
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, j.isLt, ↓reduceDIte,
      Option.getD_some] at hij
    exact hij⟩

/-- The deterministic LWE public matrix `[A * s + e | A]` modulo `q`. -/
def publicMatrix {n m q : ℕ} [Fact (Nat.Prime q)] (A : Matrix (Fin m) (Fin n) (ZMod q))
    (s : Fin n → ZMod q) (e : Fin m → ZMod q) :
    Matrix (Fin m) (Fin (n + 1)) (ZMod q) :=
  fun i => Fin.cons ((A *ᵥ s) i + e i) (A i)

/-- Draw the public matrix `[A * s + e | A]`. -/
noncomputable def publicMatrixLaw (n m q : ℕ) [Fact (Nat.Prime q)]
    (noise : PMF (ZMod q)) : PMF (Matrix (Fin m) (Fin (n + 1)) (ZMod q)) := do
  let secret ← PMF.uniformOfFintype (Fin n → ZMod q)
  let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let error ← PMF.pi (fun _ : Fin m => noise)
  return publicMatrix publicPart secret error

/-- Draw the public matrix `[A * s + e | A]` where `s` is drawn from the error distribution. -/
noncomputable def publicMatrixLawErrorSecret (n m q : ℕ) [Fact (Nat.Prime q)]
    (noise : PMF (ZMod q)) : PMF (Matrix (Fin m) (Fin (n + 1)) (ZMod q)) := do
  let secret ← PMF.pi (fun _ : Fin n => noise)
  let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let error ← PMF.pi (fun _ : Fin m => noise)
  return publicMatrix publicPart secret error

/-- The prime LWE real ensemble. -/
noncomputable def realEnsemble (n m : ℕ → ℕ) (q : ℕ → ℕ)
    [∀ security, Fact (Nat.Prime (q security))]
    (noise : (security : ℕ) → PMF (ZMod (q security))) (security : ℕ) : PMF (List Bool) :=
  (publicMatrixLaw (n security) (m security) (q security) (noise security)).map (encMatrix _ _ _)

/-- The prime LWE real ensemble with error secret. -/
noncomputable def realEnsembleErrorSecret (n m : ℕ → ℕ) (q : ℕ → ℕ)
    [∀ security, Fact (Nat.Prime (q security))]
    (noise : (security : ℕ) → PMF (ZMod (q security))) (security : ℕ) : PMF (List Bool) :=
  (publicMatrixLawErrorSecret (n security) (m security) (q security) (noise security)).map
    (encMatrix _ _ _)

/-- The uniform ensemble for prime modulus. -/
noncomputable def uniformEnsemble (n m : ℕ → ℕ) (q : ℕ → ℕ)
    [∀ security, Fact (Nat.Prime (q security))] (security : ℕ) : PMF (List Bool) :=
  (PMF.uniformOfFintype
    (Matrix (Fin (m security)) (Fin (n security + 1)) (ZMod (q security)))).map (encMatrix _ _ _)

/-- The prime search LWE game. -/
noncomputable def searchGame (n m q : ℕ) [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (adversary : List Bool → ProbComp (List Bool)) : Game := do
  let secret ← PMF.uniformOfFintype (Fin n → ZMod q)
  let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let error ← PMF.pi (fun _ : Fin m => noise)
  let word := encMatrix _ _ _ (publicMatrix publicPart secret error)
  let guessWord ← ProbComp.eval (adversary word)
  return guessWord = encZModVec n q secret

/-- The prime search LWE game with secret drawn from the error distribution. -/
noncomputable def searchGameErrorSecret (n m q : ℕ) [Fact (Nat.Prime q)] (noise : PMF (ZMod q))
    (adversary : List Bool → ProbComp (List Bool)) : Game := do
  let secret ← PMF.pi (fun _ : Fin n => noise)
  let publicPart ← PMF.uniformOfFintype (Matrix (Fin m) (Fin n) (ZMod q))
  let error ← PMF.pi (fun _ : Fin m => noise)
  let word := encMatrix _ _ _ (publicMatrix publicPart secret error)
  let guessWord ← ProbComp.eval (adversary word)
  return guessWord = encZModVec n q secret


/-- Search LWE hypothesis for prime modulus. -/
def SearchLWE (n m q : ℕ → ℕ) [∀ security, Fact (Nat.Prime (q security))]
    (noise : (security : ℕ) → PMF (ZMod (q security))) : Prop :=
  ∀ adversary : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits adversary →
    Negligible (fun security => Game.succProbability
      (PrimeLWE.searchGame (n security) (m security) (q security)
        (noise security) (adversary security)))

/-- Decision LWE hypothesis for prime modulus. -/
def DecisionLWE (n m q : ℕ → ℕ) [∀ security, Fact (Nat.Prime (q security))]
    (noise : (security : ℕ) → PMF (ZMod (q security))) : Prop :=
  ComputationallyIndistinguishable (PrimeLWE.realEnsemble n m q noise)
    (PrimeLWE.uniformEnsemble n m q)

/-- Search LWE hypothesis with error secret. -/
def SearchLWEErrorSecret (n m q : ℕ → ℕ) [∀ security, Fact (Nat.Prime (q security))]
    (noise : (security : ℕ) → PMF (ZMod (q security))) : Prop :=
  ∀ adversary : ℕ → List Bool → ProbComp (List Bool), IsPPT encBits adversary →
    Negligible (fun security => Game.succProbability
      (PrimeLWE.searchGameErrorSecret (n security) (m security) (q security)
        (noise security) (adversary security)))

/-- Decision LWE hypothesis with error secret. -/
def DecisionLWEErrorSecret (n m q : ℕ → ℕ) [∀ security, Fact (Nat.Prime (q security))]
    (noise : (security : ℕ) → PMF (ZMod (q security))) : Prop :=
  ComputationallyIndistinguishable (PrimeLWE.realEnsembleErrorSecret n m q noise)
    (PrimeLWE.uniformEnsemble n m q)

end PrimeLWE

end Cslib.Crypto
