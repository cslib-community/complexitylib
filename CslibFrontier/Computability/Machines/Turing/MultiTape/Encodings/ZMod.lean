/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Binary encodings of residues, residue vectors and residue matrices

A residue `a : ZMod q` is stored as its canonical integer representative `ZMod.cast a` in binary
sign-magnitude form (`encIntBin`). For `q > 0` the representative lies in `[0, q)`; for `q = 0`,
`ZMod 0 = ℤ` and the representative is the integer itself, so the encoding is injective for every
`q : ℕ`. Vectors `Fin n → ZMod q` are framed lists of these representatives in index order, and
matrices `Matrix (Fin n) (Fin m) (ZMod q)` are framed lists of framed rows. The dimensions and
the modulus are not stored: they are fixed by the type.

## Main definitions

* `Turing.MultiTapeTM.encZMod`: a residue as its binary canonical representative.
* `Turing.MultiTapeTM.encZModVec`: a residue vector as a framed list of representatives.
* `Turing.MultiTapeTM.encZModMatrix`: a residue matrix as a framed list of framed rows.
-/

@[expose] public section

namespace Turing.MultiTapeTM

/-- Encode an element of `ZMod q` via its canonical integer representative `ZMod.cast` in binary.
This is injective for every `q : ℕ`, including `q = 0`. -/
def encZMod (q : ℕ) : ZMod q ↪ List Bool :=
  ⟨fun a => encIntBin (ZMod.cast a),
    encIntBin.injective.comp (Function.LeftInverse.injective ZMod.intCast_zmod_cast)⟩

/-- Encode a vector in `Fin n → ZMod q` as a framed list of binary integers. -/
def encZModVec (n q : ℕ) : (Fin n → ZMod q) ↪ List Bool :=
  ⟨fun v => encList encIntBin (List.ofFn fun i : Fin n => ZMod.cast (v i)), by
    intro u v huv
    have hlist := (encList encIntBin).injective huv
    funext i
    have hi := congrArg (fun l : List ℤ => l.getD i.val 0) hlist
    simp only [List.getD_ofFn] at hi
    exact Function.LeftInverse.injective ZMod.intCast_zmod_cast hi⟩

/-- Encode a matrix in `Matrix (Fin n) (Fin m) (ZMod q)` as a framed list of row lists. -/
def encZModMatrix (n m q : ℕ) : Matrix (Fin n) (Fin m) (ZMod q) ↪ List Bool :=
  ⟨fun M => encList (encList encIntBin)
      (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => ZMod.cast (M i j)), by
    intro M N hMN
    have hrows := (encList (encList encIntBin)).injective hMN
    ext i j
    have hij := congrArg (fun rows : List (List ℤ) => (rows.getD i.val []).getD j.val 0) hrows
    simp only [List.getD_ofFn] at hij
    exact Function.LeftInverse.injective ZMod.intCast_zmod_cast hij⟩

end Turing.MultiTapeTM
