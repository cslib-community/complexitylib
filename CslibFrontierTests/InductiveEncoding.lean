/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive

/-! Tests of `enc_inductive`. -/

namespace CslibFrontierTests.InductiveEncoding

open Turing.MultiTapeTM

/-- A non-recursive inductive type with constructors of zero, one and two fields. -/
inductive Label where
  | resample
  | count (n : ℕ)
  | eval (u : ℕ) (y : List Bool)

enc_inductive eLabel : Label where
  | resample
  | count : encUnary
  | eval : encUnary, encBits

/-! The encoding unfolds to the summand of each constructor, and is injective. -/

example : eLabel .resample = [false] := by simp [eLabel_apply, eLabel_toSum]
example (n : ℕ) : eLabel (.count n) = true :: false :: encUnary n := by
  simp [eLabel_apply, eLabel_toSum]
example (u : ℕ) (y : List Bool) :
    eLabel (.eval u y) = true :: true :: encPair encUnary encBits (u, y) := by
  simp [eLabel_apply, eLabel_toSum]
example {x y : Label} (h : eLabel x = eLabel y) : x = y := eLabel.injective h

/-! Constructor rules compose with `fun_prop`. -/

example : ComputableInO (fun p : ℕ × List Bool => Label.eval p.1 p.2) (encPair encUnary encBits)
    eLabel (fun p => 2 * ((encPair encUnary encBits p).length + 1))
    fun p => 2 * ((encPair encUnary encBits p).length + 1) := by
  refine .mono (by fun_prop) 4 (fun p => ?_) fun p => ?_ <;>
  · simp only [length_encPair]
    omega

/-! Case analysis charges only the constructor taken. -/

/-- The size of a label's payload. -/
def weight (l : Label) : ℕ := eLabel_elim l (fun _ => 0) (fun n => n) (fun p => p.1)

example : weight (.eval 3 []) = 3 := rfl

example : ComputableInO (fun p : Unit × Label => eLabel_elim p.2 (fun _ => 0) (fun n => n)
      (fun q => q.1))
    (encPair encUnit eLabel) encUnary
    (fun p => 3 * (encPair encUnit eLabel p).length +
      eLabel_elim p.2 (fun _ => (encPair encUnit encUnit (p.1, ())).length)
        (fun n => (encPair encUnit encUnary (p.1, n)).length)
        (fun q => (encPair encUnit (encPair encUnary encBits) (p.1, q)).length))
    fun p => 3 * (encPair encUnit eLabel p).length +
      eLabel_elim p.2 (fun _ => (encPair encUnit encUnit (p.1, ())).length)
        (fun n => (encPair encUnit encUnary (p.1, n)).length)
        (fun q => (encPair encUnit (encPair encUnary encBits) (p.1, q)).length) :=
  eLabel_elim_inO (ComputableInO.const 0) (ComputableInDegree.snd encUnit encUnary).inO_one
    ((ComputableInDegree.snd encUnit (encPair encUnary encBits)).fst').inO_one

/-! An enumeration. -/

inductive Color where
  | red | green | blue

enc_inductive eColor : Color where
  | red
  | green
  | blue

example : eColor .blue = [true, true] := by simp [eColor_apply, eColor_toSum]

/-! A single constructor: no sum tag, and the payload is the encoding. -/

inductive Wrap where
  | wrap (n : ℕ) (b : Bool)

enc_inductive eWrap : Wrap where
  | wrap : encUnary, encBool

example (n : ℕ) (b : Bool) : eWrap (.wrap n b) = encPair encUnary encBool (n, b) := by
  simp [eWrap_apply, eWrap_toSum]

example : ComputableInO (fun p : ℕ × Bool => Wrap.wrap p.1 p.2) (encPair encUnary encBool) eWrap
    (fun p => 2 * ((encPair encUnary encBool p).length + 1))
    fun p => 2 * ((encPair encUnary encBool p).length + 1) := by
  refine .mono (by fun_prop) 4 (fun p => ?_) fun p => ?_ <;>
  · simp only [length_encPair]
    omega

example : ComputableInO (fun p : Unit × Wrap => eWrap_elim p.2 fun q => q.1)
    (encPair encUnit eWrap) encUnary
    (fun p => 1 * (encPair encUnit eWrap p).length +
      eWrap_elim p.2 fun q => (encPair encUnit (encPair encUnary encBool) (p.1, q)).length)
    fun p => 1 * (encPair encUnit eWrap p).length +
      eWrap_elim p.2 fun q => (encPair encUnit (encPair encUnary encBool) (p.1, q)).length :=
  eWrap_elim_inO ((ComputableInDegree.snd encUnit (encPair encUnary encBool)).fst').inO_one

/-! Mistakes in the constructor list are reported before anything is declared. -/

/--
error: enc_inductive: list every constructor of `Label` once, in declaration order:
  | resample | count | eval
-/
#guard_msgs in
enc_inductive eLabelOrder : Label where
  | count : encUnary
  | resample
  | eval : encUnary, encBits

/--
error: enc_inductive: `Label.eval` has 2 explicit field(s), but 1 encoding(s) are listed; give one
  encoding per field, in order
-/
#guard_msgs (whitespace := lax) in
enc_inductive eLabelFields : Label where
  | resample
  | count : encUnary
  | eval : encUnary

/--
error: Type mismatch
  encBits
has type
  List Bool ↪ List Bool
but is expected to have type
  ℕ ↪ List Bool
-/
#guard_msgs in
enc_inductive eLabelType : Label where
  | resample
  | count : encBits
  | eval : encUnary, encBits

/-- A type abbreviation, which is not an inductive type. -/
def Flag := Bool

/--
error: enc_inductive: `Flag` is not an inductive type
-/
#guard_msgs in
enc_inductive eFlag : Flag where
  | false
  | true

/-- A constructor with an implicit field. -/
inductive Tagged where
  | tag {n : ℕ} (b : Bool)

/--
error: enc_inductive: `Tagged.tag` has an implicit or instance field, which is not supported
-/
#guard_msgs in
enc_inductive eTagged : Tagged where
  | tag : encBool

/--
error: enc_inductive: `Option` has parameters or indices, which are not supported
-/
#guard_msgs in
enc_inductive eOption : Option where
  | none
  | some : encUnary

end CslibFrontierTests.InductiveEncoding
