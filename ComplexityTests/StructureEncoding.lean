/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Structure
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold
import Complexity.Tactic.OptionMatch

/-! Tests of `enc_structure`, `option_match_to_elim` and the list rules for `fun_prop`. -/

namespace ComplexityTests.StructureEncoding

open Turing.MultiTapeTM

/-- A structure with fields of different encodings. -/
structure Point where
  /-- A binary number. -/
  x : ℕ
  /-- A bit string. -/
  y : List Bool
  /-- A list of unary numbers. -/
  z : List ℕ

/-- Points, as their fields. -/
enc_structure ePoint : Point where x : encNat, y : encBits, z : (encList encUnary)

/-! The encoding unfolds to the tuple, and the encoding is injective by construction. -/

example (p : Point) : ePoint p = ePointFields (p.x, p.y, p.z) := ePoint_apply p
example {p q : Point} (h : ePoint p = ePoint q) : p = q := ePoint.injective h

/-! The rules assemble programs over the fields, at both levels of the calculus. -/

example : ComputableInDegree (fun p : Point => Point.mk p.x p.y p.z) ePoint ePoint 1 1 := by
  fun_prop (disch := lia)

-- Reading fields and rebuilding the structure, with the bounds checked once.
example : ComputableInO (fun p : Point => Point.mk p.x p.y p.z.tail) ePoint ePoint
    (fun p => 8 * ((ePoint p).length + 1)) fun p => 8 * ((ePoint p).length + 1) := by
  refine .mono (by fun_prop) 16 (fun p => ?_) fun p => ?_ <;>
  · simp only [ePoint_apply, length_encPair]
    have := ((List.tail_sublist p.z).flatMap (frame ∘ encUnary)).length_le
    omega

/-! A `match` is available to `fun_prop` as `Option.elim`, under binders and nested. -/

/-- A definition with nested matches, with the alternatives in either order. -/
def nested (o : Option ℕ) (b : ℕ) : ℕ × ℕ :=
  match o with
  | none => (b, 0)
  | some q =>
    match (if q = b then some q else none) with
    | some e => (e, q)
    | none => (q, 1)

example : (fun p : Option ℕ × ℕ => nested p.1 p.2) = fun p =>
    p.1.elim (p.2, 0) fun q => (if q = p.2 then some q else none).elim (q, 1) fun e => (e, q) := by
  unfold nested
  option_match_to_elim
  rfl

-- An alternative may use the discriminant.
example (o : Option ℕ) : (match o with | none => o | some x => o.map (· + x)) =
    o.elim o fun x => o.map (· + x) := by
  option_match_to_elim
  rfl

/-- error: option_match_to_elim: no option match in the goal -/
#guard_msgs in
example (o : Option ℕ) (h : o.isSome) : (match o, h with | some x, _ => x) = o.get h := by
  option_match_to_elim

/-! The list rules, with a unary count and a test on the list. -/

example : ComputableInO (fun p : List ℕ × ℕ => if p.1.isEmpty then [] else p.1.take p.2)
    (encPair (encList encUnary) encUnary) (encList encUnary)
    (fun p => (encPair (encList encUnary) encUnary p).length)
    fun p => (encPair (encList encUnary) encUnary p).length := by
  refine .mono (by fun_prop) 16 (fun p => ?_) fun p => ?_ <;>
  · simp only [length_encPair]
    split_ifs <;> omega

/-! `zipFold` pads or truncates, as its function decides at a missing partner. -/

-- Keeping an element without a partner pads with the rest of the first list.
example : zipFold (fun (_ : Unit) (a : ℕ) (b : Option ℕ) => some (a + b.getD 0)) ()
    [1, 2, 3] [10] = [11, 2, 3] := by decide

-- Dropping it truncates to the shorter list, as `List.zipWith` does.
example : zipFold (fun (_ : Unit) (a : ℕ) (b : Option ℕ) => b.map (a + ·)) ()
    [1, 2, 3] [10] = [11] := by decide

end ComplexityTests.StructureEncoding
