/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log

/-! Plain certificates for concrete disjunctions, inequalities, searches, bounded powers and
range products, without a tidy round trip. -/

open Turing.MultiTapeTM

/-- A unary number is zero or above a fixed threshold. -/
example : ComputableInPolyTime (fun n : ℕ => decide (n = 0 ∨ 5 < n)) encUnary encBool := by
  fun_prop

/-- A unary number differs from a fixed value. -/
example : ComputableInPolyTime (fun n : ℕ => n != 3) encUnary encBool := by
  fun_prop

/-- The first entry of a list of unary numbers above the list's length. -/
example : ComputableInPolyTime (fun l : List ℕ => l.find? fun n => decide (l.length < n))
    (encList encUnary) (encOption encUnary) := by
  fun_prop

/-- The least power of two that is at least `n`, in unary. -/
example : ComputableInPolyTime (fun n : ℕ => 2 ^ Nat.clog 2 n) encUnary encUnary := by
  fun_prop

/-- `(-2) ^ n` as a binary integer, as a product over a unary range. -/
example : ComputableInPolyTime (fun n : ℕ => ∏ _i ∈ Finset.range n, (-2 : ℤ))
    encUnary encIntBin :=
  .intBin_prod_range (f := fun _ => -2) (.const _) .id'

/-- An alternating sign, as a binary integer indexed by a unary pair. -/
private def sign (p : ℕ × ℕ) : ℤ := (-1) ^ (p.1 + p.2)

/-- `∏ i < n, (-1) ^ (n + i)` as a binary integer: `fun_prop` uses the plain range product. -/
example : ComputableInPolyTime (fun n : ℕ => ∏ i ∈ Finset.range n, sign (n, i))
    encUnary encIntBin := by
  have hsign : ComputableInPolyTime sign (encPair encUnary encUnary) encIntBin := by
    unfold sign
    fun_prop
  fun_prop

/-! The tidy-only primitives below need no plain wrapper: `fun_prop` proves their plain goals. -/

/-- `decide_ne`: a unary number differs from its double. -/
example : ComputableInPolyTime (fun n : ℕ => decide (n ≠ 2 * n)) encUnary encBool := by
  fun_prop

/-- `listTakeWithInput`: the first `n` entries of a list of length `n`, doubled. -/
example : ComputableInPolyTime (fun l : List ℕ => (l ++ l).take l.length)
    (encList encUnary) (encList encUnary) := by
  fun_prop

/-- `intBin_neg`: negate a binary integer. -/
example : ComputableInPolyTime (fun z : ℤ => -z) encIntBin encIntBin := by
  fun_prop

/-- `intBin_prod`: the product of a list of binary integers. -/
example : ComputableInPolyTime (fun l : List ℤ => l.prod) (encList encIntBin) encIntBin := by
  fun_prop

/-- `intBin_pow`: a binary integer to a unary power. -/
example : ComputableInPolyTime (fun p : ℤ × ℕ => p.1 ^ p.2) (encPair encIntBin encUnary)
    encIntBin := by
  fun_prop

/-- `intBin_pow'`: a computed binary integer to a computed unary power. -/
example : ComputableInPolyTime (fun p : ℤ × ℕ => (p.1 * p.1) ^ (p.2 + 1))
    (encPair encIntBin encUnary) encIntBin := by
  fun_prop

/-- `zipIdx`: number the entries of a list of unary numbers. -/
example : ComputableInPolyTime (fun l : List ℕ => l.zipIdx) (encList encUnary)
    (encList (encPair encUnary encUnary)) := by
  fun_prop

/-- `listIsEmpty'`: test whether a list of unary numbers is empty. -/
example : ComputableInPolyTime (fun l : List ℕ => l.isEmpty) (encList encUnary) encBool := by
  fun_prop
