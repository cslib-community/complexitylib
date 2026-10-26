/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-! Polynomial-time proof search ignores inert goal metadata, including after simplification. -/

namespace ComplexityTests.PolyTimeMetadata

open Turing.MultiTapeTM

example : no_index (ComputableTidilyInPolyTime
    (fun p : ℕ × List (List Bool) => Cslib.BitString.listXor (p.1 + 1) p.2)
    (encPair encUnary (encList encBits)) encBits) := by
  fun_prop

example : no_index (ComputableTidilyInPolyTime
    (fun p : ℕ × List (List Bool) =>
      let initial := (p.1 + 1, p.2)
      Cslib.BitString.listXor initial.1 initial.2)
    (encPair encUnary (encList encBits)) encBits) := by
  polytime

example : ComputableTidilyInPolyTime
    (fun p : ℕ × List (List Bool) => Cslib.BitString.listXor (p.1 + 1) p.2)
    (encPair encUnary (encList encBits)) encBits := by
  polytime

example : ComputableTidilyInPolyTime
    (fun word : List Bool => let copied := word.tail; copied.reverse) encBits encBits := by
  fun_prop

example : no_index (ComputableTidilyInPolyTime
    (fun word : List Bool => let copied := word.tail; copied.reverse) encBits encBits) := by
  polytime

example {α : Type} (encoding : α ↪ List Bool) : ComputableTidilyInPolyTime
    (fun values : List α => let copied := values.tail; copied.reverse)
    (encList encoding) (encList encoding) := by
  fun_prop

example {α : Type} (encoding : α ↪ List Bool) : no_index (ComputableTidilyInPolyTime
    (fun values : List α => let copied := values.tail; copied.reverse)
    (encList encoding) (encList encoding)) := by
  polytime

private def reverseCopy (word : List Bool) : List Bool := word.reverse ++ word

@[program_certificate]
private theorem reverseCopy_polytime : ComputableTidilyInPolyTime reverseCopy encBits encBits := by
  unfold reverseCopy
  fun_prop

attribute [irreducible] reverseCopy

example : no_index (ComputableTidilyInPolyTime
    (fun word : List Bool => let copied := word.tail; reverseCopy copied) encBits encBits) := by
  fun_prop

example : no_index (ComputableTidilyInPolyTime
    (fun word : List Bool => let copied := word.tail; reverseCopy copied) encBits encBits) := by
  polytime

example (algorithm : List Bool → List Bool)
    (h : ComputableTidilyInPolyTime algorithm encBits encBits) :
    no_index (ComputableTidilyInPolyTime
      (fun word : List Bool => let copied := word.tail; (algorithm copied).reverse)
      encBits encBits) := by
  fail_if_success (clear h; fun_prop)
  fail_if_success (clear h; polytime)
  fun_prop

example (algorithm : List Bool → List Bool)
    (h : ComputableTidilyInPolyTime algorithm encBits encBits) :
    no_index (ComputableTidilyInPolyTime
      (fun word : List Bool => let copied := word.tail; (algorithm copied).reverse)
      encBits encBits) := by
  fail_if_success (clear h; fun_prop)
  fail_if_success (clear h; polytime)
  polytime

example {α : Type} (encoding : α ↪ List Bool) (algorithm : List α → List α)
    (h : ComputableTidilyInPolyTime algorithm (encList encoding) (encList encoding)) :
    no_index (ComputableTidilyInPolyTime
      (fun values : List α => let copied := values.tail; (algorithm copied).reverse)
      (encList encoding) (encList encoding)) := by
  fail_if_success (clear h; fun_prop)
  fail_if_success (clear h; polytime)
  polytime

end ComplexityTests.PolyTimeMetadata
