/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime

/-! Polynomial-time proof search ignores inert goal metadata, including after simplification. -/

namespace ComplexityTests.PolyTimeMetadata

open Turing.MultiTapeTM

private def reverseCopy (word : List Bool) : List Bool := word.reverse ++ word

@[program_certificate]
private theorem reverseCopy_polytime : ComputableInPolyTime reverseCopy encBits encBits := by
  unfold reverseCopy
  fun_prop

-- Each predicate has its own user-certificate registration, so both metadata paths are tested.
@[program_certificate]
private theorem reverseCopy_tidy : ComputableTidilyInPolyTime reverseCopy encBits encBits := by
  unfold reverseCopy
  fun_prop

attribute [irreducible] reverseCopy

-- `fun_prop` and `polytime` ignore `no_index` goal metadata and local `let` bindings across plain
-- and tidy goals, including user `@[program_certificate]` theorems.
example {α : Type} (encoding : α ↪ List Bool) :
    no_index (ComputableInPolyTime
      (fun p : ℕ × List (List Bool) => Cslib.BitString.listXor (p.1 + 1) p.2)
      (encPair encUnary (encList encBits)) encBits) ∧
    no_index (ComputableInPolyTime
      (fun p : ℕ × List (List Bool) =>
        let initial := (p.1 + 1, p.2)
        Cslib.BitString.listXor initial.1 initial.2)
      (encPair encUnary (encList encBits)) encBits) ∧
    no_index (ComputableTidilyInPolyTime
      (fun word : List Bool => let copied := word.tail; copied.reverse) encBits encBits) ∧
    no_index (ComputableInPolyTime
      (fun values : List α => let copied := values.tail; copied.reverse)
      (encList encoding) (encList encoding)) ∧
    no_index (ComputableInPolyTime
      (fun word : List Bool => let copied := word.tail; reverseCopy copied) encBits encBits) :=
  ⟨by fun_prop, by polytime, by polytime, by fun_prop, by polytime⟩

-- Ordinary search also ignores metadata on tidy goals, including a user certificate call.
example : no_index (ComputableTidilyInPolyTime
    (fun word : List Bool => let copied := word.tail; copied.reverse) encBits encBits) := by
  fun_prop

example : no_index (ComputableTidilyInPolyTime
    (fun word : List Bool => let copied := word.tail; reverseCopy copied) encBits encBits) := by
  fun_prop

example {α : Type} (encoding : α ↪ List Bool)
    (algBits : List Bool → List Bool) (hBits : ComputableInPolyTime algBits encBits encBits)
    (algList : List α → List α)
    (hList : ComputableTidilyInPolyTime algList (encList encoding) (encList encoding)) :
    no_index (ComputableInPolyTime
      (fun word : List Bool => let copied := word.tail; (algBits copied).reverse)
      encBits encBits) ∧
    no_index (ComputableTidilyInPolyTime
      (fun values : List α => let copied := values.tail; (algList copied).reverse)
      (encList encoding) (encList encoding)) := by
  refine ⟨?_, ?_⟩
  · clear hList
    fail_if_success (clear hBits; fun_prop)
    fail_if_success (clear hBits; polytime)
    fun_prop
  · clear hBits
    fail_if_success (clear hList; fun_prop)
    fail_if_success (clear hList; polytime)
    polytime

end ComplexityTests.PolyTimeMetadata
