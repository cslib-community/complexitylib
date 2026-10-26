/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Tactic.PolyTime

/-! Ordinary finite-table programs, with unbounded entries and empty types. -/

namespace ComplexityTests.FiniteTables

open Cslib.Turing Turing.MultiTapeTM

-- All three words may grow with the input; the fixed table length does not bound their sizes.
private def rotateReverse (values : Fin 3 → List Bool) : Fin 3 → List Bool :=
  fun i => (values (i + 1)).reverse

example : ComputableTidilyInPolyTime rotateReverse (encPi encBits) (encPi encBits) := by
  unfold rotateReverse
  fun_prop

-- A computed update preserves and charges the other unbounded entries.
example : ComputableTidilyInPolyTime
    (fun values : Fin 3 → List Bool => Function.update values 0 (values 1 ++ values 2))
    (encPi encBits) (encPi encBits) := by polytime

-- A table of tapes supports ordinary projection and tape combinators.
example : ComputableTidilyInPolyTime
    (fun values : Fin 2 → BiTape (List Bool) =>
      Function.update values 0 ((values 0).write (values 1).head).moveLeft)
    (encPi (encBiTape encBits)) (encPi (encBiTape encBits)) := by fun_prop

-- Fixed tuples may capture the whole input in each entry.
example : ComputableTidilyInPolyTime
    (fun bits : List Bool => List.ofFn (fun _ : Fin 4 => bits.reverse))
    encBits (encList encBits) := by fun_prop

-- Aesop normalizes the tuple spelling to replication, including a symbolic fixed tuple length.
example (count : ℕ) : ComputableTidilyInPolyTime
    (fun bits : List Bool => List.ofFn (fun _ : Fin count => bits.reverse))
    encBits (encList encBits) := by polytime

example (count : ℕ) : ComputableTidilyInPolyTime
    (fun bits : List Bool => List.replicate count bits.reverse)
    encBits (encList encBits) := by fun_prop

-- Runtime replication computes its count in unary and charges every copy of an unbounded value.
example : ComputableTidilyInPolyTime
    (fun pair : ℕ × List Bool => List.replicate pair.1 pair.2)
    (encPair encUnary encBits) (encList encBits) := by polytime

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

-- There is an empty table even when no entry value exists.
example : ComputableTidilyInPolyTime (fun _ : List Bool => (Empty.elim : Empty → Empty))
    encBits (encPi encEmpty) := by fun_prop

-- The projection API itself imposes no default-value hypothesis.
example {Index Value : Type} [Fintype Index] (enc : Value ↪ List Bool) (i : Index) :
    ComputableTidilyInPolyTime (fun values : Index → Value => values i) (encPi enc) enc := by
  fun_prop

example {Index Value : Type} [Fintype Index] [DecidableEq Index]
    (enc : Value ↪ List Bool) (i : Index) :
    ComputableTidilyInPolyTime
      (fun pair : (Index → Value) × Value => Function.update pair.1 i pair.2)
      (encPair (encPi enc) enc) (encPi enc) := by fun_prop

-- Unary ranks are bounded for each fixed finite type; no efficient growing enumeration is claimed.
example (tag : Fin 7) : (encFinEnum (Fin 7) tag).length < 7 := by
  simpa using length_encFinEnum_lt tag
example (tag : Fin 7) : (encFinite (Fin 7) tag).length < 7 := by
  simpa using length_encFinite_lt tag

-- The bound includes all list framing, not only the values' own words.
example (values : Fin 3 → List Bool) {bound : ℕ} (h : ∀ i, (values i).length ≤ bound) :
    (encPi encBits values).length ≤ 3 * (2 * bound + 1) := by
  simpa using length_encPi_le encBits values h

end ComplexityTests.FiniteTables
