/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

import Complexity.Algorithms.Reachability.Savitch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Space.Reachability
import Complexity.Computability.Machines.Turing.MultiTape.Universal.Complexity
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Tests: Savitch's midpoint reachability

The binary counter, in the order of `Cslib.BitString.enumList`; the midpoint recursion and the
stack machine on a directed path through the words of width two, on a graph whose target is
unreachable, and on the trivial walk at depth zero; walks of the path through
`Cslib.Reachability.savitch_iff`; and instances of the quantitative certificate and of its
polynomial-space form for a family of depths, so that their hypotheses are satisfiable.
-/

namespace ComplexityTests.Savitch

open Cslib Cslib.Reachability Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal (encUnit)

/-! ### The binary counter -/

example :
    BitString.enumList 2 = [[false, false], [true, false], [false, true], [true, true]] ∧
    Savitch.next [true, true] = none ∧
    Savitch.next [true, false, true] = some [false, true, true] ∧
    (BitString.enumList 3).map Savitch.next =
      ((BitString.enumList 3).drop 1).map some ++ [none] :=
  ⟨by decide, rfl, rfl, by decide⟩

/-! ### A directed path -/

/-- The path `00 → 10 → 01 → 11` through the words of width two, in counter order. -/
private def path (u v : List Bool) : Bool := decide (Savitch.next u = some v)

-- At level `i`, the walks of at most `2 ^ i` steps along the directed path.
example :
    reach path 2 0 [false, false] [true, false] = true ∧
    reach path 2 0 [false, false] [false, true] = false ∧
    reach path 2 1 [false, false] [false, true] = true ∧
    reach path 2 1 [false, false] [true, true] = false ∧
    reach path 2 2 [false, false] [true, true] = true ∧
    reach path 2 3 [true, true] [false, false] = false :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- The machine itself, run for `2 ^ 8 - 1` steps by the kernel at depth 1 and via `savitch_eq` at
-- depth 2.
example :
    savitch path 2 1 [false, false] [false, true] = true ∧
    savitch path 2 1 [false, false] [true, true] = false ∧
    savitch path 2 2 [false, false] [true, true] = true :=
  ⟨by decide +kernel, by decide +kernel, by rw [savitch_eq]; decide⟩

example :
    Relation.RelatesWithinSteps
      (fun a b => a.length = 2 ∧ b.length = 2 ∧ path a b = true) [false, false] [true, true]
      (2 ^ 2) ∧
    ¬Relation.RelatesWithinSteps
      (fun a b => a.length = 2 ∧ b.length = 2 ∧ path a b = true) [false, false] [true, true]
      (2 ^ 1) :=
  ⟨(savitch_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl).mp
    (by rw [savitch_eq]; decide),
    by
      rw [← savitch_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl]
      decide +kernel⟩

/-! ### An unreachable target -/

/-- Edges between the words with the same last bit: `{00, 10}` and `{01, 11}` are disconnected. -/
private def halves (u v : List Bool) : Bool := decide (u.getLast? = v.getLast?)

example :
    reach halves 2 1 [false, false] [true, false] = true ∧
    reach halves 2 3 [false, false] [true, true] = false ∧
    savitch halves 2 1 [false, false] [true, true] = false ∧
    ¬Relation.RelatesWithinSteps
      (fun a b => a.length = 2 ∧ b.length = 2 ∧ halves a b = true) [false, false] [true, true]
      (2 ^ 3) :=
  ⟨by decide, by decide, by decide +kernel,
    by rw [← reach_iff (w := 2) (u := [false, false]) (v := [true, true]) rfl rfl]; decide⟩

/-! ### The trivial walk -/

example :
    savitch (fun _ _ => false) 2 0 [true, false] [true, false] = true ∧
    savitch (fun _ _ => false) 2 0 [true, false] [false, true] = false ∧
    savitch (fun _ _ => false) 0 3 [] [] = true :=
  ⟨by decide, by decide, by decide +kernel⟩

/-! ### The certificates, for a family of depths -/

/-- The equality of words, as an edge test with a trivial parameter, in the calculus. -/
private theorem exists_inO_eq : ∃ T S, ComputableTidilyInO
    (fun q : Unit × List Bool × List Bool => decide (q.2.1 = q.2.2))
    (encPair encUnit (encPair encBits encBits)) encBool T S :=
  ⟨_, _, ComputableInO.eqWords.tidy.comp (ComputableTidilyInO.snd encUnit _)⟩

-- Savitch's algorithm at depth `n`, with the width, the endpoints and the edge test fixed.
example : ∃ T S, ComputableInO
    (fun n : ℕ => savitch (fun u v => decide (u = v)) 1 n [false] [true]) encUnary encBool T S := by
  obtain ⟨Te, Se, hedge⟩ := exists_inO_eq
  have hin : ComputableInO (fun n : ℕ => ((), 1, n, [false], [true])) encUnary
      (encArgs encUnit) _ _ :=
    ((ComputableTidilyInO.const ()).prod ((ComputableTidilyInO.const 1).prod
      ((ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).prod
        ((ComputableTidilyInO.const [false]).prod
          (ComputableTidilyInO.const [true]))))).computableInO
  exact ⟨_, _, computableInO_savitch (edge := fun _ u v => decide (u = v)) hedge.computableInO
    hin (fun _ => rfl) fun _ => rfl⟩

-- The same family, in polynomial space.
example : ∃ t s, PolyBounded (fun n : ℕ => (encUnary n).length) s ∧
    ComputableInTimeAndSpace
      (fun n : ℕ => savitch (fun u v => decide (u = v)) 1 n [false] [true]) encUnary encBool
      t s := by
  have hedge : ComputableInPolyTime
      (fun q : Unit × List Bool × List Bool => decide (q.2.1 = q.2.2))
      (encPair encUnit (encPair encBits encBits)) encBool :=
    (ComputableTidilyInDegree.eqWords.comp
      (ComputableTidilyInDegree.snd encUnit _)).computableTidilyInPolyTime.computableInPolyTime
  have hin : ComputableInPolyTime (fun n : ℕ => ((), 1, n, [false], [true])) encUnary
      (encArgs encUnit) := by
    fun_prop
  exact exists_polyBounded_space_savitch (edge := fun _ u v => decide (u = v)) hedge hin
    (fun _ => rfl) fun _ => rfl

end ComplexityTests.Savitch
