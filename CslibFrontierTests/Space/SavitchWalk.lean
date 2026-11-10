/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.SavitchWalk
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives

/-!
# Tests: following a walk by Savitch's midpoint recursion

The walk on a directed path through the words of width two, vertex by vertex, with its deepest
stack; a run whose target is unreachable, which still ends on the target in `2 ^ (d + 1) - 1`
steps with the word of zeros as midpoint; a stack of two targets cleared in `stackSteps` steps;
the invariants of a run applied to a concrete run; and instances of the space certificates of a
round and of a run for a family of depths, so that their hypotheses are satisfiable.
-/

namespace CslibFrontierTests.SavitchWalk

open Cslib Cslib.Reachability Cslib.Reachability.Walk Turing.MultiTapeTM

/-! ### A directed path -/

/-- The path `00 → 10 → 01 → 11` through the words of width two, in counter order. -/
private def path (u v : List Bool) : Bool := decide (Savitch.next u = some v)

-- The first midpoint of `00` and `11` at level `1` is `10`; of `10` and `11` at level `0`, `01`.
example :
    midpoint path 2 1 [false, false] [true, true] = [true, false] ∧
    midpoint path 2 0 [true, false] [true, true] = [false, true] :=
  ⟨by decide, by decide⟩

-- The run from `00` to the target `11` at level `2` visits the path in order, staying put while it
-- splits targets, and arrives after `2 ^ 3 - 1 = 7` steps.
example :
    (List.range 8).map (fun n => ((step path 2)^[n] ([false, false], [([true, true], 2)])).1) =
      [[false, false], [false, false], [false, false], [false, false], [true, false],
        [true, false], [false, true], [true, true]] := by
  decide

-- After two splits the stack holds `d + 1 = 3` targets.
example :
    (step path 2)^[2] ([false, false], [([true, true], 2)]) =
      ([false, false], [([false, false], 0), ([true, false], 0), ([true, true], 1)]) := by
  decide

-- Every step of that run stays put or follows an edge.
example (n : ℕ) :
    ((step path 2)^[n + 1] ([false, false], [([true, true], 2)])).1 =
        ((step path 2)^[n] ([false, false], [([true, true], 2)])).1 ∨
      path ((step path 2)^[n] ([false, false], [([true, true], 2)])).1
        ((step path 2)^[n + 1] ([false, false], [([true, true], 2)])).1 = true :=
  eq_or_edge_iterate (edge := path) (w := 2) (d := 2) (u := [false, false]) (v := [true, true])
    rfl rfl (by decide) n

-- Every state of that run is encoded in `O((d + 1) * (d + w + 1))` bits.
example (n : ℕ) :
    (encState ((step path 2)^[n] ([false, false], [([true, true], 2)]))).length ≤
      6 * ((2 + 1) * (2 + 2 + 1)) :=
  length_encState_le
    (width_iterate path (w := 2) (s := ([false, false], [([true, true], 2)])) ⟨rfl, by simp⟩ n)
    (levelsLE_iterate path 2 (s := ([false, false], [([true, true], 2)]))
      (levelsLE_singleton 2 [true, true]) n)

/-! ### An unreachable target -/

/-- Edges between the words with the same last bit: `{00, 10}` and `{01, 11}` are disconnected. -/
private def halves (u v : List Bool) : Bool := decide (u.getLast? = v.getLast?)

-- No midpoint splits the call, so the midpoint is the word of zeros; the run still stands on the
-- target after `2 ^ 2 - 1 = 3` steps, but its last step does not follow an edge.
example :
    midpoint halves 2 0 [false, false] [true, true] = [false, false] ∧
    (step halves 2)^[2] ([false, false], [([true, true], 1)]) =
      ([false, false], [([true, true], 0)]) ∧
    (step halves 2)^[3] ([false, false], [([true, true], 1)]) = ([true, true], []) ∧
    halves [false, false] [true, true] = false :=
  ⟨by decide, by decide, iterate_step_run halves 2 1 _ _, by decide⟩

/-! ### A stack of targets -/

-- The stack `[(10, 1), (00, 0)]` is cleared in `(2 ^ 2 - 1) + (2 ^ 1 - 1) = 4` steps, standing on
-- the last target.
example :
    stackSteps [([true, false], 1), ([false, false], 0)] = 4 ∧
    (step path 2)^[4] ([false, false], [([true, false], 1), ([false, false], 0)]) =
      ([false, false], []) :=
  ⟨rfl, iterate_step_stack path 2 _ [([true, false], 1), ([false, false], 0)]⟩

/-! ### The certificates -/

/-- The equality of words, as an edge test with a trivial parameter, in the calculus. -/
private theorem exists_inO_eq : ∃ T S, ComputableTidilyInO
    (fun q : Unit × List Bool × List Bool => decide (q.2.1 = q.2.2))
    (encPair encUnit (encPair encBits encBits)) encBool T S :=
  ⟨_, _, ComputableInO.eqWords.tidy.comp (ComputableTidilyInO.snd encUnit _)⟩

-- A round of the walk with the equality of words as edge test.
example : ∃ S, ComputableInSpace (roundStep fun (_ : Unit) u v => decide (u = v))
    (encRound encUnit) (encRound encUnit) S := by
  obtain ⟨Te, Se, hedge⟩ := exists_inO_eq
  exact ⟨_, computableInSpace_roundStep (edge := fun _ u v => decide (u = v))
    hedge.computableInO⟩

-- Three steps of the run from `0` to the target `1` at level `n`, for a family of depths.
example : ∃ S, ComputableInSpace
    (fun n : ℕ => (step (fun u v => decide (u = v)) 1)^[3] ([false], [([true], n)])) encUnary
    encState S := by
  obtain ⟨Te, Se, hedge⟩ := exists_inO_eq
  have hin : ComputableInSpace (fun n : ℕ => ((), 1, n, [false], [true])) encUnary
      (encArgs encUnit) _ :=
    .of_inO ((ComputableTidilyInO.const ()).prod ((ComputableTidilyInO.const 1).prod
      ((ComputableTidilyInO.of_linear (.of_eq fun _ => rfl)).prod
        ((ComputableTidilyInO.const [false]).prod
          (ComputableTidilyInO.const [true]))))).computableInO
  exact ⟨_, computableInSpace_run (edge := fun _ u v => decide (u = v)) hedge.computableInO hin
    (ComputableInSpace.const 3) (fun _ => rfl) fun _ => rfl⟩

end CslibFrontierTests.SavitchWalk
