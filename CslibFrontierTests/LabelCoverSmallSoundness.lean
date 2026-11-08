/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.PCP.Approximation.LabelCover.SmallSoundness

/-! # Small-soundness Label Cover

Loop removal on a concrete loop, the parallel edges of the incidence reduction of a loop and their
removal by loop removal, the edges of a repetition, and the hardness statements. -/

namespace ComplexityTests.LabelCoverSmallSoundness

open Cslib.PCP Cslib.PCP.Encoded Cslib.Complexity Turing.MultiTapeTM

private def pairs : List (Bool × Bool) :=
  [(false, false), (false, true), (true, false), (true, true)]

/-- A loop requiring its own label to differ from itself, and an equality edge. -/
def loopy : Graph (Bool → Bool → Bool) :=
  ⟨2, [⟨0, 0, fun a b => a != b⟩, ⟨0, 1, fun a b => a == b⟩]⟩

example : ¬loopy.IsLoopless := by decide

-- The loop at `0` becomes an edge from `0` to the fresh vertex `1`; the equality edge from `0` to
-- `1` becomes an edge from `0` to `2`.
example : (Graph.deloop loopy).edges.map (fun d => (d.src, d.dst)) = [(0, 1), (0, 2)] := by
  decide
example : (Graph.deloop loopy).IsLoopless := Graph.isLoopless_deloop loopy
example : (Graph.deloop loopy).vertices = 4 := rfl

-- The loop's relation, read on one label, is never satisfied.
example : (Graph.deloop loopy).edges.map (fun d => d.constraint true false) = [false, false] := by
  decide

-- Loop removal keeps the value exactly.
example : ((Graph.deloop loopy).toGraph id).unsatVal = (loopy.toGraph id).unsatVal :=
  Graph.unsatVal_deloop loopy

-- The incidence projections of a loop join the same left and right vertices twice, so they are
-- parallel edges; after loop removal there are none.
example : ¬(LabelCoverIncidence.reduce pairs false true loopy).NoParallelEdges := by decide
example : (LabelCoverIncidence.reduce pairs false true (Graph.deloop loopy)).NoParallelEdges := by
  decide
example : (LabelCoverIncidence.reduce pairs false true (Graph.deloop loopy)).NoParallelEdges :=
  LabelCoverIncidence.noParallelEdges_reduce pairs false true (Graph.isLoopless_deloop loopy)

-- The three-fold repetition of the two-edge contradiction instance has `2 ^ 3` edges.
example : (LabelCoverRepetition.pow 3 (LabelCoverIncidence.contradiction false true)).edges.length =
    8 := by
  simp [LabelCoverIncidence.contradiction]

-- The edges of the `(k + 1)`-fold repetition prepend each edge to each repeated edge. The left ends
-- of the contradiction instance are `0`, `1`; those of its one-fold repetition are
-- `Nat.pair 0 0 = 0` and `Nat.pair 1 0 = 2`. Prepending gives `Nat.pair 0 0 = 0`,
-- `Nat.pair 0 2 = 4`, `Nat.pair 1 0 = 2` and `Nat.pair 1 2 = 5`.
example : (LabelCoverRepetition.pow 2 (LabelCoverIncidence.contradiction false true)).edges.map
    (fun d => d.src) = [0, 4, 2, 5] := by
  rw [LabelCoverRepetition.edges_pow_succ]
  decide

-- The hardness at soundness `(1 - 2⁻¹⁸⁶ / 6000)^{k / 21}`, for one round.
example : PromiseProblem.NPHard
    (Graph.encoding (encPi (encPi (encPair encBool (encPi encBool)))))
    (GapLabelCover (Fin 1 → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool)))
      (Fin 1 → Bool × (Fin 6 → Bool)) 1 ((1 - 1 / (6000 * 2 ^ 186)) ^ ((1 : ℝ) / 21))) := by
  simpa using GapLabelCover_npHard_pow (k := 1) one_pos

-- Soundness `1/100` is reached by some number of rounds.
example : ∃ k : ℕ, 0 < k ∧ PromiseProblem.NPHard
    (Graph.encoding (encPi (encPi (encPair encBool (encPi encBool)))))
    (GapLabelCover (Fin k → (Bool × (Fin 6 → Bool)) × (Bool × (Fin 6 → Bool)))
      (Fin k → Bool × (Fin 6 → Bool)) 1 (1 / 100)) :=
  exists_GapLabelCover_npHard (by norm_num) (by norm_num)

end ComplexityTests.LabelCoverSmallSoundness
