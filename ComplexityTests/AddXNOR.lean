/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import Complexity.Cryptanalysis.AddXNORRuns
import Complexity.Cryptanalysis.AddXNORStripping
import Complexity.Cryptanalysis.AddXNORSwap
import Mathlib.Tactic.NormNum

/-! # Full-width Add/XNOR clients and edge cases -/

open Cslib.Cryptanalysis.AddXNOR
open scoped BigOperators

-- Both a colliding and a noncolliding actual adjacent swap at width two.
example : step true (step false (0#2) (0#2)) (0#2) =
    step false (step true (0#2) (0#2)) (0#2) := by decide
example : step true (step false (1#2) (1#2)) (0#2) ≠
    step false (step true (1#2) (1#2)) (0#2) := by decide

-- Exhaustive independent enumeration of the width-two window: 48 of 64 triples.
example : (Finset.univ.filter fun p : Fin 4 × Fin 4 × Fin 4 =>
    let (t, a, b) := p;
    step true (step false (BitVec.ofNat 2 t.val) (BitVec.ofNat 2 a.val))
        (BitVec.ofNat 2 b.val) =
      step false (step true (BitVec.ofNat 2 t.val) (BitVec.ofNat 2 a.val))
        (BitVec.ofNat 2 b.val)).card = 48 := by decide

-- Width one has no constrained carry bits and always collides.
example : (𝔼 t : BitVec 1, 𝔼 a : BitVec 1, 𝔼 b : BitVec 1,
    if step true (step false t a) b = step false (step true t a) b
    then (1 : ℚ) else 0) = 1 := by
  rw [swap_collision]
  norm_num

-- A concrete arbitrary prefix and suffix, tested via the contextual theorem.
example : (𝔼 t : BitVec 3, 𝔼 a : BitVec 3, 𝔼 b : BitVec 3,
    if eval [(true, 6#3), (false, 7#3)]
        (step true (step false (eval [(false, 5#3)] t) a) b) =
      eval [(true, 6#3), (false, 7#3)]
        (step false (step true (eval [(false, 5#3)] t) a) b)
    then (1 : ℚ) else 0) = 17/32 := by
  rw [swap_collision_context]
  norm_num

-- Reverse evaluation at an arbitrary target and projection to a narrower word.
example : backward [(false, 5#8), (true, 201#8)]
    (eval [(false, 5#8), (true, 201#8)] (97#8)) = 97#8 := backward_eval _ _
example (t : BitVec 8) :
    (backward [(false, 5#8), (true, 201#8)] t).setWidth 3 =
      backward [(false, 5#3), (true, 1#3)] (t.setWidth 3) :=
  backward_project (by decide) _ _

-- Carry into bit one is nonzero on 1+1, and the explicit decomposition applies.
example : carryWord (1#8) (1#8) = 2#8 := by decide
example : eval [(false, 1#8), (true, 7#8)] (1#8) =
    ((1#8 ^^^ operandsXor [(false, 1#8), (true, 7#8)]) ^^^ ~~~0) ^^^
      accumulatedCarries [(false, 1#8), (true, 7#8)] (1#8) :=
  eval_eq_xor_parity_carries _ _

-- Actual zero solutions in both stripping parity branches.
example : Solvable ([5#3].map fun a => a ++ 0#2) (3#3 ++ 0#2) 0 := by
  apply (solvable_scaled_iff _ _ _).2
  exact Or.inl ⟨rfl, [false], rfl, rfl, by decide⟩
example : Solvable ([4#3].map fun a => a ++ 0#2) (3#3 ++ ~~~0#2) 0 := by
  apply (solvable_scaled_iff _ _ _).2
  exact Or.inr ⟨rfl, [true], rfl, rfl, by decide⟩
example (as : List (BitVec 3)) (x : BitVec 3) :
    ¬Solvable (as.map fun a => a ++ 0#2) (x ++ 1#2) 0 := by
  rw [solvable_scaled_iff]
  norm_num

-- Stripping uses the actual quotient of a divisible full-width operand.
example : strip 3 2 [(true, 16#5)] = [(true, 4#3)] := by decide

-- Preserve the fixed-string signed run formula: this is negative, not absolute.
example : fixedCorrelation 5 (runs [3]) = -1/4 := by
  rw [fixedCorrelation_runs]
  norm_num [runFactor, Function.iterate_succ_apply']

example : ∃! p : List Bool × List Bool,
    p.1.length = 2 ∧ p.1 ++ p.2 = [false, true, false] := unique_cut _ _ (by decide)
