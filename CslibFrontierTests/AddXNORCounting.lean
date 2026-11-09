/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Cryptanalysis.AddXNORParity
import CslibFrontier.Cryptanalysis.AddXNORDifference

/-!
# Checked counting, parity and difference clients

These examples exercise actual instances, the uniform and final-operand planted
experiments, necessary width hypotheses and the free-MSB difference boundary.
-/

public section

open Cslib.Cryptanalysis.AddXNOR
open scoped BigOperators

example : solutionCount (fun _ : Fin 2 => 0#1) 0#1 0#1 = 2 := by decide
example : solutionCount (fun _ : Fin 2 => 0#1) 1#1 0#1 = 2 := by decide
example : solutionCount (fun _ : Fin 0 => 0#3) 1#3 0#3 = 0 := by decide
example : solutionCount (fun _ : Fin 0 => 0#3) 0#3 0#3 = 1 := by decide
-- Width zero genuinely needs exclusion from the half-class count bound.
example : solutionCount (fun _ : Fin 2 => 0#0) 0#0 0#0 = 4 := by decide

example (t : BitVec 4) :
    (𝔼 as : Fin 3 → BitVec 4, 𝔼 s : BitVec 4, (solutionCount as s t : ℚ)) = 1 / 2 :=
  balanced_mean_solutionCount 3 t

example (as : Fin 2 → BitVec 3) (s t a : BitVec 3) :
    plantedLastMass as s t a = 8 / 8 * solutionCount (Fin.snoc as a) s t * uniformMass 3 3 := by
  exact plantedLastMass_size_bias as s t a

example (as : Fin 3 → BitVec 2) (s : BitVec 2) : solutionCount as s 0 ≤ 4 :=
  solutionCount_le_half (by decide) (by decide) as s

example (as : Fin 3 → BitVec 2) (s : BitVec 2) (bs cs : Fin 3 → Bool)
    (hb : eval (steps bs as) s = 0) (hc : eval (steps cs as) s = 0) :
    Even (hammingDist bs cs) := solution_hamming_even (by decide) bs cs as s hb hc

example (t a : BitVec 4) : (t ^^^ 8#4) + a = (t + a) ^^^ 8#4 :=
  msb_addition_difference 3 t a

example (post : List (Bool × BitVec 3)) (s a : BitVec 3) :
    eval post (step false s a) ≠ eval post (step true s a) :=
  operator_flip_ne (by decide) s a post

-- Two active low bits, even though the difference also contains the free MSB.
example : activeDifferenceBits 11#4 = 2 := by decide
example :
    (𝔼 t : BitVec 4, 𝔼 a : BitVec 4,
      if (t ^^^ 11#4) + a = (t + a) ^^^ 11#4 then (1 : ℚ) else 0) = 1 / 4 := by
  rw [addition_difference_probability]
  norm_num [show activeDifferenceBits 11#4 = 2 by decide]

-- The MSB-only difference has Hamming weight one but preservation probability one.
-- Thus Proposition 3's parenthetical `2^-w` needs the non-MSB weight of Lemma 7.
example :
    (𝔼 t : BitVec 3, 𝔼 a : BitVec 3,
      if (t ^^^ 4#3) + a = (t + a) ^^^ 4#3 then (1 : ℚ) else 0) = 1 := by
  rw [addition_difference_probability]
  norm_num [show activeDifferenceBits 4#3 = 0 by decide]

example : Cslib.BitString.weight (fun i : Fin 3 => (4#3).getLsbD i) = 1 := by decide
