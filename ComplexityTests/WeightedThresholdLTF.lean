/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.LTF
import Mathlib.Tactic.NormNum

open Cslib.Circuits.Boolean.WeightedThreshold

-- Ties are accepted, opposite nonzero coefficients have equal rank, and zero is excluded.
example : ltfEval (fun i : Fin 3 => if i = 0 then (1 : ℝ) else if i = 1 then -1 else 0)
    0 (fun _ => true) = true := by
  norm_num [ltfEval, Fin.sum_univ_succ]

example :
    let a : Fin 3 → ℝ := fun i => if i = 0 then 1 else if i = 1 then -1 else 0
    ltfWeightRank a 0 = 2 ∧ ltfWeightRank a 1 = 2 ∧ (2 : Fin 3) ∉ ltfSupport a := by
  norm_num [ltfWeightRank, ltfSupport, Fin.univ_succ, Finset.filter_insert, Finset.filter_singleton]
