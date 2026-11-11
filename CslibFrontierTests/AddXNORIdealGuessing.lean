/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
public import CslibFrontier.Cryptanalysis.AddXNORIdealGuessing
import Mathlib.Tactic.NormNum

/-! # Hidden-word guessing clients -/

public section

open Cslib Cslib.Probability Cslib.OracleComp
open Cslib.Cryptanalysis.AddXNOR.IdealChain

/-- A biased candidate is still independent of the hidden word. -/
example : ((PMF.uniformOfFintype (Operators 3)).bind fun bits =>
    (PMF.pure (fun _ => true : Operators 3)).map
      (fun candidate => decide (candidate = bits))) true = 1 / 8 := by
  simpa only [show (2 : ENNReal) ^ 3 = 8 by norm_num] using
    Guessing.independent_guess 3 (PMF.pure (fun _ => true))

/-- The stopped bound permits arbitrary private coins and bidirectional adaptive calls;
it needs neither a budget nor a candidate-correctness premise. -/
example (perms : Label 3 → Equiv.Perm (Fin 5))
    (program : ProbOracleComp (Spec 3 (Fin 5)) (Operators 3)) :
    ((PMF.uniformOfFintype (Operators 3)).bind fun bits =>
      (ProbOracleComp.runWith
        (Visible.handler false perms ((sourceCut bits 1).splice perms 0 4)) program
        (((), []), false)).map
          (fun (candidate, _, flag) => decide (candidate = bits) && !flag)) true ≤ 1 / 8 := by
  classical
  simpa only [show (2 : ENNReal) ^ 3 = 8 by norm_num] using
    Guessing.stopped_guess_le perms 0 4 1 program
