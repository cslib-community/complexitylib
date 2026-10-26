/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! Public PCP theorem clients for ordinary SAT and framed Boolean words. -/

namespace ComplexityTests.PCPCompleteness

open Cslib.Complexity Turing.MultiTapeTM

-- encCNF uses encNat for variable names, with no bound on their numeric values.
example : SAT ∈ PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) encCNF :=
  NP_subset_PCP_log encCNF SAT.mem_NP

-- Class equality also applies to framed input words and a direct functional verifier.
example : {word : List Bool | word.headD false = true} ∈
    PCP (fun n => Nat.log 2 n + 1) (fun _ => 1) (encList encBool) := by
  rw [← NP_eq_PCP_log]
  refine ⟨0, fun p => p.1.headD false, by fun_prop, ?_⟩
  intro word
  simp [Polynomial.eval_zero]

end ComplexityTests.PCPCompleteness
