/- Diagnostic fixture only: original goals are identical in all three variants. -/
module
import Complexity.Tactic.PPT

open Turing.MultiTapeTM Cslib Cslib.Probability

example : ComputableInPolyTime (fun p : List Bool × List Bool => p.1 ++ p.2)
    (encPair encBits encBits) encBits := by
  polytime

example : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary := by
  fun_prop (disch := assumption)

example (_f : ℕ → Bool) : True := by
  fail_if_success
    have : ComputableInPolyTime _f encUnary encBool := by
      fun_prop
  trivial

example : IsPPTOn encBits encBits (fun word => pure word) := by
  ppt

-- The quote is authored syntax, but is not an executed tactic call.
run_elab do
  let _ ← `(tactic| polytime)
  pure ()

-- Macro-generated dispatch is recorded separately from original authored calls.
macro "diag1155_generated" : tactic => `(tactic| polytime)
example : ComputableInPolyTime (fun word : List Bool => word) encBits encBits := by
  diag1155_generated

example : ComputableInPolyTime (fun n : ℕ => n + 1) encUnary encUnary ∧
    ComputableInPolyTime (fun word : List Bool => word.reverse) encBits encBits := by
  constructor
  all_goals polytime
