/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.WordRAM.ExactNotation

/-!
# Failure messages of `ram_eval` and `ram_exact_eval`

When neither rule of `ram_eval` applies, the error names the step that failed: the goal is not an
`ExecWithin` or `Exec` goal, `simp` cannot evaluate the program, the interpreter returns `none`,
symbolic execution leaves a condition open, or `omega` cannot prove the instruction bound.
`ram_exact_eval` reports the same steps under its own name.
-/

namespace CslibFrontierTests.WordRAMEvalDiagnostics

open Cslib.WordRAM

private abbrev a : Fin 2 := 0
private abbrev b : Fin 2 := 1

private def two : Code .standard 2 := ram[ a ← #3; b ← #4 ]
private def spin : Code .standard 2 := ram[ a ← #0; b ← #2; while a < b do [ a ← width% ] ]
private def under : Code .exact 2 := ram_exact[ a ← #3; b ← #4; a ← a - b ]
private def branch : Code .standard 2 := ram[ if a < b then [ a ← #1 ] else [ a ← #2 ] ]

/-! The goal must be an `ExecWithin` or an `Exec` goal. -/

/--
error: ram_eval: expected a goal `ExecWithin w c x y T` or `Exec w c x y T`, got
  1 = 2
-/
#guard_msgs in
example : 1 = 2 := by
  ram_eval

/--
error: ram_exact_eval: expected a goal `ExecWithin w c x y T` or `Exec w c x y T`, got
  1 = 2
-/
#guard_msgs in
example : 1 = 2 := by
  ram_exact_eval

/-! A program that is not named among the simp lemmas stays folded, and `simp` makes no progress. -/

/--
error: ram_eval: simp could not evaluate the program:
  `simp` made no progress
Pass the program's definition among the simp lemmas, as in `ram_eval [myProgram]`.
-/
#guard_msgs in
example (x : Data 2) : ∃ y, ExecWithin 8 two x y 2 := by
  apply Exists.intro
  ram_eval

/-! The two instructions of `two` do not fit an allowance of one. -/

/--
error: ram_eval: the program runs to completion, but `omega` could not prove the instruction bound
  2 ≤ 1
-/
#guard_msgs in
example (x : Data 2) : ∃ y, ExecWithin 8 two x y 1 := by
  apply Exists.intro
  ram_eval [two]

/-! Without loop fuel the interpreter stops in the loop and returns `none`; one iteration of fuel
is enough. -/

/--
error: ram_eval: the interpreter returns `none`: the program faults (a written value does not fit
a word, an exact operation is undefined, or it samples with `rand`), or a loop needs more
iterations than allowed, as in `ram_eval 3`.
-/
#guard_msgs (whitespace := lax) in
example (x : Data 2) : ∃ y, ExecWithin 8 spin x y 20 := by
  apply Exists.intro
  ram_eval [spin]

example (x : Data 2) : ∃ y, ExecWithin 8 spin x y 20 := by
  refine ⟨?y, ?run⟩
  case run => ram_eval 1 [spin]

/-! Exact subtraction below zero is undefined, so the exact interpreter returns `none`. -/

/--
error: ram_exact_eval: the interpreter returns `none`: the program faults (a written value does
not fit a word, an exact operation is undefined, or it samples with `rand`), or a loop needs more
iterations than allowed, as in `ram_exact_eval 3`.
-/
#guard_msgs (whitespace := lax) in
example (x : Data 2) : ∃ y, ExecWithin 8 under x y 5 := by
  apply Exists.intro
  ram_exact_eval [under]

/-! A branch on unknown registers stays open and is shown. -/

/--
error: ram_eval: symbolic execution did not finish; there remains
  (if x.regs a < x.regs b then some (x.set a 1, 2) else some (x.set a 2, 3)) = some (?_, ?_)
Pass the definitions of called programs and facts that decide the remaining branches and `Fits`
conditions among the simp lemmas, or allow more loop iterations, as in `ram_eval 3`.
-/
#guard_msgs (whitespace := lax) in
set_option pp.mvars false in
example (x : Data 2) : ∃ y, ExecWithin 8 branch x y 5 := by
  apply Exists.intro
  ram_eval [branch]

/-! A simp lemma that does not elaborate is reported as such, without the hint to unfold the
program. -/

/--
error: ram_eval: a given simp lemma does not elaborate:
  Unknown identifier `noSuchLemma`
-/
#guard_msgs in
example (x : Data 2) : ∃ y, ExecWithin 8 two x y 2 := by
  apply Exists.intro
  ram_eval [two, noSuchLemma]

/-! Under `try` and `first` the failure is silent, as before, and the next alternative runs. The
failing attempts change no goal, which the unused-tactic linter would report. -/

set_option linter.unusedTactic false in
example (x : Data 2) : ∃ y, ExecWithin 8 two x y 2 := by
  apply Exists.intro
  try ram_eval
  ram_eval [two]

set_option linter.unusedTactic false in
example : 1 = 1 := by
  first
  | ram_eval
  | rfl

end CslibFrontierTests.WordRAMEvalDiagnostics
