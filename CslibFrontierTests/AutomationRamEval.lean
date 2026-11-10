/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
-- upstream: local-only (test driver)

import CslibFrontier.Computability.WordRAM.ExactNotation

/-! `ram_eval` and `ram_exact_eval` find their fixed simp lemmas in the simp sets
`ram_eval_simps` and `ram_exact_eval_simps`, indexed once where they are declared. Elaborating the
literal lemma list on every call instead costs about 240,000 heartbeats per call: the four calls
below take about 630,000 heartbeats together, and about 1,600,000 with the literal list. -/

namespace CslibFrontierTests.AutomationRamEval

open Cslib.WordRAM

/-- Register names for a two-register program. -/
abbrev r0 : Fin 2 := 0
/-- Register names for a two-register program. -/
abbrev r1 : Fin 2 := 1

set_option maxHeartbeats 1000 in
-- Pin the indexed simp sets' cost as the regression budget; do not raise it to absorb a return
-- of per-call elaboration of the lemma list, only for a toolchain change that moves the cost.
example (x : Data 2) (n w : ℕ) (hx : x.regs r0 = n) (hfit : Fits w (2 * n + 1)) :
    ExecWithin 8 ram[ r0 ← #3; r1 ← r0 + r0 ] x ((x.set r0 3).set r1 6) 2 ∧
    ExecWithin w ram[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 ∧
    Exec w ram_exact[ r1 ← r0 + r0 ] x (x.set r1 (n + n)) 1 ∧
    Exec 8 ram_exact[ r0 ← #3; r1 ← r0 - r0 ] x ((x.set r0 3).set r1 0) 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ram_eval
  · ram_eval [hx]
  · ram_exact_eval [hx]
  · ram_exact_eval

end CslibFrontierTests.AutomationRamEval
