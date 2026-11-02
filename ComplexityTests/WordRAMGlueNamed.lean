/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import Complexity.Computability.WordRAM.Glue

/-! An imported, unexposed named routine for word-glue composition regressions. -/

public section

namespace ComplexityTests.WordRAMGlueNamed

open Cslib.WordRAM

/-- The body is deliberately not exposed to importing clients. -/
def twice (n : ℕ) : ℕ := n + n

/-- A named certificate can be reused without unfolding its function. -/
theorem twice_glue : GlueComputable .exact (fun v => twice (v 0))
    (fun v : Fin 1 → ℕ => 2 * v 0 ≤ 100) (fun _ => 100) := by
  unfold twice
  fun_prop (disch := intros; omega)

/-- A two-input routine whose definition is also hidden across this module boundary. -/
def weighted (v : Fin 2 → ℕ) : ℕ := v 0 + 2 * v 1

/-- The fixed domain and envelope make the named routine safe independently of its callers. -/
theorem weighted_glue : GlueComputable .exact weighted
    (fun v => v 0 + 2 * v 1 ≤ 100) (fun _ => 100) := by
  unfold weighted
  fun_prop (disch := intros; omega)

/-- A concrete value pins the opaque routine's ordinary natural-number meaning. -/
theorem weighted_three_six : weighted ![3, 6] = 15 := by
  unfold weighted
  decide

end ComplexityTests.WordRAMGlueNamed
