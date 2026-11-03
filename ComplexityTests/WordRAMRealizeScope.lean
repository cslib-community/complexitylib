/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (realize syntax-scope regression tests)

public import Complexity.Computability.WordRAM.Realization.Basic
import Complexity.Tactic.Realize

/-!
# Importing realization machinery does not activate its tactic

A private import, including one through an abstract's bridge, must not make `realize` available
outside the Word-RAM scope. Opening either the namespace or its scope activates the same tactic.
-/

public section

namespace ComplexityTests.WordRAMRealizeScope

-- Test the parser directly: an unknown tactic is a parse error, outside `#guard_msgs`' scope.
run_cmd do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "realize" with
  | .error _ => pure ()
  | .ok _ => throwError "`realize` is active without the Word-RAM scope"

open scoped Cslib.WordRAM in
/-- Opening the scope activates the tactic without opening its declaration namespace. -/
theorem read_with_scoped_open : Cslib.WordRAM.Realization.Realizes .exact
    (fun n : ℕ => Cslib.DataStructure.Memory.read n)
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

open Cslib.WordRAM in
/-- Opening the namespace also activates its scoped tactic. -/
theorem read_with_namespace_open : Cslib.WordRAM.Realization.Realizes .exact
    (fun n : ℕ => Cslib.DataStructure.Memory.read n)
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

-- The command-local opens above must not activate the syntax for later declarations.
run_cmd do
  match Lean.Parser.runParserCategory (← Lean.getEnv) `tactic "realize" with
  | .error _ => pure ()
  | .ok _ => throwError "a command-local open leaked the `realize` syntax"

end ComplexityTests.WordRAMRealizeScope
