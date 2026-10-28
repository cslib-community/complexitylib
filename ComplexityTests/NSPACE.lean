/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.LogSpace.Complement
import Complexity.Computability.Complexity.Problems.STCON.Completeness

/-!
# Nondeterministic space tests

The Immerman–Szelepcsényi theorem for nondeterministic space
(`Cslib.Complexity.NSPACE_eq_coNSPACE`) is instantiated at logarithmic, linear and quadratic
space, none of which needs a constructibility hypothesis. The classes are nonvacuous: directed
`s`–`t` connectivity is in `NSPACE(log₂ n)` and in `NSPACE(n)`, and so is its complement. `NL` is
`NSPACE(log₂ n)`, and `NL = coNL` remains its special case.
-/

namespace ComplexityTests.NSPACE

open Cslib Cslib.Complexity

example {α : Type} (enc : α ↪ List Bool) :
    NSPACE enc (fun n => n ^ 2) = coNSPACE enc (fun n => n ^ 2) :=
  NSPACE_eq_coNSPACE fun n => (Nat.log2_le_self n).trans (Nat.le_self_pow (by omega) n)

/-- Directed connectivity is in nondeterministic logarithmic space. -/
theorem stcon_mem_log : STCON ∈ NSPACE encSTCON Nat.log2 :=
  NL_eq_NSPACE (enc := encSTCON) ▸ STCON.mem_NL

/-- Logarithmic space is within linear space, so directed connectivity is in `NSPACE(n)`. -/
theorem stcon_mem_linear : STCON ∈ NSPACE encSTCON id :=
  NSPACE_subset_of_le_mul_add 1 0 (fun n => by simpa using Nat.log2_le_self n) stcon_mem_log

-- The complements, by the theorem.
example : STCONᶜ ∈ NSPACE encSTCON Nat.log2 := compl_mem_NSPACE (fun _ => le_rfl) stcon_mem_log

example : STCON ∈ coNSPACE encSTCON Nat.log2 :=
  (NSPACE_eq_coNSPACE (s := Nat.log2) fun _ => le_rfl) ▸ stcon_mem_log

example : STCON ∈ coNL encSTCON :=
  NL_eq_coNL (enc := encSTCON) ▸ STCON.mem_NL

example : STCONᶜ ∈ NSPACE encSTCON id := compl_mem_NSPACE Nat.log2_le_self stcon_mem_linear

example : STCON ∈ coNSPACE encSTCON id :=
  (NSPACE_eq_coNSPACE (s := id) Nat.log2_le_self) ▸ stcon_mem_linear

end ComplexityTests.NSPACE
