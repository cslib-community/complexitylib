/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Polynomial
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness

/-!
# Nondeterministic space tests

The Immerman–Szelepcsényi theorem for nondeterministic space
(`Cslib.Complexity.NSPACE_eq_coNSPACE`) is instantiated at logarithmic, linear and quadratic
space, none of which needs a constructibility hypothesis. The classes are nonvacuous: directed
`s`–`t` connectivity is in `NSPACE(log₂ n)` and in `NSPACE(n)`, and so is its complement. `NL` is
`NSPACE(log₂ n)`, and `NL = coNL` remains its special case. A polynomially bounded
nondeterministic space class is within `NPSPACE` (`Cslib.Complexity.NSPACE_subset_NPSPACE`), so
directed connectivity is in `NPSPACE`.

Nondeterministic space within deterministic exponential time
(`Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE`) is instantiated at a bound below `log₂ n`, at
logarithmic space and at linear space, again without constructibility, and applied to directed
connectivity and its complement.
-/

namespace CslibFrontierTests.NSPACE

open Cslib Cslib.Complexity

example {α : Type} (enc : α ↪ List Bool) :
    NSPACE enc (fun n => n ^ 2) = coNSPACE enc (fun n => n ^ 2) :=
  NSPACE_eq_coNSPACE fun n => (Nat.log2_le_self n).trans (Nat.le_self_pow (by omega) n)

/-- Directed connectivity is in nondeterministic logarithmic space. -/
theorem stcon_mem_log : STCON ∈ NSPACE encSTCON Nat.log2 :=
  NL_eq_NSPACE (enc := encSTCON) ▸ STCON.mem_NL

/-- Logarithmic space is within linear space, so directed connectivity is in `NSPACE(n)`. -/
theorem stcon_mem_linear : STCON ∈ NSPACE encSTCON id :=
  NSPACE_mono Nat.log2_le_self stcon_mem_log

-- The complements, by the theorem.
example : STCONᶜ ∈ NSPACE encSTCON Nat.log2 := compl_mem_NSPACE (fun _ => le_rfl) stcon_mem_log

example : STCON ∈ coNSPACE encSTCON Nat.log2 :=
  (NSPACE_eq_coNSPACE (s := Nat.log2) fun _ => le_rfl) ▸ stcon_mem_log

example : STCON ∈ coNL encSTCON :=
  NL_eq_coNL (enc := encSTCON) ▸ STCON.mem_NL

example : STCONᶜ ∈ NSPACE encSTCON id := compl_mem_NSPACE Nat.log2_le_self stcon_mem_linear

example : STCON ∈ coNSPACE encSTCON id :=
  (NSPACE_eq_coNSPACE (s := id) Nat.log2_le_self) ▸ stcon_mem_linear

/-- Linear space is polynomially bounded, so directed connectivity is in `NPSPACE`. -/
example : STCON ∈ NPSPACE encSTCON := NSPACE_subset_NPSPACE .id stcon_mem_linear

/-- The same membership through the union of the classes `NSPACE (n ^ k)`. -/
example : ∃ k, STCON ∈ NSPACE encSTCON (· ^ k) :=
  mem_NPSPACE_iff_exists_mem_NSPACE.mp (NSPACE_subset_NPSPACE .id stcon_mem_linear)

/-! ### Nondeterministic space within deterministic exponential time -/

/-- Any bound, even one below `log₂ n`: the time keeps the `log₂ n` term. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ NSPACE enc fun _ => 0) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * (Nat.log2 n + 0 + 1)) :=
  exists_mem_DTIME_of_mem_NSPACE h

/-- Directed connectivity is in `DTIME(2 ^ O(log₂ n))`. -/
example : ∃ c, STCON ∈ DTIME encSTCON fun n => 2 ^ (c * Nat.log2 n) :=
  exists_mem_DTIME_of_mem_NSPACE_of_log2_le (fun _ => le_rfl) stcon_mem_log

/-- The complement of directed connectivity is in `DTIME(2 ^ O(n))`, through
Immerman–Szelepcsényi. -/
example : ∃ c, STCONᶜ ∈ DTIME encSTCON fun n => 2 ^ (c * id n) :=
  exists_mem_DTIME_of_mem_NSPACE_of_log2_le Nat.log2_le_self
    (compl_mem_NSPACE Nat.log2_le_self stcon_mem_linear)

/-- `NSPACE(n) ⊆ DTIME(2 ^ O(n))`, problem by problem. -/
example {α : Type} {enc : α ↪ List Bool} {A : Set α} (h : A ∈ NSPACE enc id) :
    ∃ c, A ∈ DTIME enc fun n => 2 ^ (c * n) :=
  exists_mem_DTIME_of_mem_NSPACE_of_log2_le Nat.log2_le_self h

end CslibFrontierTests.NSPACE
