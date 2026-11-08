/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Call
public import Complexity.Computability.WordRAM.SymbolicExec

/-!
# Continuing symbolic execution through routine contracts

The tactic `wram_call` consumes an existential routine specification at the current `WP` goal.
Its continuation receives the returned state and complete postcondition, with the routine's
instruction allowance already added by `WP.seq`. Resume straight-line execution with `wram_exec`.
The routine's definition stays closed: correctness, safety conditions and its charge come from
the contract, not from symbolic execution of its body.

The renamed form first applies the existing `ExecWithin.rename_post` and retains the caller's
outside-register frame. Both forms normalize memory and register projections of bank views once,
including the facts passed to the continuation. The supplied contract retains all word-fit,
alias, memory and frame obligations.

An existing time-indexed `WP` specification is also accepted; its continuation binds the returned
data, the instruction allowance and its postcondition. At a `WP.Exact` goal, which counts
instructions exactly, the contract states an exact count, `∃ y, Exec w c x y T ∧ P y`, or is a
time-indexed `WP.Exact` specification. No alternative execution or resource model
is added.

## Main results

* `WP.of_spec`, `WP.Exact.of_spec`: continue from a fixed-time existential routine contract.
* `wram_call`: consume a proved routine contract without unfolding its program.
-/

public section

namespace Cslib.WordRAM

/-- Continue from a routine's complete postcondition at its given instruction allowance. -/
theorem WP.of_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, ExecWithin w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.of_execWithin hy (hQ y hP)

/-- Continue from a routine's complete postcondition at its exact instruction count. -/
theorem WP.Exact.of_spec {B : Basis} {r w T : ℕ} {c : Code B r} {x : Data r}
    {P : Data r → Prop} {Q : Data r → ℕ → Prop}
    (h : ∃ y, Exec w c x y T ∧ P y) (hQ : ∀ y, P y → Q y T) :
    WP.Exact w c x Q := by
  obtain ⟨y, hy, hP⟩ := h
  exact WP.Exact.of_exec hy (hQ y hP)

/-- Apply a fixed-time or time-indexed routine contract and expose its continuation.
Only bank-view projections are normalized; the callee program remains closed. -/
syntax (name := wramCall) "wram_call " term:max " with" (ppSpace colGt rintroPat)+ : tactic

macro_rules
  | `(tactic| wram_call $h with $pats*) =>
    `(tactic| (
      first
      | refine Cslib.WordRAM.WP.of_spec $h ?_
      | refine Cslib.WordRAM.WP.mono $h ?_
      | refine Cslib.WordRAM.WP.Exact.of_spec $h ?_
      | refine Cslib.WordRAM.WP.Exact.mono $h ?_
      rintro $pats*
      try simp only [Cslib.WordRAM.Data.comap_regs, Cslib.WordRAM.Data.comap_mem] at *))

/-- Apply a routine contract in an injective bank and retain the outside-register frame. -/
tactic_extension wramCall

@[tactic_alt wramCall]
syntax (name := wramCallRenamed) "wram_call " term:max " renamed " term:max " with"
  (ppSpace colGt rintroPat)+ : tactic

macro_rules
  | `(tactic| wram_call $h renamed $hf with $pats*) =>
    `(tactic| first
      | wram_call (Cslib.WordRAM.ExecWithin.rename_post $hf $h) with $pats*
      | wram_call (Cslib.WordRAM.Exec.rename_post $hf $h) with $pats*)

end Cslib.WordRAM
