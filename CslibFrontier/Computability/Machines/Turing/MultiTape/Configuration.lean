/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Configuration.lean`)

public import CslibFrontier.Init
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration
public import Mathlib.Basic.Finite.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi

/-!
# Finiteness of multi-tape Turing machine actions

With finitely many symbols and control states, there are finitely many one-step multi-tape
Turing machine actions (`Turing.Action.instFinite`).

## Main results

* `Turing.Action.instFinite`: `Finite (Turing.Action k Symbol State)` when `Symbol` and `State`
  are finite.
-/

@[expose] public section

namespace Turing

/-- With finitely many states and symbols, there are finitely many actions. -/
instance Action.instFinite {k : ℕ} {Symbol State : Type*} [Finite Symbol] [Finite State] :
    Finite (Action k Symbol State) :=
  Finite.of_injective
    (fun a : Action k Symbol State => (a.inputTape, a.workTapes, a.output, a.state))
    fun a b h => by
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl

end Turing
