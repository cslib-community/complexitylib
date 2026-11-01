/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.InputLength
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearch
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Fixed square-root-space simulation driver

A fixed machine first scans its original read-only input, then starts the increasing-guess
outer search with the measured length. Neither a supplied input length nor a time bound enters
its initial state. Intermediate stages are silent; the final output is one Boolean.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type}

/-- Input-length scanner or the active increasing-guess search. -/
abbrev State (k : ℕ) (Q : Type) := QueryMachine.InputLength.State ⊕ OuterSearch.State k Q

/-- The measured counter enters the outer search without copying the input. -/
@[expose] def resume (state : QueryMachine.InputLength.State) : OuterSearch.State k Q :=
  OuterSearch.initial state.1

/-- Scan first, then simulate the source on the same original input. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) where
  init := .inl QueryMachine.InputLength.machine.init
  query := Sum.elim QueryMachine.InputLength.machine.query (OuterSearch.machine M e).query
  next := fun (state, symbol) => state.elim
    (fun scan => if QueryMachine.InputLength.machine.halted scan then .inr (resume scan)
      else .inl (QueryMachine.InputLength.machine.next (scan, symbol)))
    (fun active => .inr ((OuterSearch.machine M e).next (active, symbol)))
  emit _ := []
  halted := Sum.elim (fun _ => false) (OuterSearch.machine M e).halted
  finish := Sum.elim (fun _ => []) (OuterSearch.machine M e).finish

variable [Finite Q]

/-- Actual scan and search payloads, including their phase tag. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum QueryMachine.InputLength.encState (OuterSearch.encState (k := k) (Q := Q))

/-- Native handoff computes the positive starting guess from the actual measured counter. -/
theorem resume_inSpace : ComputableInSpace (resume (k := k) (Q := Q))
    QueryMachine.InputLength.encState OuterSearch.encState
    (fun a => (QueryMachine.InputLength.encState a).length) :=
  (budget_comp_linear (g := OuterSearch.initial (k := k) (Q := Q))
    OuterSearch.initial_inSpace (fst encNat encBool)).of_enc_eq fun _ => rfl

/-- Original-input queries are preserved in both phases. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  sumElim QueryMachine.InputLength.query_inSpace (OuterSearch.machine_query_inSpace M e)

/-- Native scanning, handoff and search transitions. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) := by
  have hs := fst QueryMachine.InputLength.encState (encOption encBool)
  have hinl := of_inO (ComputableInO.inl QueryMachine.InputLength.encState
    (OuterSearch.encState (k := k) (Q := Q)))
  have hinr := of_inO (ComputableInO.inr QueryMachine.InputLength.encState
    (OuterSearch.encState (k := k) (Q := Q)))
  have hrun := budget_comp_linear hinl QueryMachine.InputLength.next_inSpace
  have hresume := budget_comp_linear hinr (budget_comp_linear resume_inSpace hs)
  have hhalt := budget_comp_linear QueryMachine.InputLength.halted_inSpace hs
  have hleft := budget_ite hhalt hresume hrun
  have hright := budget_comp_linear hinr (OuterSearch.machine_next_inSpace M e)
  exact sumElimFst hleft hright

/-- All intermediate phases are silent. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) := budget_const [] (.refl _)

/-- The driver stops precisely when its outer search stops. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := QueryMachine.InputLength.encState) false (.refl _))
    (OuterSearch.machine_halted_inSpace M e)

/-- The final returned Boolean is the driver output. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := QueryMachine.InputLength.encState) [] (.refl _))
    (OuterSearch.machine_finish_inSpace M e)

end Turing.MultiTapePTM.BlockComputation.Driver
