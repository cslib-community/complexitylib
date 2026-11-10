/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.InputLength
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Fixed block-simulation driver

A fixed machine first scans its original read-only input, then starts the increasing-guess
outer search with the measured length. Neither a supplied input length nor a time bound enters
its initial state. Intermediate stages are silent; the final output is one Boolean. The driver
is generic over the schedule evaluator and the guess parameters; Williams's square-root-space
simulation is one instance.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable (E : ScheduleSearch.Evaluator)

/-- Input-length scanner or the active increasing-guess search. -/
abbrev State := QueryMachine.InputLength.State ⊕ OuterSearch.State E

/-- The measured counter enters the outer search without copying the input. -/
@[expose] def resume (state : QueryMachine.InputLength.State) : OuterSearch.State E :=
  OuterSearch.initial E state.1

/-- Scan first, then simulate the source on the same original input. -/
@[expose] def machine (k : ℕ) (P : OuterSearch.Parameters) : QueryMachine (State E) where
  init := .inl QueryMachine.InputLength.machine.init
  query := Sum.elim QueryMachine.InputLength.machine.query (OuterSearch.machine E k P).query
  next := fun (state, symbol) => state.elim
    (fun scan => if QueryMachine.InputLength.machine.halted scan then .inr (resume E scan)
      else .inl (QueryMachine.InputLength.machine.next (scan, symbol)))
    (fun active => .inr ((OuterSearch.machine E k P).next (active, symbol)))
  emit _ := []
  halted := Sum.elim (fun _ => false) (OuterSearch.machine E k P).halted
  finish := Sum.elim (fun _ => []) (OuterSearch.machine E k P).finish

/-- Actual scan and search payloads, including their phase tag. -/
@[expose] noncomputable def encState : State E ↪ List Bool :=
  encSum QueryMachine.InputLength.encState (OuterSearch.encState E)

/-- Native handoff computes the positive starting guess from the actual measured counter. -/
theorem resume_inSpace : ComputableInSpace (resume E)
    QueryMachine.InputLength.encState (OuterSearch.encState E)
    (fun a => (QueryMachine.InputLength.encState a).length) :=
  (budget_comp_linear (g := OuterSearch.initial E)
    (OuterSearch.initial_inSpace E) (fst encNat encBool)).of_enc_eq fun _ => rfl

/-- Original-input queries are preserved in both phases. -/
theorem machine_query_inSpace (k : ℕ) (P : OuterSearch.Parameters) : ComputableInSpace
    (machine E k P).query (encState E) encNat (fun a => (encState E a).length) :=
  sumElim QueryMachine.InputLength.query_inSpace (OuterSearch.machine_query_inSpace E k P)

/-- Native scanning, handoff and search transitions. -/
theorem machine_next_inSpace (k : ℕ) (P : OuterSearch.Parameters) : ComputableInSpace
    (machine E k P).next (encPair (encState E) (encOption encBool)) (encState E)
      (fun a => (encPair (encState E) (encOption encBool) a).length) := by
  have hs := fst QueryMachine.InputLength.encState (encOption encBool)
  have hinl := of_inO (ComputableInO.inl QueryMachine.InputLength.encState
    (OuterSearch.encState E))
  have hinr := of_inO (ComputableInO.inr QueryMachine.InputLength.encState
    (OuterSearch.encState E))
  have hrun := budget_comp_linear hinl QueryMachine.InputLength.next_inSpace
  have hresume := budget_comp_linear hinr (budget_comp_linear (resume_inSpace E) hs)
  have hhalt := budget_comp_linear QueryMachine.InputLength.halted_inSpace hs
  have hleft := budget_ite hhalt hresume hrun
  have hright := budget_comp_linear hinr (OuterSearch.machine_next_inSpace E k P)
  exact sumElimFst hleft hright

/-- All intermediate phases are silent. -/
theorem machine_emit_inSpace (k : ℕ) (P : OuterSearch.Parameters) : ComputableInSpace
    (machine E k P).emit (encPair (encState E) (encOption encBool)) encBits
      (fun a => (encPair (encState E) (encOption encBool) a).length) := budget_const [] (.refl _)

/-- The driver stops precisely when its outer search stops. -/
theorem machine_halted_inSpace (k : ℕ) (P : OuterSearch.Parameters) : ComputableInSpace
    (machine E k P).halted (encState E) encBool (fun a => (encState E a).length) :=
  sumElim (budget_const (encIn := QueryMachine.InputLength.encState) false (.refl _))
    (OuterSearch.machine_halted_inSpace E k P)

/-- The final returned Boolean is the driver output. -/
theorem machine_finish_inSpace (k : ℕ) (P : OuterSearch.Parameters) : ComputableInSpace
    (machine E k P).finish (encState E) encBits (fun a => (encState E a).length) :=
  sumElim (budget_const (encIn := QueryMachine.InputLength.encState) [] (.refl _))
    (OuterSearch.machine_finish_inSpace E k P)

end Turing.MultiTapePTM.BlockComputation.Driver
