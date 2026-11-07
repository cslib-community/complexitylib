/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import
  Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierChunkInit
public import Complexity.Computability.TreeEval.Ary.Packed.QueryGateSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Native interpolation with checked block-table calls

The interpolation loop retains actual binary simulation metadata and asks the checked numeric
supplier for one table value at each assignment counter. The supplier receives the loop's
stored limit and current counter, rather than a precomputed table. The original input remains
the shared query input throughout both machines.

The fixed template initializes only an unused default state. Every runtime parameter is read
from an explicitly supplied caller state; changing the template does not affect `runFrom`.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Interpolation

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- Input length, block width, schedule, interval, chunk width/index and padded child stride. -/
abbrev Context := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- The actual binary supplier metadata is charged beside the interpolation point. -/
@[expose] noncomputable def encContext : Context ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat encNat)))))

/-- A running interpolation caller, or that caller suspended beside one table supplier. -/
abbrev State (k : ℕ) (Q : Type) :=
  QueryGate.State Context ⊕ (QueryGate.State Context × SupplierChunk.State k Q)

/-- Initialize the next actual table request from stored metadata, limit and counter. -/
@[expose] noncomputable def start (e : Q ≃ Fin s) : QueryGate.State Context →
    SupplierChunk.State k Q :=
  fun (((N, b, σ, i, m, chunk, stride), _, _, limit), counter, _) =>
    SupplierChunk.prepare e ((m, chunk), (N, b, σ, i, limit, counter, stride))

/-- Default metadata affects only `init`; actual interpolation states are prepared separately. -/
@[expose] def template : QueryGate.Params Context :=
  ((0, 0, 0, 0, 0, 0, 0), (0, 0, 0), [], 0)

/-- Fresh caller counters for actual prepared parameters, rather than the template metadata. -/
@[expose] def initial : QueryGate.Params Context → State k Q :=
  fun q => .inl (QueryGate.initial q)

/-- One fixed machine executes interpolation using actual runtime parameters in its state. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) :=
  QueryGate.machine template (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e)

variable [Finite Q]

/-- Both the suspended caller and the complete numeric supplier storage are explicit. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  QueryGate.encMachineState encContext (SupplierChunk.encState (k := k) (Q := Q))

/-- Actual interpolation parameters initialize their caller state in native linear space. -/
theorem initial_inSpace : ComputableInSpace (initial (k := k) (Q := Q))
    (QueryGate.encParams encContext) encState
      (fun a => (QueryGate.encParams encContext a).length) := by
  have hid : ComputableInSpace (fun q : QueryGate.Params Context => q)
      (QueryGate.encParams encContext) (QueryGate.encParams encContext)
      (fun q => (QueryGate.encParams encContext q).length) :=
    of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hcaller := budget_prod hid (budget_prod
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encNat) 0 (.refl _)))
  exact (budget_comp_linear
    (of_inO (ComputableInO.inl (QueryGate.encState encContext)
      (encPair (QueryGate.encState encContext) (SupplierChunk.encState (k := k) (Q := Q)))))
    hcaller).of_enc_eq fun _ => rfl

/-- Preparing each table request uses native space linear in the actual caller storage. -/
theorem start_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (start (k := k) e) (QueryGate.encState encContext)
      SupplierChunk.encState (fun a => (QueryGate.encState encContext a).length) := by
  have hpar := fst (QueryGate.encParams encContext) (encPair encNat encNat)
  have hctx := hpar.fst'
  have hN := hctx.fst'
  have hb := hctx.snd'.fst'
  have hσ := hctx.snd'.snd'.fst'
  have hi := hctx.snd'.snd'.snd'.fst'
  have hm := hctx.snd'.snd'.snd'.snd'.fst'
  have hchunk := hctx.snd'.snd'.snd'.snd'.snd'.fst'
  have hstride := hctx.snd'.snd'.snd'.snd'.snd'.snd'
  have hlimit := hpar.snd'.snd'.snd'
  have hcounter := (snd (QueryGate.encParams encContext) (encPair encNat encNat)).fst'
  exact (budget_comp_linear (SupplierChunk.prepare_inSpace (k := k) e)
    (budget_prod (budget_prod hm hchunk)
      (budget_prod hN (budget_prod hb (budget_prod hσ (budget_prod hi
        (budget_prod hlimit (budget_prod hcounter hstride)))))))).of_enc_eq fun _ => rfl

/-- Queries include native initialization of the requested checked table call. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat
      (fun a => (encState a).length) :=
  QueryGate.machine_query_inSpace encContext SupplierChunk.encState template
    (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e)
    (SupplierChunk.machine_query_inSpace M e) (start_inSpace e)

/-- A local transition includes initialization, table steps and extracting the returned value. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryGate.machine_next_inSpace encContext SupplierChunk.encState template
    (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e)
    (SupplierChunk.machine_next_inSpace M e) (SupplierChunk.machine_halted_inSpace M e)
    (start_inSpace e) (SupplierChunk.answer_inSpace M e)

/-- The interpolation/table composition emits no intermediate output. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryGate.machine_emit_inSpace encContext SupplierChunk.encState template
    (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e) (start_inSpace e)

/-- The supplied runtime limit controls completion. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool
      (fun a => (encState a).length) :=
  QueryGate.machine_halted_inSpace encContext SupplierChunk.encState template
    (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e)

/-- The modular sum remains in the returned caller state, with an empty finish stream. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits
      (fun a => (encState a).length) :=
  QueryGate.machine_finish_inSpace encContext SupplierChunk.encState template
    (SupplierChunk.machine M e) (start e) (SupplierChunk.answer M e)

omit [Finite Q] in
/-- The fixed template has no effect on executions from actual runtime caller states. -/
theorem machine_runFrom_eq_params (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (q : QueryGate.Params Context) (w : List Bool) (state : State k Q) (t : ℕ) :
    (machine M e).runFrom w state t =
      (QueryGate.machine q (SupplierChunk.machine M e) (start e)
        (SupplierChunk.answer M e)).runFrom w state t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [QueryMachine.runFrom_succ, ih, QueryMachine.runFrom_succ]
    rfl

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Interpolation
