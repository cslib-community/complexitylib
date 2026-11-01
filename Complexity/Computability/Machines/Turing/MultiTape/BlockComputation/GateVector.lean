/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateInterpolation
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallSpace
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Streaming complete packed gate vectors

The caller retains interpolation parameters, an output-coordinate cursor and one accumulated
output prefix. Each coordinate invokes the same native interpolation machine on the original
query input. Returned values are reduced modulo the retained modulus before one element is
appended. No runtime-length vector is allocated by initialization.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateVector

open MultiTapeTM MultiTapeTM.ComputableInSpace
open Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- Actual interpolation parameters and the number of requested output coordinates. -/
abbrev Params := QueryGate.Params Interpolation.Context × ℕ

/-- Parameters, the next coordinate and the already returned coordinate prefix. -/
abbrev CallerState := Params × ℕ × List ℕ

/-- A vector caller, or one suspended vector caller beside its interpolation callee. -/
abbrev State (k : ℕ) (Q : Type) :=
  CallerState ⊕ (CallerState × Interpolation.State k Q)

/-- Change only the output-coordinate field of actual interpolation metadata. -/
@[expose] def setChunk : QueryGate.Params Interpolation.Context → ℕ →
    QueryGate.Params Interpolation.Context :=
  fun ((N, b, σ, i, m, _, stride), parameters, point, limit) chunk =>
    ((N, b, σ, i, m, chunk, stride), parameters, point, limit)

/-- Initialize one coordinate's interpolation from the caller's actual stored parameters. -/
@[expose] def start : CallerState → Interpolation.State k Q :=
  fun ((params, _), chunk, _) => Interpolation.initial (setChunk params chunk)

/-- Read a completed interpolation accumulator; suspended states have no returned answer. -/
@[expose] def answer : Interpolation.State k Q → ℕ :=
  Sum.elim (fun (_, _, value) => value) (fun _ => 0)

/-- Return one reduced coordinate and advance without retaining the callee. -/
@[expose] def resume : CallerState → Interpolation.State k Q → CallerState :=
  fun (params, chunk, values) returned =>
    let ((_, (p, _, _), _, _), _) := params
    (params, chunk + 1, values ++ [answer returned % p])

/-- Request another coordinate exactly while the output cursor is below the runtime count. -/
@[expose] def request : CallerState → Option (Interpolation.State k Q) :=
  fun ((params, count), chunk, values) =>
    if chunk < count then some (start ((params, count), chunk, values)) else none

/-- The default caller is halted; actual states are supplied through `initial`. -/
@[expose] def caller : QueryMachine CallerState where
  init := ((Interpolation.template, 0), 0, [])
  query _ := 0
  next := Prod.fst
  emit _ := []
  halted := fun ((_, count), chunk, _) => decide (count ≤ chunk)
  finish _ := []

/-- One fixed vector machine reuses one interpolation callee at a time. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) :=
  caller.withCalls (Interpolation.machine M e) request resume

/-- Actual parameters start with an empty prefix and zero cursor. -/
@[expose] def initial (params : Params) : State k Q := .inl (params, 0, [])

/-- All parameters are explicitly retained beside the runtime output count. -/
@[expose] noncomputable def encParams : Params ↪ List Bool :=
  encPair (QueryGate.encParams Interpolation.encContext) encNat

/-- The growing prefix is charged by its actual framed natural-number encoding. -/
@[expose] noncomputable def encCaller : CallerState ↪ List Bool :=
  encPair encParams (encPair encNat (encList encNat))

variable [Finite Q]

/-- A suspended caller pays for its complete interpolation state. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum encCaller (encPair encCaller Interpolation.encState)

/-- Replacing the requested chunk retains the actual point and assignment limit. -/
theorem setChunk_inSpace : ComputableInSpace (fun a => setChunk a.1 a.2)
    (encPair (QueryGate.encParams Interpolation.encContext) encNat)
    (QueryGate.encParams Interpolation.encContext)
    (fun a => (encPair (QueryGate.encParams Interpolation.encContext) encNat a).length) := by
  have hpar := fst (QueryGate.encParams Interpolation.encContext) encNat
  have hchunk := snd (QueryGate.encParams Interpolation.encContext) encNat
  have hctx := hpar.fst'
  have hrest := hpar.snd'
  have hN := hctx.fst'
  have hb := hctx.snd'.fst'
  have hσ := hctx.snd'.snd'.fst'
  have hi := hctx.snd'.snd'.snd'.fst'
  have hm := hctx.snd'.snd'.snd'.snd'.fst'
  have hstride := hctx.snd'.snd'.snd'.snd'.snd'.snd'
  exact (budget_prod
    (budget_prod hN (budget_prod hb (budget_prod hσ (budget_prod hi
      (budget_prod hm (budget_prod hchunk hstride)))))) hrest).of_enc_eq fun _ => rfl

/-- Preparing one coordinate is native in the actual caller-state storage. -/
theorem start_inSpace : ComputableInSpace (start (k := k) (Q := Q)) encCaller
    Interpolation.encState (fun a => (encCaller a).length) := by
  have hparams := fst encParams (encPair encNat (encList encNat))
  have hchunk := (snd encParams (encPair encNat (encList encNat))).fst'
  have hargs : ComputableInSpace
      (fun q : CallerState => (q.1.1, q.2.1)) encCaller
      (encPair (QueryGate.encParams Interpolation.encContext) encNat)
      (fun a => (encCaller a).length) :=
    budget_prod (f := fun q : CallerState => q.1.1) (g := fun q => q.2.1)
      hparams.fst' hchunk
  have hchunked : ComputableInSpace
      (fun q : CallerState => setChunk q.1.1 q.2.1) encCaller
      (QueryGate.encParams Interpolation.encContext) (fun a => (encCaller a).length) :=
    budget_comp_linear (f := fun q : CallerState => (q.1.1, q.2.1))
      (g := fun a => setChunk a.1 a.2) (encIn := encCaller)
      (encB := encPair (QueryGate.encParams Interpolation.encContext) encNat)
      (encC := QueryGate.encParams Interpolation.encContext) setChunk_inSpace hargs
  exact (budget_comp_linear
    (f := fun q : CallerState => setChunk q.1.1 q.2.1)
    (g := Interpolation.initial (k := k) (Q := Q)) (encIn := encCaller)
    (encB := QueryGate.encParams Interpolation.encContext)
    (encC := Interpolation.encState (k := k) (Q := Q))
    (Interpolation.initial_inSpace (k := k) (Q := Q)) hchunked).of_enc_eq fun _ => rfl

/-- Reading a completed accumulator needs no output stream. -/
theorem answer_inSpace : ComputableInSpace (answer (k := k) (Q := Q))
    Interpolation.encState encNat (fun a => (Interpolation.encState a).length) := by
  have hleft := (snd (QueryGate.encParams Interpolation.encContext) (encPair encNat encNat)).snd'
  exact sumElim hleft
    (budget_const (encIn := encPair (QueryGate.encState Interpolation.encContext)
      (SupplierChunk.encState (k := k) (Q := Q))) (encB := encNat) 0 (.refl _))

/-- Resumption charges the appended returned coordinate and the retained output prefix. -/
theorem resume_inSpace : ComputableInSpace
    (fun a : CallerState × Interpolation.State k Q => resume a.1 a.2)
    (encPair encCaller Interpolation.encState) encCaller
    (fun a => (encPair encCaller Interpolation.encState a).length) := by
  have hc := fst encCaller (Interpolation.encState (k := k) (Q := Q))
  have ht := snd encCaller (Interpolation.encState (k := k) (Q := Q))
  have hparams := hc.fst'
  have hchunk := hc.snd'.fst'
  have hvalues := hc.snd'.snd'
  have hp := hparams.fst'.snd'.fst'.fst'
  have hv := budget_natMod (budget_comp_linear answer_inSpace ht) hp
  exact (budget_prod hparams (budget_prod (budget_natSucc hchunk)
    (budget_snoc hvalues hv))).of_enc_eq fun _ => rfl

/-- A call is requested only while a coordinate remains. -/
theorem request_inSpace : ComputableInSpace (request (k := k) (Q := Q)) encCaller
    (encOption Interpolation.encState) (fun a => (encCaller a).length) := by
  have hparams := fst encParams (encPair encNat (encList encNat))
  have hcount := hparams.snd'
  have hchunk := (snd encParams (encPair encNat (encList encNat))).fst'
  have hSome : ComputableInSpace (fun q => some (start (k := k) (Q := Q) q))
      encCaller (encOption (Interpolation.encState (k := k) (Q := Q)))
      (fun a => (encCaller a).length) :=
    budget_comp_linear (f := start (k := k) (Q := Q)) (g := Option.some)
      (encIn := encCaller) (encB := Interpolation.encState (k := k) (Q := Q))
      (encC := encOption (Interpolation.encState (k := k) (Q := Q)))
      (of_inO (ComputableInDegree.optionSome
        (enc₁ := Interpolation.encState (k := k) (Q := Q))).inO_one)
      (start_inSpace (k := k) (Q := Q))
  refine (budget_ite (budget_natLt hchunk hcount) hSome
    (budget_const (encB := encOption Interpolation.encState) none (.refl _))).of_enc_eq ?_
  rintro ⟨⟨params, count⟩, chunk, values⟩
  by_cases h : chunk < count <;> simp [request, h]

/-- Runtime vector parameters initialize only fresh small counters and an empty prefix. -/
theorem initial_inSpace : ComputableInSpace (initial (k := k) (Q := Q)) encParams encState
    (fun a => (encParams a).length) := by
  have hid : ComputableInSpace (fun a : Params => a) encParams encParams
      (fun a => (encParams a).length) := of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hcaller := budget_prod hid (budget_prod
    (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encList encNat) [] (.refl _)))
  exact (budget_comp_linear
    (of_inO (ComputableInO.inl encCaller
      (encPair encCaller (Interpolation.encState (k := k) (Q := Q))))) hcaller).of_enc_eq
        fun _ => rfl

private theorem caller_query_inSpace : ComputableInSpace caller.query encCaller encNat
    (fun a => (encCaller a).length) := budget_const 0 (.refl _)

private theorem caller_next_inSpace : ComputableInSpace caller.next
    (encPair encCaller (encOption encBool)) encCaller
    (fun a => (encPair encCaller (encOption encBool) a).length) :=
  fst encCaller (encOption encBool)

private theorem caller_emit_inSpace : ComputableInSpace caller.emit
    (encPair encCaller (encOption encBool)) encBits
    (fun a => (encPair encCaller (encOption encBool) a).length) := budget_const [] (.refl _)

private theorem caller_halted_inSpace : ComputableInSpace caller.halted encCaller encBool
    (fun a => (encCaller a).length) := by
  have hparams := fst encParams (encPair encNat (encList encNat))
  have hcount := hparams.snd'
  have hchunk := (snd encParams (encPair encNat (encList encNat))).fst'
  exact (budget_finite (encC := encBool) Bool.not (budget_natLt hchunk hcount)).of_enc_eq
    fun ⟨⟨_, count⟩, chunk, _⟩ => by
      by_cases h : count ≤ chunk
      · have hn : ¬chunk < count := by omega
        simp [caller, h, hn]
      · have hn : chunk < count := by omega
        simp [caller, h, hn]

private theorem caller_finish_inSpace : ComputableInSpace caller.finish encCaller encBits
    (fun a => (encCaller a).length) := budget_const [] (.refl _)

/-- The active interpolation callee reads the same original query input. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  QueryMachine.withCalls_query_inSpace caller (Interpolation.machine M e) request resume
    encCaller Interpolation.encState caller_query_inSpace
    (Interpolation.machine_query_inSpace M e) request_inSpace

/-- One transition either enters a coordinate call, advances it, or appends its returned value. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryMachine.withCalls_next_inSpace caller (Interpolation.machine M e) request resume
    encCaller Interpolation.encState caller_next_inSpace
    (Interpolation.machine_next_inSpace M e) (Interpolation.machine_halted_inSpace M e)
    request_inSpace resume_inSpace

/-- Calls and returns do not retain output streams. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  QueryMachine.withCalls_emit_inSpace caller (Interpolation.machine M e) request resume
    encCaller Interpolation.encState caller_emit_inSpace request_inSpace

/-- Completion depends only on the caller's actual cursor and coordinate count. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  QueryMachine.withCalls_halted_inSpace caller (Interpolation.machine M e) request resume
    encCaller Interpolation.encState caller_halted_inSpace

/-- The final coordinate vector remains in the returned state, not an output stream. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  QueryMachine.withCalls_finish_inSpace caller (Interpolation.machine M e) request resume
    encCaller Interpolation.encState caller_finish_inSpace

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateVector
