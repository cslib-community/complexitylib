/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.GateVectorBounds
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NodeReply
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.NormalizePoint
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Native gate replies at implicit addresses

An actual implicit address selects either a paid initial-source vector or the complete native
interpolation machine. Invalid and nongate addresses return an empty reply. Interpolation uses
the schedule and interval resolved from the address, with the actual stored point reduced modulo
its retained modulus. All branches use the raw evaluator's existing reply format.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply

open MultiTapeTM MultiTapeTM.ComputableInSpace Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- An actual implicit address and actual interpolation parameters with output count. -/
abbrev Args := ImplicitPath.WalkArgs × GateVector.Params

/-- A completed immediate reply or the complete active interpolation-vector state. -/
abbrev State (k : ℕ) (Q : Type) := RawController.Reply ⊕ GateVector.State k Q

/-- Resolve interval metadata and normalize the retained field point. -/
@[expose] def prepare (k : ℕ) : Args → GateVector.Params :=
  fun (address, ((N, b, _, _, m, _, stride), (p, alphabet, n), point, limit), count) =>
    let (σ, _, _) := address
    (((N, b, σ, ImplicitPath.walk k address - 1, m, 0, stride),
      (p, alphabet, n), NormalizePoint.normalize p point, limit), count)

/-- Immediate nongate rejection, paid source padding, or a fresh positive-interval vector. -/
@[expose] def initial (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) : Args → State k Q :=
  fun (address, params) =>
    let (gateParams, count) := params
    let ((_, _, _, _, m, _, _), _, _, limit) := gateParams
    if ImplicitNode.classify k address = 2 then
      if ImplicitPath.walk k address = 0 then
        .inl (0, InitialVector.values M e (limit, m, count))
      else .inr (GateVector.initial (prepare k (address, params)))
    else .inl (0, [])

/-- The immediate branch halts; the active branch runs on the same original input. -/
@[expose] noncomputable def machine (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    QueryMachine (State k Q) where
  init := .inl (0, [])
  query := Sum.elim (fun _ => 0) (GateVector.machine M e).query
  next := fun (q, symbol) => q.elim (fun reply => .inl reply)
    (fun active => .inr ((GateVector.machine M e).next (active, symbol)))
  emit _ := []
  halted := Sum.elim (fun _ => true) (GateVector.machine M e).halted
  finish _ := []

/-- Read the retained completed vector without constructing an uncharged return word. -/
@[expose] def answer : State k Q → RawController.Reply :=
  Sum.elim id (Sum.elim (fun (_, _, values) => (0, values)) (fun _ => (0, [])))

/-- Both address storage and retained vector parameters are charged. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair ImplicitPath.encWalkArgs GateVector.encParams

variable [Finite Q]

/-- Immediate replies and active states each retain their actual payload. -/
@[expose] noncomputable def encState : State k Q ↪ List Bool :=
  encSum RawController.encReply (GateVector.encState (k := k) (Q := Q))

/-- Preparing the actual point and resolved interval uses native linear local space. -/
theorem prepare_inSpace : ComputableInSpace (prepare k) encArgs GateVector.encParams
    (fun a => (encArgs a).length) := by
  have ha := fst ImplicitPath.encWalkArgs GateVector.encParams
  have hv := snd ImplicitPath.encWalkArgs GateVector.encParams
  have hpar := hv.fst'
  have hc := hpar.fst'
  have hrest := hpar.snd'
  have hparameters := hrest.fst'
  have hpoint := hrest.snd'.fst'
  have hlimit := hrest.snd'.snd'
  have hN := hc.fst'
  have hb := hc.snd'.fst'
  have hm := hc.snd'.snd'.snd'.snd'.fst'
  have hstride := hc.snd'.snd'.snd'.snd'.snd'.snd'
  have hindex := budget_natSub (budget_comp_linear (ImplicitPath.walk_inSpace k) ha)
    (budget_const (encB := encNat) 1 (.refl _))
  have hnorm := budget_comp_linear NormalizePoint.normalize_inSpace
    (budget_prod hparameters.fst' hpoint)
  exact (budget_prod
    (budget_prod
      (budget_prod hN (budget_prod hb (budget_prod ha.fst' (budget_prod hindex
        (budget_prod hm (budget_prod (budget_const (encB := encNat) 0 (.refl _)) hstride))))))
      (budget_prod hparameters (budget_prod hnorm hlimit))) hv.snd').of_enc_eq
        fun _ => rfl

/-- Dispatch and paid source construction use the actual encoded arguments. -/
theorem initial_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (initial M e) encArgs encState (fun a => (encArgs a).length) := by
  have ha := fst ImplicitPath.encWalkArgs GateVector.encParams
  have hv := snd ImplicitPath.encWalkArgs GateVector.encParams
  have hpar := hv.fst'
  have hc := hpar.fst'
  have hlimit := hpar.snd'.snd'.snd'
  have hm := hc.snd'.snd'.snd'.snd'.fst'
  have hsource := budget_comp_linear (InitialVector.values_inSpace M e)
    (budget_prod hlimit (budget_prod hm hv.snd'))
  have hinl := of_inO (ComputableInO.inl RawController.encReply
    (GateVector.encState (k := k) (Q := Q)))
  have hinr := of_inO (ComputableInO.inr RawController.encReply
    (GateVector.encState (k := k) (Q := Q)))
  have hsource' := budget_comp_linear hinl
    (budget_prod (budget_const (encB := encNat) 0 (.refl _)) hsource)
  have hactive := budget_comp_linear hinr
    (budget_comp_linear (GateVector.initial_inSpace (k := k) (Q := Q)) (prepare_inSpace (k := k)))
  have hgate := budget_natEq (budget_comp_linear (ImplicitNode.classify_inSpace k) ha)
    (budget_const (encB := encNat) 2 (.refl _))
  have hzero := budget_natIsZero (budget_comp_linear (ImplicitPath.walk_inSpace k) ha)
  have hempty := budget_const (encIn := encArgs) (encB := encState (k := k) (Q := Q))
    (.inl (0, [])) (.refl _)
  refine (budget_ite hgate (budget_ite hzero hsource' hactive) hempty).of_enc_eq ?_
  rintro ⟨address, params, count⟩
  by_cases hg : ImplicitNode.classify k address = 2 <;>
    by_cases hz : ImplicitPath.walk k address = 0 <;> simp [initial, hg, hz] <;> rfl

/-- Reading a reply retains the existing raw-controller encoding. -/
theorem answer_inSpace : ComputableInSpace (answer (k := k) (Q := Q)) encState
    RawController.encReply (fun a => (encState a).length) := by
  have hid : ComputableInSpace (fun a : RawController.Reply => a)
      RawController.encReply RawController.encReply
      (fun a => (RawController.encReply a).length) :=
    of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hvalues := (snd GateVector.encParams (encPair encNat (encList encNat))).snd'
  have hcaller := budget_prod
    (budget_const (encIn := GateVector.encCaller) (encB := encNat) 0 (.refl _)) hvalues
  have hsuspended := budget_const
    (encIn := encPair GateVector.encCaller (Interpolation.encState (k := k) (Q := Q)))
    (encB := RawController.encReply) (0, []) (.refl _)
  exact sumElim hid (sumElim hcaller hsuspended)

/-- Queries preserve the vector machine's original-input interface. -/
theorem machine_query_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).query encState encNat (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := RawController.encReply) (encB := encNat) 0 (.refl _))
    (GateVector.machine_query_inSpace M e)

/-- One native transition preserves the immediate or active branch. -/
theorem machine_next_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).next (encPair encState (encOption encBool)) encState
      (fun a => (encPair encState (encOption encBool) a).length) := by
  have hleft := budget_comp_linear
    (of_inO (ComputableInO.inl RawController.encReply
      (GateVector.encState (k := k) (Q := Q))))
    (fst RawController.encReply (encOption encBool))
  have hright := budget_comp_linear
    (of_inO (ComputableInO.inr RawController.encReply
      (GateVector.encState (k := k) (Q := Q)))) (GateVector.machine_next_inSpace M e)
  exact sumElimFst hleft hright

/-- Replies emit no intermediate words. -/
theorem machine_emit_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).emit (encPair encState (encOption encBool)) encBits
      (fun a => (encPair encState (encOption encBool) a).length) :=
  budget_const [] (.refl _)

/-- Immediate replies halt; active vectors use their existing halt predicate. -/
theorem machine_halted_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).halted encState encBool (fun a => (encState a).length) :=
  sumElim (budget_const (encIn := RawController.encReply) (encB := encBool) true (.refl _))
    (GateVector.machine_halted_inSpace M e)

/-- The reply remains in the state rather than an output stream. -/
theorem machine_finish_inSpace (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) :
    ComputableInSpace (machine M e).finish encState encBits (fun a => (encState a).length) :=
  budget_const [] (.refl _)

end Turing.MultiTapePTM.BlockComputation.QueryReplay.GateReply
