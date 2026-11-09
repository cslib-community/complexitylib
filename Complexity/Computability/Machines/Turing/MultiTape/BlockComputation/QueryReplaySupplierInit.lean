/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayCheckedGate
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAssignments
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLoad
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadPort
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadRow
import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Native initialization of the checked local gate supplier

Initialization reads the previous/provider labels from the actual interpolation counter,
computes the schedule's provider map, input origin and expected head directions, and checks all
labels. Rejection retains an actual label word for paid FAIL output. Acceptance loads the
assembled windows into the original-input replay kernel.

The input length is supplied as binary metadata; the caller must obtain it from the existing
original-input length scanner. The interval address is local: source/horizon handling and
implicit tree-path navigation are separate caller operations.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier

open MultiTapeTM MultiTapeTM.ComputableInSpace

variable {k s : ℕ} {Q : Type} [Finite Q]

/-- Input length, block width, schedule, interval, assignment limit/counter and padded stride. -/
abbrev Args := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- Binary runtime metadata and the actual assignment counter/limit storage. -/
@[expose] noncomputable def encArgs : Args ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat encNat)))))

/-- Initialize a total checked supplier from actual assignment and schedule data. -/
@[expose] noncomputable def prepare (e : Q ≃ Fin s) : Args → CheckedGate.State k Q :=
  fun (N, b, σ, i, limit, counter, stride) =>
    let words := Assignments.labels k (limit, counter, stride, Encoding.width k s b)
    let ports := ScheduleRead.providerMap k (σ, i)
    match Providers.Labels.combine e (b, ports, words.1, words.2) with
    | none => .inl words.1
    | some raw =>
      let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
      .inr ((positive, negative, ScheduleRead.fullrow k (σ, i)),
        Load.load (N, b, (positive, negative), raw))

private theorem labelWidth_inSpace (k s : ℕ) :
    ComputableInSpace (Encoding.width k s) encNat encNat (fun b => (encNat b).length) := by
  have hb : ComputableInSpace (fun b : ℕ => b) encNat encNat
      (fun b => (encNat b).length) :=
    of_inO (ComputableInO.of_eq (f := id) fun _ => rfl)
  have hsize := budget_comp_linear natSize hb
  have hwindow := budget_natMul (budget_const (encB := encNat) k (.refl _))
    (budget_natMul (budget_const (encB := encNat) 3 (.refl _))
      (budget_natMul hb (budget_const (encB := encNat) 2 (.refl _))))
  exact (budget_natSucc (budget_natAdd
    (budget_const (encB := encNat) (s + 1).size (.refl _))
    (budget_natAdd (budget_natMul (budget_const (encB := encNat) (k + 1) (.refl _)) hsize)
      (budget_natAdd (budget_const (encB := encNat) 2 (.refl _)) hwindow)))).of_enc_eq
    fun _ => rfl

/-- All preparation work uses native space linear in actual binary metadata and assignment
storage. Original input symbols remain on the query input, outside this state. -/
theorem prepare_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (prepare (k := k) e) encArgs CheckedGate.encState
      (fun a => (encArgs a).length) := by
  have hN := fst encNat (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat encNat)))) )
  have hrest := snd encNat (encPair encNat (encPair encNat (encPair encNat
    (encPair encNat (encPair encNat encNat)))) )
  have hb := hrest.fst'
  have hσ := hrest.snd'.fst'
  have hi := hrest.snd'.snd'.fst'
  have hlimit := hrest.snd'.snd'.snd'.fst'
  have hcounter := hrest.snd'.snd'.snd'.snd'.fst'
  have hstride := hrest.snd'.snd'.snd'.snd'.snd'
  have haddress := budget_prod hσ hi
  have hwidth := budget_comp_linear (labelWidth_inSpace k s) hb
  have hwords := budget_comp_linear (Assignments.labels_inSpace k)
    (budget_prod hlimit (budget_prod hcounter (budget_prod hstride hwidth)))
  have hports := budget_comp_linear (ScheduleRead.providerMap_inSpace k) haddress
  have hcombined := budget_comp_linear (Providers.Labels.combine_inSpace (k := k) e)
    (budget_prod hb (budget_prod hports (budget_prod hwords.fst' hwords.snd')))
  let empty : RawResult k Q := (none, fun _ => 0, .empty, fun _ => [])
  have hget : ComputableInSpace (fun o : Option (RawResult k Q) => o.getD empty)
      (encOption encRawResult) encRawResult (fun o => (encOption encRawResult o).length) :=
    of_inO (ComputableInDegree.getD (enc₁ := encRawResult) empty).inO_one
  have hisSome : ComputableInSpace (fun o : Option (RawResult k Q) => o.isSome)
      (encOption encRawResult) encBool (fun o => (encOption encRawResult o).length) :=
    of_inO (ComputableInDegree.isSome encRawResult).inO_one
  have horigin := budget_comp_linear (ScheduleRead.origin_inSpace k 0) haddress
  have hrow := budget_comp_linear (ScheduleRead.fullrow_inSpace k) haddress
  have hload := budget_comp_linear (Load.load_inSpace (k := k) (Q := Q))
    (budget_prod hN (budget_prod hb (budget_prod horigin
      (budget_comp_linear hget hcombined))))
  have hcontext := budget_prod horigin.fst' (budget_prod horigin.snd' hrow)
  have hsuccess := budget_comp_linear
    (of_inO (ComputableInO.inr encBits (Gate.encState (k := k) (Q := Q))))
    (budget_prod hcontext hload)
  have hfailure := budget_comp_linear
    (of_inO (ComputableInO.inl encBits (Gate.encState (k := k) (Q := Q)))) hwords.fst'
  refine (budget_ite (budget_comp_linear hisSome hcombined) hsuccess hfailure).of_enc_eq ?_
  rintro ⟨N, b, σ, i, limit, counter, stride⟩
  cases hc : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i),
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).1,
      (Assignments.labels k (limit, counter, stride, Encoding.width k s b)).2) <;>
    simp [prepare, hc, CheckedGate.encState]

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier
