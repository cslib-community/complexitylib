/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayCheckedGate
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAssignments
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayLoad
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadPort
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadRow
import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.WidthSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum

/-!
# Native initialization of the checked local gate supplier

Initialization reads the previous/provider labels from the actual interpolation counter,
computes the schedule's provider map, input origin and expected head directions, and checks all
labels. Rejection retains an actual label word for paid FAIL output. Acceptance loads the
assembled windows into the original-input replay kernel.

`Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier.prepareWords` takes the label words
explicitly, for callers that keep them in a table rather than an interpolation counter;
`Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier.prepare` reads them from the counter
and calls it.

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

/-- Input length, block width, schedule, interval, and the previous and provider label words. -/
abbrev WordArgs (k : ℕ) := ℕ × ℕ × ℕ × ℕ × Assignments.Words k

/-- Binary runtime metadata beside the actual label words. -/
@[expose] noncomputable def encWordArgs : WordArgs k ↪ List Bool :=
  encPair encNat (encPair encNat (encPair encNat (encPair encNat (Assignments.encWords (k := k)))))

/-- Initialize a total checked supplier from schedule data and explicit label words: the
previous interval's label and the labels of the window providers. -/
@[expose] noncomputable def prepareWords (e : Q ≃ Fin s) : WordArgs k → CheckedGate.State k Q :=
  fun (N, b, σ, i, words) =>
    let ports := ScheduleRead.providerMap k (σ, i)
    match Providers.Labels.combine e (b, ports, words.previous, words.providers) with
    | none => .inl words.previous
    | some raw =>
      let (positive, negative) := ScheduleRead.origin k 0 (σ, i)
      .inr ((positive, negative, ScheduleRead.fullrow k (σ, i)),
        Load.load (N, b, (positive, negative), raw))

/-- Initialize a total checked supplier from actual assignment and schedule data: the label words
are read from the assignment counter. -/
@[expose] noncomputable def prepare (e : Q ≃ Fin s) : Args → CheckedGate.State k Q :=
  fun (N, b, σ, i, limit, counter, stride) =>
    prepareWords e (N, b, σ, i,
      Assignments.labels k { limit, counter, stride, width := Encoding.width k s b })

/-- All preparation work from explicit label words uses native space linear in the binary
metadata and the words. Original input symbols remain on the query input, outside this state. -/
theorem prepareWords_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (prepareWords (k := k) e) encWordArgs CheckedGate.encState
      (fun a => (encWordArgs a).length) := by
  have hN := fst encNat (encPair encNat (encPair encNat (encPair encNat
    (Assignments.encWords (k := k)))))
  have hrest := snd encNat (encPair encNat (encPair encNat (encPair encNat
    (Assignments.encWords (k := k)))))
  have hb := hrest.fst'
  have hσ := hrest.snd'.fst'
  have hi := hrest.snd'.snd'.fst'
  have hwords := hrest.snd'.snd'.snd'
  have hprevious := Assignments.encWords_previous_budget hwords
  have hproviders := Assignments.encWords_providers_budget hwords
  have haddress := budget_prod hσ hi
  have hports := budget_comp_linear (ScheduleRead.providerMap_inSpace k) haddress
  have hcombined := budget_comp_linear (Providers.Labels.combine_inSpace (k := k) e)
    (budget_prod hb (budget_prod hports (budget_prod hprevious hproviders)))
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
    (of_inO (ComputableInO.inl encBits (Gate.encState (k := k) (Q := Q)))) hprevious
  refine (budget_ite (budget_comp_linear hisSome hcombined) hsuccess hfailure).of_enc_eq ?_
  rintro ⟨N, b, σ, i, words⟩
  cases hc : Providers.Labels.combine e (b, ScheduleRead.providerMap k (σ, i), words.previous,
      words.providers) <;>
    simp [prepareWords, hc, CheckedGate.encState]

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
  have hlimit := hrest.snd'.snd'.snd'.fst'
  have hcounter := hrest.snd'.snd'.snd'.snd'.fst'
  have hstride := hrest.snd'.snd'.snd'.snd'.snd'
  have hwidth := budget_comp_linear (Encoding.width_inSpace k s) hb
  have hwords := budget_comp_linear (Assignments.labels_inSpace k)
    (Assignments.encArgs_mk_budget hlimit hcounter hstride hwidth)
  exact (budget_comp_linear (prepareWords_inSpace (k := k) e)
    (budget_prod hN (budget_prod hb (budget_prod hrest.snd'.fst'
      (budget_prod hrest.snd'.snd'.fst' hwords))))).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.BlockComputation.QueryReplay.Supplier
