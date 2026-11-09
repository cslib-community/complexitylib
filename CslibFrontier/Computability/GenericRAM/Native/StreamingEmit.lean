/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.StreamingFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists

/-!
# Streaming list output with a separate evolving state

The output tape accumulates emitted records; it is never the next callback state.
The actual machine uses the existing framed streaming kernel. Its time sums actual
callback/state/token work and its space takes actual prefix maxima, charging the
materialized output separately. This permits bounded quarter-join batch generation
without threading a retained dictionary or growing output list through pair callbacks.

## Main definitions

* `emitFold`: semantic ordered output of a stateful record stream.
* `emitFoldCertificate`: an actual uniform machine from concrete next/emitter certificates.
-/

public section
namespace Cslib.GenericRAM.NativeCertificate
open Turing.MultiTapeTM

/-- Ordered records emitted by a stream whose evolving state is separate from its output. -/
@[expose] def emitFold {σ α β : Type} (next : σ → α → σ) (emit : σ → α → List β) :
    σ → List α → List β
  | _, [] => []
  | state, row :: rows => emit state row ++ emitFold next emit (next state row) rows

private theorem emitFold_encoding {σ α β : Type} (eb : β ↪ List Bool)
    (next : σ → α → σ) (emit : σ → α → List β) (state : σ) (rows : List α) :
    streamEmit (fun q => next q.1 q.2) (fun q => encList eb (emit q.1 q.2)) state rows =
      encList eb (emitFold next emit state rows) := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih => rw [streamEmit, emitFold, encList_append, ih]

/-- Execute the supplied next/emitter implementations, summing their actual clocks and using
finite actual prefix maxima for workspace. The output is charged without adding time to space. -/
noncomputable def emitFoldCertificate {σ α β : Type} (es : σ ↪ List Bool)
    (ea : α ↪ List Bool) (eb : β ↪ List Bool) (next : σ → α → σ) (emit : σ → α → List β)
    (nextMachine : NativeCertificate (fun q : σ × α => next q.1 q.2) (encPair es ea) es)
    (emitMachine : NativeCertificate (fun q : σ × α => emit q.1 q.2)
      (encPair es ea) (encList eb)) :
    NativeCertificate (fun q : σ × List α => emitFold next emit q.1 q.2)
      (encPair es (encList ea)) (encList eb) := by
  let enext := encPair es (encFramed ea)
  let framed : NativeCertificate (id : σ × α → _) enext enext :=
    .linear (.of_eq (fun _ => rfl))
  let decoded : NativeCertificate (id : α → α) (encFramed ea) ea :=
    .linear (.of_linear (.of_unframe (fun _ => by simp)))
  let argument := framed.fst.prod (decoded.comp framed.snd)
  let nm := nextMachine.comp argument
  let em := emitMachine.comp argument
  let N := Classical.choose nm.computes.tidy
  have hn := (Classical.choose_spec nm.computes.tidy).1
  have encoded := em.computes.of_enc_eq
    (g := fun q : σ × α => encList eb (emit q.1 q.2)) (encC := encBits) (fun _ => rfl)
  let E := Classical.choose encoded.tidy
  have he := (Classical.choose_spec encoded.tidy).1
  let finishProof := computableInTimeAndSpace_of_const
    (encIn := es) (encOut := encBits) ([] : List Bool)
  let F := Classical.choose finishProof
  have hf := Classical.choose_spec finishProof
  let st := fun (q : σ × List α) j => streamState q.1 (fun p => next p.1 p.2) q.2 j
  let R := fun (q : σ × List α) j => if hj : j < q.2.length then
    N * (nm.time (st q j, q.2[j])+1) + E * (em.time (st q j, q.2[j])+1) +
      (es (st q j)).length + (es (st q (j+1))).length +
        (encFramed ea q.2[j]).length + 1 else 0
  let Q := fun (q : σ × List α) => (Finset.range q.2.length).sup (fun j =>
    if hj : j < q.2.length then
      N * (nm.space (st q j, q.2[j])+1) + E * (em.space (st q j, q.2[j])+1) else 0)
  let B := fun (q : σ × List α) =>
    (Finset.range (q.2.length+1)).sup (fun j => (es (st q j)).length) +
      streamRecordLength (encFramed ea) q.2
  have kernel := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (encA := encFramed ea) (encS := es) (encIn := encPair es (encList ea))
    (encOut := encList eb) (next := fun p : σ × α => next p.1 p.2)
    (g := fun q : σ × List α => emitFold next emit q.1 q.2)
    rawFrameReader (fun row => frame (ea row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) Prod.fst Prod.snd (fun _ => rfl)
    hn he hf.computableTidilyInTimeAndSpace
    (fun q => by simp only [encBits_apply, Function.const_apply, List.append_nil,
      emitFold_encoding])
    (roundCost := R) (sMax := Q) (lMax := B)
    (fun q j hj => by simp only [R, dite_eq_left hj, st]; rfl)
    (fun q j hj => by
      have h := Finset.le_sup (f := fun j => if hj : j < q.2.length then
        N * (nm.space (st q j, q.2[j])+1) + E * (em.space (st q j, q.2[j])+1) else 0)
        (Finset.mem_range.mpr hj)
      simpa only [dite_eq_left hj] using h)
    (fun q j hj => by
      have h := Finset.le_sup (f := fun j => (es (st q j)).length)
        (Finset.mem_range.mpr (by omega : j < q.2.length+1))
      exact h.trans (Nat.le_add_right _ _))
    (fun q j hj => (le_listMax (f := fun a => (encFramed ea a).length)
      (List.getElem_mem hj)).trans (Nat.le_add_left _ _))
  let C := Classical.choose kernel
  have hk := Classical.choose_spec kernel
  let T := fun (q : σ × List α) => C *
    (2 * F + 2 + (encPair es (encList ea) q).length +
      (∑ j ∈ Finset.range q.2.length, R q j) + B q + 1)
  let S := fun (q : σ × List α) => C * (0 + Q q + B q + 1)
  have realizes : ComputableInTimeAndSpace
      (fun q : σ × List α => emitFold next emit q.1 q.2)
      (encPair es (encList ea)) (encList eb) T S := by
    simpa only [Function.const_apply, T, S, C, F] using hk.computableInTimeAndSpace
  exact ⟨T, (fun q => S q + (encList eb (emitFold next emit q.1 q.2)).length),
    ComputableInO.of_bounds realizes 1 (fun _ => by simp) (fun _ => by simp; omega)
      (fun _ => by simp; omega)⟩

end Cslib.GenericRAM.NativeCertificate
