/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.GenericRAM.Native.Combinators
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.StreamingFilter
import all Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import Complexity.Foundations.Data.List.Fold

/-!
# Native certificates for a single-pass encoded fold

A framed list is read once by the uniform streaming kernel. The callback keeps
an encoded parameter and evolving state. Time sums the actual callback costs
and state/token copies; workspace takes their maxima over actual prefixes.
The input rearrangement, final projection and returned state are also charged.
In particular this construction does not charge its total running time as space.
Captured parameters and states are copied each round; persistent-tape algorithms
need a different callback construction to avoid those costs.

## Main definitions

* `foldlStream`: a single-pass fold certificate from an actual callback certificate.
-/

public section
namespace Cslib.GenericRAM.NativeCertificate
open Turing.MultiTapeTM

/-- Execute a fold with one framed-list read, summing actual round costs and
bounding workspace by actual callback/state/token prefix maxima. -/
noncomputable def foldlStream {π σ α : Type} (ep : π ↪ List Bool)
    (es : σ ↪ List Bool) (ea : α ↪ List Bool) (step : π → σ → α → σ)
    (body : NativeCertificate (fun q : (π × σ) × α => step q.1.1 q.1.2 q.2)
      (encPair (encPair ep es) ea) es) :
    NativeCertificate (fun q : π × (σ × List α) => q.2.2.foldl (step q.1) q.2.1)
      (encPair ep (encPair es (encList ea))) es := by
  let estate := encPair ep es
  let enext := encPair estate (encFramed ea)
  let next := fun q : (π × σ) × α => (q.1.1, step q.1.1 q.1.2 q.2)
  let raw : NativeCertificate (id : (π × σ) × α → _)
      (encPair estate ea) (encPair estate ea) := .linear (.of_eq (fun _ => rfl))
  let lifted := raw.fst.fst.prod body
  let framed : NativeCertificate (id : (π × σ) × α → _) enext enext :=
    .linear (.of_eq (fun _ => rfl))
  let decoded : NativeCertificate (id : α → α) (encFramed ea) ea :=
    .linear (.of_linear (.of_unframe (fun _ => by simp)))
  let argument := framed.fst.prod (decoded.comp framed.snd)
  have hn : ComputableInO next enext estate
      (fun q => argument.time q + lifted.time (q.1, q.2))
      (fun q => argument.space q + lifted.space (q.1, q.2)) := (lifted.comp argument).computes
  let cN := Classical.choose hn.tidy
  have hN := (Classical.choose_spec hn.tidy).1
  let finishProof := (ComputableInO.snd ep es).tidy
  let cF := Classical.choose finishProof
  have hF := (Classical.choose_spec finishProof).1
  let emptyProof := computableInTimeAndSpace_of_const
    (encIn := enext) (encOut := encBits) ([] : List Bool)
  let cE := Classical.choose emptyProof
  have hE := Classical.choose_spec emptyProof
  let st := fun (q : (π × σ) × List α) j =>
    (q.1.1, (q.2.take j).foldl (step q.1.1) q.1.2)
  have stateEq (q : (π × σ) × List α) (j : ℕ) :
      streamState q.1 next q.2 j = st q j := by
    exact List.foldl_keep_fst (fun p state row => step p state row) q.1.1 (q.2.take j) q.1.2
  let R := fun (q : (π × σ) × List α) j => if hj : j < q.2.length then
    cN * (argument.time (st q j, q.2[j]) + lifted.time (st q j, q.2[j]) + 1) +
      (2*cE+2) + (estate (st q j)).length + (estate (st q (j+1))).length +
        (encFramed ea q.2[j]).length + 1 else 0
  let Q := fun (q : (π × σ) × List α) => (Finset.range q.2.length).sup (fun j =>
    if hj : j < q.2.length then
      cN * (argument.space (st q j, q.2[j]) + lifted.space (st q j, q.2[j]) + 1) else 0)
  let B := fun (q : (π × σ) × List α) =>
    (Finset.range (q.2.length+1)).sup (fun j => (estate (st q j)).length) +
      streamRecordLength (encFramed ea) q.2
  have kernel := ComputableTidilyInTimeAndSpace.streamFold_pair_sum
    (encA := encFramed ea) (encS := estate)
    (encIn := encPair estate (encList ea)) (encOut := es) (next := next)
    (g := fun q : (π × σ) × List α => q.2.foldl (step q.1.1) q.1.2)
    rawFrameReader (fun row => frame (ea row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) Prod.fst Prod.snd (fun _ => rfl)
    hN hE.computableTidilyInTimeAndSpace hF
    (fun q => by
      simp only [encBits_apply, Function.const_apply, streamEmit_const_nil, List.nil_append,
        stateEq, st, List.take_length])
    (roundCost := R) (sMax := Q) (lMax := B)
    (fun q j hj => by simp only [stateEq, R, dite_eq_left hj]; rfl)
    (fun q j hj => by
      have h := Finset.le_sup (f := fun j => if hj : j < q.2.length then
        cN * (argument.space (st q j, q.2[j]) + lifted.space (st q j, q.2[j]) + 1) else 0)
        (Finset.mem_range.mpr hj)
      simpa only [stateEq, dite_eq_left hj, Nat.add_zero] using h)
    (fun q j hj => by
      have h := Finset.le_sup (f := fun j => (estate (st q j)).length)
        (Finset.mem_range.mpr (by omega : j < q.2.length+1))
      simp only [stateEq]
      exact h.trans (Nat.le_add_right _ _))
    (fun q j hj => (le_listMax (f := fun a => (encFramed ea a).length)
      (List.getElem_mem hj)).trans (Nat.le_add_left _ _))
  let C := Classical.choose kernel
  have hk := Classical.choose_spec kernel
  let T := fun (q : (π × σ) × List α) => C *
    (cF * ((estate (st q q.2.length)).length+1) + (encPair estate (encList ea) q).length +
      (∑ j ∈ Finset.range q.2.length, R q j) + B q + 1)
  let S := fun (q : (π × σ) × List α) => C *
    (cF * ((estate (st q q.2.length)).length+1) + Q q + B q + 1)
  have realizes : ComputableInTimeAndSpace
      (fun q : (π × σ) × List α => q.2.foldl (step q.1.1) q.1.2)
      (encPair estate (encList ea)) es T S := by
    simpa only [Function.const_apply, stateEq, T, S, C, cF, estate] using
      hk.computableInTimeAndSpace
  let machine : NativeCertificate
      (fun q : (π × σ) × List α => q.2.foldl (step q.1.1) q.1.2)
      (encPair estate (encList ea)) es :=
    ⟨T, (fun q => S q + (es (q.2.foldl (step q.1.1) q.1.2)).length),
      ComputableInO.of_bounds realizes 1 (fun _ => by simp) (fun _ => by simp; omega)
        (fun _ => by simp; omega)⟩
  let ei := encPair ep (encPair es (encList ea))
  let original : NativeCertificate (id : π × (σ × List α) → _) ei ei :=
    .linear (.of_eq (fun _ => rfl))
  exact NativeCertificate.congr (machine.comp
    ((original.fst.prod original.snd.fst).prod original.snd.snd)) (fun _ => rfl)

end Cslib.GenericRAM.NativeCertificate
