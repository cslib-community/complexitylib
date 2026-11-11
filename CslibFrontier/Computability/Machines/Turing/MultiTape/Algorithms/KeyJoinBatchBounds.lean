/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatch
public import CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoinBatch
import all CslibFrontier.Computability.GenericRAM.Native.StreamingEmitBounds
import all CslibFrontier.Computability.GenericRAM.Native.StreamingFoldBounds
import all CslibFrontier.Computability.GenericRAM.Native.Combinators
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts

/-!
# Cumulative resources of actual bounded class windows

Use the installed scalar-state emitter, summing the encoded sizes of its groups.
The row-aligned window's population potential pays its actual emitted records;
no maximum-group-size times group-count charge is used for time. The actual
count/division/filter/cross callback profiles remain explicit in this envelope;
this does not establish the sharp global dissection resource theorem.

## Main results

* `window_state_wire`: binary scalar widths at every prefix, including endpoints.
* `window_prefix_population`, `window_emission_sum`: cumulative output populations.
* `windowCertificate_bounds`: installed time/workspace with cumulative group wires
  and actual callback sums/maxima, including internal tapes.
-/

public section
namespace Turing.MultiTapeTM.KeyJoinBatch
open Cslib.GenericRAM

private abbrev er := RadixPartition.recordEncoding
private abbrev el := encList er
private abbrev en := encPair encNat encNat

private theorem advance_le (bounds : ℕ × ℕ) (group : List SortedMatch.Record) :
    (advance bounds group).1 ≤ bounds.1 ∧ (advance bounds group).2 ≤ bounds.2 :=
  ⟨Nat.sub_le _ _, Nat.sub_le _ _⟩

private theorem state_le (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record))
    (j : ℕ) :
    (streamState bounds (fun q => advance q.1 q.2) groups j).1 ≤ bounds.1 ∧
      (streamState bounds (fun q => advance q.1 q.2) groups j).2 ≤ bounds.2 := by
  change ((groups.take j).foldl advance bounds).1 ≤ bounds.1 ∧
    ((groups.take j).foldl advance bounds).2 ≤ bounds.2
  have aux (rows : List (List SortedMatch.Record)) (b : ℕ × ℕ) :
      (rows.foldl advance b).1 ≤ b.1 ∧ (rows.foldl advance b).2 ≤ b.2 := by
    induction rows generalizing b with
    | nil => exact ⟨le_rfl, le_rfl⟩
    | cons g gs ih =>
      exact ⟨(ih (advance b g)).1.trans (advance_le b g).1,
        (ih (advance b g)).2.trans (advance_le b g).2⟩
  exact aux _ _

/-- Every prefix of the actual group scan retains only the original binary rank widths.
This includes the final state and permits empty groups and zero capacity. -/
theorem window_state_wire (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record))
    (j : ℕ) :
    (encPair encNat encNat (streamState bounds (fun q => advance q.1 q.2) groups j)).length ≤
      (encPair encNat encNat bounds).length := by
  have h := state_le bounds groups j
  have a := length_encNat_mono h.1
  have b := length_encNat_mono h.2
  simp only [length_encPair]
  omega

private theorem emission_potential (bounds : ℕ × ℕ) (group : List SortedMatch.Record) :
    (groupWindow bounds group).length+(advance bounds group).2 ≤ bounds.2+group.length := by
  have h := groupWindow_length bounds group
  have hmin := Nat.sub_add_min_cancel bounds.2 (KeyJoin.population group-bounds.1)
  dsimp only [advance]
  omega

/-- The actual emitted-prefix population plus remaining capacity is bounded by the original
capacity plus records read so far. This controls cumulative callback output,
including uneven groups. -/
theorem window_prefix_population (bounds : ℕ × ℕ)
    (groups : List (List SortedMatch.Record)) (n : ℕ) (hn : n ≤ groups.length) :
    (∑ j ∈ Finset.range n, if h : j < groups.length then
      (groupWindow (streamState bounds (fun q => advance q.1 q.2) groups j)
        groups[j]).length
      else 0)+
      (streamState bounds (fun q => advance q.1 q.2) groups n).2 ≤
        bounds.2+(groups.take n).flatten.length := by
  induction n with
  | zero => simp [streamState]
  | succ n ih =>
    have hlt : n < groups.length := by omega
    have prev := ih (by omega)
    have step := emission_potential
      (streamState bounds (fun q => advance q.1 q.2) groups n) groups[n]
    rw [Finset.sum_range_succ, dite_eq_left hlt, streamState_succ _ _ _ hlt]
    rw [List.take_succ_eq_append_getElem hlt, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.length_append]
    dsimp only at ⊢
    omega

/-- Sum of actual callback output sizes is linear in capacity plus quarter input records.
Uneven groups and collisions do not introduce an extra group-count factor. -/
theorem window_emission_sum (bounds : ℕ × ℕ) (groups : List (List SortedMatch.Record)) :
    (∑ j ∈ Finset.range groups.length, if h : j < groups.length then
      (groupWindow (streamState bounds (fun q => advance q.1 q.2) groups j) groups[j]).length
      else 0) ≤ bounds.2+groups.flatten.length := by
  have h := window_prefix_population bounds groups groups.length le_rfl
  rw [List.take_length] at h
  omega

private theorem group_wire_sum (groups : List (List SortedMatch.Record)) :
    (∑ j ∈ Finset.range groups.length, if h : j < groups.length then
      (el groups[j]).length else 0) = (el groups.flatten).length := by
  rw [Finset.sum_range]
  simp only [dite_eq_left (Fin.isLt _)]
  rw [← List.sum_ofFn
    (f := fun i : Fin groups.length => (el groups[(i : ℕ)]).length)]
  have mapped := List.map_ofFn (f := fun i : Fin groups.length => groups[(i : ℕ)])
    (g := fun group => (el group).length)
  simp only [List.ofFn_getElem, Function.comp_def] at mapped
  rw [← mapped]
  simp only [el, length_encList, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]

/-- Actual next-state and window-emission clocks at the visited scalar states. -/
noncomputable def windowCallbackTime (bounds : ℕ × ℕ)
    (groups : List (List SortedMatch.Record)) : ℕ :=
  ∑ j ∈ Finset.range groups.length, if h : j < groups.length then
    advanceCertificate.time
      (streamState bounds (fun q => advance q.1 q.2) groups j, groups[j])+
    groupWindowCertificate.time
      (streamState bounds (fun q => advance q.1 q.2) groups j, groups[j]) else 0

/-- Maximum actual callback workspace, including each callback's internal temporary tapes. -/
noncomputable def windowCallbackSpace (bounds : ℕ × ℕ)
    (groups : List (List SortedMatch.Record)) : ℕ :=
  (Finset.range groups.length).sup (fun j => if h : j < groups.length then
    advanceCertificate.space
      (streamState bounds (fun q => advance q.1 q.2) groups j, groups[j])+
    groupWindowCertificate.space
      (streamState bounds (fun q => advance q.1 q.2) groups j, groups[j]) else 0)

/-- The unchanged installed window certificate pays cumulative group wire size, rather than
maximum group size times the number of groups. Its remaining callback clocks are the actual
count/division/filter/cross profiles; they are not replaced by unit record costs. The space
bound includes materialized input/output and all intermediate callback/prefix tapes. -/
theorem windowCertificate_bounds : ∃ K : ℕ, ∀ bounds groups,
    windowCertificate.time (bounds, groups) ≤ K*(windowCallbackTime bounds groups+
      (encPair (encPair encNat encNat)
        (encList (encList RadixPartition.recordEncoding)) (bounds, groups)).length+
      (groups.length+1)*((encPair encNat encNat bounds).length+1)+
      2*(encList RadixPartition.recordEncoding groups.flatten).length+1) ∧
    windowCertificate.space (bounds, groups) ≤ K*(windowCallbackSpace bounds groups+
      (encPair (encPair encNat encNat)
        (encList (encList RadixPartition.recordEncoding)) (bounds, groups)).length+
      (encPair encNat encNat bounds).length+
      (encList RadixPartition.recordEncoding groups.flatten).length+
      (encList RadixPartition.recordEncoding (window bounds groups)).length+1) := by
  obtain ⟨K, bound⟩ := NativeCertificate.emitFoldCertificate_bounds en el er advance groupWindow
    advanceCertificate groupWindowCertificate
  refine ⟨K, ?_⟩
  intro bounds groups
  have stateWidth : NativeCertificate.foldStateWidth en
      (fun (_ : Unit) => advance) ((), (bounds, groups)) ≤ (en bounds).length := by
    apply Finset.sup_le
    intro j _
    exact window_state_wire bounds groups j
  have maxWire : streamRecordLength el groups ≤ (el groups.flatten).length := by
    apply listMax_le
    intro group hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have h := Finset.single_le_sum
      (f := fun j => if h : j < groups.length then (el groups[j]).length else 0)
      (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    rw [dite_eq_left hj, group_wire_sum] at h
    exact h
  have clocks :
      (∑ j ∈ Finset.range groups.length, if h : j < groups.length then
        advanceCertificate.time
          (streamState bounds (fun q => advance q.1 q.2) groups j, groups[j])+
        groupWindowCertificate.time
          (streamState bounds (fun q => advance q.1 q.2) groups j, groups[j])+
        (el groups[j]).length else 0) =
          windowCallbackTime bounds groups+(el groups.flatten).length := by
    rw [← group_wire_sum]
    dsimp only [windowCallbackTime]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [dite_eq_left (Finset.mem_range.mp hj), dite_eq_left (Finset.mem_range.mp hj),
      dite_eq_left (Finset.mem_range.mp hj)]
  have copies := Nat.mul_le_mul_left (groups.length+1) (Nat.add_le_add_right stateWidth 1)
  have actual := bound (bounds, groups)
  constructor
  · apply actual.1.trans
    apply Nat.mul_le_mul_left
    dsimp only [NativeCertificate.emitTimeBudget]
    rw [clocks]
    dsimp only [en, el, er] at *
    omega
  · apply actual.2.trans
    apply Nat.mul_le_mul_left
    change (encPair en (encList el) (bounds, groups)).length+
      windowCallbackSpace bounds groups+
      NativeCertificate.foldStateWidth en (fun (_ : Unit) => advance) ((), (bounds, groups))+
      streamRecordLength el groups+(el (window bounds groups)).length+1 ≤ _
    have copies' : NativeCertificate.foldStateWidth en
        (fun (_ : Unit) => advance) ((), (bounds, groups))+
        streamRecordLength el groups ≤ (en bounds).length+(el groups.flatten).length :=
      Nat.add_le_add stateWidth maxWire
    simpa only [en, el, er, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_left copies'
        ((encPair en (encList el) (bounds, groups)).length+windowCallbackSpace bounds groups))
        (el (window bounds groups)).length) 1

end Turing.MultiTapeTM.KeyJoinBatch
