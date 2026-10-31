/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.PolyTime.GreedySlotScore
public import Complexity.Foundations.Combinatorics.PacketPacking
import Complexity.Computability.PolyTime.GreedyLabelSchedule
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Foundations.Data.List.Lookup
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Data.List.GetD

/-!
# Computing the packing of Lemma D.3 in polynomial time

`Cslib.PacketPacking.packing` packs the edges of a bipartite multigraph into packets (Lemma D.3 of
[OpenAI2026ETH], §D.4.2, pp. 58–59). This file computes it natively, on vertices and edges
numbered by natural numbers, and proves that the result is exactly `packing`
(`nativePacking_eq`), so Lemma D.3 (1) and (3), `numPackets_packing_mul_le` and the `2M / r`
port bounds `row_ports_packing_le` and `col_ports_packing_le`, hold for the native output.

**Labels.** `labelPass` runs the conditional-expectation pass of `partialLabels` over the rows,
then the columns. For each slot it streams the `r ^ a` candidates in radix order with
`Cslib.BalancedSchedules.streamBestSlotLabel`, the selector of Lemma 4.5, scoring them by the
cleared incidence potential alone: the group term vanishes for zero variables
(`clearedJointScore_zero_one`). The candidate count is capped (`cappedLength`): when
`r ^ a ≤ M`, for `M` the number of edges, the selector streams all candidates, and otherwise it
streams one empty word. So every step runs in polynomial time, and under `r ^ a ≤ M`, which
(D.6) implies (`pow_le_card_of_packing`), the pass is exactly `partialLabels` (`labelPass_eq`).

**Packets.** `packingOfWords` follows `Packing.ofLabels`: it numbers the edges within their
classes (`classIndices`), takes the largest class (`maxLoadOf`) and the number of packets
(`numPacketsOf`), and gives each edge its packet (`packetOf`) and slot (`slotOf`) by the
arithmetic of `packetEquiv` and `BitString.equivFin`. `packetSymbols` decodes the symbols of a
packet. These are exact for any labels (`packingOfWords_eq`, `packetSymbols_eq`).

**Inputs.** The numbers of rows and columns and the label length are in unary, the alphabet size
and the `(row, column)` edges in binary (`encPackingInput`). The bound `r ^ a ≤ M` is not
checked: without it the native output is still computed in polynomial time, but it need not be
`packing`.

## Main definitions

* `Cslib.PacketPacking.cappedLength`: the label length streamed by the selector.
* `Cslib.PacketPacking.bestLabel`, `Cslib.PacketPacking.labelStep`,
  `Cslib.PacketPacking.labelPass`, `Cslib.PacketPacking.labelWords`: one selection, one step, the
  pass and the row and column words.
* `Cslib.PacketPacking.packingOfWords`, `Cslib.PacketPacking.nativePacking`: the packets and
  slots for given words, and the whole packing.
* `Cslib.PacketPacking.packetSymbols`: the symbols of a packet.
* `Cslib.PacketPacking.edgeList`, `Cslib.PacketPacking.encPackingInput`: the edges of a `Fin`
  multigraph as a list, and the input encoding.

## Main results

* `Cslib.PacketPacking.labelPass_eq`, `Cslib.PacketPacking.labelWords_eq`: the pass computes
  `partialLabels`, and the words are `rowLabels` and `colLabels`.
* `Cslib.PacketPacking.packingOfWords_eq`, `Cslib.PacketPacking.packetSymbols_eq`: the packets,
  slots and symbols of `Packing.ofLabels`.
* `Cslib.PacketPacking.nativePacking_eq`: the native packing is `packing`.
* `Cslib.PacketPacking.computableInPolyTime_labelWords`,
  `Cslib.PacketPacking.computableInPolyTime_packingOfWords`,
  `Cslib.PacketPacking.computableInPolyTime_nativePacking`,
  `Cslib.PacketPacking.computableInPolyTime_packetSymbols`: polynomial time.

## References

* [OpenAI2026ETH], Appendix D.4.2, Lemma D.3 and its proof, pp. 58–59.
-/

public section

namespace Cslib.PacketPacking

open Finset Cslib.BalancedSchedules Cslib.GenericRAM Turing.MultiTapeTM

/-! ### The label pass -/

/-- Partial row and column words, `none` where no label is fixed yet. -/
abbrev PartialWords : Type := List (Option (List ℕ)) × List (Option (List ℕ))

/-- The parameters of the pass: `(a, r)` and the incidences `(column, row)`. -/
abbrev LabelParams : Type := (ℕ × ℕ) × List (ℕ × ℕ)

/-- The label length that the selector streams: `a` when `r ^ a ≤ m`, so that there are at most
`m` candidates, and `0` otherwise. -/
@[expose] def cappedLength (a r m : ℕ) : ℕ := if r ^ a ≤ m then a else 0

/-- The label of a slot chosen by the conditional expectation of the incidence potential:
`streamBestSlotLabel` with no group term (zero variables) and unit weight, over the capped label
length. -/
@[expose] def bestLabel (p : LabelParams) (words : PartialWords) (slot : Bool × ℕ) : List ℕ :=
  let ((a, r), edges) := p
  streamBestSlotLabel 0 (cappedLength a r edges.length) r 1 edges words slot

/-- One step of the pass: a slot without a word gets `bestLabel`. -/
@[expose] def labelStep (p : LabelParams) (words : PartialWords) (slot : Bool × ℕ) :
    PartialWords :=
  if (readSlotSchedule slot words).isSome then words
  else updateSlotSchedules slot (some (bestLabel p words slot)) words

/-- The slots of the pass: the rows `(false, v)`, then the columns `(true, w)`. -/
@[expose] def labelSlots (nR nC : ℕ) : List (Bool × ℕ) :=
  (List.range nR).map (fun v => (false, v)) ++ (List.range nC).map fun w => (true, w)

/-- **The label pass** on `nR` rows and `nC` columns, with the edges given as `(row, column)`
pairs. -/
@[expose] def labelPass (nR nC a r : ℕ) (edges : List (ℕ × ℕ)) : PartialWords :=
  (labelSlots nR nC).foldl (labelStep ((a, r), edges.map Prod.swap))
    (List.replicate nR none, List.replicate nC none)

/-- **The row and column words**: the pass, with the zero word where none was fixed. -/
@[expose] def labelWords (nR nC a r : ℕ) (edges : List (ℕ × ℕ)) :
    List (List ℕ) × List (List ℕ) :=
  ((labelPass nR nC a r edges).1.map (·.getD (List.replicate a 0)),
    (labelPass nR nC a r edges).2.map (·.getD (List.replicate a 0)))

/-! ### Correctness -/

/-- The words `[r]^a` with digits in base `r`, in the radix order of the selector. -/
theorem labelCandidates_eq {r : ℕ} (hr : 1 ≤ r) (a : ℕ) :
    labelCandidates a r =
      (List.range (r ^ a)).map fun j => wordToSchedule hr a (decodeLabelWord r a j) := by
  apply List.ext_getElem (by simp [labelCandidates])
  intro j h₁ h₂
  simp only [labelCandidates, List.getElem_map, List.getElem_finRange, List.getElem_range]
  exact (wordToSchedule_decodeLabelWord_eq_finFunctionFinEquiv_symm hr a ⟨j, by simpa
    [labelCandidates] using h₁⟩).symm

/-- The enumeration of `Fin n` lists `0, …, n - 1`. -/
theorem toList_fin (n : ℕ) : FinEnum.toList (Fin n) = List.finRange n := by
  change (List.finRange (List.finRange n).dedup.length).map (List.finRange n).dedup.get = _
  rw [List.map_get_finRange, (List.nodup_finRange n).dedup]

/-- The second inequality of (D.6), `L D ≤ M`, implies that there are at most `M` candidate
labels. -/
theorem pow_le_card_of_packing {a r M : ℕ} (hr : 1 ≤ r) (hL : 2 ^ a * r ^ (2 * a) ≤ M) :
    r ^ a ≤ M :=
  (Nat.pow_le_pow_right hr (by omega)).trans ((Nat.le_mul_of_pos_left _ (Nat.two_pow_pos a)).trans
    hL)

/-- The first minimizer of a score over `0, …, K - 1` is the argmin. -/
private theorem argmin_map_range {α : Type} (g : ℕ → α) (f : α → ℚ) {K jStar : ℕ}
    (hle : ∀ j < K, f (g jStar) ≤ f (g j)) (hlt : ∀ j < jStar, f (g jStar) < f (g j))
    (hj : jStar < K) : ((List.range K).map g).argmin f = some (g jStar) := by
  induction K with
  | zero => omega
  | succ K ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, List.argmin_concat]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
    · rw [ih (fun j hj => hle j (Nat.lt_succ_of_lt hj)) hj']
      have : ¬ f (g K) < f (g jStar) := not_lt.mpr (hle K (Nat.lt_succ_self K))
      simp only [this, ↓reduceIte]
    · cases harg : ((List.range jStar).map g).argmin f with
      | none => rfl
      | some c =>
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp (List.argmin_mem harg)
        have := hlt j (List.mem_range.mp hj)
        simp only [this, ↓reduceIte]

/-- With zero variables and unit weight, the joint score of the selector is the cleared incidence
potential scaled by `r`, so it orders the candidates as `partialIncidencePotential` does. -/
theorem clearedJointScore_zero_one {E nC nR a r : ℕ} (hr : 1 ≤ r) (hE : 0 < E)
    (edge : Fin E → Fin nC × Fin nR) (rows : Fin nR → Option (Fin a → Fin r))
    (cols : Fin nC → Option (Fin a → Fin r)) :
    (clearedJointScore 0 a r 1 (edgesOfFin edge) (partialScheduleListOfFin rows)
      (partialScheduleListOfFin cols) : ℚ) =
      ((r : ℚ) * ((r ^ a : ℕ) : ℚ) ^ 2) * partialIncidencePotential edge rows cols := by
  have h := clearedIncidencePotential_eq_mul hr edge rows cols
  simp only [clearedJointScore, length_edgesOfFin, Nat.mul_one, Nat.mul_zero, hE.ne',
    ↓reduceIte, Nat.add_zero, max_eq_right (Nat.zero_le 1), Nat.cast_mul, h]
  ring

/-- Two scores that are the same positive multiple of two rationals compare as they do. -/
private theorem cast_le_lt_iff {s₁ s₂ : ℕ} {f₁ f₂ c : ℚ} (hc : 0 < c) (h₁ : (s₁ : ℚ) = c * f₁)
    (h₂ : (s₂ : ℚ) = c * f₂) : (s₁ ≤ s₂ ↔ f₁ ≤ f₂) ∧ (s₁ < s₂ ↔ f₁ < f₂) := by
  rw [← Nat.cast_le (α := ℚ), ← Nat.cast_lt (α := ℚ), h₁, h₂]
  exact ⟨mul_le_mul_iff_right₀ hc, mul_lt_mul_iff_right₀ hc⟩

section Bridge

variable {m nR nC a r : ℕ} [NeZero r] (rowOf : Fin m → Fin nR) (colOf : Fin m → Fin nC)

/-- Partial labels on `Fin` vertices as lists of words. -/
@[expose] def toWords
    (assigned : (Fin nR → Option (Fin a → Fin r)) × (Fin nC → Option (Fin a → Fin r))) :
    PartialWords :=
  (partialScheduleListOfFin assigned.1, partialScheduleListOfFin assigned.2)

/-- A row or column of `Fin` vertices as a slot of the pass. -/
@[expose] def slotPair : Fin nR ⊕ Fin nC → Bool × ℕ
  | .inl v => (false, v)
  | .inr w => (true, w)

include rowOf colOf in
/-- **One step of the pass** is one step of `greedyLabelPassBy` for the incidence potential,
when `r ^ a ≤ m`. -/
theorem labelStep_toWords (hK : r ^ a ≤ m)
    (assigned : (Fin nR → Option (Fin a → Fin r)) × (Fin nC → Option (Fin a → Fin r)))
    (s : Fin nR ⊕ Fin nC) :
    labelStep ((a, r), edgesOfFin fun e => (colOf e, rowOf e)) (toWords assigned) (slotPair s) =
      toWords (greedyLabelStepBy (partialIncidencePotential fun e => (colOf e, rowOf e))
        (labelCandidates a r) assigned s) := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  have hpos : 0 < r ^ a := Nat.pow_pos hr
  have hm : 0 < m := hpos.trans_le hK
  set edges := edgesOfFin fun e => (colOf e, rowOf e)
  have hcap : cappedLength a r edges.length = a := by
    simp only [cappedLength, edges, length_edgesOfFin, hK, ↓reduceIte]
  have hc : (0 : ℚ) < (r : ℚ) * ((r ^ a : ℕ) : ℚ) ^ 2 := by
    have : (0 : ℚ) < r := by exact_mod_cast hr
    have : (0 : ℚ) < ((r ^ a : ℕ) : ℚ) := by exact_mod_cast hpos
    positivity
  obtain ⟨jStar, hj, hw, hle, hlt⟩ :=
    exists_min_index_streamBestSlotLabel 0 a r 1 edges (toWords assigned) (slotPair s) hpos
  have hset (k : ℕ) {N : ℕ} (labels : Fin N → Option (Fin a → Fin r)) (i : Fin N) :=
    set_partialScheduleListOfFin (hr := hr) labels i (decodeLabelWord r a k)
      (length_decodeLabelWord r a k) (fun _ hx => mem_decodeLabelWord_lt hr hx)
  have hlen : (decodeLabelWord r a jStar).length = a := length_decodeLabelWord r a jStar
  have hdig : ∀ x ∈ decodeLabelWord r a jStar, x < r := fun _ hx => mem_decodeLabelWord_lt hr hx
  rcases s with v | w
  · have hread : readSlotSchedule (false, v) (toWords assigned) =
        (assigned.1 v).map scheduleToWord := by
      simp only [toWords, readSlotSchedule, Bool.false_eq_true, ↓reduceIte,
        partialScheduleListOfFin, List.getD_ofFn]
    cases hv : assigned.1 v with
    | some x => simp only [labelStep, slotPair, hread, hv, Option.map_some, Option.isSome_some,
        ↓reduceIte, greedyLabelStepBy]
    | none =>
      have harg : (labelCandidates a r).argmin (fun word => partialIncidencePotential
          (fun e => (colOf e, rowOf e)) (Function.update assigned.1 v (some word)) assigned.2) =
          some (wordToSchedule hr a (decodeLabelWord r a jStar)) := by
        rw [labelCandidates_eq hr]
        have hiff (i j : ℕ) := cast_le_lt_iff hc
          (s₁ := candidateSlotScore 0 a r 1 edges (toWords assigned) (false, v) i)
          (s₂ := candidateSlotScore 0 a r 1 edges (toWords assigned) (false, v) j)
          (by simp only [candidateSlotScore, toWords, updateSlotSchedules, Bool.false_eq_true,
                ↓reduceIte, hset i assigned.1 v]
              exact clearedJointScore_zero_one hr hm _ _ _)
          (by simp only [candidateSlotScore, toWords, updateSlotSchedules, Bool.false_eq_true,
                ↓reduceIte, hset j assigned.1 v]
              exact clearedJointScore_zero_one hr hm _ _ _)
        exact argmin_map_range _ _ (fun j hj' => (hiff jStar j).1.mp (hle j hj'))
          (fun j hj' => (hiff jStar j).2.mp (hlt j hj')) hj
      simp only [slotPair] at hw
      simp only [labelStep, slotPair, hread, hv, Option.map_none, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, greedyLabelStepBy, harg, bestLabel, hcap, hw]
      simp only [updateSlotSchedules, toWords, Bool.false_eq_true, ↓reduceIte,
        set_partialScheduleListOfFin (hr := hr) assigned.1 v _ hlen hdig]
  · have hread : readSlotSchedule (true, w) (toWords assigned) =
        (assigned.2 w).map scheduleToWord := by
      simp only [toWords, readSlotSchedule, ↓reduceIte, partialScheduleListOfFin, List.getD_ofFn]
    cases hw' : assigned.2 w with
    | some x => simp only [labelStep, slotPair, hread, hw', Option.map_some, Option.isSome_some,
        ↓reduceIte, greedyLabelStepBy]
    | none =>
      have harg : (labelCandidates a r).argmin (fun word => partialIncidencePotential
          (fun e => (colOf e, rowOf e)) assigned.1 (Function.update assigned.2 w (some word))) =
          some (wordToSchedule hr a (decodeLabelWord r a jStar)) := by
        rw [labelCandidates_eq hr]
        have hiff (i j : ℕ) := cast_le_lt_iff hc
          (s₁ := candidateSlotScore 0 a r 1 edges (toWords assigned) (true, w) i)
          (s₂ := candidateSlotScore 0 a r 1 edges (toWords assigned) (true, w) j)
          (by simp only [candidateSlotScore, toWords, updateSlotSchedules, ↓reduceIte,
                hset i assigned.2 w]
              exact clearedJointScore_zero_one hr hm _ _ _)
          (by simp only [candidateSlotScore, toWords, updateSlotSchedules, ↓reduceIte,
                hset j assigned.2 w]
              exact clearedJointScore_zero_one hr hm _ _ _)
        exact argmin_map_range _ _ (fun j hj' => (hiff jStar j).1.mp (hle j hj'))
          (fun j hj' => (hiff jStar j).2.mp (hlt j hj')) hj
      simp only [slotPair] at hw
      simp only [labelStep, slotPair, hread, hw', Option.map_none, Option.isSome_none,
        Bool.false_eq_true, ↓reduceIte, greedyLabelStepBy, harg, bestLabel, hcap, hw]
      simp only [updateSlotSchedules, toWords, ↓reduceIte,
        set_partialScheduleListOfFin (hr := hr) assigned.2 w _ hlen hdig]

/-- The edges of `rowOf` and `colOf` as `(row, column)` pairs. -/
@[expose] def edgeList : List (ℕ × ℕ) := List.ofFn fun e => ((rowOf e : ℕ), (colOf e : ℕ))

/-- **The pass computes `partialLabels`** when `r ^ a ≤ m`. -/
theorem labelPass_eq (hK : r ^ a ≤ m) :
    labelPass nR nC a r (edgeList rowOf colOf) = toWords (partialLabels rowOf colOf a r) := by
  have hedges : (edgeList rowOf colOf).map Prod.swap = edgesOfFin fun e => (colOf e, rowOf e) := by
    simp only [edgeList, edgesOfFin, List.map_ofFn, Function.comp_def, Prod.swap_prod_mk]
  have hslots : labelSlots nR nC =
      ((FinEnum.toList (Fin nR)).map Sum.inl ++ (FinEnum.toList (Fin nC)).map Sum.inr).map
        slotPair := by
    simp only [labelSlots, toList_fin, List.map_append, List.map_map, Function.comp_def, slotPair,
      ← List.map_coe_finRange_eq_range (n := nR), ← List.map_coe_finRange_eq_range (n := nC)]
  have hinit : (List.replicate nR (none : Option (List ℕ)), List.replicate nC none) =
      toWords ((fun _ => none, fun _ => none) :
        (Fin nR → Option (Fin a → Fin r)) × (Fin nC → Option (Fin a → Fin r))) := by
    simp only [toWords, partialScheduleListOfFin, Option.map_none, List.ofFn_const]
  rw [labelPass, hedges, hslots, List.foldl_map, hinit, partialLabels, greedyLabelPassBy]
  exact List.foldl_hom _ fun assigned s => labelStep_toWords rowOf colOf hK assigned s

/-- **The words are `rowLabels` and `colLabels`** when `r ^ a ≤ m`. -/
theorem labelWords_eq (hK : r ^ a ≤ m) :
    labelWords nR nC a r (edgeList rowOf colOf) =
      (List.ofFn fun v => scheduleToWord (rowLabels rowOf colOf a r v),
        List.ofFn fun w => scheduleToWord (colLabels rowOf colOf a r w)) := by
  have hzero : scheduleToWord (fun _ : Fin a => (0 : Fin r)) = List.replicate a 0 := by
    simp only [scheduleToWord, Fin.val_zero, List.ofFn_const]
  have hget {N : ℕ} (labels : Fin N → Option (Fin a → Fin r)) :
      (partialScheduleListOfFin labels).map (·.getD (List.replicate a 0)) =
        List.ofFn fun v => scheduleToWord (completeLabels labels (fun _ _ => 0) v) := by
    simp only [partialScheduleListOfFin, List.map_ofFn, Function.comp_def, completeLabels]
    congr 1
    funext v
    cases labels v <;> simp only [Option.map_none, Option.getD_none, Option.map_some,
      Option.getD_some, hzero]
  simp only [labelWords, labelPass_eq rowOf colOf hK, toWords, hget, rowLabels, colLabels]

end Bridge

/-! ### Polynomial time -/

/-- The parameters `((a, r), incidences)` of the pass: `a` in unary, `r` and the incidences in
binary. -/
@[expose] def encLabelParams : LabelParams ↪ List Bool :=
  encPair (encPair encUnary encNat) (encList (encPair encNat encNat))

/-- The inputs `((nR, nC, a), (r, edges))` of the packing: the numbers of rows and columns and the
label length `a` in unary, the alphabet size `r` and the `(row, column)` edges in binary. -/
abbrev PackingInput : Type := (ℕ × ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The encoding of `PackingInput`. -/
@[expose] def encPackingInput : PackingInput ↪ List Bool :=
  encPair (encPair encUnary (encPair encUnary encUnary)) (encPair encNat (encList (encPair encNat
    encNat)))

/-- A list has at most as many entries as its encoding has bits. -/
private theorem length_le_length_encList {α : Type} {enc : α ↪ List Bool} (l : List α) :
    l.length ≤ (encList enc l).length := by
  rw [length_encList]
  induction l with
  | nil => simp
  | cons _ _ ih => simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-- The capped label length, in unary. -/
private theorem computableInPolyTime_cappedLength :
    ComputableInPolyTime (fun p : LabelParams => cappedLength p.1.1 p.1.2 p.2.length)
      encLabelParams encUnary := by
  have hpow : ComputableInPolyTime (fun p : LabelParams => p.1.2 ^ p.1.1) encLabelParams encNat :=
    ComputableInPolyTime.binary_pow' (by unfold encLabelParams; fun_prop)
      (by unfold encLabelParams; fun_prop)
  have hm : ComputableInPolyTime (fun p : LabelParams => p.2.length) encLabelParams encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by unfold encLabelParams; fun_prop)
  have hc := ComputableInPolyTime.bool_not.comp (ComputableInPolyTime.binary_lt' hm hpow)
  have ha : ComputableInPolyTime (fun p : LabelParams => p.1.1) encLabelParams encUnary := by
    unfold encLabelParams; fun_prop
  refine (hc.ite' ha (.const 0)).of_enc_eq fun p => ?_
  simp only [Function.comp_apply, cappedLength, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not, not_lt]

/-- The selector input of `bestLabel`. -/
private def bestLabelIn (q : (LabelParams × PartialWords) × (Bool × ℕ)) : StreamSlotIn :=
  (((0, cappedLength q.1.1.1.1 q.1.1.1.2 q.1.1.2.length), (q.1.1.1.2, 1), q.1.1.2), (q.2, q.1.2))

/-- The encoding of the arguments of `bestLabel` and `labelStep`. -/
abbrev encStepIn : (LabelParams × PartialWords) × (Bool × ℕ) ↪ List Bool :=
  encPair (encPair encLabelParams encPartialSchedules) (encPair encBool encUnary)

private theorem computableInPolyTime_bestLabelIn :
    ComputableInPolyTime bestLabelIn encStepIn encStreamSlotIn := by
  have hcap := computableInPolyTime_cappedLength.comp
    (show ComputableInPolyTime (fun q : (LabelParams × PartialWords) × (Bool × ℕ) => q.1.1)
      encStepIn encLabelParams by fun_prop)
  unfold bestLabelIn encStreamSlotIn encScoreParams
  have h0 : ComputableInPolyTime (fun _ : (LabelParams × PartialWords) × (Bool × ℕ) => (0 : ℕ))
      encStepIn encUnary := .const 0
  refine ((h0.prod hcap).prod ?_).prod ?_
  · unfold encStepIn encLabelParams; fun_prop
  · unfold encStepIn; fun_prop

/-- **`bestLabel` is polynomial-time**: the capped selector streams at most `m + 1` candidates. -/
theorem computableInPolyTime_bestLabel :
    ComputableInPolyTime
      (fun (((p, words), slot) : (LabelParams × PartialWords) × (Bool × ℕ)) =>
        bestLabel p words slot)
      encStepIn (encList encNat) := by
  obtain ⟨poly, hpoly, -, hB⟩ := streamBestSlotCertificate_bounds
  let cIn := NativeCertificate.ofPolyTime computableInPolyTime_bestLabelIn
  have hIn := NativeCertificate.ofPolyTime_isPolynomial computableInPolyTime_bestLabelIn
  let c := streamBestSlotCertificate.comp cIn
  -- The selector streams `r ^ cappedLength … ≤ m + 1` candidates, `m ≤` the input length.
  have hcount (q : (LabelParams × PartialWords) × (Bool × ℕ)) :
      q.1.1.1.2 ^ cappedLength q.1.1.1.1 q.1.1.1.2 q.1.1.2.length + 1 ≤
        (encStepIn q).length + 2 := by
    have hm : q.1.1.2.length ≤ (encStepIn q).length := by
      refine (length_le_length_encList (enc := encPair encNat encNat) q.1.1.2).trans ?_
      simp only [encStepIn, encLabelParams, length_encPair]
      omega
    unfold cappedLength
    split_ifs with h
    · omega
    · simp only [pow_zero]; omega
  have hsize : PolyBounded (fun q => (encStepIn q).length)
      (fun q => poly (encStreamSlotIn (bestLabelIn q)).length) :=
    (PolyBounded.of_polynomiallyBounded (fun s => (encStreamSlotIn s).length) hpoly).comp
      computableInPolyTime_bestLabelIn.polyBounded_length
  have hc : c.IsPolynomial := by
    refine ⟨(hIn.1.add (((PolyBounded.self).add (.const 2)).mul hsize)).mono fun q => ?_,
      (hIn.2.add hsize).mono fun q => ?_⟩
    · exact Nat.add_le_add_left ((hB _).1.trans (Nat.mul_le_mul_right _ (hcount q))) _
    · exact Nat.add_le_add_left (hB _).2 _
  exact (c.polyTime hc).of_enc_eq fun ⟨⟨⟨_, _⟩, _⟩, _⟩ => rfl

/-- One step of the pass is polynomial-time. -/
theorem computableInPolyTime_labelStep :
    ComputableInPolyTime
      (fun (((p, words), slot) : (LabelParams × PartialWords) × (Bool × ℕ)) =>
        labelStep p words slot)
      encStepIn encPartialSchedules := by
  have hread : ComputableInPolyTime
      (fun q : (LabelParams × PartialWords) × (Bool × ℕ) => (readSlotSchedule q.2 q.1.2).isSome)
      encStepIn encBool :=
    ComputableInPolyTime.optionIsSome (computableInPolyTime_readSlotSchedule.comp
      (show ComputableInPolyTime (fun q : (LabelParams × PartialWords) × (Bool × ℕ) => (q.2, q.1.2))
        encStepIn _ by fun_prop))
  have hupd := computableInPolyTime_updateSlotSchedules.comp
    (show ComputableInPolyTime (fun q : (LabelParams × PartialWords) × (Bool × ℕ) =>
        ((q.2, some (bestLabel q.1.1 q.1.2 q.2)), q.1.2)) encStepIn
        (encPair (encPair (encPair encBool encUnary) (encOption (encList encNat)))
          encPartialSchedules) by
      refine ((ComputableInPolyTime.snd _ _).prod ?_).prod (by fun_prop)
      exact (ComputableInPolyTime.optionSome (encList encNat)).comp computableInPolyTime_bestLabel)
  exact hread.ite' (by fun_prop) hupd

/-- The invariant of the pass: two lists of the right lengths, holding words of the capped length
with digits below `max r 1`. -/
private def WordsInvariant (nR nC len r : ℕ) (words : PartialWords) : Prop :=
  words.1.length = nR ∧ words.2.length = nC ∧
    (∀ o ∈ words.1, ∀ w, o = some w → w.length = len ∧ ∀ y ∈ w, y < max r 1) ∧
    (∀ o ∈ words.2, ∀ w, o = some w → w.length = len ∧ ∀ y ∈ w, y < max r 1)

private theorem wordsInvariant_labelStep {nR nC a r : ℕ} {incidences : List (ℕ × ℕ)}
    {words : PartialWords}
    (h : WordsInvariant nR nC (cappedLength a r incidences.length) r words) (slot : Bool × ℕ) :
    WordsInvariant nR nC (cappedLength a r incidences.length) r
      (labelStep ((a, r), incidences) words slot) := by
  obtain ⟨h1, h2, hw1, hw2⟩ := h
  unfold labelStep
  split_ifs
  · exact ⟨h1, h2, hw1, hw2⟩
  have hlen := length_streamBestSlotLabel 0 (cappedLength a r incidences.length) r 1 incidences
    words slot
  have hdig {y : ℕ} (hy : y ∈ streamBestSlotLabel 0 (cappedLength a r incidences.length) r 1
      incidences words slot) : y < max r 1 :=
    mem_streamBestSlotLabel_lt_max 0 (cappedLength a r incidences.length) r 1 incidences words slot
      hy
  have hset {L : List (Option (List ℕ))} {i : ℕ}
      (hL : ∀ o ∈ L, ∀ w, o = some w →
        w.length = cappedLength a r incidences.length ∧ ∀ y ∈ w, y < max r 1) :
      ∀ o ∈ L.set i (some (bestLabel ((a, r), incidences) words slot)), ∀ w, o = some w →
        w.length = cappedLength a r incidences.length ∧ ∀ y ∈ w, y < max r 1 := by
    intro o ho w hw
    rcases List.mem_or_eq_of_mem_set ho with hmem | rfl
    · exact hL o hmem w hw
    · cases hw
      exact ⟨hlen, fun _ hy => hdig hy⟩
  unfold updateSlotSchedules
  split_ifs
  · exact ⟨h1, by rw [List.length_set, h2], hw1, hset hw2⟩
  · exact ⟨by rw [List.length_set, h1], h2, hset hw1, hw2⟩

/-- **The label pass is polynomial-time.** -/
theorem computableInPolyTime_labelPass :
    ComputableInPolyTime
      (fun (((nR, nC, a), r, edges) : PackingInput) => labelPass nR nC a r edges)
      encPackingInput encPartialSchedules := by
  have hpar : ComputableInPolyTime (fun x : PackingInput => ((x.1.2.2, x.2.1), x.2.2.map Prod.swap))
      encPackingInput encLabelParams := by
    unfold encPackingInput encLabelParams
    have h1 : ComputableInPolyTime (fun x : PackingInput => (x.1.2.2, x.2.1))
        (encPair (encPair encUnary (encPair encUnary encUnary))
          (encPair encNat (encList (encPair encNat encNat)))) (encPair encUnary encNat) := by
      fun_prop
    refine h1.prod ?_
    refine ComputableInPolyTime.mapWithInput (f := fun _ e => Prod.swap e) (by fun_prop) ?_
    exact (ComputableInPolyTime.snd _ _).snd'.prod (ComputableInPolyTime.snd _ _).fst'
  have hlist : ComputableInPolyTime (fun x : PackingInput => labelSlots x.1.1 x.1.2.1)
      encPackingInput (encList (encPair encBool encUnary)) := by
    unfold labelSlots encPackingInput
    exact ComputableInPolyTime.listAppend'
      (ComputableInPolyTime.mapWithInput (by fun_prop) (by fun_prop))
      (ComputableInPolyTime.mapWithInput (by fun_prop) (by fun_prop))
  have hinit : ComputableInPolyTime
      (fun x : PackingInput => ((List.replicate x.1.1 none, List.replicate x.1.2.1 none) :
        PartialWords)) encPackingInput encPartialSchedules := by
    unfold encPackingInput encPartialSchedules; fun_prop
  let bound (x : PackingInput) : ℕ :=
    2 * (2 * (encPackingInput x).length) *
      (2 * (encPackingInput x).length * (2 * (encPackingInput x).length + 1) + 3) + 1
  have hsize : PolyBounded (fun x => (encPackingInput x).length) bound := by
    have h := PolyBounded.self (size := fun x : PackingInput => (encPackingInput x).length)
    exact ((((PolyBounded.const 2).mul ((PolyBounded.const 2).mul h)).mul
      ((((PolyBounded.const 2).mul h).mul (((PolyBounded.const 2).mul h).add
        (.const 1))).add (.const 3))).add (.const 1))
  refine (ComputableInPolyTime.foldlWith_spec hpar hlist hinit computableInPolyTime_labelStep
    (fun x _ words => WordsInvariant x.1.1 x.1.2.1 (cappedLength x.1.2.2 x.2.1
      (x.2.2.map Prod.swap).length) x.2.1 words)
    (fun x => ?_) (fun x _ words slot _ h => wordsInvariant_labelStep h slot) hsize
    (fun x _ words _ h => ?_)).1
  · refine ⟨List.length_replicate, List.length_replicate, ?_, ?_⟩ <;>
      intro o ho w hw <;> rcases List.mem_replicate.mp ho with ⟨_, rfl⟩ <;> cases hw
  · obtain ⟨h1, h2, hw1, hw2⟩ := h
    refine (length_encPartialSchedules_le h1 h2 hw1 hw2).trans ?_
    obtain ⟨⟨nR, nC, a⟩, r, edges⟩ := x
    have hcap : cappedLength a r (edges.map Prod.swap).length ≤ a := by
      unfold cappedLength; split_ifs <;> omega
    have hr : (encNat r).length ≤ (encPackingInput ((nR, nC, a), r, edges)).length := by
      simp only [encPackingInput, length_encPair]; omega
    have hn : nR + nC ≤ 2 * (encPackingInput ((nR, nC, a), r, edges)).length := by
      simp only [encPackingInput, length_encPair, encUnary_apply, List.length_replicate]; omega
    have ha : a ≤ (encPackingInput ((nR, nC, a), r, edges)).length := by
      simp only [encPackingInput, length_encPair, encUnary_apply, List.length_replicate]; omega
    dsimp only [bound]
    gcongr
    · exact hcap.trans ha

/-- **The row and column words are polynomial-time.** -/
theorem computableInPolyTime_labelWords :
    ComputableInPolyTime
      (fun (((nR, nC, a), r, edges) : PackingInput) => labelWords nR nC a r edges)
      encPackingInput (encPair (encList (encList encNat)) (encList (encList encNat))) := by
  have hpass := computableInPolyTime_labelPass
  unfold encPartialSchedules at hpass
  have ha : ComputableInPolyTime (fun x : PackingInput => x.1.2.2) encPackingInput encUnary := by
    unfold encPackingInput; fun_prop
  unfold labelWords
  refine (ComputableInPolyTime.mapWithInput ((ComputableInPolyTime.fst _ _).comp hpass) ?_).prod
    (ComputableInPolyTime.mapWithInput ((ComputableInPolyTime.snd _ _).comp hpass) ?_) <;>
    exact ComputableInPolyTime.optionGetDWithInput (by fun_prop) (by fun_prop)

/-! ### Packets and slots -/

/-- The pairs of words at the two ends of the `(row, column)` edges. -/
@[expose] def edgeWordPairs (rowWords colWords : List (List ℕ)) (edges : List (ℕ × ℕ)) :
    List (List ℕ × List ℕ) :=
  edges.map fun e => (rowWords.getD e.1 [], colWords.getD e.2 [])

/-- The number of each edge within its class: how many earlier edges have the same pair of
words. -/
@[expose] def classIndices (pairs : List (List ℕ × List ℕ)) : List ℕ :=
  (List.range pairs.length).map fun i =>
    (List.range i).countP fun j => decide (pairs.getD j ([], []) = pairs.getD i ([], []))

/-- The largest class size: one more than the largest class number, or zero without edges. -/
@[expose] def maxLoadOf (indices : List ℕ) : ℕ :=
  (indices.map (· + 1)).foldl max 0

/-- The number of packets: the blocks of `2 ^ a` slots needed for the largest class, times the
`(r * r) ^ a` words of pairs of symbols. -/
@[expose] def numPacketsOf (a r : ℕ) (indices : List ℕ) : ℕ :=
  (maxLoadOf indices + (2 ^ a - 1)) / 2 ^ a * (r * r) ^ a

/-- The slot of an edge with row word `ρ`, column word `κ` and class number `c`. Where the two
symbols differ, digit `i` is `1` when the row symbol is the larger; where they agree, it is
digit `i` of `c`. -/
@[expose] def slotOf (a : ℕ) (ρ κ : List ℕ) (c : ℕ) : ℕ :=
  ((List.range a).map fun i =>
    if (if ρ.getD i 0 = κ.getD i 0 then c.testBit i else decide (κ.getD i 0 < ρ.getD i 0))
    then 2 ^ i else 0).sum

/-- The packet of an edge with row word `ρ`, column word `κ` and class number `c`: its block
`c / 2 ^ a`, and in each coordinate the sorted pair of symbols, swapped when digit `i` of `c` is
`1`, numbered as `Cslib.PacketPacking.packetEquiv` numbers them. -/
@[expose] def packetOf (a r : ℕ) (ρ κ : List ℕ) (c : ℕ) : ℕ :=
  ((List.range a).map fun i =>
    (if c.testBit i then min (ρ.getD i 0) (κ.getD i 0) + r * max (ρ.getD i 0) (κ.getD i 0)
      else max (ρ.getD i 0) (κ.getD i 0) + r * min (ρ.getD i 0) (κ.getD i 0)) * (r * r) ^ i).sum +
    (r * r) ^ a * (c / 2 ^ a)

/-- **The packing for given words**: the number of packets, and the packet and slot of each
`(row, column)` edge. -/
@[expose] def packingOfWords (a r : ℕ) (rowWords colWords : List (List ℕ))
    (edges : List (ℕ × ℕ)) : ℕ × List (ℕ × ℕ) :=
  (numPacketsOf a r (classIndices (edgeWordPairs rowWords colWords edges)),
    ((edgeWordPairs rowWords colWords edges).zip
      (classIndices (edgeWordPairs rowWords colWords edges))).map fun ((ρ, κ), c) =>
        (packetOf a r ρ κ c, slotOf a ρ κ c))

/-- **The packing of Lemma D.3**, natively: the row and column words, the number of packets, and
the packet and slot of each `(row, column)` edge. -/
@[expose] def nativePacking (nR nC a r : ℕ) (edges : List (ℕ × ℕ)) :
    (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) :=
  (labelWords nR nC a r edges,
    packingOfWords a r (labelWords nR nC a r edges).1 (labelWords nR nC a r edges).2 edges)

/-- The symbols of packet `p` in coordinate `i`, as `Packing.symbols` decodes them: digit `i` of
`p mod (r * r) ^ a` in base `r * r`, split into two digits in base `r` and sorted. -/
@[expose] def packetSymbols (a r p i : ℕ) : ℕ × ℕ :=
  let d := p % (r * r) ^ a / (r * r) ^ i % (r * r)
  (min (d / r) (d % r), max (d / r) (d % r))

section PacketBridge

variable {m nR nC a r : ℕ} (rowOf : Fin m → Fin nR) (colOf : Fin m → Fin nC)
  (ρ : Fin nR → Fin a → Fin r) (κ : Fin nC → Fin a → Fin r)

/-- A digit of a word. -/
private theorem getD_scheduleToWord (w : Fin a → Fin r) (i : Fin a) :
    (scheduleToWord w).getD i 0 = (w i : ℕ) := by
  rw [scheduleToWord, List.getD_ofFn]

/-- A running maximum is the maximum of the start and the list. -/
private theorem foldl_max_eq (l : List ℕ) (b : ℕ) :
    l.foldl max b = max b (l.foldr max 0) := by
  induction l generalizing b with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, List.foldr_cons, max_assoc]

/-- The words of the edges. -/
private theorem edgeWordPairs_eq :
    edgeWordPairs (List.ofFn fun v => scheduleToWord (ρ v))
        (List.ofFn fun w => scheduleToWord (κ w)) (edgeList rowOf colOf) =
      List.ofFn fun e => (scheduleToWord (ρ (rowOf e)), scheduleToWord (κ (colOf e))) := by
  simp only [edgeWordPairs, edgeList, List.map_ofFn, Function.comp_def, List.getD_ofFn]

/-- Counting earlier indices with a property counts the earlier edges with it. -/
private theorem countP_range_eq_card (P : Fin m → Prop) [DecidablePred P] (q : ℕ → Bool)
    (e : Fin m) (hq : ∀ j (hj : j < m), q j = decide (P ⟨j, hj⟩)) :
    (List.range e).countP q = #{e' | e' < e ∧ P e'} := by
  rw [List.countP_eq_length_filter, ← Finset.card_map Fin.valEmbedding,
    ← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext j
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_map, mem_filter,
    mem_univ, true_and, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨hj, hqj⟩
    have hjm : j < m := hj.trans e.isLt
    exact ⟨⟨j, hjm⟩, ⟨Fin.mk_lt_of_lt_val hj, by simpa [hq j hjm] using hqj⟩, rfl⟩
  · rintro ⟨e', ⟨he', hP⟩, rfl⟩
    exact ⟨he', by simpa [hq e' e'.isLt] using hP⟩

/-- The class numbers. -/
private theorem classIndices_eq [NeZero r] :
    classIndices (List.ofFn fun e => (scheduleToWord (ρ (rowOf e)), scheduleToWord (κ (colOf e)))) =
      List.ofFn (classIndex rowOf colOf ρ κ) := by
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  set p := fun e : Fin m => (scheduleToWord (ρ (rowOf e)), scheduleToWord (κ (colOf e)))
  apply List.ext_getElem (by simp [classIndices])
  intro i h₁ h₂
  have hi : i < m := by simpa using h₂
  simp only [classIndices, List.length_ofFn, List.getElem_map, List.getElem_range,
    List.getElem_ofFn]
  refine countP_range_eq_card _ _ ⟨i, hi⟩ fun j hj => ?_
  rw [show (List.ofFn p).getD j ([], []) = p ⟨j, hj⟩ from List.getD_ofFn p ⟨j, hj⟩ _,
    show (List.ofFn p).getD i ([], []) = p ⟨i, hi⟩ from List.getD_ofFn p ⟨i, hi⟩ _]
  simp only [p, pairLabel, Prod.mk.injEq]
  congr 1
  exact propext ⟨fun h => ⟨scheduleToWord_inj hr h.1, scheduleToWord_inj hr h.2⟩,
    fun h => ⟨h.1 ▸ rfl, h.2 ▸ rfl⟩⟩

/-- The largest class size. -/
private theorem maxLoadOf_eq :
    maxLoadOf (List.ofFn (classIndex rowOf colOf ρ κ)) = maxLoad rowOf colOf ρ κ := by
  rw [maxLoadOf, foldl_max_eq, maxLoad, Finset.sup_def, Fin.univ_val_map, Multiset.sup_coe,
    List.map_ofFn]
  simp only [Function.comp_def, Nat.zero_max, Nat.bot_eq_zero]

/-- The slots. -/
private theorem slotOf_eq (e : Fin m) :
    slotOf a (scheduleToWord (ρ (rowOf e))) (scheduleToWord (κ (colOf e)))
        (classIndex rowOf colOf ρ κ e) = ((Packing.ofLabels rowOf colOf ρ κ).slot e : ℕ) := by
  simp only [slotOf, List.sum_map_range, Packing.ofLabels, BitString.val_equivFin_eq_sum,
    slotBits, getD_scheduleToWord, Fin.val_inj, Fin.val_fin_lt]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp_all

/-- The packets. -/
private theorem packetOf_eq (e : Fin m) :
    packetOf a r (scheduleToWord (ρ (rowOf e))) (scheduleToWord (κ (colOf e)))
        (classIndex rowOf colOf ρ κ e) = ((Packing.ofLabels rowOf colOf ρ κ).packet e : ℕ) := by
  simp only [packetOf, List.sum_map_range, Packing.ofLabels, packetEquiv, packetData,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    finProdFinEquiv_apply_val, finFunctionFinEquiv_apply, Equiv.arrowCongr_apply,
    Function.comp_def, getD_scheduleToWord, Equiv.refl_symm]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (classIndex rowOf colOf ρ κ e).testBit i <;> simp [h, Fin.val_max, Fin.val_min]

/-- **The packing for given words** is `Packing.ofLabels`. -/
theorem packingOfWords_eq [NeZero r] :
    packingOfWords a r (List.ofFn fun v => scheduleToWord (ρ v))
        (List.ofFn fun w => scheduleToWord (κ w)) (edgeList rowOf colOf) =
      ((Packing.ofLabels rowOf colOf ρ κ).numPackets,
        List.ofFn fun e => (((Packing.ofLabels rowOf colOf ρ κ).packet e : ℕ),
          ((Packing.ofLabels rowOf colOf ρ κ).slot e : ℕ))) := by
  simp only [packingOfWords, edgeWordPairs_eq, classIndices_eq]
  refine Prod.ext ?_ ?_
  · simp only [numPacketsOf, maxLoadOf_eq, Packing.ofLabels, numBlocks]
  · apply List.ext_getElem (by simp)
    intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn, packetOf_eq, slotOf_eq]

/-- **The symbols of a packet** are those of `Packing.ofLabels`. -/
theorem packetSymbols_eq (p : Fin (Packing.ofLabels rowOf colOf ρ κ).numPackets)
    (i : Fin a) :
    packetSymbols a r p i = ((((Packing.ofLabels rowOf colOf ρ κ).symbols p i).1 : ℕ),
      (((Packing.ofLabels rowOf colOf ρ κ).symbols p i).2 : ℕ)) := by
  simp only [packetSymbols, Packing.ofLabels, packetEquiv, Equiv.symm_trans_apply,
    finProdFinEquiv_symm_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map,
    Equiv.arrowCongr_symm, Equiv.arrowCongr_apply, Function.comp_def, Equiv.refl_symm,
    Equiv.refl_apply, Fin.val_max, Fin.val_min, Fin.coe_divNat, Fin.coe_modNat,
    finFunctionFinEquiv_symm_apply_val]
  rfl

end PacketBridge

/-- **The native packing is the packing of Lemma D.3** when `r ^ a ≤ m`, which (D.6) implies
(`pow_le_card_of_packing`): the words of `rowLabels` and `colLabels`, the number of packets, and
the packet and slot of each edge. So Lemma D.3 (1) and (3) hold for its output. -/
theorem nativePacking_eq {m nR nC a r : ℕ} [NeZero r] (rowOf : Fin m → Fin nR)
    (colOf : Fin m → Fin nC) (hK : r ^ a ≤ m) :
    nativePacking nR nC a r (edgeList rowOf colOf) =
      ((List.ofFn fun v => scheduleToWord ((packing rowOf colOf a r).rowLabel v),
          List.ofFn fun w => scheduleToWord ((packing rowOf colOf a r).colLabel w)),
        (packing rowOf colOf a r).numPackets,
        List.ofFn fun e => (((packing rowOf colOf a r).packet e : ℕ),
          ((packing rowOf colOf a r).slot e : ℕ))) := by
  simp only [nativePacking, labelWords_eq rowOf colOf hK, packingOfWords_eq]
  rfl

/-- **Lemma D.3 (1) for the native packing.** Under (D.6), `2 Δ D² ≤ M` and `L D ≤ M`, the native
packing has at most `3M / L` packets. -/
theorem numPackets_nativePacking_mul_le {m nR nC a r Δ : ℕ} [NeZero r] (rowOf : Fin m → Fin nR)
    (colOf : Fin m → Fin nC) (hrow : ∀ v, #{e | rowOf e = v} ≤ Δ)
    (hcol : ∀ w, #{e | colOf e = w} ≤ Δ) (hM : 2 * Δ * (r ^ (2 * a)) ^ 2 ≤ m)
    (hL : 2 ^ a * r ^ (2 * a) ≤ m) :
    let (_, numPackets, _) := nativePacking nR nC a r (edgeList rowOf colOf)
    numPackets * 2 ^ a ≤ 3 * m := by
  dsimp only
  have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr (NeZero.ne r)
  rw [nativePacking_eq rowOf colOf (pow_le_card_of_packing hr hL)]
  simpa using numPackets_packing_mul_le rowOf colOf a r hrow hcol (by simpa using hM)
    (by simpa using hL)

/-! ### Polynomial time of the packets -/

/-- The inputs `(((a, r), (rowWords, colWords)), edges)` of `packingOfWords`: `a` in unary and the
rest in binary. -/
abbrev WordsInput : Type := ((ℕ × ℕ) × (List (List ℕ) × List (List ℕ))) × List (ℕ × ℕ)

/-- The encoding of `WordsInput`. -/
@[expose] def encWordsInput : WordsInput ↪ List Bool :=
  encPair (encPair (encPair encUnary encNat) (encPair (encList (encList encNat))
    (encList (encList encNat)))) (encList (encPair encNat encNat))

/-- The output encoding of `packingOfWords`: the number of packets and the `(packet, slot)` pairs,
in binary. -/
@[expose] def encPlacements : ℕ × List (ℕ × ℕ) ↪ List Bool :=
  encPair encNat (encList (encPair encNat encNat))

private theorem binary_add'' {α : Type} {input : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun x => f x + g x) input encNat :=
  ComputableInPolyTime.binary_add.comp (hf.prod hg)

private theorem binary_max' {α : Type} {input : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun x => max (f x) (g x)) input encNat :=
  ((ComputableInPolyTime.binary_lt' hf hg).ite' hg hf).of_enc_eq fun x => by
    by_cases h : f x < g x
    · simp [h, max_eq_right h.le]
    · simp [h, max_eq_left (not_lt.mp h)]

private theorem binary_min' {α : Type} {input : α ↪ List Bool} {f g : α → ℕ}
    (hf : ComputableInPolyTime f input encNat) (hg : ComputableInPolyTime g input encNat) :
    ComputableInPolyTime (fun x => min (f x) (g x)) input encNat :=
  ((ComputableInPolyTime.binary_lt' hf hg).ite' hf hg).of_enc_eq fun x => by
    by_cases h : f x < g x
    · simp [h, min_eq_left h.le]
    · simp [h, min_eq_right (not_lt.mp h)]

/-- The inputs `((a, r), (ρ, κ), c)` of `slotOf` and `packetOf`, with `c` in unary. -/
private abbrev encEdgeIn : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ ↪ List Bool :=
  encPair (encPair (encPair encUnary encNat) (encPair (encList encNat) (encList encNat))) encUnary

private theorem computableInPolyTime_slotOf :
    ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ =>
      slotOf q.1.1.1 q.1.2.1 q.1.2.2 q.2) encEdgeIn encNat := by
  unfold slotOf
  refine (show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
    (ComputableInPolyTime.mapWithInput (by fun_prop) ?_)
  let encI := encPair encEdgeIn encUnary
  have hx : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ =>
      p.1.1.2.1.getD p.2 0) encI encNat := by fun_prop
  have hy : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ =>
      p.1.1.2.2.getD p.2 0) encI encNat := by fun_prop
  have hc : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ => p.1.2)
      encI encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hi : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ => p.2)
      encI encUnary := by fun_prop
  have hbit := (ComputableInPolyTime.decide_eq' hx hy).ite'
    (ComputableInPolyTime.binary_testBit hc hi) (ComputableInPolyTime.binary_lt' hy hx)
  refine (hbit.ite' (ComputableInPolyTime.binary_two_pow.comp hi) (.const 0)).of_enc_eq
    fun p => ?_
  simp only [decide_eq_true_eq, Function.comp_apply]

private theorem computableInPolyTime_packetOf :
    ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ =>
      packetOf q.1.1.1 q.1.1.2 q.1.2.1 q.1.2.2 q.2) encEdgeIn encNat := by
  unfold packetOf
  have hr : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ => q.1.1.2)
      encEdgeIn encNat := by fun_prop
  have hrr : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ => q.1.1.2 * q.1.1.2)
      encEdgeIn encNat := ComputableInPolyTime.binary_mul' hr hr
  have hc : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ => q.2)
      encEdgeIn encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have ha : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ => q.1.1.1)
      encEdgeIn encUnary := by fun_prop
  have hblock : ComputableInPolyTime (fun q : ((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ =>
      (q.1.1.2 * q.1.1.2) ^ q.1.1.1 * (q.2 / 2 ^ q.1.1.1)) encEdgeIn encNat :=
    ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_pow' hrr ha)
      (ComputableInPolyTime.binary_div.comp (hc.prod (ComputableInPolyTime.binary_two_pow.comp ha)))
  let encI := encPair encEdgeIn encUnary
  have hx : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ =>
      p.1.1.2.1.getD p.2 0) encI encNat := by fun_prop
  have hy : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ =>
      p.1.1.2.2.getD p.2 0) encI encNat := by fun_prop
  have hr' : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ => p.1.1.1.2)
      encI encNat := by fun_prop
  have hmin := binary_min' hx hy
  have hmax := binary_max' hx hy
  have hi : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ => p.2)
      encI encUnary := by fun_prop
  have hc' : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ => p.1.2)
      encI encNat := ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hterm := (ComputableInPolyTime.binary_testBit hc' hi).ite'
    (binary_add'' hmin (ComputableInPolyTime.binary_mul' hr' hmax))
    (binary_add'' hmax (ComputableInPolyTime.binary_mul' hr' hmin))
  have hpow : ComputableInPolyTime (fun p : (((ℕ × ℕ) × (List ℕ × List ℕ)) × ℕ) × ℕ =>
      (p.1.1.1.2 * p.1.1.1.2) ^ p.2) encI encNat :=
    ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_mul' hr' hr') hi
  exact binary_add''
    ((show ComputableInPolyTime List.sum (encList encNat) encNat by fun_prop).comp
      (ComputableInPolyTime.mapWithInput (by fun_prop)
        (ComputableInPolyTime.binary_mul' hterm hpow))) hblock

private theorem computableInPolyTime_slotOf' {γ : Type} {encIn : γ ↪ List Bool}
    {a c : γ → ℕ} {ρ κ : γ → List ℕ} (ha : ComputableInPolyTime a encIn encUnary)
    (hρ : ComputableInPolyTime ρ encIn (encList encNat))
    (hκ : ComputableInPolyTime κ encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => slotOf (a x) (ρ x) (κ x) (c x)) encIn encNat := by
  have h := computableInPolyTime_slotOf.comp
    (((ha.prod (ComputableInPolyTime.const (encIn := encIn) (encOut := encNat) 0)).prod
      (hρ.prod hκ)).prod hc)
  exact h

private theorem computableInPolyTime_packetOf' {γ : Type} {encIn : γ ↪ List Bool}
    {a r c : γ → ℕ} {ρ κ : γ → List ℕ} (ha : ComputableInPolyTime a encIn encUnary)
    (hr : ComputableInPolyTime r encIn encNat)
    (hρ : ComputableInPolyTime ρ encIn (encList encNat))
    (hκ : ComputableInPolyTime κ encIn (encList encNat))
    (hc : ComputableInPolyTime c encIn encUnary) :
    ComputableInPolyTime (fun x => packetOf (a x) (r x) (ρ x) (κ x) (c x)) encIn encNat := by
  have h := computableInPolyTime_packetOf.comp (((ha.prod hr).prod (hρ.prod hκ)).prod hc)
  exact h

/-- A class number is below the number of edges. -/
private theorem mem_classIndices_lt {pairs : List (List ℕ × List ℕ)} {c : ℕ}
    (hc : c ∈ classIndices pairs) : c < pairs.length := by
  simp only [classIndices, List.mem_map, List.mem_range] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  exact (List.countP_le_length.trans (List.length_range).le).trans_lt hi

private theorem computableInPolyTime_edgeWordPairs :
    ComputableInPolyTime (fun y : WordsInput => edgeWordPairs y.1.2.1 y.1.2.2 y.2) encWordsInput
      (encList (encPair (encList encNat) (encList encNat))) := by
  unfold edgeWordPairs encWordsInput
  refine ComputableInPolyTime.mapWithInput (by fun_prop) ?_
  exact (ComputableInPolyTime.listGetD_binary [] (by fun_prop) (by fun_prop)).prod
    (ComputableInPolyTime.listGetD_binary [] (by fun_prop) (by fun_prop))

private theorem computableInPolyTime_classIndices :
    ComputableInPolyTime classIndices (encList (encPair (encList encNat) (encList encNat)))
      (encList encUnary) := by
  unfold classIndices
  let encP := encList (encPair (encList encNat) (encList encNat))
  refine ComputableInPolyTime.mapWithInput
    (ComputableInPolyTime.range.comp ((ComputableInPolyTime.length_list _).comp
      (ComputableInPolyTime.id' (encIn := encP)))) ?_
  refine ComputableInPolyTime.countPWithInput (ComputableInPolyTime.range.comp
    (ComputableInPolyTime.snd _ _)) ?_
  have hget := ComputableInPolyTime.listGetD (encA := encPair (encList encNat) (encList encNat))
    (encL := encP) ([], [])
  exact ComputableInPolyTime.decide_eq'
    (hget.comp ((by fun_prop :
      ComputableInPolyTime (fun q : (List (List ℕ × List ℕ) × ℕ) × ℕ => q.1.1)
        (encPair (encPair encP encUnary) encUnary) encP).prod (ComputableInPolyTime.snd _ _)))
    (hget.comp ((by fun_prop :
      ComputableInPolyTime (fun q : (List (List ℕ × List ℕ) × ℕ) × ℕ => q.1.1)
        (encPair (encPair encP encUnary) encUnary) encP).prod (by fun_prop)))

private theorem computableInPolyTime_maxLoadOf :
    ComputableInPolyTime (fun y : WordsInput =>
      maxLoadOf (classIndices (edgeWordPairs y.1.2.1 y.1.2.2 y.2))) encWordsInput encUnary := by
  have hcs := computableInPolyTime_classIndices.comp computableInPolyTime_edgeWordPairs
  unfold maxLoadOf
  have h1 : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.1.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by fun_prop
  have h2 : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => p.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by fun_prop
  have hstep : ComputableInPolyTime (fun p : (ℕ × ℕ) × ℕ => max p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encUnary) encUnary := by
    refine (ComputableInPolyTime.unary_add' h1 (ComputableInPolyTime.unary_sub' h2 h1)).of_enc_eq
      fun p => ?_
    congr 1
    omega
  have hlist : ComputableInPolyTime (fun y : WordsInput =>
      (classIndices (edgeWordPairs y.1.2.1 y.1.2.2 y.2)).map (· + 1)) encWordsInput
      (encList encUnary) :=
    ComputableInPolyTime.mapWithInput hcs (by fun_prop)
  have hgrowth : PolyBounded (fun y : WordsInput => (encWordsInput y).length)
      (fun y => (encWordsInput y).length + 1) := PolyBounded.self.add (.const 1)
  refine ComputableInPolyTime.foldlWith_of_bounded_growth (par := fun _ : WordsInput => (0 : ℕ))
    (step := fun _ s v => max s v) (encP := encUnary) (.const 0) hlist (.const 0) hstep
    hgrowth ?_
  intro y s v hv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hv
  have hlt := mem_classIndices_lt hc
  have hlen : (edgeWordPairs y.1.2.1 y.1.2.2 y.2).length ≤ (encWordsInput y).length := by
    refine (le_of_eq (List.length_map _)).trans ((length_le_length_encList
      (enc := encPair encNat encNat) y.2).trans ?_)
    simp only [encWordsInput, length_encPair]; omega
  simp only [encUnary_apply, List.length_replicate]
  omega

private theorem computableInPolyTime_numPacketsOf :
    ComputableInPolyTime (fun y : WordsInput =>
      numPacketsOf y.1.1.1 y.1.1.2 (classIndices (edgeWordPairs y.1.2.1 y.1.2.2 y.2)))
      encWordsInput encNat := by
  have ha : ComputableInPolyTime (fun y : WordsInput => y.1.1.1) encWordsInput encUnary := by
    unfold encWordsInput; fun_prop
  have hr : ComputableInPolyTime (fun y : WordsInput => y.1.1.2) encWordsInput encNat := by
    unfold encWordsInput; fun_prop
  have h2a := ComputableInPolyTime.binary_two_pow.comp ha
  have hload := ComputableInPolyTime.unary_to_binary.comp computableInPolyTime_maxLoadOf
  unfold numPacketsOf
  exact ComputableInPolyTime.binary_mul'
    (ComputableInPolyTime.binary_div.comp ((binary_add'' hload
      (ComputableInPolyTime.binary_sub' h2a (.const 1))).prod h2a))
    (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_mul' hr hr) ha)

/-- **The packing for given words is polynomial-time.** -/
theorem computableInPolyTime_packingOfWords :
    ComputableInPolyTime
      (fun ((((a, r), (rowWords, colWords)), edges) : WordsInput) =>
        packingOfWords a r rowWords colWords edges)
      encWordsInput encPlacements := by
  have hpairs := computableInPolyTime_edgeWordPairs
  have hcs := computableInPolyTime_classIndices.comp hpairs
  have hzip := (ComputableInPolyTime.zip _ _).comp (hpairs.prod hcs)
  let encQ := encPair encWordsInput (encPair (encPair (encList encNat) (encList encNat)) encUnary)
  have ha : ComputableInPolyTime (fun p : WordsInput × ((List ℕ × List ℕ) × ℕ) => p.1.1.1.1)
      encQ encUnary := by unfold encQ encWordsInput; fun_prop
  have hr : ComputableInPolyTime (fun p : WordsInput × ((List ℕ × List ℕ) × ℕ) => p.1.1.1.2)
      encQ encNat := by unfold encQ encWordsInput; fun_prop
  have hρ : ComputableInPolyTime (fun p : WordsInput × ((List ℕ × List ℕ) × ℕ) => p.2.1.1)
      encQ (encList encNat) := by unfold encQ; fun_prop
  have hκ : ComputableInPolyTime (fun p : WordsInput × ((List ℕ × List ℕ) × ℕ) => p.2.1.2)
      encQ (encList encNat) := by unfold encQ; fun_prop
  have hc : ComputableInPolyTime (fun p : WordsInput × ((List ℕ × List ℕ) × ℕ) => p.2.2)
      encQ encUnary := by unfold encQ; fun_prop
  have hstep := (computableInPolyTime_packetOf' ha hr hρ hκ hc).prod
    (computableInPolyTime_slotOf' ha hρ hκ hc)
  have hmap := ComputableInPolyTime.mapWithInput
    (f := fun (y : WordsInput) (q : (List ℕ × List ℕ) × ℕ) =>
      (packetOf y.1.1.1 y.1.1.2 q.1.1 q.1.2 q.2, slotOf y.1.1.1 q.1.1 q.1.2 q.2)) hzip hstep
  exact (computableInPolyTime_numPacketsOf.prod hmap).of_enc_eq fun _ => by congr 1

/-- The output encoding of `nativePacking`. -/
@[expose] def encNativePacking :
    (List (List ℕ) × List (List ℕ)) × ℕ × List (ℕ × ℕ) ↪ List Bool :=
  encPair (encPair (encList (encList encNat)) (encList (encList encNat))) encPlacements

/-- **The native packing is polynomial-time.** With `nativePacking_eq`, Lemma D.3's packing is
computable in polynomial time whenever `r ^ a` is at most the number of edges. -/
theorem computableInPolyTime_nativePacking :
    ComputableInPolyTime
      (fun (((nR, nC, a), r, edges) : PackingInput) => nativePacking nR nC a r edges)
      encPackingInput encNativePacking := by
  have hW := computableInPolyTime_labelWords
  have har : ComputableInPolyTime (fun x : PackingInput => (x.1.2.2, x.2.1)) encPackingInput
      (encPair encUnary encNat) := by unfold encPackingInput; fun_prop
  have hedges : ComputableInPolyTime (fun x : PackingInput => x.2.2) encPackingInput
      (encList (encPair encNat encNat)) := by unfold encPackingInput; fun_prop
  have hin : ComputableInPolyTime (fun x : PackingInput =>
      (((x.1.2.2, x.2.1), labelWords x.1.1 x.1.2.1 x.1.2.2 x.2.1 x.2.2), x.2.2))
      encPackingInput encWordsInput := by
    unfold encWordsInput
    exact (har.prod hW).prod hedges
  have h := computableInPolyTime_packingOfWords.comp hin
  have h' := hW.prod h
  exact h'

/-- **The symbols of a packet are polynomial-time**, with `a` and `i` in unary. -/
theorem computableInPolyTime_packetSymbols {γ : Type} {encIn : γ ↪ List Bool}
    {a r p i : γ → ℕ} (ha : ComputableInPolyTime a encIn encUnary)
    (hr : ComputableInPolyTime r encIn encNat) (hp : ComputableInPolyTime p encIn encNat)
    (hi : ComputableInPolyTime i encIn encUnary) :
    ComputableInPolyTime (fun x => packetSymbols (a x) (r x) (p x) (i x)) encIn
      (encPair encNat encNat) := by
  have hrr := ComputableInPolyTime.binary_mul' hr hr
  have hd : ComputableInPolyTime (fun x => p x % (r x * r x) ^ a x / (r x * r x) ^ i x %
      (r x * r x)) encIn encNat :=
    ComputableInPolyTime.binary_mod.comp ((ComputableInPolyTime.binary_div.comp
      ((ComputableInPolyTime.binary_mod.comp (hp.prod (ComputableInPolyTime.binary_pow' hrr
        ha))).prod (ComputableInPolyTime.binary_pow' hrr hi))).prod hrr)
  have hq := ComputableInPolyTime.binary_div.comp (hd.prod hr)
  have hm := ComputableInPolyTime.binary_mod.comp (hd.prod hr)
  have h := (binary_min' hq hm).prod (binary_max' hq hm)
  exact h

end Cslib.PacketPacking
