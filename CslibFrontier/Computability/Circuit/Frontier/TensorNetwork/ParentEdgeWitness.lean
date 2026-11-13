/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.NativeChild
public import CslibFrontier.Foundations.Data.BitString.List.LowBits
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.SortedCount
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Intervals

/-!
# Verifying a parent edge without constructing a child graph

The native child numbers row ports first and column ports second. A proposed parent edge is
correct exactly when its selected endpoint belongs to the child group and its predecessor count,
with the row-port offset for a column, is the proposed child index. The characterization includes
the child-index bound: the default edge zero returned by an out-of-range `getD` is not a witness.

`parentEdge_witness_iff_bits` replaces the two counts by finite-width bit tests, sharing one
certified row total between the offset and the row/column decision. Each summand examines one
parent edge. Counts may equal the number of edges, so `clog 2 (edgeCount + 1)` bits suffice;
using the rank-only width `clog 2 edgeCount` would lose the all-row case at a power of two.

These are semantic verification contracts, not a native running-time bound. They do not make
list lookup, recursive endpoint access, group-label access, or counting free. A machine using
them must implement and charge those operations on its actual representation.

## Main results

* `NativeChild.parentEdge_witness_iff`: exact bounded parent-edge witnesses.
* `NativeChild.portRank_eq_sum_predecessors`: one Boolean test per possible predecessor.
* `NativeChild.parentEdge_witness_iff_bits`: witnesses checked through bounded count bits.
-/

public section

namespace Cslib.Circuits.Frontier.NativeChild

open Cslib.BitString

variable (groups : List ℕ) (g : ℕ) (ends : List (ℕ × ℕ))

private theorem portRank_spec (sel : ℕ × ℕ → ℕ) {e : ℕ} (he : e < ends.length)
    (hgroup : groups.getD (sel (ends.getD e (0, 0))) 0 = g) :
    ∃ h : portRank groups g ends sel e < (portEdges groups g ends sel).length,
      (portEdges groups g ends sel)[portRank groups g ends sel e]'h = e := by
  have h := List.getElem?_filter_countP_take
    (fun e' => decide (groups.getD (sel (ends.getD e' (0, 0))) 0 = g))
    (l := List.range ends.length) (r := e) (by simpa using he) (by simpa using hgroup)
  simpa [portEdges, portRank, List.take_range, min_eq_left he.le] using
    List.getElem?_eq_some_iff.mp h

private theorem getD_portEdges_eq_iff (sel : ℕ × ℕ → ℕ) {j e : ℕ}
    (hj : j < (portEdges groups g ends sel).length) :
    (portEdges groups g ends sel).getD j 0 = e ↔
      e < ends.length ∧ groups.getD (sel (ends.getD e (0, 0))) 0 = g ∧
        portRank groups g ends sel e = j := by
  rw [List.getD_eq_getElem _ _ hj]
  constructor
  · intro h
    have hmem : e ∈ portEdges groups g ends sel := h ▸ List.getElem_mem hj
    obtain ⟨he, hg⟩ := List.mem_filter.mp hmem
    have he' : e < ends.length := List.mem_range.mp he
    have hg' : groups.getD (sel (ends.getD e (0, 0))) 0 = g := of_decide_eq_true hg
    obtain ⟨hr, hget⟩ := portRank_spec groups g ends sel he' hg'
    refine ⟨he', hg', ?_⟩
    exact ((List.nodup_range (n := ends.length)).filter _).getElem_inj_iff.mp (hget.trans h.symm)
  · rintro ⟨he, hg, rfl⟩
    exact (portRank_spec groups g ends sel he hg).choose_spec

/-- A valid child edge has precisely the parent edges certified by endpoint membership and
the appropriate predecessor rank. Both row and column witnesses exclude padded indices. -/
theorem parentEdge_witness_iff (j e : ℕ) :
    (j < (portEdges groups g ends Prod.fst).length +
        (portEdges groups g ends Prod.snd).length ∧ parentEdge groups g ends j = e) ↔
      e < ends.length ∧
        ((groups.getD (ends.getD e (0, 0)).1 0 = g ∧ portRank groups g ends Prod.fst e = j) ∨
          (groups.getD (ends.getD e (0, 0)).2 0 = g ∧
            (portEdges groups g ends Prod.fst).length +
              portRank groups g ends Prod.snd e = j)) := by
  constructor
  · rintro ⟨hj, hparent⟩
    by_cases hr : j < (portEdges groups g ends Prod.fst).length
    · rw [parentEdge, ite_eq_left hr] at hparent
      obtain ⟨he, hg, hrank⟩ := (getD_portEdges_eq_iff groups g ends Prod.fst hr).mp hparent
      exact ⟨he, Or.inl ⟨hg, hrank⟩⟩
    · rw [parentEdge, ite_eq_right hr] at hparent
      have hc : j - (portEdges groups g ends Prod.fst).length <
          (portEdges groups g ends Prod.snd).length := by omega
      obtain ⟨he, hg, hrank⟩ := (getD_portEdges_eq_iff groups g ends Prod.snd hc).mp hparent
      exact ⟨he, Or.inr ⟨hg, by omega⟩⟩
  · rintro ⟨he, ⟨hg, hrank⟩ | ⟨hg, hrank⟩⟩
    · obtain ⟨hr, _⟩ := portRank_spec groups g ends Prod.fst he hg
      have hj : j < (portEdges groups g ends Prod.fst).length := by omega
      refine ⟨by omega, ?_⟩
      rw [parentEdge, ite_eq_left hj]
      exact (getD_portEdges_eq_iff groups g ends Prod.fst hj).mpr ⟨he, hg, hrank⟩
    · obtain ⟨hc, _⟩ := portRank_spec groups g ends Prod.snd he hg
      have hj : ¬j < (portEdges groups g ends Prod.fst).length := by omega
      refine ⟨by omega, ?_⟩
      rw [parentEdge, ite_eq_right hj]
      exact (getD_portEdges_eq_iff groups g ends Prod.snd (by omega)).mpr
        ⟨he, hg, by omega⟩

/-- One predecessor test reads the group of one selected endpoint and compares the edge index
with the prefix bound. Sums below range over actual edges, never default list padding. -/
@[expose] def portPredecessor (sel : ℕ × ℕ → ℕ) (bound : ℕ)
    (candidate : ℕ) : Bool :=
  decide (candidate < bound ∧
    groups.getD (sel (ends.getD candidate (0, 0))) 0 = g)

/-- A prefix rank, including the total at `bound = ends.length`, is a sum of bounded endpoint
tests. The prefix bound prevents the native rank's default-padding behavior past the edge list. -/
theorem portRank_eq_sum_predecessors (sel : ℕ × ℕ → ℕ) {bound : ℕ}
    (hbound : bound ≤ ends.length) :
    portRank groups g ends sel bound =
      ∑ candidate : Fin ends.length, (portPredecessor groups g ends sel bound candidate).toNat := by
  have hr : (List.range ends.length).filter (fun e => e < bound) = List.range bound := by
    simpa only [List.Ico.zero_bot] using List.Ico.filter_lt_of_ge (n := 0) hbound
  rw [portRank, ← hr, List.countP_filter, ← List.map_coe_finRange_eq_range,
    ← List.ofFn_eq_map, List.countP_ofFn]
  refine Finset.sum_congr rfl fun candidate _ => ?_
  simp [portPredecessor, Bool.toNat, cond_eq_ite, and_comm]

/-- The number of selected ports is the full-prefix rank. -/
theorem length_portEdges_eq_portRank (sel : ℕ × ℕ → ℕ) :
    (portEdges groups g ends sel).length = portRank groups g ends sel ends.length := by
  rw [portEdges, ← List.countP_eq_length_filter]
  rfl

/-- A bounded count proposal is correct exactly when all its low bits match the predecessor
sum. The strict edge-count bound accommodates a full prefix containing every edge. -/
theorem eq_portRank_iff_predecessor_bits (sel : ℕ × ℕ → ℕ) {bound width guess : ℕ}
    (hbound : bound ≤ ends.length) (hwidth : ends.length < 2 ^ width)
    (hguess : guess < 2 ^ width) :
    guess = portRank groups g ends sel bound ↔
      ∀ bit : Fin width, guess.testBit bit.val =
        (∑ candidate : Fin ends.length,
          (portPredecessor groups g ends sel bound candidate).toNat).testBit bit.val := by
  rw [← portRank_eq_sum_predecessors groups g ends sel hbound]
  constructor
  · rintro rfl bit
    rfl
  · intro h
    have hrank : portRank groups g ends sel bound ≤ bound :=
      (List.countP_le_length).trans_eq List.length_range
    apply lowBits_injective_of_lt hguess (hrank.trans_lt (hbound.trans_lt hwidth))
    rw [lowBits_eq_ofFn, lowBits_eq_ofFn]
    exact congrArg List.ofFn (funext h)

/-- `clog 2 (edgeCount + 1)` handles zero edges, full prefixes, and power-of-two edge counts. -/
theorem eq_portRank_iff_clog_predecessor_bits (sel : ℕ × ℕ → ℕ) {bound guess : ℕ}
    (hbound : bound ≤ ends.length) (hguess : guess < 2 ^ Nat.clog 2 (ends.length + 1)) :
    guess = portRank groups g ends sel bound ↔
      ∀ bit : Fin (Nat.clog 2 (ends.length + 1)), guess.testBit bit.val =
        (∑ candidate : Fin ends.length,
          (portPredecessor groups g ends sel bound candidate).toNat).testBit bit.val :=
  eq_portRank_iff_predecessor_bits groups g ends sel hbound
    (Nat.lt_of_lt_of_le (by omega) (Nat.le_pow_clog (by decide) _)) hguess

/-- Once the row total is certified, a proposed parent is checked using endpoint membership
and the bits of one prefix count. Row and column branches use the same certified offset.
The right side contains no filtered port list or child-network construction. -/
theorem parentEdge_witness_iff_bits {width rows j e : ℕ}
    (hwidth : ends.length < 2 ^ width) (hrows : rows < 2 ^ width)
    (hrowBits : ∀ bit : Fin width, rows.testBit bit.val =
      (∑ candidate : Fin ends.length,
        (portPredecessor groups g ends Prod.fst ends.length candidate).toNat).testBit bit.val) :
    (j < (portEdges groups g ends Prod.fst).length +
        (portEdges groups g ends Prod.snd).length ∧ parentEdge groups g ends j = e) ↔
      e < ends.length ∧
        ((groups.getD (ends.getD e (0, 0)).1 0 = g ∧ j < 2 ^ width ∧
            ∀ bit : Fin width, j.testBit bit.val =
              (∑ candidate : Fin ends.length,
                (portPredecessor groups g ends Prod.fst e candidate).toNat).testBit bit.val) ∨
          (groups.getD (ends.getD e (0, 0)).2 0 = g ∧ rows ≤ j ∧ j - rows < 2 ^ width ∧
            ∀ bit : Fin width, (j - rows).testBit bit.val =
              (∑ candidate : Fin ends.length,
                (portPredecessor groups g ends Prod.snd e candidate).toNat).testBit bit.val)) := by
  have hrowsEq : rows = (portEdges groups g ends Prod.fst).length := by
    rw [length_portEdges_eq_portRank]
    exact (eq_portRank_iff_predecessor_bits groups g ends Prod.fst le_rfl hwidth hrows).mpr
      hrowBits
  rw [parentEdge_witness_iff]
  constructor
  · rintro ⟨he, ⟨hg, hrank⟩ | ⟨hg, hrank⟩⟩
    · have hj : j < 2 ^ width := by
        have hrankLe : portRank groups g ends Prod.fst e ≤ e :=
          List.countP_le_length.trans_eq List.length_range
        omega
      exact ⟨he, Or.inl ⟨hg, hj,
        (eq_portRank_iff_predecessor_bits groups g ends Prod.fst he.le hwidth hj).mp
          hrank.symm⟩⟩
    · have hj : j - rows < 2 ^ width := by
        have hrankLe : portRank groups g ends Prod.snd e ≤ e :=
          List.countP_le_length.trans_eq List.length_range
        omega
      refine ⟨he, Or.inr ⟨hg, by omega, hj, ?_⟩⟩
      exact (eq_portRank_iff_predecessor_bits groups g ends Prod.snd he.le hwidth hj).mp
        (by omega)
  · rintro ⟨he, ⟨hg, hj, hbits⟩ | ⟨hg, hrow, hj, hbits⟩⟩
    · exact ⟨he, Or.inl ⟨hg,
        ((eq_portRank_iff_predecessor_bits groups g ends Prod.fst he.le hwidth hj).mpr
          hbits).symm⟩⟩
    · have hcount :=
        (eq_portRank_iff_predecessor_bits groups g ends Prod.snd he.le hwidth hj).mpr hbits
      exact ⟨he, Or.inr ⟨hg, by omega⟩⟩

end Cslib.Circuits.Frontier.NativeChild
