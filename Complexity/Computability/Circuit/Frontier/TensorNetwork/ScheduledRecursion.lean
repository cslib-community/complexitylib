/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Recursion

/-!
# The contraction recursion with the parameter schedule

This file runs the contraction recursion (`TensorNetwork.contractRec`) with the parameter schedule
of [OpenAI2026ETH] (§D.4.2, (D.4)–(D.6), p. 58) from `Cslib.Circuits.Frontier.ContractionSchedule`,
so that its correctness and the running-time certificate refer to the same calls.

**The schedule of call parameters** (`ContractionSchedule.callParams s`). For size `s`, a call at
depth `d` with `M` edges is a leaf when `M ≤ H = leafSize s`. Otherwise it has `a = slotBits s d`
slot bits, taper `u = taper s d`, multiplicity step `h = ⌈3 M / u⌉` (`taperStep`), and degree
bound `Δ = degreeBound s`. Its children are recovered at the precisions `p_t = nodePrecision`.
Correctness of the recursion holds for this schedule as for every other
(`TensorNetwork.exists_contractRec_eq_add`).

**An active call.** At a call with `Active C s d M p` and `ActiveBounds C s d M p` (the certificate
`exists_activeBounds` gives the second from the first for `s ≥ s₀`) on a network that runs from
rows to columns with at most `Δ` ports at each end, and with at least `2 ^ (4 ⌊log₂ s⌋)`
interpolation points:

* the guard holds, so the call is the active call `callValue`
  (`contractRec_callParams_eq_callValue`);
* every lifted child runs from rows to columns within the degree bound
  (`TensorNetwork.rowsToColumnsLE_finLift_child`), has at most `M / 16` edges
  (`sixteen_mul_card_edges_child_le`), and is evaluated at a precision within the schedule
  (`nodePrecision_le_of_taperMult_pos`), so it is a leaf or an active call at depth `d + 1`
  (`Active.child`);
* there are at most `2 ^ e_d` mode tuples at each active node (`card_modeBudget_callParams_le`), and
  the nodes, points and groups contribute `2 ^ (2 ⌊log₂ s⌋)` (`ActiveBounds.branching_le`).

These are the per-call facts that a certificate of the running time instantiates along the
recursion tree.

## Main definitions

* `Cslib.Circuits.Frontier.ContractionSchedule.taperStep`: `h = ⌈3 M / u⌉`.
* `Cslib.Circuits.Frontier.ContractionSchedule.callParams`: the schedule of call parameters.

## Main results

* `Cslib.Circuits.Frontier.ContractionSchedule.ActiveBounds.admissible`: the parameters of an active
  call are admissible.
* `Cslib.Circuits.Frontier.ContractionSchedule.contractRec_callParams_eq_callValue`: an active call.
* `Cslib.Circuits.Frontier.ContractionSchedule.sixteen_mul_card_edges_child_le`,
  `Cslib.Circuits.Frontier.ContractionSchedule.nodePrecision_le_of_taperMult_pos`,
  `Cslib.Circuits.Frontier.ContractionSchedule.card_modeBudget_callParams_le`: its children and
  their number.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.2 (p. 58),
  §D.4.4–§D.4.7, pp. 60–64.
-/

public section

open Finset

namespace Cslib.Circuits.Frontier.ContractionSchedule

open TensorNetwork

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### The schedule of call parameters -/

/-- The multiplicity step `h = ⌈3 M / u⌉` of Lemma D.5 at depth `d`, with `u = taper s d`. -/
@[expose] def taperStep (s d M : ℕ) : ℕ :=
  (3 * M + taper s d - 1) / taper s d

theorem le_taperStep_mul {s d M : ℕ} (hu : 1 ≤ taper s d) :
    3 * M ≤ taperStep s d M * taper s d := by
  have h1 := Nat.lt_div_mul_add (a := 3 * M + taper s d - 1) (b := taper s d) (by omega)
  unfold taperStep
  generalize (3 * M + taper s d - 1) / taper s d * taper s d = y at h1 ⊢
  omega

theorem taperStep_mul_le (s d M : ℕ) : taperStep s d M * taper s d ≤ 3 * M + taper s d :=
  (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)

/-- **The schedule of call parameters** for size `s`: a call at depth `d` with `M` edges is a leaf
when `M ≤ leafSize s`, and otherwise has `a = slotBits s d`, `u = taper s d`, `h = ⌈3 M / u⌉` and
the degree bound `Δ = degreeBound s`. -/
@[expose] def callParams (s d M : ℕ) : Option CallParams :=
  if M ≤ leafSize s then none
  else some ⟨slotBits s d, taper s d, taperStep s d M, degreeBound s⟩

theorem callParams_of_le {s d M : ℕ} (h : M ≤ leafSize s) : callParams s d M = none :=
  ite_eq_left h

theorem callParams_of_lt {s d M : ℕ} (h : leafSize s < M) :
    callParams s d M = some ⟨slotBits s d, taper s d, taperStep s d M, degreeBound s⟩ :=
  ite_eq_right (not_le.mpr h)

/-- **The parameters of an active call are admissible**, given `2 ^ (4 ⌊log₂ s⌋)` interpolation
points. -/
theorem ActiveBounds.admissible {C s d M p : ℕ} (hB : ActiveBounds C s d M p) {N₀ : ℕ}
    (hN₀ : 2 ^ (4 * Nat.log 2 s) ≤ N₀) :
    (CallParams.mk (slotBits s d) (taper s d) (taperStep s d M) (degreeBound s)).Admissible M
      N₀ where
  one_le_u := hB.one_le_taper
  u_le_edges := hB.taper_le_edges
  u_le_a := by
    have := slotBits_eq s d
    simp only
    omega
  le_h_mul := le_taperStep_mul hB.one_le_taper
  h_mul_le := taperStep_mul_le s d M
  points_lt := by
    have := hB.points_le
    simp only
    omega

/-! ### An active call -/

section Active

variable {K : Type*} [CommRing K] [Algebra ℚ K] (B : Subring K)
  (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {N₀ : ℕ} (pts : Fin N₀ → B)

/-- **An active call of the scheduled recursion.** At an active call (`Active`, `ActiveBounds`) on a
network that runs from rows to columns within the degree bound, with at least
`2 ^ (4 ⌊log₂ s⌋)` interpolation points, the recursion is the active call `callValue` with the
packing of Lemma D.3 at `a = slotBits s d`, `u = taper s d` and `h = ⌈3 M / u⌉`, and recursive
calls at depth `d + 1` for the children. -/
theorem contractRec_callParams_eq_callValue {C s d n m p : ℕ}
    {N : TensorNetwork B Bool (Fin n) (Fin m)} {side : Fin n → Bool} (hA : Active C s d m p)
    (hAB : ActiveBounds C s d m p) (hN : N.RowsToColumnsLE side (degreeBound s))
    (hN₀ : 2 ^ (4 * Nat.log 2 s) ≤ N₀) :
    contractRec B hB (callParams s) pts d n m N side p =
      callValue B hB
        (fun n' m' N' side' p' =>
          if m' < m then contractRec B hB (callParams s) pts (d + 1) n' m' N' side' p'
          else N'.contraction)
        N side hN.side_src hN.side_tgt (PacketPacking.packing N.src N.tgt (slotBits s d) 64) p
        (taper s d) (taperStep s d m) (hAB.admissible hN₀).u_le_a
        fun k : Fin (m * (2 * 2 ^ slotBits s d - 1) + 1) =>
          pts (Fin.castLE (hAB.admissible hN₀).points_lt k) :=
  contractRec_eq_callValue (callParams_of_lt hA.leafSize_lt) ⟨hN, hAB.admissible hN₀⟩ p

variable {C s d n m p : ℕ} {N : TensorNetwork B Bool (Fin n) (Fin m)} {side : Fin n → Bool}

/-- **The children of an active call have at most `M / 16` edges**, as `Active.child` requires
(Lemma D.3 (3) under (D.6), `TensorNetwork.mul_card_edges_child_callSplitting_le`). -/
theorem sixteen_mul_card_edges_child_le (hAB : ActiveBounds C s d m p)
    (hN : N.RowsToColumnsLE side (degreeBound s)) (hua : taper s d ≤ slotBits s d) {t : ℤ}
    (ht : t ∈ recoveryNodes (slotBits s d)) (hq : 0 < taperMult (taper s d) (taperStep s d m) t)
    (z : B) (g : Fin 64) :
    16 * Fintype.card
        ({e // (callSplitting B hB N side hN.side_src hN.side_tgt
            (PacketPacking.packing N.src N.tgt (slotBits s d) 64) p (taper s d) (taperStep s d m)
            hua ht hq z).group (N.src e) = g} ⊕
          {e // (callSplitting B hB N side hN.side_src hN.side_tgt
            (PacketPacking.packing N.src N.tgt (slotBits s d) 64) p (taper s d) (taperStep s d m)
            hua ht hq z).group (N.tgt e) = g}) ≤
      m := by
  have h := mul_card_edges_child_callSplitting_le B hB N side hN.side_src hN.side_tgt hN.src_le
    hN.tgt_le (by rw [Fintype.card_fin]; exact hAB.degree_mul_pairs_sq_le) p (taper s d)
    (taperStep s d m) hua ht hq z g
  have := Fintype.card_fin m
  omega

/-- **The children of an active call are evaluated within the precision schedule**: a node of
positive multiplicity passes `p_t ≤ precisionBound C s (d + 1)` to its children. -/
theorem nodePrecision_le_of_taperMult_pos (hAB : ActiveBounds C s d m p) {t : ℤ}
    (hq : 0 < taperMult (taper s d) (taperStep s d m) t) :
    nodePrecision p (taperStep s d m) (slotBits s d) (Fintype.card (Fin m)) (padicValInt 2 t) ≤
      precisionBound C s (d + 1) := by
  rw [Fintype.card_fin]
  exact hAB.nodePrecision_le _ _ (padicValInt_lt_of_taperMult_pos_left hq) (taperStep_mul_le s d m)

omit [Algebra ℚ K] in
/-- **The mode count (D.15) at an active call**: at a node of positive multiplicity, there are at
most `2 ^ e_d` mode tuples for the packing of Lemma D.3, which has at most `3 M / L` packets. -/
theorem card_modeBudget_callParams_le (hA : Active C s d m p) (hAB : ActiveBounds C s d m p)
    (hN : N.RowsToColumnsLE side (degreeBound s)) {t : ℤ}
    (hq : 0 < taperMult (taper s d) (taperStep s d m) t) :
    #(modeBudget
        (fun Z : Fin (PacketPacking.packing N.src N.tgt (slotBits s d) 64).numPackets ×
            Fin (2 ^ (padicValInt 2 t + 1)) ×
            Fin (nodePrecision p (taperStep s d m) (slotBits s d) (Fintype.card (Fin m))
              (padicValInt 2 t)) => (Z.2.2 : ℕ) + 1)
        (nodePrecision p (taperStep s d m) (slotBits s d) (Fintype.card (Fin m))
          (padicValInt 2 t))) ≤
      2 ^ branchExponent C s d := by
  have hP := PacketPacking.numPackets_packing_mul_le N.src N.tgt (slotBits s d) 64 hN.src_le
    hN.tgt_le (by rw [Fintype.card_fin]; exact hAB.degree_mul_pairs_sq_le)
    (by rw [Fintype.card_fin]; exact hAB.slots_mul_pairs_le)
  rw [Fintype.card_fin] at hP ⊢
  exact hAB.card_modeBudget_le hA (padicValInt_lt_of_taperMult_pos_left hq)
    (taperStep_mul_le s d m) (by rwa [Fintype.card_fin])

end Active

end Cslib.Circuits.Frontier.ContractionSchedule
