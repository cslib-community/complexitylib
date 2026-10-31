/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ActiveCall
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Reindex
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Schedule

/-!
# The contraction recursion and its correctness

This file assembles the recursive contraction algorithm of [OpenAI2026ETH] (§D.4.7, p. 64) from
its active calls, and proves it correct by induction from the leaves.

**One node** (`TensorNetwork.nodeSplitting`). For a network whose edges run from rows to columns,
a packing `Q` of its edges into packets of `2 ^ a` slots, and a nonzero grid point `t` of
valuation `i < a`, group the vertices by their symbol in coordinate `i` of `Q` (`packingGroup`).
The packing bridge `packingGroup_src_tgt` orients the groups, so the Cauchy matrix at
`T = t + α ζ` has the mode splitting `TensorNetwork.cauchyModeSplitting` (§D.4.5, p. 62). At a call
with input precision `p`, `TensorNetwork.callSplitting` is this splitting for the network reduced
modulo `2 ^ p_t`, `p_t = p + 8 h D_t + 8 M (a + 1)`: the schedule's
`ContractionSchedule.nodePrecision` at the valuation of `t`, the precision of Lemma D.5.

**One call from its children.** If every value `v t k` reduces modulo `2 ^ p_t` to the sum over
the mode tuples of the products of the contractions of the children (the right side of (D.16)),
then interpolation and tapered recovery return the contraction modulo `2 ^ p`
(`TensorNetwork.exists_recoverFromValues_eq_add_of_children`). The children's contractions may
come from any *contraction oracle* (`TensorNetwork.ContractionOracle`) that is correct modulo the
precision it is given: a child over `B ⧸ (2 ^ p_t)` is lifted to `B` along a section of the
reduction and renumbered by `Fin` (`TensorNetwork.finLift`,
`TensorNetwork.ContractionOracle.evalLift`), and the oracle's value then reduces to its contraction
(`TensorNetwork.ContractionOracle.mk_evalLift`). The value of
an active node is `TensorNetwork.nodeValue`, the values of a call are `TensorNetwork.callValues`,
and the recovered value is `TensorNetwork.callValue`
(`TensorNetwork.exists_callValue_eq_add`).

**The recursion** (`TensorNetwork.contractRec`). A call receives a network on `Fin n` vertices
and `Fin m` edges, its sides, its depth `d` and its precision `p`. A *schedule* gives the
parameters `a`, `u`, `h` and the degree bound `Δ` of a call from its depth and its number of edges
(`CallParams`), or none at a leaf; the manuscript's schedule is
`ContractionSchedule.callParams`. The call is active when its guard holds (`CallParams.Guard`):
the parameters meet the hypotheses of Lemma D.5 (`CallParams.Admissible`, with `u ≤ a` and enough
interpolation points), and the network runs from rows to columns with at most `Δ` ports at each
end of each vertex (`TensorNetwork.RowsToColumnsLE`). It packs the edges with
`PacketPacking.packing` (Lemma D.3, `r = 64`), takes the first `M (2 L - 1) + 1` of a fixed family
of interpolation points, and evaluates each child by a recursive call at depth `d + 1` and precision
`p_t`. A leaf, an inactive call, and a child that does not have fewer edges than its parent are
evaluated by the contraction itself, the direct summation of the manuscript's leaves. The recursion
is well founded on the number of edges.

**Correctness** (`TensorNetwork.exists_contractRec_eq_add`). For interpolation points with unit
differences, every call returns the contraction modulo `2 ^ p`, for every schedule: the manuscript's
"induction from the leaves" (p. 64) becomes strong induction on the number of edges. So the
parameter schedule (D.4)–(D.6) matters only for the running time, which this file does not treat.
Under the first inequality of (D.6), every child has at most `M / 16` edges
(`TensorNetwork.mul_card_edges_child_callSplitting_le`, from Lemma D.3 (3)), so an active call with
an edge never falls back for its children, and when `2 L ≤ Δ` the lifted children again run from
rows to columns within the degree bound (`TensorNetwork.rowsToColumnsLE_finLift_child`). In the
manuscript's ring `B = O = ℤ_(2)[U] / (f)`, the binary-coordinate lifts are such points
(`AdjoinRoot.isUnit_integerDigitLift_sub`).

## Main definitions

* `Cslib.Circuits.Frontier.TensorNetwork.RowsToColumnsLE`: a network from rows to columns with a
  degree bound.
* `Cslib.Circuits.Frontier.TensorNetwork.nodeSplitting`,
  `Cslib.Circuits.Frontier.TensorNetwork.callSplitting`: the mode splitting at an active node.
* `Cslib.Circuits.Frontier.TensorNetwork.finLift`: a child lifted to `B` and numbered by `Fin`.
* `Cslib.Circuits.Frontier.TensorNetwork.ContractionOracle`: values for child calls, with
  `ContractionOracle.Correct` and `ContractionOracle.evalLift`.
* `Cslib.Circuits.Frontier.TensorNetwork.nodeValue`,
  `Cslib.Circuits.Frontier.TensorNetwork.callValues`,
  `Cslib.Circuits.Frontier.TensorNetwork.callValue`: one active call from an oracle.
* `Cslib.Circuits.Frontier.TensorNetwork.CallParams`: the parameters of a call, with
  `CallParams.Admissible` and the guard `CallParams.Guard`.
* `Cslib.Circuits.Frontier.TensorNetwork.contractRec`: the recursion.

## Main results

* `Cslib.Circuits.Frontier.TensorNetwork.exists_recoverFromValues_eq_add_of_children`: one call is
  correct when its values are the sums of the products of the children's contractions.
* `Cslib.Circuits.Frontier.TensorNetwork.callSplitting_side`,
  `Cslib.Circuits.Frontier.TensorNetwork.callSplitting_group`,
  `Cslib.Circuits.Frontier.TensorNetwork.callSplitting_packet`: the fields of the splitting.
* `Cslib.Circuits.Frontier.TensorNetwork.exists_callValue_eq_add`: one call is correct for a
  correct oracle.
* `Cslib.Circuits.Frontier.TensorNetwork.mul_card_edges_child_callSplitting_le`: under (D.6), the
  children have at most `M / 16` edges.
* `Cslib.Circuits.Frontier.TensorNetwork.ModeSplitting.rowsToColumnsLE_child`,
  `Cslib.Circuits.Frontier.TensorNetwork.rowsToColumnsLE_finLift_child`: the children keep the
  degree bound.
* `Cslib.Circuits.Frontier.TensorNetwork.contractRec_eq_callValue`,
  `Cslib.Circuits.Frontier.TensorNetwork.contractRec_of_sched_eq_none`: an active call and a leaf.
* `Cslib.Circuits.Frontier.TensorNetwork.exists_contractRec_eq_add`,
  `Cslib.Circuits.Frontier.TensorNetwork.mk_contractRec`: the recursion returns the contraction
  modulo `2 ^ p`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Lemma D.3 (pp. 58–59),
  §D.4.4–§D.4.7, pp. 60–64.
-/

public section

open Polynomial Finset

namespace Cslib.Circuits.Frontier

open ContractionSchedule (nodePrecision)

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### Node precisions -/

/-- A node of positive multiplicity has valuation below `u`. -/
theorem padicValInt_lt_of_taperMult_pos_left {u h : ℕ} {t : ℤ} (hq : 0 < taperMult u h t) :
    padicValInt 2 t < u := by
  unfold taperMult at hq
  by_contra hc
  rw [Nat.sub_eq_zero_of_le (not_lt.mp hc), mul_zero] at hq
  exact lt_irrefl 0 hq

/-- A node of positive multiplicity has valuation below `u`, so below `a` when `u ≤ a`. -/
theorem padicValInt_lt_of_taperMult_pos {u h a : ℕ} {t : ℤ} (hq : 0 < taperMult u h t)
    (hua : u ≤ a) : padicValInt 2 t < a :=
  (padicValInt_lt_of_taperMult_pos_left hq).trans_le hua

/-- The ideal `(2 ^ n)` of a commutative ring. -/
abbrev twoPowIdeal (B : Type*) [CommRing B] (n : ℕ) : Ideal B :=
  Ideal.span {(2 : B) ^ n}

/-- `2 ^ n = 0` modulo `2 ^ n`. -/
theorem two_pow_eq_zero_twoPowIdeal (B : Type*) [CommRing B] (n : ℕ) :
    (2 : B ⧸ twoPowIdeal B n) ^ n = 0 := by
  have : Ideal.Quotient.mk (twoPowIdeal B n) ((2 : B) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_ofNat] at this

/-- The ideal `(2 ^ p_t)` of the node `t` of a call with `M` edges, packets of `2 ^ a` slots,
multiplicity step `h` and input precision `p`. -/
abbrev nodeIdeal (B : Type*) [CommRing B] (M a h p : ℕ) (t : ℤ) : Ideal B :=
  twoPowIdeal B (nodePrecision p h a M (padicValInt 2 t))

namespace TensorNetwork

/-! ### Networks from rows to columns -/

/-- Every edge of `N` runs from a row (`side v = true`) to a column, and every vertex has at most
`Δ` ports at each end: the bipartite form and the degree bound `Δ` of the networks of the
recursion (§D.4.2, p. 58). -/
structure RowsToColumnsLE {R U V E : Type*} [Fintype E] [DecidableEq V]
    (N : TensorNetwork R U V E) (side : V → Bool) (Δ : ℕ) : Prop where
  /-- Edges start at rows. -/
  side_src : ∀ e, side (N.src e) = true
  /-- Edges end at columns. -/
  side_tgt : ∀ e, side (N.tgt e) = false
  /-- Every vertex is the source of at most `Δ` edges. -/
  src_le : ∀ v, #{e | N.src e = v} ≤ Δ
  /-- Every vertex is the target of at most `Δ` edges. -/
  tgt_le : ∀ w, #{e | N.tgt e = w} ≤ Δ

instance {R U : Type*} {n m : ℕ} (N : TensorNetwork R U (Fin n) (Fin m)) (side : Fin n → Bool)
    (Δ : ℕ) : Decidable (N.RowsToColumnsLE side Δ) :=
  decidable_of_iff ((∀ e, side (N.src e) = true) ∧ (∀ e, side (N.tgt e) = false) ∧
      (∀ v, #{e | N.src e = v} ≤ Δ) ∧ ∀ w, #{e | N.tgt e = w} ≤ Δ)
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-! ### The modes of an active node -/

section Node

variable {R V E : Type*} [CommRing R] [Fintype E] {a r : ℕ}

/-- **The modes of an active node** (§D.4.5). For a network whose edges run from rows to columns,
a packing `Q` of its edges, and a nonzero grid point `t` of valuation `i < a`, the mode splitting
of the Cauchy matrix at `T = t + α ζ` with the vertices grouped by their symbol in coordinate `i`
of `Q` (`cauchyModeSplitting`, oriented by `packingGroup_src_tgt`). -/
noncomputable def nodeSplitting (N : TensorNetwork R Bool V E) (side : V → Bool)
    (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false)
    (Q : PacketPacking.Packing N.src N.tgt a r) (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ}
    (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ recoveryNodes a) (hia : padicValInt 2 t < a) :
    N.ModeSplitting (cauchyValueMatrix κ ζ a t Q.packet fun e => Q.slot e) (Fin r)
      (Fin Q.numPackets) (Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) × Fin p) :=
  cauchyModeSplitting (group := packingGroup side Q ⟨_, hia⟩) (packet := Q.packet)
    (slot := fun e => Q.slot e) (sym := fun q => Q.symbols q ⟨_, hia⟩) (i := padicValInt 2 t)
    side hsrc htgt (packingGroup_src_tgt side hsrc htgt Q ⟨_, hia⟩) (packing_slot_lt Q) hia κ ζ hp
    (mem_of_mem_erase ht) (two_pow_padicValInt_dvd_and_not_dvd (ne_of_mem_erase ht)).1
    (two_pow_padicValInt_dvd_and_not_dvd (ne_of_mem_erase ht)).2

/-- **The child identity at an active node** ((D.16)): the deformed contraction along the Cauchy
matrix at `T = t + α ζ` is the sum, over the mode tuples of weight below `p`, of the products over
the groups of the contractions of the children of `nodeSplitting`. -/
theorem deformedContraction_eq_sum_nodeSplitting [Fintype V] [DecidableEq V] [DecidableEq E]
    (N : TensorNetwork R Bool V E) (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
    (htgt : ∀ e, side (N.tgt e) = false) (Q : PacketPacking.Packing N.src N.tgt a r)
    (κ : ℤ₍₂₎ →+* R) (ζ : R) {p : ℕ} (hp : (2 : R) ^ p = 0) {t : ℤ} (ht : t ∈ recoveryNodes a)
    (hia : padicValInt 2 t < a) :
    N.deformedContraction side (cauchyValueMatrix κ ζ a t Q.packet fun e => Q.slot e) =
      ∑ β ∈ modeBudget
          (fun Z : Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) × Fin p => (Z.2.2 : ℕ) + 1) p,
        ∏ g, ((nodeSplitting N side hsrc htgt Q κ ζ hp ht hia).child β g).contraction :=
  deformedContraction_cauchyValueMatrix_eq_sum (group := packingGroup side Q ⟨_, hia⟩)
    (packet := Q.packet) (slot := fun e => Q.slot e) (sym := fun q => Q.symbols q ⟨_, hia⟩)
    (i := padicValInt 2 t) side hsrc htgt (packingGroup_src_tgt side hsrc htgt Q ⟨_, hia⟩)
    (packing_slot_lt Q) hia κ ζ hp (mem_of_mem_erase ht)
    (two_pow_padicValInt_dvd_and_not_dvd (ne_of_mem_erase ht)).1
    (two_pow_padicValInt_dvd_and_not_dvd (ne_of_mem_erase ht)).2

end Node

/-! ### One call from its children -/

section Children

variable {K : Type*} [CommRing K] [Algebra ℚ K] (B : Subring K)
  (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  [DecidableEq E]

/-- The mode splitting at the active node `t` and the point `z` of a call with input precision
`p`: `nodeSplitting` for the network reduced modulo `2 ^ p_t`, at the reduction of `z`. -/
noncomputable def callSplitting (N : TensorNetwork B Bool V E) (side : V → Bool)
    (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false) {a r : ℕ}
    (Q : PacketPacking.Packing N.src N.tgt a r) (p u h : ℕ) (hua : u ≤ a) {t : ℤ}
    (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (z : B) :
    ModeSplitting
      (N.map (Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t)))
      (cauchyValueMatrix
        ((Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t)).comp
          (integerHom B hB))
        (Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t) z) a t
        Q.packet fun e => Q.slot e)
      (Fin r) (Fin Q.numPackets)
      (Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
        Fin (nodePrecision p h a (Fintype.card E) (padicValInt 2 t))) :=
  nodeSplitting (N.map (Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t)))
    side hsrc htgt Q _ _ (two_pow_eq_zero_twoPowIdeal _ _) ht
    (padicValInt_lt_of_taperMult_pos hq hua)

section Fields

variable (N : TensorNetwork B Bool V E) (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
  (htgt : ∀ e, side (N.tgt e) = false) {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r)
  (p u h : ℕ) (hua : u ≤ a) {t : ℤ} (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (z : B)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The rows of the splitting at an active node are the rows of the call. -/
@[simp] theorem callSplitting_side :
    (callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).side = side :=
  cauchyModeSplitting_side ..

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The groups at an active node of valuation `i` are the symbols in coordinate `i` of the
packing. -/
@[simp] theorem callSplitting_group :
    (callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).group =
      packingGroup side Q ⟨_, padicValInt_lt_of_taperMult_pos hq hua⟩ :=
  cauchyModeSplitting_group ..

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
/-- The packets of the splitting at an active node are the packets of the packing. -/
@[simp] theorem callSplitting_packet :
    (callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).packet = Q.packet :=
  cauchyModeSplitting_packet ..

end Fields

/-- **Correctness of one active call from its children** ([OpenAI2026ETH], §D.4.4–§D.4.7). Let
`N` have entries in `B`, edges from rows to columns, and a packing `Q` into packets of `2 ^ a`
slots. Let `1 ≤ u ≤ M`, `u ≤ a` and `3 M ≤ h u ≤ 3 M + u` for `M` edges, and let the
`n > M (2 L - 1)` points `ζ k` have unit differences. If at every node `t` of positive
multiplicity each value `v t k` reduces modulo `2 ^ p_t` to the sum, over the mode tuples of
weight below `p_t`, of the products over the groups of the contractions of the children of
`callSplitting` at `ζ k` (the right side of (D.16)), then the recovered value agrees with the
contraction modulo `2 ^ p`. -/
theorem exists_recoverFromValues_eq_add_of_children (N : TensorNetwork B Bool V E)
    (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false)
    {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r) {u h p : ℕ} (hu : 1 ≤ u)
    (huM : u ≤ Fintype.card E) (hua : u ≤ a) (hh : 3 * Fintype.card E ≤ h * u)
    (hh' : h * u ≤ 3 * Fintype.card E + u) {n : ℕ} (ζ : Fin n → B)
    (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l)) (hn : Fintype.card E * (2 * 2 ^ a - 1) < n)
    (v : ℤ → Fin n → B)
    (hv : ∀ t (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) k,
      Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t) (v t k) =
        ∑ β ∈ modeBudget (fun Z : Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
            Fin (nodePrecision p h a (Fintype.card E) (padicValInt 2 t)) => (Z.2.2 : ℕ) + 1)
            (nodePrecision p h a (Fintype.card E) (padicValInt 2 t)),
          ∏ g, ((callSplitting B hB N side hsrc htgt Q p u h hua ht hq (ζ k)).child β
            g).contraction) :
    ∃ b ∈ B, recoverFromValues B a u h ζ v = (N.contraction : K) + 2 ^ p * b :=
  exists_recoverFromValues_eq_add_of_mk B hB N side (packing_slot_lt Q)
    (packing_slot_injective Q) hu huM hh hh' ζ hζ hn v fun t ht hq k =>
      (hv t ht hq k).trans (deformedContraction_eq_sum_nodeSplitting
        (N.map (Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t))) side
        hsrc htgt Q _ _ (two_pow_eq_zero_twoPowIdeal _ _) ht
        (padicValInt_lt_of_taperMult_pos hq hua)).symm

end Children

/-! ### Lifting child networks -/

section FinLift

variable {B : Type*} [CommRing B] {V E : Type*} [Fintype V] [Fintype E] {p : ℕ}

/-- A network over `B ⧸ (2 ^ p)` on finite types, lifted to `B` along a section of the reduction
(`TensorNetwork.mapFun`) and numbered by `Fin` (`TensorNetwork.reindex`): the network that a child
call receives. -/
noncomputable def finLift (N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E) :
    TensorNetwork B Bool (Fin (Fintype.card V)) (Fin (Fintype.card E)) :=
  (N.mapFun (Function.surjInv Ideal.Quotient.mk_surjective)).reindex (Fintype.equivFin V)
    (Fintype.equivFin E)

/-- The contraction of a lifted network reduces to the contraction. -/
theorem mk_contraction_finLift [DecidableEq E] (N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E) :
    Ideal.Quotient.mk (twoPowIdeal B p) (finLift N).contraction = N.contraction := by
  rw [finLift, contraction_reindex,
    contraction_map_mapFun _ (Function.surjInv_eq Ideal.Quotient.mk_surjective)]

/-- Lifting keeps a network running from rows to columns, with its degree bound. -/
theorem RowsToColumnsLE.finLift [DecidableEq V] {N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E}
    {side : V → Bool} {Δ : ℕ} (h : N.RowsToColumnsLE side Δ) :
    (TensorNetwork.finLift N).RowsToColumnsLE (side ∘ (Fintype.equivFin V).symm) Δ where
  side_src e := by
    simp only [TensorNetwork.finLift, Function.comp_apply, reindex_src, Equiv.symm_apply_apply]
    exact h.side_src _
  side_tgt e := by
    simp only [TensorNetwork.finLift, Function.comp_apply, reindex_tgt, Equiv.symm_apply_apply]
    exact h.side_tgt _
  src_le v := by
    rw [TensorNetwork.finLift, card_reindex_src]
    exact h.src_le _
  tgt_le w := by
    rw [TensorNetwork.finLift, card_reindex_tgt]
    exact h.tgt_le _

end FinLift

/-! ### Contraction oracles -/

/-- A *contraction oracle*: a value for every Boolean tensor network on the vertices `Fin n` and the
edges `Fin m`, with its sides, at every precision. A call of the recursion evaluates its children
through an oracle. -/
abbrev ContractionOracle (B : Type*) : Type _ :=
  (n m : ℕ) → TensorNetwork B Bool (Fin n) (Fin m) → (Fin n → Bool) → ℕ → B

namespace ContractionOracle

variable {B : Type*} [CommRing B]

/-- An oracle is *correct* when each of its values agrees with the contraction modulo the
precision `2 ^ p` it is given. -/
@[expose] def Correct (rec : ContractionOracle B) : Prop :=
  ∀ n m (N : TensorNetwork B Bool (Fin n) (Fin m)) side p,
    ∃ c, rec n m N side p = N.contraction + 2 ^ p * c

/-- The value of an oracle on a network over `B ⧸ (2 ^ p)` on finite types, at precision `p`: the
query on the lifted network `finLift N`. -/
noncomputable def evalLift (rec : ContractionOracle B) {V E : Type*} [Fintype V] [Fintype E]
    {p : ℕ} (N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E) (side : V → Bool) : B :=
  rec _ _ (finLift N) (side ∘ (Fintype.equivFin V).symm) p

/-- **A correct oracle evaluates a lifted network**: its value reduces modulo `2 ^ p` to the
contraction. -/
theorem mk_evalLift {rec : ContractionOracle B} (hrec : rec.Correct) {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] {p : ℕ} (N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E)
    (side : V → Bool) :
    Ideal.Quotient.mk (twoPowIdeal B p) (rec.evalLift N side) = N.contraction := by
  obtain ⟨c, hc⟩ := hrec _ _ (finLift N) (side ∘ (Fintype.equivFin V).symm) p
  have h2 : Ideal.Quotient.mk (twoPowIdeal B p) ((2 : B) ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [evalLift, hc, map_add, map_mul, h2, zero_mul, add_zero, mk_contraction_finLift]

end ContractionOracle

/-! ### One call from an oracle -/

section Call

variable {K : Type*} [CommRing K] [Algebra ℚ K] (B : Subring K)
  (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
  [DecidableEq E]

/-- **The value at an active node** ((D.16)): the sum, over the mode tuples of weight below `p_t`,
of the products over the groups of the oracle's values on the children of `callSplitting` at `z`.
A child has its old vertices as rows and its packets as columns. -/
noncomputable def nodeValue (rec : ContractionOracle B) (N : TensorNetwork B Bool V E)
    (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false)
    {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r) (p u h : ℕ) (hua : u ≤ a) {t : ℤ}
    (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (z : B) : B :=
  ∑ β ∈ modeBudget (fun Z : Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
      Fin (nodePrecision p h a (Fintype.card E) (padicValInt 2 t)) => (Z.2.2 : ℕ) + 1)
      (nodePrecision p h a (Fintype.card E) (padicValInt 2 t)),
    ∏ g, rec.evalLift ((callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).child β g)
      Sum.isLeft

/-- For a correct oracle, the value at an active node reduces modulo `2 ^ p_t` to the right side of
(D.16). -/
theorem mk_nodeValue {rec : ContractionOracle B} (hrec : rec.Correct)
    (N : TensorNetwork B Bool V E) (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
    (htgt : ∀ e, side (N.tgt e) = false) {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r)
    (p u h : ℕ) (hua : u ≤ a) {t : ℤ} (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t)
    (z : B) :
    Ideal.Quotient.mk (nodeIdeal B (Fintype.card E) a h p t)
        (nodeValue B hB rec N side hsrc htgt Q p u h hua ht hq z) =
      ∑ β ∈ modeBudget (fun Z : Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
          Fin (nodePrecision p h a (Fintype.card E) (padicValInt 2 t)) => (Z.2.2 : ℕ) + 1)
          (nodePrecision p h a (Fintype.card E) (padicValInt 2 t)),
        ∏ g, ((callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).child β g).contraction := by
  simp only [nodeValue, map_sum, map_prod, ContractionOracle.mk_evalLift hrec]

/-- The values of an active call at the nodes and interpolation points: `nodeValue` at the nodes
of positive multiplicity, and zero elsewhere. -/
noncomputable def callValues (rec : ContractionOracle B) (N : TensorNetwork B Bool V E)
    (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false)
    {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r) (p u h : ℕ) (hua : u ≤ a) {n : ℕ}
    (ζ : Fin n → B) (t : ℤ) (k : Fin n) : B :=
  if hq : t ∈ recoveryNodes a ∧ 0 < taperMult u h t then
    nodeValue B hB rec N side hsrc htgt Q p u h hua hq.1 hq.2 (ζ k)
  else 0

open Classical in
/-- **One active call** (§D.4.7): interpolate and recover (`recoverFromValues`) the values
`callValues` computed from the oracle. The recovered value lies in `B` when the oracle is correct
(`exists_callValue_eq_add`); otherwise the call returns zero. -/
noncomputable def callValue (rec : ContractionOracle B) (N : TensorNetwork B Bool V E)
    (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false)
    {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r) (p u h : ℕ) (hua : u ≤ a) {n : ℕ}
    (ζ : Fin n → B) : B :=
  if hx : recoverFromValues B a u h ζ (callValues B hB rec N side hsrc htgt Q p u h hua ζ) ∈ B then
    ⟨_, hx⟩
  else 0

/-- **Correctness of one active call** for a correct oracle: under the hypotheses of
`exists_recoverFromValues_eq_add_of_children`, the call returns the contraction modulo `2 ^ p`. -/
theorem exists_callValue_eq_add {rec : ContractionOracle B} (hrec : rec.Correct)
    (N : TensorNetwork B Bool V E) (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
    (htgt : ∀ e, side (N.tgt e) = false) {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r)
    {u h p : ℕ} (hu : 1 ≤ u) (huM : u ≤ Fintype.card E) (hua : u ≤ a)
    (hh : 3 * Fintype.card E ≤ h * u) (hh' : h * u ≤ 3 * Fintype.card E + u) {n : ℕ}
    (ζ : Fin n → B) (hζ : Pairwise fun k l => IsUnit (ζ k - ζ l))
    (hn : Fintype.card E * (2 * 2 ^ a - 1) < n) :
    ∃ c : B, callValue B hB rec N side hsrc htgt Q p u h hua ζ = N.contraction + 2 ^ p * c := by
  obtain ⟨b, hb, hx⟩ := exists_recoverFromValues_eq_add_of_children B hB N side hsrc htgt Q hu
    huM hua hh hh' ζ hζ hn (callValues B hB rec N side hsrc htgt Q p u h hua ζ)
    fun t ht hq k => by
      rw [callValues, dite_eq_left ⟨ht, hq⟩]
      exact mk_nodeValue B hB hrec N side hsrc htgt Q p u h hua ht hq (ζ k)
  have hx' : recoverFromValues B a u h ζ (callValues B hB rec N side hsrc htgt Q p u h hua ζ) =
      ((N.contraction + 2 ^ p * ⟨b, hb⟩ : B) : K) := by
    rw [hx]
    push_cast
    rfl
  refine ⟨⟨b, hb⟩, ?_⟩
  rw [callValue, dite_eq_left (by rw [hx']; exact (N.contraction + 2 ^ p * ⟨b, hb⟩).2)]
  exact Subtype.ext hx'

end Call

/-! ### The children of an active call -/

namespace ModeSplitting

variable {R V E G P M : Type*} [CommRing R] [Fintype M] {N : TensorNetwork R Bool V E}
  {W : Matrix E E R} (S : N.ModeSplitting W G P M) [Fintype E] [DecidableEq E] [DecidableEq P]
  [DecidableEq G] [DecidableEq M] [DecidableEq V]

/-- **Children run from rows to columns within the degree bound.** If every vertex of `N` has at
most `Δ` ports at each end, and the packets have `2 ^ a` slots with `2 · 2 ^ a ≤ Δ`, then each
child runs from its old vertices to its packets with at most `Δ` ports at each vertex: old
vertices keep their degrees, and a packet vertex has at most `2 L` ports (§D.4.6, p. 63). -/
theorem rowsToColumnsLE_child {Δ a : ℕ} {slot : E → ℕ} (hrow : ∀ v, #{e | N.src e = v} ≤ Δ)
    (hcol : ∀ w, #{e | N.tgt e = w} ≤ Δ) (hslot : ∀ e, slot e < 2 ^ a)
    (hinj : ∀ e e', S.packet e = S.packet e' → slot e = slot e' → e = e') (hL : 2 * 2 ^ a ≤ Δ)
    (β : M → ℕ) (g : G) : (S.child β g).RowsToColumnsLE Sum.isLeft Δ where
  side_src := by rintro (e | e) <;> rfl
  side_tgt := by rintro (e | e) <;> rfl
  src_le := by
    rintro (v | q)
    · rw [S.card_child_src_inl]
      by_cases hv : S.side v.1
      · have h0 : #{e | N.tgt e = v.1} = 0 := card_eq_zero.mpr <| filter_eq_empty_iff.mpr
          fun e _ he => by
            have := S.side_tgt e
            rw [he, hv] at this
            exact absurd this (by decide)
        rw [h0, add_zero]
        exact hrow _
      · have h0 : #{e | N.src e = v.1} = 0 := card_eq_zero.mpr <| filter_eq_empty_iff.mpr
          fun e _ he => by
            have := S.side_src e
            rw [he] at this
            exact hv this
        rw [h0, zero_add]
        exact hcol _
    · rw [S.card_child_src_inr]
      exact Nat.zero_le _
  tgt_le := by
    rintro (v | q)
    · rw [S.card_child_tgt_inl]
      exact Nat.zero_le _
    · exact (S.card_child_tgt_inr_le hslot hinj β g q).trans hL

end ModeSplitting

section ChildSize

variable {K : Type*} [CommRing K] [Algebra ℚ K] (B : Subring K)
  (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) {V E : Type*} [Fintype V] [DecidableEq V] [FinEnum V]
  [Fintype E] [DecidableEq E] [LinearOrder E]

omit [Fintype V] [DecidableEq E] in
/-- **Children have at most `M / 16` edges** under the size hypothesis `2 Δ D² ≤ M` of (D.6),
`D = 64 ^ (2 a)`, for the packing of Lemma D.3 with `r = 64` and maximum degree `Δ`: each group has
at most `2 M / 64` ports on each side (`PacketPacking.row_ports_packing_le`), and a child has one
edge per port of its group. The source (§D.4.6, p. 63) bounds a child by `6M/r = 3M/32 < M/8`
edges from the `3M/r` port bound of Lemma D.3 (3); `PacketPacking.packing` has the sharper port
bound `2M/r`. -/
theorem mul_card_edges_child_callSplitting_le (N : TensorNetwork B Bool V E) (side : V → Bool)
    (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false) {a Δ : ℕ}
    (hrow : ∀ v, #{e | N.src e = v} ≤ Δ) (hcol : ∀ w, #{e | N.tgt e = w} ≤ Δ)
    (hM : 2 * Δ * (64 ^ (2 * a)) ^ 2 ≤ Fintype.card E) (p u h : ℕ) (hua : u ≤ a) {t : ℤ}
    (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (z : B) (g : Fin 64) :
    64 * Fintype.card
        ({e // (callSplitting B hB N side hsrc htgt (PacketPacking.packing N.src N.tgt a 64) p u h
            hua ht hq z).group (N.src e) = g} ⊕
          {e // (callSplitting B hB N side hsrc htgt (PacketPacking.packing N.src N.tgt a 64) p u h
            hua ht hq z).group (N.tgt e) = g}) ≤
      4 * Fintype.card E := by
  have := ModeSplitting.mul_card_edges_child_le (c := 2) (r := 64)
    (callSplitting B hB N side hsrc htgt (PacketPacking.packing N.src N.tgt a 64) p u h hua ht hq z)
    g (by
      rw [callSplitting_group]
      exact (congrArg (64 * ·) (card_packingGroup_src side hsrc _ _ g)).trans_le
        (PacketPacking.row_ports_packing_le N.src N.tgt a 64 hrow hcol hM _ g)) (by
      rw [callSplitting_group]
      exact (congrArg (64 * ·) (card_packingGroup_tgt side htgt _ _ g)).trans_le
        (PacketPacking.col_ports_packing_le N.src N.tgt a 64 hrow hcol hM _ g))
  exact this.trans_eq (by ring)

omit [LinearOrder E] [FinEnum V] in
/-- **The lifted children of an active call run from rows to columns within the degree bound**
`Δ`, when the call does and its packets have `2 · 2 ^ a ≤ Δ` slots: the networks the child calls
receive meet the network part of their guard (`CallParams.Guard`). -/
theorem rowsToColumnsLE_finLift_child (N : TensorNetwork B Bool V E) (side : V → Bool)
    (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false) {a r : ℕ}
    (Q : PacketPacking.Packing N.src N.tgt a r) (p u h : ℕ) (hua : u ≤ a) {t : ℤ}
    (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t) (z : B) {Δ : ℕ}
    (hrow : ∀ v, #{e | N.src e = v} ≤ Δ) (hcol : ∀ w, #{e | N.tgt e = w} ≤ Δ)
    (hL : 2 * 2 ^ a ≤ Δ) (β) (g : Fin r) :
    (finLift ((callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).child β g)).RowsToColumnsLE
      (Sum.isLeft ∘ (Fintype.equivFin _).symm) Δ :=
  RowsToColumnsLE.finLift <| ModeSplitting.rowsToColumnsLE_child
    (callSplitting B hB N side hsrc htgt Q p u h hua ht hq z) hrow hcol (packing_slot_lt Q)
    (by rw [callSplitting_packet]; exact packing_slot_injective Q) hL β g

end ChildSize

/-! ### The recursion -/

/-- The parameters of an active call: packets of `L = 2 ^ a` slots, the tapered multiplicities
`q_t = h max(0, u - v₂ t)` of Lemma D.5, and the degree bound `Δ` of (D.6). -/
structure CallParams where
  /-- The packets have `2 ^ a` slots. -/
  a : ℕ
  /-- The number of levels of positive multiplicity. -/
  u : ℕ
  /-- The step of the multiplicities between levels. -/
  h : ℕ
  /-- The degree bound `Δ`. -/
  degree : ℕ

/-- The parameters of a call with `M` edges and `n` interpolation points are *admissible* when
they meet the hypotheses of Lemma D.5, `1 ≤ u ≤ M`, `u ≤ a` and `3 M ≤ h u ≤ 3 M + u`, and there
are more than `M (2 L - 1)` points. -/
structure CallParams.Admissible (θ : CallParams) (M n : ℕ) : Prop where
  /-- `1 ≤ u`. -/
  one_le_u : 1 ≤ θ.u
  /-- `u ≤ M`. -/
  u_le_edges : θ.u ≤ M
  /-- `u ≤ a`. -/
  u_le_a : θ.u ≤ θ.a
  /-- `3 M ≤ h u`. -/
  le_h_mul : 3 * M ≤ θ.h * θ.u
  /-- `h u ≤ 3 M + u`, as for `h = ⌈3 M / u⌉`. -/
  h_mul_le : θ.h * θ.u ≤ 3 * M + θ.u
  /-- There are more than `M (2 L - 1)` interpolation points. -/
  points_lt : M * (2 * 2 ^ θ.a - 1) < n

instance (θ : CallParams) (M n : ℕ) : Decidable (θ.Admissible M n) :=
  decidable_of_iff (1 ≤ θ.u ∧ θ.u ≤ M ∧ θ.u ≤ θ.a ∧ 3 * M ≤ θ.h * θ.u ∧
      θ.h * θ.u ≤ 3 * M + θ.u ∧ M * (2 * 2 ^ θ.a - 1) < n)
    ⟨fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩,
      fun ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ => ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩⟩

/-- The *guard* of an active call on a network `N` with `m` edges, its sides `side` and `n`
interpolation points: the parameters `θ` are admissible, and `N` runs from rows to columns with
at most `Δ = θ.degree` ports at each end of each vertex, the degree bound under which Lemma D.3
makes the children smaller (`mul_card_edges_child_callSplitting_le`). Correctness does not use the
degree bound. -/
structure CallParams.Guard (θ : CallParams) {R : Type*} {n m : ℕ}
    (N : TensorNetwork R Bool (Fin n) (Fin m)) (side : Fin n → Bool) (N₀ : ℕ) : Prop
    extends N.RowsToColumnsLE side θ.degree where
  /-- The parameters are admissible. -/
  admissible : θ.Admissible m N₀

instance (θ : CallParams) {R : Type*} {n m : ℕ} (N : TensorNetwork R Bool (Fin n) (Fin m))
    (side : Fin n → Bool) (N₀ : ℕ) : Decidable (θ.Guard N side N₀) :=
  decidable_of_iff (N.RowsToColumnsLE side θ.degree ∧ θ.Admissible m N₀)
    ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun h => ⟨h.toRowsToColumnsLE, h.admissible⟩⟩

section Recursion

variable {K : Type*} [CommRing K] [Algebra ℚ K] (B : Subring K)
  (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) (sched : ℕ → ℕ → Option CallParams) {N₀ : ℕ}
  (pts : Fin N₀ → B)

/-- **The contraction recursion** ([OpenAI2026ETH], §D.4.7). A call at depth `d` on a network `N`
with `m` edges, sides `side` and precision `p` asks the schedule for its parameters. When there
are none, or the guard fails (`CallParams.Guard`), it returns the contraction (direct
summation). Otherwise it is an active call (`callValue`) with the packing of Lemma D.3 (`r = 64`)
and the first `M (2 L - 1) + 1` points of `pts`, whose children are recursive calls at depth
`d + 1`; a child that does not have fewer edges returns its contraction. -/
noncomputable def contractRec (d n m : ℕ) (N : TensorNetwork B Bool (Fin n) (Fin m))
    (side : Fin n → Bool) (p : ℕ) : B :=
  match sched d m with
  | none => N.contraction
  | some θ =>
    if hθ : θ.Guard N side N₀ then
      callValue B hB
        (fun n' m' N' side' p' =>
          if hm : m' < m then contractRec (d + 1) n' m' N' side' p' else N'.contraction)
        N side hθ.side_src hθ.side_tgt (PacketPacking.packing N.src N.tgt θ.a 64) p θ.u θ.h
        hθ.admissible.u_le_a
        fun k : Fin (m * (2 * 2 ^ θ.a - 1) + 1) => pts (Fin.castLE hθ.admissible.points_lt k)
    else N.contraction
termination_by m

variable {B hB sched pts} in
/-- **An active call** of the recursion: when the schedule gives parameters whose guard holds, the
call is `callValue` with the packing of Lemma D.3, the first `M (2 L - 1) + 1` points, and
recursive calls at depth `d + 1` for the children with fewer edges. -/
theorem contractRec_eq_callValue {d n m : ℕ} {N : TensorNetwork B Bool (Fin n) (Fin m)}
    {side : Fin n → Bool} {θ : CallParams} (hs : sched d m = some θ) (hθ : θ.Guard N side N₀)
    (p : ℕ) :
    contractRec B hB sched pts d n m N side p =
      callValue B hB
        (fun n' m' N' side' p' =>
          if m' < m then contractRec B hB sched pts (d + 1) n' m' N' side' p' else N'.contraction)
        N side hθ.side_src hθ.side_tgt (PacketPacking.packing N.src N.tgt θ.a 64) p θ.u θ.h
        hθ.admissible.u_le_a
        fun k : Fin (m * (2 * 2 ^ θ.a - 1) + 1) => pts (Fin.castLE hθ.admissible.points_lt k) := by
  rw [contractRec.eq_def]
  simp only [hs]
  rw [dite_eq_left hθ]
  rfl

variable {B hB sched pts} in
/-- **A leaf** of the recursion, where the schedule gives no parameters, is evaluated directly. -/
theorem contractRec_of_sched_eq_none {d n m : ℕ} {N : TensorNetwork B Bool (Fin n) (Fin m)}
    {side : Fin n → Bool} (hs : sched d m = none) (p : ℕ) :
    contractRec B hB sched pts d n m N side p = N.contraction := by
  rw [contractRec.eq_def]
  simp only [hs]

/-- **Correctness of the recursion** ([OpenAI2026ETH], §D.4.7, p. 64: correctness "by induction
from the leaves"). For interpolation points with unit differences, every call returns the
contraction modulo `2 ^ p`, for every schedule and depth. -/
theorem exists_contractRec_eq_add (hpts : Pairwise fun k l => IsUnit (pts k - pts l)) (d n m : ℕ)
    (N : TensorNetwork B Bool (Fin n) (Fin m)) (side : Fin n → Bool) (p : ℕ) :
    ∃ c : B, contractRec B hB sched pts d n m N side p = N.contraction + 2 ^ p * c := by
  induction m using Nat.strong_induction_on generalizing d n p with
  | _ m ih =>
  rw [contractRec]
  split
  · exact ⟨0, by simp⟩
  · rename_i θ _
    split_ifs with hθ
    · obtain ⟨hu, huM, hua, hh, hh', hn⟩ := hθ.admissible
      refine exists_callValue_eq_add B hB (fun n' m' N' side' p' => ?_) N side hθ.side_src
        hθ.side_tgt _ hu (by simpa using huM) hua (by simpa using hh) (by simpa using hh') _
        (fun k l hkl => hpts fun h => hkl (Fin.castLE_injective _ h)) (by simp)
      split_ifs with hm
      · exact ih m' hm (d + 1) n' N' side' p'
      · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩

/-- **The recursion computes the contraction modulo `2 ^ p`.** -/
theorem mk_contractRec (hpts : Pairwise fun k l => IsUnit (pts k - pts l)) (d n m : ℕ)
    (N : TensorNetwork B Bool (Fin n) (Fin m)) (side : Fin n → Bool) (p : ℕ) :
    Ideal.Quotient.mk (twoPowIdeal B p) (contractRec B hB sched pts d n m N side p) =
      Ideal.Quotient.mk (twoPowIdeal B p) N.contraction := by
  obtain ⟨c, hc⟩ := exists_contractRec_eq_add B hB sched pts hpts d n m N side p
  rw [hc, Ideal.Quotient.eq, add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Recursion

end TensorNetwork

end Cslib.Circuits.Frontier
