/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ActiveCall
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Reindex

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
modulo `2 ^ p_t`, `p_t = p + 8 h D_t + 8 M (a + 1)` (`nodePrecision`).

**One call from its children.** If every value `v t k` reduces modulo `2 ^ p_t` to the sum over
the mode tuples of the products of the contractions of the children (the right side of (D.16)),
then interpolation and tapered recovery return the contraction modulo `2 ^ p`
(`TensorNetwork.exists_recoverFromValues_eq_add_of_children`). The children's contractions may
come from any *contraction oracle* (`TensorNetwork.ContractionOracle`) that is correct modulo the
precision it is given: a child over `B ⧸ (2 ^ p_t)` is lifted to `B` along a section of the
reduction and renumbered by `Fin` (`TensorNetwork.ContractionOracle.evalLift`), and the oracle's
value then reduces to its contraction (`TensorNetwork.ContractionOracle.mk_evalLift`). The value of
an active node is `TensorNetwork.nodeValue`, the values of a call are `TensorNetwork.callValues`,
and the recovered value is `TensorNetwork.callValue`
(`TensorNetwork.exists_callValue_eq_add`).

**The recursion** (`TensorNetwork.contractRec`). A call receives a network on `Fin n` vertices
and `Fin m` edges, its sides, its depth `d` and its precision `p`. A *schedule* gives the
parameters `a`, `u`, `h` of a call from its depth and its number of edges (`CallParams`), or none
at a leaf. The call is active when the parameters meet the hypotheses of Lemma D.5
(`CallParams.Admissible`, with `u ≤ a` and enough interpolation points) and the edges run from
rows to columns. It packs the edges with `PacketPacking.packing` (Lemma D.3, `r = 64`), takes the
first `M (2 L - 1) + 1` of a fixed family of interpolation points, and evaluates each child by a
recursive call at depth `d + 1` and precision `p_t`. A leaf, an inactive call, and a child that
does not have fewer edges than its parent are evaluated by the contraction itself, the direct
summation of the manuscript's leaves. The recursion is well founded on the number of edges.

**Correctness** (`TensorNetwork.exists_contractRec_eq_add`). For interpolation points with unit
differences, every call returns the contraction modulo `2 ^ p`, for every schedule: the manuscript's
"induction from the leaves" (p. 64) becomes strong induction on the number of edges. So the
parameter schedule (D.4)–(D.6) matters only for the running time, which this file does not treat.
Under the first inequality of (D.6), every child has at most `M / 16` edges
(`TensorNetwork.mul_card_edges_child_callSplitting_le`, from Lemma D.3 (3)), so an active call with
an edge never falls back for its children. In the manuscript's ring `B = O = ℤ_(2)[U] / (f)`, the
binary-coordinate lifts are such points (`AdjoinRoot.isUnit_integerDigitLift_sub`).

## Main definitions

* `Cslib.Circuits.Frontier.nodePrecision`: the child precision `p_t`.
* `Cslib.Circuits.Frontier.TensorNetwork.nodeSplitting`,
  `Cslib.Circuits.Frontier.TensorNetwork.callSplitting`: the mode splitting at an active node.
* `Cslib.Circuits.Frontier.TensorNetwork.ContractionOracle`: values for child calls, with
  `ContractionOracle.Correct` and `ContractionOracle.evalLift`.
* `Cslib.Circuits.Frontier.TensorNetwork.nodeValue`,
  `Cslib.Circuits.Frontier.TensorNetwork.callValues`,
  `Cslib.Circuits.Frontier.TensorNetwork.callValue`: one active call from an oracle.
* `Cslib.Circuits.Frontier.TensorNetwork.CallParams`: the parameters of a call.
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

/-- The subring `ℤ_(2)` of rationals with odd denominator. -/
local notation "ℤ₍₂₎" => Valuation.integer (Rat.padicValuation 2)

/-! ### Node precisions -/

/-- The precision `p_t = p + 8 h D_t + 8 M (a + 1)`, `D_t = 2 ^ (a - v₂ t)`, that a call of input
precision `p` with `M` edges passes to the children of the node `t` (Lemma D.5). -/
@[expose] def nodePrecision (M a h p : ℕ) (t : ℤ) : ℕ :=
  p + 8 * h * 2 ^ (a - padicValInt 2 t) + 8 * M * (a + 1)

/-- A node of positive multiplicity has valuation below `u`, so below `a` when `u ≤ a`. -/
theorem padicValInt_lt_of_taperMult_pos {u h a : ℕ} {t : ℤ} (hq : 0 < taperMult u h t)
    (hua : u ≤ a) : padicValInt 2 t < a := by
  unfold taperMult at hq
  have : padicValInt 2 t < u := by
    by_contra hc
    rw [Nat.sub_eq_zero_of_le (not_lt.mp hc), mul_zero] at hq
    exact lt_irrefl 0 hq
  omega

/-- The ideal `(2 ^ n)` of a commutative ring. -/
abbrev twoPowIdeal (B : Type*) [CommRing B] (n : ℕ) : Ideal B :=
  Ideal.span {(2 : B) ^ n}

/-- `2 ^ n = 0` modulo `2 ^ n`. -/
theorem two_pow_eq_zero_twoPowIdeal (B : Type*) [CommRing B] (n : ℕ) :
    (2 : B ⧸ twoPowIdeal B n) ^ n = 0 := by
  have : Ideal.Quotient.mk (twoPowIdeal B n) ((2 : B) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_ofNat] at this

namespace TensorNetwork

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
      (N.map (Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t))))
      (cauchyValueMatrix
        ((Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t))).comp
          (integerHom B hB))
        (Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t)) z) a t
        Q.packet fun e => Q.slot e)
      (Fin r) (Fin Q.numPackets)
      (Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
        Fin (nodePrecision (Fintype.card E) a h p t)) :=
  nodeSplitting (N.map (Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t))))
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
      Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t)) (v t k) =
        ∑ β ∈ modeBudget (fun Z : Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
            Fin (nodePrecision (Fintype.card E) a h p t) => (Z.2.2 : ℕ) + 1)
            (nodePrecision (Fintype.card E) a h p t),
          ∏ g, ((callSplitting B hB N side hsrc htgt Q p u h hua ht hq (ζ k)).child β
            g).contraction) :
    ∃ b ∈ B, recoverFromValues B a u h ζ v = (N.contraction : K) + 2 ^ p * b :=
  exists_recoverFromValues_eq_add_of_mk B hB N side (packing_slot_lt Q)
    (packing_slot_injective Q) hu huM hh hh' ζ hζ hn v fun t ht hq k =>
      (hv t ht hq k).trans (deformedContraction_eq_sum_nodeSplitting
        (N.map (Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t)))) side
        hsrc htgt Q _ _ (two_pow_eq_zero_twoPowIdeal _ _) ht
        (padicValInt_lt_of_taperMult_pos hq hua)).symm

end Children

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

/-- The value of an oracle on a network over `B ⧸ (2 ^ p)` on finite types, at precision `p`: lift
the entries to `B` along a section of the reduction (`TensorNetwork.mapFun`), number the vertices
and edges (`TensorNetwork.reindex`), and query. -/
noncomputable def evalLift (rec : ContractionOracle B) {V E : Type*} [Fintype V] [Fintype E]
    {p : ℕ} (N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E) (side : V → Bool) : B :=
  rec _ _ ((N.mapFun (Function.surjInv Ideal.Quotient.mk_surjective)).reindex
    (Fintype.equivFin V) (Fintype.equivFin E)) (side ∘ (Fintype.equivFin V).symm) p

/-- **A correct oracle evaluates a lifted network**: its value reduces modulo `2 ^ p` to the
contraction. -/
theorem mk_evalLift {rec : ContractionOracle B} (hrec : rec.Correct) {V E : Type*} [Fintype V]
    [Fintype E] [DecidableEq E] {p : ℕ} (N : TensorNetwork (B ⧸ twoPowIdeal B p) Bool V E)
    (side : V → Bool) :
    Ideal.Quotient.mk (twoPowIdeal B p) (rec.evalLift N side) = N.contraction := by
  obtain ⟨c, hc⟩ := hrec _ _ ((N.mapFun (Function.surjInv Ideal.Quotient.mk_surjective)).reindex
    (Fintype.equivFin V) (Fintype.equivFin E)) (side ∘ (Fintype.equivFin V).symm) p
  have h2 : Ideal.Quotient.mk (twoPowIdeal B p) ((2 : B) ^ p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [evalLift, hc, map_add, map_mul, h2, zero_mul, add_zero, contraction_reindex,
    contraction_map_mapFun _ (Function.surjInv_eq Ideal.Quotient.mk_surjective)]

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
      Fin (nodePrecision (Fintype.card E) a h p t) => (Z.2.2 : ℕ) + 1)
      (nodePrecision (Fintype.card E) a h p t),
    ∏ g, rec.evalLift ((callSplitting B hB N side hsrc htgt Q p u h hua ht hq z).child β g)
      Sum.isLeft

/-- For a correct oracle, the value at an active node reduces modulo `2 ^ p_t` to the right side of
(D.16). -/
theorem mk_nodeValue {rec : ContractionOracle B} (hrec : rec.Correct)
    (N : TensorNetwork B Bool V E) (side : V → Bool) (hsrc : ∀ e, side (N.src e) = true)
    (htgt : ∀ e, side (N.tgt e) = false) {a r : ℕ} (Q : PacketPacking.Packing N.src N.tgt a r)
    (p u h : ℕ) (hua : u ≤ a) {t : ℤ} (ht : t ∈ recoveryNodes a) (hq : 0 < taperMult u h t)
    (z : B) :
    Ideal.Quotient.mk (twoPowIdeal B (nodePrecision (Fintype.card E) a h p t))
        (nodeValue B hB rec N side hsrc htgt Q p u h hua ht hq z) =
      ∑ β ∈ modeBudget (fun Z : Fin Q.numPackets × Fin (2 ^ (padicValInt 2 t + 1)) ×
          Fin (nodePrecision (Fintype.card E) a h p t) => (Z.2.2 : ℕ) + 1)
          (nodePrecision (Fintype.card E) a h p t),
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

/-! ### Children are smaller under (D.6) -/

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

end ChildSize

/-! ### The recursion -/

/-- The parameters of an active call: packets of `L = 2 ^ a` slots, and the tapered multiplicities
`q_t = h max(0, u - v₂ t)` of Lemma D.5. -/
structure CallParams where
  /-- The packets have `2 ^ a` slots. -/
  a : ℕ
  /-- The number of levels of positive multiplicity. -/
  u : ℕ
  /-- The step of the multiplicities between levels. -/
  h : ℕ

/-- The parameters of a call with `M` edges and `n` interpolation points are *admissible* when
they meet the hypotheses of Lemma D.5, `1 ≤ u ≤ M`, `u ≤ a` and `3 M ≤ h u ≤ 3 M + u`, and there
are more than `M (2 L - 1)` points. -/
@[expose] def CallParams.Admissible (θ : CallParams) (M n : ℕ) : Prop :=
  1 ≤ θ.u ∧ θ.u ≤ M ∧ θ.u ≤ θ.a ∧ 3 * M ≤ θ.h * θ.u ∧ θ.h * θ.u ≤ 3 * M + θ.u ∧
    M * (2 * 2 ^ θ.a - 1) < n

instance (θ : CallParams) (M n : ℕ) : Decidable (θ.Admissible M n) := by
  unfold CallParams.Admissible
  infer_instance

section Recursion

variable {K : Type*} [CommRing K] [Algebra ℚ K] (B : Subring K)
  (hB : ∀ c ∈ ℤ₍₂₎, algebraMap ℚ K c ∈ B) (sched : ℕ → ℕ → Option CallParams) {N₀ : ℕ}
  (pts : Fin N₀ → B)

/-- **The contraction recursion** ([OpenAI2026ETH], §D.4.7). A call at depth `d` on a network `N`
with `m` edges, sides `side` and precision `p` asks the schedule for its parameters. When there
are none, the parameters are not admissible, or an edge does not run from a row to a column, it
returns the contraction (direct summation). Otherwise it is an active call (`callValue`) with the
packing of Lemma D.3 (`r = 64`) and the first `M (2 L - 1) + 1` points of `pts`, whose children
are recursive calls at depth `d + 1`; a child that does not have fewer edges returns its
contraction. -/
noncomputable def contractRec (d n m : ℕ) (N : TensorNetwork B Bool (Fin n) (Fin m))
    (side : Fin n → Bool) (p : ℕ) : B :=
  match sched d m with
  | none => N.contraction
  | some θ =>
    if hθ : θ.Admissible m N₀ ∧ (∀ e, side (N.src e) = true) ∧ ∀ e, side (N.tgt e) = false then
      callValue B hB
        (fun n' m' N' side' p' =>
          if hm : m' < m then contractRec (d + 1) n' m' N' side' p' else N'.contraction)
        N side hθ.2.1 hθ.2.2 (PacketPacking.packing N.src N.tgt θ.a 64) p θ.u θ.h hθ.1.2.2.1
        fun k : Fin (m * (2 * 2 ^ θ.a - 1) + 1) => pts (Fin.castLE hθ.1.2.2.2.2.2 k)
    else N.contraction
termination_by m

variable {B hB sched pts} in
/-- **An active call** of the recursion: when the schedule gives admissible parameters and the edges
run from rows to columns, the call is `callValue` with the packing of Lemma D.3, the first
`M (2 L - 1) + 1` points, and recursive calls at depth `d + 1` for the children with fewer edges. -/
theorem contractRec_eq_callValue {d n m : ℕ} {N : TensorNetwork B Bool (Fin n) (Fin m)}
    {side : Fin n → Bool} {θ : CallParams} (hs : sched d m = some θ) (hθ : θ.Admissible m N₀)
    (hsrc : ∀ e, side (N.src e) = true) (htgt : ∀ e, side (N.tgt e) = false) (p : ℕ) :
    contractRec B hB sched pts d n m N side p =
      callValue B hB
        (fun n' m' N' side' p' =>
          if m' < m then contractRec B hB sched pts (d + 1) n' m' N' side' p' else N'.contraction)
        N side hsrc htgt (PacketPacking.packing N.src N.tgt θ.a 64) p θ.u θ.h hθ.2.2.1
        fun k : Fin (m * (2 * 2 ^ θ.a - 1) + 1) => pts (Fin.castLE hθ.2.2.2.2.2 k) := by
  rw [contractRec.eq_def]
  simp only [hs]
  rw [dite_eq_left ⟨hθ, hsrc, htgt⟩]
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
    · obtain ⟨hu, huM, hua, hh, hh', hn⟩ := hθ.1
      refine exists_callValue_eq_add B hB (fun n' m' N' side' p' => ?_) N side hθ.2.1 hθ.2.2 _
        hu (by simpa using huM) hua (by simpa using hh) (by simpa using hh') _
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
