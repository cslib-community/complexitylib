/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Deformation
public import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Modes and the child networks of a deformed contraction

This file proves the child identity (D.16) of [OpenAI2026ETH] (§D.4.5–§D.4.6, pp. 62–63), the
step of the proof of the Boolean tensor contraction theorem (Theorem D.1) that turns one
deformed contraction into a sum of products of smaller contractions.

**Setting.** Let `N` be a Boolean tensor network whose edges run from *rows* (their sources) to
*columns* (their targets), and let `W` be a matrix indexed by the edges. The deformed contraction
(`TensorNetwork.deformedContraction`, the manuscript's (D.8)) is

  `F(W) = ∑ X Y, A(Y) B(X) ∏ e, l_{Y e}((W X) e)`.

A *mode splitting* (`TensorNetwork.ModeSplitting`) sorts the vertices on both sides into
*groups* and the edges into *packets*, and splits every entry of `W` as

  `W e e' = localPart e e' + ∑ Z, coeff e Z * form Z e'`,

where the local part only joins a row port to a column port of the same packet and group, and
each *mode* `Z` has a packet, a *target* group, whose row ports carry its coefficients, and a
*source* group, whose column ports its linear form `L_Z(X) = ∑ e', form Z e' X e'` reads. In the
manuscript the modes are the terms of the geometric expansion (D.12) of the crossing entries of
the Cauchy matrix; here they are arbitrary.

**Mode expansion.** Each affine factor `l_{Y e}((W X) e)` is affine in the mode values, so the
product of the affine factors of the row ports of one packet and group (a *block*) expands as a
polynomial in the modes targeted at that block. Its coefficient at the exponents `β`
(`ModeSplitting.blockCoeff`) sums, over the ways to pick the local term or one mode in each
factor with the multiplicities `β`, the product of the picked coefficients.

**Children** (`ModeSplitting.child`). For a tuple of exponents `β` and a group `g`, the child
network has the vertices of group `g` from both sides of `N`, with their tensors, and one new
vertex per packet. Its edges are the ports of group `g`: an edge from the row of `e` to the packet
of `e` for each row port `e` of group `g`, carrying the row bit `Y e`, and one from the column of
`e` to the packet of `e` for each column port of group `g`, carrying the column bit `X e`. The
tensor at a packet (`ModeSplitting.packetTensor`) is the coefficient at `β` for that packet and
group times `∏ L_Z(X) ^ β Z` over the modes of that packet with source `g`. So children are
tensor networks on `{v // group v = g} ⊕ P`, bipartite with the old vertices as rows
(`ModeSplitting.isBipartite_child`).

**The child identity** (`ModeSplitting.deformedContraction_eq_sum_prod_contraction_child`, the
manuscript's (D.16)). If the coefficient of each mode `Z` is divisible by `π ^ w Z` with
`w Z ≥ 1`, and `π ^ p = 0`, then

  `F(W) = ∑ β ∈ modeBudget w p, ∏ g, Z_{g, β}`,

where `Z_{g, β}` is the contraction of the child of group `g` and `modeBudget w p` is the set of
tuples with `∑ Z, w Z * β Z < p` (the manuscript's (D.14)). The manuscript works modulo `2 ^ p_t`
with `π = 2` and `w Z = b + 1`; here the ring itself has `π ^ p = 0`, as in `A / 2 ^ p_t`, and a
congruence in a larger ring follows by mapping to its quotient
(`TensorNetwork.deformedContraction_map`). Without truncation, the same expansion gives
`F(W) = ∑ β, ∏ g, Z_{g, β}` over all tuples with entries at most the number of edges, in every
commutative ring (`ModeSplitting.deformedContraction_eq_sum_prod_contraction_child_of_le`).

The proof is the manuscript's: distribute the product of the affine factors over the blocks,
expand each block in its modes, substitute the mode values, and sum the bits of each group
independently. The construction of the modes from the Cauchy kernel ((D.12)–(D.13)), the count
(D.15) of the tuples, and the size bounds on the children are separate steps.

## Main definitions

* `TensorNetwork.affineSign`: the sign of the variable part of an affine factor.
* `TensorNetwork.ModeSplitting`: groups, packets, and the splitting of a matrix into a local part
  and modes.
* `TensorNetwork.modeBudget`: the tuples of exponents of total weight below `p`.
* `TensorNetwork.ModeSplitting.blockCoeff`: the coefficient of a mode monomial in the product of
  the affine factors of a block.
* `TensorNetwork.ModeSplitting.packetTensor`: the tensor at a packet vertex of a child.
* `TensorNetwork.ModeSplitting.child`: the child network of a group.

## Main results

* `TensorNetwork.affineFactor_add`: `l_b (u + w) = l_b u ± w`.
* `TensorNetwork.mem_modeBudget`: membership in the budget.
* `TensorNetwork.ModeSplitting.packetTensor_congr`: a packet tensor reads only the ports of its
  packet and group.
* `TensorNetwork.ModeSplitting.pow_dvd_blockCoeff`: the coefficient of a mode monomial is
  divisible by `π` to its total weight.
* `TensorNetwork.ModeSplitting.isBipartite_child`, `TensorNetwork.ModeSplitting.card_edges_child`:
  children are bipartite, with one edge per port of their group.
* `TensorNetwork.ModeSplitting.deformedContraction_eq_sum_prod_contraction_child_of_le`: the
  exact expansion of `F(W)` into children.
* `TensorNetwork.ModeSplitting.deformedContraction_eq_sum_prod_contraction_child`: the child
  identity (D.16).

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §D.4.5–§D.4.6,
  (D.14) and (D.16), pp. 62–63.
-/

public section

namespace Cslib.Circuits.Frontier

open Finset

namespace TensorNetwork

variable {R V E : Type*} [CommRing R]

/-! ### Affine factors of a sum -/

/-- The sign of the variable part of an affine factor: `affineSign true = 1` and
`affineSign false = -1`, so that `l_b (u + w) = l_b u + affineSign b * w`. -/
@[expose] def affineSign (b : Bool) : R :=
  if b then 1 else -1

/-- An affine factor of a sum: `l_b (u + w) = l_b u + affineSign b * w`. -/
theorem affineFactor_add (b : Bool) (u w : R) :
    affineFactor b (u + w) = affineFactor b u + affineSign b * w := by
  cases b <;> simp only [affineFactor, affineSign, Bool.false_eq_true, ite_false, ite_true] <;>
    ring

/-! ### Mode splittings -/

/-- A *mode splitting* (§D.4.5 of [OpenAI2026ETH]) of the deformed contraction of a Boolean tensor
network `N` along a matrix `W`. The rows of `N` (`side v = true`) are the sources of its edges and
the columns their targets. The vertices on both sides are sorted into *groups* and the edges into
*packets*, and every entry of `W` splits into a *local part*, which joins a row port to a column
port of the same packet and group, and a sum over the *modes* `Z`, each contributing
`coeff e Z * form Z e'`. A mode has a packet, a *target* group, the only row ports of its packet
whose forms contain it, and a *source* group, the only column ports of its packet that its linear
form reads. -/
structure ModeSplitting (N : TensorNetwork R Bool V E) (W : Matrix E E R) (G P M : Type*)
    [Fintype M] where
  /-- The side of a vertex: `true` for rows, `false` for columns. -/
  side : V → Bool
  /-- The group of a vertex. -/
  group : V → G
  /-- The packet of an edge. -/
  packet : E → P
  /-- The local part of the matrix. -/
  localPart : Matrix E E R
  /-- The packet of a mode. -/
  modePacket : M → P
  /-- The source group of a mode: its form reads the column ports of this group. -/
  source : M → G
  /-- The target group of a mode: it occurs in the forms of the row ports of this group. -/
  target : M → G
  /-- The coefficient of a mode in the form of a row port. -/
  coeff : E → M → R
  /-- The linear form in the column bits that a mode stands for. -/
  form : M → E → R
  /-- Edges start at rows. -/
  side_src : ∀ e, side (N.src e) = true
  /-- Edges end at columns. -/
  side_tgt : ∀ e, side (N.tgt e) = false
  /-- The splitting of the matrix. -/
  apply_eq : ∀ e e', W e e' = localPart e e' + ∑ Z, coeff e Z * form Z e'
  /-- The local part joins ports of the same packet and group. -/
  localPart_ne_zero : ∀ e e', localPart e e' ≠ 0 →
    packet e' = packet e ∧ group (N.tgt e') = group (N.src e)
  /-- A mode occurs only in the forms of the row ports of its packet and target group. -/
  coeff_ne_zero : ∀ e Z, coeff e Z ≠ 0 → modePacket Z = packet e ∧ target Z = group (N.src e)
  /-- A mode reads only the column ports of its packet and source group. -/
  form_ne_zero : ∀ Z e, form Z e ≠ 0 → modePacket Z = packet e ∧ source Z = group (N.tgt e)

/-- The tuples of exponents `β` of total weight `∑ Z, w Z * β Z` below `p`, the index set of the
manuscript's (D.14). -/
@[expose] def modeBudget {M : Type*} [Fintype M] [DecidableEq M] (w : M → ℕ) (p : ℕ) :
    Finset (M → ℕ) :=
  {β ∈ Fintype.piFinset fun _ => range p | ∑ Z, w Z * β Z < p}

/-- For positive weights, the budget holds exactly the tuples of total weight below `p`. -/
theorem mem_modeBudget {M : Type*} [Fintype M] [DecidableEq M] {w : M → ℕ} (hw : ∀ Z, 0 < w Z)
    {p : ℕ} {β : M → ℕ} : β ∈ modeBudget w p ↔ ∑ Z, w Z * β Z < p := by
  simp only [modeBudget, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h Z
  calc β Z ≤ w Z * β Z := Nat.le_mul_of_pos_left _ (hw Z)
    _ ≤ ∑ Z, w Z * β Z := single_le_sum (fun Z _ => Nat.zero_le (w Z * β Z)) (mem_univ Z)
    _ < p := h

namespace ModeSplitting

variable {G P M : Type*} [Fintype M] {N : TensorNetwork R Bool V E} {W : Matrix E E R}
  (S : ModeSplitting N W G P M)

/-- The block of a row port: its packet and the group of its row. -/
@[expose] def rowBlock (e : E) : P × G :=
  (S.packet e, S.group (N.src e))

/-- The block of a mode: its packet and its target group. -/
@[expose] def targetBlock (Z : M) : P × G :=
  (S.modePacket Z, S.target Z)

/-- The source block of a mode: its packet and its source group. -/
@[expose] def sourceBlock (Z : M) : P × G :=
  (S.modePacket Z, S.source Z)

section Forms

variable [Fintype E]

/-- The local form of a row port on the column bits `X`. -/
@[expose] def localForm (X : E → Bool) (e : E) : R :=
  ∑ e', S.localPart e e' * if X e' then 1 else 0

/-- The value `L_Z(X) = ∑ e', form Z e' X e'` of a mode on the column bits `X`. -/
@[expose] def modeValue (X : E → Bool) (Z : M) : R :=
  ∑ e', S.form Z e' * if X e' then 1 else 0

/-- The terms of the expansion of the affine factor of a row port: the local term, and the
coefficient of each mode. -/
@[expose] def choiceTerm (Y X : E → Bool) (e : E) : Option M → R
  | none => affineFactor (Y e) (S.localForm X e)
  | some Z => affineSign (Y e) * S.coeff e Z

theorem localForm_congr {X X' : E → Bool} {e : E}
    (h : ∀ e', S.packet e' = S.packet e → S.group (N.tgt e') = S.group (N.src e) → X e' = X' e') :
    S.localForm X e = S.localForm X' e := by
  refine sum_congr rfl fun e' _ => ?_
  by_cases h0 : S.localPart e e' = 0
  · rw [h0, zero_mul, zero_mul]
  · obtain ⟨hp, hg⟩ := S.localPart_ne_zero e e' h0
    rw [h e' hp hg]

theorem modeValue_congr {X X' : E → Bool} {Z : M}
    (h : ∀ e, S.packet e = S.modePacket Z → S.group (N.tgt e) = S.source Z → X e = X' e) :
    S.modeValue X Z = S.modeValue X' Z := by
  refine sum_congr rfl fun e _ => ?_
  by_cases h0 : S.form Z e = 0
  · rw [h0, zero_mul, zero_mul]
  · obtain ⟨hp, hg⟩ := S.form_ne_zero Z e h0
    rw [h e hp.symm hg.symm]

/-- The form of a row port splits into its local form and its modes. -/
theorem mulVec_apply (X : E → Bool) (e : E) :
    W.mulVec (fun e' => if X e' then 1 else 0) e =
      S.localForm X e + ∑ Z, S.coeff e Z * S.modeValue X Z := by
  simp only [Matrix.mulVec, dotProduct, S.apply_eq, add_mul, sum_add_distrib, localForm,
    modeValue, mul_sum, sum_mul]
  rw [sum_comm (s := univ) (t := univ) (f := fun e' Z => S.coeff e Z * S.form Z e' * _)]
  simp only [mul_assoc]

/-- The affine factor of a row port as the sum of its terms, each times the value of its mode. -/
theorem affineFactor_mulVec (Y X : E → Bool) (e : E) :
    affineFactor (Y e) (W.mulVec (fun e' => if X e' then 1 else 0) e) =
      ∑ o : Option M, S.choiceTerm Y X e o * o.elim 1 (S.modeValue X) := by
  rw [S.mulVec_apply, affineFactor_add, Fintype.sum_option, mul_sum]
  simp only [choiceTerm, Option.elim, mul_one, mul_assoc]

end Forms

/-! ### Coefficients of mode monomials -/

section Coefficients

variable [Fintype E] [DecidableEq E] [DecidableEq P] [DecidableEq G] [DecidableEq M]

/-- The coefficient of the mode monomial with exponents `β` in the product of the affine factors
of the row ports of the block `k`. It sums, over the ways `φ` to pick in each factor either its
local term or one of the modes targeted at `k`, each mode `Z` of `k` picked `β Z` times, the
product of the picked terms. It depends only on the exponents of the modes of `k`. -/
@[expose] def blockCoeff (k : P × G) (β : M → ℕ) (Y X : E → Bool) : R :=
  ∑ φ : {e // S.rowBlock e = k} → Option M,
    if (∀ e Z, φ e = some Z → S.targetBlock Z = k) ∧
        ∀ Z, S.targetBlock Z = k → #{e | φ e = some Z} = β Z then
      ∏ e, S.choiceTerm Y X e.1 (φ e)
    else 0

/-- The tensor at the vertex of packet `q` in the child of group `g`: the coefficient of the mode
monomial `β` for the row ports of `q` in group `g`, times `L_Z(X) ^ β Z` for the modes of `q` with
source `g`. -/
@[expose] def packetTensor (β : M → ℕ) (q : P) (g : G) (Y X : E → Bool) : R :=
  S.blockCoeff (q, g) β Y X * ∏ Z with S.sourceBlock Z = (q, g), S.modeValue X Z ^ β Z

/-- A block coefficient depends only on the exponents of the modes of its block. -/
theorem blockCoeff_congr_exponents {k : P × G} {β β' : M → ℕ}
    (h : ∀ Z, S.targetBlock Z = k → β Z = β' Z) (Y X : E → Bool) :
    S.blockCoeff k β Y X = S.blockCoeff k β' Y X := by
  refine sum_congr rfl fun φ _ => ?_
  refine if_congr (and_congr Iff.rfl (forall_congr' fun Z => imp_congr_right fun hZ => ?_)) rfl
    rfl
  rw [h Z hZ]

/-- **A packet tensor is local:** it reads only the row and column ports of its packet and
group. -/
theorem packetTensor_congr (β : M → ℕ) (q : P) (g : G) {Y Y' X X' : E → Bool}
    (hY : ∀ e, S.packet e = q → S.group (N.src e) = g → Y e = Y' e)
    (hX : ∀ e, S.packet e = q → S.group (N.tgt e) = g → X e = X' e) :
    S.packetTensor β q g Y X = S.packetTensor β q g Y' X' := by
  unfold packetTensor blockCoeff
  congr 1
  · refine sum_congr rfl fun φ _ => if_congr Iff.rfl (prod_congr rfl fun e _ => ?_) rfl
    obtain ⟨e, he⟩ := e
    simp only [rowBlock, Prod.mk.injEq] at he
    have hl : S.localForm X e = S.localForm X' e := S.localForm_congr fun e' hp hg =>
      hX e' (hp.trans he.1) (hg.trans he.2)
    cases φ ⟨e, _⟩ <;> simp only [choiceTerm, hY e he.1 he.2, hl]
  · refine prod_congr rfl fun Z hZ => ?_
    simp only [sourceBlock, mem_filter, mem_univ, true_and, Prod.mk.injEq] at hZ
    rw [S.modeValue_congr fun e hp hg => hX e (hp.trans hZ.1) (hg.trans hZ.2)]

/-- A choice of terms with exponent `β Z` above the number of edges never exists, so the block
coefficient of such a mode's block vanishes. -/
theorem blockCoeff_eq_zero_of_card_lt {Z : M} {β : M → ℕ} (hZ : Fintype.card E < β Z)
    (Y X : E → Bool) : S.blockCoeff (S.targetBlock Z) β Y X = 0 := by
  refine sum_eq_zero fun φ _ => ite_eq_right fun h => ?_
  have hle : #{e | φ e = some Z} ≤ Fintype.card E :=
    (card_filter_le _ _).trans (by rw [card_univ]; exact Fintype.card_subtype_le _)
  rw [h.2 Z rfl] at hle
  omega

omit [DecidableEq E] in
/-- The weight of a picked term: zero for the local term and `w Z` for the mode `Z`. -/
private theorem sum_elim_weight {k : P × G} (w : M → ℕ) (φ : {e // S.rowBlock e = k} → Option M) :
    ∑ e, (φ e).elim 0 w = ∑ Z, #{e | φ e = some Z} * w Z := by
  rw [← sum_fiberwise' univ φ (fun o => o.elim 0 w)]
  simp only [sum_const, smul_eq_mul, Fintype.sum_option, Option.elim, mul_zero, zero_add]

/-- **The coefficient of a mode monomial is divisible by `π` to its total weight**, when the
coefficient of each mode `Z` is divisible by `π ^ w Z`. -/
theorem pow_dvd_blockCoeff (w : M → ℕ) {π : R} (hdiv : ∀ e Z, π ^ w Z ∣ S.coeff e Z)
    (k : P × G) (β : M → ℕ) (Y X : E → Bool) :
    π ^ (∑ Z with S.targetBlock Z = k, w Z * β Z) ∣ S.blockCoeff k β Y X := by
  refine dvd_sum fun φ _ => ?_
  split_ifs with h
  · have hexp : ∑ Z with S.targetBlock Z = k, w Z * β Z = ∑ e, (φ e).elim 0 w := by
      rw [sum_elim_weight, sum_filter]
      refine sum_congr rfl fun Z _ => ?_
      split_ifs with hZ
      · rw [h.2 Z hZ, mul_comm]
      · have : #{e | φ e = some Z} = 0 := card_eq_zero.mpr (filter_eq_empty_iff.mpr
          fun e _ he => hZ (h.1 e Z he))
        rw [this, zero_mul]
    rw [hexp, ← prod_pow_eq_pow_sum]
    refine prod_dvd_prod_of_dvd _ _ fun e _ => ?_
    cases φ e with
    | none => simp only [Option.elim, pow_zero, one_dvd]
    | some Z => exact Dvd.dvd.mul_left (hdiv e.1 Z) _
  · exact dvd_zero _

/-- The product of the block coefficients vanishes when the total weight reaches `p`, if
`π ^ p = 0`. -/
theorem prod_blockCoeff_eq_zero (w : M → ℕ) {π : R} (hdiv : ∀ e Z, π ^ w Z ∣ S.coeff e Z)
    {p : ℕ} (hπ : π ^ p = 0) [Fintype P] [Fintype G] {β : M → ℕ}
    (hβ : p ≤ ∑ Z, w Z * β Z) (Y X : E → Bool) : ∏ k, S.blockCoeff k β Y X = 0 := by
  have hdvd : π ^ (∑ Z, w Z * β Z) ∣ ∏ k, S.blockCoeff k β Y X := by
    rw [← sum_fiberwise univ S.targetBlock (fun Z => w Z * β Z), ← prod_pow_eq_pow_sum]
    exact prod_dvd_prod_of_dvd _ _ fun k _ => S.pow_dvd_blockCoeff w hdiv k β Y X
  rw [← Nat.add_sub_cancel' hβ, pow_add, hπ, zero_mul] at hdvd
  exact zero_dvd_iff.mp hdvd

end Coefficients

/-! ### The mode expansion -/

section Expansion

variable [Fintype E] [DecidableEq E] [DecidableEq P] [DecidableEq G] [DecidableEq M]

omit [DecidableEq E] in
/-- The product of the values of the picked modes, the local term counting as one. -/
private theorem prod_elim_modeValue {k : P × G} (φ : {e // S.rowBlock e = k} → Option M)
    (X : E → Bool) :
    ∏ e, (φ e).elim 1 (S.modeValue X) = ∏ Z, S.modeValue X Z ^ #{e | φ e = some Z} := by
  rw [← prod_fiberwise' univ φ (fun o => o.elim 1 (S.modeValue X))]
  simp only [prod_const, Fintype.prod_option, Option.elim, one_pow, one_mul]

/-- The exponent tuples supported on the modes of one block, with entries at most `n`. -/
private abbrev blockBox (n : ℕ) (k : P × G) : Finset (M → ℕ) :=
  {β ∈ Fintype.piFinset fun _ => range (n + 1) | ∀ Z, S.targetBlock Z ≠ k → β Z = 0}

/-- **Mode expansion of one block.** The product of the affine factors of the row ports of a
block is a polynomial in the values of the modes targeted at it, with the block coefficients. -/
private theorem prod_block (Y X : E → Bool) (k : P × G) :
    ∏ e : {e // S.rowBlock e = k},
        affineFactor (Y e) (W.mulVec (fun e' => if X e' then 1 else 0) e) =
      ∑ β ∈ S.blockBox (Fintype.card E) k, S.blockCoeff k β Y X * ∏ Z, S.modeValue X Z ^ β Z := by
  simp only [S.affineFactor_mulVec, Fintype.prod_sum, prod_mul_distrib, S.prod_elim_modeValue,
    blockCoeff, sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun φ _ => ?_
  set c : M → ℕ := fun Z => #{e | φ e = some Z} with hc
  by_cases hv : ∀ e Z, φ e = some Z → S.targetBlock Z = k
  · rw [sum_eq_single c]
    · rw [ite_eq_left ⟨hv, fun Z _ => rfl⟩]
    · intro β hβ hne
      refine ite_eq_right fun h => hne (funext fun Z => ?_)
      by_cases hZ : S.targetBlock Z = k
      · exact (h.2 Z hZ).symm
      · rw [(mem_filter.mp hβ).2 Z hZ]
        exact (card_eq_zero.mpr (filter_eq_empty_iff.mpr fun e _ he => hZ (hv e Z he))).symm
    · intro hn
      refine absurd ?_ hn
      simp only [mem_filter, Fintype.mem_piFinset, mem_range]
      refine ⟨fun Z => Nat.lt_succ_of_le ((card_filter_le _ _).trans ?_), fun Z hZ => ?_⟩
      · rw [card_univ]
        exact Fintype.card_subtype_le _
      · exact card_eq_zero.mpr (filter_eq_empty_iff.mpr fun e _ he => hZ (hv e Z he))
  · push Not at hv
    obtain ⟨e, Z, he, hZ⟩ := hv
    rw [sum_eq_zero fun β _ => ite_eq_right fun h => hZ (h.1 e Z he)]
    refine mul_eq_zero_of_left (prod_eq_zero (mem_univ e) ?_) _
    rw [he, choiceTerm]
    refine mul_eq_zero_of_right _ (by_contra fun h0 => hZ ?_)
    obtain ⟨hp, hg⟩ := S.coeff_ne_zero e.1 Z h0
    rw [targetBlock, hp, hg]
    exact e.2

omit [Fintype E] [DecidableEq E] in
/-- Sums over the tuples supported on each block combine into one sum over all tuples. -/
private theorem prod_sum_blockBox (n : ℕ) [Fintype P] [Fintype G] (f : P × G → (M → ℕ) → R) :
    ∏ k, ∑ β ∈ S.blockBox n k, f k β =
      ∑ β ∈ Fintype.piFinset (fun _ : M => range (n + 1)),
        ∏ k, f k (fun Z => if S.targetBlock Z = k then β Z else 0) := by
  rw [prod_univ_sum]
  refine sum_nbij' (fun x Z => x (S.targetBlock Z) Z)
    (fun β k Z => if S.targetBlock Z = k then β Z else 0) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Fintype.mem_piFinset, mem_filter] at hx ⊢
    exact fun Z => (hx (S.targetBlock Z)).1 Z
  · intro β hβ
    simp only [Fintype.mem_piFinset, mem_filter, mem_range] at hβ ⊢
    refine fun k => ⟨fun Z => ?_, fun Z hZ => ite_eq_right hZ⟩
    split_ifs
    exacts [hβ Z, Nat.succ_pos n]
  · intro x hx
    simp only [Fintype.mem_piFinset, mem_filter] at hx
    funext k Z
    split_ifs with h
    · subst h
      rfl
    · exact ((hx k).2 Z h).symm
  · intro β _
    funext Z
    simp only [ite_true]
  · intro x hx
    simp only [Fintype.mem_piFinset, mem_filter] at hx
    refine prod_congr rfl fun k _ => congrArg (f k) (funext fun Z => ?_)
    split_ifs with h
    · subst h
      rfl
    · exact (hx k).2 Z h

/-- **Mode expansion.** The product of all affine factors is a sum over exponent tuples of the
product of the block coefficients times the mode monomial. -/
private theorem prod_affineFactor_eq_sum [Fintype P] [Fintype G] (Y X : E → Bool) :
    ∏ e, affineFactor (Y e) (W.mulVec (fun e' => if X e' then 1 else 0) e) =
      ∑ β ∈ Fintype.piFinset (fun _ : M => range (Fintype.card E + 1)),
        (∏ k, S.blockCoeff k β Y X) * ∏ Z, S.modeValue X Z ^ β Z := by
  rw [← Fintype.prod_fiberwise S.rowBlock]
  simp only [S.prod_block, S.prod_sum_blockBox]
  refine sum_congr rfl fun β _ => ?_
  rw [prod_mul_distrib]
  congr 1
  · exact prod_congr rfl fun k _ => S.blockCoeff_congr_exponents (fun Z hZ => ite_eq_left hZ) Y X
  · rw [prod_comm]
    refine prod_congr rfl fun Z _ => ?_
    simp only [pow_ite, pow_zero]
    exact Fintype.prod_ite_eq (S.targetBlock Z) _

/-- **Truncated mode expansion.** When `π ^ p = 0`, only the tuples in the budget remain. -/
private theorem prod_affineFactor_eq_sum_modeBudget [Fintype P] [Fintype G] (w : M → ℕ)
    (hw : ∀ Z, 0 < w Z) {π : R} {p : ℕ} (hπ : π ^ p = 0) (hdiv : ∀ e Z, π ^ w Z ∣ S.coeff e Z)
    (Y X : E → Bool) :
    ∏ e, affineFactor (Y e) (W.mulVec (fun e' => if X e' then 1 else 0) e) =
      ∑ β ∈ modeBudget w p, (∏ k, S.blockCoeff k β Y X) * ∏ Z, S.modeValue X Z ^ β Z := by
  rw [S.prod_affineFactor_eq_sum]
  set box := Fintype.piFinset (fun _ : M => range (Fintype.card E + 1))
  rw [← sum_subset (inter_subset_left (s₁ := box) (s₂ := modeBudget w p)),
    ← sum_subset (inter_subset_right (s₁ := box) (s₂ := modeBudget w p))]
  · intro β hβ hn
    have hbox : β ∉ box := fun h => hn (mem_inter.mpr ⟨h, hβ⟩)
    simp only [box, Fintype.mem_piFinset, mem_range, not_forall, not_lt] at hbox
    obtain ⟨Z, hZ⟩ := hbox
    have hZ' : Fintype.card E < β Z := by omega
    rw [prod_eq_zero (i := S.targetBlock Z) (mem_univ _)
      (S.blockCoeff_eq_zero_of_card_lt hZ' Y X), zero_mul]
  · intro β hβ hn
    have hb : β ∉ modeBudget w p := fun h => hn (mem_inter.mpr ⟨hβ, h⟩)
    rw [mem_modeBudget hw, not_lt] at hb
    rw [S.prod_blockCoeff_eq_zero w hdiv hπ hb, zero_mul]

end Expansion

/-! ### Child networks -/

section Child

variable [Fintype E] [DecidableEq E] [DecidableEq P] [DecidableEq G] [DecidableEq M]
  [DecidableEq V]

/-- The *child network* of the group `g` for the exponents `β` (§D.4.6). Its vertices are the
vertices of group `g`, from both sides, and one vertex per packet. For every row port `e` of group
`g` it has an edge from the row of `e` to the packet of `e`, and for every column port of group
`g` an edge from the column of `e` to the packet of `e`. A row keeps its tensor, reading the row
bits on its edges, and a column keeps its tensor, reading the column bits; the tensor at a packet
is `packetTensor`. -/
@[expose] def child (β : M → ℕ) (g : G) :
    TensorNetwork R Bool ({v // S.group v = g} ⊕ P)
      ({e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g}) where
  src := Sum.elim (fun e => .inl ⟨N.src e.1, e.2⟩) (fun e => .inl ⟨N.tgt e.1, e.2⟩)
  tgt := Sum.elim (fun e => .inr (S.packet e.1)) (fun e => .inr (S.packet e.1))
  tensor
    | .inl v, y =>
      if S.side v.1 then
        N.tensor v.1 fun e => if h : N.src e = v.1 then y (.inl ⟨e, h ▸ v.2⟩) else false
      else
        N.tensor v.1 fun e => if h : N.tgt e = v.1 then y (.inr ⟨e, h ▸ v.2⟩) else false
    | .inr q, y =>
      S.packetTensor β q g (fun e => if h : S.group (N.src e) = g then y (.inl ⟨e, h⟩) else false)
        (fun e => if h : S.group (N.tgt e) = g then y (.inr ⟨e, h⟩) else false)
  tensor_congr := by
    rintro (v | q) y y' h
    · have hs : ∀ e (he : N.src e = v.1), y (.inl ⟨e, he ▸ v.2⟩) = y' (.inl ⟨e, he ▸ v.2⟩) := by
        intro e he
        exact h _ (Or.inl (congrArg Sum.inl (Subtype.ext he)))
      have ht : ∀ e (he : N.tgt e = v.1), y (.inr ⟨e, he ▸ v.2⟩) = y' (.inr ⟨e, he ▸ v.2⟩) := by
        intro e he
        exact h _ (Or.inl (congrArg Sum.inl (Subtype.ext he)))
      simp only
      split_ifs
      · congr 1
        funext e
        split_ifs with he
        exacts [hs e he, rfl]
      · congr 1
        funext e
        split_ifs with he
        exacts [ht e he, rfl]
    · refine S.packetTensor_congr β q g (fun e hq hg => ?_) (fun e hq hg => ?_)
      · simp only [hg, dite_true]
        exact h _ (Or.inr (by simp only [Sum.elim_inl, hq]))
      · simp only [hg, dite_true]
        exact h _ (Or.inr (by simp only [Sum.elim_inr, hq]))

@[simp] theorem child_src_inl (β : M → ℕ) (g : G) (e : {e // S.group (N.src e) = g}) :
    (S.child β g).src (.inl e) = .inl ⟨N.src e.1, e.2⟩ :=
  rfl

@[simp] theorem child_src_inr (β : M → ℕ) (g : G) (e : {e // S.group (N.tgt e) = g}) :
    (S.child β g).src (.inr e) = .inl ⟨N.tgt e.1, e.2⟩ :=
  rfl

@[simp] theorem child_tgt_inl (β : M → ℕ) (g : G) (e : {e // S.group (N.src e) = g}) :
    (S.child β g).tgt (.inl e) = .inr (S.packet e.1) :=
  rfl

@[simp] theorem child_tgt_inr (β : M → ℕ) (g : G) (e : {e // S.group (N.tgt e) = g}) :
    (S.child β g).tgt (.inr e) = .inr (S.packet e.1) :=
  rfl

/-- **Children are bipartite**, with the old vertices on one side and the packets on the other;
every edge runs from an old vertex to a packet. -/
theorem isBipartite_child (β : M → ℕ) (g : G) : (S.child β g).IsBipartite :=
  ⟨Sum.isLeft, by rintro (e | e) <;> simp⟩

omit [DecidableEq E] [DecidableEq P] [DecidableEq M] [DecidableEq V] in
/-- A child has one edge for each port of its group. -/
theorem card_edges_child (g : G) :
    Fintype.card ({e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g}) =
      #{e | S.group (N.src e) = g} + #{e | S.group (N.tgt e) = g} := by
  rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]

/-- The bits of the ports of group `g`, read off the row bits `Y` and the column bits `X`. -/
private abbrev groupBits (Y X : E → Bool) (g : G) :
    {e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g} → Bool :=
  Sum.elim (fun e => Y e.1) (fun e => X e.1)

/-- On the bits of its group, an old vertex of a child reads the row bits if it is a row and the
column bits if it is a column. -/
private theorem child_tensor_inl_groupBits (β : M → ℕ) (g : G) (v : {v // S.group v = g})
    (Y X : E → Bool) :
    (S.child β g).tensor (.inl v) (S.groupBits Y X g) =
      if S.side v.1 then N.tensor v.1 Y else N.tensor v.1 X := by
  simp only [child]
  split_ifs with hv
  · refine N.tensor_congr v.1 _ _ fun e he => ?_
    by_cases hs : N.src e = v.1
    · simp only [hs, dite_true, Sum.elim_inl]
    · have ht : N.tgt e = v.1 := he.resolve_left hs
      have := S.side_tgt e
      rw [ht, hv] at this
      exact absurd this (by decide)
  · refine N.tensor_congr v.1 _ _ fun e he => ?_
    by_cases ht : N.tgt e = v.1
    · simp only [ht, dite_true, Sum.elim_inr]
    · have hs : N.src e = v.1 := he.resolve_right ht
      have := S.side_src e
      rw [hs] at this
      exact absurd this hv

/-- On the bits of its group, a packet of a child reads the row and column bits. -/
private theorem child_tensor_inr_groupBits (β : M → ℕ) (g : G) (q : P) (Y X : E → Bool) :
    (S.child β g).tensor (.inr q) (S.groupBits Y X g) = S.packetTensor β q g Y X := by
  simp only [child]
  refine S.packetTensor_congr β q g (fun e _ hg => ?_) (fun e _ hg => ?_)
  · simp only [hg, dite_true, Sum.elim_inl]
  · simp only [hg, dite_true, Sum.elim_inr]

/-- **The weight of an assignment factors over the groups.** For every tuple `β`, the term of
the expanded deformed contraction at the row bits `Y` and column bits `X` is the product, over the
groups, of the weights of the bits of each group in its child. -/
private theorem weight_eq_prod_child [Fintype V] [Fintype P] [Fintype G] (β : M → ℕ)
    (Y X : E → Bool) :
    (∏ v ∈ univ.filter (S.side · = true), N.tensor v Y) *
        (∏ v ∈ univ.filter (S.side · = false), N.tensor v X) *
        ((∏ k, S.blockCoeff k β Y X) * ∏ Z, S.modeValue X Z ^ β Z) =
      ∏ g, ∏ x, (S.child β g).tensor x (S.groupBits Y X g) := by
  simp only [Fintype.prod_sum_type, S.child_tensor_inl_groupBits, S.child_tensor_inr_groupBits,
    prod_mul_distrib]
  rw [Fintype.prod_fiberwise S.group (fun v => if S.side v then N.tensor v Y else N.tensor v X),
    prod_ite]
  simp only [Bool.not_eq_true]
  have hk : ∏ k, S.blockCoeff k β Y X = ∏ g, ∏ q, S.blockCoeff (q, g) β Y X := by
    rw [Fintype.prod_prod_type, prod_comm]
  have hZ : ∏ Z, S.modeValue X Z ^ β Z =
      ∏ g, ∏ q, ∏ Z with S.sourceBlock Z = (q, g), S.modeValue X Z ^ β Z := by
    rw [prod_comm, ← Fintype.prod_prod_type (f := fun k => ∏ Z with S.sourceBlock Z = k,
      S.modeValue X Z ^ β Z), prod_fiberwise]
  simp only [packetTensor, prod_mul_distrib, hk, hZ]

/-- Splitting the row and column bits by group. -/
private def splitBits :
    (E → Bool) × (E → Bool) ≃
      ∀ g, ({e // S.group (N.src e) = g} ⊕ {e // S.group (N.tgt e) = g} → Bool) where
  toFun YX g := S.groupBits YX.1 YX.2 g
  invFun y := (fun e => y _ (.inl ⟨e, rfl⟩), fun e => y _ (.inr ⟨e, rfl⟩))
  left_inv _ := rfl
  right_inv y := by
    funext g c
    rcases c with ⟨e, rfl⟩ | ⟨e, rfl⟩ <;> rfl

/-- **The sum over the bits factors over the groups**: for each tuple `β`, the sum over all row
and column bits of the expanded term is the product of the contractions of the children. -/
private theorem sum_weight_eq_prod_contraction_child [Fintype V] [Fintype P] [Fintype G]
    (β : M → ℕ) :
    ∑ X : E → Bool, ∑ Y : E → Bool,
        (∏ v ∈ univ.filter (S.side · = true), N.tensor v Y) *
          (∏ v ∈ univ.filter (S.side · = false), N.tensor v X) *
          ((∏ k, S.blockCoeff k β Y X) * ∏ Z, S.modeValue X Z ^ β Z) =
      ∏ g, (S.child β g).contraction := by
  simp only [S.weight_eq_prod_child, contraction]
  rw [Fintype.prod_sum, sum_comm, ← Fintype.sum_prod_type']
  exact Fintype.sum_equiv S.splitBits _ _ fun _ => rfl

/-- **The exact child expansion.** In every commutative ring, the deformed contraction is the sum,
over the exponent tuples with entries at most the number of edges, of the products over the
groups of the contractions of the children. -/
theorem deformedContraction_eq_sum_prod_contraction_child_of_le [Fintype V] [Fintype P]
    [Fintype G] :
    N.deformedContraction S.side W =
      ∑ β ∈ Fintype.piFinset (fun _ : M => range (Fintype.card E + 1)),
        ∏ g, (S.child β g).contraction := by
  simp only [deformedContraction, S.prod_affineFactor_eq_sum, mul_sum]
  exact (sum_congr rfl fun X _ => sum_comm).trans
    (sum_comm.trans (sum_congr rfl fun β _ => S.sum_weight_eq_prod_contraction_child β))

/-- **The child identity** ((D.16) of [OpenAI2026ETH]). If the coefficient of every mode `Z` is
divisible by `π ^ w Z`, with positive weights, and `π ^ p = 0`, then the deformed contraction is
the sum, over the exponent tuples of total weight below `p`, of the products over the groups of
the contractions of the children. In the manuscript, `π = 2`, `p = p_t` and the ring is
`A / 2 ^ p_t`. -/
theorem deformedContraction_eq_sum_prod_contraction_child [Fintype V] [Fintype P] [Fintype G]
    (w : M → ℕ) (hw : ∀ Z, 0 < w Z) {π : R} {p : ℕ} (hπ : π ^ p = 0)
    (hdiv : ∀ e Z, π ^ w Z ∣ S.coeff e Z) :
    N.deformedContraction S.side W = ∑ β ∈ modeBudget w p, ∏ g, (S.child β g).contraction := by
  simp only [deformedContraction, S.prod_affineFactor_eq_sum_modeBudget w hw hπ hdiv, mul_sum]
  exact (sum_congr rfl fun X _ => sum_comm).trans
    (sum_comm.trans (sum_congr rfl fun β _ => S.sum_weight_eq_prod_contraction_child β))

end Child

end ModeSplitting

end TensorNetwork

end Cslib.Circuits.Frontier
