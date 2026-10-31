/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.BlockNetwork
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Binarize
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Explicit block-counting networks

The block-counting network of a schedule (`Turing.MultiTapePTM.blockNetwork`) carries structured
letters on its edges: control records and block contents (`Turing.MultiTapePTM.BlockLetter`).
This module writes it out as an explicit Boolean tensor network
(`Cslib.Circuits.Frontier.ExplicitTensorNetwork`), the form that a contraction algorithm reads,
completing the construction of Lemma 2.2 of the note *Deterministic simulations of
nondeterministic and randomized time* (30 October 2026) formalized in issue #1833:

1. **Binarize** by a concrete injective code of the letters
   (`Turing.MultiTapePTM.letterCode`), in `letterBits k s b = (s + k + 4) * b` bits, where `s`
   numbers the states. A letter is numbered by `Turing.MultiTapePTM.letterEquiv`, composed of the
   standard numberings of finite products, sums, options and functions (`finProdFinEquiv`,
   `finSumFinEquiv`, `finSuccEquiv`, `finFunctionFinEquiv`); its code is the binary digits of its
   number.
2. **Subdivide** every Boolean edge by an equality tensor, which makes the network bipartite.
3. **Write out** (`Cslib.Circuits.Frontier.TensorNetwork.toExplicit`), numbering the old vertices
   (the intervals and sinks) first and the subdivision vertices after them, both by concrete
   numberings (`Turing.MultiTapePTM.explicitVertexEquiv`, `Turing.MultiTapePTM.explicitEdgeEquiv`).

Each step preserves the contraction, so the explicit networks of the schedules still sum to the
accepting count (`Turing.MultiTapePTM.sum_contraction_explicitBlockNetwork`).

**Size.** With `q` intervals, `k` work tapes and `m = letterBits k s b`, the explicit network has
`2 * (q * (3 * k + 1) * m)` edges and maximum degree at most `2 * (3 * k + 1) * m`, both `O(b)` per
interval. Its first `q * (3 * k + 2)` vertices are the rows of a bipartition: every edge has
exactly one port at a row and one at a column
(`Cslib.Circuits.Frontier.ExplicitTensorNetwork.IsRowsFirstBipartite`). Every table has length
`2 ^ (number of ports)`, and its entries are at most `2 ^ b`.

These are the inputs of the Boolean tensor contraction theorem [OpenAI2026ETH, Theorem D.1]
as the counting simulation of #1833 uses it: with `b = ⌈log₂ (t + 2)⌉` and `q * b ≤ 2 t`, the
networks have `O(t)` edges and maximum degree `O(log t)`.

## Main definitions

* `Turing.MultiTapePTM.letterEquiv`, `Turing.MultiTapePTM.letterCode`,
  `Turing.MultiTapePTM.letterBits`: the numbering and binary code of the letters.
* `Turing.MultiTapePTM.blockEdgeEquiv`, `Turing.MultiTapePTM.explicitVertexEquiv`,
  `Turing.MultiTapePTM.explicitEdgeEquiv`: the numberings of edges and vertices.
* `Turing.MultiTapePTM.explicitBlockNetwork`: the explicit block-counting network of a schedule.

## Main results

* `Turing.MultiTapePTM.letterCode_injective`: the code is injective.
* `Turing.MultiTapePTM.contraction_explicitBlockNetwork`: writing the network out preserves its
  contraction.
* `Turing.MultiTapePTM.sum_contraction_explicitBlockNetwork`: summed over the schedules, the
  contractions are the accepting count.
* `Turing.MultiTapePTM.admissible_explicitBlockNetwork`: at a clock `t` with `b = O(log t)` and
  `q * b ≤ 2 t`, the network is rows-first bipartite with `O(t)` edges and degree `O(log t)`.
* `Turing.MultiTapePTM.numEdges_explicitBlockNetwork`,
  `Turing.MultiTapePTM.length_vertices_explicitBlockNetwork`,
  `Turing.MultiTapePTM.maxDegree_explicitBlockNetwork_le`,
  `Turing.MultiTapePTM.isRowsFirstBipartite_explicitBlockNetwork`,
  `Turing.MultiTapePTM.length_table_explicitBlockNetwork`,
  `Turing.MultiTapePTM.entry_le_explicitBlockNetwork`: size, degree, bipartition and tables.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On Time Versus Space*][HopcroftPaulValiant1977]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.1 (p. 53)
-/

public section

namespace Turing

namespace MultiTapeNTM.ChoiceTable.OutputTrack

/-- The output tracks numbered `empty ↦ 0`, `accept ↦ 1`, `other ↦ 2`. -/
@[expose] def equivFin : OutputTrack ≃ Fin 3 where
  toFun
    | .empty => 0
    | .accept => 1
    | .other => 2
  invFun i := if i = 0 then .empty else if i = 1 then .accept else .other
  left_inv t := by cases t <;> rfl
  right_inv i := by fin_cases i <;> rfl

end MultiTapeNTM.ChoiceTable.OutputTrack

namespace MultiTapePTM

open Cslib.Circuits.Frontier MultiTapeNTM.ChoiceTable Function

variable {k q s : ℕ} {State : Type} {b : ℕ}

/-! ### Numbering and coding the letters -/

section Letters

variable [NeZero b]

/-- The residues modulo `b > 0` numbered by their values. -/
@[expose] def zmodEquiv (b : ℕ) [NeZero b] : ZMod b ≃ Fin b :=
  (ZMod.finEquiv b).toEquiv.symm

@[simp] theorem val_zmodEquiv (r : ZMod b) : (zmodEquiv b r : ℕ) = r.val := by
  obtain _ | b := b
  · exact absurd rfl (NeZero.ne 0)
  · rfl

/-- The contents of a cell numbered `none ↦ 0`, `some false ↦ 1`, `some true ↦ 2`. -/
@[expose] def cellEquiv : Option Bool ≃ Fin 3 :=
  (Equiv.optionCongr finTwoEquiv.symm).trans (finSuccEquiv 2).symm

/-- The control records numbered: the state (with `none` first, then the states numbered by `e`),
then the head offsets as `k + 1` digits in base `b`, then the output track. -/
@[expose] def controlEquiv (e : State ≃ Fin s) :
    BlockControl k State b ≃ Fin ((s + 1) * (b ^ (k + 1) * 3)) :=
  (Equiv.prodCongr ((Equiv.optionCongr e).trans (finSuccEquiv s).symm)
    ((Equiv.prodCongr
      ((Equiv.arrowCongr (finSuccEquiv k).symm (zmodEquiv b)).trans finFunctionFinEquiv)
      OutputTrack.equivFin).trans finProdFinEquiv)).trans finProdFinEquiv

/-- The block contents numbered as `b` digits in base `3`. -/
@[expose] def contentsEquiv (b : ℕ) [NeZero b] : (ZMod b → Option Bool) ≃ Fin (3 ^ b) :=
  (Equiv.arrowCongr (zmodEquiv b) cellEquiv).trans finFunctionFinEquiv

/-- **The letters numbered**: the control records first (`Turing.MultiTapePTM.controlEquiv`),
then the block contents (`Turing.MultiTapePTM.contentsEquiv`). -/
@[expose] def letterEquiv (e : State ≃ Fin s) :
    BlockLetter k State b ≃ Fin ((s + 1) * (b ^ (k + 1) * 3) + 3 ^ b) :=
  (Equiv.sumCongr (controlEquiv e) (contentsEquiv b)).trans finSumFinEquiv

/-- The number of bits of a letter: `(s + k + 4) * b`, for `s` states and `k` work tapes. -/
@[expose] def letterBits (k s b : ℕ) : ℕ := (s + k + 4) * b

/-- Every letter number fits in `letterBits k s b` bits. -/
theorem card_letter_le_two_pow :
    (s + 1) * (b ^ (k + 1) * 3) + 3 ^ b ≤ 2 ^ letterBits k s b := by
  have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr (NeZero.ne b)
  have hs : s + 1 ≤ 2 ^ (s * b) :=
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_right two_pos (Nat.le_mul_of_pos_right s hb))
  have hbk : b ^ (k + 1) ≤ 2 ^ ((k + 1) * b) := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self).le _
  have h3 : 3 ≤ 2 ^ (2 * b) := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * b) := Nat.pow_le_pow_right two_pos (by omega)
  have h3b : 3 ^ b ≤ 2 ^ (2 * b) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _
  have hctl : (s + 1) * (b ^ (k + 1) * 3) ≤ 2 ^ ((s + k + 3) * b) := by
    calc (s + 1) * (b ^ (k + 1) * 3) ≤ 2 ^ (s * b) * (2 ^ ((k + 1) * b) * 2 ^ (2 * b)) :=
          Nat.mul_le_mul hs (Nat.mul_le_mul hbk h3)
      _ = 2 ^ ((s + k + 3) * b) := by rw [← pow_add, ← pow_add]; ring_nf
  have hcon : 3 ^ b ≤ 2 ^ ((s + k + 3) * b) :=
    h3b.trans (Nat.pow_le_pow_right two_pos (Nat.mul_le_mul_right b (by omega)))
  calc _ ≤ 2 ^ ((s + k + 3) * b) + 2 ^ ((s + k + 3) * b) := Nat.add_le_add hctl hcon
    _ = 2 ^ ((s + k + 3) * b + 1) := by rw [pow_succ]; ring
    _ ≤ 2 ^ letterBits k s b :=
        Nat.pow_le_pow_right two_pos (by unfold letterBits; nlinarith)

/-- **The letter code**: the `letterBits k s b` binary digits, least significant first, of the
number of a letter (`Turing.MultiTapePTM.letterEquiv`). -/
@[expose] def letterCode (e : State ≃ Fin s) (l : BlockLetter k State b) :
    Fin (letterBits k s b) → Bool :=
  fun j => (letterEquiv e l : ℕ).testBit j

/-- **The letter code is injective**: letter numbers fit in `letterBits k s b` bits. -/
theorem letterCode_injective (e : State ≃ Fin s) :
    Injective (letterCode (k := k) (b := b) e) := by
  intro l l' h
  have hlt : ∀ l : BlockLetter k State b, (letterEquiv e l : ℕ) < 2 ^ letterBits k s b :=
    fun l => (letterEquiv e l).isLt.trans_le card_letter_le_two_pow
  refine (letterEquiv e).injective (Fin.ext (Nat.eq_of_testBit_eq fun j => ?_))
  by_cases hj : j < letterBits k s b
  · exact congrFun h ⟨j, hj⟩
  · rw [Nat.testBit_lt_two_pow ((hlt l).trans_le (Nat.pow_le_pow_right two_pos (not_lt.mp hj))),
      Nat.testBit_lt_two_pow ((hlt l').trans_le (Nat.pow_le_pow_right two_pos (not_lt.mp hj)))]

instance : Nonempty (BlockLetter k State b) := ⟨.inr fun _ => none⟩

end Letters

/-! ### Numbering the edges and vertices -/

-- A named instance keeps the instances on the vertex types of the explicit network small.
instance (k q : ℕ) : DecidableEq (BlockEdge k q) :=
  inferInstanceAs (DecidableEq (Fin q ⊕ (Fin q × Fin k × Fin 3)))

/-- The edges of a block-counting network numbered: the control edges first, then the block edges
`(i, h, d)` in lexicographic order. -/
@[expose] def blockEdgeEquiv (k q : ℕ) : BlockEdge k q ≃ Fin (q * (3 * k + 1)) :=
  ((Equiv.sumCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)).trans
      finSumFinEquiv).trans (finCongr (by ring))

/-- The vertices of the explicit network numbered: the old vertices first (the intervals, then the
sinks in the order of their edges), then the subdivision vertices, one for each copy `(e, j)` of an
edge. -/
@[expose] def explicitVertexEquiv (k q m : ℕ) :
    (Fin q ⊕ BlockEdge k q) ⊕ (BlockEdge k q × Fin m) ≃
      Fin (q * (3 * k + 2) + q * (3 * k + 1) * m) :=
  (Equiv.sumCongr
    (((Equiv.sumCongr (Equiv.refl _) (blockEdgeEquiv k q)).trans finSumFinEquiv).trans
      (finCongr (by ring)))
    ((Equiv.prodCongr (blockEdgeEquiv k q) (Equiv.refl _)).trans finProdFinEquiv)).trans
    finSumFinEquiv

/-- The edges of the explicit network numbered: the source halves of the copies `(e, j)` first,
then their target halves. -/
@[expose] def explicitEdgeEquiv (k q m : ℕ) :
    (BlockEdge k q × Fin m) ⊕ (BlockEdge k q × Fin m) ≃ Fin (2 * (q * (3 * k + 1) * m)) :=
  ((Equiv.sumCongr ((Equiv.prodCongr (blockEdgeEquiv k q) (Equiv.refl _)).trans finProdFinEquiv)
    ((Equiv.prodCongr (blockEdgeEquiv k q) (Equiv.refl _)).trans finProdFinEquiv)).trans
      finSumFinEquiv).trans (finCongr (by ring))

/-- The old vertices come first. -/
theorem explicitVertexEquiv_inl (k q m : ℕ) (v : Fin q ⊕ BlockEdge k q) :
    (explicitVertexEquiv k q m (.inl v) : ℕ) < q * (3 * k + 2) := by
  simp only [explicitVertexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Fin.val_castAdd]
  exact Fin.isLt _

/-- The subdivision vertices come after the old ones. -/
theorem le_explicitVertexEquiv_inr (k q m : ℕ) (p : BlockEdge k q × Fin m) :
    q * (3 * k + 2) ≤ (explicitVertexEquiv k q m (.inr p) : ℕ) := by
  simp only [explicitVertexEquiv, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right, Fin.val_natAdd]
  omega

/-! ### The explicit network -/

variable (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ) [NeZero b]
  (σ : Schedule k q) (e : State ≃ Fin s)

/-- **The explicit block-counting network** of the schedule `σ`: the block-counting network
binarized by the letter code (`Turing.MultiTapePTM.letterCode`), subdivided by equality tensors
and written out with the old vertices first. Its first `q * (3 * k + 2)` vertices are the rows of
its bipartition. -/
@[expose] noncomputable def explicitBlockNetwork : ExplicitTensorNetwork ℕ :=
  ((machine.blockNetwork input b σ).binarize (letterCode e)).subdivide.toExplicit
    (explicitVertexEquiv k q (letterBits k s b)) (explicitEdgeEquiv k q (letterBits k s b))

/-- **Writing the network out preserves its contraction.** -/
theorem contraction_explicitBlockNetwork [Fintype State] :
    (machine.explicitBlockNetwork input b σ e).contraction =
      (machine.blockNetwork input b σ).contraction := by
  rw [explicitBlockNetwork, TensorNetwork.contraction_toExplicit,
    TensorNetwork.contraction_subdivide,
    TensorNetwork.contraction_binarize _ (letterCode_injective e)]

/-- **The block-counting identity for the explicit networks** (the note's Lemma 2.2, equation
(2)). Summed over the movement schedules of `q > 0` intervals of `b` bits, the contractions of the
explicit block-counting networks are the accepting count on `q * b` bits. -/
theorem sum_contraction_explicitBlockNetwork [Finite State] (hq : 0 < q) :
    ∑ σ : Schedule k q, (machine.explicitBlockNetwork input b σ e).contraction =
      machine.acceptCount input (q * b) := by
  have := Fintype.ofFinite State
  simp only [contraction_explicitBlockNetwork]
  exact machine.sum_contraction_blockNetwork input b hq

/-- The explicit network has `2 * (q * (3 * k + 1) * letterBits k s b)` edges: two halves of each
of the `letterBits k s b` copies of each of the `q * (3 * k + 1)` edges. -/
theorem numEdges_explicitBlockNetwork :
    (machine.explicitBlockNetwork input b σ e).numEdges =
      2 * (q * (3 * k + 1) * letterBits k s b) := rfl

/-- The explicit network has `q * (3 * k + 2)` old vertices and one subdivision vertex for each
copy of an edge. -/
theorem length_vertices_explicitBlockNetwork :
    (machine.explicitBlockNetwork input b σ e).vertices.length =
      q * (3 * k + 2) + q * (3 * k + 1) * letterBits k s b := by
  simp [explicitBlockNetwork, TensorNetwork.toExplicit]

/-- **The degree bound**: at most `2 * (3 * k + 1) * letterBits k s b` ports at every vertex,
`O(b)` for a fixed machine. -/
theorem maxDegree_explicitBlockNetwork_le :
    (machine.explicitBlockNetwork input b σ e).maxDegree ≤
      2 * (3 * k + 1) * letterBits k s b := by
  have hm : 1 ≤ letterBits k s b :=
    Nat.mul_pos (by omega) (Nat.pos_of_neZero b)
  refine TensorNetwork.maxDegree_toExplicit_le _ _ _
    (TensorNetwork.maxDegreeLE_subdivide _ ?_ ?_ ?_)
  · exact TensorNetwork.loopless_binarize _ _ (machine.loopless_blockNetwork input b σ)
  · exact TensorNetwork.maxDegreeLE_binarize _ _ (machine.maxDegreeLE_blockNetwork input b σ)
  · nlinarith

/-- **The bipartition**: the first `q * (3 * k + 2)` vertices, the old ones, are rows; every edge
joins an old vertex to a subdivision vertex. -/
theorem isRowsFirstBipartite_explicitBlockNetwork :
    (machine.explicitBlockNetwork input b σ e).IsRowsFirstBipartite (q * (3 * k + 2)) := by
  refine TensorNetwork.isRowsFirstBipartite_toExplicit _ _ _ _ fun p => ?_
  rcases p with p | p <;>
  simp only [TensorNetwork.subdivide_src_inl, TensorNetwork.subdivide_src_inr,
    TensorNetwork.subdivide_tgt_inl, TensorNetwork.subdivide_tgt_inr] <;>
  exact iff_of_true (explicitVertexEquiv_inl _ _ _ _)
    (not_lt.mpr (le_explicitVertexEquiv_inr _ _ _ _))

/-- **Admissibility at a clock `t`.** With blocks of `b ≤ 3 ⌊log₂ t⌋` steps and padded time
`q * b ≤ 2 t`, the explicit network is rows-first bipartite with `O(t)` edges and maximum degree
`O(log t)`, with the constant `6 (3 k + 1) (s + k + 4)` of the machine. For the counting
simulation, `b = ⌈log₂ (t + 2)⌉` (`Nat.clog_two_add_two_le_three_mul_log_two`). -/
theorem admissible_explicitBlockNetwork {t : ℕ} (hb : b ≤ 3 * Nat.log 2 t) (hqb : q * b ≤ 2 * t) :
    (machine.explicitBlockNetwork input b σ e).IsRowsFirstBipartite (q * (3 * k + 2)) ∧
      (machine.explicitBlockNetwork input b σ e).numEdges ≤ 6 * (3 * k + 1) * (s + k + 4) * t ∧
      (machine.explicitBlockNetwork input b σ e).maxDegree ≤
        6 * (3 * k + 1) * (s + k + 4) * Nat.log 2 t := by
  refine ⟨machine.isRowsFirstBipartite_explicitBlockNetwork input b σ e, ?_, ?_⟩
  · rw [numEdges_explicitBlockNetwork, letterBits]
    calc 2 * (q * (3 * k + 1) * ((s + k + 4) * b))
        = 2 * (3 * k + 1) * (s + k + 4) * (q * b) := by ring
      _ ≤ 2 * (3 * k + 1) * (s + k + 4) * (2 * t) := Nat.mul_le_mul_left _ hqb
      _ ≤ 6 * (3 * k + 1) * (s + k + 4) * t := by
          have h4 : 2 * (3 * k + 1) * (s + k + 4) * (2 * t) =
              4 * ((3 * k + 1) * (s + k + 4) * t) := by ring
          have h6 : 6 * (3 * k + 1) * (s + k + 4) * t = 6 * ((3 * k + 1) * (s + k + 4) * t) := by
            ring
          omega
  · refine (machine.maxDegree_explicitBlockNetwork_le input b σ e).trans ?_
    rw [letterBits]
    calc 2 * (3 * k + 1) * ((s + k + 4) * b) = 2 * (3 * k + 1) * (s + k + 4) * b := by ring
      _ ≤ 2 * (3 * k + 1) * (s + k + 4) * (3 * Nat.log 2 t) := Nat.mul_le_mul_left _ hb
      _ = 6 * (3 * k + 1) * (s + k + 4) * Nat.log 2 t := by ring

/-- Every table of the explicit network lists the values at all bits on its ports. -/
theorem length_table_explicitBlockNetwork {p : List ℕ × List ℕ}
    (hp : p ∈ (machine.explicitBlockNetwork input b σ e).vertices) :
    p.2.length = 2 ^ p.1.length :=
  TensorNetwork.length_table_toExplicit _ _ _ hp

/-- **The entry bound**: every table entry of the explicit network is at most `2 ^ b`. -/
theorem entry_le_explicitBlockNetwork {p : List ℕ × List ℕ}
    (hp : p ∈ (machine.explicitBlockNetwork input b σ e).vertices) {a : ℕ} (ha : a ∈ p.2) :
    a ≤ 2 ^ b := by
  obtain ⟨v, y, rfl⟩ := TensorNetwork.exists_tensor_of_mem_toExplicit _ _ _ hp ha
  have hone : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
  rcases v with v | p
  · rw [TensorNetwork.subdivide_tensor_inl]
    rcases TensorNetwork.tensor_binarize_eq_zero_or (machine.blockNetwork input b σ)
      (letterCode e) v _ with h | ⟨x, h⟩
    · rw [h]
      exact Nat.zero_le _
    · rw [h]
      exact machine.tensor_blockNetwork_le input b σ v x
  · rw [TensorNetwork.subdivide_tensor_inr]
    split_ifs
    · exact hone
    · exact Nat.zero_le _

end MultiTapePTM

end Turing
