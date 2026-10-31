/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork
import Mathlib.Algebra.BigOperators.Fin

/-!
# The graph of an explicit block-counting network, on numbers

The explicit block-counting network of a schedule
(`Turing.MultiTapePTM.explicitBlockNetwork`) is defined through structured types: schedules,
edges `Turing.MultiTapePTM.BlockEdge`, and the next appearance of a block in windows
(`Turing.MultiTapePTM.firstAfter`). This module computes its graph, the ports of every vertex,
by arithmetic on natural numbers, the form in which a polynomial-time construction produces it.

* **Schedules** are numbered by their `(k + 1) q` entries as digits in base `3`
  (`Turing.MultiTapePTM.scheduleEquiv`), the entries of one interval consecutive with the input
  head first, and the sign of digit `δ` being `δ - 1`. Any natural number `σ` names the schedule
  of its digits `σ / 3 ^ j % 3` (`Turing.MultiTapePTM.scheduleOfNat`), which is the numbered one
  for `σ < 3 ^ ((k + 1) q)` (`Turing.MultiTapePTM.scheduleOfNat_eq_symm`). So summing over the
  numbers below `3 ^ ((k + 1) q)` is summing over the schedules
  (`Turing.MultiTapePTM.sum_range_scheduleOfNat`).
* **Block indices** are counts of digits: a head is in block `#{2} - #{0}` at the start of
  interval `i`, counting the digits `2` and `0` of that head in the intervals before `i`
  (`Turing.MultiTapePTM.scheduleBlock_scheduleOfNat`). Whether a block lies in a window is then a
  comparison of natural numbers (`Turing.MultiTapePTM.inWindowNum_iff`), and the next appearance
  of a block is a search over the intervals (`Turing.MultiTapePTM.firstAfterNum_eq`).
* **Endpoints.** The numbered explicit edges have sources and targets given by
  `Turing.MultiTapePTM.explicitSrcNum` and `Turing.MultiTapePTM.explicitTgtNum`, and the ports of
  a vertex are the edge numbers with that vertex as an endpoint
  (`Turing.MultiTapePTM.explicitPortsNum`). They are the ports of the explicit network
  (`Turing.MultiTapePTM.map_val_explicitPorts`,
  `Turing.MultiTapePTM.map_fst_vertices_explicitBlockNetwork`).

## Main definitions

* `Turing.MultiTapePTM.signEquiv`, `Turing.MultiTapePTM.scheduleEquiv`,
  `Turing.MultiTapePTM.scheduleOfNat`: numbering the schedules.
* `Turing.MultiTapePTM.digitCount`, `Turing.MultiTapePTM.inWindowNum`,
  `Turing.MultiTapePTM.firstAfterNum`, `Turing.MultiTapePTM.edgeTargetNum`: block indices,
  windows, next appearances and edge targets on numbers.
* `Turing.MultiTapePTM.explicitSrcNum`, `Turing.MultiTapePTM.explicitTgtNum`,
  `Turing.MultiTapePTM.explicitPortsNum`: the endpoints of the explicit edges and the ports of the
  vertices.

## Main results

* `Turing.MultiTapePTM.sum_range_scheduleOfNat`: summing over schedule numbers.
* `Turing.MultiTapePTM.edgeTargetNum_blockEdgeEquiv`: the edge targets on numbers.
* `Turing.MultiTapePTM.explicitSrcNum_explicitEdgeEquiv`,
  `Turing.MultiTapePTM.explicitTgtNum_explicitEdgeEquiv`: the endpoints on numbers.
* `Turing.MultiTapePTM.map_val_explicitPorts`,
  `Turing.MultiTapePTM.map_fst_vertices_explicitBlockNetwork`: the ports of the explicit network
  on numbers.
-/

public section

namespace Turing.MultiTapePTM

open Cslib.Circuits.Frontier

variable {k q : ℕ}

/-! ### Numbering the schedules -/

/-- The signs numbered `-1 ↦ 0`, `0 ↦ 1`, `1 ↦ 2`. -/
@[expose] def signEquiv : SignType ≃ Fin 3 where
  toFun
    | .neg => 0
    | .zero => 1
    | .pos => 2
  invFun i := if i = 0 then .neg else if i = 1 then .zero else .pos
  left_inv s := by cases s <;> rfl
  right_inv i := by fin_cases i <;> rfl

/-- The sign numbered `δ` is `δ - 1`: one for the digit `2`, minus one for the digit `0`. -/
theorem coe_signEquiv_symm (δ : Fin 3) :
    ((signEquiv.symm δ : SignType) : ℤ) =
      (if (δ : ℕ) = 2 then 1 else 0) - (if (δ : ℕ) = 0 then 1 else 0) := by
  fin_cases δ <;> rfl

/-- The digit position of the entry of interval `i` and head `head` in a schedule number:
`head + (k + 1) i`, numbering the input head `0` and work head `h` as `h + 1`. -/
@[expose] def scheduleIndexEquiv (k q : ℕ) : Fin q × Option (Fin k) ≃ Fin ((k + 1) * q) :=
  ((Equiv.prodCongr (Equiv.refl _) (finSuccEquiv k).symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm q (k + 1)))

theorem val_scheduleIndexEquiv (i : Fin q) (head : Option (Fin k)) :
    (scheduleIndexEquiv k q (i, head) : ℕ) = ((finSuccEquiv k).symm head : ℕ) + (k + 1) * i := by
  simp [scheduleIndexEquiv, finProdFinEquiv_apply_val]

/-- **The schedules numbered** by their `(k + 1) q` entries as digits in base `3`: the entry of
interval `i` and head `head` is the digit at position `head + (k + 1) i`
(`Turing.MultiTapePTM.scheduleIndexEquiv`), numbered by `Turing.MultiTapePTM.signEquiv`. -/
@[expose] def scheduleEquiv (k q : ℕ) : Schedule k q ≃ Fin (3 ^ ((k + 1) * q)) :=
  (Equiv.curry _ _ _).symm.trans
    ((Equiv.arrowCongr (scheduleIndexEquiv k q) signEquiv).trans finFunctionFinEquiv)

/-- **The schedule of a number**: its entry for interval `i` and head `head` is named by the digit
of `σ` in base `3` at position `head + (k + 1) i`. Every natural number names a schedule; below
`3 ^ ((k + 1) q)` this is the numbering `Turing.MultiTapePTM.scheduleEquiv`. -/
@[expose] def scheduleOfNat (k q σ : ℕ) : Schedule k q := fun i head =>
  signEquiv.symm ⟨σ / 3 ^ (((finSuccEquiv k).symm head : ℕ) + (k + 1) * i) % 3,
    Nat.mod_lt _ (by norm_num)⟩

/-- Below `3 ^ ((k + 1) q)`, the schedule of a number is the numbered one. -/
theorem scheduleOfNat_eq_symm {σ : ℕ} (hσ : σ < 3 ^ ((k + 1) * q)) :
    scheduleOfNat k q σ = (scheduleEquiv k q).symm ⟨σ, hσ⟩ := by
  funext i head
  rw [scheduleOfNat]
  change _ = signEquiv.symm (finFunctionFinEquiv.symm ⟨σ, hσ⟩ (scheduleIndexEquiv k q (i, head)))
  congr 1

/-- **Summing over schedule numbers** is summing over the schedules. -/
theorem sum_range_scheduleOfNat {M : Type*} [AddCommMonoid M] (f : Schedule k q → M) :
    ∑ σ ∈ Finset.range (3 ^ ((k + 1) * q)), f (scheduleOfNat k q σ) = ∑ σ : Schedule k q, f σ := by
  rw [Finset.sum_range]
  simp only [scheduleOfNat_eq_symm (Fin.isLt _), Fin.eta]
  exact Fintype.sum_equiv (scheduleEquiv k q).symm _ _ fun _ => rfl

/-! ### Block indices, windows and next appearances on numbers -/

/-- The number of intervals `i' < i` in which the digit of `σ` at position `c + (k + 1) i'` is
`δ`. For `c` the number of a head, these are the intervals of `scheduleOfNat k q σ` moving that
head by `δ - 1` blocks. -/
@[expose] def digitCount (k σ c δ i : ℕ) : ℕ :=
  (List.range i).countP fun i' => σ / 3 ^ (c + (k + 1) * i') % 3 = δ

/-- **Block indices are digit counts**: at the start of interval `i ≤ q`, a head is in block
`#{2} - #{0}`, counting its digits `2` and `0` in the earlier intervals. -/
theorem scheduleBlock_scheduleOfNat (σ : ℕ) {i : ℕ} (hi : i ≤ q) (head : Option (Fin k)) :
    scheduleBlock (scheduleOfNat k q σ) i head =
      (digitCount k σ ((finSuccEquiv k).symm head) 2 i : ℤ) -
        digitCount k σ ((finSuccEquiv k).symm head) 0 i := by
  induction i with
  | zero => simp [digitCount]
  | succ i ih =>
    rw [scheduleBlock_succ _ (by omega), ih (by omega), scheduleOfNat, coe_signEquiv_symm]
    simp only [digitCount, List.range_succ, List.countP_append, List.countP_singleton]
    split_ifs <;> simp_all <;> omega

/-- Whether the block `j = b(i) + δ - 1` of interval `i`'s window lies in the window of interval
`i'`, from the digit counts `P` (digits `2`) and `N` (digits `0`) of the head at `i` and `i'`:
`|b(i') - j| ≤ 1` for `b = P - N`, compared in natural numbers. -/
@[expose] def inWindowNum (k σ c i δ i' : ℕ) : Bool :=
  decide (digitCount k σ c 2 i' + digitCount k σ c 0 i + 1 ≤
      digitCount k σ c 0 i' + digitCount k σ c 2 i + δ + 1 ∧
    digitCount k σ c 0 i' + digitCount k σ c 2 i + δ ≤
      digitCount k σ c 2 i' + digitCount k σ c 0 i + 2)

/-- **Windows on numbers.** -/
theorem inWindowNum_iff (σ : ℕ) (i i' : Fin q) (h : Fin k) (δ : Fin 3) :
    inWindowNum k σ (h + 1) i δ i' = true ↔
      InWindow (scheduleOfNat k q σ) h (portBlock (scheduleOfNat k q σ) i h δ) i' := by
  have hc : (((finSuccEquiv k).symm (some h) : Fin (k + 1)) : ℕ) = h + 1 := by simp
  have hb := scheduleBlock_scheduleOfNat (k := k) σ i.isLt.le (some h)
  have hb' := scheduleBlock_scheduleOfNat (k := k) σ i'.isLt.le (some h)
  rw [hc] at hb hb'
  simp only [InWindow, portBlock, hb, hb', abs_le, inWindowNum, decide_eq_true_eq]
  omega

/-- The next interval after `i` whose window contains the block `δ` of interval `i`'s window, for
the head with digit offset `c`, found by searching the intervals in order. -/
@[expose] def firstAfterNum (k q σ c i δ : ℕ) : Option ℕ :=
  (List.range q).find? fun i' => decide (i < i') && inWindowNum k σ c i δ i'

/-- **Next appearances on numbers.** -/
theorem firstAfterNum_eq (σ : ℕ) (i : Fin q) (h : Fin k) (δ : Fin 3) :
    firstAfterNum k q σ (h + 1) i δ =
      (firstAfter (InWindow (scheduleOfNat k q σ) h
        (portBlock (scheduleOfNat k q σ) i h δ)) i).map Fin.val := by
  cases hf : firstAfter (InWindow (scheduleOfNat k q σ) h
      (portBlock (scheduleOfNat k q σ) i h δ)) i with
  | none =>
    rw [firstAfter_eq_none_iff] at hf
    simp only [Option.map_none, firstAfterNum, List.find?_eq_none, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, not_and]
    intro j hj hij hw
    exact hf ⟨j, hj⟩ hij ((inWindowNum_iff σ i ⟨j, hj⟩ h δ).mp hw)
  | some i' =>
    obtain ⟨hlt, hw, hmin⟩ := firstAfter_eq_some_iff.mp hf
    simp only [Option.map_some, firstAfterNum, List.find?_range_eq_some, List.mem_range,
      Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨⟨hlt, (inWindowNum_iff σ i i' h δ).mpr hw⟩, i'.isLt, fun j hj => ?_⟩
    by_cases hij : i.val < j
    · refine Or.inr ?_
      rw [Bool.eq_false_iff, ne_eq, inWindowNum_iff σ i ⟨j, by omega⟩ h δ]
      exact hmin ⟨j, by omega⟩ hij hj
    · exact Or.inl hij

/-! ### Edge targets and endpoints on numbers -/

/-- The number of the block edge `(i, h, δ)`: after the `q` control edges, in lexicographic
order. -/
theorem val_blockEdgeEquiv_inr (i : Fin q) (h : Fin k) (δ : Fin 3) :
    (blockEdgeEquiv k q (.inr (i, h, δ)) : ℕ) = q + (δ + 3 * h + k * 3 * i) := by
  simp [blockEdgeEquiv, finProdFinEquiv_apply_val, Nat.add_assoc]

/-- The number of the control edge leaving interval `i`. -/
theorem val_blockEdgeEquiv_inl (i : Fin q) : (blockEdgeEquiv k q (.inl i) : ℕ) = i := by
  simp [blockEdgeEquiv]

/-- The number of an interval as a vertex of the explicit network. -/
theorem val_explicitVertexEquiv_interval (m : ℕ) (i : Fin q) :
    (explicitVertexEquiv k q m (.inl (.inl i)) : ℕ) = i := by
  simp [explicitVertexEquiv]

/-- The number of the sink of an edge as a vertex of the explicit network. -/
theorem val_explicitVertexEquiv_sink (m : ℕ) (e : BlockEdge k q) :
    (explicitVertexEquiv k q m (.inl (.inr e)) : ℕ) = q + blockEdgeEquiv k q e := by
  simp [explicitVertexEquiv, Nat.add_comm]

/-- The number of the subdivision vertex of copy `j` of an edge. -/
theorem val_explicitVertexEquiv_inr (m : ℕ) (e : BlockEdge k q) (j : Fin m) :
    (explicitVertexEquiv k q m (.inr (e, j)) : ℕ) =
      q * (3 * k + 2) + (j + m * blockEdgeEquiv k q e) := by
  simp [explicitVertexEquiv, finProdFinEquiv_apply_val]

/-- The number of the source half of copy `j` of an edge. -/
theorem val_explicitEdgeEquiv_inl (m : ℕ) (e : BlockEdge k q) (j : Fin m) :
    (explicitEdgeEquiv k q m (.inl (e, j)) : ℕ) = j + m * blockEdgeEquiv k q e := by
  simp [explicitEdgeEquiv, finProdFinEquiv_apply_val]

/-- The number of the target half of copy `j` of an edge. -/
theorem val_explicitEdgeEquiv_inr (m : ℕ) (e : BlockEdge k q) (j : Fin m) :
    (explicitEdgeEquiv k q m (.inr (e, j)) : ℕ) =
      q * (3 * k + 1) * m + (j + m * blockEdgeEquiv k q e) := by
  simp [explicitEdgeEquiv, finProdFinEquiv_apply_val, Nat.add_comm]

/-- The number of the vertex at which the block edge numbered `n` ends (`edgeTarget`): the next
interval for a control edge (`n < q`), and for a block edge the next interval whose window
contains its block; the sink `q + n` of the edge when there is none. -/
@[expose] def edgeTargetNum (k q σ n : ℕ) : ℕ :=
  if n < q then (if n + 1 < q then n + 1 else q + n)
  else (firstAfterNum k q σ ((n - q) % (k * 3) / 3 + 1) ((n - q) / (k * 3)) ((n - q) % 3)).getD
    (q + n)

/-- **Edge targets on numbers.** -/
theorem edgeTargetNum_blockEdgeEquiv (σ m : ℕ) (e : BlockEdge k q) :
    edgeTargetNum k q σ (blockEdgeEquiv k q e) =
      explicitVertexEquiv k q m (.inl (edgeTarget (scheduleOfNat k q σ) e)) := by
  rcases e with i | ⟨i, h, δ⟩
  · rw [val_blockEdgeEquiv_inl, edgeTargetNum, ite_eq_left i.isLt]
    simp only [edgeTarget]
    split_ifs with hi
    · rw [val_explicitVertexEquiv_interval]
    · rw [val_explicitVertexEquiv_sink, val_blockEdgeEquiv_inl]
  · have hk : 0 < k := Fin.pos h
    have hδ := δ.isLt
    have hh := h.isLt
    have hlt : (δ : ℕ) + 3 * (h : ℕ) < k * 3 := by omega
    have hdiv : ((δ : ℕ) + 3 * (h : ℕ) + k * 3 * (i : ℕ)) / (k * 3) = i := by
      rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
    have hmod : ((δ : ℕ) + 3 * (h : ℕ) + k * 3 * (i : ℕ)) % (k * 3) = (δ : ℕ) + 3 * (h : ℕ) := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    have hmod3 : ((δ : ℕ) + 3 * (h : ℕ) + k * 3 * (i : ℕ)) % 3 = δ := by
      rw [show (δ : ℕ) + 3 * (h : ℕ) + k * 3 * (i : ℕ) = δ + 3 * (h + k * i) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hδ]
    have hdiv3 : ((δ : ℕ) + 3 * (h : ℕ)) / 3 = h := by omega
    rw [val_blockEdgeEquiv_inr, edgeTargetNum, ite_eq_right (by omega), Nat.add_sub_cancel_left,
      hdiv, hmod, hmod3, hdiv3, firstAfterNum_eq σ i h δ]
    simp only [edgeTarget]
    cases firstAfter (InWindow (scheduleOfNat k q σ) h
        (portBlock (scheduleOfNat k q σ) i h δ)) i with
    | none =>
      simp only [Option.map_none, Option.getD_none, Option.elim_none]
      rw [val_explicitVertexEquiv_sink, val_blockEdgeEquiv_inr]
    | some i' =>
      simp only [Option.map_some, Option.getD_some, Option.elim_some]
      rw [val_explicitVertexEquiv_interval]

/-- The number of the interval that the block edge numbered `n` leaves. -/
@[expose] def blockSrcNum (k q n : ℕ) : ℕ := if n < q then n else (n - q) / (k * 3)

/-- The interval an edge leaves, on numbers. -/
theorem blockSrcNum_blockEdgeEquiv (m : ℕ) (e : BlockEdge k q) :
    blockSrcNum k q (blockEdgeEquiv k q e) =
      explicitVertexEquiv k q m (.inl (.inl (e.elim id Prod.fst))) := by
  rw [val_explicitVertexEquiv_interval]
  rcases e with i | ⟨i, h, δ⟩
  · rw [val_blockEdgeEquiv_inl, blockSrcNum, ite_eq_left i.isLt]
    rfl
  · have hδ := δ.isLt
    have hh := h.isLt
    have hlt : (δ : ℕ) + 3 * (h : ℕ) < k * 3 := by omega
    rw [val_blockEdgeEquiv_inr, blockSrcNum, ite_eq_right (by omega), Nat.add_sub_cancel_left,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hlt, zero_add]
    rfl

/-- The number of the vertex at which the explicit edge numbered `j` starts: the interval of its
edge for a source half (`j < q (3 k + 1) m`), and the target of its edge for a target half. -/
@[expose] def explicitSrcNum (k q m σ j : ℕ) : ℕ :=
  if j < q * (3 * k + 1) * m then blockSrcNum k q (j / m)
  else edgeTargetNum k q σ ((j - q * (3 * k + 1) * m) / m)

/-- The number of the vertex at which the explicit edge numbered `j` ends: the subdivision vertex
of its copy. -/
@[expose] def explicitTgtNum (k q m j : ℕ) : ℕ :=
  q * (3 * k + 2) + if j < q * (3 * k + 1) * m then j else j - q * (3 * k + 1) * m

section Endpoints

variable {State : Type} (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ)
  [NeZero b] {m : ℕ} (code : BlockLetter k State b → Fin m → Bool)

private theorem lt_card_mul (e : BlockEdge k q) (j : Fin m) :
    (j : ℕ) + m * blockEdgeEquiv k q e < q * (3 * k + 1) * m := by
  have := (blockEdgeEquiv k q e).isLt
  have := j.isLt
  nlinarith

private theorem add_mul_div (e : BlockEdge k q) (j : Fin m) :
    ((j : ℕ) + m * blockEdgeEquiv k q e) / m = blockEdgeEquiv k q e := by
  have := j.isLt
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt j.isLt, zero_add]

omit [NeZero b] in
/-- **The sources of the explicit edges on numbers.** -/
theorem explicitSrcNum_explicitEdgeEquiv (σ : ℕ) (p : (BlockEdge k q × Fin m) ⊕
    (BlockEdge k q × Fin m)) :
    explicitSrcNum k q m σ (explicitEdgeEquiv k q m p) =
      explicitVertexEquiv k q m
        (((machine.blockNetwork input b (scheduleOfNat k q σ)).binarize code).subdivide.src p) := by
  rcases p with ⟨e, j⟩ | ⟨e, j⟩
  · rw [val_explicitEdgeEquiv_inl, explicitSrcNum, ite_eq_left (lt_card_mul e j), add_mul_div,
      blockSrcNum_blockEdgeEquiv m e]
    simp only [TensorNetwork.subdivide_src_inl, TensorNetwork.binarize_src, blockNetwork_src]
  · rw [val_explicitEdgeEquiv_inr, explicitSrcNum, ite_eq_right (by omega), Nat.add_sub_cancel_left,
      add_mul_div, edgeTargetNum_blockEdgeEquiv σ m e]
    simp only [TensorNetwork.subdivide_src_inr, TensorNetwork.binarize_tgt, blockNetwork_tgt]

omit [NeZero b] in
/-- **The targets of the explicit edges on numbers.** -/
theorem explicitTgtNum_explicitEdgeEquiv (σ : ℕ) (p : (BlockEdge k q × Fin m) ⊕
    (BlockEdge k q × Fin m)) :
    explicitTgtNum k q m (explicitEdgeEquiv k q m p) =
      explicitVertexEquiv k q m
        (((machine.blockNetwork input b (scheduleOfNat k q σ)).binarize code).subdivide.tgt p) := by
  rcases p with ⟨e, j⟩ | ⟨e, j⟩
  · rw [val_explicitEdgeEquiv_inl, explicitTgtNum, ite_eq_left (lt_card_mul e j)]
    exact (val_explicitVertexEquiv_inr m e j).symm
  · rw [val_explicitEdgeEquiv_inr, explicitTgtNum, ite_eq_right (by omega), Nat.add_sub_cancel_left]
    exact (val_explicitVertexEquiv_inr m e j).symm

end Endpoints

/-! ### Ports on numbers -/

/-- The ports of the vertex numbered `v`: the numbers of the explicit edges starting or ending at
it, in increasing order. -/
@[expose] def explicitPortsNum (k q m σ v : ℕ) : List ℕ :=
  (List.range (2 * (q * (3 * k + 1) * m))).filter fun j =>
    decide (explicitSrcNum k q m σ j = v ∨ explicitTgtNum k q m j = v)

variable {State : Type} (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ)
  [NeZero b]

omit [NeZero b] in
/-- **The ports of a vertex on numbers**: for any letter code, the ports of the vertex `w` of the
binarized and subdivided network, numbered by `explicitEdgeEquiv`, are
`explicitPortsNum` at the number of `w`. -/
theorem map_val_explicitPorts {m : ℕ} (code : BlockLetter k State b → Fin m → Bool) (σ : ℕ)
    (w : (Fin q ⊕ BlockEdge k q) ⊕ BlockEdge k q × Fin m) :
    ((((machine.blockNetwork input b (scheduleOfNat k q σ)).binarize code).subdivide.explicitPorts
        (explicitEdgeEquiv k q m) w).map Fin.val) =
      explicitPortsNum k q m σ (explicitVertexEquiv k q m w) := by
  rw [explicitPortsNum, ← List.map_coe_finRange_eq_range, List.filter_map,
    TensorNetwork.explicitPorts]
  congr 1
  refine List.filter_congr fun j _ => ?_
  have hj := (explicitEdgeEquiv k q m).apply_symm_apply j
  simp only [Function.comp_apply, decide_eq_decide]
  conv_rhs => rw [← hj, explicitSrcNum_explicitEdgeEquiv machine input b code σ,
    explicitTgtNum_explicitEdgeEquiv machine input b code σ]
  simp only [Fin.val_inj, Equiv.apply_eq_iff_eq]

variable {s : ℕ} (e : State ≃ Fin s)

/-- **The ports of the explicit network on numbers**: vertex `v` of the explicit network of the
schedule of `σ` has the ports `explicitPortsNum k q (letterBits k s b) σ v`. -/
theorem map_fst_vertices_explicitBlockNetwork (σ : ℕ) :
    (machine.explicitBlockNetwork input b (scheduleOfNat k q σ) e).vertices.map Prod.fst =
      (List.range (q * (3 * k + 2) + q * (3 * k + 1) * letterBits k s b)).map
        (explicitPortsNum k q (letterBits k s b) σ) := by
  rw [explicitBlockNetwork, TensorNetwork.toExplicit, List.map_ofFn,
    ← List.map_coe_finRange_eq_range, List.map_map, List.ofFn_eq_map]
  refine List.map_congr_left fun v _ => ?_
  simp only [Function.comp_apply]
  rw [map_val_explicitPorts, Equiv.apply_symm_apply]

end Turing.MultiTapePTM
