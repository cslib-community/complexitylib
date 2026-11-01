/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.CarryLookahead
public import Complexity.Computability.Circuit.Boolean.ThresholdNC1
import Complexity.Foundations.Data.Nat.Log
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Linear-size population counting and thresholds

The word width at a node of a balanced addition tree is the height of that node plus one.
Consequently, the existing quadratic-size adder suffices for a linear-size population counter:
there are exponentially fewer nodes at increasing heights. All gates, including constants,
are charged. The input is padded with zeros to a power of two, so the construction also handles
an empty input.

## Main definitions

* `Cslib.Circuits.Boolean.PopulationCount.tree`: the counter on a power-of-two input block.
* `Cslib.Circuits.Boolean.populationCountCircuit`: the counter on an arbitrary input block.
* `Cslib.Circuits.Boolean.linearThresholdCircuit`: a threshold circuit of linear size.

## Main results

* `Cslib.Circuits.Boolean.val_eval_populationCountCircuit`: exact binary population count.
* `Cslib.Circuits.Boolean.size_populationCountCircuit_le`: a linear gate bound.
* `Cslib.Circuits.Boolean.eval_linearThresholdCircuit`: exact threshold semantics.
* `Cslib.Circuits.Boolean.size_linearThresholdCircuit_le`: a linear gate bound.

## References

Binary addition and threshold circuits are standard; see [Vollmer, Chapter 1][Vollmer1999].
The concrete adders and their source attribution are in `Boolean.CarryLookahead`.
-/

public section

namespace Cslib.Circuits.Boolean

open BitString

namespace PopulationCount

/-- Select a bit from the first half of the next tree level. -/
@[expose] def leftWire (h : ℕ) (i : Fin (2 ^ h)) : Fin (2 ^ (h + 1)) :=
  ⟨i.val, by have := i.isLt; rw [pow_succ, Nat.mul_two]; omega⟩

/-- Select a bit from the second half of the next tree level. -/
@[expose] def rightWire (h : ℕ) (i : Fin (2 ^ h)) : Fin (2 ^ (h + 1)) :=
  ⟨2 ^ h + i.val, by have := i.isLt; rw [pow_succ, Nat.mul_two]; omega⟩

/-- Add the counts of the two half blocks, retaining the final carry. A height-`h` tree has
`2^h` inputs and `h+1` output bits. -/
@[expose] def tree : (h : ℕ) → Circuit signature (2 ^ h) (h + 1)
  | 0 => Circuit.id signature 1
  | h + 1 =>
    (carryLookahead (h + 1)).comp
      ((((tree h).comp (Circuit.wiring signature (leftWire h))).append
          ((tree h).comp (Circuit.wiring signature (rightWire h)))).append
        (Circuit.oneGate (.const false) Fin.elim0))

private theorem weight_halves (h : ℕ) (x : BitString (2 ^ (h + 1))) :
    weight (x ∘ leftWire h) + weight (x ∘ rightWire h) = weight x := by
  have he : 2 ^ h + 2 ^ h = 2 ^ (h + 1) := by rw [pow_succ, Nat.mul_two]
  rw [weight_eq_sum_toNat, weight_eq_sum_toNat, weight_eq_sum_toNat]
  calc
    _ = ∑ i : Fin (2 ^ h + 2 ^ h), (x (Fin.cast he i)).toNat := by
      rw [Fin.sum_univ_add]
      rfl
    _ = ∑ i : Fin (2 ^ (h + 1)), (x i).toNat :=
      Fintype.sum_equiv (finCongr he) _ _ (fun _ => rfl)

/-- The output word is the exact number of true inputs, including the full carry. -/
theorem val_eval_tree (h : ℕ) (x : BitString (2 ^ h)) :
    (BitString.equivFin (h + 1) ((tree h).eval interpretation x) : ℕ) = weight x := by
  induction h with
  | zero =>
    change (equivFin 1 x : ℕ) = weight x
    rw [val_equivFin_eq_sum, weight_eq_sum_toNat]
    simp
  | succ h ih =>
    simp only [tree, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_wiring]
    change (BitString.equivFin (h + 1 + 1)
      ((carryLookahead (h + 1)).eval interpretation
        (Fin.append
          (Fin.append ((tree h).eval interpretation (x ∘ leftWire h))
            ((tree h).eval interpretation (x ∘ rightWire h))) (fun _ => false))) : ℕ) = _
    rw [val_eval_carryLookahead, ih, ih, Bool.toNat_false, Nat.add_zero, weight_halves]

private theorem size_tree_succ (h : ℕ) :
    (tree (h + 1)).size = 2 * (tree h).size + (carryLookahead (h + 1)).size + 1 := by
  simp [tree, Nat.two_mul, Nat.add_comm, Nat.add_left_comm]

private theorem size_tree_with_slack (h : ℕ) :
    (tree h).size + 21 * (h ^ 2 + 6 * h + 11) ≤ 231 * 2 ^ h := by
  induction h with
  | zero => simp [tree]
  | succ h ih =>
    have hadd := size_carryLookahead_le (h + 1)
    rw [size_tree_succ, pow_succ 2 h]
    nlinarith

/-- The increasing word widths cost only a constant per leaf in total. -/
theorem size_tree_le (h : ℕ) : (tree h).size ≤ 231 * 2 ^ h := by
  have := size_tree_with_slack h
  omega

/-- One shared false gate extends a word with zeros. -/
@[expose] def pad (n m : ℕ) : Circuit signature n m :=
  (Circuit.wiring signature (fun i : Fin m =>
      if hi : i.val < n then Fin.castAdd 1 ⟨i.val, hi⟩ else Fin.natAdd n 0)).comp
    ((Circuit.id signature n).append (Circuit.oneGate (.const false) Fin.elim0))

/-- Padding agrees with the standard zero extension of a bit string. -/
@[simp] theorem eval_pad (n m : ℕ) (x : BitString n) :
    (pad n m).eval interpretation x = zeroExtend x := by
  funext i
  simp only [pad, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_append,
    Function.comp_apply, zeroExtend]
  split_ifs with hi
  · change Fin.append x (fun _ => false) (Fin.castAdd 1 ⟨i.val, hi⟩) = _
    exact Fin.append_left _ _ _
  · change Fin.append x (fun _ => false) (Fin.natAdd n 0) = false
    exact Fin.append_right _ _ _

/-- Zero padding charges exactly one gate. -/
@[simp] theorem size_pad (n m : ℕ) : (pad n m).size = 1 := by
  simp [pad]

private theorem weight_zeroExtend {n m : ℕ} (h : n ≤ m) (x : BitString n) :
    weight (zeroExtend (d' := m) x) = weight x := by
  rw [weight, weight]
  have hlt (i : Fin m) (hi : i ∈ Finset.univ.filter (fun j => zeroExtend x j = true)) :
      i.val < n := by
    have ht := (Finset.mem_filter.mp hi).2
    by_contra hn
    simp [zeroExtend, hn] at ht
  refine Finset.card_bij (fun i hi => (⟨i.val, hlt i hi⟩ : Fin n)) ?_ ?_ ?_
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa only [zeroExtend, dite_eq_left (hlt i hi)] using (Finset.mem_filter.mp hi).2⟩
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun a : Fin n => a.val) hij)
  · intro i hi
    refine ⟨⟨i.val, i.isLt.trans_le h⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [zeroExtend, i.isLt] using (Finset.mem_filter.mp hi).2⟩

end PopulationCount

/-- A population count on `n` inputs. Padding to the next power of two uses one shared false
gate, and the balanced tree returns `⌈log₂(n+1)⌉+1` bits. -/
@[expose] def populationCountCircuit (n : ℕ) :
    Circuit signature n (Nat.clog 2 (n + 1) + 1) :=
  (PopulationCount.tree (Nat.clog 2 (n + 1))).comp
    (PopulationCount.pad n (2 ^ Nat.clog 2 (n + 1)))

/-- The circuit computes the exact binary numeral of the input's Hamming weight. -/
theorem val_eval_populationCountCircuit (n : ℕ) (x : BitString n) :
    (BitString.equivFin (Nat.clog 2 (n + 1) + 1)
      ((populationCountCircuit n).eval interpretation x) : ℕ) = weight x := by
  rw [populationCountCircuit, Circuit.eval_comp, PopulationCount.val_eval_tree,
    PopulationCount.eval_pad]
  exact PopulationCount.weight_zeroExtend
    ((Nat.le_succ n).trans (Nat.le_pow_clog Nat.one_lt_two _)) x

/-- A uniform linear gate bound, with constants and padding included. -/
theorem size_populationCountCircuit_le (n : ℕ) :
    (populationCountCircuit n).size ≤ 463 * (n + 1) := by
  have hs := PopulationCount.size_tree_le (Nat.clog 2 (n + 1))
  have hp := Nat.pow_clog_le_mul Nat.one_lt_two (Nat.succ_ne_zero n)
  rw [populationCountCircuit, Circuit.size_comp, PopulationCount.size_pad]
  nlinarith

/-- Compare the population count with a cutoff. An impossible cutoff returns false. -/
@[expose] def linearThresholdCircuit (n q : ℕ) : Circuit signature n 1 :=
  if hq : q ≤ n then
    let w := Nat.clog 2 (n + 1) + 1
    have hb : q < 2 ^ w :=
      (Nat.lt_succ_of_le hq).trans_le ((Nat.le_pow_clog Nat.one_lt_two (n + 1)).trans
        (Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (Nat.le_succ _)))
    (leCircuit w).comp
      ((wordConstCircuit n ((BitString.equivFin w).symm ⟨q, hb⟩)).append
        (populationCountCircuit n))
  else Circuit.oneGate (.const false) Fin.elim0

/-- The linear-size threshold circuit accepts precisely when at least `q` inputs are true. -/
@[simp] theorem eval_linearThresholdCircuit (n q : ℕ) (x : BitString n) :
    (linearThresholdCircuit n q).eval interpretation x = single (threshold n q) x := by
  funext o
  dsimp [linearThresholdCircuit]
  split_ifs with hq
  · rw [Circuit.eval_comp, Circuit.eval_append, eval_wordConstCircuit, eval_leCircuit]
    simp only [threshold, Equiv.apply_symm_apply, Fin.le_iff_val_le_val,
      val_eval_populationCountCircuit]
  · simp only [Circuit.eval_oneGate, interpretation, threshold_eq_false_of_lt (not_le.mp hq)]

/-- Linear population counting followed by comparison remains linear in the input count. -/
theorem size_linearThresholdCircuit_le (n q : ℕ) :
    (linearThresholdCircuit n q).size ≤ 476 * (n + 1) := by
  simp only [linearThresholdCircuit]
  split_ifs with hq
  · rw [Circuit.size_comp, Circuit.size_append, size_leCircuit, size_wordConstCircuit]
    have hs := size_populationCountCircuit_le n
    have hl : Nat.clog 2 (n + 1) ≤ n + 1 :=
      Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le)
    omega
  · simp only [Circuit.size_oneGate]
    omega

end Cslib.Circuits.Boolean
