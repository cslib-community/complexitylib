/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ThresholdNC1
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.Reduce
import CslibFrontier.Computability.Circuit.CompositionDepth
import CslibFrontier.Foundations.Data.BitString.Binary
import Mathlib.Data.Nat.Size

/-!
# Integer threshold gates in logarithmic depth

An integer threshold gate (`Cslib.Circuits.Boolean.IntThreshold.Op`) is true when `∑ uᵢ xᵢ > θ`.
Reading each input with a negative weight as its negation, the condition becomes `T ≤ ∑ |uᵢ| ℓᵢ`
for the literals `ℓᵢ` and a target `T`
(`Cslib.Circuits.Boolean.IntThreshold.Op.interpretation_iff`).
With `W` bits for the sum and the target, the masked words `|uᵢ| · ℓᵢ` and the offset `2 ^ W - T`
are summed by a balanced carry-save tree with a logarithmic-depth finishing adder
(`Cslib.Circuits.Boolean.sumPairs`), and bit `W` of the result decides the gate
(`Cslib.Circuits.Boolean.IntThreshold.Op.eval_deMorganCircuit`). The De Morgan circuit has
`O(k W²)` gates and depth `O(log k + log W)` for `k` inputs
(`Cslib.Circuits.Boolean.IntThreshold.Op.size_deMorganCircuit_le`,
`Cslib.Circuits.Boolean.IntThreshold.Op.depth_deMorganCircuit_le`).

## Main definitions

* `Cslib.Circuits.Boolean.IntThreshold.Op`, `Cslib.Circuits.Boolean.IntThreshold.signature`,
  `Cslib.Circuits.Boolean.IntThreshold.interpretation`: integer threshold gates.
* `Cslib.Circuits.Boolean.IntThreshold.Op.deMorganCircuit`: the De Morgan circuit of a gate.

## Main results

* `Cslib.Circuits.Boolean.IntThreshold.Op.eval_deMorganCircuit`: correctness.
* `Cslib.Circuits.Boolean.IntThreshold.Op.size_deMorganCircuit_le`,
  `Cslib.Circuits.Boolean.IntThreshold.Op.depth_deMorganCircuit_le`,
  `Cslib.Circuits.Boolean.IntThreshold.Op.width_le`: size, depth and width.

## References

* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
* [R. E. Ladner, M. J. Fischer, *Parallel prefix computation*][LadnerFischer1980]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

namespace IntThreshold

open BitString

/-- An integer threshold gate: `k` inputs, integer weights and an integer bias. -/
structure Op where
  /-- The number of inputs. -/
  arity : ℕ
  /-- The weight of each input. -/
  weight : Fin arity → ℤ
  /-- The bias. -/
  bias : ℤ

/-- The signature of integer threshold gates. -/
abbrev signature : Signature := ⟨Op, Op.arity⟩

/-- An integer threshold gate is true when the weighted sum of its inputs exceeds its bias. -/
def interpretation : Interpretation signature Bool :=
  fun op x => decide (op.bias < ∑ i, op.weight i * ((x i).toNat : ℤ))

namespace Op

variable (op : Op)

/-- The absolute value of a weight. -/
def absWeight (i : Fin op.arity) : ℕ := (op.weight i).natAbs

/-- The total absolute weight of the negative inputs. -/
def negMass : ℕ := ∑ i, if op.weight i < 0 then op.absWeight i else 0

/-- The threshold on the sum of the absolute weights of the true literals. -/
def target : ℤ := op.bias + op.negMass + 1

/-- The word width: every literal sum and the target are below `2 ^ width`. -/
def width : ℕ := Nat.size (∑ i, op.absWeight i + op.target.toNat)

/-- The literal of input `i`: the input itself for a nonnegative weight and its negation
otherwise. -/
def literal (i : Fin op.arity) (x : Fin op.arity → Bool) : Bool :=
  if 0 ≤ op.weight i then x i else !x i

/-- **The threshold through literals**: the weighted sum exceeds the bias exactly when the
absolute weights of the true literals sum to at least the target. -/
theorem interpretation_iff (x : Fin op.arity → Bool) :
    interpretation op x = decide (op.target ≤
      ((∑ i, op.absWeight i * (op.literal i x).toNat : ℕ) : ℤ)) := by
  have hsum : ∑ i, op.weight i * ((x i).toNat : ℤ) =
      ((∑ i, op.absWeight i * (op.literal i x).toNat : ℕ) : ℤ) - op.negMass := by
    simp only [negMass, Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_zero,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [absWeight, literal]
    by_cases hw : 0 ≤ op.weight i
    · rw [ite_eq_left hw, ite_eq_right (not_lt.mpr hw), Int.natCast_natAbs, abs_of_nonneg hw,
        sub_zero]
    · rw [ite_eq_right hw, ite_eq_left (not_le.mp hw), Int.natCast_natAbs,
        abs_of_neg (not_le.mp hw)]
      cases x i <;> simp
  rw [interpretation, hsum, target]
  exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-! ### The circuit -/

/-- A natural number below `2 ^ w` is the value of its first `w` binary digits. -/
theorem sum_testBit_mul_two_pow {w a : ℕ} (ha : a < 2 ^ w) :
    ∑ b : Fin w, (a.testBit b).toNat * 2 ^ (b : ℕ) = a := by
  have := val_equivFin_eq_sum ((equivFin w).symm ⟨a, ha⟩)
  simp only [Equiv.apply_symm_apply, equivFin_symm_apply] at this
  exact this.symm

/-- Bit `w` of a number below `2 ^ (w + 1)` is set exactly when the number is at least
`2 ^ w`. -/
theorem testBit_eq_decide_le {w n : ℕ} (hn : n < 2 ^ (w + 1)) :
    n.testBit w = decide (2 ^ w ≤ n) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hlt : n / 2 ^ w < 2 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    rwa [pow_succ, mul_comm] at hn
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hc
    rw [Nat.div_eq_of_lt (not_le.mp hc)] at h
    simp at h
  · have : 1 ≤ n / 2 ^ w := (Nat.le_div_iff_mul_le (by positivity)).mpr (by simpa using h)
    omega

/-- The sum of all absolute weights and the target is below `2 ^ width`. -/
theorem lt_two_pow_width : ∑ i, op.absWeight i + op.target.toNat < 2 ^ op.width :=
  Nat.lt_size_self _

/-- The circuit of the literal of input `i`. -/
def literalCircuit (i : Fin op.arity) : Circuit Boolean.signature op.arity 1 :=
  if 0 ≤ op.weight i then Circuit.wiring Boolean.signature fun _ => i
  else Circuit.oneGate .not fun _ => i

theorem eval_literalCircuit (i : Fin op.arity) (x : Fin op.arity → Bool) :
    (op.literalCircuit i).eval Boolean.interpretation x 0 = op.literal i x := by
  simp only [literalCircuit, literal]
  split_ifs <;> rfl

/-- Bit `b` of the masked word of input `i`: bit `b` of its absolute weight if its literal is
true, and `false` otherwise. -/
def bitCircuit (i : Fin op.arity) (b : ℕ) : Circuit Boolean.signature op.arity 1 :=
  if (op.absWeight i).testBit b then op.literalCircuit i
  else Circuit.oneGate (.const false) Fin.elim0

theorem eval_bitCircuit (i : Fin op.arity) (b : ℕ) (x : Fin op.arity → Bool) :
    (op.bitCircuit i b).eval Boolean.interpretation x 0 =
      ((op.absWeight i).testBit b && op.literal i x) := by
  simp only [bitCircuit]
  split_ifs with h
  · rw [eval_literalCircuit, h, Bool.true_and]
  · simp only [Bool.not_eq_true] at h
    rw [h, Bool.false_and]
    rfl

/-- The masked word of input `i`: its absolute weight when its literal is true, and `0`
otherwise, in `width + 1` bits. -/
def maskWord (i : Fin op.arity) : Circuit Boolean.signature op.arity (op.width + 1) :=
  Circuit.pi fun b => op.bitCircuit i b

theorem val_eval_maskWord (i : Fin op.arity) (x : Fin op.arity → Bool) :
    (equivFin (op.width + 1) ((op.maskWord i).eval Boolean.interpretation x) : ℕ) =
      op.absWeight i * (op.literal i x).toNat := by
  have ha : op.absWeight i < 2 ^ (op.width + 1) := by
    have h1 : op.absWeight i ≤ ∑ j, op.absWeight j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 := op.lt_two_pow_width
    have h3 : 2 ^ op.width ≤ 2 ^ (op.width + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rw [val_equivFin_eq_sum]
  simp only [maskWord, Circuit.eval_pi, eval_bitCircuit]
  cases op.literal i x
  · simp
  · simp only [Bool.and_true, Bool.toNat_true, mul_one]
    exact sum_testBit_mul_two_pow ha

/-- The offset `2 ^ width - target` added to the literal sum. -/
def offset : ℕ := 2 ^ op.width - op.target.toNat

theorem offset_lt : op.offset < 2 ^ (op.width + 1) := by
  have : 2 ^ op.width ≤ 2 ^ (op.width + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 0 < 2 ^ op.width := by positivity
  simp only [offset]
  omega

/-- The constant word of the offset. -/
def offsetWord : Circuit Boolean.signature op.arity (op.width + 1) :=
  wordConstCircuit op.arity ((equivFin (op.width + 1)).symm ⟨op.offset, op.offset_lt⟩)

/-- The carry-save summands: the masked words and the offset. -/
def summands : List (Circuit Boolean.signature op.arity ((op.width + 1) + (op.width + 1))) :=
  List.ofFn (fun i => pairWithZero (op.maskWord i)) ++ [pairWithZero op.offsetWord]

/-- The sum of the masked words and the offset. -/
def sumCircuit : Circuit Boolean.signature op.arity (op.width + 1) :=
  sumPairs op.arity (op.width + 1) op.summands

theorem val_eval_sumCircuit (x : Fin op.arity → Bool) :
    (equivFin (op.width + 1) (op.sumCircuit.eval Boolean.interpretation x) : ℕ) =
      ∑ i, op.absWeight i * (op.literal i x).toNat + op.offset := by
  have hlt : ∑ i, op.absWeight i * (op.literal i x).toNat + op.offset < 2 ^ (op.width + 1) := by
    have h1 : ∑ i, op.absWeight i * (op.literal i x).toNat ≤ ∑ i, op.absWeight i :=
      Finset.sum_le_sum fun i _ => by cases op.literal i x <;> simp
    have h2 := op.lt_two_pow_width
    have h3 : op.offset ≤ 2 ^ op.width := Nat.sub_le _ _
    rw [pow_succ]
    omega
  rw [sumCircuit, val_eval_sumPairs, summands, List.map_append, List.sum_append, List.map_ofFn,
    List.sum_ofFn]
  simp only [Function.comp_apply, pairVal_eval_pairWithZero, val_eval_maskWord,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, offsetWord,
    eval_wordConstCircuit, Equiv.apply_symm_apply]
  rw [Nat.mod_eq_of_lt (op.offset_lt)]
  have hterm (i : Fin op.arity) : op.absWeight i * (op.literal i x).toNat % 2 ^ (op.width + 1) =
      op.absWeight i * (op.literal i x).toNat := by
    refine Nat.mod_eq_of_lt (lt_of_le_of_lt ?_ hlt)
    exact (Finset.single_le_sum (f := fun j => op.absWeight j * (op.literal j x).toNat)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)).trans (Nat.le_add_right _ _)
  simp only [hterm]
  exact Nat.mod_eq_of_lt hlt

/-- **The De Morgan circuit of an integer threshold gate**: a constant `true` when the target is
at most zero, and otherwise bit `width` of the sum of the masked words and the offset. -/
def deMorganCircuit : Circuit Boolean.signature op.arity 1 :=
  if op.target ≤ 0 then Circuit.oneGate (.const true) Fin.elim0
  else (Circuit.wiring Boolean.signature fun _ => Fin.last op.width).comp op.sumCircuit

/-- The De Morgan circuit of an integer threshold gate computes it. -/
theorem eval_deMorganCircuit (x : Fin op.arity → Bool) :
    op.deMorganCircuit.eval Boolean.interpretation x 0 = interpretation op x := by
  rw [interpretation_iff]
  simp only [deMorganCircuit]
  split_ifs with hT
  · simp only [Circuit.eval_oneGate]
    exact (decide_eq_true (hT.trans (Nat.cast_nonneg _))).symm
  · rw [Circuit.eval_comp, Circuit.eval_wiring, Function.comp_apply]
    have hsum := op.val_eval_sumCircuit x
    set y := op.sumCircuit.eval Boolean.interpretation x
    have hy : y (Fin.last op.width) =
        ((equivFin (op.width + 1) y : ℕ)).testBit op.width := by
      conv_lhs => rw [← (equivFin (op.width + 1)).symm_apply_apply y]
      rw [equivFin_symm_apply]
      rfl
    rw [hy, hsum, testBit_eq_decide_le (hsum ▸ (equivFin (op.width + 1) y).isLt)]
    have hTpos : 0 < op.target := not_le.mp hT
    have hTle : op.target.toNat ≤ 2 ^ op.width := by
      have := op.lt_two_pow_width
      omega
    simp only [offset]
    refine decide_eq_decide.mpr ⟨fun h => ?_, fun h => ?_⟩ <;> omega

/-! ### Size and depth -/

theorem size_literalCircuit_le (i : Fin op.arity) : (op.literalCircuit i).size ≤ 1 := by
  simp only [literalCircuit]
  split_ifs <;> simp

theorem depth_literalCircuit_le (i : Fin op.arity) : (op.literalCircuit i).depth ≤ 1 := by
  simp only [literalCircuit]
  split_ifs <;> simp

theorem size_bitCircuit_le (i : Fin op.arity) (b : ℕ) : (op.bitCircuit i b).size ≤ 1 := by
  simp only [bitCircuit]
  split_ifs
  · exact op.size_literalCircuit_le i
  · simp

theorem depth_bitCircuit_le (i : Fin op.arity) (b : ℕ) : (op.bitCircuit i b).depth ≤ 1 := by
  simp only [bitCircuit]
  split_ifs
  · exact op.depth_literalCircuit_le i
  · simp

theorem size_maskWord_le (i : Fin op.arity) : (op.maskWord i).size ≤ op.width + 1 := by
  rw [maskWord, Circuit.size_pi]
  calc ∑ j : Fin (op.width + 1), (op.bitCircuit i j).size
      ≤ ∑ _j : Fin (op.width + 1), 1 := Finset.sum_le_sum fun j _ => op.size_bitCircuit_le i j
    _ = op.width + 1 := by simp

theorem depth_maskWord_le (i : Fin op.arity) : (op.maskWord i).depth ≤ 1 :=
  Circuit.depth_pi_le _ fun b => op.depth_bitCircuit_le i b

theorem size_sumCircuit_le :
    op.sumCircuit.size ≤ 21 * (op.width + 2) ^ 2 + 4 + op.arity * (op.width + 2) +
      (op.arity + 1) * (40 * (op.width + 1)) := by
  refine (size_sumPairs_le _).trans ?_
  have hlen : op.summands.length = op.arity + 1 := by simp [summands]
  have hsum : (op.summands.map Circuit.size).sum ≤ op.arity * (op.width + 2) + 3 := by
    simp only [summands, List.map_append, List.sum_append, List.map_ofFn, List.sum_ofFn,
      Function.comp_apply, size_pairWithZero, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, offsetWord, size_wordConstCircuit]
    have : ∑ i, ((op.maskWord i).size + 1) ≤ ∑ _i : Fin op.arity, (op.width + 2) :=
      Finset.sum_le_sum fun i _ => by have := op.size_maskWord_le i; omega
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  rw [hlen]
  nlinarith

theorem depth_sumCircuit_le :
    op.sumCircuit.depth ≤ 9 + 2 * Nat.clog 2 (op.width + 2) + 12 * Nat.clog 2 (op.arity + 1) := by
  have hD : ∀ C ∈ op.summands, C.depth ≤ 1 := by
    intro C hC
    simp only [summands, List.mem_append, List.mem_ofFn, List.mem_singleton] at hC
    rcases hC with ⟨i, rfl⟩ | rfl
    · exact (depth_pairWithZero_le _).trans (max_le (op.depth_maskWord_le i) le_rfl)
    · exact (depth_pairWithZero_le _).trans (max_le (depth_wordConstCircuit_le _ _) le_rfl)
  have hlen : op.summands.length = op.arity + 1 := by simp [summands]
  have h := depth_sumPairs_le _ hD
  rw [hlen, show op.width + 1 + 1 = op.width + 2 by omega] at h
  exact h.trans (by omega)

/-- The De Morgan circuit of an integer threshold gate has polynomial size in its arity and
width. -/
theorem size_deMorganCircuit_le :
    op.deMorganCircuit.size ≤ 70 * (op.arity + 1) * (op.width + 2) ^ 2 := by
  set P := (op.arity + 1) * (op.width + 2) ^ 2
  have h1 : (op.width + 2) ^ 2 ≤ P := Nat.le_mul_of_pos_left _ (by omega)
  have hsq : op.width + 2 ≤ (op.width + 2) ^ 2 := Nat.le_self_pow two_ne_zero _
  have h2 : 4 ≤ (op.width + 2) ^ 2 := by
    have := Nat.pow_le_pow_left (by omega : 2 ≤ op.width + 2) 2
    simpa using this
  have h3 : op.arity * (op.width + 2) ≤ P := Nat.mul_le_mul (by omega) hsq
  have h4 : (op.arity + 1) * (op.width + 1) ≤ P := Nat.mul_le_mul le_rfl (by omega)
  have h5 : (op.arity + 1) * (40 * (op.width + 1)) = 40 * ((op.arity + 1) * (op.width + 1)) := by
    ring
  have hP : 70 * (op.arity + 1) * (op.width + 2) ^ 2 = 70 * P := by simp only [P]; ring
  rw [hP]
  simp only [deMorganCircuit]
  split_ifs
  · simp only [Circuit.size_oneGate]
    omega
  · rw [Circuit.size_comp]
    simp only [Circuit.size_wiring]
    refine op.size_sumCircuit_le.trans ?_
    omega

/-- The De Morgan circuit of an integer threshold gate has logarithmic depth in its arity and
width. -/
theorem depth_deMorganCircuit_le :
    op.deMorganCircuit.depth ≤
      9 + 2 * Nat.clog 2 (op.width + 2) + 12 * Nat.clog 2 (op.arity + 1) := by
  simp only [deMorganCircuit]
  split_ifs
  · simp only [Circuit.depth_oneGate]
    omega
  · refine (Circuit.depth_comp_le _ _).trans ?_
    simp only [Circuit.depth_wiring, zero_add]
    exact op.depth_sumCircuit_le

/-- With weights and bias bounded by `B`, the width is at most the bit size of
`(2 k + 2) (B + 1)`. -/
theorem width_le {B : ℕ} (hw : ∀ i, |op.weight i| ≤ B) (hb : |op.bias| ≤ B) :
    op.width ≤ Nat.size ((2 * op.arity + 2) * (B + 1)) := by
  refine Nat.size_le_size ?_
  have habs (i : Fin op.arity) : op.absWeight i ≤ B := by
    have := hw i
    rw [Int.abs_eq_natAbs] at this
    exact_mod_cast this
  have hsum : ∑ i, op.absWeight i ≤ op.arity * B :=
    (Finset.sum_le_sum fun i _ => habs i).trans (by simp)
  have hneg : op.negMass ≤ op.arity * B :=
    (Finset.sum_le_sum fun i _ => by split_ifs <;> simp).trans hsum
  have hb' : op.bias ≤ B := (le_abs_self _).trans hb
  have htarget : op.target.toNat ≤ B + op.arity * B + 1 := by
    simp only [target]
    have : (op.negMass : ℤ) ≤ op.arity * B := by exact_mod_cast hneg
    omega
  nlinarith

end Op

end IntThreshold

end Cslib.Circuits.Boolean
