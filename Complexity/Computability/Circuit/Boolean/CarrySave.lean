/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Balanced
public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Foundations.Data.BitString.Basic
public import Complexity.Foundations.Data.BitString.Weight
import Mathlib.Tactic.Ring

/-!
# Carry-save addition trees and logarithmic-depth bit counting

A 3-to-2 carry-save adder (`csa3to2 w`) reduces three `w`-bit words `x`, `y`, `z` to a bitwise
exclusive-or word `csaSum x y z` and a shifted carry word `csaCarry x y z` in constant depth (`≤ 6`)
and linear size (`≤ 20 w`), preserving the sum of their unsigned values modulo `2 ^ w`
(`val_csaSum_add_val_csaCarry_mod`). Two carry-save layers form a 4-to-2 reducer (`csa4to2 w`) that
combines two redundant carry-save pairs `(a₁, b₁)` and `(a₂, b₂)` into one pair `(s, c)` in depth
at most `12` and size at most `40 w`.

Combining `k` one-bit inputs along a balanced binary tree (`Circuit.balanced`) of 4-to-2 reducers
produces a carry-save pair whose sum modulo `2 ^ w` is the Hamming weight `BitString.weight x`, in
depth `O(log k)` and size `O(k w)`. Iterating `csa3to2 w` with a zero third word `w` times
(`finishCircuit w w`) clears a further carry bit at every step
(`sndBits_eval_finishCircuit_eq_false`), collapsing the carry-save pair to a single `w`-bit binary
numeral in depth `O(w)` and size `O(w²)`.
Taking `w = ⌈log₂ (k + 1)⌉` gives a De Morgan circuit (`weightCircuit k`) of depth `O(log k)` and
size `O(k log k)` that outputs the exact binary representation of `BitString.weight x`
(`val_eval_weightCircuit`) [Chandra, Stockmeyer and Vishkin][ChandraStockmeyerVishkin1984],
[Vollmer, Chapter 1][Vollmer1999].

## Main definitions

* `Cslib.Circuits.Boolean.pairVal`, `Cslib.Circuits.Boolean.maj3`,
  `Cslib.Circuits.Boolean.csaSum`, `Cslib.Circuits.Boolean.csaCarry`: carry-save pair value, 3-bit
  majority carry, and bitwise sum and shifted carry words on `w`-bit words.
* `Cslib.Circuits.Boolean.csaSumFormula`, `Cslib.Circuits.Boolean.maj3Formula`,
  `Cslib.Circuits.Boolean.csaCarryFormula`, `Cslib.Circuits.Boolean.csa4to2FirstIn`: coordinate
  formulas and input wiring for 3-to-2 and 4-to-2 carry-save reduction.
* `Cslib.Circuits.Boolean.csa3to2`, `Cslib.Circuits.Boolean.csa4to2`: 3-to-2 and 4-to-2 carry-save
  reduction circuits on `w`-bit words.
* `Cslib.Circuits.Boolean.finishStepIn`, `Cslib.Circuits.Boolean.finishStep`,
  `Cslib.Circuits.Boolean.finishCircuit`: carry-clearing step and iteration reducing a carry-save
  pair to a single `w`-bit word.
* `Cslib.Circuits.Boolean.zeroPairCircuit`, `Cslib.Circuits.Boolean.bitPairCircuit`,
  `Cslib.Circuits.Boolean.weightPairCircuit`, `Cslib.Circuits.Boolean.weightCircuit`: leaf circuits,
  balanced carry-save reduction tree, and De Morgan circuit computing the binary numeral of the
  Hamming weight of `k` input bits.

## Main results

* `Cslib.Circuits.Boolean.val_csaSum_add_val_csaCarry_mod`: 3-to-2 carry-save reduction preserves
  the sum modulo `2 ^ w`.
* `Cslib.Circuits.Boolean.val_eval_weightCircuit`: `weightCircuit k` computes the exact binary
  numeral of `BitString.weight x` in `⌈log₂ (k + 1)⌉` bits.
* `Cslib.Circuits.Boolean.size_weightCircuit_le`,
  `Cslib.Circuits.Boolean.depth_weightCircuit_le`: size `O(k log k)` and depth `O(log k)`.

## References

* [A. K. Chandra, L. Stockmeyer, U. Vishkin, *Constant depth reducibility*]
  [ChandraStockmeyerVishkin1984]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open BitString Finset

variable {n w k : ℕ}

/-! ### Unsigned word values and carry-save arithmetic -/

/-- The sum of the unsigned values of a carry-save pair of `w`-bit words. -/
def pairVal (p : BitString (w + w)) : ℕ :=
  (BitString.equivFin w (fstBits p) : ℕ) + (BitString.equivFin w (sndBits p) : ℕ)

/-- The carry-save value of an appended pair `(x, y)` is the sum of the unsigned values of `x` and
`y`. -/
@[simp] theorem pairVal_append (x y : BitString w) :
    pairVal (Fin.append x y) = (BitString.equivFin w x : ℕ) + (BitString.equivFin w y : ℕ) := by
  simp [pairVal]

/-- The carry of a 1-bit full adder: whether at least two of the three bits are true. -/
def maj3 (a b c : Bool) : Bool :=
  (a && b) || ((a && c) || (b && c))

/-- Single-bit full-adder identity: the exclusive-or sum plus twice the majority carry equals the
integer sum of the three input bits. -/
theorem toNat_xor_add_two_mul_toNat_maj3 (a b c : Bool) :
    ((a ^^ b) ^^ c).toNat + 2 * (maj3 a b c).toNat = a.toNat + b.toNat + c.toNat := by
  cases a <;> cases b <;> cases c <;> rfl

/-- The bitwise exclusive-or word of a 3-to-2 carry-save adder on `w`-bit words. -/
def csaSum (x y z : BitString w) : BitString w :=
  fun i => (x i ^^ y i) ^^ z i

/-- The shifted carry word of a 3-to-2 carry-save adder on `w`-bit words: bit `0` is `false` and
bit `i + 1` is the full-adder carry from bit `i`. -/
def csaCarry (x y z : BitString w) : BitString w :=
  fun i => if h : 0 < (i : ℕ) then
    maj3 (x ⟨(i : ℕ) - 1, by omega⟩) (y ⟨(i : ℕ) - 1, by omega⟩) (z ⟨(i : ℕ) - 1, by omega⟩)
  else false

private theorem val_csaCarry_add_top (x y z : BitString (w + 1)) :
    (BitString.equivFin (w + 1) (csaCarry x y z) : ℕ) +
      (maj3 (x (Fin.last w)) (y (Fin.last w)) (z (Fin.last w))).toNat * 2 ^ (w + 1) =
    ∑ i : Fin (w + 1), (maj3 (x i) (y i) (z i)).toNat * 2 ^ ((i : ℕ) + 1) := by
  rw [val_equivFin_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [csaCarry, Fin.val_zero, lt_self_iff_false, ↓reduceDIte, Bool.toNat_false, zero_mul,
    zero_add, Fin.val_succ, Nat.add_pos_right _ Nat.one_pos, Nat.add_sub_cancel, Fin.val_castSucc,
    Fin.val_last]
  rfl

/-- **Carry-save 3-to-2 invariant**: the sum and shifted carry words have the same sum of unsigned
values modulo `2 ^ w` as the three input words. -/
theorem val_csaSum_add_val_csaCarry_mod (x y z : BitString w) :
    ((BitString.equivFin w (csaSum x y z) : ℕ) + (BitString.equivFin w (csaCarry x y z) : ℕ)) %
      2 ^ w =
    ((BitString.equivFin w x : ℕ) + (BitString.equivFin w y : ℕ) +
      (BitString.equivFin w z : ℕ)) % 2 ^ w := by
  rcases w with _ | w
  · simp [Nat.mod_one]
  · have hsum : (BitString.equivFin (w + 1) x : ℕ) + (BitString.equivFin (w + 1) y : ℕ) +
        (BitString.equivFin (w + 1) z : ℕ) =
      (BitString.equivFin (w + 1) (csaSum x y z) : ℕ) +
        (BitString.equivFin (w + 1) (csaCarry x y z) : ℕ) +
        (maj3 (x (Fin.last w)) (y (Fin.last w)) (z (Fin.last w))).toNat * 2 ^ (w + 1) := by
      rw [add_assoc (BitString.equivFin (w + 1) (csaSum x y z) : ℕ), val_csaCarry_add_top,
        val_equivFin_eq_sum x, val_equivFin_eq_sum y, val_equivFin_eq_sum z,
        val_equivFin_eq_sum (csaSum x y z), ← sum_add_distrib, ← sum_add_distrib,
        ← sum_add_distrib]
      refine sum_congr rfl fun i _ => ?_
      calc (x i).toNat * 2 ^ (i : ℕ) + (y i).toNat * 2 ^ (i : ℕ) + (z i).toNat * 2 ^ (i : ℕ)
        _ = ((x i).toNat + (y i).toNat + (z i).toNat) * 2 ^ (i : ℕ) := by ring
        _ = ((csaSum x y z i).toNat + 2 * (maj3 (x i) (y i) (z i)).toNat) * 2 ^ (i : ℕ) := by
          rw [csaSum, toNat_xor_add_two_mul_toNat_maj3]
        _ = (csaSum x y z i).toNat * 2 ^ (i : ℕ) +
            (maj3 (x i) (y i) (z i)).toNat * 2 ^ ((i : ℕ) + 1) := by
          rw [pow_succ]; ring
    rw [hsum, Nat.add_mul_mod_self_right]

/-- When the third word is zero and the first `t` bits of `y` are `false`, the first `t + 1` bits
of the shifted carry word `csaCarry x y 0` are `false`. -/
theorem csaCarry_eq_false_of_lt {t : ℕ} (x y : BitString w)
    (hy : ∀ i : Fin w, (i : ℕ) < t → y i = false) (i : Fin w) (hi : (i : ℕ) < t + 1) :
    csaCarry x y (fun _ => false) i = false := by
  simp only [csaCarry]
  split_ifs with h
  · have hlt : (⟨(i : ℕ) - 1, by omega⟩ : Fin w).val < t := by dsimp; omega
    rw [hy _ hlt]
    cases x ⟨(i : ℕ) - 1, by omega⟩ <;> rfl
  · rfl

/-! ### 3-to-2 and 4-to-2 carry-save circuits -/

/-- Formula for bit `i` of `csaSum` on three `w`-bit words. -/
def csaSumFormula (w : ℕ) (i : Fin w) : Formula signature (w + (w + w)) :=
  Formula.xor
    (Formula.xor (.input (Fin.castAdd (w + w) i)) (.input (Fin.natAdd w (Fin.castAdd w i))))
    (.input (Fin.natAdd w (Fin.natAdd w i)))

/-- `csaSumFormula w i` evaluates to bit `i` of `csaSum` on the three `w`-bit words of `u`. -/
@[simp] theorem eval_csaSumFormula (i : Fin w) (u : BitString (w + (w + w))) :
    (csaSumFormula w i).eval interpretation u =
      csaSum (fstBits u) (fstBits (sndBits u)) (sndBits (sndBits u)) i := by
  simp [csaSumFormula, csaSum, fstBits, sndBits]

/-- `csaSumFormula w i` has size `15`. -/
@[simp] theorem size_csaSumFormula (i : Fin w) : (csaSumFormula w i).size = 15 := by
  simp [csaSumFormula, Formula.size_xor]

/-- `csaSumFormula w i` has depth at most `6`. -/
theorem depth_csaSumFormula_le (i : Fin w) : (csaSumFormula w i).depth ≤ 6 := by
  have h1 := Formula.depth_xor_le
    (Formula.input (σ := signature) (Fin.castAdd (w + w) i))
    (Formula.input (σ := signature) (Fin.natAdd w (Fin.castAdd w i)))
  have h2 := Formula.depth_xor_le
    (Formula.xor (.input (Fin.castAdd (w + w) i)) (.input (Fin.natAdd w (Fin.castAdd w i))))
    (Formula.input (σ := signature) (Fin.natAdd w (Fin.natAdd w i)))
  simp only [Formula.depth_input] at h1 h2
  rw [csaSumFormula]
  omega

/-- Formula for `maj3` on three input coordinates. -/
def maj3Formula (a b c : Fin n) : Formula signature n :=
  ((Formula.input a).and (.input b)).or
    (((Formula.input a).and (.input c)).or ((Formula.input b).and (.input c)))

/-- `maj3Formula a b c` evaluates to `maj3 (u a) (u b) (u c)`. -/
@[simp] theorem eval_maj3Formula (a b c : Fin n) (u : BitString n) :
    (maj3Formula a b c).eval interpretation u = maj3 (u a) (u b) (u c) := by
  simp [maj3Formula, maj3]

/-- `maj3Formula a b c` has size `5`. -/
@[simp] theorem size_maj3Formula (a b c : Fin n) : (maj3Formula a b c).size = 5 :=
  rfl

/-- `maj3Formula a b c` has depth at most `3`. -/
theorem depth_maj3Formula_le (a b c : Fin n) : (maj3Formula a b c).depth ≤ 3 := by
  simp [maj3Formula]

/-- Formula for bit `i` of `csaCarry` on three `w`-bit words. -/
def csaCarryFormula (w : ℕ) (i : Fin w) : Formula signature (w + (w + w)) :=
  if h : 0 < (i : ℕ) then
    maj3Formula (Fin.castAdd (w + w) ⟨(i : ℕ) - 1, by omega⟩)
      (Fin.natAdd w (Fin.castAdd w ⟨(i : ℕ) - 1, by omega⟩))
      (Fin.natAdd w (Fin.natAdd w ⟨(i : ℕ) - 1, by omega⟩))
  else .const false

/-- `csaCarryFormula w i` evaluates to bit `i` of `csaCarry` on the three `w`-bit words of `u`. -/
@[simp] theorem eval_csaCarryFormula (i : Fin w) (u : BitString (w + (w + w))) :
    (csaCarryFormula w i).eval interpretation u =
      csaCarry (fstBits u) (fstBits (sndBits u)) (sndBits (sndBits u)) i := by
  simp only [csaCarryFormula, csaCarry]
  split_ifs with h <;> simp [fstBits, sndBits]

/-- `csaCarryFormula w i` has size at most `5`. -/
theorem size_csaCarryFormula_le (i : Fin w) : (csaCarryFormula w i).size ≤ 5 := by
  simp only [csaCarryFormula]
  split_ifs <;> simp

/-- `csaCarryFormula w i` has depth at most `3`. -/
theorem depth_csaCarryFormula_le (i : Fin w) : (csaCarryFormula w i).depth ≤ 3 := by
  simp only [csaCarryFormula]
  split_ifs
  · exact depth_maj3Formula_le _ _ _
  · simp

/-- **3-to-2 carry-save adder**: reduces three `w`-bit words to two `w`-bit words `(sum, carry)`
with the same sum modulo `2 ^ w`, using at most `20 w` gates and depth at most `6`. -/
def csa3to2 (w : ℕ) : Circuit signature (w + (w + w)) (w + w) :=
  (Circuit.pi fun i => (csaSumFormula w i).toCircuit).append
    (Circuit.pi fun i => (csaCarryFormula w i).toCircuit)

/-- `csa3to2 w` evaluates to the pair `(csaSum, csaCarry)` on the three `w`-bit words of `u`. -/
@[simp] theorem eval_csa3to2 (u : BitString (w + (w + w))) :
    (csa3to2 w).eval interpretation u =
      Fin.append (csaSum (fstBits u) (fstBits (sndBits u)) (sndBits (sndBits u)))
        (csaCarry (fstBits u) (fstBits (sndBits u)) (sndBits (sndBits u))) := by
  rw [csa3to2, Circuit.eval_append]
  congr 1 <;> funext i <;> simp

/-- `csa3to2 w` preserves the sum of the three `w`-bit input words modulo `2 ^ w`. -/
theorem pairVal_eval_csa3to2_mod (u : BitString (w + (w + w))) :
    pairVal ((csa3to2 w).eval interpretation u) % 2 ^ w =
      ((BitString.equivFin w (fstBits u) : ℕ) + pairVal (sndBits u)) % 2 ^ w := by
  rw [eval_csa3to2, pairVal_append, val_csaSum_add_val_csaCarry_mod, pairVal, add_assoc]

/-- `csa3to2 w` has size at most `20 * w`. -/
theorem size_csa3to2_le (w : ℕ) : (csa3to2 w).size ≤ 20 * w := by
  rw [csa3to2, Circuit.size_append, Circuit.size_pi, Circuit.size_pi]
  have h1 : ∑ i : Fin w, (csaSumFormula w i).toCircuit.size = 15 * w := by
    simp [Formula.size_toCircuit, mul_comm]
  have h2 : ∑ i : Fin w, (csaCarryFormula w i).toCircuit.size ≤ 5 * w := by
    simpa [Formula.size_toCircuit, mul_comm] using
      sum_le_card_nsmul (univ : Finset (Fin w))
        (fun i => (csaCarryFormula w i).toCircuit.size) 5 fun i _ => by
          rw [Formula.size_toCircuit]
          exact size_csaCarryFormula_le i
  omega

/-- `csa3to2 w` has depth at most `6`. -/
theorem depth_csa3to2_le (w : ℕ) : (csa3to2 w).depth ≤ 6 :=
  (Circuit.depth_append_le _ _).trans <| max_le
    (Circuit.depth_pi_le _ fun i => (Formula.depth_toCircuit_le _).trans (depth_csaSumFormula_le i))
    ((Circuit.depth_pi_le _ fun i =>
      (Formula.depth_toCircuit_le _).trans (depth_csaCarryFormula_le i)).trans (by omega))

/-- Wiring selecting the first three `w`-bit words of two carry-save pairs. -/
def csa4to2FirstIn (w : ℕ) : Fin (w + (w + w)) → Fin ((w + w) + (w + w)) :=
  Fin.append (Fin.castAdd (w + w) ∘ Fin.castAdd w)
    (Fin.append (Fin.castAdd (w + w) ∘ Fin.natAdd w) (Fin.natAdd (w + w) ∘ Fin.castAdd w))

/-- **4-to-2 carry-save reducer**: combines two carry-save pairs `(a₁, b₁)` and `(a₂, b₂)` of
`w`-bit words into a single carry-save pair in depth at most `12` and size at most `40 w`. -/
def csa4to2 (w : ℕ) : Circuit signature ((w + w) + (w + w)) (w + w) :=
  (csa3to2 w).comp
    ((Circuit.wiring signature (Fin.natAdd (w + w) ∘ Fin.natAdd w)).append
      ((csa3to2 w).comp (Circuit.wiring signature (csa4to2FirstIn w))))

/-- `csa4to2 w` preserves the sum of the two carry-save input pairs modulo `2 ^ w`. -/
theorem pairVal_eval_csa4to2_mod (p₁ p₂ : BitString (w + w)) :
    pairVal ((csa4to2 w).eval interpretation (Fin.append p₁ p₂)) % 2 ^ w =
      (pairVal p₁ + pairVal p₂) % 2 ^ w := by
  rw [csa4to2, Circuit.eval_comp, pairVal_eval_csa3to2_mod, Circuit.eval_append, fstBits_append,
    sndBits_append, Circuit.eval_comp, Circuit.eval_wiring, Circuit.eval_wiring,
     ← Nat.add_mod_mod, pairVal_eval_csa3to2_mod, Nat.add_mod_mod]
  have h1 : Fin.append p₁ p₂ ∘ (Fin.natAdd (w + w) ∘ Fin.natAdd w) = sndBits p₂ := by
    funext i
    simp [sndBits, -Fin.natAdd_eq_addNat]
  have h2 : fstBits (Fin.append p₁ p₂ ∘ csa4to2FirstIn w) = fstBits p₁ := by
    funext i
    simp [fstBits, csa4to2FirstIn, -Fin.natAdd_eq_addNat]
  have h3 : sndBits (Fin.append p₁ p₂ ∘ csa4to2FirstIn w) =
      Fin.append (sndBits p₁) (fstBits p₂) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [fstBits, sndBits, csa4to2FirstIn, -Fin.natAdd_eq_addNat]
  rw [h1, h2, h3, pairVal_append]
  congr 1
  unfold pairVal
  ring

/-- `csa4to2 w` has size at most `40 * w`. -/
theorem size_csa4to2_le (w : ℕ) : (csa4to2 w).size ≤ 40 * w := by
  rw [csa4to2, Circuit.size_comp, Circuit.size_append, Circuit.size_comp, Circuit.size_wiring,
    Circuit.size_wiring, zero_add, zero_add]
  have := size_csa3to2_le w
  omega

/-- `csa4to2 w` has depth at most `12`. -/
theorem depth_csa4to2_le (w : ℕ) : (csa4to2 w).depth ≤ 12 := by
  rw [csa4to2]
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h := depth_csa3to2_le w
  have h' : ((Circuit.wiring signature (Fin.natAdd (w + w) ∘ Fin.natAdd w)).append
      ((csa3to2 w).comp (Circuit.wiring signature (csa4to2FirstIn w)))).depth ≤ 6 :=
    (Circuit.depth_append_le _ _).trans (max_le (by simp)
      ((Circuit.depth_comp_le _ _).trans (by simpa using h)))
  omega

/-! ### Carry-clearing iteration -/

/-- Wiring that appends `w` copies of a single constant wire to a `(w + w)`-bit carry-save pair. -/
def finishStepIn (w : ℕ) : Fin (w + (w + w)) → Fin ((w + w) + 1) :=
  Fin.append (Fin.castAdd 1 ∘ Fin.castAdd w)
    (Fin.append (Fin.castAdd 1 ∘ Fin.natAdd w) fun _ => Fin.natAdd (w + w) 0)

/-- One carry-clearing step: applies `csa3to2 w` to `(a, b, 0)`, clearing one more low carry bit. -/
def finishStep (w : ℕ) : Circuit signature (w + w) (w + w) :=
  (csa3to2 w).comp ((Circuit.wiring signature (finishStepIn w)).comp
    ((Circuit.id signature (w + w)).append (Circuit.oneGate (Op.const false) Fin.elim0)))

/-- `finishStep w` evaluates to `(csaSum a b 0, csaCarry a b 0)` on the carry-save pair
`p = (a, b)`. -/
theorem eval_finishStep (p : BitString (w + w)) :
    (finishStep w).eval interpretation p =
      Fin.append (csaSum (fstBits p) (sndBits p) (fun _ => false))
        (csaCarry (fstBits p) (sndBits p) (fun _ => false)) := by
  rw [finishStep, Circuit.eval_comp, Circuit.eval_comp, eval_csa3to2]
  have h1 : fstBits ((Circuit.wiring signature (finishStepIn w)).eval interpretation
      (((Circuit.id signature (w + w)).append
        (Circuit.oneGate (Op.const false) Fin.elim0)).eval interpretation p)) = fstBits p := by
    funext i
    simp [fstBits, finishStepIn, -Fin.natAdd_eq_addNat]
  have h2 : fstBits (sndBits ((Circuit.wiring signature (finishStepIn w)).eval interpretation
      (((Circuit.id signature (w + w)).append
        (Circuit.oneGate (Op.const false) Fin.elim0)).eval interpretation p))) = sndBits p := by
    funext i
    simp [fstBits, sndBits, finishStepIn, -Fin.natAdd_eq_addNat]
  have h3 : sndBits (sndBits ((Circuit.wiring signature (finishStepIn w)).eval interpretation
      (((Circuit.id signature (w + w)).append
        (Circuit.oneGate (Op.const false) Fin.elim0)).eval interpretation p))) =
      fun _ => false := by
    funext i
    simp [sndBits, finishStepIn, interpretation, -Fin.natAdd_eq_addNat]
  rw [h1, h2, h3]

/-- `finishStep w` preserves the carry-save value modulo `2 ^ w`. -/
theorem pairVal_eval_finishStep_mod (p : BitString (w + w)) :
    pairVal ((finishStep w).eval interpretation p) % 2 ^ w = pairVal p % 2 ^ w := by
  rw [eval_finishStep, pairVal_append, val_csaSum_add_val_csaCarry_mod, val_equivFin_false,
    add_zero, pairVal]

/-- `finishStep w` has size at most `20 * w + 1`. -/
theorem size_finishStep_le (w : ℕ) : (finishStep w).size ≤ 20 * w + 1 := by
  simp only [finishStep, Circuit.size_comp, Circuit.size_append, Circuit.size_wiring,
    Circuit.size_oneGate]
  have := size_csa3to2_le w
  omega

/-- `finishStep w` has depth at most `7`. -/
theorem depth_finishStep_le (w : ℕ) : (finishStep w).depth ≤ 7 := by
  rw [finishStep]
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h := depth_csa3to2_le w
  have h' : ((Circuit.wiring signature (finishStepIn w)).comp
      ((Circuit.id signature (w + w)).append
        (Circuit.oneGate (Op.const false) Fin.elim0))).depth ≤ 1 :=
    (Circuit.depth_comp_le _ _).trans (by
      simpa using (Circuit.depth_append_le _ _).trans (by simp))
  omega

/-- `t` steps of carry-clearing on a `(w + w)`-bit carry-save pair. -/
def finishCircuit (w : ℕ) : ℕ → Circuit signature (w + w) (w + w)
  | 0 => Circuit.id signature (w + w)
  | t + 1 => (finishStep w).comp (finishCircuit w t)

/-- `finishCircuit w t` preserves the carry-save value modulo `2 ^ w`. -/
theorem pairVal_eval_finishCircuit_mod (t : ℕ) (p : BitString (w + w)) :
    pairVal ((finishCircuit w t).eval interpretation p) % 2 ^ w = pairVal p % 2 ^ w := by
  induction t with
  | zero => rfl
  | succ t ih => rw [finishCircuit, Circuit.eval_comp, pairVal_eval_finishStep_mod, ih]

/-- After `t` carry-clearing steps, the first `t` bits of the carry word are `false`. -/
theorem sndBits_eval_finishCircuit_eq_false (t : ℕ) (p : BitString (w + w)) (i : Fin w)
    (hi : (i : ℕ) < t) :
    sndBits ((finishCircuit w t).eval interpretation p) i = false := by
  induction t generalizing i with
  | zero => omega
  | succ t ih =>
    rw [finishCircuit, Circuit.eval_comp, eval_finishStep, sndBits_append]
    exact csaCarry_eq_false_of_lt _ _ (fun j hj => ih j hj) i hi

/-- After `w` carry-clearing steps, the carry word is identically zero, so the first `w`-bit word
has unsigned value congruent to `pairVal p` modulo `2 ^ w`. -/
theorem val_fstBits_eval_finishCircuit_mod (p : BitString (w + w)) :
    (BitString.equivFin w (fstBits ((finishCircuit w w).eval interpretation p)) : ℕ) % 2 ^ w =
      pairVal p % 2 ^ w := by
  have h := pairVal_eval_finishCircuit_mod w p
  have hsnd : sndBits ((finishCircuit w w).eval interpretation p) = fun _ => false :=
    funext fun i => sndBits_eval_finishCircuit_eq_false w p i i.isLt
  unfold pairVal at h
  rwa [hsnd, val_equivFin_false, add_zero] at h

/-- `finishCircuit w t` has size at most `t * (20 * w + 1)`. -/
theorem size_finishCircuit_le (w t : ℕ) : (finishCircuit w t).size ≤ t * (20 * w + 1) := by
  induction t with
  | zero => simp [finishCircuit]
  | succ t ih =>
    rw [finishCircuit, Circuit.size_comp, add_one_mul]
    exact Nat.add_le_add ih (size_finishStep_le w)

/-- `finishCircuit w t` has depth at most `7 * t`. -/
theorem depth_finishCircuit_le (w t : ℕ) : (finishCircuit w t).depth ≤ 7 * t := by
  induction t with
  | zero => simp [finishCircuit]
  | succ t ih =>
    rw [finishCircuit]
    refine (Circuit.depth_comp_le _ _).trans ?_
    have := depth_finishStep_le w
    omega

/-! ### Balanced carry-save tree for Hamming weight -/

/-- A carry-save pair of `w`-bit words all of whose bits are `false`, from one `const false`
gate. -/
def zeroPairCircuit (k w : ℕ) : Circuit signature k (w + w) :=
  (Circuit.wiring signature fun _ => 0).comp (Circuit.oneGate (Op.const false) Fin.elim0)

/-- `zeroPairCircuit k w` outputs `false` on every wire. -/
@[simp] theorem eval_zeroPairCircuit (x : BitString k) :
    (zeroPairCircuit k w).eval interpretation x = fun _ => false :=
  rfl

/-- `zeroPairCircuit k w` has size `1`. -/
@[simp] theorem size_zeroPairCircuit : (zeroPairCircuit k w).size = 1 :=
  rfl

/-- `zeroPairCircuit k w` has depth at most `1`. -/
theorem depth_zeroPairCircuit_le : (zeroPairCircuit k w).depth ≤ 1 :=
  (Circuit.depth_comp_le _ _).trans (by simp)

/-- Leaf circuit placing input bit `j : Fin k` into bit `0` of the first `w`-bit word, and `false`
on all other wires of the `(w + w)`-bit carry-save pair, using one `const false` gate. -/
def bitPairCircuit (k w : ℕ) (j : Fin k) : Circuit signature k (w + w) :=
  (Circuit.wiring signature (Fin.addCases
      (fun i : Fin w => if (i : ℕ) = 0 then Fin.castAdd 1 j else Fin.natAdd k 0)
      fun _ : Fin w => Fin.natAdd k 0)).comp
    ((Circuit.id signature k).append (Circuit.oneGate (Op.const false) Fin.elim0))

/-- `bitPairCircuit k w j` outputs a carry-save pair with value congruent to `(x j).toNat` modulo
`2 ^ w`. -/
theorem pairVal_eval_bitPairCircuit_mod (j : Fin k) (x : BitString k) :
    pairVal ((bitPairCircuit k w j).eval interpretation x) % 2 ^ w = (x j).toNat % 2 ^ w := by
  rcases w with _ | w
  · simp [Nat.mod_one]
  · rw [pairVal]
    have hsnd : sndBits ((bitPairCircuit k (w + 1) j).eval interpretation x) =
        fun _ => false := by
      funext i
      simp [bitPairCircuit, interpretation, -Fin.natAdd_eq_addNat]
    rw [hsnd, val_equivFin_false, add_zero, val_equivFin_eq_sum, Fin.sum_univ_succ]
    have h0 : fstBits ((bitPairCircuit k (w + 1) j).eval interpretation x) 0 = x j := by
      simp [bitPairCircuit, -Fin.natAdd_eq_addNat]
    have hsucc : ∀ i : Fin w,
        fstBits ((bitPairCircuit k (w + 1) j).eval interpretation x) i.succ = false := fun i => by
      simp [bitPairCircuit, interpretation, -Fin.natAdd_eq_addNat]
    simp [h0, hsucc, -fstBits_apply]

/-- `bitPairCircuit k w j` has size `1`. -/
@[simp] theorem size_bitPairCircuit (j : Fin k) : (bitPairCircuit k w j).size = 1 :=
  rfl

/-- `bitPairCircuit k w j` has depth at most `1`. -/
theorem depth_bitPairCircuit_le (j : Fin k) : (bitPairCircuit k w j).depth ≤ 1 :=
  (Circuit.depth_comp_le _ _).trans (by
    simpa using (Circuit.depth_append_le _ _).trans (by simp))

/-- Balanced binary tree of `csa4to2 w` reducers over all `k` input bits. -/
def weightPairCircuit (k w : ℕ) : Circuit signature k (w + w) :=
  Circuit.balanced (csa4to2 w) (zeroPairCircuit k w) (List.ofFn (bitPairCircuit k w))

private theorem pairVal_balancedFold_mod {β : Type*}
    (op : BitString (w + w) → BitString (w + w) → BitString (w + w))
    (hop : ∀ u v, pairVal (op u v) % 2 ^ w = (pairVal u + pairVal v) % 2 ^ w)
    (e : BitString (w + w)) (he : pairVal e % 2 ^ w = 0)
    (f : β → BitString (w + w)) (l : List β) :
    pairVal (l.balancedFold op e f) % 2 ^ w =
      (l.map fun b => pairVal (f b) % 2 ^ w).sum % 2 ^ w :=
  List.balancedFold_induction
    (p := fun l u => pairVal u % 2 ^ w = (l.map fun b => pairVal (f b) % 2 ^ w).sum % 2 ^ w)
    he (fun b => by simp)
    (fun l₁ l₂ u v _ _ hu hv => by
      rw [hop, Nat.add_mod, hu, hv, ← Nat.add_mod, List.map_append, List.sum_append]) l

/-- `weightPairCircuit k w` outputs a carry-save pair whose value modulo `2 ^ w` is the Hamming
weight `BitString.weight x`. -/
theorem pairVal_eval_weightPairCircuit_mod (x : BitString k) :
    pairVal ((weightPairCircuit k w).eval interpretation x) % 2 ^ w =
      BitString.weight x % 2 ^ w := by
  rw [weightPairCircuit, Circuit.eval_balanced,
    pairVal_balancedFold_mod _ (fun u v => pairVal_eval_csa4to2_mod u v) _
      (by simp [pairVal, fstBits, sndBits])]
  simp only [List.map_ofFn, Function.comp_def, pairVal_eval_bitPairCircuit_mod, List.sum_ofFn,
    ← Finset.sum_nat_mod, BitString.weight_eq_sum_toNat]

/-- `weightPairCircuit k w` has size at most `max 1 k + k * (40 * w)`. -/
theorem size_weightPairCircuit_le (k w : ℕ) :
    (weightPairCircuit k w).size ≤ max 1 k + k * (40 * w) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp [weightPairCircuit, Circuit.balanced]
  · rw [weightPairCircuit, Circuit.size_balanced _ _ (by simpa using hk.ne')]
    simp only [List.map_ofFn, Function.comp_def, size_bitPairCircuit, List.sum_ofFn,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one,
      List.length_ofFn, Nat.max_eq_right hk]
    refine Nat.add_le_add_left ((Nat.mul_le_mul_right _ (Nat.sub_le k 1)).trans
      (Nat.mul_le_mul_left k (size_csa4to2_le w))) k

/-- `weightPairCircuit k w` has depth at most `1 + 12 * Nat.clog 2 k`. -/
theorem depth_weightPairCircuit_le (k w : ℕ) :
    (weightPairCircuit k w).depth ≤ 1 + 12 * Nat.clog 2 k := by
  refine (Circuit.depth_balanced_le _ _ (D := 1)
    (fun C hC => ?_) (fun _ => depth_zeroPairCircuit_le)).trans ?_
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hC
    exact depth_bitPairCircuit_le j
  · rw [List.length_ofFn]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (depth_csa4to2_le w)) 1

/-- **Logarithmic-depth Hamming weight circuit**: outputs the `⌈log₂ (k + 1)⌉`-bit binary numeral
of `BitString.weight x` (least significant bit first), using `O(k log k)` gates and depth
`O(log k)`. -/
def weightCircuit (k : ℕ) : Circuit signature k (Nat.clog 2 (k + 1)) :=
  let w := Nat.clog 2 (k + 1)
  (Circuit.wiring signature (Fin.castAdd w)).comp
    ((finishCircuit w w).comp (weightPairCircuit k w))

/-- `weightCircuit k` computes the exact binary numeral of `BitString.weight x`. -/
theorem val_eval_weightCircuit (x : BitString k) :
    (BitString.equivFin (Nat.clog 2 (k + 1)) ((weightCircuit k).eval interpretation x) : ℕ) =
      BitString.weight x := by
  set w := Nat.clog 2 (k + 1)
  have hlt : BitString.weight x < 2 ^ w :=
    (BitString.weight_le_length x).trans_lt
      ((Nat.lt_succ_self k).trans_le (Nat.le_pow_clog one_lt_two (k + 1)))
  have heval :
      ((BitString.equivFin w ((weightCircuit k).eval interpretation x) : Fin (2 ^ w)) : ℕ) <
        2 ^ w := (BitString.equivFin w ((weightCircuit k).eval interpretation x)).isLt
  rw [← Nat.mod_eq_of_lt heval, ← Nat.mod_eq_of_lt hlt, weightCircuit, Circuit.eval_comp,
    Circuit.eval_comp, Circuit.eval_wiring]
  exact (val_fstBits_eval_finishCircuit_mod _).trans (pairVal_eval_weightPairCircuit_mod x)

/-- `weightCircuit k` has size `O(k log k)`. -/
theorem size_weightCircuit_le (k : ℕ) :
    (weightCircuit k).size ≤
      max 1 k + k * (40 * Nat.clog 2 (k + 1)) +
        Nat.clog 2 (k + 1) * (20 * Nat.clog 2 (k + 1) + 1) := by
  simp only [weightCircuit, Circuit.size_comp, Circuit.size_wiring, add_zero]
  exact Nat.add_le_add (size_weightPairCircuit_le k _) (size_finishCircuit_le _ _)

/-- `weightCircuit k` has depth `O(log k)`. -/
theorem depth_weightCircuit_le (k : ℕ) :
    (weightCircuit k).depth ≤ 1 + 19 * Nat.clog 2 (k + 1) := by
  dsimp [weightCircuit]
  refine (Circuit.depth_comp_le _ _).trans ?_
  rw [Circuit.depth_wiring, zero_add]
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h1 := depth_finishCircuit_le (Nat.clog 2 (k + 1)) (Nat.clog 2 (k + 1))
  have h2 : (weightPairCircuit k (Nat.clog 2 (k + 1))).depth ≤ 1 + 12 * Nat.clog 2 (k + 1) :=
    (depth_weightPairCircuit_le k (Nat.clog 2 (k + 1))).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left 12 (Nat.clog_mono_right 2 (Nat.le_succ k))) 1)
  omega

end Cslib.Circuits.Boolean
