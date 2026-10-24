/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.Boolean.Selection
import Complexity.Computability.Circuit.CompositionDepth
import Mathlib.Tactic.FinCases

/-!
# Comparing and selecting words

Circuits over the De Morgan basis that compare words of `w` bits, read as numbers with the least
significant bit first (`BitString.equivFin`), and select one of two words.

* The *multiplexer* `muxCircuit w` reads a control bit `c` and two words `a` and `b`, and outputs
  `a` when `c` is true and `b` otherwise. Bit `i` is `(c ∧ a i) ∨ (¬c ∧ b i)`, with one negation of
  `c` shared by all bits: `3 w + 1` gates and depth at most `3`.
* The *comparator* `leCircuit w` reads two words `x` and `y` and outputs whether `x ≤ y`. It scans
  the bits from the least significant: `x ≤ y` on the first `k + 1` bits when `x k < y k`, or when
  `x k = y k` and `x ≤ y` on the first `k` bits; that is the majority of `¬x k`, `y k` and the
  comparison of the first `k` bits. This costs five gates a bit and one for the comparison of empty
  words: `5 w + 1` gates and depth at most `4 w + 1`.
* The *minimum* `minCircuit w` selects the smaller of two words, the first on ties: a comparator
  feeding a multiplexer, of `8 w + 2` gates. The *keyed minimum* `keyedMinCircuit k p` selects, of
  two records made of a key of `k` bits followed by a payload of `p` bits, the one with the smaller
  key, the first on ties, with `8 k + 3 p + 2` gates.

Zero-width words and keys are allowed; the comparator of empty words returns true.
Pairwise keyed selection preserves the first payload on equal keys.

A balanced tree of keyed minimums selects a record with the least key among many
(`Cslib.Circuits.Boolean.tournamentCircuit`).

## Main definitions

* `Cslib.Circuits.Boolean.muxCircuit`, `Cslib.Circuits.Boolean.leCircuit`,
  `Cslib.Circuits.Boolean.minCircuit`, `Cslib.Circuits.Boolean.keyedMinCircuit`: the circuits.
* `Cslib.BitString.recordKey`, `Cslib.BitString.keyedMinFn`: the key of a record, and
  the record with the smaller key.

## Main results

* `Cslib.Circuits.Boolean.eval_muxCircuit`, `size_muxCircuit`, `depth_muxCircuit_le`.
* `Cslib.Circuits.Boolean.eval_leCircuit`, `size_leCircuit`, `depth_leCircuit_le`.
* `Cslib.Circuits.Boolean.eval_minCircuit`, `size_minCircuit`, `depth_minCircuit_le`.
* `Cslib.Circuits.Boolean.eval_keyedMinCircuit`, `size_keyedMinCircuit`,
  `depth_keyedMinCircuit_le`.

## References

Adapted from Samuel Schlesinger's earlier Complexitylib modules
`Circuits/{Multiplexer,BinaryComparison,BinaryMinimum,KeyedMinimum}`.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open BitString

variable {w k p : ℕ}

/-! ### The multiplexer -/

/-- Bit `i` of the multiplexer, `(c ∧ a i) ∨ (¬c ∧ b i)`, on the control `c`, the words `a` and `b`,
and the negated control. -/
def muxBit (i : Fin w) : Formula signature (1 + (w + w) + 1) :=
  ((Formula.input (Fin.castAdd 1 (Fin.castAdd (w + w) 0))).and
      (.input (Fin.castAdd 1 (Fin.natAdd 1 (Fin.castAdd w i))))).or
    ((Formula.input (Fin.natAdd (1 + (w + w)) 0)).and
      (.input (Fin.castAdd 1 (Fin.natAdd 1 (Fin.natAdd w i)))))

/-- The *multiplexer*: reading a control bit `c` and words `a` and `b`, it outputs `a` when `c` is
true and `b` otherwise. -/
def muxCircuit (w : ℕ) : Circuit signature (1 + (w + w)) w :=
  (Circuit.pi fun i => (muxBit i).toCircuit).comp
    ((Circuit.id signature _).append (Circuit.oneGate Op.not fun _ => Fin.castAdd (w + w) 0))

@[simp] theorem eval_muxCircuit (c : Bool) (a b : BitString w) :
    (muxCircuit w).eval interpretation (Fin.append (fun _ : Fin 1 => c) (Fin.append a b)) =
      if c then a else b := by
  funext i
  simp only [muxCircuit, muxBit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_pi,
    Formula.eval_toCircuit, Formula.eval_or, Formula.eval_and, Formula.eval_input, Fin.append_left,
    Fin.append_right, Circuit.eval_wiring, Circuit.eval_oneGate, Function.comp_apply, id]
  cases c <;> simp [interpretation]

@[simp] theorem size_muxCircuit (w : ℕ) : (muxCircuit w).size = 3 * w + 1 := by
  rw [show 3 * w + 1 = 1 + w * 3 by ring]
  simp [muxCircuit, muxBit]

theorem depth_muxCircuit_le (w : ℕ) : (muxCircuit w).depth ≤ 3 :=
  (Circuit.depth_comp_le _ _).trans <| Nat.add_le_add (b := 2) (d := 1)
    (Circuit.depth_pi_le _ fun i => (Formula.depth_toCircuit_le _).trans (by simp [muxBit]))
    ((Circuit.depth_append_le _ _).trans (by simp))

/-! ### The comparator -/

/-- One step of the comparator, on `le`, `x k`, `y k` and `¬x k`:
`(¬x k ∧ y k) ∨ (le ∧ (¬x k ∨ y k))`. -/
def leStepFormula : Formula signature (1 + 2 + 1) :=
  ((Formula.input (Fin.natAdd (1 + 2) 0)).and (.input (Fin.castAdd 1 (Fin.natAdd 1 1)))).or
    ((Formula.input (Fin.castAdd 1 (Fin.castAdd 2 0))).and
      ((Formula.input (Fin.natAdd (1 + 2) 0)).or (.input (Fin.castAdd 1 (Fin.natAdd 1 1)))))

/-- One step of the comparator: from whether `x ≤ y` on the bits below `k`, and from `x k` and
`y k`, whether `x ≤ y` on the bits up to `k`. -/
def leStep : Circuit signature (1 + 2) 1 :=
  leStepFormula.toCircuit.comp
    ((Circuit.id signature _).append (Circuit.oneGate Op.not fun _ => Fin.natAdd 1 0))

theorem eval_leStep (b c d : Bool) :
    leStep.eval interpretation (Fin.append (fun _ : Fin 1 => b) ![c, d]) =
      fun _ => ((!c && d) || (b && (!c || d))) := by
  funext j
  simp only [leStep, leStepFormula, Circuit.eval_comp, Circuit.eval_append,
    Formula.eval_toCircuit, Formula.eval_or, Formula.eval_and, Formula.eval_input, Fin.append_left,
    Fin.append_right, Circuit.eval_wiring, Circuit.eval_oneGate, Function.comp_apply, id]
  cases b <;> cases c <;> cases d <;> rfl

@[simp] theorem size_leStep : leStep.size = 5 :=
  rfl

theorem depth_leStep_le : leStep.depth ≤ 4 :=
  (Circuit.depth_comp_le _ _).trans <| Nat.add_le_add (b := 3) (d := 1)
    ((Formula.depth_toCircuit_le _).trans (by simp [leStepFormula]))
    ((Circuit.depth_append_le _ _).trans (by simp))

/-- The first `w` bits of each of two words of `w + 1` bits. -/
def lowBits (w : ℕ) : Fin (w + w) → Fin (w + 1 + (w + 1)) :=
  Fin.append (fun i => Fin.castAdd (w + 1) i.castSucc) fun i => Fin.natAdd (w + 1) i.castSucc

theorem append_comp_lowBits (x y : BitString (w + 1)) :
    Fin.append x y ∘ lowBits w = Fin.append (Fin.init x) (Fin.init y) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Function.comp_apply, lowBits, Fin.append_left, Fin.init]
  · simp only [Function.comp_apply, lowBits, Fin.append_right, Fin.init]

/-- The last bit of each of two words of `w + 1` bits. -/
def topBits (w : ℕ) : Fin 2 → Fin (w + 1 + (w + 1)) :=
  ![Fin.castAdd (w + 1) (Fin.last w), Fin.natAdd (w + 1) (Fin.last w)]

theorem append_comp_topBits (x y : BitString (w + 1)) :
    Fin.append x y ∘ topBits w = ![x (Fin.last w), y (Fin.last w)] := by
  funext j
  fin_cases j
  · exact Fin.append_left x y (Fin.last w)
  · exact Fin.append_right x y (Fin.last w)

/-- The *comparator*: reading words `x` and `y` of `w` bits, it outputs whether `x ≤ y` as numbers
with the least significant bit first. -/
def leCircuit : (w : ℕ) → Circuit signature (w + w) 1
  | 0 => Circuit.oneGate (Op.const true) Fin.elim0
  | w + 1 => leStep.comp (((leCircuit w).comp (Circuit.wiring signature (lowBits w))).append
      (Circuit.wiring signature (topBits w)))

@[simp] theorem eval_leCircuit (x y : BitString w) :
    (leCircuit w).eval interpretation (Fin.append x y) =
      fun _ => decide (BitString.equivFin w x ≤ BitString.equivFin w y) := by
  induction w with
  | zero =>
    funext j
    have hx : (BitString.equivFin 0 x : ℕ) < 1 := (BitString.equivFin 0 x).isLt
    have hy : (BitString.equivFin 0 y : ℕ) < 1 := (BitString.equivFin 0 y).isLt
    exact (decide_eq_true (Fin.le_iff_val_le_val.2 (by omega))).symm
  | succ w ih =>
    rw [leCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_comp, Circuit.eval_wiring,
      append_comp_lowBits, ih, Circuit.eval_wiring, BitString.decide_equivFin_le_succ,
      append_comp_topBits, eval_leStep]
    funext j
    cases decide (BitString.equivFin w (Fin.init x) ≤ BitString.equivFin w (Fin.init y)) <;>
      cases x (Fin.last w) <;> cases y (Fin.last w) <;> rfl

@[simp] theorem size_leCircuit (w : ℕ) : (leCircuit w).size = 5 * w + 1 := by
  induction w with
  | zero => rfl
  | succ w ih =>
    rw [leCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_comp, ih]
    simp only [Circuit.size_wiring, size_leStep]
    ring

theorem depth_leCircuit_le (w : ℕ) : (leCircuit w).depth ≤ 4 * w + 1 := by
  induction w with
  | zero => simp [leCircuit]
  | succ w ih =>
    rw [leCircuit]
    refine (Circuit.depth_comp_le _ _).trans ?_
    have h : (((leCircuit w).comp (Circuit.wiring signature (lowBits w))).append
        (Circuit.wiring signature (topBits w))).depth ≤ 4 * w + 1 :=
      (Circuit.depth_append_le _ _).trans (max_le ((Circuit.depth_comp_le _ _).trans (by simpa
        using ih)) (by simp))
    have := depth_leStep_le
    omega

/-! ### The minimum and the keyed minimum -/

/-- The *minimum*: reading words `x` and `y` of `w` bits, it outputs the smaller, `x` on ties. -/
def minCircuit (w : ℕ) : Circuit signature (w + w) w :=
  (muxCircuit w).comp ((leCircuit w).append (Circuit.id signature (w + w)))

@[simp] theorem eval_minCircuit (x y : BitString w) :
    (minCircuit w).eval interpretation (Fin.append x y) =
      if BitString.equivFin w x ≤ BitString.equivFin w y then x else y := by
  rw [minCircuit, Circuit.eval_comp, Circuit.eval_append, eval_leCircuit, Circuit.eval_wiring,
    Function.comp_id, eval_muxCircuit]
  simp only [decide_eq_true_eq]

@[simp] theorem size_minCircuit (w : ℕ) : (minCircuit w).size = 8 * w + 2 := by
  rw [minCircuit, Circuit.size_comp, Circuit.size_append, size_leCircuit, size_muxCircuit,
    Circuit.size_wiring]
  ring

theorem depth_minCircuit_le (w : ℕ) : (minCircuit w).depth ≤ 4 * w + 4 :=
  (Circuit.depth_comp_le _ _).trans <| (Nat.add_le_add (depth_muxCircuit_le w)
    ((Circuit.depth_append_le _ _).trans (max_le (depth_leCircuit_le w) (by simp)))).trans_eq
      (by ring)

/-- The keys of two records. -/
def keyBits (k p : ℕ) : Fin (k + k) → Fin (k + p + (k + p)) :=
  Fin.append (fun i => Fin.castAdd (k + p) (Fin.castAdd p i))
    fun i => Fin.natAdd (k + p) (Fin.castAdd p i)

theorem append_comp_keyBits (r s : BitString (k + p)) :
    Fin.append r s ∘ keyBits k p = Fin.append (recordKey r) (recordKey s) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Function.comp_apply, keyBits, Fin.append_left, recordKey, BitString.fstBits_apply]
  · simp only [Function.comp_apply, keyBits, Fin.append_right, recordKey, BitString.fstBits_apply]

/-- The *keyed minimum*: reading two records of a key of `k` bits followed by a payload of `p`
bits, it outputs the one with the smaller key, the first on ties. -/
def keyedMinCircuit (k p : ℕ) : Circuit signature (k + p + (k + p)) (k + p) :=
  (muxCircuit (k + p)).comp
    (((leCircuit k).comp (Circuit.wiring signature (keyBits k p))).append
      (Circuit.id signature _))

@[simp] theorem eval_keyedMinCircuit (r s : BitString (k + p)) :
    (keyedMinCircuit k p).eval interpretation (Fin.append r s) = keyedMinFn r s := by
  rw [keyedMinCircuit, Circuit.eval_comp, Circuit.eval_append, Circuit.eval_comp,
    Circuit.eval_wiring, append_comp_keyBits, eval_leCircuit, Circuit.eval_wiring,
    Function.comp_id, eval_muxCircuit, keyedMinFn]
  simp only [decide_eq_true_eq]

@[simp] theorem size_keyedMinCircuit (k p : ℕ) :
    (keyedMinCircuit k p).size = 8 * k + 3 * p + 2 := by
  rw [keyedMinCircuit, Circuit.size_comp, Circuit.size_append, Circuit.size_comp, size_leCircuit,
    size_muxCircuit, Circuit.size_wiring, Circuit.size_wiring]
  ring

theorem depth_keyedMinCircuit_le (k p : ℕ) : (keyedMinCircuit k p).depth ≤ 4 * k + 4 :=
  (Circuit.depth_comp_le _ _).trans <| (Nat.add_le_add (depth_muxCircuit_le (k + p))
    ((Circuit.depth_append_le _ _).trans (max_le ((Circuit.depth_comp_le _ _).trans
      (by simpa using depth_leCircuit_le k)) (by simp)))).trans_eq (by ring)

end Cslib.Circuits.Boolean
