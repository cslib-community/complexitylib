/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DeMorgan
public import CslibFrontier.Computability.Circuit.Inputization
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Computability.Circuit.StraightLine
import CslibFrontier.Foundations.Data.BitString.Binary
import Cslib.Computability.Circuit.Synthesis

/-!
# Window templates

The reduction of Ilango, Loff and Oliveira [IlangoLoffOliveira2020, §4.2, pp. 22:20–22:21] gives
a circuit minimizer a random truth table `T` on `p` input bits together with, for each set `A_i`
of a set system, a circuit whose gates depend only on the entries of `T` inside `A_i`; its last
gate computes `T` restricted to `A_i`. Covering the inputs with `c` of the sets, `T` is the OR of
`c` such windows, which costs `c - 1` further gates (completeness, [p. 22:22, Lemma 15]).

This file builds such a family in the constant-free De Morgan basis, as one program `template A T`
on `p` inputs, and proves the facts the reduction uses about it. The source writes each window as a
canonical DNF [pp. 22:19–22:20]; here all windows share the `p` negations, a constant-zero gate and
the `p · 2^p` gates of prefix conjunctions, and window `i` is an OR chain: its gate `window i y` is
the OR of the accepted inputs of `A i` up to `y`, in the order of `BitString.equivFin`. This is a
construction choice internal to the proof: like the source's, its gates depend on `T` only through
the entries inside the window they belong to.

* **Layout** (`Gate`, `gateCount`, `Gate.set`, `Gate.op`): the gates, their number and their
  operations depend only on `p` and the number `t` of sets.
* **Locality** (`value_congr`): the function computed by a gate of window `i` depends only on `T`
  restricted to `A i`; the other gates compute fixed functions. With the layout, these are the two
  facts the counting argument uses; the program itself depends on `T`, and `exists_program`
  realizes it with the layout's operations.
* **Exact cost** (`ecomplexity_template`): computing all the gate functions costs exactly their
  number of distinct non-input functions, over any De Morgan basis.
* **Completeness** (`ecomplexity_append_le`): with a cover `C` of the inputs by sets, the template
  followed by `T` costs at most that number plus `#C - 1`.

## Main definitions

* `Cslib.MultiMCSP.Window.Gate`, `Cslib.MultiMCSP.Window.gateCount`,
  `Cslib.MultiMCSP.Window.Gate.equivFin`: the gates of a template and their numbering.
* `Cslib.MultiMCSP.Window.Gate.set`, `Cslib.MultiMCSP.Window.Gate.op`: the window a gate belongs
  to and its operation.
* `Cslib.MultiMCSP.Window.value`: the function each gate computes, in closed form.
* `Cslib.MultiMCSP.Window.template`: all gate functions, as a multi-output function.
* `Cslib.MultiMCSP.Window.tableFun`: the function whose truth table is `T`.

## Main results

* `Cslib.MultiMCSP.Window.exists_program`: a program computing the template, with the layout's
  operations.
* `Cslib.MultiMCSP.Window.value_congr`: locality of the gate functions.
* `Cslib.MultiMCSP.Window.value_window_last`: the last gate of window `i` computes `T` on `A i`.
* `Cslib.MultiMCSP.Window.ecomplexity_template`: the template costs its number of distinct
  non-input gate functions.
* `Cslib.MultiMCSP.Window.ecomplexityGiven_tableFun_le`,
  `Cslib.MultiMCSP.Window.ecomplexity_append_le`: completeness.

## References

* [R. Ilango, B. Loff, I. C. Oliveira, *NP-Hardness of Circuit Minimization for Multi-Output
  Functions*][IlangoLoffOliveira2020]
-/

public section

namespace Cslib.MultiMCSP.Window

open Circuits Finset

/-- The gates of a window template on `p` inputs with `t` windows: a negation of each input, a
constant-zero gate, a prefix conjunction `grid y k` of the first `k + 1` literals of each input `y`,
and a gate `window i y` of window `i` for each input `y`. -/
inductive Gate (p t : ℕ) where
  /-- The negation of input `i`. -/
  | neg (i : Fin p)
  /-- The constant zero. -/
  | zero
  /-- Whether the first `k + 1` input bits agree with those of `y`. -/
  | grid (y : Fin (2 ^ p)) (k : Fin p)
  /-- Whether the input is at most `y`, lies in window `i` and is accepted by the table. -/
  | window (i : Fin t) (y : Fin (2 ^ p))
  deriving DecidableEq

variable {p t : ℕ}

namespace Gate

/-- The gates as a sum of their four kinds. -/
private def equivSum (p t : ℕ) :
    Gate p t ≃ Fin p ⊕ (Unit ⊕ ((Fin (2 ^ p) × Fin p) ⊕ (Fin t × Fin (2 ^ p)))) where
  toFun
    | neg i => .inl i
    | zero => .inr (.inl ())
    | grid y k => .inr (.inr (.inl (y, k)))
    | window i y => .inr (.inr (.inr (i, y)))
  invFun
    | .inl i => neg i
    | .inr (.inl _) => zero
    | .inr (.inr (.inl (y, k))) => grid y k
    | .inr (.inr (.inr (i, y))) => window i y
  left_inv κ := by cases κ <;> rfl
  right_inv s := by rcases s with i | _ | ⟨y, k⟩ | ⟨i, y⟩ <;> rfl

end Gate

/-- The number of gates of a window template: `p` negations, one zero, `2^p · p` prefix
conjunctions and `t · 2^p` window gates. -/
def gateCount (p t : ℕ) : ℕ :=
  p + (1 + (2 ^ p * p + t * 2 ^ p))

theorem gateCount_eq (p t : ℕ) : gateCount p t = p + (1 + (2 ^ p * p + t * 2 ^ p)) :=
  by rfl

/-- The numbering of the gates: negations, then zero, then the prefix conjunctions of each input in
turn, then the gates of each window in turn. -/
def Gate.equivFin (p t : ℕ) : Gate p t ≃ Fin (gateCount p t) :=
  (Gate.equivSum p t).trans <|
    (Equiv.sumCongr (Equiv.refl _) <|
      Equiv.sumCongr (finOneEquiv.symm) (Equiv.sumCongr finProdFinEquiv finProdFinEquiv |>.trans
        finSumFinEquiv) |>.trans finSumFinEquiv) |>.trans finSumFinEquiv

@[simp] theorem Gate.val_equivFin_neg (i : Fin p) :
    (Gate.equivFin p t (.neg i) : ℕ) = i :=
  by rfl

@[simp] theorem Gate.val_equivFin_zero : (Gate.equivFin p t .zero : ℕ) = p :=
  by rfl

@[simp] theorem Gate.val_equivFin_grid (y : Fin (2 ^ p)) (k : Fin p) :
    (Gate.equivFin p t (.grid y k) : ℕ) = p + (1 + (k + p * y)) :=
  by rfl

@[simp] theorem Gate.val_equivFin_window (i : Fin t) (y : Fin (2 ^ p)) :
    (Gate.equivFin p t (.window i y) : ℕ) = p + (1 + (2 ^ p * p + (y + 2 ^ p * i))) :=
  by rfl

/-- The window a gate belongs to: `i` for the gates `window i y`, none for the shared gates. -/
def Gate.set : Gate p t → Option (Fin t)
  | window i _ => some i
  | _ => none

@[simp] theorem Gate.set_window (i : Fin t) (y : Fin (2 ^ p)) :
    (Gate.window i y : Gate p t).set = some i :=
  by rfl

/-- The operation of each gate: NOT for the negations, AND for zero and the prefix conjunctions,
OR for the window gates. -/
def Gate.op : Gate p t → Boolean.DeMorgan.Op
  | neg _ => .not
  | zero | grid _ _ => .and
  | window _ _ => .or

/-- The function each gate computes, in closed form; `A i` is window `i` and `T` the truth table. -/
def value (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) :
    Gate p t → (Fin p → Bool) → Bool
  | .neg i, x => !x i
  | .zero, _ => false
  | .grid y k, x => decide (∀ b : Fin p, b ≤ k → x b = (y : ℕ).testBit b)
  | .window i y, x =>
    decide (BitString.equivFin p x ≤ y ∧ BitString.equivFin p x ∈ A i ∧
      T (BitString.equivFin p x) = true)

@[simp] theorem value_neg (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) (i : Fin p)
    (x : Fin p → Bool) : value A T (.neg i) x = !x i :=
  by rfl

@[simp] theorem value_zero (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (x : Fin p → Bool) : value A T .zero x = false :=
  by rfl

theorem value_grid (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) (y : Fin (2 ^ p))
    (k : Fin p) (x : Fin p → Bool) :
    value A T (.grid y k) x = decide (∀ b : Fin p, b ≤ k → x b = (y : ℕ).testBit b) :=
  by rfl

theorem value_window (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) (i : Fin t)
    (y : Fin (2 ^ p)) (x : Fin p → Bool) :
    value A T (.window i y) x = decide (BitString.equivFin p x ≤ y ∧
      BitString.equivFin p x ∈ A i ∧ T (BitString.equivFin p x) = true) :=
  by rfl

/-- The window template: the functions of all gates, in the order of `Gate.equivFin`. -/
def template (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) :
    (Fin p → Bool) → Fin (gateCount p t) → Bool :=
  fun x j => value A T ((Gate.equivFin p t).symm j) x

theorem template_apply (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (x : Fin p → Bool) (j : Fin (gateCount p t)) :
    template A T x j = value A T ((Gate.equivFin p t).symm j) x := by rfl

@[simp] theorem template_equivFin (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (κ : Gate p t) (x : Fin p → Bool) : template A T x (Gate.equivFin p t κ) = value A T κ x := by
  simp only [template, Equiv.symm_apply_apply]

/-- The function whose truth table is `T`, inputs read in the order of `BitString.equivFin`. -/
def tableFun (T : Fin (2 ^ p) → Bool) : (Fin p → Bool) → Bool :=
  fun x => T (BitString.equivFin p x)

@[simp] theorem tableFun_apply (T : Fin (2 ^ p) → Bool) (x : Fin p → Bool) :
    tableFun T x = T (BitString.equivFin p x) := by rfl

/-! ### Locality -/

/-- **Locality.** A gate of window `i` computes a function that depends on `T` only through its
entries in `A i`; the other gates compute the same function for every `T`. -/
theorem value_congr (A : Fin t → Finset (Fin (2 ^ p))) {T T' : Fin (2 ^ p) → Bool} (κ : Gate p t)
    (h : ∀ i, κ.set = some i → ∀ y ∈ A i, T y = T' y) : value A T κ = value A T' κ := by
  cases κ with
  | neg i => rfl
  | zero => rfl
  | grid y k => rfl
  | window i y =>
    funext x
    simp only [value_window]
    refine decide_eq_decide.mpr (and_congr_right fun _ => ?_)
    exact ⟨fun ⟨hm, hT⟩ => ⟨hm, (h i rfl _ hm).symm.trans hT⟩,
      fun ⟨hm, hT⟩ => ⟨hm, (h i rfl _ hm).trans hT⟩⟩

/-- The last input `2^p - 1`, whose window gates compute the windows of `T`. -/
def lastIdx (p : ℕ) : Fin (2 ^ p) :=
  ⟨2 ^ p - 1, Nat.sub_lt (Nat.two_pow_pos p) Nat.one_pos⟩

/-- **The window identity.** The last gate of window `i` computes `T` restricted to `A i`. -/
theorem value_window_last (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) (i : Fin t)
    (x : Fin p → Bool) :
    value A T (.window i (lastIdx p)) x =
      decide (BitString.equivFin p x ∈ A i ∧ T (BitString.equivFin p x) = true) := by
  have hle : BitString.equivFin p x ≤ lastIdx p := by
    rw [Fin.le_iff_val_le_val]
    simp only [lastIdx]
    have := (BitString.equivFin p x).isLt
    omega
  rw [value_window]
  exact decide_eq_decide.mpr (and_iff_right hle)

/-! ### The program -/

section Lines

open Boolean

/-- The wire of a gate. -/
private abbrev gateWire (κ : Gate p t) : Wire p (gateCount p t) :=
  .gate (Gate.equivFin p t κ)

private def notLine (w : Wire p (gateCount p t)) : Line DeMorgan.signature p (gateCount p t) :=
  ⟨.not, fun _ => w⟩

private def andLine (w₁ w₂ : Wire p (gateCount p t)) :
    Line DeMorgan.signature p (gateCount p t) :=
  ⟨.and, fun a => if a.val = 0 then w₁ else w₂⟩

private def orLine (w₁ w₂ : Wire p (gateCount p t)) :
    Line DeMorgan.signature p (gateCount p t) :=
  ⟨.or, fun a => if a.val = 0 then w₁ else w₂⟩

private theorem eval_notLine (w : Wire p (gateCount p t)) (x : Fin p → Bool)
    (v : Fin (gateCount p t) → Bool) :
    (notLine w).eval DeMorgan.interpretation x v = !Wire.elim x v w :=
  rfl

private theorem eval_andLine (w₁ w₂ : Wire p (gateCount p t)) (x : Fin p → Bool)
    (v : Fin (gateCount p t) → Bool) :
    (andLine w₁ w₂).eval DeMorgan.interpretation x v = (Wire.elim x v w₁ && Wire.elim x v w₂) :=
  rfl

private theorem eval_orLine (w₁ w₂ : Wire p (gateCount p t)) (x : Fin p → Bool)
    (v : Fin (gateCount p t) → Bool) :
    (orLine w₁ w₂).eval DeMorgan.interpretation x v = (Wire.elim x v w₁ || Wire.elim x v w₂) :=
  rfl

/-- The literal of bit `b` that is true when the input agrees with `y` there. -/
private def litWire (y : Fin (2 ^ p)) (b : Fin p) : Wire p (gateCount p t) :=
  if (y : ℕ).testBit b then .input b else gateWire (.neg b)

/-- The last input bit. -/
private def lastBit (p : ℕ) [NeZero p] : Fin p :=
  ⟨p - 1, Nat.sub_lt (Nat.pos_of_ne_zero (NeZero.ne p)) Nat.one_pos⟩

variable [NeZero p]

/-- The line of each gate. -/
private def line (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) (κ : Gate p t) :
    Line DeMorgan.signature p (gateCount p t) :=
  match κ with
  | .neg i => notLine (.input i)
  | .zero => andLine (.input 0) (gateWire (.neg 0))
  | .grid y k =>
    andLine (if hk : (k : ℕ) = 0 then litWire y k else gateWire (.grid y ⟨k - 1, by omega⟩))
      (litWire y k)
  | .window i y =>
    orLine (if hy : (y : ℕ) = 0 then gateWire .zero else gateWire (.window i ⟨y - 1, by omega⟩))
      (if y ∈ A i ∧ T y = true then gateWire (.grid y (lastBit p)) else gateWire .zero)

private theorem line_op (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (κ : Gate p t) : (line A T κ).op = κ.op := by
  cases κ <;> rfl

omit [NeZero p] in
private theorem elim_gateWire (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (x : Fin p → Bool) (κ : Gate p t) :
    Wire.elim x (template A T x) (gateWire κ) = value A T κ x := by
  simp only [gateWire, Wire.elim_gate, template_equivFin]

omit [NeZero p] in
private theorem elim_litWire (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (x : Fin p → Bool) (y : Fin (2 ^ p)) (b : Fin p) :
    Wire.elim x (template A T x) (litWire y b) = decide (x b = (y : ℕ).testBit b) := by
  unfold litWire
  split <;> rename_i h
  · simp [h]
  · rw [elim_gateWire]
    simp [h]

/-- The last prefix conjunction of `y` recognizes `y`. -/
private theorem value_grid_last (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (y : Fin (2 ^ p)) (x : Fin p → Bool) :
    value A T (.grid y (lastBit p)) x = decide (BitString.equivFin p x = y) := by
  rw [value_grid]
  refine decide_eq_decide.mpr ⟨fun h => ?_, fun h b _ => ?_⟩
  · rw [← Equiv.eq_symm_apply]
    funext b
    rw [BitString.equivFin_symm_apply]
    refine h b ?_
    rw [Fin.le_iff_val_le_val]
    simp only [lastBit]
    omega
  · subst h
    have hb := BitString.equivFin_symm_apply (BitString.equivFin p x) b
    rw [Equiv.symm_apply_apply] at hb
    exact hb

private theorem value_eq_eval (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (x : Fin p → Bool) (κ : Gate p t) :
    value A T κ x = (line A T κ).eval DeMorgan.interpretation x (template A T x) := by
  cases κ with
  | neg i => rfl
  | zero =>
    simp only [line, eval_andLine, Wire.elim_input, elim_gateWire, value_neg, value_zero]
    cases x 0 <;> rfl
  | grid y k =>
    simp only [line, eval_andLine, elim_litWire]
    by_cases hk : (k : ℕ) = 0
    · rw [dite_eq_left hk, elim_litWire, Bool.and_self, value_grid]
      refine decide_eq_decide.mpr ⟨fun h => h k le_rfl, fun h b hb => ?_⟩
      obtain rfl : b = k := Fin.ext (by rw [Fin.le_iff_val_le_val] at hb; omega)
      exact h
    · rw [dite_eq_right hk, elim_gateWire, value_grid, value_grid, ← Bool.decide_and]
      refine decide_eq_decide.mpr
        ⟨fun h => ⟨fun b hb => h b ?_, h k le_rfl⟩, fun ⟨h, hk'⟩ b hb => ?_⟩
      · rw [Fin.le_iff_val_le_val] at hb ⊢
        simp only at hb
        omega
      · rcases (Fin.le_iff_val_le_val.mp hb).lt_or_eq with hlt | heq
        · exact h b (by rw [Fin.le_iff_val_le_val]; simp only; omega)
        · obtain rfl : b = k := Fin.ext heq
          exact hk'
  | window i y =>
    simp only [line, eval_orLine]
    have hsel : Wire.elim x (template A T x)
        (if y ∈ A i ∧ T y = true then gateWire (.grid y (lastBit p)) else gateWire .zero) =
        decide (BitString.equivFin p x = y ∧ y ∈ A i ∧ T y = true) := by
      split <;> rename_i hy
      · rw [elim_gateWire, value_grid_last]
        exact decide_eq_decide.mpr (by tauto)
      · rw [elim_gateWire, value_zero]
        exact (decide_eq_false fun h => hy h.2).symm
    rw [hsel, value_window]
    split <;> rename_i hy0
    · rw [elim_gateWire, value_zero, Bool.false_or]
      refine decide_eq_decide.mpr ⟨fun ⟨hle, hm, hT⟩ => ?_, fun ⟨he, hm, hT⟩ => ?_⟩
      · have he : BitString.equivFin p x = y :=
          Fin.ext (by rw [Fin.le_iff_val_le_val] at hle; omega)
        exact ⟨he, he ▸ hm, he ▸ hT⟩
      · exact ⟨he.le, he ▸ hm, he ▸ hT⟩
    · rw [elim_gateWire, value_window, ← Bool.decide_or]
      refine decide_eq_decide.mpr ⟨fun ⟨hle, hm, hT⟩ => ?_, ?_⟩
      · rcases (Fin.le_iff_val_le_val.mp hle).lt_or_eq with hlt | heq
        · exact .inl ⟨by rw [Fin.le_iff_val_le_val]; simp only; omega, hm, hT⟩
        · have he : BitString.equivFin p x = y := Fin.ext heq
          exact .inr ⟨he, he ▸ hm, he ▸ hT⟩
      · rintro (⟨hle, hm, hT⟩ | ⟨he, hm, hT⟩)
        · exact ⟨by rw [Fin.le_iff_val_le_val] at hle ⊢; simp only at hle; omega, hm, hT⟩
        · exact ⟨he.le, he ▸ hm, he ▸ hT⟩

/-- A wire is *early* for gate `κ` when it is an input or a gate numbered before `κ`. -/
private def Early (κ : Gate p t) (w : Wire p (gateCount p t)) : Prop :=
  ∀ s, w = .gate s → s < Gate.equivFin p t κ

omit [NeZero p] in
private theorem early_input (κ : Gate p t) (i : Fin p) : Early κ (.input i) := by
  intro s h
  cases h

omit [NeZero p] in
private theorem early_gateWire {κ κ' : Gate p t}
    (h : (Gate.equivFin p t κ' : ℕ) < Gate.equivFin p t κ) : Early κ (gateWire κ') := by
  rintro s hs
  cases hs
  exact h

omit [NeZero p] in
private theorem early_litWire (κ : Gate p t) (y : Fin (2 ^ p)) (b : Fin p)
    (h : p ≤ (Gate.equivFin p t κ : ℕ)) : Early κ (litWire y b) := by
  unfold litWire
  split
  · exact early_input κ b
  · exact early_gateWire (by simp only [Gate.val_equivFin_neg]; omega)

omit [NeZero p] in
private theorem early_ite {κ : Gate p t} {c : Prop} [Decidable c] {w₁ w₂ : Wire p (gateCount p t)}
    (h₁ : Early κ w₁) (h₂ : Early κ w₂) : Early κ (if c then w₁ else w₂) := by
  split
  · exact h₁
  · exact h₂

omit [NeZero p] in
private theorem early_dite {κ : Gate p t} {c : Prop} [Decidable c] {w₁ : c → Wire p (gateCount p t)}
    {w₂ : ¬c → Wire p (gateCount p t)} (h₁ : ∀ h, Early κ (w₁ h)) (h₂ : ∀ h, Early κ (w₂ h)) :
    Early κ (if h : c then w₁ h else w₂ h) := by
  split
  · exact h₁ _
  · exact h₂ _

private theorem line_early (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (κ : Gate p t) (a) : Early κ ((line A T κ).wires a) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  cases κ with
  | neg i => exact early_input _ i
  | zero =>
    change Early _ (if a.val = 0 then _ else _)
    exact early_ite (early_input _ _)
      (early_gateWire (by simp only [Gate.val_equivFin_neg, Gate.val_equivFin_zero]; simpa))
  | grid y k =>
    have hlit : Early (Gate.grid y k : Gate p t) (litWire y k) :=
      early_litWire _ y k (by simp only [Gate.val_equivFin_grid]; omega)
    change Early _ (if a.val = 0 then _ else _)
    refine early_ite (early_dite (fun _ => hlit) fun hk => early_gateWire ?_) hlit
    simp only [Gate.val_equivFin_grid]
    omega
  | window i y =>
    have hy := y.isLt
    have hgrid : p * (y : ℕ) + p ≤ 2 ^ p * p := by
      rw [Nat.mul_comm (2 ^ p), ← Nat.mul_succ]
      exact Nat.mul_le_mul_left p hy
    change Early _ (if a.val = 0 then _ else _)
    refine early_ite (early_dite (fun _ => early_gateWire ?_) fun hy0 => early_gateWire ?_)
      (early_ite (early_gateWire ?_) (early_gateWire ?_))
    · simp only [Gate.val_equivFin_zero, Gate.val_equivFin_window]
      omega
    · simp only [Gate.val_equivFin_window]
      omega
    · simp only [Gate.val_equivFin_grid, Gate.val_equivFin_window, lastBit]
      omega
    · simp only [Gate.val_equivFin_zero, Gate.val_equivFin_window]
      omega

/-- **The template as a program.** For `p ≥ 1`, a program over the constant-free De Morgan basis
with one gate for each gate of the layout computes the window template, and its gate
`Gate.equivFin p t κ` performs the operation `κ.op`. -/
theorem exists_program (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool) :
    ∃ P : Program DeMorgan.signature p (gateCount p t),
      (∀ x, P.eval DeMorgan.interpretation x = template A T x) ∧
        ∀ κ, (P.lines (Gate.equivFin p t κ)).op = κ.op := by
  obtain ⟨P, hP, hop⟩ := Program.exists_eval_eq_of_lines DeMorgan.interpretation
    (fun j => line A T ((Gate.equivFin p t).symm j)) (template A T)
    (fun j a s hs => by
      simpa only [Equiv.apply_symm_apply] using line_early A T _ a s hs)
    (fun x j => value_eq_eval A T x _)
  refine ⟨P, hP, fun κ => ?_⟩
  rw [hop, Equiv.symm_apply_apply, line_op]

end Lines

/-! ### Cost -/

universe v

variable {σ : Signature.{v}} {I : Interpretation σ Bool} [Boolean.DeMorganBasis I]

/-- **Exact cost of the template.** For `p ≥ 1`, over any De Morgan basis, computing all gate
functions of a window template costs exactly the number of distinct ones that are not input
projections. This is the analogue for this template of [IlangoLoffOliveira2020, Proposition 14,
pp. 22:21–22:22]. -/
theorem ecomplexity_template [NeZero p] (A : Fin t → Finset (Fin (2 ^ p)))
    (T : Fin (2 ^ p) → Bool) :
    ecomplexity I (template A T) = #(nonInputComponents (template A T)) := by
  obtain ⟨P, hP, -⟩ := exists_program A T
  have heval : (P.mapOp (Boolean.DeMorganBasis.hom I)).eval I = template A T :=
    funext fun x => (Program.eval_mapOp (I := Boolean.DeMorgan.interpretation) P x).trans (hP x)
  rw [← heval]
  exact ecomplexity_eval_eq_card_nonInputComponents I _

/-- An OR of `#C` input coordinates costs `#C - 1` gates of the constant-free basis. -/
private theorem synthesis_or {n : ℕ} {C : Finset (Fin n)} (hC : C.Nonempty) :
    Synthesis Boolean.DeMorgan.interpretation (inputs n) {fun x => decide (∃ a ∈ C, x a = true)}
      (#C - 1) := by
  induction hC using Finset.Nonempty.cons_induction with
  | singleton a =>
    have hf : (fun x : Fin n → Bool => decide (∃ b ∈ ({a} : Finset (Fin n)), x b = true)) =
        fun x => x a := by
      funext x
      simp
    rw [hf]
    exact Synthesis.of_mem ⟨a, rfl⟩
  | cons a s ha hs ih =>
    have hbin := Synthesis.binary (Synthesis.of_mem (s := inputs n) ⟨a, rfl⟩) ih
      Boolean.DeMorgan.Op.or
    have hf : (fun x : Fin n → Bool =>
        Boolean.DeMorgan.interpretation .or fun i => if i.val = 0 then x a
          else decide (∃ b ∈ s, x b = true)) =
        fun x => decide (∃ b ∈ Finset.cons a s ha, x b = true) := by
      funext x
      simp only [Boolean.DeMorgan.interpretation_or, Fin.isValue, Fin.val_zero, ite_true,
        Fin.val_one, one_ne_zero, ite_false, Finset.mem_cons, exists_eq_or_imp, Bool.decide_or,
        Bool.decide_eq_true]
    rw [hf] at hbin
    refine hbin.mono le_rfl le_rfl ?_
    rw [Finset.card_cons]
    have := hs.card_pos
    omega

/-- **The table given the template.** If the windows `C` cover every input, then `T` costs at
most `#C - 1` gates given the template: it is the OR of the last gates of those windows. This is
the analogue for this template of [IlangoLoffOliveira2020, Lemma 15, p. 22:22], with the sharper
bound `#C - 1`. -/
theorem ecomplexityGiven_tableFun_le (A : Fin t → Finset (Fin (2 ^ p))) (T : Fin (2 ^ p) → Bool)
    (C : Finset (Fin t)) (hC : ∀ y, ∃ i ∈ C, y ∈ A i) :
    ecomplexityGiven I (single (tableFun T)) (template A T) ≤ ((#C - 1 : ℕ) : ℕ∞) := by
  -- The input coordinate carrying the last gate of each window.
  let coord (i : Fin t) : Fin (p + gateCount p t) :=
    Fin.natAdd p (Gate.equivFin p t (.window i (lastIdx p)))
  have hinj : Function.Injective coord := fun i j h => by
    simpa [coord, Fin.natAdd_inj] using h
  have hne : (C.image coord).Nonempty := by
    obtain ⟨i, hi, -⟩ := hC 0
    exact ⟨_, Finset.mem_image_of_mem coord hi⟩
  obtain ⟨c, hc, hsize⟩ := (synthesis_or hne).exists_circuit
  refine (ecomplexityGiven_le_of_eval _ _ (c.mapOp (Boolean.DeMorganBasis.hom I))
    fun x => ?_).trans ?_
  · rw [Circuit.eval_mapOp (I := Boolean.DeMorgan.interpretation), hc]
    funext o
    simp only [single_apply, tableFun, Finset.mem_image, exists_exists_and_eq_and, coord,
      Fin.append_right, template_equivFin, value_window_last, decide_eq_true_eq]
    obtain ⟨i, hi, hy⟩ := hC (BitString.equivFin p x)
    cases hT : T (BitString.equivFin p x)
    · simp
    · simpa [hT] using ⟨i, hi, hy⟩
  · rw [Circuit.size_mapOp]
    exact_mod_cast hsize.trans (by rw [Finset.card_image_of_injective _ hinj])

/-- **Completeness.** For `p ≥ 1`, if the windows `C` cover every input, the template followed by
`T` costs at most the number of distinct non-input gate functions plus `#C - 1`. This is the
analogue for this template of [IlangoLoffOliveira2020, Lemma 15, p. 22:22]. -/
theorem ecomplexity_append_le [NeZero p] (A : Fin t → Finset (Fin (2 ^ p)))
    (T : Fin (2 ^ p) → Bool) (C : Finset (Fin t)) (hC : ∀ y, ∃ i ∈ C, y ∈ A i) :
    ecomplexity I (fun x => Fin.append (template A T x) (single (tableFun T) x)) ≤
      ((#(nonInputComponents (template A T)) + (#C - 1) : ℕ) : ℕ∞) := by
  refine (ecomplexity_append_le_add_ecomplexityGiven _ _).trans ?_
  rw [ecomplexity_template, Nat.cast_add]
  exact add_le_add le_rfl (ecomplexityGiven_tableFun_le A T C hC)

end Cslib.MultiMCSP.Window
