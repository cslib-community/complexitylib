/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation
public import Complexity.Computability.TreeEval.Ary.Descending

/-!
# HPV block computation as an implicit Tree Evaluation instance

Each interval has one control dependency and three window dependencies per work tape. Their
indices strictly decrease. The existing `Ary.Tree` unfolds those dependencies, with constant
source gates padding shorter paths. Its value is exactly the encoded functional block value.

The supplied codec must decode every encoded value correctly. A guard maps every word outside
its image to the distinct FAIL value, so the gate is defined on all bit strings. Codec size,
native gate computation, input access and space certification are separate obligations.

## Main results

* `Turing.MultiTapePTM.BlockComputation.eval_tree`: the unfolded tree preserves the coded value.
* `Turing.MultiTapePTM.BlockComputation.nodeAt_tree`: every path has the implicit label.
* `Turing.MultiTapePTM.BlockComputation.eval_tree_final_eq_some_iff`: success validates the
  complete movement schedule.
* `Turing.MultiTapePTM.BlockComputation.eval_tree_final_eq_fail_iff`: wrong guesses return FAIL.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation

open Cslib.TreeEval

variable {k q b ℓ : ℕ} {State : Type}

/-- A checked decoder returns FAIL rather than treating an invalid word as a valid interval view. -/
@[expose] def decodeChecked (encode : Option (View k State b) → Fin ℓ → Bool)
    (decode : (Fin ℓ → Bool) → Option (View k State b)) (w : Fin ℓ → Bool) :
    Option (View k State b) :=
  if ∀ i, encode (decode w) i = w i then decode w else none

/-- Valid codewords are unaffected by the validity guard. -/
theorem decodeChecked_encode (encode : Option (View k State b) → Fin ℓ → Bool)
    (decode : (Fin ℓ → Bool) → Option (View k State b))
    (hdecode : Function.LeftInverse decode encode) (v : Option (View k State b)) :
    decodeChecked encode decode (encode v) = v := by
  simp [decodeChecked, hdecode v]

/-- Every word outside the encoding's image is decoded as FAIL. -/
theorem decodeChecked_invalid (encode : Option (View k State b) → Fin ℓ → Bool)
    (decode : (Fin ℓ → Bool) → Option (View k State b)) (w : Fin ℓ → Bool)
    (hw : ∀ v, encode v ≠ w) : decodeChecked encode decode w = none := by
  have hnot : ¬ ∀ i, encode (decode w) i = w i :=
    fun h => hw (decode w) (funext h)
  simp [decodeChecked, hnot]

variable (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ)
  (σ : Schedule k q)

/-- Child zero is the preceding interval. The remaining children are the last window providers,
numbered by work tape and window entry; missing providers are the initial source. -/
@[expose] def child : ℕ → Fin (k * 3 + 1) → ℕ
  | 0, _ => 0
  | n + 1, j =>
    if hi : n < q then
      Fin.cases n (fun p =>
        let hd := finProdFinEquiv.symm p
        match lastBefore (InWindow σ hd.1 (portBlock σ ⟨n, hi⟩ hd.1 hd.2)) ⟨n, hi⟩ with
        | none => 0
        | some i => i + 1) j
    else 0

/-- Every dependency of a positive index is strictly earlier, including total out-of-range cases. -/
theorem child_lt (i : ℕ) (hi : 0 < i) (j : Fin (k * 3 + 1)) : child σ i j < i := by
  cases i with
  | zero => omega
  | succ n =>
    simp only [child]
    split_ifs with hn
    · refine Fin.cases ?_ (fun p => ?_) j
      · simp only [Fin.cases_zero]
        omega
      · simp only [Fin.cases_succ]
        split
        next => omega
        next i hp =>
          have hprev := (lastBefore_eq_some_iff.mp hp).1
          change (i : ℕ) < n at hprev
          omega
    · omega

/-- The unencoded interval gate, with a source gate at zero and FAIL beyond the horizon. -/
@[expose] noncomputable def intervalGate :
    ℕ → (Fin (k * 3 + 1) → Option (View k State b)) → Option (View k State b)
  | 0, _ => some (initialView machine b)
  | n + 1, children =>
    if hi : n < q then
      gate machine input b σ ⟨n, hi⟩ (children 0)
        (fun h d => children (Fin.succ (finProdFinEquiv (h, d))))
    else none

variable (encode : Option (View k State b) → Fin ℓ → Bool)
  (decode : (Fin ℓ → Bool) → Option (View k State b))

/-- Decode all children, run the local interval gate, and encode its result. -/
@[expose] noncomputable def codeGate (i : ℕ) : Ary.Gate (k * 3 + 1) ℓ := fun children =>
  encode (intervalGate machine input b σ i (fun j => decodeChecked encode decode (children j)))

/-- The complete uniform-height Tree Evaluation instance, unfolded without a new tree model. -/
@[expose] noncomputable def tree (height root : ℕ) : Ary.Tree (k * 3 + 1) ℓ height :=
  Ary.Descending.tree (encode (some (initialView machine b))) (child σ)
    (codeGate machine input b σ encode decode) height root

private theorem intervalGate_value {n : ℕ} (hn : n < q) :
    intervalGate machine input b σ (n + 1)
      (fun j => value machine input b σ (child σ (n + 1) j)) =
        value machine input b σ (n + 1) := by
  rw [value, dite_eq_left hn]
  simp only [intervalGate, child, dite_eq_left hn, Fin.cases_zero, Fin.cases_succ,
    Equiv.symm_apply_apply]
  congr 2
  funext h d
  split
  next hfirst =>
    rw [value]
    split
    next => rfl
    next j hsecond =>
      have hc := hfirst.symm.trans hsecond
      cases hc
  next j hfirst =>
    split
    next hsecond =>
      have hc := hsecond.symm.trans hfirst
      cases hc
    next j' hsecond =>
      have heq : j = j' := Option.some.inj (hfirst.symm.trans hsecond)
      subst j'
      rfl

variable (hdecode : Function.LeftInverse decode encode)

include hdecode

private theorem descending_value_eq {n : ℕ} (hn : n ≤ q) :
    Ary.Descending.value (encode (some (initialView machine b))) (child σ)
      (codeGate machine input b σ encode decode) (child_lt σ) n =
        encode (value machine input b σ n) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rw [Ary.Descending.value, value]
    | succ n =>
      rw [Ary.Descending.value]
      have hchildren :
          (fun j => decodeChecked encode decode
            (Ary.Descending.value (encode (some (initialView machine b))) (child σ)
              (codeGate machine input b σ encode decode) (child_lt σ)
              (child σ (n + 1) j))) =
            fun j => value machine input b σ (child σ (n + 1) j) := by
        funext j
        have hj := child_lt σ (n + 1) (by omega) j
        rw [ih _ hj (by omega), decodeChecked_encode encode decode hdecode]
      change encode (intervalGate machine input b σ (n + 1) _) = _
      rw [hchildren, intervalGate_value machine input b σ (by omega)]

/-- Unfolding an interval computation preserves its encoded value. -/
theorem eval_tree {height root : ℕ} (hroot : root ≤ q) (hheight : root ≤ height) :
    (tree machine input b σ encode decode height root).eval =
      encode (value machine input b σ root) := by
  rw [tree, Ary.Descending.eval_tree _ _ _ (child_lt σ) hheight]
  exact descending_value_eq machine input b σ encode decode hdecode hroot

omit hdecode in
/-- The implicit node lookup follows dependency indices along the path. -/
theorem nodeAt_tree (height root : ℕ) (P : List (Fin (k * 3 + 1))) :
    (tree machine input b σ encode decode height root).nodeAt P =
      Ary.Descending.lookup (encode (some (initialView machine b))) (child σ)
        (codeGate machine input b σ encode decode) height root P :=
  Ary.Descending.nodeAt_tree _ _ _ _ _ _

variable [NeZero b]

/-- The final tree returns the encoded true view exactly for the true complete movement guess. -/
theorem eval_tree_final_eq_some_iff (v : View k State b) :
    (tree machine input b σ encode decode q q).eval = encode (some v) ↔
      actualSchedule machine input b (q := q) = σ ∧ v = trueView machine input b σ q := by
  rw [eval_tree machine input b σ encode decode hdecode le_rfl le_rfl]
  rw [hdecode.injective.eq_iff]
  exact value_final_eq_some_iff machine input b σ v

/-- A wrong movement guess evaluates to the encoded FAIL value. -/
theorem eval_tree_final_eq_fail_iff :
    (tree machine input b σ encode decode q q).eval = encode none ↔
      actualSchedule machine input b (q := q) ≠ σ := by
  rw [eval_tree machine input b σ encode decode hdecode le_rfl le_rfl]
  rw [hdecode.injective.eq_iff]
  exact value_final_eq_none_iff machine input b σ

end Turing.MultiTapePTM.BlockComputation
