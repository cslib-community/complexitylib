/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Primitives.Garbling.BinaryToOneHotObliviousness

/-! # Garbled one-hot conversion: checked instances

The one-hot product on a concrete table; the gadget over one-bit labels `ZMod 2`, evaluated on
every input with a toy hash; the correctness and table-product theorems for these labels; the
query bound of the reduction; and the obliviousness theorem with step-separated tweaks, which checks
that its tweak hypothesis is satisfiable. -/

@[expose] public section

namespace CslibFrontierTests.GarblingOneHot

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Crypto.Garbling.BinaryToOneHot

/-- A two-row table with two output bits: row `0` is `(true, false)` and row `1` is
`(true, true)`. -/
def tab : Fin 2 → Fin 2 → Bool := ![![true, false], ![true, true]]

-- The product with a one-hot vector reads the selected row, by computation.
example : tableMulBits tab (oneHot 0) = tab 0 ∧ tableMulBits tab (oneHot 1) = tab 1 := by
  decide

-- Additivity of `bitOffset` in characteristic two is choice-free.
/--
info: 'Cslib.Crypto.Garbling.bitOffset_add' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms bitOffset_add

/-- A toy hash on one-bit labels; it ignores the tweak and is not correlation robust. -/
def toyH (g : ZMod 2) (_ : Unit) : ZMod 2 := g + 1

/-- The only tweak. -/
def toyTw (t : ℕ) (_ : Fin (t + 1) → Bool) : Unit := ()

-- With two input bits and one ciphertext, the evaluator obtains the labels of the one-hot vector
-- of its input on every input and every choice of zero-labels and offset, by computation.
example : ∀ (Δ : ZMod 2) (X : Fin 2 → ZMod 2) (x : Fin 2 → Bool) (j : Fin 2 → Bool),
    evaluate toyH toyTw 1 x (fun t => X t + bitOffset Δ (x t)) (garble toyH toyTw Δ 1 X).2 j =
      (garble toyH toyTw Δ 1 X).1 j + bitOffset Δ (oneHot x j) := by
  decide

-- The general correctness theorem specializes to the same statement for three input bits.
example (Δ : ZMod 2) (X : Fin 3 → ZMod 2) (x : Fin 3 → Bool) :
    evaluate toyH toyTw 2 x (fun t => X t + bitOffset Δ (x t)) (garble toyH toyTw Δ 2 X).2 =
      fun j => (garble toyH toyTw Δ 2 X).1 j + bitOffset Δ (oneHot x j) :=
  evaluate_garble toyH toyTw Δ 2 X x

-- The table product of the evaluator's labels is a label of the selected row.
example (Δ : ZMod 2) (X : Fin 2 → ZMod 2) (x : Fin 2 → Bool)
    (T : (Fin 2 → Bool) → Fin 3 → Bool) :
    tableMul T (evaluate toyH toyTw 1 x (fun t => X t + bitOffset Δ (x t))
        (garble toyH toyTw Δ 1 X).2) =
      fun u => tableMul T (garble toyH toyTw Δ 1 X).1 u + bitOffset Δ (T x u) :=
  tableMul_evaluate_garble toyH toyTw Δ 1 X x T

/-- A toy tweakable hash on one-bit labels, with tweaks in `Fin 2`. -/
def toyH2 (g : ZMod 2) (τ : Fin 2) : ZMod 2 := g + (τ.val : ZMod 2)

/-- Step `t` uses tweak `t mod 2` at every position, so the two steps of a three-input gadget use
different tweaks. -/
def stepTw (t : ℕ) (_ : Fin (t + 1) → Bool) : Fin 2 := Fin.ofNat 2 t

theorem stepTw_separated : ∀ t t' (j : Fin (t + 1) → Bool) (j' : Fin (t' + 1) → Bool),
    t < 2 → t' < 2 → stepTw t j = stepTw t' j' → t = t' := by
  intro t t' j j' ht ht' h
  have := congrArg Fin.val h
  simp only [stepTw, Fin.val_ofNat] at this
  omega

-- Each reduction makes one query per doubling step, and at most one query per tweak when the
-- tweaks of distinct steps do not collide.
example (x : Fin 3 → Bool) (D : OneHotView (ZMod 2) 2 → ProbComp Bool) :
    (reduction toyH2 stepTw 2 x D).IsQueryBounded 2 :=
  isQueryBounded_reduction toyH2 stepTw 2 x D

example (x : Fin 3 → Bool) (D : OneHotView (ZMod 2) 2 → ProbComp Bool) :
    CCR.IsTweakUnique (reduction toyH2 stepTw 2 x D) :=
  isTweakUnique_reduction toyH2 stepTw 2 stepTw_separated x D

-- The obliviousness theorem applies with step-separated tweaks and a uniform offset, for every
-- distinguisher. With the toy hash the right side is not small; this checks that `htw` is
-- satisfiable.
example (x : Fin 3 → Bool) (D : OneHotView (ZMod 2) 2 → ProbComp Bool) :
    Game.advantage (realGame toyH2 stepTw id 2 x D) (simGame 2 D) =
      CCR.advantage toyH2 id id (reduction toyH2 stepTw 2 x D) :=
  advantage_realGame_simGame_eq toyH2 stepTw id 2 stepTw_separated x D

end CslibFrontierTests.GarblingOneHot
