/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Protocol
public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Foundations.Data.BitString.Basic
public import Mathlib.Data.Nat.Log

/-!
# The index gadget and lifted search problems

A *search problem* on `n` bits is a relation `R : (Fin n → Bool) → O → Prop`: on input `z`, any
`o` with `R z o` is a correct answer. Composing it with `n` copies of the *index gadget*
`Ind_m : [m] × {0, 1}^m → {0, 1}`, `Ind_m (a, w) = w a`, gives a two-party search problem.
Alice holds pointers `x : Fin n → Fin m`, Bob holds blocks `y : Fin n → Fin m → Bool`, and the
`i`-th input bit is `y i (x i)` (`Communication.Lifting.ind`). The *lifted* problem
`Communication.Lifting.lift R` asks for an answer to `R` on that input
[Göös, Pitassi and Watson][GoosPitassiWatson2018].

A decision tree for `R` gives a protocol for the lifted problem: to query bit `i`, Alice sends
`x i` in `⌈log₂ m⌉` bits and Bob answers with `y i (x i)` (`Communication.Lifting.ofDecisionTree`).
So the communication complexity of the lifted problem is at most `⌈log₂ m⌉ + 1` times the depth of
any decision tree for `R` (`Communication.Lifting.ecomplexity_lift_le`)
[Göös, Pitassi and Watson, (1)][GoosPitassiWatson2018]. The lifting theorem says that this
protocol is optimal up to a constant factor when `m` is a large enough polynomial in `n`.

## Main definitions

* `Cslib.Communication.Lifting.ind`: `n` copies of the index gadget.
* `Cslib.Communication.Lifting.lift`: the lifted search problem.
* `Cslib.Communication.Lifting.ofDecisionTree`: the protocol simulating a decision tree.

## Main results

* `Cslib.Communication.Lifting.run_ofDecisionTree`,
  `Cslib.Communication.Lifting.depth_ofDecisionTree_le`: the simulation is correct and costs
  `⌈log₂ m⌉ + 1` bits per query.
* `Cslib.Communication.Lifting.ecomplexity_lift_le`: the upper bound of the lifting theorem.

## References

* [M. Göös, T. Pitassi and T. Watson, *Deterministic communication vs. partition
  number*][GoosPitassiWatson2018]
* [R. Raz and P. McKenzie, *Separation of the monotone NC hierarchy*][RazMcKenzie1999]
-/

@[expose] public section

namespace Cslib.Communication.Lifting

variable {n m : ℕ} {O : Type*}

/-- `n` copies of the index gadget: the `i`-th bit is the bit of Bob's block `y i` at Alice's
pointer `x i`. -/
def ind (x : Fin n → Fin m) (y : Fin n → Fin m → Bool) : Fin n → Bool :=
  fun i => y i (x i)

@[simp] theorem ind_apply (x : Fin n → Fin m) (y : Fin n → Fin m → Bool) (i : Fin n) :
    ind x y i = y i (x i) :=
  rfl

/-- The search problem `R` lifted by the index gadget: Alice holds `x`, Bob holds `y`, and `o`
is a correct answer when it answers `R` on `ind x y`. -/
def lift (R : (Fin n → Bool) → O → Prop) :
    (Fin n → Fin m) → (Fin n → Fin m → Bool) → O → Prop :=
  fun x y o => R (ind x y) o

/-- The protocol simulating a decision tree: to query bit `i`, Alice sends the binary numeral of
`x i`, and Bob announces `y i (x i)`. -/
def ofDecisionTree :
    DecisionTree (Fin n) O → Protocol (Fin n → Fin m) (Fin n → Fin m → Bool) O
  | .leaf o => .output o
  | .node i t₀ t₁ => Protocol.aliceSend (Nat.clog 2 m) (fun x => BitString.indexBits (x i))
      fun w => .bob (fun y => decide (∃ a, BitString.indexBits a = w ∧ y i a = true))
        (ofDecisionTree t₀) (ofDecisionTree t₁)

/-- The simulating protocol outputs what the decision tree outputs on `ind x y`. -/
@[simp] theorem run_ofDecisionTree (t : DecisionTree (Fin n) O) (x : Fin n → Fin m)
    (y : Fin n → Fin m → Bool) : (ofDecisionTree t).run x y = t.eval (ind x y) := by
  induction t with
  | leaf o => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    have hbit : decide (∃ a, BitString.indexBits a = BitString.indexBits (x i) ∧ y i a = true) =
        y i (x i) := by
      cases h : y i (x i)
      · simp only [decide_eq_false_iff_not, not_exists, not_and]
        intro a ha
        rw [BitString.indexBits_injective ha, h]
        exact Bool.false_ne_true
      · exact decide_eq_true ⟨x i, rfl, h⟩
    rw [ofDecisionTree, Protocol.run_aliceSend, Protocol.run_bob, hbit, ih₀, ih₁,
      DecisionTree.eval_node, ind_apply]

/-- Each query costs `⌈log₂ m⌉ + 1` bits. -/
theorem depth_ofDecisionTree_le (t : DecisionTree (Fin n) O) :
    (ofDecisionTree (m := m) t).depth ≤ t.depth * (Nat.clog 2 m + 1) := by
  induction t with
  | leaf o => simp [ofDecisionTree]
  | node i t₀ t₁ ih₀ ih₁ =>
    refine (Protocol.depth_aliceSend_le (d := max t₀.depth t₁.depth * (Nat.clog 2 m + 1) + 1)
      fun w => ?_).trans ?_
    · simp only [Protocol.depth_bob, add_le_add_iff_right, max_le_iff]
      exact ⟨ih₀.trans (Nat.mul_le_mul_right _ (le_max_left _ _)),
        ih₁.trans (Nat.mul_le_mul_right _ (le_max_right _ _))⟩
    · rw [DecisionTree.depth_node, Nat.succ_mul]
      omega

/-- **The upper bound of the lifting theorem.** If a decision tree of depth `d` solves `R`, then
the lifted problem has communication complexity at most `d (⌈log₂ m⌉ + 1)`
[Göös, Pitassi and Watson, (1)][GoosPitassiWatson2018]. -/
theorem ecomplexity_lift_le {R : (Fin n → Bool) → O → Prop} {t : DecisionTree (Fin n) O}
    (ht : ∀ z, R z (t.eval z)) :
    Protocol.ecomplexity (lift (m := m) R) Set.univ Set.univ ≤
      (t.depth * (Nat.clog 2 m + 1) : ℕ) := by
  refine (Protocol.ecomplexity_le_depth (p := ofDecisionTree t) fun x _ y _ => ?_).trans
    (by exact_mod_cast depth_ofDecisionTree_le t)
  simp only [lift, run_ofDecisionTree]
  exact ht _

end Cslib.Communication.Lifting
