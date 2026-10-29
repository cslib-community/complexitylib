/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Composition.lean`)

public import Complexity.Computability.Circuit.CompositionDepth
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Fin

/-!
# Circuits side by side

`Circuit.pi cs` runs the single-output circuits `cs j` on the same inputs and lists their outputs
(`Circuit.eval_pi`); its size is the sum of their sizes (`Circuit.size_pi`) and its depth the
largest of their depths (`Circuit.depth_pi_le`), also with costs (`Circuit.depthWith_pi_le`).

## Main definitions

* `Cslib.Circuits.Circuit.pi`: single-output circuits side by side.
* `Cslib.Circuits.Circuit.oneGate`: the circuit of one gate on inputs.

## Main results

* `Cslib.Circuits.Circuit.eval_pi`, `Cslib.Circuits.Circuit.size_pi`,
  `Cslib.Circuits.Circuit.depth_pi_le`: the function, size and depth of circuits side by side.
* `Cslib.Circuits.Circuit.depth_oneGate`, `Cslib.Circuits.Circuit.fanInAtMost_oneGate`: one gate
  has depth one, and fan-in the arity of its operation.
* `Cslib.Circuits.Circuit.depthWith_pi_le`, `Cslib.Circuits.Circuit.depthWith_oneGate`: the same
  for depths with costs.
-/

@[expose] public section

namespace Cslib.Circuits.Circuit

variable {σ : Signature} {n : ℕ} {U : Type*}

/-- The single-output circuits `cs j` on shared inputs, with output `j` the output of `cs j`. -/
def pi : {m : ℕ} → (Fin m → Circuit σ n 1) → Circuit σ n m
  | 0, _ => Circuit.wiring σ Fin.elim0
  | m + 1, cs => (pi fun i => cs i.castSucc).append (cs (Fin.last m))

/-- Output `j` of `pi cs` is the output of `cs j`. -/
@[simp] theorem eval_pi {I : Interpretation σ U} {m : ℕ} (cs : Fin m → Circuit σ n 1)
    (x : Fin n → U) : (pi cs).eval I x = fun j => (cs j).eval I x 0 := by
  induction m with
  | zero => funext j; exact j.elim0
  | succ m ih =>
    funext j
    rw [pi, eval_append]
    induction j using Fin.lastCases with
    | last => exact Fin.append_right _ _ 0
    | cast j =>
      rw [show j.castSucc = Fin.castAdd 1 j from rfl, Fin.append_left, ih]
      rfl

/-- The size of `pi cs` is the sum of the sizes. -/
@[simp] theorem size_pi {m : ℕ} (cs : Fin m → Circuit σ n 1) : (pi cs).size = ∑ j, (cs j).size := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pi, size_append, ih, Fin.sum_univ_castSucc]

/-- With costs, the depth of `pi cs` is at most the largest depth. -/
theorem depthWith_pi_le (cost : σ.Op → ℕ) {m : ℕ} (cs : Fin m → Circuit σ n 1) {D : ℕ}
    (h : ∀ j, (cs j).depthWith cost ≤ D) : (pi cs).depthWith cost ≤ D := by
  induction m with
  | zero => exact (Circuit.depthWith_le_iff cost _).2 fun j => j.elim0
  | succ m ih =>
    rw [pi]
    exact (depthWith_append_le cost _ _).trans (max_le (ih _ fun j => h _) (h _))

/-- The circuit of one gate: the operation `op` applied to the inputs `args`. -/
def oneGate (op : σ.Op) (args : Fin (σ.Arity op) → Fin n) : Circuit σ n 1 :=
  ⟨.gate .empty ⟨op, fun a => .input (args a)⟩, fun _ => .gate 0⟩

/-- Evaluating `oneGate op args` at `x` applies `I op` to the selected inputs `x ∘ args`. -/
@[simp] theorem eval_oneGate {I : Interpretation σ U} (op : σ.Op) (args : Fin (σ.Arity op) → Fin n)
    (x : Fin n → U) (j : Fin 1) : (oneGate op args).eval I x j = I op fun a => x (args a) :=
  rfl

/-- The circuit `oneGate op args` has size `1`. -/
@[simp] theorem size_oneGate (op : σ.Op) (args : Fin (σ.Arity op) → Fin n) :
    (oneGate op args).size = 1 :=
  rfl

/-- With costs, one gate has the depth of its cost. -/
@[simp] theorem depthWith_oneGate (cost : σ.Op → ℕ) (op : σ.Op)
    (args : Fin (σ.Arity op) → Fin n) : (oneGate op args).depthWith cost = cost op := by
  refine le_antisymm ((Circuit.depthWith_le_iff cost _).2 fun _ => ?_) ?_
  · exact (Line.depthWith_eq_cost cost _ fun _ => rfl).le
  · exact (Line.depthWith_eq_cost cost _ fun _ => rfl).symm.le.trans
      ((oneGate op args).wireDepthsWith_outputs_le_depthWith cost 0)

/-- The depth of `pi cs` is at most the largest depth. -/
theorem depth_pi_le {m : ℕ} (cs : Fin m → Circuit σ n 1) {D : ℕ} (h : ∀ j, (cs j).depth ≤ D) :
    (pi cs).depth ≤ D := by
  simpa only [Circuit.depthWith_one] using
    depthWith_pi_le 1 cs fun j => by simpa only [Circuit.depthWith_one] using h j

/-- One gate has depth one. -/
@[simp] theorem depth_oneGate (op : σ.Op) (args : Fin (σ.Arity op) → Fin n) :
    (oneGate op args).depth = 1 := by
  simpa only [Circuit.depthWith_one, Pi.one_apply] using depthWith_oneGate 1 op args

/-- One gate has fan-in at most `r` exactly when its operation has arity at most `r`. -/
@[simp] theorem fanInAtMost_oneGate (op : σ.Op) (args : Fin (σ.Arity op) → Fin n) (r : ℕ) :
    (oneGate op args).FanInAtMost r ↔ σ.Arity op ≤ r :=
  ⟨fun h => h.2, fun h => ⟨trivial, h⟩⟩

end Cslib.Circuits.Circuit
