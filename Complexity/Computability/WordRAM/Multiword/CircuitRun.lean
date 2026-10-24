/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Multiword.Circuit

/-!
# Sequential execution of multiword instruction graphs

An instruction graph whose sources precede their destinations can be executed in node order.
The execution theorem composes a checked implementation of each node over the standard RAM
basis. It tracks the encoded prefix, instruction count, and preservation of memory.

## Main definitions

* `Circuit.prefix`: completed node values, with future entries zeroed.
* `Circuit.nop`: one-instruction no-op terminator.
* `Circuit.run`: sequential composition of a supplied node compiler.

## Main results

* `Circuit.size_run`: a linear code-size bound from the node-size bound.
* `Circuit.exec_run`: a linear execution bound from the checked node-execution contract.

## References

* [Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*][CLRS2009].
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword.Circuit

variable {n : ℕ}

/-- Values of completed nodes, with future entries zeroed. -/
def «prefix» (v : Fin n → ℕ) (k : ℕ) : Fin n → ℕ :=
  fun j => if j.val < k then v j else 0

/-- Completing the next node extends the encoded prefix by one entry. -/
private theorem update_prefix (v : Fin n → ℕ) (d : Fin n) :
    Function.update («prefix» v d.val) d (v d) = «prefix» v (d.val + 1) := by
  funext j
  by_cases hj : j = d
  · subst j
    simp [«prefix»]
  · have hne : j.val ≠ d.val := fun h => hj (Fin.ext h)
    rw [Function.update_of_ne hj]
    unfold «prefix»
    have hlt : j.val < d.val ↔ j.val < d.val + 1 := by omega
    simp only [hlt]

namespace Operation

/-- Evaluation depends only on the earlier source values of a node. -/
private theorem eval_congr {d : Fin n} {op : Operation n} {v u : Fin n → ℕ}
    (he : op.Earlier d) (h : ∀ j, j.val < d.val → v j = u j) :
    op.eval v = op.eval u := by
  cases op with
  | constant z => rfl
  | binary f a b =>
    change a.val < d.val ∧ b.val < d.val at he
    simp only [eval, h a he.1, h b he.2]

/-- The admissibility bounds depend only on the earlier source values of a node. -/
private theorem admissible_congr {w : ℕ} {d : Fin n} {op : Operation n} {v u : Fin n → ℕ}
    (he : op.Earlier d) (h : ∀ j, j.val < d.val → v j = u j) :
    op.Admissible w v ↔ op.Admissible w u := by
  cases op with
  | constant z => rfl
  | binary f a b =>
    change a.val < d.val ∧ b.val < d.val at he
    simp only [Admissible, eval, h a he.1, h b he.2]

end Operation

/-- A one-instruction terminator that copies a workspace register to itself. -/
def nop : Code .standard (Bank.capacity n + 4) :=
  .op (.copy Workspace.carry Workspace.carry)

/-- Execute up to `fuel` consecutive nodes, stopping at the end of the graph. -/
def run (emit : Fin n → Operation n → Code .standard (Bank.capacity n + 4))
    (ops : Fin n → Operation n) (k : ℕ) : ℕ → Code .standard (Bank.capacity n + 4)
  | 0 => nop
  | fuel + 1 => if h : k < n then
      .seq (emit ⟨k, h⟩ (ops ⟨k, h⟩)) (run emit ops (k + 1) fuel)
    else nop

/-- A node compiler of size at most four thousand gives a linear compiled-size bound. -/
theorem size_run (emit : Fin n → Operation n → Code .standard (Bank.capacity n + 4))
    (hsize : ∀ d op, (emit d op).size ≤ 4000) (ops : Fin n → Operation n) (k fuel : ℕ) :
    (run emit ops k fuel).size ≤ fuel * 4000 + 1 := by
  induction fuel generalizing k with
  | zero => simp [run, nop, Code.size]
  | succ fuel ih =>
    by_cases hk : k < n
    · simp only [run, dite_eq_left hk, Code.size]
      have := hsize ⟨k, hk⟩ (ops ⟨k, hk⟩)
      have := ih (k + 1)
      omega
    · simp [run, hk, nop, Code.size]

/-- Sequential composition of checked node executions reconstructs the prescribed graph
values. Only nodes in the executed interval need satisfy the graph specification. -/
theorem exec_run
    (emit : Fin n → Operation n → Code .standard (Bank.capacity n + 4))
    {w : ℕ}
    (hnode : ∀ (d : Fin n) (op : Operation n) (x : Data (Bank.capacity n + 4))
      (v : Fin n → ℕ), op.Earlier d → op.Admissible w v → Bank.Encodes w x v →
      ∃ y, ExecWithin w (emit d op) x y 4000 ∧
        Bank.Encodes w y (Function.update v d (op.eval v)) ∧ y.mem = x.mem)
    (ops : Fin n → Operation n) (v : Fin n → ℕ) (k fuel : ℕ)
    (hbound : k + fuel ≤ n)
    (hgraph : ∀ i : Fin n, k ≤ i.val → i.val < k + fuel →
      (ops i).Earlier i ∧ (ops i).eval v = v i ∧ (ops i).Admissible w v)
    (x : Data (Bank.capacity n + 4)) (hx : Bank.Encodes w x («prefix» v k)) :
    ∃ y, ExecWithin w (run emit ops k fuel) x y (fuel * 4000 + 1) ∧
      Bank.Encodes w y («prefix» v (k + fuel)) ∧ y.mem = x.mem := by
  induction fuel generalizing k x with
  | zero =>
    refine ⟨x, ?_, ?_, rfl⟩
    · simpa [run, nop, Data.set] using
        (ExecWithin.copy (B := .standard) (w := w) (x := x)
          (d := Workspace.carry) (s := Workspace.carry))
    · simpa only [Nat.add_zero] using hx
  | succ fuel ih =>
    have hk : k < n := by omega
    let d : Fin n := ⟨k, hk⟩
    obtain ⟨he, hv, ha⟩ := hgraph d (by rfl) (by dsimp [d]; omega)
    have hprefix (j : Fin n) (hj : j.val < d.val) : «prefix» v k j = v j := by
      exact ite_eq_left hj
    have heval : (ops d).eval («prefix» v k) = v d :=
      (Operation.eval_congr he hprefix).trans hv
    have hadm : (ops d).Admissible w («prefix» v k) :=
      (Operation.admissible_congr he hprefix).mpr ha
    obtain ⟨z, hz, hze, hzm⟩ := hnode d (ops d) x («prefix» v k) he hadm hx
    rw [heval, update_prefix v d] at hze
    obtain ⟨y, hy, hye, hym⟩ := ih (k + 1) (by omega)
      (fun i hi hi' => hgraph i (by omega) (by omega)) z hze
    refine ⟨y, ?_, ?_, hym.trans hzm⟩
    · simpa only [run, dite_eq_left hk, Nat.succ_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hz.seq hy
    · simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hye

end Cslib.WordRAM.Multiword.Circuit

end
