/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Program.lean`)

public import Cslib.Computability.Circuit.Program

/-!
# Lines read earlier wires

In the widened lines of a program (`Program.lines`), every gate wire that a line reads comes
before the line's own gate (`Program.lt_of_lines_wires_eq_gate`), so facts about wires can be
proved by induction along the program order (`Program.wire_induction`). Bounded fan-in is a
bound on the arity of every line (`Program.fanInAtMost_iff`).

The value of a gate is its operation applied to the values of the wires it reads
(`Program.trace_gate`, and `Program.trace_gate_last` for the last gate), and a valuation of the
wires that reads the inputs and satisfies the equation of every gate is the trace
(`Program.eq_trace_of_forall_gate`).

## Main results

* `Program.wire_induction`: induction along the program order.
* `Program.fanInAtMost_iff`: bounded fan-in, gate by gate.
* `Program.trace_gate`, `Program.trace_gate_last`: the value of a gate.
* `Program.trace_induction`: propagate a semantic invariant from inputs through gates.
* `Program.trace_rel`, `Program.eval_rel`: lift a relation between two interpretations.
* `Program.eq_trace_of_forall_gate`: the trace is the unique solution of the gate equations.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- The gate wires read by a line come before its gate. -/
theorem Program.lt_of_lines_wires_eq_gate (p : Program σ n g) (k : Fin g)
    (s : Fin (σ.Arity (p.lines k).op)) (j : Fin g) (h : (p.lines k).wires s = .gate j) :
    j < k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    -- Both kinds of gate widen a line whose gate wires are earlier, by `Wire.castSucc`.
    have widen (line' : Line σ n g) (bound : Fin (g + 1))
        (hbound : ∀ s j, line'.wires s = .gate j → j.castSucc < bound) :
        ∀ s j, (line'.mapWires Wire.Renaming.castSucc).wires s = .gate j → j < bound := by
      intro s j h
      change Wire.Renaming.castSucc (line'.wires s) = _ at h
      rw [Wire.Renaming.castSucc_apply] at h
      cases hw : line'.wires s with
      | input => rw [hw] at h; cases h
      | gate j' =>
        rw [hw] at h
        cases h
        exact hbound s j' hw
    revert s j
    induction k using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last]
      exact widen line _ fun _ j _ => Fin.castSucc_lt_last j
    | cast k =>
      rw [Program.lines_gate_castSucc]
      exact widen _ _ fun s j hw => Fin.castSucc_lt_castSucc_iff.2 (ih k s j hw)

/-- A program has fan-in at most `r` exactly when every gate reads at most `r` wires. -/
theorem Program.fanInAtMost_iff {p : Program σ n g} {r : ℕ} :
    p.FanInAtMost r ↔ ∀ k, σ.Arity (p.lines k).op ≤ r := by
  induction p with
  | empty => exact iff_of_true trivial fun k => k.elim0
  | gate p line ih =>
    rw [Program.FanInAtMost, ih, Fin.forall_fin_succ']
    simp only [Program.lines_gate_castSucc, Program.lines_gate_last, Line.mapWires_op]

/-- Induction along the program order: a property of wires that holds for the inputs, and for a
gate whenever it holds for the wires the gate reads, holds for every wire. -/
theorem Program.wire_induction (p : Program σ n g) {P : Wire n g → Prop}
    (input : ∀ i, P (.input i)) (gate : ∀ k, (∀ s, P ((p.lines k).wires s)) → P (.gate k))
    (w : Wire n g) : P w := by
  have hgate : ∀ m, ∀ k : Fin g, (k : ℕ) = m → P (.gate k) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro k hk
      refine gate k fun s => ?_
      cases hw : (p.lines k).wires s with
      | input i => exact input i
      | gate j => exact ih j (hk ▸ p.lt_of_lines_wires_eq_gate k s j hw) j rfl
  cases w with
  | input i => exact input i
  | gate k => exact hgate k k rfl

section Trace

variable {U : Type*}

/-- The value of a gate is its operation applied to the values of the wires it reads. -/
theorem Program.trace_gate (p : Program σ n g) (I : Interpretation σ U) (x : Fin n → U)
    (k : Fin g) :
    p.trace I x (.gate k) = I (p.lines k).op fun a => p.trace I x ((p.lines k).wires a) :=
  (p.lines_eval I x k).symm

/-- The value of the last gate of a program is its operation applied to the values of its
arguments. -/
theorem Program.trace_gate_last (p : Program σ n g) (line : Line σ n g) (I : Interpretation σ U)
    (x : Fin n → U) :
    (p.gate line).trace I x (.gate (Fin.last g)) = I line.op fun a => p.trace I x (line.wires a) :=
  p.eval_gate_last line I x

/-- An invariant holding on the inputs and preserved by every evaluated gate holds on every
wire. The preservation hypothesis is needed only for the arguments actually read by the gate. -/
theorem Program.trace_induction (p : Program σ n g) (I : Interpretation σ U) (x : Fin n → U)
    {P : U → Prop} (input : ∀ i, P (x i))
    (gate : ∀ k, (∀ a, P (p.trace I x ((p.lines k).wires a))) →
      P (I (p.lines k).op (p.trace I x ∘ (p.lines k).wires))) (w : Wire n g) :
    P (p.trace I x w) := by
  refine p.wire_induction (P := fun w => P (p.trace I x w)) input (fun k ih => ?_) w
  rw [p.trace_gate]
  exact gate k ih

/-- A valuation of the wires is the trace of `p` when it reads the inputs and satisfies the
equation of every gate. -/
theorem Program.eq_trace_of_forall_gate {p : Program σ n g} {I : Interpretation σ U}
    {v : Wire n g → U} {x : Fin n → U} (hin : ∀ i, v (.input i) = x i)
    (hgate : ∀ k, v (.gate k) = I (p.lines k).op fun a => v ((p.lines k).wires a)) :
    v = p.trace I x := by
  have hv : v = Wire.elim x fun k => v (.gate k) := by
    funext w
    cases w with
    | input i => exact hin i
    | gate k => rfl
  have hgates : (fun k => v (.gate k)) = p.eval I x := by
    refine p.eq_eval_of_forall_lines_eval I x _ fun k => ?_
    simp only [Line.eval, Function.comp_def, ← hv]
    exact (hgate k).symm
  rw [Program.trace, ← hgates, ← hv]

end Trace

/-- Two interpretations preserve a relation on every wire if the inputs are related and the
operations occurring in the program preserve it. No condition is imposed on unused operations. -/
theorem Program.trace_rel {U V : Type*} (p : Program σ n g)
    {I : Interpretation σ U} {J : Interpretation σ V} {x : Fin n → U} {y : Fin n → V}
    (R : U → V → Prop) (input : ∀ i, R (x i) (y i))
    (gate : ∀ k a b, (∀ i, R (a i) (b i)) → R (I (p.lines k).op a) (J (p.lines k).op b))
    (w : Wire n g) : R (p.trace I x w) (p.trace J y w) := by
  refine p.wire_induction (P := fun w => R (p.trace I x w) (p.trace J y w))
    input (fun k ih => ?_) w
  rw [p.trace_gate, p.trace_gate]
  exact gate k _ _ ih

/-- Related inputs and gate interpretations give related gate values. -/
theorem Program.eval_rel {U V : Type*} (p : Program σ n g)
    {I : Interpretation σ U} {J : Interpretation σ V} {x : Fin n → U} {y : Fin n → V}
    (R : U → V → Prop) (input : ∀ i, R (x i) (y i))
    (gate : ∀ k a b, (∀ i, R (a i) (b i)) → R (I (p.lines k).op a) (J (p.lines k).op b))
    (k : Fin g) : R (p.eval I x k) (p.eval J y k) :=
  p.trace_rel R input gate (.gate k)

end Cslib.Circuits
