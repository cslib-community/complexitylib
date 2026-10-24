/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Simulation.lean`)

public import Complexity.Computability.Circuit.Pi
public import Cslib.Computability.Circuit.Simulation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Circuit simulation and exact costs

The cost of a program is the sum of the costs of its lines (`Program.cost_eq_sum`), so a bound on
the cost of every operation bounds the cost of the program by the number of gates
(`Program.cost_le_mul`). Costs add up along the composition of circuits
(`Circuit.cost_program_comp`, `Circuit.cost_program_append`, `Circuit.cost_program_pi`).
Replacing each gate by a supplied circuit also preserves costs exactly, charging the source
operation the entire cost of its replacement (`Circuit.cost_program_simulate`).

## Main definitions

* `Cslib.Circuits.Circuit.simulate`: replace every gate by its implementation circuit.

## Main results

* `Cslib.Circuits.Circuit.eval_simulate`: simulation preserves all circuit outputs.
* `Cslib.Circuits.Program.cost_simulateProgram`, `Cslib.Circuits.Circuit.cost_program_simulate`:
  exact arbitrary weighted cost under simulation.
* `Cslib.Circuits.Program.cost_eq_sum`: program cost as a sum over gates.
* `Cslib.Circuits.Circuit.cost_program_comp`, `Cslib.Circuits.Circuit.cost_program_append`,
  `Cslib.Circuits.Circuit.cost_program_pi`: exact composition costs.
-/

@[expose] public section

namespace Cslib.Circuits

universe v w u

variable {σ : Signature.{v}} {τ : Signature.{w}} {U : Type u} {n g : ℕ}

/-- The cost of a program is the sum of the costs of its lines. -/
theorem Program.cost_eq_sum (p : Program σ n g) (cost : σ.Op → ℕ) :
    p.cost cost = ∑ k, cost (p.lines k).op := by
  induction p with
  | empty => simp
  | gate p line ih =>
    rw [Program.cost_gate, ih, Fin.sum_univ_castSucc]
    simp [Program.lines_gate_last, Program.lines_gate_castSucc]

/-- If every operation costs at most `b`, a program with `g` gates costs at most `b * g`. -/
theorem Program.cost_le_mul (p : Program σ n g) {cost : σ.Op → ℕ} {b : ℕ}
    (h : ∀ op, cost op ≤ b) : p.cost cost ≤ b * g :=
  (p.cost_mono h).trans_eq (p.cost_const b)

/-- Continuing a program adds the costs. -/
@[simp] theorem Program.cost_append {k g₂ : ℕ} (p : Program σ n g) (feed : Fin k → Wire n g)
    (q : Program σ k g₂) (cost : σ.Op → ℕ) :
    (p.append feed q).cost cost = p.cost cost + q.cost cost := by
  induction q with
  | empty => rfl
  | gate q line ih => rw [Program.append, Program.cost_gate, Program.cost_gate, ih,
      Line.mapWires_op, Nat.add_assoc]

/-- Weighted simulation cost is exactly the sum of the replacement-circuit costs. -/
theorem Program.cost_simulateProgram (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (cost : τ.Op → ℕ) :
    (p.simulateProgram impl).cost cost = p.cost fun op => (impl op).program.cost cost := by
  induction p with
  | empty => rfl
  | gate p line ih =>
    change ((p.simulateProgram impl).append _ (impl line.op).program).cost cost = _
    rw [cost_append, cost_gate, ih]

variable {m : ℕ}

/-- The circuit with every gate replaced by the circuit `impl op` for its operation. -/
def Circuit.simulate (c : Circuit σ n m) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) :
    Circuit τ n m :=
  ⟨c.program.simulateProgram impl, c.program.simulateRenaming impl ∘ c.outputs⟩

/-- The size of `c.simulate impl` is the program cost weighted by replacement circuit sizes. -/
@[simp] theorem Circuit.size_simulate (c : Circuit σ n m)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) :
    (c.simulate impl).size = c.program.cost fun op => (impl op).size :=
  rfl

/-- Replacing the gates by circuits computing their operations computes the same function. -/
theorem Circuit.eval_simulate {I : Interpretation σ U} {J : Interpretation τ U}
    (c : Circuit σ n m) (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    (h : ∀ op, (impl op).Computes J (single (I op))) : (c.simulate impl).eval J = c.eval I :=
  funext fun x => congrArg (· ∘ c.outputs) (c.program.trace_simulate impl h x)

namespace Circuit

/-! The costs of circuits built from smaller ones. They are not `simp` lemmas: `simp` would first
rewrite the number of gates, an implicit argument of `Program.cost`, by `Circuit.size_comp` and the
like, after which they no longer match. They apply with `rw` and `simp only`. -/

variable {p : ℕ}

/-- A pure wiring circuit has zero program cost under any operation weight. -/
theorem cost_program_wiring (select : Fin m → Fin n) (cost : σ.Op → ℕ) :
    (Circuit.wiring σ select).program.cost cost = 0 :=
  rfl

/-- A single-gate circuit has program cost equal to the cost of its operation. -/
theorem cost_program_oneGate (op : σ.Op) (args : Fin (σ.Arity op) → Fin n)
    (cost : σ.Op → ℕ) : (oneGate op args).program.cost cost = cost op :=
  Nat.zero_add _

/-- Sequential composition adds the costs. -/
theorem cost_program_comp (d : Circuit σ m p) (c : Circuit σ n m) (cost : σ.Op → ℕ) :
    (d.comp c).program.cost cost = c.program.cost cost + d.program.cost cost :=
  Program.cost_append _ _ _ cost

/-- Parallel composition adds the costs. -/
theorem cost_program_append (c : Circuit σ n m) (d : Circuit σ n p) (cost : σ.Op → ℕ) :
    (c.append d).program.cost cost = c.program.cost cost + d.program.cost cost :=
  Program.cost_append _ _ _ cost

/-- Gate replacement preserves arbitrary weighted costs exactly. -/
theorem cost_program_simulate (c : Circuit σ n m)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (cost : τ.Op → ℕ) :
    (c.simulate impl).program.cost cost =
      c.program.cost fun op => (impl op).program.cost cost :=
  c.program.cost_simulateProgram impl cost

/-- The cost of `pi cs` is the sum of the costs. -/
theorem cost_program_pi (cs : Fin m → Circuit σ n 1) (cost : σ.Op → ℕ) :
    (pi cs).program.cost cost = ∑ j, (cs j).program.cost cost := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pi, cost_program_append, ih, Fin.sum_univ_castSucc]

end Circuit

end Cslib.Circuits
