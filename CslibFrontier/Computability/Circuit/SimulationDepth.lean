/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Computability/Circuit/Simulation.lean`)

public import CslibFrontier.Computability.Circuit.CompositionDepth
public import CslibFrontier.Computability.Circuit.Simulation

/-!
# The depth of a simulation

Replacing every gate of a program by a circuit computing its operation (`Program.simulate`) makes
each wire at most as deep as its depth in the original program when an operation `op` costs the
depth of its replacement circuit (`Program.wireDepths_simulateRenaming_le`). So a circuit over one
basis is simulated by a circuit over another basis whose depth is bounded by the original depth
with these costs (`Circuit.depth_simulate_le`), at most the original depth times the largest depth
of a replacement.

## Main results

* `Cslib.Circuits.Program.wireDepths_simulateRenaming_le`: depths of simulated wires.
* `Cslib.Circuits.Circuit.depth_simulate_le`: the depth of a simulated circuit.
* `Cslib.Circuits.Circuit.exists_simulation_depth_le`: simulation with bounds on size and depth.
-/

public section

namespace Cslib.Circuits

universe v w u

variable {σ : Signature.{v}} {τ : Signature.{w}} {U : Type u} {n g m : ℕ}

/-- **The depth of a simulation**: a wire of the simulating program is at most as deep as the
original wire, when every operation costs the depth of the circuit replacing it. -/
theorem Program.wireDepths_simulateRenaming_le (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) (w : Wire n g) :
    (p.simulateProgram impl).wireDepths (p.simulateRenaming impl w) ≤
      p.wireDepthsWith (fun op => (impl op).depth) w := by
  induction p with
  | empty => cases w with
    | input i => exact le_rfl
    | gate j => exact j.elim0
  | gate q line ih =>
    dsimp only [simulateProgram, simulateRenaming, simulate, cost_gate]
    dsimp only [simulateProgram, simulateRenaming] at ih
    set cost : σ.Op → ℕ := fun op => (impl op).depth
    refine Wire.lastCases ?_ (fun w => ?_) w
    · simp only [Wire.Renaming.apply_gate, Wire.Renaming.skipLast_gates_last]
      rw [Program.wireDepthsWith_gateWire, Program.depthsWith_gate_last]
      have h₀ := line.wireDepth_add_le_depthWith cost (q.wireDepthsWith cost)
      have hc : (impl line.op).depth ≤ line.depthWith cost (q.wireDepthsWith cost) :=
        line.cost_le_depthWith cost _
      have hD (a : Fin (σ.Arity line.op)) :
          (q.simulate impl).1.wireDepths (((q.simulate impl).2 ∘ line.wires) a) ≤
            line.depthWith cost (q.wireDepthsWith cost) - (impl line.op).depth := by
        have h₁ := ih (line.wires a)
        have h₂ : q.wireDepthsWith cost (line.wires a) + (impl line.op).depth ≤
            line.depthWith cost (q.wireDepthsWith cost) := h₀ a
        simp only [Function.comp_apply]
        omega
      have h := Program.wireDepths_append_appendedWire_le _ _ hD (impl line.op).program
        ((impl line.op).outputs 0)
      have ho := (impl line.op).outputDepths_le_depth 0
      simp only [Circuit.outputDepths, Function.comp_apply] at ho
      omega
    · rw [Wire.Renaming.skipLast_castSucc, Program.wireDepthsWith_gate_castSucc]
      have hold := (Program.wireDepths_append_castAdd (q.simulate impl).1
        ((q.simulate impl).2 ∘ line.wires) (impl line.op).program ((q.simulate impl).2 w)).trans_le
        (ih w)
      cases w <;> exact hold

/-- The simulated circuit is at most as deep as the original circuit when every operation costs
the depth of its replacement. -/
theorem Circuit.depth_simulate_le (c : Circuit σ n m)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1) :
    (c.simulate impl).depth ≤ c.depthWith fun op => (impl op).depth :=
  (Circuit.depth_le_iff _).2 fun j =>
    (c.program.wireDepths_simulateRenaming_le impl (c.outputs j)).trans
      (c.wireDepthsWith_outputs_le_depthWith _ j)

/-- **Simulation with bounds on size and depth**: if every operation of `I` is computed under `J`
by a circuit with at most `size op` gates and depth at most `depth op`, then every circuit over
`σ` has an equivalent circuit over `τ` with at most `c.program.cost size` gates and depth at most
`c.depthWith depth`. -/
theorem Circuit.exists_simulation_depth_le {I : Interpretation σ U} {J : Interpretation τ U}
    (c : Circuit σ n m) (size depth : σ.Op → ℕ)
    (h : ∀ op, ∃ d : Circuit τ (σ.Arity op) 1,
      d.Computes J (single (I op)) ∧ d.size ≤ size op ∧ d.depth ≤ depth op) :
    ∃ d : Circuit τ n m, d.eval J = c.eval I ∧ d.size ≤ c.program.cost size ∧
      d.depth ≤ c.depthWith depth := by
  choose impl himpl hsize hdepth using h
  exact ⟨c.simulate impl, c.eval_simulate impl himpl,
    (c.size_simulate impl).trans_le (c.program.cost_mono hsize),
    (c.depth_simulate_le impl).trans (c.depthWith_mono hdepth)⟩

end Cslib.Circuits
