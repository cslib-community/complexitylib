/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.SemiCircuit
public import Cslib.Computability.Circuit.Full
public import Mathlib.Data.Fin.VecNotation
import Complexity.Computability.Circuit.Program

/-!
# The semi-circuit of a circuit

A circuit over the full binary basis with `n` inputs and one output is a fair semi-circuit without
equations (`SemiCircuit.ofCircuit`): input `i` is the parameter `i`, gate `j` is the gate `n + j`,
and a constant line becomes a gate with a constant operation. It is well formed
(`SemiCircuit.wellFormed_ofCircuit`), and the output of a consistent assignment is the output of
the circuit on the values of the parameters (`SemiCircuit.out_eval_ofCircuit`).

## Main definitions

* `Cslib.Circuits.Boolean.SemiCircuit.ofCircuit`: the semi-circuit of a circuit.

## Main results

* `Cslib.Circuits.Boolean.SemiCircuit.wellFormed_ofCircuit`,
  `Cslib.Circuits.Boolean.SemiCircuit.out_eval_ofCircuit`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.SemiCircuit

open Cslib.Circuits

variable {n : ℕ}

/-- The name of a wire of a circuit with `n` inputs: input `i` is `i` and gate `j` is `n + j`. -/
def wireName {g : ℕ} : Wire n g → ℕ
  | .input i => i
  | .gate j => n + j

/-- The gate of a line of a circuit over the full binary basis; a constant becomes a gate with
a constant operation. -/
def lineGate {g : ℕ} : Line (fullSignature 2 Bool) n g → Gate
  | ⟨.fn op, w⟩ => ⟨fun a b => op ![a, b], .node (wireName (w ⟨0, by simp [fullSignature]⟩)),
      .node (wireName (w ⟨1, by simp [fullSignature]⟩))⟩
  | ⟨.con c, _⟩ => ⟨fun _ _ => c, .const false, .const false⟩

theorem eval_lineGate {g : ℕ} (line : Line (fullSignature 2 Bool) n g) (val : ℕ → Bool) :
    (lineGate line).eval val =
      fullInterpretation line.op fun a => val (wireName (line.wires a)) := by
  obtain ⟨op | c, w⟩ := line
  · simp only [lineGate, Gate.eval, Arg.eval_node, fullInterpretation]
    congr 1
    funext a
    obtain ⟨_ | _ | k, ha⟩ := a
    · rfl
    · rfl
    · simp at ha
  · rfl

private theorem reads_lineGate {g : ℕ} {line : Line (fullSignature 2 Bool) n g} {i : ℕ}
    (h : (lineGate line).Reads i) : ∃ a, wireName (line.wires a) = i := by
  obtain ⟨op | c, w⟩ := line
  · rcases h with h | h
    · exact ⟨_, Arg.node.inj h⟩
    · exact ⟨_, Arg.node.inj h⟩
  · rcases h with h | h <;> cases h

/-- The semi-circuit of a circuit over the full binary basis with one output: its inputs are the
parameters, its lines the gates, and it has no auxiliary variables and no equations. -/
def ofCircuit (C : Circuit (fullSignature 2 Bool) n 1) : SemiCircuit where
  params := Finset.range n
  aux := ∅
  gates := Finset.Ico n (n + C.size)
  gate i := if h : n ≤ i ∧ i < n + C.size then lineGate (C.program.lines ⟨i - n, by omega⟩)
    else ⟨fun _ _ => false, .const false, .const false⟩
  eqns := ∅
  eqn _ := ⟨∅, false⟩
  out := ⟨.node (wireName (C.outputs 0)), false⟩

@[simp] theorem ofCircuit_params (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).params = Finset.range n := rfl

@[simp] theorem ofCircuit_aux (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).aux = ∅ := rfl

@[simp] theorem ofCircuit_gates (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).gates = Finset.Ico n (n + C.size) := rfl

@[simp] theorem ofCircuit_eqns (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).eqns = ∅ := rfl

private theorem ofCircuit_gate (C : Circuit (fullSignature 2 Bool) n 1) (k : Fin C.size) :
    (ofCircuit C).gate (n + k) = lineGate (C.program.lines k) := by
  have h : n ≤ n + (k : ℕ) ∧ n + (k : ℕ) < n + C.size := ⟨Nat.le_add_right _ _, by omega⟩
  simp only [ofCircuit, dite_eq_left h]
  congr 2
  exact Fin.ext (by simp)

theorem wireName_mem_live (C : Circuit (fullSignature 2 Bool) n 1) (w : Wire n C.size) :
    wireName w ∈ (ofCircuit C).live := by
  cases w with
  | input i => simp [live, ofCircuit, wireName]
  | gate j => simp [live, ofCircuit, wireName]

theorem exists_eq_add_of_mem_gates {C : Circuit (fullSignature 2 Bool) n 1} {J : ℕ}
    (hJ : J ∈ (ofCircuit C).gates) : ∃ k : Fin C.size, J = n + k := by
  simp only [ofCircuit, Finset.mem_Ico] at hJ
  exact ⟨⟨J - n, by omega⟩, by dsimp only; omega⟩

/-- The semi-circuit of a circuit is well formed. -/
theorem wellFormed_ofCircuit (C : Circuit (fullSignature 2 Bool) n 1) :
    (ofCircuit C).WellFormed where
  disjoint_params_aux := Finset.disjoint_empty_right _
  disjoint_params_gates := by
    rw [Finset.disjoint_left]
    intro i hi hg
    simp only [ofCircuit, Finset.mem_range, Finset.mem_Ico] at hi hg
    omega
  disjoint_aux_gates := Finset.disjoint_empty_left _
  reads_lt J hJ i hi hr := by
    obtain ⟨k, rfl⟩ := exists_eq_add_of_mem_gates hJ
    rw [ofCircuit_gate] at hr
    obtain ⟨a, ha⟩ := reads_lineGate hr
    simp only [ofCircuit, Finset.mem_Ico] at hi
    cases hw : (C.program.lines k).wires a with
    | input i' => rw [hw] at ha; simp only [wireName] at ha; omega
    | gate j =>
      rw [hw] at ha
      simp only [wireName] at ha
      rw [← ha]
      exact Nat.add_lt_add_left (C.program.lt_of_lines_wires_eq_gate k a j hw) n
  reads_live J hJ i hr := by
    obtain ⟨k, rfl⟩ := exists_eq_add_of_mem_gates hJ
    rw [ofCircuit_gate] at hr
    obtain ⟨a, rfl⟩ := reads_lineGate hr
    exact wireName_mem_live C _
  terms_subset e he := by simp [ofCircuit] at he
  card_terms_le e he := by simp [ofCircuit] at he
  out_live i hi := by
    cases hi
    exact wireName_mem_live C _
  solvable u := ⟨u, fun _ _ => rfl, fun e he => by simp [ofCircuit] at he⟩
  unique _ _ _ _ _ v hv := by simp [ofCircuit] at hv

/-- On a consistent assignment, the output of the semi-circuit of a circuit is the output of the
circuit on the values of the parameters. -/
theorem out_eval_ofCircuit (C : Circuit (fullSignature 2 Bool) n 1) {val : ℕ → Bool}
    (hval : (ofCircuit C).Consistent val) :
    (ofCircuit C).out.eval val = C.eval fullInterpretation (fun i => val i) 0 := by
  have htrace : (fun w => val (wireName w)) =
      C.program.trace fullInterpretation (fun i => val i) := by
    refine Program.eq_trace_of_forall_gate (fun i => rfl) fun k => ?_
    have hk : n + (k : ℕ) ∈ (ofCircuit C).gates := by
      simp only [ofCircuit, Finset.mem_Ico]; omega
    have := hval.2 _ hk
    rw [ofCircuit_gate, eval_lineGate] at this
    exact this
  change (val (wireName (C.outputs 0)) ^^ false) = _
  rw [Bool.xor_false, Circuit.eval, Function.comp_apply, ← htrace]

end Cslib.Circuits.Boolean.SemiCircuit
