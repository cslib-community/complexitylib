/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Depth
public import Complexity.Computability.Circuit.Formula

/-!
# Unfolding circuits into formulas

Every wire of a program carries the function of a formula: unfold the gates below it into a tree,
copying a gate once for each time it is read (`Program.wireFormula`). The formula of an output of a
circuit (`Circuit.toFormula`) computes that output (`Circuit.eval_toFormula`) and has exactly its
depth, whatever each operation costs (`Circuit.depthWith_toFormula`). Copying gates can make the
formula exponentially larger than the circuit, but no larger than its depth allows: over a basis
of fan-in at most `r ≥ 2`, the formula of an output of a circuit of depth `d` has fewer than
`r ^ d` operation nodes (`Circuit.size_toFormula_lt`). So circuits of fan-in two and logarithmic
depth are formulas of logarithmic depth and polynomial size [Jukna, Chapter 6][Jukna2012].

## Main definitions

* `Cslib.Circuits.Program.gateFormula`, `Cslib.Circuits.Program.wireFormula`: the formulas
  unfolding the gates and the wires of a program.
* `Cslib.Circuits.Circuit.toFormula`: the formula unfolding an output of a circuit.

## Main results

* `Cslib.Circuits.Circuit.eval_toFormula`, `Cslib.Circuits.Circuit.Computes.toFormula`: the formula
  of an output computes it.
* `Cslib.Circuits.Circuit.depthWith_toFormula`, `Cslib.Circuits.Circuit.depth_toFormula_le`: it is
  as deep as the output, so no deeper than the circuit.
* `Cslib.Circuits.Circuit.size_toFormula_lt`: under bounded fan-in, its size is at most exponential
  in the depth of the circuit.
* `Cslib.Circuits.Program.gateFormula_eq_gate`,
  `Cslib.Circuits.Program.exists_wireFormula_eq_of_eq_gate`: the formula of a gate is its operation
  applied to the formulas of the wires it reads, so the formulas of the wires are closed under
  taking arguments.
* `Cslib.Circuits.Formula.toFormula_toCircuit`,
  `Cslib.Circuits.Formula.gateFormula_toCircuit_of_closed`: the circuit of a formula unfolds to
  the formula, and the formulas of its gates are subformulas.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

universe v

variable {σ : Signature.{v}} {n g m : ℕ} {U : Type*}

/-- The formulas unfolding the gates of a program: a gate is its operation applied to the formulas
of the wires it reads, so a gate read several times is copied. -/
def Program.gateFormula : {g : ℕ} → Program σ n g → Fin g → Formula σ n
  | _, .empty => Fin.elim0
  | _, .gate p line =>
    Fin.lastCases (.gate line.op fun a => Wire.elim .input p.gateFormula (line.wires a))
      p.gateFormula

/-- The formula unfolding a wire of a program: an input, or the formula of a gate. -/
def Program.wireFormula (p : Program σ n g) : Wire n g → Formula σ n :=
  Wire.elim .input p.gateFormula

/-- Unfolding an input wire `.input i` gives the input formula `.input i`. -/
@[simp] theorem Program.wireFormula_input (p : Program σ n g) (i : Fin n) :
    p.wireFormula (.input i) = .input i :=
  rfl

/-- Unfolding a gate wire `.gate k` gives the gate formula `p.gateFormula k`. -/
@[simp] theorem Program.wireFormula_gate (p : Program σ n g) (k : Fin g) :
    p.wireFormula (.gate k) = p.gateFormula k :=
  rfl

/-- The formula of the newly added last gate is `line.op` applied to the formulas of its argument
wires. -/
@[simp] theorem Program.gateFormula_gate_last (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).gateFormula (Fin.last g) =
      .gate line.op fun a => p.wireFormula (line.wires a) := by
  simp [gateFormula, wireFormula]

/-- Appending a gate leaves the formulas of earlier gates unchanged. -/
@[simp] theorem Program.gateFormula_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (k : Fin g) : (p.gate line).gateFormula k.castSucc = p.gateFormula k := by
  simp [gateFormula]

/-- Appending a gate leaves the formulas of earlier wires unchanged. -/
@[simp] theorem Program.wireFormula_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (w : Wire n g) : (p.gate line).wireFormula w.castSucc = p.wireFormula w := by
  cases w <;> simp

/-- The formula of a gate is its operation applied to the formulas of the wires its line reads. -/
theorem Program.gateFormula_eq_gate (p : Program σ n g) (k : Fin g) :
    p.gateFormula k = .gate (p.lines k).op fun a => p.wireFormula ((p.lines k).wires a) := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [gateFormula_gate_last, lines_gate_last]
      simp only [Line.mapWires_op, Line.mapWires_wires, Wire.Renaming.castSucc_apply,
        wireFormula_gate_castSucc]
    | cast k =>
      rw [gateFormula_gate_castSucc, ih, lines_gate_castSucc]
      simp only [Line.mapWires_op, Line.mapWires_wires, Wire.Renaming.castSucc_apply,
        wireFormula_gate_castSucc]

/-- The arguments of the root of the formula of a wire are formulas of wires: the formulas of the
wires of a program are closed under taking arguments. -/
theorem Program.exists_wireFormula_eq_of_eq_gate (p : Program σ n g) {w : Wire n g} {op : σ.Op}
    {args : Fin (σ.Arity op) → Formula σ n} (h : p.wireFormula w = .gate op args)
    (j : Fin (σ.Arity op)) : ∃ w', p.wireFormula w' = args j := by
  cases w with
  | input i => cases h
  | gate k =>
    rw [wireFormula_gate, gateFormula_eq_gate] at h
    cases h
    exact ⟨_, rfl⟩

/-- The formula of a gate computes the gate. -/
@[simp] theorem Program.eval_gateFormula (I : Interpretation σ U) (p : Program σ n g)
    (k : Fin g) (x : Fin n → U) : (p.gateFormula k).eval I x = p.eval I x k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [gateFormula_gate_last, Formula.eval_gate, eval_gate_last, Line.eval]
      congr 1
      funext a
      simp only [Function.comp_apply]
      generalize line.wires a = w
      cases w <;> simp [ih]
    | cast k => rw [gateFormula_gate_castSucc, eval_gate_castSucc, ih]

/-- The formula of a wire computes the wire. -/
@[simp] theorem Program.eval_wireFormula (I : Interpretation σ U) (p : Program σ n g)
    (w : Wire n g) (x : Fin n → U) : (p.wireFormula w).eval I x = p.trace I x w := by
  cases w <;> simp [trace]

/-- The formula of a gate is as deep as the gate, whatever each operation costs. -/
@[simp] theorem Program.depthWith_gateFormula (cost : σ.Op → ℕ) (p : Program σ n g)
    (k : Fin g) : (p.gateFormula k).depthWith cost = p.depthsWith cost k := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    have hw (w : Wire n g) : (p.wireFormula w).depthWith cost = p.wireDepthsWith cost w := by
      cases w <;> simp [ih]
    induction k using Fin.lastCases with
    | last =>
      rw [gateFormula_gate_last, Formula.depthWith_gate, depthsWith_gate_last,
        Line.depthWith_eq_sup]
      simp only [hw]
    | cast k => rw [gateFormula_gate_castSucc, depthsWith_gate_castSucc, ih]

/-- The formula of a wire is as deep as the wire, whatever each operation costs. -/
@[simp] theorem Program.depthWith_wireFormula (cost : σ.Op → ℕ) (p : Program σ n g)
    (w : Wire n g) : (p.wireFormula w).depthWith cost = p.wireDepthsWith cost w := by
  cases w <;> simp

/-- The formula of a wire is as deep as the wire. -/
@[simp] theorem Program.depth_wireFormula (p : Program σ n g) (w : Wire n g) :
    (p.wireFormula w).depth = p.wireDepths w := by
  rw [← Formula.depthWith_one, ← wireDepthsWith_one, ← depthWith_wireFormula]

/-- The formula unfolding output `j` of a circuit. -/
def Circuit.toFormula (C : Circuit σ n m) (j : Fin m) : Formula σ n :=
  C.program.wireFormula (C.outputs j)

section Circuit

variable (C : Circuit σ n m) (j : Fin m)

/-- The formula of an output computes the output. -/
@[simp] theorem Circuit.eval_toFormula (I : Interpretation σ U) (x : Fin n → U) :
    (C.toFormula j).eval I x = C.eval I x j :=
  C.program.eval_wireFormula I _ x

/-- The formula of an output of a circuit computing `f` computes that output of `f`. -/
theorem Circuit.Computes.toFormula {C : Circuit σ n m} {I : Interpretation σ U}
    {f : (Fin n → U) → Fin m → U} (h : C.Computes I f) (j : Fin m) :
    (C.toFormula j).Computes I fun x => f x j := fun x => by
  rw [eval_toFormula, h x]

/-- The formula of an output is as deep as the output, whatever each operation costs. -/
@[simp] theorem Circuit.depthWith_toFormula (cost : σ.Op → ℕ) :
    (C.toFormula j).depthWith cost = C.program.wireDepthsWith cost (C.outputs j) :=
  C.program.depthWith_wireFormula cost _

/-- The formula of an output is no deeper than the circuit, whatever each operation costs. -/
theorem Circuit.depthWith_toFormula_le (cost : σ.Op → ℕ) :
    (C.toFormula j).depthWith cost ≤ C.depthWith cost :=
  (C.depthWith_toFormula j cost).trans_le (C.wireDepthsWith_outputs_le_depthWith cost j)

/-- The formula of an output is as deep as the output. -/
@[simp] theorem Circuit.depth_toFormula : (C.toFormula j).depth = C.outputDepths j :=
  C.program.depth_wireFormula _

/-- The formula of an output is no deeper than the circuit. -/
theorem Circuit.depth_toFormula_le : (C.toFormula j).depth ≤ C.depth :=
  (C.depth_toFormula j).trans_le (C.outputDepths_le_depth j)

/-- Over a basis of fan-in at most `r`, where `2 ≤ r`, the formula of an output of a circuit of
depth `d` has fewer than `r ^ d` operation nodes. -/
theorem Circuit.size_toFormula_lt {r : ℕ} (hr : ∀ op, σ.Arity op ≤ r) (hr₂ : 2 ≤ r) :
    (C.toFormula j).size < r ^ C.depth :=
  ((C.toFormula j).size_lt_pow_depth hr hr₂).trans_le
    (Nat.pow_le_pow_right (by omega) (C.depth_toFormula_le j))

end Circuit

/-! ### Unfolding the circuit of a formula -/

/-- Continuing `p` by `q` leaves the formulas of the wires of `p` unchanged. -/
@[simp] theorem Program.wireFormula_append_castAdd {k g₁ g₂ : ℕ} (p : Program σ n g₁)
    (feed : Fin k → Wire n g₁) (q : Program σ k g₂) (w : Wire n g₁) :
    (p.append feed q).wireFormula (w.castAdd g₂) = p.wireFormula w := by
  induction q with
  | empty => cases w <;> rfl
  | @gate g₂ q line ih =>
    have h : w.castAdd (g₂ + 1) = (w.castAdd g₂).castSucc := by cases w <;> rfl
    rw [h]
    exact (wireFormula_gate_castSucc (p.append feed q) _ _).trans ih

/-- Continuing `p` by `q` on the inputs, a wire of `q` unfolds to its formula in `q`. -/
@[simp] theorem Program.wireFormula_append_input_appendedWire {g₁ g₂ : ℕ} (p : Program σ n g₁)
    (q : Program σ n g₂) (w : Wire n g₂) :
    (p.append Wire.input q).wireFormula (appendedWire Wire.input w) = q.wireFormula w := by
  induction q with
  | empty =>
    cases w with
    | input i => rfl
    | gate j => exact j.elim0
  | @gate g₂ q line ih =>
    cases w with
    | input i => rfl
    | gate j =>
      induction j using Fin.lastCases with
      | last =>
        change (p.append Wire.input q |>.gate _).gateFormula (Fin.last (g₁ + g₂)) = _
        rw [gateFormula_gate_last, wireFormula_gate, gateFormula_gate_last]
        simp only [Line.mapWires_op, Line.mapWires_wires, ih]
      | cast j =>
        change (p.append Wire.input q |>.gate _).wireFormula (appendedWire Wire.input
          (Wire.gate j)).castSucc = _
        rw [wireFormula_gate_castSucc, ih, wireFormula_gate, wireFormula_gate,
          gateFormula_gate_castSucc]

/-- The formulas of the gates of `p` continued by `q` on the inputs are formulas of gates of `p`
or of `q`. -/
theorem Program.gateFormula_append_input_of_forall {g₁ g₂ : ℕ}
    (P : Formula σ n → Prop) (p : Program σ n g₁) (q : Program σ n g₂)
    (hp : ∀ k, P (p.gateFormula k)) (hq : ∀ k, P (q.gateFormula k)) (k : Fin (g₁ + g₂)) :
    P ((p.append Wire.input q).gateFormula k) := by
  induction k using Fin.addCases with
  | left k =>
    simpa using congrArg P (wireFormula_append_castAdd p Wire.input q (.gate k)) ▸ hp k
  | right k =>
    simpa using congrArg P (wireFormula_append_input_appendedWire p q (.gate k)) ▸ hq k

/-- Output `j` of circuits side by side unfolds to the output of the `j`-th circuit. -/
@[simp] theorem Circuit.toFormula_pi {m : ℕ} (cs : Fin m → Circuit σ n 1) (j : Fin m) :
    (Circuit.pi cs).toFormula j = (cs j).toFormula 0 := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    induction j using Fin.lastCases with
    | last =>
      rw [toFormula, Circuit.pi, Circuit.append]
      dsimp only
      rw [show Fin.last m = Fin.natAdd m 0 from rfl, Fin.append_right]
      exact Program.wireFormula_append_input_appendedWire _ _ _
    | cast j =>
      rw [toFormula, Circuit.pi, Circuit.append]
      dsimp only
      rw [show j.castSucc = Fin.castAdd 1 j from rfl, Fin.append_left]
      exact (Program.wireFormula_append_castAdd _ _ _ _).trans (ih _ j)

/-- The formulas of the gates of circuits side by side are formulas of gates of the circuits. -/
theorem Circuit.gateFormula_pi_of_forall (P : Formula σ n → Prop) {m : ℕ}
    (cs : Fin m → Circuit σ n 1) (h : ∀ j k, P ((cs j).program.gateFormula k))
    (k : Fin (Circuit.pi cs).size) :
    P ((Circuit.pi cs).program.gateFormula k) := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    exact Program.gateFormula_append_input_of_forall P _ _ (ih _ fun j => h _) (h _) k

/-- The circuit of a formula unfolds to the formula. -/
@[simp] theorem Formula.toFormula_toCircuit (F : Formula σ n) : F.toCircuit.toFormula 0 = F := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    change (Program.gate _ _).gateFormula (Fin.last _) = _
    rw [Program.gateFormula_gate_last]
    simp only [Line.mapWires_op, Line.mapWires_wires]
    congr 1
    funext a
    exact (Program.wireFormula_append_castAdd _ _ Program.empty _).trans
      ((Circuit.toFormula_pi _ a).trans (ih a))

/-- The formulas of the gates of the circuit of a formula `F` are subformulas of `F`: they satisfy
every property of `F` inherited by the arguments of operation nodes. -/
theorem Formula.gateFormula_toCircuit_of_closed (P : Formula σ n → Prop)
    (hP : ∀ op args j, P (.gate op args) → P (args j)) {F : Formula σ n} (hF : P F)
    (k : Fin F.toCircuit.size) : P (F.toCircuit.program.gateFormula k) := by
  induction F with
  | input i => exact k.elim0
  | gate op args ih =>
    change Fin ((Circuit.pi fun a => (args a).toCircuit).size + 1) at k
    induction k using Fin.lastCases with
    | last =>
      change P ((gate op args).toCircuit.toFormula 0)
      rwa [toFormula_toCircuit]
    | cast k =>
      change P ((Program.gate _ _).gateFormula k.castSucc)
      rw [Program.gateFormula_gate_castSucc]
      exact Circuit.gateFormula_pi_of_forall P _ (fun j => ih j (hP op args j hF)) k

end Cslib.Circuits
