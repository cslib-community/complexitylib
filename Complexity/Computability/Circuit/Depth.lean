/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Depth.lean`)

public import Cslib.Computability.Circuit.Depth
public import Complexity.Computability.Circuit.Program
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Depths along program lines, and depths with costs

Every wire read by a gate is shallower than the gate (`Program.wireDepths_lines_lt`), which is what
makes induction on depth go through for programs.

The depth with costs (`Circuit.depthWith cost`) charges `cost op` for a gate of operation `op`
instead of one, so it is the largest total cost of the gates on a path to an output. Unit costs
give `Circuit.depth` (`Circuit.depthWith_one`). With free negations it is the largest number of
AND and OR gates on a path in a circuit over the unbounded fan-in basis, the depth of AC⁰ circuits
with negations at the inputs.

## Main definitions

* `Cslib.Circuits.depthInterpretation`: interpretation computing weighted gate depth.
* `Cslib.Circuits.Line.depthWith`, `Cslib.Circuits.Program.depthsWith`,
  `Cslib.Circuits.Program.wireDepthsWith`, `Cslib.Circuits.Circuit.depthWith`: depths with costs.

## Main results

* `Fin.foldl_max_eq_max_sup`: folding `max` is taking the supremum, so depths are suprema
  (`Cslib.Circuits.Line.depthWith_eq_sup`, `Cslib.Circuits.Circuit.depthWith_eq_sup`).
* `Cslib.Circuits.Program.depths_eq_depth_lines`: the depth of a gate is the depth of its line.
* `Cslib.Circuits.Program.wireDepths_lines_lt`: the wires a gate reads are shallower than it.
* `Cslib.Circuits.Program.depths_pos`: gates have positive depth.
* `Cslib.Circuits.Program.wireDepthsWith_lines_add_le`: with costs, the wires a gate reads are
  shallower than it by at least its cost.
* `Cslib.Circuits.Circuit.depthWith_one`: unit costs give the depth.
* `Cslib.Circuits.Circuit.depthWith_le_iff`, `Cslib.Circuits.Circuit.depthWith_mono`: bounds, and
  monotonicity in the costs.
* `Cslib.Circuits.Circuit.depthWith_le_depth`: costs of at most one never increase the depth.
* `Cslib.Circuits.Circuit.depthWith_le_mul_depth`: if every gate costs at most `b`, the depth with
  costs is at most `b` times the depth.
-/

@[expose] public section

/-- Folding `max` over the values of `f`, from `init`, gives the larger of `init` and their
supremum. -/
theorem Fin.foldl_max_eq_max_sup {α : Type*} [LinearOrder α] [OrderBot α] {m : ℕ} (f : Fin m → α)
    (init : α) :
    Fin.foldl m (fun acc i => max acc (f i)) init = max init (Finset.univ.sup f) := by
  induction m generalizing init with
  | zero => simp
  | succ m ih =>
    rw [Fin.foldl_succ, ih, Fin.univ_succ, Finset.sup_cons, Finset.sup_map]
    simp [max_assoc, Function.comp_def]

namespace Cslib.Circuits

variable {σ : Signature} {n g : ℕ}

/-- A gate is deeper than every wire it reads. -/
theorem Line.wireDepth_lt_depth (line : Line σ n g) (depths : Wire n g → ℕ)
    (a : Fin (σ.Arity line.op)) : depths (line.wires a) < line.depth depths := by
  have h := (line.depth_le_add_one_iff depths (d := line.depth depths - 1)).1
    (by have := line.depth_pos depths; omega) a
  have := line.depth_pos depths
  omega

/-- The depth of a gate of a program is the depth of its line, over the depths of the wires. -/
theorem Program.depths_eq_depth_lines (p : Program σ n g) (k : Fin g) :
    p.depths k = (p.lines k).depth p.wireDepths := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    have h : (fun w => (p.gate line).wireDepths (Wire.Renaming.castSucc w)) = p.wireDepths :=
      funext fun w => by rw [Wire.Renaming.castSucc_apply, Program.wireDepths_gate_castSucc]
    induction k using Fin.lastCases with
    | last =>
      rw [Program.lines_gate_last, Program.depths_gate_last]
      exact congrArg line.depth h.symm
    | cast k =>
      rw [Program.lines_gate_castSucc, Program.depths_gate_castSucc, ih]
      exact congrArg (p.lines k).depth h.symm

/-- The wires read by a gate of a program are shallower than the gate. -/
theorem Program.wireDepths_lines_lt (p : Program σ n g) (k : Fin g)
    (a : Fin (σ.Arity (p.lines k).op)) : p.wireDepths ((p.lines k).wires a) < p.depths k :=
  p.depths_eq_depth_lines k ▸ (p.lines k).wireDepth_lt_depth _ a

/-- Every gate of a program has positive depth. -/
theorem Program.depths_pos (p : Program σ n g) (k : Fin g) : 0 < p.depths k :=
  p.depths_eq_depth_lines k ▸ (p.lines k).depth_pos _

/-! ### Depth with costs

The depth of a wire when each operation `op` costs `cost op` instead of one: the largest total
cost of the gates on a path to the wire. With negations costing nothing, it is the largest number
of AND and OR gates on a path, the depth of AC⁰ circuits with negations at the inputs. -/

/-- Folding `max` over natural numbers from `0` gives their supremum. -/
private theorem foldl_max_zero {m : ℕ} (f : Fin m → ℕ) :
    Fin.foldl m (fun acc i => max acc (f i)) 0 = Finset.univ.sup f := by
  rw [Fin.foldl_max_eq_max_sup, Nat.zero_max]

/-- The depth interpretation takes the largest argument depth and adds the operation's cost.
In particular, a nullary gate contributes its own cost. -/
def depthInterpretation (cost : σ.Op → ℕ) : Interpretation σ ℕ :=
  fun op depths => Fin.foldl (σ.Arity op) (fun depth k => max depth (depths k)) 0 + cost op

/-- The depth of a line when its operation costs `cost op`. -/
def Line.depthWith (cost : σ.Op → ℕ) (line : Line σ n g) (wireDepths : Wire n g → ℕ) : ℕ :=
  Fin.foldl (σ.Arity line.op) (fun depth k => max depth (wireDepths (line.wires k))) 0 +
    cost line.op

/-- The depth of a line with costs is the largest depth of the wires it reads plus its cost. -/
theorem Line.depthWith_eq_sup (cost : σ.Op → ℕ) (line : Line σ n g) (depths : Wire n g → ℕ) :
    line.depthWith cost depths = (Finset.univ.sup fun a => depths (line.wires a)) + cost line.op :=
  congrArg (· + cost line.op) (foldl_max_zero _)

/-- A line is at least as deep as its cost. -/
theorem Line.cost_le_depthWith (cost : σ.Op → ℕ) (line : Line σ n g) (depths : Wire n g → ℕ) :
    cost line.op ≤ line.depthWith cost depths :=
  Nat.le_add_left _ _

/-- A line is at least as deep as every wire it reads plus its cost. -/
theorem Line.wireDepth_add_le_depthWith (cost : σ.Op → ℕ) (line : Line σ n g)
    (depths : Wire n g → ℕ) (a : Fin (σ.Arity line.op)) :
    depths (line.wires a) + cost line.op ≤ line.depthWith cost depths := by
  rw [Line.depthWith_eq_sup]
  exact Nat.add_le_add_right
    (Finset.le_sup (f := fun a => depths (line.wires a)) (Finset.mem_univ a)) _

/-- With unit costs, `Line.depthWith` is `Line.depth`. -/
@[simp] theorem Line.depthWith_one (line : Line σ n g) (depths : Wire n g → ℕ) :
    line.depthWith 1 depths = line.depth depths := by
  simp only [Line.depthWith, Line.depth, Pi.one_apply]
  omega

/-- Raising argument depths by at most `D` raises an operation's depth by at most `D`. -/
theorem depthInterpretation_le_add (cost : σ.Op → ℕ) (op : σ.Op)
    {depths depths' : Fin (σ.Arity op) → ℕ} {D : ℕ} (h : ∀ a, depths a ≤ depths' a + D) :
    depthInterpretation cost op depths ≤ depthInterpretation cost op depths' + D := by
  have : Finset.univ.sup depths ≤ Finset.univ.sup depths' + D :=
    Finset.sup_le fun a _ => (h a).trans (Nat.add_le_add_right
      (Finset.le_sup (f := depths') (Finset.mem_univ a)) _)
  simp only [depthInterpretation, foldl_max_zero]
  lia

/-- Raising the depths of the wires by at most `D` raises the depth of a line by at most `D`. -/
theorem Line.depthWith_le_add (cost : σ.Op → ℕ) (line : Line σ n g) {depths depths' : Wire n g → ℕ}
    {D : ℕ} (h : ∀ a, depths (line.wires a) ≤ depths' (line.wires a) + D) :
    line.depthWith cost depths ≤ line.depthWith cost depths' + D :=
  depthInterpretation_le_add cost line.op h

/-- A line reading only wires of depth zero has the depth of its cost. -/
theorem Line.depthWith_eq_cost (cost : σ.Op → ℕ) (line : Line σ n g) {depths : Wire n g → ℕ}
    (h : ∀ a, depths (line.wires a) = 0) : line.depthWith cost depths = cost line.op := by
  rw [Line.depthWith_eq_sup, (Finset.sup_eq_bot_iff _ _).2 fun a _ => h a, Nat.bot_eq_zero,
    zero_add]

/-- `Line.depthWith` is monotone in the costs and in the depths of the wires. -/
theorem Line.depthWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    {depths depths' : Wire n g → ℕ} (hdepths : ∀ w, depths w ≤ depths' w) (line : Line σ n g) :
    line.depthWith cost depths ≤ line.depthWith cost' depths' := by
  rw [Line.depthWith_eq_sup, Line.depthWith_eq_sup]
  exact Nat.add_le_add (Finset.sup_mono_fun fun _ _ => hdepths _) (hcost _)

/-- The depth of every gate is evaluation in the depth interpretation, with zero-depth inputs. -/
def Program.depthsWith (cost : σ.Op → ℕ) (p : Program σ n g) : Fin g → ℕ :=
  p.eval (depthInterpretation cost) (fun _ => 0)

/-- The depth of every wire of a program when each operation `op` costs `cost op`. -/
def Program.wireDepthsWith (cost : σ.Op → ℕ) (p : Program σ n g) : Wire n g → ℕ :=
  Wire.elim (fun _ => 0) (p.depthsWith cost)

/-- Every input wire has depth `0` under `wireDepthsWith`. -/
@[simp] theorem Program.wireDepthsWith_input (cost : σ.Op → ℕ) (p : Program σ n g) (i : Fin n) :
    p.wireDepthsWith cost (.input i) = 0 := rfl

/-- The depth of a gate wire under `wireDepthsWith` is the weighted depth of that gate. -/
@[simp] theorem Program.wireDepthsWith_gateWire (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g) :
    p.wireDepthsWith cost (.gate k) = p.depthsWith cost k := rfl

/-- The weighted depth of the last gate in `p.gate line` is `line.depthWith` over `p`'s wire
depths. -/
@[simp] theorem Program.depthsWith_gate_last (cost : σ.Op → ℕ) (p : Program σ n g)
    (line : Line σ n g) :
    (p.gate line).depthsWith cost (Fin.last g) = line.depthWith cost (p.wireDepthsWith cost) := by
  exact p.eval_gate_last line (depthInterpretation cost) (fun _ => 0)

/-- Appending a gate line leaves the weighted depths of earlier gates unchanged. -/
@[simp] theorem Program.depthsWith_gate_castSucc (cost : σ.Op → ℕ) (p : Program σ n g)
    (line : Line σ n g) (j : Fin g) :
    (p.gate line).depthsWith cost j.castSucc = p.depthsWith cost j := by
  exact p.eval_gate_castSucc line (depthInterpretation cost) (fun _ => 0) j

/-- Appending a gate line leaves the weighted depths of earlier wires unchanged. -/
@[simp] theorem Program.wireDepthsWith_gate_castSucc (cost : σ.Op → ℕ) (p : Program σ n g)
    (line : Line σ n g) (w : Wire n g) :
    (p.gate line).wireDepthsWith cost w.castSucc = p.wireDepthsWith cost w := by
  cases w <;> simp

/-- The depth of a gate is the depth of its line over the depths of the wires. -/
theorem Program.depthsWith_eq_depthWith_lines (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g) :
    p.depthsWith cost k = (p.lines k).depthWith cost (p.wireDepthsWith cost) :=
  (p.lines_eval (depthInterpretation cost) (fun _ => 0) k).symm

/-- A gate is at least as deep as its cost. -/
theorem Program.cost_le_depthsWith (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g) :
    cost (p.lines k).op ≤ p.depthsWith cost k :=
  p.depthsWith_eq_depthWith_lines cost k ▸ (p.lines k).cost_le_depthWith cost _

/-- With unit costs, `Program.depthsWith` is `Program.depths`. -/
@[simp] theorem Program.depthsWith_one (p : Program σ n g) :
    p.depthsWith 1 = p.depths := by
  symm
  apply p.eq_eval_of_forall_lines_eval
  intro k
  change (p.lines k).depthWith 1 p.wireDepths = p.depths k
  rw [Line.depthWith_one, p.depths_eq_depth_lines]

/-- With unit costs, `Program.wireDepthsWith` is `Program.wireDepths`. -/
@[simp] theorem Program.wireDepthsWith_one (p : Program σ n g) :
    p.wireDepthsWith 1 = p.wireDepths := by
  simp [Program.wireDepthsWith, Program.wireDepths]

/-- `Program.depthsWith` is monotone in the costs. -/
theorem Program.depthsWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    (p : Program σ n g) (k : Fin g) : p.depthsWith cost k ≤ p.depthsWith cost' k := by
  apply p.eval_rel (· ≤ ·) (fun _ => le_rfl) _ k
  intro k a b hab
  simp only [depthInterpretation, foldl_max_zero]
  exact Nat.add_le_add (Finset.sup_mono_fun fun i _ => hab i) (hcost _)

/-- `Program.wireDepthsWith` is monotone in the costs. -/
theorem Program.wireDepthsWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    (p : Program σ n g) (w : Wire n g) : p.wireDepthsWith cost w ≤ p.wireDepthsWith cost' w := by
  cases w <;> simp [p.depthsWith_mono hcost]

/-- The wires read by a gate are shallower than the gate by at least its cost. -/
theorem Program.wireDepthsWith_lines_add_le (cost : σ.Op → ℕ) (p : Program σ n g) (k : Fin g)
    (a : Fin (σ.Arity (p.lines k).op)) :
    p.wireDepthsWith cost ((p.lines k).wires a) + cost (p.lines k).op ≤ p.depthsWith cost k :=
  p.depthsWith_eq_depthWith_lines cost k ▸ (p.lines k).wireDepth_add_le_depthWith cost _ a

/-- The largest depth of an output when each operation `op` costs `cost op`. -/
def Circuit.depthWith (cost : σ.Op → ℕ) {m : ℕ} (c : Circuit σ n m) : ℕ :=
  Fin.foldl m (fun depth k => max depth (c.program.wireDepthsWith cost (c.outputs k))) 0

/-- The depth of a circuit with costs is the largest depth of its outputs. -/
theorem Circuit.depthWith_eq_sup (cost : σ.Op → ℕ) {m : ℕ} (c : Circuit σ n m) :
    c.depthWith cost = Finset.univ.sup fun j => c.program.wireDepthsWith cost (c.outputs j) :=
  foldl_max_zero _

/-- A circuit has depth at most `D` with costs exactly when all its outputs do. -/
theorem Circuit.depthWith_le_iff (cost : σ.Op → ℕ) {m : ℕ} (c : Circuit σ n m) {D : ℕ} :
    c.depthWith cost ≤ D ↔ ∀ j, c.program.wireDepthsWith cost (c.outputs j) ≤ D := by
  simp [Circuit.depthWith_eq_sup]

/-- Every output is at most as deep, with costs, as the circuit. -/
theorem Circuit.wireDepthsWith_outputs_le_depthWith (cost : σ.Op → ℕ) {m : ℕ}
    (c : Circuit σ n m) (j : Fin m) :
    c.program.wireDepthsWith cost (c.outputs j) ≤ c.depthWith cost :=
  (c.depthWith_le_iff cost).1 le_rfl j

/-- With unit costs, `Circuit.depthWith` is `Circuit.depth`. -/
@[simp] theorem Circuit.depthWith_one {m : ℕ} (c : Circuit σ n m) :
    c.depthWith 1 = c.depth := by
  simp [Circuit.depthWith, Circuit.depth, Circuit.outputDepths]

/-- `Circuit.depthWith` is monotone in the costs. -/
theorem Circuit.depthWith_mono {cost cost' : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ cost' op)
    {m : ℕ} (c : Circuit σ n m) : c.depthWith cost ≤ c.depthWith cost' :=
  (c.depthWith_le_iff cost).2 fun j =>
    (c.program.wireDepthsWith_mono hcost _).trans (c.wireDepthsWith_outputs_le_depthWith cost' j)

/-- A pure input-wiring circuit has weighted depth `0`. -/
@[simp] theorem Circuit.depthWith_wiring (cost : σ.Op → ℕ) {m : ℕ} (select : Fin m → Fin n) :
    (Circuit.wiring σ select).depthWith cost = 0 :=
  Nat.eq_zero_of_le_zero <| (Circuit.depthWith_le_iff cost _).2 fun _ => le_rfl

/-- A circuit with `0` outputs has weighted depth `0`. -/
@[simp] theorem Circuit.depthWith_zero_outputs (cost : σ.Op → ℕ) (c : Circuit σ n 0) :
    c.depthWith cost = 0 :=
  rfl

/-- Costs of at most one never increase the depth. -/
theorem Circuit.depthWith_le_depth {cost : σ.Op → ℕ} (hcost : ∀ op, cost op ≤ 1) {m : ℕ}
    (c : Circuit σ n m) : c.depthWith cost ≤ c.depth :=
  c.depthWith_one ▸ c.depthWith_mono hcost

/-- If every gate of a program costs at most `b`, every gate is at most `b` times as deep with
costs as without. -/
theorem Program.depthsWith_le_mul_depths {cost : σ.Op → ℕ} {b : ℕ} (p : Program σ n g)
    (h : ∀ k, cost (p.lines k).op ≤ b) (k : Fin g) : p.depthsWith cost k ≤ b * p.depths k := by
  rw [← p.depthsWith_one]
  apply p.eval_rel (fun a d => a ≤ b * d) (fun _ => by simp) _ k
  intro j a d had
  simp only [depthInterpretation, foldl_max_zero, Pi.one_apply, Nat.mul_add, Nat.mul_one]
  apply Nat.add_le_add _ (h j)
  exact Finset.sup_le fun i _ => (had i).trans
    (Nat.mul_le_mul_left b (Finset.le_sup (f := d) (Finset.mem_univ i)))

/-- If every gate of a program costs at most `b`, every wire is at most `b` times as deep with
costs as without. -/
theorem Program.wireDepthsWith_le_mul_wireDepths {cost : σ.Op → ℕ} {b : ℕ} (p : Program σ n g)
    (h : ∀ k, cost (p.lines k).op ≤ b) (w : Wire n g) :
    p.wireDepthsWith cost w ≤ b * p.wireDepths w := by
  cases w with
  | input i => simp
  | gate j => exact p.depthsWith_le_mul_depths h j

/-- If every gate of a circuit costs at most `b`, its depth with costs is at most `b` times its
depth. -/
theorem Circuit.depthWith_le_mul_depth {cost : σ.Op → ℕ} {b m : ℕ} (c : Circuit σ n m)
    (h : ∀ k, cost (c.program.lines k).op ≤ b) : c.depthWith cost ≤ b * c.depth :=
  (c.depthWith_le_iff cost).2 fun j => (c.program.wireDepthsWith_le_mul_wireDepths h _).trans
    (Nat.mul_le_mul_left b (c.outputDepths_le_depth j))

end Cslib.Circuits
