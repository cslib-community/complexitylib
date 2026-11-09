/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Homomorphism
public import Cslib.Computability.Circuit.Synthesis

/-!
# Circuits on truth tables

An interpretation `I` of a signature over a carrier `U` lifts pointwise to the functions `X → U`
(`Cslib.Circuits.Interpretation.pointwise`): an operation applied to functions is applied value by
value. Evaluation at a point `x : X` is a homomorphism from the lifted interpretation to `I`
(`Cslib.Circuits.Interpretation.evalAt`), so the value of every wire of a circuit under the lifted
interpretation is, at each point, the value of that wire under `I`
(`Cslib.Circuits.Program.trace_pointwise_apply`, `Cslib.Circuits.Circuit.eval_pointwise_apply`).

Take `X = Fin n → U` and start from the coordinate projections. Then every wire carries its truth
table, the function it computes (`Cslib.Circuits.Program.trace_pointwise_proj`), so the values of
the wires are exactly the functions available in the program
(`Cslib.Circuits.available_eq_range_trace_pointwise`), and the outputs of a circuit are the
functions it computes (`Cslib.Circuits.Circuit.eval_pointwise_proj`). A circuit computes `f`
exactly when its lifted evaluation at the projections is the truth table of `f`
(`Cslib.Circuits.Circuit.computes_iff_eval_pointwise_proj`). This is the description of a circuit
as a sequence of functions, each obtained by applying a basis operation to earlier ones
[Jukna2012], and it makes truth tables ordinary semantic values: geometric statements about
functions, such as Hamming distances between wires, are statements about values of the lifted
interpretation.

## Main definitions

* `Cslib.Circuits.Interpretation.pointwise`: the pointwise lift of an interpretation.
* `Cslib.Circuits.Interpretation.evalAt`: evaluation at a point, as a homomorphism.

## Main results

* `Cslib.Circuits.Program.trace_pointwise_apply`, `Cslib.Circuits.Circuit.eval_pointwise_apply`:
  lifted evaluation is evaluation at every point.
* `Cslib.Circuits.Program.trace_pointwise_proj`,
  `Cslib.Circuits.available_eq_range_trace_pointwise`: wires carry truth tables.
* `Cslib.Circuits.Circuit.eval_pointwise_proj`,
  `Cslib.Circuits.Circuit.computes_iff_eval_pointwise_proj`: outputs are truth tables.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U : Type*} {n m : ℕ}

/-! ### The pointwise lift -/

/-- The pointwise lift of `I` to functions `X → U`: an operation is applied value by value. -/
def Interpretation.pointwise (X : Type*) (I : Interpretation σ U) : Interpretation σ (X → U) :=
  fun op args x => I op fun i => args i x

/-- Evaluating `I.pointwise X op args` at `x` applies `I op` to the values of `args` at `x`. -/
@[simp] theorem Interpretation.pointwise_apply (X : Type*) (I : Interpretation σ U) (op : σ.Op)
    (args : Fin (σ.Arity op) → X → U) (x : X) :
    I.pointwise X op args x = I op fun i => args i x :=
  rfl

/-- Evaluation at a point is a homomorphism from the pointwise lift. -/
def Interpretation.evalAt (I : Interpretation σ U) {X : Type*} (x : X) :
    Homomorphism (I.pointwise X) I where
  map f := f x
  homomorphic _ _ := rfl

/-- The underlying map of `I.evalAt x` evaluates a function at `x`. -/
@[simp] theorem Interpretation.evalAt_map (I : Interpretation σ U) {X : Type*} (x : X)
    (f : X → U) : (I.evalAt x).map f = f x :=
  rfl

/-! ### Evaluation is pointwise -/

/-- Every wire of a program, under the pointwise lift, takes at each point the value of that wire
under `I`. -/
theorem Program.trace_pointwise_apply {g : ℕ} (p : Program σ n g) (I : Interpretation σ U)
    {X : Type*} (a : Fin n → X → U) (w : Wire n g) (x : X) :
    p.trace (I.pointwise X) a w x = p.trace I (fun j => a j x) w :=
  congrFun (p.map_trace (I.evalAt x) a) w

/-- Every output of a circuit, under the pointwise lift, takes at each point the value of that
output under `I`. -/
theorem Circuit.eval_pointwise_apply (c : Circuit σ n m) (I : Interpretation σ U) {X : Type*}
    (a : Fin n → X → U) (o : Fin m) (x : X) :
    c.eval (I.pointwise X) a o x = c.eval I (fun j => a j x) o :=
  congrFun (c.map_eval (I.evalAt x) a) o

/-! ### Truth tables -/

/-- **Wires carry truth tables.** Under the pointwise lift, started at the coordinate
projections, every wire of a program carries the function it computes. -/
theorem Program.trace_pointwise_proj {g : ℕ} (p : Program σ n g) (I : Interpretation σ U) :
    p.trace (I.pointwise (Fin n → U)) (fun j x => x j) = p.wireFunction I :=
  funext fun w => funext fun x => p.trace_pointwise_apply I _ w x

/-- The functions available in a program are the values of its wires under the pointwise lift,
started at the coordinate projections. -/
theorem available_eq_range_trace_pointwise (I : Interpretation σ U) {g : ℕ} (p : Program σ n g) :
    available I p = Set.range (p.trace (I.pointwise (Fin n → U)) fun j x => x j) := by
  rw [Program.trace_pointwise_proj]
  rfl

/-- **Outputs are truth tables.** Under the pointwise lift, started at the coordinate projections,
every output of a circuit is the function that output computes. -/
theorem Circuit.eval_pointwise_proj (c : Circuit σ n m) (I : Interpretation σ U) (o : Fin m) :
    c.eval (I.pointwise (Fin n → U)) (fun j x => x j) o = fun x => c.eval I x o :=
  funext fun x => c.eval_pointwise_apply I _ o x

/-- A circuit computes `f` exactly when its lifted evaluation at the coordinate projections is
the truth table of `f`. -/
theorem Circuit.computes_iff_eval_pointwise_proj (c : Circuit σ n m) (I : Interpretation σ U)
    (f : (Fin n → U) → Fin m → U) :
    c.Computes I f ↔ c.eval (I.pointwise (Fin n → U)) (fun j x => x j) = fun o x => f x o := by
  simp only [funext_iff, Circuit.eval_pointwise_proj, Circuit.Computes]
  exact forall_comm

end Cslib.Circuits
