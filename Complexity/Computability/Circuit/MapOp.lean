/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Formula
public import Complexity.Computability.Circuit.MapLines
public import Complexity.Computability.Circuit.SignatureHom

/-!
# Translating circuits and formulas between signatures

A map of signatures `φ : σ.Hom τ` (`Cslib.Circuits.Signature.Hom`) sends each operation of `σ` to
an operation of `τ` of the same
arity. It is a map of the operation symbols, unlike cslib's `Homomorphism`, which maps the carriers
of two interpretations of one signature. It translates programs and circuits over `σ` into
programs and circuits over `τ` gate by gate (`Circuit.mapOp`), keeping the size and the depth
(`Circuit.size_mapOp`, `Circuit.depth_mapOp`), and when `φ` keeps the meaning of every operation
(`Signature.Hom.Preserves`) the translated circuit computes the same function
(`Circuit.eval_mapOp`). This embeds circuits over a basis into circuits over a larger basis; it is
analogous to cslib's `Program.simulate` with a budget of one gate for every operation. Formulas
are translated likewise (`Formula.mapOp`), keeping their function, size, leaves and depth.

## Main definitions

* `Cslib.Circuits.Line.mapOp`, `Cslib.Circuits.Program.mapOp`, `Cslib.Circuits.Circuit.mapOp`,
  `Cslib.Circuits.Formula.mapOp`: the translation along a map of signatures.

## Main results

* `Cslib.Circuits.Circuit.eval_mapOp`, `Cslib.Circuits.Circuit.Computes.mapOp`: the translation
  computes the same function along a meaning-preserving map.
* `Cslib.Circuits.Circuit.size_mapOp`, `Cslib.Circuits.Circuit.depth_mapOp`: size and depth are
  kept.
* `Cslib.Circuits.Circuit.mapOp_id`, `Cslib.Circuits.Circuit.mapOp_comp`: translation is
  functorial.
* `Cslib.Circuits.Formula.eval_mapOp`, `Cslib.Circuits.Formula.depthWith_mapOp`: a translated
  formula computes the same function, with depth measured by the costs of the images.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ τ υ : Signature} {n g m : ℕ} {U : Type*}

variable (φ : σ.Hom τ)

/-- The line performing `φ op` on the wires of `line`. -/
def Line.mapOp (line : Line σ n g) : Line τ n g :=
  ⟨φ line.op, fun a => line.wires (Fin.cast (φ.arity_eq line.op) a)⟩

/-- The program performing `φ op` in place of each operation `op`: its lines translated by
`Line.mapOp`. -/
def Program.mapOp (p : Program σ n g) : Program τ n g :=
  p.mapLines (Line.mapOp φ)

/-- The circuit performing `φ op` in place of each operation `op`. -/
def Circuit.mapOp (c : Circuit σ n m) : Circuit τ n m :=
  c.mapLines (Line.mapOp φ)

variable {φ}

/-- Translating a line along `φ` applies `φ` to its operation symbol. -/
@[simp] theorem Line.mapOp_op (line : Line σ n g) : (line.mapOp φ).op = φ line.op :=
  rfl

/-- Translating a line along `φ` casts its argument wires along `φ.arity_eq`. -/
@[simp] theorem Line.mapOp_wires (line : Line σ n g) (a : Fin (τ.Arity (φ line.op))) :
    (line.mapOp φ).wires a = line.wires (Fin.cast (φ.arity_eq line.op) a) :=
  rfl

/-- Translating the empty program yields the empty program. -/
@[simp] theorem Program.mapOp_empty : (Program.empty : Program σ n 0).mapOp φ = .empty :=
  rfl

/-- Translating a program extended by a gate translates both the prefix and the gate line. -/
@[simp] theorem Program.mapOp_gate (p : Program σ n g) (line : Line σ n g) :
    (p.gate line).mapOp φ = (p.mapOp φ).gate (line.mapOp φ) :=
  rfl

/-- The program of a translated circuit is the translated program. -/
@[simp] theorem Circuit.mapOp_program (c : Circuit σ n m) :
    (c.mapOp φ).program = c.program.mapOp φ :=
  rfl

/-- Translating a circuit preserves its output wires. -/
@[simp] theorem Circuit.mapOp_outputs (c : Circuit σ n m) : (c.mapOp φ).outputs = c.outputs :=
  rfl

/-- Translating operation symbols preserves every fan-in bound. -/
@[simp] theorem Program.fanInAtMost_mapOp (p : Program σ n g) (r : ℕ) :
    (p.mapOp φ).FanInAtMost r ↔ p.FanInAtMost r := by
  induction p with
  | empty => rfl
  | gate p line ih =>
    simp only [Program.mapOp_gate, Program.FanInAtMost, Line.mapOp_op, ih]
    have h : τ.Arity (φ line.op) = σ.Arity line.op := φ.arity_eq line.op
    rw [h]

/-- Translating operation symbols preserves every circuit fan-in bound. -/
@[simp] theorem Circuit.fanInAtMost_mapOp (c : Circuit σ n m) (r : ℕ) :
    (c.mapOp φ).FanInAtMost r ↔ c.FanInAtMost r :=
  Program.fanInAtMost_mapOp c.program r

/-- Translating a line along the identity signature homomorphism leaves it unchanged. -/
@[simp] theorem Line.mapOp_id (line : Line σ n g) : line.mapOp (Signature.Hom.id σ) = line :=
  rfl

/-- Translating a line along a composition translates it twice. -/
theorem Line.mapOp_comp (ψ : τ.Hom υ) (line : Line σ n g) :
    line.mapOp (ψ.comp φ) = (line.mapOp φ).mapOp ψ :=
  rfl

/-- Translating a program along the identity signature homomorphism leaves it unchanged. -/
@[simp] theorem Program.mapOp_id (p : Program σ n g) : p.mapOp (Signature.Hom.id σ) = p := by
  induction p with
  | empty => rfl
  | gate p line ih => rw [mapOp_gate, ih, Line.mapOp_id]

/-- Translating a program along a composition translates it twice. -/
theorem Program.mapOp_comp (ψ : τ.Hom υ) (p : Program σ n g) :
    p.mapOp (ψ.comp φ) = (p.mapOp φ).mapOp ψ := by
  induction p with
  | empty => rfl
  | gate p line ih => rw [mapOp_gate, ih, Line.mapOp_comp, mapOp_gate, mapOp_gate]

/-- Translating a circuit along the identity signature homomorphism leaves it unchanged. -/
@[simp] theorem Circuit.mapOp_id (c : Circuit σ n m) : c.mapOp (Signature.Hom.id σ) = c := by
  change (⟨c.program.mapOp _, c.outputs⟩ : Circuit σ n m) = c
  rw [Program.mapOp_id]

/-- Translating a circuit along a composition translates it twice. -/
theorem Circuit.mapOp_comp (ψ : τ.Hom υ) (c : Circuit σ n m) :
    c.mapOp (ψ.comp φ) = (c.mapOp φ).mapOp ψ := by
  change (⟨c.program.mapOp (ψ.comp φ), c.outputs⟩ : Circuit υ n m) =
    ⟨(c.program.mapOp φ).mapOp ψ, c.outputs⟩
  rw [Program.mapOp_comp]

/-- Translating operation symbols preserves circuit size. -/
@[simp] theorem Circuit.size_mapOp (c : Circuit σ n m) : (c.mapOp φ).size = c.size :=
  rfl

/-- A translated line has the same depth. -/
theorem Line.depth_mapOp (line : Line σ n g) (depths : Wire n g → ℕ) :
    (line.mapOp φ).depth depths = line.depth depths :=
  le_antisymm
    ((Line.depth_le_add_one_iff _ _).2 fun _ => (line.depth_le_add_one_iff depths).1 le_rfl _)
    ((Line.depth_le_add_one_iff _ _).2 fun a => by
      simpa using ((line.mapOp φ).depth_le_add_one_iff depths).1 le_rfl
        (Fin.cast (φ.arity_eq line.op).symm a))

/-- The translated program has the same gate depths. -/
theorem Program.depths_mapOp (p : Program σ n g) : (p.mapOp φ).depths = p.depths :=
  p.depths_mapLines Line.depth_mapOp

/-- Translating operation symbols preserves circuit depth. -/
@[simp] theorem Circuit.depth_mapOp (c : Circuit σ n m) : (c.mapOp φ).depth = c.depth :=
  c.depth_mapLines Line.depth_mapOp

variable {I : Interpretation σ U} {J : Interpretation τ U}

/-- The translated program computes the same gate values along a meaning-preserving map. -/
theorem Program.eval_mapOp [hφ : φ.Preserves I J] (p : Program σ n g) (x : Fin n → U) :
    (p.mapOp φ).eval J x = p.eval I x :=
  p.eval_mapLines (f := Line.mapOp φ)
    (fun line x gates => hφ.interpret_eq line.op (Wire.elim x gates ∘ line.wires)) x

/-- **The translated circuit computes the same function** along a meaning-preserving map. -/
theorem Circuit.eval_mapOp [hφ : φ.Preserves I J] (c : Circuit σ n m) (x : Fin n → U) :
    (c.mapOp φ).eval J x = c.eval I x :=
  congrFun (c.eval_mapLines (f := Line.mapOp φ)
    (fun line x gates => hφ.interpret_eq line.op (Wire.elim x gates ∘ line.wires))) x

/-- A circuit translated along a meaning-preserving map computes what the circuit computes. -/
theorem Circuit.Computes.mapOp [φ.Preserves I J] {c : Circuit σ n m}
    {f : (Fin n → U) → Fin m → U} (hc : c.Computes I f) : (c.mapOp φ).Computes J f :=
  fun x => (Circuit.eval_mapOp c x).trans (hc x)

/-! ### Formulas -/

variable (φ) in
/-- The formula performing `φ op` in place of each operation `op`. -/
def Formula.mapOp : Formula σ n → Formula τ n
  | .input i => .input i
  | .gate op args => .gate (φ op) fun a => (args (Fin.cast (φ.arity_eq op) a)).mapOp

/-- Translating an input leaf formula yields the same input leaf. -/
@[simp] theorem Formula.mapOp_input (i : Fin n) :
    (Formula.input i : Formula σ n).mapOp φ = .input i :=
  rfl

/-- Translating a gate formula translates its operation symbol and recursively translates its
arguments. -/
@[simp] theorem Formula.mapOp_gate (op : σ.Op) (args : Fin (σ.Arity op) → Formula σ n) :
    (Formula.gate op args).mapOp φ =
      .gate (φ op) fun a => (args (Fin.cast (φ.arity_eq op) a)).mapOp φ :=
  rfl

/-- Reindexing along `Fin.cast` keeps a sum. -/
private theorem sum_cast {k l : ℕ} (h : k = l) (f : Fin l → ℕ) :
    ∑ a : Fin k, f (Fin.cast h a) = ∑ j, f j := by
  subst h
  rfl

/-- Reindexing along `Fin.cast` keeps a supremum. -/
private theorem sup_cast {k l : ℕ} (h : k = l) (f : Fin l → ℕ) :
    (Finset.univ.sup fun a : Fin k => f (Fin.cast h a)) = Finset.univ.sup f := by
  subst h
  rfl

/-- The translated formula has the same depth when `φ op` costs what `op` does. -/
@[simp] theorem Formula.depthWith_mapOp (cost : τ.Op → ℕ) (F : Formula σ n) :
    (F.mapOp φ).depthWith cost = F.depthWith (cost ∘ φ) := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [Formula.mapOp_gate, Formula.depthWith_gate, ih, Function.comp_apply]
    exact congrArg (· + cost (φ op))
      (sup_cast (φ.arity_eq op) fun j => (args j).depthWith (cost ∘ φ))

/-- The translated formula has the same size. -/
@[simp] theorem Formula.size_mapOp (F : Formula σ n) : (F.mapOp φ).size = F.size := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [Formula.mapOp_gate, Formula.size_gate, ih]
    exact congrArg (· + 1) (sum_cast (φ.arity_eq op) fun j => (args j).size)

/-- The translated formula has the same leaves. -/
@[simp] theorem Formula.leafSize_mapOp (F : Formula σ n) : (F.mapOp φ).leafSize = F.leafSize := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [Formula.mapOp_gate, Formula.leafSize_gate, ih]
    exact sum_cast (φ.arity_eq op) fun j => (args j).leafSize

/-- **The translated formula computes the same function** along a meaning-preserving map. -/
theorem Formula.eval_mapOp [hφ : φ.Preserves I J] (F : Formula σ n) (x : Fin n → U) :
    (F.mapOp φ).eval J x = F.eval I x := by
  induction F with
  | input i => rfl
  | gate op args ih =>
    simp only [Formula.mapOp_gate, Formula.eval_gate, ih]
    exact hφ.interpret_eq op fun j => (args j).eval I x

/-- A formula translated along a meaning-preserving map computes what the formula computes. -/
theorem Formula.Computes.mapOp [φ.Preserves I J] {F : Formula σ n} {f : (Fin n → U) → U}
    (hF : F.Computes I f) : (F.mapOp φ).Computes J f :=
  fun x => (Formula.eval_mapOp F x).trans (hF x)

end Cslib.Circuits
