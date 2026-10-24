/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.FanInTwo
import Mathlib.Algebra.BigOperators.Fin

/-!
# Symmetric gates reading their wires with multiplicities

The extra gates of the bases of TC (majority) and of ACⁱ[q] (`MOD_q`) are symmetric: their value
depends only on the number of their true arguments. Unlike a conjunction or a disjunction, such a
gate depends on how often it reads a wire, so its fan-in is not bounded by the size of the circuit
(`Unbounded.dedup` does not apply). It is determined, however, by the distinct wires it reads and
their multiplicities.

`Unbounded.multSignature` is the unbounded fan-in basis together with a gate `.gate N mult` for
every `N` and every `mult : Fin N → ℕ`, reading `N` wires, the `i`th of them `mult i` times; under
`Unbounded.multInterpretation G` it computes `G (∑ i, mult i)` of the number of true arguments
counted with multiplicity (`Unbounded.multWeight`). Replacing every gate of a circuit over
`Unbounded.extSignature` by the gate reading its distinct wires with their multiplicities, and
every conjunction and disjunction by `Unbounded.dedupLine`, gives a circuit over `multSignature`
(`Unbounded.multCircuit`) computing the same function, when the extra gates of `m` arguments compute
`G m` of the number of their true arguments (`Unbounded.eval_multCircuit`), with the same size, no
larger depth, and every gate reading at most `n + s` wires (`Unbounded.arity_lines_multCircuit_le`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.MultOp`, `Cslib.Circuits.Boolean.Unbounded.MultOp.arity`,
  `Cslib.Circuits.Boolean.Unbounded.multSignature`,
  `Cslib.Circuits.Boolean.Unbounded.multInterpretation`: symmetric gates with multiplicities.
* `Cslib.Circuits.Boolean.Unbounded.multLine`, `Cslib.Circuits.Boolean.Unbounded.multCircuit`:
  the line and circuit whose symmetric gates read their distinct wires with multiplicities.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_multCircuit`,
  `Cslib.Circuits.Boolean.Unbounded.depth_multCircuit_le`,
  `Cslib.Circuits.Boolean.Unbounded.arity_lines_multCircuit_le`: aggregating multiplicities keeps
  the function and the size, makes no gate deeper, and bounds the fan-in by the number of inputs
  and gates.

## References

* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Unbounded

open Finset

variable {n g m : ℕ}

/-- The operations of the unbounded fan-in basis, and a symmetric gate reading `N` wires, the `i`th
of them `mult i` times. -/
inductive MultOp where
  /-- An operation of the unbounded fan-in basis. -/
  | ac (op : Op)
  /-- A symmetric gate reading `N` wires with multiplicities `mult`. -/
  | gate (N : ℕ) (mult : Fin N → ℕ)

/-- The arity of an operation: the number of distinct wires a symmetric gate reads. -/
abbrev MultOp.arity : MultOp → ℕ
  | .ac op => op.arity
  | .gate N _ => N

/-- The signature of the unbounded fan-in basis with symmetric gates reading their wires with
multiplicities. It is reducible, so that case analysis on its operations sees their arities. -/
abbrev multSignature : Signature :=
  ⟨MultOp, MultOp.arity⟩

/-- The number of true arguments, the `i`th counted `mult i` times. -/
def multWeight {N : ℕ} (mult : Fin N → ℕ) (x : Fin N → Bool) : ℕ :=
  ∑ i, mult i * (x i).toNat

/-- The meaning of the basis with symmetric gates: the gate of multiplicities `mult` computes
`G (∑ i, mult i)` of the number of true arguments counted with multiplicity. -/
def multInterpretation (G : ℕ → ℕ → Bool) : Interpretation multSignature Bool
  | .ac op, x => interpretation op x
  | .gate _ mult, x => G (∑ i, mult i) (multWeight mult x)

/-- Evaluating an unbounded fan-in gate `.ac op` under `multInterpretation G` agrees with
`interpretation op`. -/
@[simp] theorem multInterpretation_ac (G : ℕ → ℕ → Bool) (op : Op) (x : Fin op.arity → Bool) :
    multInterpretation G (.ac op) x = interpretation op x :=
  rfl

/-- Evaluating a symmetric gate `.gate N mult` under `multInterpretation G` applies
`G (∑ i, mult i)` to `multWeight mult x`. -/
@[simp] theorem multInterpretation_gate (G : ℕ → ℕ → Bool) (N : ℕ) (mult : Fin N → ℕ)
    (x : Fin N → Bool) :
    multInterpretation G (.gate N mult) x = G (∑ i, mult i) (multWeight mult x) :=
  rfl

/-! ### Aggregating multiplicities -/

/-- The line reading the distinct wires of `line`: a conjunction or disjunction reads each once,
and a symmetric gate reads each with its multiplicity in `line`. -/
def multLine : Line extSignature n g → Line multSignature n g
  | ⟨.ac op, w⟩ => ⟨.ac (dedupLine ⟨op, w⟩).op, (dedupLine ⟨op, w⟩).wires⟩
  | ⟨.gate _, w⟩ => ⟨.gate (List.ofFn w).dedup.length
      fun j => (List.ofFn w).count (List.ofFn w).dedup[j.1], fun j => (List.ofFn w).dedup[j.1]⟩

private theorem sum_map_filter_eq {α : Type*} (p : α → Bool) (f : α → ℕ) (l : List α) :
    ((l.filter p).map f).sum = (l.map fun a => f a * (p a).toNat).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih]

private theorem countP_eq_sum {α : Type*} (p : α → Bool) (l : List α) :
    l.countP p = (l.map fun a => (p a).toNat).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [h, ih, add_comm]

/-- Reading the distinct wires with their multiplicities counts the true arguments. -/
private theorem multWeight_count_dedup {k : ℕ} (w : Fin k → Wire n g) (v : Wire n g → Bool) :
    multWeight
        (fun j : Fin (List.ofFn w).dedup.length => (List.ofFn w).count (List.ofFn w).dedup[j.1])
        (fun j => v (List.ofFn w).dedup[j.1]) = BitString.weight (v ∘ w) := by
  rw [multWeight, Fin.sum_univ_fun_getElem (List.ofFn w).dedup
      (fun a => (List.ofFn w).count a * (v a).toNat), ← sum_map_filter_eq,
    List.sum_map_count_dedup_filter_eq_countP, countP_eq_sum, List.map_ofFn, List.sum_ofFn,
    BitString.weight_eq_sum_toNat]
  rfl

/-- Reading the distinct wires with their multiplicities keeps the number of arguments. -/
private theorem sum_count_dedup {k : ℕ} (w : Fin k → Wire n g) :
    ∑ j : Fin (List.ofFn w).dedup.length, (List.ofFn w).count (List.ofFn w).dedup[j.1] = k := by
  rw [Fin.sum_univ_fun_getElem (List.ofFn w).dedup (fun a => (List.ofFn w).count a),
    List.sum_map_count_dedup_eq_length, List.length_ofFn]

/-- Aggregating multiplicities keeps the value of a line, when the extra gate of `m` arguments
computes `G m` of the number of its true arguments. -/
theorem eval_multLine {G : ℕ → ℕ → Bool} {f : ∀ m, BooleanFunction m}
    (hf : ∀ m x, f m x = G m (BitString.weight x)) (line : Line extSignature n g)
    (x : Fin n → Bool) (gates : Fin g → Bool) :
    (multLine line).eval (multInterpretation G) x gates =
      line.eval (extInterpretation f) x gates := by
  obtain ⟨op, w⟩ := line
  cases op with
  | ac op => exact eval_dedupLine ⟨op, w⟩ x gates
  | gate k =>
    change G _ (multWeight _ _) = f k _
    rw [hf, sum_count_dedup]
    exact congrArg (G k) (multWeight_count_dedup w (Wire.elim x gates))

/-- Aggregating multiplicities makes no line deeper. -/
theorem depth_multLine_le (line : Line extSignature n g) (depths : Wire n g → ℕ) :
    (multLine line).depth depths ≤ line.depth depths := by
  obtain ⟨op, w⟩ := line
  cases op with
  | ac op => exact depth_dedupLine_le ⟨op, w⟩ depths
  | gate k =>
    set line : Line extSignature n g := ⟨.gate k, w⟩
    have hpos := line.depth_pos depths
    have hle : ∀ a, depths (w a) ≤ line.depth depths - 1 := fun a => by
      have : depths (w a) < line.depth depths := line.wireDepth_lt_depth depths a
      omega
    refine ((Line.depth_le_add_one_iff _ depths (d := line.depth depths - 1)).2 fun j => ?_).trans
      (by omega)
    have hj : j.val < (List.ofFn w).dedup.length := j.isLt
    obtain ⟨a, ha⟩ := (List.mem_ofFn' _ _).1 (List.mem_dedup.1 (List.getElem_mem hj))
    change depths (List.ofFn w).dedup[j.val] ≤ _
    rw [← ha]
    exact hle a

/-- A line reading its distinct wires reads at most all `n + g` wires. -/
private theorem arity_multLine_le (line : Line extSignature n g) :
    multSignature.Arity (multLine line).op ≤ n + g := by
  obtain ⟨op, w⟩ := line
  cases op with
  | ac op => exact arity_dedupLine_le ⟨op, w⟩
  | gate k => exact (List.nodup_dedup _).length_le_card.trans_eq Wire.card

private theorem arity_lines_mapLines_multLine_le (p : Program extSignature n g) (k : Fin g) :
    multSignature.Arity ((p.mapLines multLine).lines k).op ≤ n + g := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapLines_gate, Program.lines_gate_last, Line.mapWires_op]
      exact (arity_multLine_le line).trans (Nat.le_succ _)
    | cast k =>
      rw [Program.mapLines_gate, Program.lines_gate_castSucc, Line.mapWires_op]
      exact (ih k).trans (Nat.le_succ _)

/-- The circuit whose symmetric gates read their distinct wires with multiplicities, and whose
conjunctions and disjunctions read their distinct wires once. -/
def multCircuit (C : Circuit extSignature n m) : Circuit multSignature n m :=
  C.mapLines multLine

/-- Aggregating multiplicities keeps the size. -/
@[simp] theorem size_multCircuit (C : Circuit extSignature n m) : (multCircuit C).size = C.size :=
  rfl

/-- **Aggregating multiplicities keeps the function computed**, when the extra gate of `m`
arguments computes `G m` of the number of its true arguments. -/
theorem eval_multCircuit {G : ℕ → ℕ → Bool} {f : ∀ m, BooleanFunction m}
    (hf : ∀ m x, f m x = G m (BitString.weight x)) (C : Circuit extSignature n m) :
    (multCircuit C).eval (multInterpretation G) = C.eval (extInterpretation f) :=
  Circuit.eval_mapLines (eval_multLine hf) C

/-- Aggregating multiplicities makes no gate deeper. -/
theorem depth_multCircuit_le (C : Circuit extSignature n m) : (multCircuit C).depth ≤ C.depth :=
  Circuit.depth_mapLines_le depth_multLine_le C

/-- Every gate of `multCircuit C` reads at most all `n + C.size` wires. -/
theorem arity_lines_multCircuit_le (C : Circuit extSignature n m) (k : Fin C.size) :
    multSignature.Arity ((multCircuit C).program.lines k).op ≤ n + C.size :=
  arity_lines_mapLines_multLine_le C.program k

/-- **Fan-in reduction**: the gates of `multCircuit C` have fan-in at most the number of inputs and
gates of `C`. -/
theorem fanInAtMost_multCircuit (C : Circuit extSignature n m) :
    (multCircuit C).FanInAtMost (n + C.size) :=
  Program.fanInAtMost_iff.2 (arity_lines_multCircuit_le C)

end Cslib.Circuits.Boolean.Unbounded
