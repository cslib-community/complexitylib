/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.DepthClasses
public import Complexity.Computability.Circuit.Boolean.Formula
public import Complexity.Computability.Circuit.MapLines
public import Complexity.Computability.Circuit.SimulationDepth
import Mathlib.Algebra.BigOperators.Fin
import Complexity.Computability.Circuit.Program
import Complexity.Computability.Circuit.Simulation
import Complexity.Foundations.Data.Nat.PolynomialBound.Log

/-!
# Simulating unbounded fan-in with fan-in two

A disjunction of `k ≥ 1` arguments is a balanced tree of `k - 1` disjunctions of fan-in two, of
depth `⌈log₂ k⌉` (`Formula.size_orList_add_one`, `Formula.depthWith_orList_le`), and so is a
conjunction. Replacing every gate of a circuit over the unbounded fan-in basis by such a tree
gives a De Morgan circuit for the same function. A gate may read one wire many times, so its
fan-in is not bounded by the size of the circuit; but a conjunction or a disjunction keeps its
value when it reads each of its wires once, so every circuit with `n` inputs and `s` gates has an
equivalent circuit of the same size and no larger depth whose gates have fan-in at most `n + s`
(`Unbounded.dedup`). Replacing its gates gives a De Morgan circuit with at most `s (n + s)` gates
and depth at most `max 1 ⌈log₂ (n + s)⌉ · d` (`Unbounded.exists_deMorgan_simulation`).

For circuits of polynomial size `log (n + s)` is `O(log n)`, so polynomial-size circuits of depth
`O((log n) ^ i)` and unbounded fan-in become polynomial-size circuits of fan-in two and depth
`O((log n) ^ (i + 1))`: **ACⁱ ⊆ NCⁱ⁺¹** (`AC_subset_NC_succ`)
[Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]. With
`NCⁱ ⊆ ACⁱ`, the two hierarchies have the same union (`iUnion_NC_eq_iUnion_AC`).

## Main definitions

* `Cslib.Circuits.Boolean.Unbounded.dedupLine`, `Cslib.Circuits.Boolean.Unbounded.dedup`: the line
  and circuit whose gates read their distinct wires, each once.
* `Cslib.Circuits.Boolean.Unbounded.Op.deMorganFormula`: a De Morgan formula for each operation of
  the unbounded fan-in basis.

## Main results

* `Cslib.Circuits.Boolean.Unbounded.eval_dedup`, `Cslib.Circuits.Boolean.Unbounded.depth_dedup_le`,
  `Cslib.Circuits.Boolean.Unbounded.fanInAtMost_dedup`: reading every wire once keeps the function
  and the size, makes no gate deeper, and bounds the fan-in by the number of inputs and gates.
* `Cslib.Circuits.Boolean.Unbounded.exists_deMorgan_simulation`: a circuit of unbounded fan-in
  with `n` inputs, `s` gates and depth `d` has an equivalent De Morgan circuit with at most
  `s (n + s)` gates and depth at most `max 1 ⌈log₂ (n + s)⌉ · d`.
* `Cslib.Circuits.Boolean.AC_subset_NC_succ`: **ACⁱ ⊆ NCⁱ⁺¹**.
* `Cslib.Circuits.Boolean.AC0_subset_NC_one`: **AC⁰ ⊆ NC¹**.
* `Cslib.Circuits.Boolean.iUnion_NC_eq_iUnion_AC`: **NC = AC**.
* `Cslib.Circuits.Boolean.AC_subset_PPoly`: **ACⁱ ⊆ P/poly**.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

@[expose] public section

namespace Cslib.Circuits

namespace Boolean

namespace Unbounded

variable {n g m : ℕ}

/-! ### Reading every wire once -/

private theorem forall_get_dedup_ofFn_iff {α : Type*} [DecidableEq α] {k : ℕ} (w : Fin k → α)
    (P : α → Prop) : (∀ j, P ((List.ofFn w).dedup.get j)) ↔ ∀ j, P (w j) := by
  rw [← List.forall_mem_iff_get, ← List.forall_mem_ofFn_iff]
  simp only [List.mem_dedup]

private theorem exists_get_dedup_ofFn_iff {α : Type*} [DecidableEq α] {k : ℕ} (w : Fin k → α)
    (P : α → Prop) : (∃ j, P ((List.ofFn w).dedup.get j)) ↔ ∃ j, P (w j) := by
  rw [← List.exists_mem_iff_get]
  simp [List.mem_dedup, List.mem_ofFn']

/-- The line reading the distinct wires of `line`, each once. A conjunction or a disjunction does
not depend on how often it reads a wire, so this keeps the value of the line. -/
def dedupLine : Line signature n g → Line signature n g
  | ⟨.not, w⟩ => ⟨.not, w⟩
  | ⟨.and _, w⟩ => ⟨.and (List.ofFn w).dedup.length, (List.ofFn w).dedup.get⟩
  | ⟨.or _, w⟩ => ⟨.or (List.ofFn w).dedup.length, (List.ofFn w).dedup.get⟩

/-- Reading every wire once keeps the value of a line. -/
theorem eval_dedupLine (line : Line signature n g) (x : Fin n → Bool) (gates : Fin g → Bool) :
    (dedupLine line).eval interpretation x gates = line.eval interpretation x gates := by
  obtain ⟨op, w⟩ := line
  cases op with
  | not => rfl
  | and k =>
    exact decide_eq_decide.2 (forall_get_dedup_ofFn_iff w fun a => Wire.elim x gates a = true)
  | or k =>
    exact decide_eq_decide.2 (exists_get_dedup_ofFn_iff w fun a => Wire.elim x gates a = true)

/-- Reading every wire once makes no line deeper. -/
theorem depth_dedupLine_le (line : Line signature n g) (depths : Wire n g → ℕ) :
    (dedupLine line).depth depths ≤ line.depth depths := by
  have hpos := line.depth_pos depths
  have hle : ∀ a, depths (line.wires a) ≤ line.depth depths - 1 := fun a => by
    have := line.wireDepth_lt_depth depths a
    omega
  refine ((Line.depth_le_add_one_iff _ depths (d := line.depth depths - 1)).2 ?_).trans
    (by omega)
  obtain ⟨op, w⟩ := line
  cases op with
  | not => exact hle
  | and k => exact (forall_get_dedup_ofFn_iff w fun a => depths a ≤ _).2 hle
  | or k => exact (forall_get_dedup_ofFn_iff w fun a => depths a ≤ _).2 hle

/-- A line reading every wire once reads at most all `n + g` wires. -/
theorem arity_dedupLine_le (line : Line signature n g) :
    signature.Arity (dedupLine line).op ≤ n + g := by
  obtain ⟨op, w⟩ := line
  cases op with
  | not => exact (Fintype.card_pos_iff.2 ⟨w 0⟩).trans_eq Wire.card
  | and k => exact (List.nodup_dedup _).length_le_card.trans_eq Wire.card
  | or k => exact (List.nodup_dedup _).length_le_card.trans_eq Wire.card

/-- The gates of a program reading every wire once read at most all wires. -/
private theorem arity_lines_mapLines_dedupLine_le (p : Program signature n g) (k : Fin g) :
    signature.Arity ((p.mapLines dedupLine).lines k).op ≤ n + g := by
  induction p with
  | empty => exact k.elim0
  | @gate g p line ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [Program.mapLines_gate, Program.lines_gate_last, Line.mapWires_op]
      exact (arity_dedupLine_le line).trans (Nat.le_succ _)
    | cast k =>
      rw [Program.mapLines_gate, Program.lines_gate_castSucc, Line.mapWires_op]
      exact (ih k).trans (Nat.le_succ _)

/-- The circuit whose gates read their distinct wires, each once. It computes the same function
(`eval_dedup`) with the same size and no larger depth (`depth_dedup_le`), and its gates have
fan-in at most the number of inputs and gates (`fanInAtMost_dedup`). -/
def dedup (C : Circuit signature n m) : Circuit signature n m :=
  C.mapLines dedupLine

/-- Reading every wire once keeps the size. -/
@[simp] theorem size_dedup (C : Circuit signature n m) : (dedup C).size = C.size :=
  rfl

/-- Reading every wire once keeps the function computed. -/
@[simp] theorem eval_dedup (C : Circuit signature n m) :
    (dedup C).eval interpretation = C.eval interpretation :=
  Circuit.eval_mapLines eval_dedupLine C

/-- Reading every wire once makes no gate deeper. -/
theorem depth_dedup_le (C : Circuit signature n m) : (dedup C).depth ≤ C.depth :=
  Circuit.depth_mapLines_le depth_dedupLine_le C

/-- Every gate of `dedup C` reads at most all `n + C.size` wires. -/
private theorem arity_lines_dedup_le (C : Circuit signature n m) (k : Fin C.size) :
    signature.Arity ((dedup C).program.lines k).op ≤ n + C.size :=
  arity_lines_mapLines_dedupLine_le C.program k

/-- **Fan-in reduction**: the gates of `dedup C` have fan-in at most the number of inputs and
gates of `C`. -/
theorem fanInAtMost_dedup (C : Circuit signature n m) : (dedup C).FanInAtMost (n + C.size) :=
  Program.fanInAtMost_iff.2 (arity_lines_dedup_le C)

/-! ### Balanced trees for the gates -/

/-- A De Morgan formula for each operation of the unbounded fan-in basis: the negation of the
input, and the balanced conjunction and disjunction of the inputs. -/
def Op.deMorganFormula : (op : Op) → Formula Boolean.signature op.arity
  | .not => (Formula.input 0).not
  | .and _ => Formula.andList (List.ofFn Formula.input)
  | .or _ => Formula.orList (List.ofFn Formula.input)

/-- The De Morgan formula of an operation computes it. -/
theorem Op.computes_deMorganFormula (op : Op) :
    op.deMorganFormula.Computes Boolean.interpretation (interpretation op) := fun x => by
  cases op with
  | not => rfl
  | and k =>
    rw [deMorganFormula, Formula.eval_andList, interpretation_and, Bool.eq_iff_iff,
      List.all_eq_true]
    simp
  | or k =>
    rw [deMorganFormula, Formula.eval_orList, interpretation_or, Bool.eq_iff_iff,
      List.any_eq_true]
    simp

/-- The De Morgan formula of an operation of `k` arguments has at most `max 1 k` nodes: one
negation, a constant for no arguments, and `k - 1` binary gates for `k ≥ 1` arguments. -/
theorem Op.size_deMorganFormula_le (op : Op) : op.deMorganFormula.size ≤ max 1 op.arity := by
  cases op with
  | not => simp [deMorganFormula]
  | and k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · have := Formula.size_andList_add_one
        (l := List.ofFn (Formula.input (σ := Boolean.signature) (n := k))) (by simpa using hk.ne')
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, Formula.size_input,
        Finset.sum_const_zero, List.length_ofFn, zero_add] at this
      exact (le_max_right 1 k).trans' (by rw [deMorganFormula]; omega)
  | or k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · have := Formula.size_orList_add_one
        (l := List.ofFn (Formula.input (σ := Boolean.signature) (n := k))) (by simpa using hk.ne')
      simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply, Formula.size_input,
        Finset.sum_const_zero, List.length_ofFn, zero_add] at this
      exact (le_max_right 1 k).trans' (by rw [deMorganFormula]; omega)

/-- The De Morgan formula of an operation of `k` arguments has depth at most `max 1 ⌈log₂ k⌉`:
one for a negation or a constant, and `⌈log₂ k⌉` for a balanced tree of `k ≥ 1` arguments. -/
theorem Op.depth_deMorganFormula_le (op : Op) :
    op.deMorganFormula.depth ≤ max 1 (Nat.clog 2 op.arity) := by
  cases op with
  | not => simp [deMorganFormula]
  | and k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · have := Formula.depthWith_andList_le (cost := 1)
        (l := List.ofFn (Formula.input (σ := Boolean.signature) (n := k))) (d := 0) (by simp)
        (by simpa using hk.ne')
      simp only [Formula.depthWith_one, List.length_ofFn, Pi.one_apply, one_mul,
        zero_add] at this
      exact this.trans (le_max_right _ _)
  | or k =>
    rcases k.eq_zero_or_pos with rfl | hk
    · simp [deMorganFormula]
    · have := Formula.depthWith_orList_le (cost := 1)
        (l := List.ofFn (Formula.input (σ := Boolean.signature) (n := k))) (d := 0) (by simp)
        (by simpa using hk.ne')
      simp only [Formula.depthWith_one, List.length_ofFn, Pi.one_apply, one_mul,
        zero_add] at this
      exact this.trans (le_max_right _ _)

/-! ### Simulation -/

/-- **Fan-in two simulates unbounded fan-in** [Arora and Barak, Section 6.7][AroraBarak09]: a
circuit of unbounded fan-in with `n` inputs, `s` gates and depth `d` has an equivalent De Morgan
circuit with at most `s (n + s)` gates and depth at most `max 1 ⌈log₂ (n + s)⌉ · d`. Its gates are
first made to read every wire once (`dedup`), and then replaced by balanced trees. -/
theorem exists_deMorgan_simulation (C : Circuit signature n m) :
    ∃ D : Circuit Boolean.signature n m, D.eval Boolean.interpretation = C.eval interpretation ∧
      D.size ≤ C.size * (n + C.size) ∧
      D.depth ≤ max 1 (Nat.clog 2 (n + C.size)) * C.depth := by
  refine ⟨(dedup C).simulate fun op => op.deMorganFormula.toCircuit, ?_, ?_, ?_⟩
  · rw [Circuit.eval_simulate _ _ fun op => (Op.computes_deMorganFormula op).toCircuit, eval_dedup]
  · rw [Circuit.size_simulate, Program.cost_eq_sum]
    refine (Finset.sum_le_sum (g := fun _ => n + C.size) fun k _ => ?_).trans_eq
      (by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, size_dedup])
    rw [Formula.size_toCircuit]
    have hk : 1 ≤ n + C.size := by have := k.pos; simp only [size_dedup] at this; omega
    exact (Op.size_deMorganFormula_le _).trans
      (max_le hk (arity_lines_dedup_le C k))
  · refine (Circuit.depth_simulate_le _ _).trans
      ((Circuit.depthWith_le_mul_depth _ fun k => ?_).trans
        (Nat.mul_le_mul_left _ (depth_dedup_le C)))
    exact (Formula.depth_toCircuit_le _).trans ((Op.depth_deMorganFormula_le _).trans
      (max_le_max le_rfl (Nat.clog_mono_right 2 (arity_lines_dedup_le C k))))

end Unbounded

/-! ### ACⁱ ⊆ NCⁱ⁺¹ -/

/-- **ACⁱ ⊆ NCⁱ⁺¹** [Arora and Barak, Section 6.7][AroraBarak09], [Vollmer, Chapter 4][Vollmer1999]:
polynomial-size circuits of depth `O((log n) ^ i)` and unbounded fan-in are simulated by
polynomial-size circuits of depth `O((log n) ^ (i + 1))` and fan-in two. -/
theorem AC_subset_NC_succ (i : ℕ) : AC i ⊆ NC (i + 1) := by
  rintro L ⟨c, s, hs, hC⟩
  obtain ⟨e, he⟩ := PolynomiallyBounded.exists_clog_le_mul_log (s := fun n => n + s n)
    (by fun_prop)
  refine ⟨c * (e + 1), fun n => s n * (n + s n), by fun_prop, fun n => ?_⟩
  obtain ⟨C, hCc, hCd, hCs⟩ := hC n
  obtain ⟨D, hDe, hDs, hDd⟩ := Unbounded.exists_deMorgan_simulation C
  refine ⟨D, fun x => (congrFun hDe x).trans (hCc x), ?_, ?_⟩
  · have hlog : max 1 (Nat.clog 2 (n + C.size)) ≤ (e + 1) * (Nat.log 2 n + 1) := by
      have := (Nat.clog_mono_right 2 (Nat.add_le_add_left hCs n)).trans (he n)
      rw [add_one_mul]
      exact max_le (Nat.le_add_left_of_le (Nat.le_add_left 1 _)) (this.trans (Nat.le_add_right _ _))
    calc D.depth ≤ max 1 (Nat.clog 2 (n + C.size)) * C.depth := hDd
      _ ≤ ((e + 1) * (Nat.log 2 n + 1)) * (c * (Nat.log 2 n + 1) ^ i) := Nat.mul_le_mul hlog hCd
      _ = c * (e + 1) * (Nat.log 2 n + 1) ^ (i + 1) := by ring
  · calc D.size ≤ C.size * (n + C.size) := hDs
      _ ≤ s n * (n + s n) := by gcongr

/-- **AC⁰ ⊆ NC¹.** -/
theorem AC0_subset_NC_one : AC0 ⊆ NC 1 :=
  AC_zero.symm.subset.trans (AC_subset_NC_succ 0)

/-- **NC = AC**: the NC and AC hierarchies have the same union. -/
theorem iUnion_NC_eq_iUnion_AC : ⋃ i, NC i = ⋃ i, AC i :=
  (Set.iUnion_mono NC_subset_AC).antisymm <| Set.iUnion_subset fun i =>
    (AC_subset_NC_succ i).trans (Set.subset_iUnion NC (i + 1))

/-- **`ACⁱ ⊆ P/poly`** for every `i`. -/
theorem AC_subset_PPoly (i : ℕ) : AC i ⊆ PPoly :=
  (AC_subset_NC_succ i).trans (NC_subset_PPoly (i + 1))

end Boolean

end Cslib.Circuits
