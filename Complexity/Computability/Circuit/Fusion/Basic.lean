/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SourceComplexity
import Complexity.Computability.Circuit.Program
import Complexity.Computability.Circuit.Simulation

/-!
# Fusion covers of circuit gates

A family of predicates on semantic values supplies candidate invariants. If every input
satisfies an invariant and some output violates it, some evaluated gate fails to preserve it.
Thus the semantic gate configurations form a static cover of all candidate invariants.
The cover has exactly the program's weighted cost, including unused gates and nullary operations;
sharing and repeated outputs incur no additional cost.

This algebra-generic obstruction requires neither a Boolean structure nor an order on values.
The reference-to-observation implication used in Fusion models is one possible predicate.
`Program.trace_induction` supplies the direct preservation argument, without selecting a failing
atom. Extracting a failing atom from a cover may use classical logic.

## Main definitions

* `Cslib.Circuits.Fusion.Atom`, `Cslib.Circuits.Fusion.Atom.Preserves`: an operation with its
  semantic arguments, and predicate preservation across it.
* `Cslib.Circuits.Fusion.IsCover`, `Cslib.Circuits.Fusion.Cover`,
  `Cslib.Circuits.Fusion.Cover.cost`: a finite family defeating every candidate invariant, and its
  weighted operation cost.
* `Cslib.Circuits.Fusion.programAtoms`, `Cslib.Circuits.Fusion.Cover.ofProgram`: the semantic gate
  atoms of a program, and the cover they form.
* `Cslib.Circuits.Fusion.coverComplexity`: minimum weighted cover cost, or infinity.

## Main results

* `Cslib.Circuits.Fusion.programAtoms_isCover`: the gates cover failed invariants.
* `Cslib.Circuits.Fusion.Cover.cost_ofProgram`: extraction preserves arbitrary operation costs.
* `Cslib.Circuits.Fusion.coverComplexity_le_ecomplexityFrom`: transfer to native source complexity.

## References

* Adapted from LowerBound/Fusion/Framework.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u v w z

variable {σ : Signature.{u}} {U : Type v} {W : Type w} {n g m : ℕ}

/-- One semantic gate configuration, without any constraint on where its arguments came from. -/
structure Atom (σ : Signature.{u}) (U : Type v) where
  /-- The operation at the gate. -/
  op : σ.Op
  /-- The value supplied to each argument. -/
  arguments : Fin (σ.Arity op) → U

/-- An atom preserves a predicate if it holds on the result whenever it holds on all arguments. -/
def Atom.Preserves (a : Atom σ U) (I : Interpretation σ U) (P : U → Prop) : Prop :=
  (∀ i, P (a.arguments i)) → P (I a.op a.arguments)

/-- No candidate invariant is preserved by every atom in a cover. -/
def IsCover (I : Interpretation σ U) (P : W → U → Prop) {k : ℕ}
    (atoms : Fin k → Atom σ U) : Prop :=
  ∀ t, ¬ ∀ i, (atoms i).Preserves I (P t)

/-- A finite fusion cover. Repeated atoms are allowed and charged separately. -/
structure Cover (I : Interpretation σ U) (P : W → U → Prop) where
  /-- Number of atoms, including repetitions. -/
  size : ℕ
  /-- Semantic gate configurations in the cover. -/
  atoms : Fin size → Atom σ U
  /-- Every candidate invariant fails at some atom. -/
  isCover : IsCover I P atoms

variable {I : Interpretation σ U} {P : W → U → Prop}

/-- Total operation weight of a cover. -/
def Cover.cost (c : Cover I P) (weight : σ.Op → ℕ) : ℕ :=
  ∑ i, weight (c.atoms i).op

/-- The least weighted cost of any finite cover; infinity if there is no cover. -/
noncomputable def coverComplexity (I : Interpretation σ U) (P : W → U → Prop)
    (weight : σ.Op → ℕ) : ℕ∞ :=
  ⨅ c : Cover I P, (c.cost weight : ℕ∞)

/-- Every cover bounds the minimum cover cost from above. -/
theorem coverComplexity_le (c : Cover I P) (weight : σ.Op → ℕ) :
    coverComplexity I P weight ≤ c.cost weight :=
  iInf_le _ c

/-- A lower bound on minimum cover complexity is exactly a bound for every finite cover. -/
theorem le_coverComplexity_iff {weight : σ.Op → ℕ} {k : ℕ∞} :
    k ≤ coverComplexity I P weight ↔ ∀ c : Cover I P, k ≤ c.cost weight :=
  le_iInf_iff

/-- Semantic atoms of a native program, indexed by its gates in program order. -/
def programAtoms (p : Program σ n g) (I : Interpretation σ U) (input : Fin n → U)
    (k : Fin g) : Atom σ U where
  op := (p.lines k).op
  arguments := p.trace I input ∘ (p.lines k).wires

/-- Adding a gate appends its evaluated atom, preserving every earlier atom. -/
theorem programAtoms_gate (p : Program σ n g) (line : Line σ n g)
    (I : Interpretation σ U) (input : Fin n → U) :
    programAtoms (p.gate line) I input =
      Fin.snoc (programAtoms p I input) ⟨line.op, p.trace I input ∘ line.wires⟩ := by
  funext k
  induction k using Fin.lastCases <;>
    simp only [Fin.snoc_last, Fin.snoc_castSucc] <;> unfold programAtoms
  all_goals
    first | rw [Program.lines_gate_last] | rw [Program.lines_gate_castSucc]
    congr 1
    funext a
    exact Program.trace_gate_castSucc p line I input _

/-- Gates cover every invariant that holds on the inputs and fails on some wire. -/
theorem programAtoms_isCover (p : Program σ n g) (I : Interpretation σ U)
    (P : W → U → Prop) (input : Fin n → U) (hin : ∀ t i, P t (input i))
    (hfail : ∀ t, ∃ w, ¬ P t (p.trace I input w)) :
    IsCover I P (programAtoms p I input) := by
  intro t h
  obtain ⟨w, hw⟩ := hfail t
  exact hw (p.trace_induction I input (hin t) h w)

/-- Extract all gates as a cover; no failing atom needs to be selected. -/
def Cover.ofProgram (p : Program σ n g) (I : Interpretation σ U) (P : W → U → Prop)
    (input : Fin n → U) (hin : ∀ t i, P t (input i))
    (hfail : ∀ t, ∃ w, ¬ P t (p.trace I input w)) : Cover I P :=
  ⟨g, programAtoms p I input, programAtoms_isCover p I P input hin hfail⟩

/-- Extracting a program's cover preserves its exact weighted cost. -/
@[simp] theorem Cover.cost_ofProgram (p : Program σ n g) (I : Interpretation σ U)
    (P : W → U → Prop) (input : Fin n → U) (hin : ∀ t i, P t (input i))
    (hfail : ∀ t, ∃ w, ¬ P t (p.trace I input w)) (weight : σ.Op → ℕ) :
    (Cover.ofProgram p I P input hin hfail).cost weight = p.cost weight :=
  (p.cost_eq_sum weight).symm

/-- Every program violating all candidate invariants pays at least the minimum cover cost. -/
private theorem coverComplexity_le_program_cost (p : Program σ n g) (I : Interpretation σ U)
    (P : W → U → Prop) (input : Fin n → U) (hin : ∀ t i, P t (input i))
    (hfail : ∀ t, ∃ w, ¬ P t (p.trace I input w)) (weight : σ.Op → ℕ) :
    coverComplexity I P weight ≤ p.cost weight := by
  simpa only [Cover.cost_ofProgram] using
    coverComplexity_le (Cover.ofProgram p I P input hin hfail) weight

/-- Failure on any designated output suffices. Different witnesses may use different outputs. -/
theorem coverComplexity_le_circuit_cost (c : Circuit σ n m) (I : Interpretation σ U)
    (P : W → U → Prop) (input : Fin n → U) (hin : ∀ t i, P t (input i))
    (hfail : ∀ t, ∃ o, ¬ P t (c.eval I input o)) (weight : σ.Op → ℕ) :
    coverComplexity I P weight ≤ c.program.cost weight :=
  coverComplexity_le_program_cost c.program I P input hin
    (fun t => (hfail t).elim fun o ho => ⟨c.outputs o, ho⟩) weight

/-- A single source assignment separating inputs from target outputs bounds source complexity.
The common source domain remains arbitrary; its chosen assignment must actually exist. -/
theorem coverComplexity_le_ecomplexityFrom {X : Type z} (I : Interpretation σ U)
    (P : W → U → Prop) (weight : σ.Op → ℕ) (target : X → Fin m → U)
    (sources : X → Fin n → U) (x : X) (hin : ∀ t i, P t (sources x i))
    (hfail : ∀ t, ∃ o, ¬ P t (target x o)) :
    coverComplexity I P weight ≤ ecomplexityFrom I weight target sources := by
  refine le_ecomplexityFrom_iff.mpr fun c hc => ?_
  exact coverComplexity_le_circuit_cost c I P (sources x) hin (hc x ▸ hfail) weight

end Cslib.Circuits.Fusion
