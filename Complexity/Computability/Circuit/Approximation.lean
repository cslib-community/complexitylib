/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Simulation

/-!
# The approximation method

A *local approximation scheme* compares a circuit evaluated exactly with the same circuit evaluated
in an approximate interpretation, on a finite space of samples. It gives, for every gate, a finite
set of samples on which replacing the exact operation by the approximate one may go wrong, of
bounded size. Evaluating the circuit approximately, the approximate value of every wire is then
correct on every sample outside the union of the exception sets of the gates (`program_correct`),
and so a circuit computing a target fails on at most as many samples as the total cost of its
gates (`card_failures_le_cost`). Each gate is charged once, however often its value is reused.

Correctness is a relation between exact values, so that it can be one-sided, as in Razborov's
method of approximations for monotone circuits [Jukna, Chapter 9][Jukna2012].

## Main definitions

* `Cslib.Circuits.Approximation.Scheme`: a local approximation scheme.
* `Cslib.Circuits.Approximation.Scheme.programExceptions`: the exceptions of all gates.
* `Cslib.Circuits.Approximation.Scheme.failures`: the samples on which an approximate value is
  wrong.

## Main results

* `Cslib.Circuits.Approximation.Scheme.program_correct`: the approximate values are correct away
  from the exceptions.
* `Cslib.Circuits.Approximation.Scheme.card_failures_le_cost`: the number of failures is at most
  the total cost.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Approximation

variable {σ : Signature} {U A Sample : Type*} {n : ℕ}

/-- A local approximation scheme for the exact interpretation `exact` by the approximate
interpretation `approx`, on samples `Sample`: `decode a s` reads an approximate value `a` on the
sample `s`, the exact circuit inputs on a sample are `exactInput s`, and the approximate ones are
`approxInput`. -/
structure Scheme (exact : Interpretation σ U) (approx : Interpretation σ A)
    (decode : A → Sample → U) (exactInput : Sample → Fin n → U) (approxInput : Fin n → A) where
  /-- Correctness of a decoded approximate value with respect to an exact value. -/
  relation : U → U → Prop
  relation_trans : ∀ {u v w}, relation u v → relation v w → relation u w
  /-- The exact operations preserve correctness. -/
  map_relation : ∀ op (u v : Fin (σ.Arity op) → U), (∀ i, relation (u i) (v i)) →
    relation (exact op u) (exact op v)
  /-- The number of exceptions charged to each operation. -/
  errorCost : σ.Op → ℕ
  /-- The samples on which applying an approximate operation to given arguments may go wrong. -/
  exceptions : ∀ op : σ.Op, (Fin (σ.Arity op) → A) → Finset Sample
  /-- The approximate inputs are correct on every sample. -/
  input_correct : ∀ s i, relation (exactInput s i) (decode (approxInput i) s)
  /-- An approximate operation is correct away from its exceptions. -/
  gate_correct : ∀ op (a : Fin (σ.Arity op) → A) s, s ∉ exceptions op a →
    relation (exact op fun i => decode (a i) s) (decode (approx op a) s)
  exceptions_card_le : ∀ op a, (exceptions op a).card ≤ errorCost op

namespace Scheme

variable {exact : Interpretation σ U} {approx : Interpretation σ A} {decode : A → Sample → U}
  {exactInput : Sample → Fin n → U} {approxInput : Fin n → A} [DecidableEq Sample]
  (S : Scheme exact approx decode exactInput approxInput)

/-- The exceptions of all gates of a program, applied to their approximate arguments. -/
def programExceptions : ∀ {g : ℕ}, Program σ n g → Finset Sample
  | _, .empty => ∅
  | _, .gate p line =>
    programExceptions p ∪ S.exceptions line.op (p.trace approx approxInput ∘ line.wires)

@[simp] theorem programExceptions_empty :
    S.programExceptions (Program.empty : Program σ n 0) = ∅ := rfl

@[simp] theorem programExceptions_gate {g : ℕ} (p : Program σ n g) (line : Line σ n g) :
    S.programExceptions (p.gate line) =
      S.programExceptions p ∪ S.exceptions line.op (p.trace approx approxInput ∘ line.wires) :=
  rfl

/-- There are at most as many exceptions as the total cost of the gates. -/
private theorem card_programExceptions_le {g : ℕ} (p : Program σ n g) :
    (S.programExceptions p).card ≤ p.cost S.errorCost := by
  induction p with
  | empty => simp
  | gate p line ih =>
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add ih (S.exceptions_card_le _ _))

/-- Away from the exceptions, the approximate value of every wire is correct. -/
theorem program_correct {g : ℕ} (p : Program σ n g) {s : Sample}
    (hs : s ∉ S.programExceptions p) :
    ∀ w : Wire n g, S.relation (p.trace exact (exactInput s) w)
      (decode (p.trace approx approxInput w) s) := by
  induction p with
  | empty =>
    intro w
    cases w with
    | input i => exact S.input_correct s i
    | gate i => exact i.elim0
  | @gate g p line ih =>
    simp only [programExceptions_gate, Finset.mem_union, not_or] at hs
    intro w
    induction w using Wire.lastCases with
    | last =>
      change S.relation ((p.gate line).eval exact (exactInput s) (Fin.last g))
        (decode ((p.gate line).eval approx approxInput (Fin.last g)) s)
      rw [Program.eval_gate_last, Program.eval_gate_last]
      exact S.relation_trans (S.map_relation line.op _ _ fun i => ih hs.1 (line.wires i))
        (S.gate_correct line.op _ s hs.2)
    | castSucc w => simpa only [Program.trace_gate_castSucc] using ih hs.1 w

/-- Away from the exceptions, every output of a circuit is correct. -/
private theorem circuit_correct {m : ℕ} (C : Circuit σ n m) (o : Fin m) {s : Sample}
    (hs : s ∉ S.programExceptions C.program) :
    S.relation (C.eval exact (exactInput s) o) (decode (C.eval approx approxInput o) s) :=
  S.program_correct C.program hs (C.outputs o)

end Scheme

namespace Scheme

variable {exact : Interpretation σ U} {approx : Interpretation σ A} {decode : A → Sample → U}
  {exactInput : Sample → Fin n → U} {approxInput : Fin n → A}
  (S : Scheme exact approx decode exactInput approxInput) [DecidableRel S.relation]

/-- The samples of `samples` on which the approximate value `a` is not correct for `target`. -/
def failures (samples : Finset Sample) (a : A) (target : Sample → U) : Finset Sample :=
  samples.filter fun s => ¬S.relation (target s) (decode a s)

@[simp] theorem mem_failures {samples : Finset Sample} {a : A} {target : Sample → U}
    {s : Sample} : s ∈ S.failures samples a target ↔ s ∈ samples ∧
      ¬S.relation (target s) (decode a s) := by
  simp [failures]

/-- A circuit computing `target` exactly on the samples fails, approximately, only on
exceptions. -/
theorem failures_subset_programExceptions [DecidableEq Sample] (samples : Finset Sample)
    (C : Circuit σ n 1) {target : Sample → U}
    (hC : ∀ s ∈ samples, C.eval exact (exactInput s) 0 = target s) :
    S.failures samples (C.eval approx approxInput 0) target ⊆
      S.programExceptions C.program := fun s hs => by
  by_contra h
  obtain ⟨hs, hfail⟩ := (S.mem_failures).1 hs
  exact hfail (hC s hs ▸ S.circuit_correct C 0 h)

/-- **The approximation method.** A circuit computing `target` exactly on the samples fails,
approximately, on at most as many of them as the total cost of its gates. -/
theorem card_failures_le_cost (samples : Finset Sample) (C : Circuit σ n 1) {target : Sample → U}
    (hC : ∀ s ∈ samples, C.eval exact (exactInput s) 0 = target s) :
    (S.failures samples (C.eval approx approxInput 0) target).card ≤
      C.program.cost S.errorCost := by
  classical
  exact (Finset.card_le_card (S.failures_subset_programExceptions samples C hC)).trans
    (S.card_programExceptions_le C.program)

end Scheme

end Cslib.Circuits.Approximation
