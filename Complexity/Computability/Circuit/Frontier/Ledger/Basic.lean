/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Erase
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Complexity.Computability.Circuit.Program

/-!
# Ledgers for gates of unbounded fan-in

The frontier method charges each gate for its fan-in, so it cannot afford gates of unbounded
fan-in. A few of them can nevertheless be absorbed, when they *aggregate*: when their outputs are
determined by a product, in a commutative monoid, of contributions of the wires.

Mark a set of gates as *special*. A *ledger* for them in a commutative monoid `M`
(`Frontier.Ledger`) assigns to each wire and each of its values a *contribution* in `M`, and
reads off the value of every special gate from the product of the contributions of all wires.
The defining identity holds for *every* assignment of values to the wires, not only for runs of
the program. For example, `k` gates computing AND, OR, parity, or counts modulo `m` of their
arguments have a ledger in a product of `k` small monoids (`Frontier.Ledger.ofAggregates`).

**Guess and check.** Replace each special gate by a constant (`Cslib.Circuits.Program.eraseGates`):
the result has fan-in bounded by that of the other gates. To run it, guess the final product
`m ∈ M` and let each constant read its value from `m` (`Frontier.Ledger.run`). The guess is
*consistent* when the run reproduces it: when the product of the contributions of the run is `m`.

* A consistent guess yields the true run (`Frontier.Ledger.run_eq_trace`): the constants hold
  the values that the special gates compute from the run.
* The product of the contributions of the true run is a consistent guess
  (`Frontier.Ledger.run_total_trace`).

So a program with special gates is an ordinary program, of bounded fan-in, together with one
global register in `M`: the guess, checked against an accumulated product. A sweep carries the
guess and the product accumulated so far in its messages, at a cost of `2 log |M|`.

## Main definitions

* `Cslib.Circuits.Frontier.Ledger special p I M`: a ledger for the special gates of `p` in `M`.
* `Cslib.Circuits.Frontier.Ledger.total`, `Cslib.Circuits.Frontier.Ledger.totalOn`: the product
  of the contributions of all wires, and of the wires of a set.
* `Cslib.Circuits.Frontier.Ledger.run`: the run of the erased program on a guess.

## Main results

* `Cslib.Circuits.Frontier.Ledger.run_eq_trace`, `Cslib.Circuits.Frontier.Ledger.run_total_trace`:
  guess and check.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

universe v

variable {σ : Signature.{v}} {n s : ℕ} {U : Type*}

/-- A *ledger* for the special gates of a program, in a commutative monoid `M`: a contribution
of each wire for each of its values, and a readout of the value of each special gate from the
product of all contributions. The identity holds for every assignment of values to the wires. -/
structure Ledger (special : Fin s → Prop) (p : Program σ n s) (I : Interpretation σ U)
    (M : Type*) [CommMonoid M] where
  /-- The contribution of a wire carrying a value. -/
  contribution : Wire n s → U → M
  /-- The value of each special gate, read off the product of the contributions. -/
  readout : M → {g // special g} → U
  /-- The readout of a special gate is the gate applied to the values of its arguments. -/
  readout_prod : ∀ (v : Wire n s → U) (g : {g // special g}),
    readout (∏ w, contribution w (v w)) g = I (p.lines g).op fun a => v ((p.lines g).wires a)

namespace Ledger

variable {special : Fin s → Prop} {p : Program σ n s} {I : Interpretation σ U} {M : Type*}
  [CommMonoid M] (L : Ledger special p I M)

/-- The product of the contributions of an assignment of values to the wires. -/
def total (v : Wire n s → U) : M :=
  ∏ w, L.contribution w (v w)

open Classical in
/-- The product of the contributions of the wires in `Q`. -/
noncomputable def totalOn (Q : Set (Wire n s)) (v : Wire n s → U) : M :=
  ∏ w ∈ Finset.univ.filter (· ∈ Q), L.contribution w (v w)

/-- The total is the product on `Q` times the product on its complement. -/
theorem total_eq_mul (Q : Set (Wire n s)) (v : Wire n s → U) :
    L.total v = L.totalOn Q v * L.totalOn Qᶜ v := by
  classical
  rw [total, totalOn, totalOn, ← Finset.prod_filter_mul_prod_filter_not Finset.univ (· ∈ Q)]
  simp only [Set.mem_compl_iff]

variable [DecidablePred special]

/-- The run of the erased program, with the constants reading their values from the guess `m`. -/
def run (m : M) (x : Fin n → U) : Wire n s → U :=
  (p.eraseGates special).trace (I.withConstants (L.readout m)) x

@[simp] theorem run_input (m : M) (x : Fin n → U) (i : Fin n) : L.run m x (.input i) = x i :=
  rfl

/-- The value of a gate in the run with guess `m`: the readout for a special gate, and the gate
applied to the values of its arguments otherwise. -/
private theorem run_gate (m : M) (x : Fin n → U) (g : Fin s) :
    L.run m x (.gate g) = if h : special g then L.readout m ⟨g, h⟩
      else I (p.lines g).op fun a => L.run m x ((p.lines g).wires a) :=
  p.trace_eraseGates_gate x g

/-- The value of a special gate in the run with guess `m` is its readout. -/
theorem run_gate_of_special (m : M) (x : Fin n → U) {g : Fin s} (hg : special g) :
    L.run m x (.gate g) = L.readout m ⟨g, hg⟩ := by
  simp only [run_gate, hg, ↓reduceDIte]

/-- The value of an ordinary gate in the run with guess `m` is the gate applied to its
arguments. -/
theorem run_gate_of_not_special (m : M) (x : Fin n → U) {g : Fin s} (hg : ¬special g) :
    L.run m x (.gate g) = I (p.lines g).op fun a => L.run m x ((p.lines g).wires a) := by
  simp only [run_gate, hg, ↓reduceDIte]

/-- **Guess and check, soundness.** If the run with guess `m` reproduces `m`, it is the true
run. -/
theorem run_eq_trace {m : M} {x : Fin n → U} (h : L.total (L.run m x) = m) :
    L.run m x = p.trace I x := by
  refine Program.eq_trace_of_forall_gate (fun _ => rfl) fun g => ?_
  by_cases hg : special g
  · have hread := L.readout_prod (L.run m x) ⟨g, hg⟩
    rw [← total, h] at hread
    rw [L.run_gate_of_special m x hg, hread]
  · exact L.run_gate_of_not_special m x hg

/-- **Guess and check, completeness.** The product of the contributions of the true run is a
guess whose run is the true run. -/
theorem run_total_trace (x : Fin n → U) : L.run (L.total (p.trace I x)) x = p.trace I x :=
  Program.trace_eraseGates fun g hg => (L.readout_prod _ ⟨g, hg⟩).trans (p.trace_gate I x g).symm

/-- **The consistent guess is unique.** A guess reproduces itself exactly when it is the product
of the contributions of the true run. -/
theorem total_run_eq_iff (m : M) (x : Fin n → U) :
    L.total (L.run m x) = m ↔ m = L.total (p.trace I x) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [L.run_eq_trace h] at h
    exact h.symm
  · rw [h, L.run_total_trace]

end Ledger

end Cslib.Circuits.Frontier
