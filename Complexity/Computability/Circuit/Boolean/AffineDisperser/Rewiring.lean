/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.AffineDisperser.Operations
public import Complexity.Computability.Circuit.Boolean.SemiCircuit.Rewiring

/-!
# Moving and rewiring gates of states

The preparatory operations of [Mishra and Santhanam, Sections 4.1 and 4.2][MishraSanthanam2026]
that change only gates, on states of gate elimination:

* `State.moveAffine`: moving an affine gate reading no gates into the affine system, as the
  equation `SemiCircuit.affEqn` (`State.Valid.moveAffine`);
* `State.rewire`: replacing a gate by one reading only parameters and computing the same value
  whenever the other gates take their values, used to reroute the children of the minimal AND
  (`State.Valid.rewire`).

Both keep the parameters, the pairs and the parameter map.

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser.State.moveAffine`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.rewire`.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.moveAffine`,
  `Cslib.Circuits.Boolean.AffineDisperser.State.Valid.rewire`: they preserve validity.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 3.5n − o(n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.AffineDisperser

open Finset SemiCircuit

namespace State

variable {n : ℕ} {f : BooleanFunction n}

/-! ### Moving affine gates into the affine system -/

/-- Move the affine gate `J` into the affine system as the auxiliary variable `J` with the new
equation `e`. -/
def moveAffine (S : State n) (J e : ℕ) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.moveAffine J e }

/-- Moving an affine gate into the affine system preserves the parameters of the state. -/
@[simp] theorem moveAffine_params (S : State n) (J e : ℕ) :
    (S.moveAffine J e).params = S.params := rfl

/-- Moving an affine gate into the affine system preserves the pairs of the state. -/
@[simp] theorem moveAffine_pairs (S : State n) (J e : ℕ) :
    (S.moveAffine J e).pairs = S.pairs := rfl

/-- Moving an affine gate into the affine system preserves the size of the state. -/
theorem moveAffine_size {S : State n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).size = S.size := by
  have h1 := Finset.card_erase_add_one h.mem
  have h2 := Finset.card_insert_of_notMem h.fresh
  simp only [SemiCircuit.size] at *
  change (S.gates.erase J).card + (insert e S.eqns).card = _
  omega

/-- Moving an affine gate into the affine system decreases the number of gates by `1`. -/
theorem moveAffine_gates_card {S : State n} {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).gates.card + 1 = S.gates.card :=
  Finset.card_erase_add_one h.mem

/-- Moving a gate into the affine system does not increase the degree of any parameter. -/
theorem moveAffine_deg_le {S : State n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e)
    {z : ℕ} (hz : z ∈ S.params) : (S.moveAffine J e).deg z ≤ S.deg z :=
  deg_moveAffine_le h fun he => hS.wf.notMem_gates_of_mem_params hz (he ▸ h.mem)

/-- Moving an affine gate reading no gates into the affine system preserves validity. -/
theorem Valid.moveAffine {S : State n} (hS : S.Valid f) {J e : ℕ} (h : S.MoveOK J e) :
    (S.moveAffine J e).Valid f :=
  hS.of_liftsTo rfl rfl rfl (hS.wf.moveAffine h) h.liftsTo

/-! ### Rewiring a gate -/

/-- Replace the gate `J` by the gate `g`. -/
def rewire (S : State n) (J : ℕ) (g : Gate) : State n :=
  { S with toSemiCircuit := S.toSemiCircuit.rewire J g }

/-- Rewiring a gate preserves the parameters of the state. -/
@[simp] theorem rewire_params (S : State n) (J : ℕ) (g : Gate) :
    (S.rewire J g).params = S.params := rfl

/-- Rewiring a gate preserves the pairs of the state. -/
@[simp] theorem rewire_pairs (S : State n) (J : ℕ) (g : Gate) :
    (S.rewire J g).pairs = S.pairs := rfl

/-- Rewiring a gate preserves the size of the state. -/
theorem rewire_size (S : State n) (J : ℕ) (g : Gate) : (S.rewire J g).size = S.size := rfl

/-- Rewiring a gate preserves the set of gate names. -/
theorem rewire_gates (S : State n) (J : ℕ) (g : Gate) : (S.rewire J g).gates = S.gates := rfl

/-- A gate `K` is a child of `z` in `S.rewire J g` iff `K ∈ S.gates` and the gate at `K` (which
is `g` when `K = J`) reads `z`. -/
theorem inl_mem_children_rewire (S : State n) (J : ℕ) (g : Gate) (z K : ℕ) :
    Sum.inl K ∈ (S.rewire J g).children z ↔
      K ∈ S.gates ∧ (if K = J then g.Reads z else (S.gate K).Reads z) := by
  rw [SemiCircuit.inl_mem_children]
  change K ∈ S.gates ∧ (Function.update S.gate J g K).Reads z ↔ _
  by_cases hKJ : K = J
  · subst hKJ; rw [Function.update_self, ite_eq_left rfl]
  · rw [Function.update_of_ne hKJ, ite_eq_right hKJ]

/-- Rewiring a gate preserves the equation children of every variable. -/
theorem inr_mem_children_rewire (S : State n) (J : ℕ) (g : Gate) (z e : ℕ) :
    Sum.inr e ∈ (S.rewire J g).children z ↔ Sum.inr e ∈ S.children z := by
  simp only [SemiCircuit.inr_mem_children]
  rfl

/-- Rewiring a gate preserves validity. -/
theorem Valid.rewire {S : State n} (hS : S.Valid f) {J : ℕ} {g : Gate} (h : S.RewireOK J g) :
    (S.rewire J g).Valid f :=
  hS.of_liftsTo rfl rfl rfl (hS.wf.rewire h) h.liftsTo

end State

end Cslib.Circuits.Boolean.AffineDisperser
