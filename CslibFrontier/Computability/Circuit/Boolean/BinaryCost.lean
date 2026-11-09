/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.FanIn
public import CslibFrontier.Computability.Circuit.Simulation
public import CslibFrontier.Computability.Circuit.Support
public import Cslib.Computability.Circuit.Boolean.Basic

/-!
# Counting the binary gates of De Morgan circuits

The size of a De Morgan circuit counts every gate. The usual measure for lower bounds charges only
the AND and OR gates and lets negations and constants be free [Jukna, Section 1.2][Jukna2012]. It
is the cost of a program for `binaryCost`, and it is at most the size
(`Program.cost_binaryCost_le`).

Because only binary AND and OR gates have arity two while constants have arity zero and negations
have arity one (`Boolean.arity_le_one_add_binaryCost`), only binary gates increase the number of
supporting inputs in the backward cone of a frontier
(`Program.card_biUnion_wireSupport_le_cost_binaryCost`). Every De Morgan circuit with `m` outputs
therefore depends on at most `m + c.program.cost binaryCost` inputs
(`Circuit.card_inputSupport_le_cost_binaryCost`).

## Main definitions

* `Cslib.Circuits.Boolean.Op.IsBinary`: AND and OR, the operations of arity two.
* `Cslib.Circuits.Boolean.binaryCost`: the cost function charging one for each AND and OR gate.

## Main results

* `Cslib.Circuits.Boolean.arity_le_one_add_binaryCost`: every De Morgan operation has arity at most
  `1 + binaryCost op`.
* `Cslib.Circuits.Program.cost_binaryCost_le`: the number of binary gates is at most the size.
* `Cslib.Circuits.Program.cost_binaryCost_eq_iff_forall_isBinary`: `p.cost binaryCost = g` iff every
  line of `p` is a binary AND or OR gate.
* `Cslib.Circuits.Program.card_biUnion_wireSupport_le_cost_binaryCost`: the number of inputs
  supporting a frontier of wires is at most `frontier.card + p.cost binaryCost`.
* `Cslib.Circuits.Circuit.card_inputSupport_le_cost_binaryCost`,
  `Cslib.Circuits.Circuit.essential_le_cost_binaryCost`: a De Morgan circuit with `m` outputs has at
  most `m + c.program.cost binaryCost` supporting (or essential) inputs.
* `Cslib.Circuits.Circuit.cost_binaryCost_eq_size_of_size_le`: a one-output De Morgan circuit with
  all `n` inputs in its support and `c.size + 1 ≤ n` has
  `c.program.cost binaryCost = c.size = n - 1` and consists solely of binary AND/OR gates.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits

variable {n m g : ℕ}

namespace Boolean

/-- The binary operations of the De Morgan basis, AND and OR. -/
def Op.IsBinary (op : Op) : Prop :=
  signature.Arity op = 2

/-- Decidability of whether a De Morgan operation is binary. -/
instance : DecidablePred Op.IsBinary :=
  fun op => inferInstanceAs (Decidable (signature.Arity op = 2))

/-- A De Morgan operation is binary if and only if it is `.and` or `.or`. -/
theorem Op.isBinary_iff {op : Op} : op.IsBinary ↔ op = .and ∨ op = .or := by
  cases op <;> simp [Op.IsBinary]

/-- The conjunction operation `.and` is binary. -/
theorem Op.isBinary_and : Op.and.IsBinary :=
  rfl

/-- The disjunction operation `.or` is binary. -/
theorem Op.isBinary_or : Op.or.IsBinary :=
  rfl

/-- The arguments of a binary operation are numbered `0` and `1`. -/
theorem Op.IsBinary.val_lt_two {op : Op} (h : op.IsBinary) (s : Fin (signature.Arity op)) :
    (s : ℕ) < 2 :=
  s.isLt.trans_eq h

/-- Two different arguments of a binary operation are all of its arguments. -/
theorem Op.IsBinary.eq_or_eq {op : Op} (h : op.IsBinary) {s t : Fin (signature.Arity op)}
    (hst : s ≠ t) (u : Fin (signature.Arity op)) : u = s ∨ u = t := by
  have hs := h.val_lt_two s
  have ht := h.val_lt_two t
  have hu := h.val_lt_two u
  rw [Ne, Fin.ext_iff] at hst
  rw [Fin.ext_iff, Fin.ext_iff]
  omega

/-- The cost function charging one for each AND and OR gate and nothing for negations and
constants. Its counterparts for the other bases are `Monotone.binaryCost`, its restriction to the
monotone basis (`Monotone.binaryCost_toDeMorgan`), and `Unbounded.andOrCost`, which also charges
the constants of the unbounded fan-in basis, its AND and OR gates of no arguments. -/
def binaryCost : Op → ℕ
  | .and | .or => 1
  | .const _ | .not => 0

/-- A conjunction gate has binary cost `1`. -/
@[simp] theorem binaryCost_and : binaryCost .and = 1 :=
  rfl

/-- A disjunction gate has binary cost `1`. -/
@[simp] theorem binaryCost_or : binaryCost .or = 1 :=
  rfl

/-- A negation gate has binary cost `0`. -/
@[simp] theorem binaryCost_not : binaryCost .not = 0 :=
  rfl

/-- A constant gate has binary cost `0`. -/
@[simp] theorem binaryCost_const (b : Bool) : binaryCost (.const b) = 0 :=
  rfl

/-- Every De Morgan operation has binary cost at most `1`. -/
theorem binaryCost_le_one (op : Op) : binaryCost op ≤ 1 := by
  cases op <;> simp

/-- The binary cost of an operation is `1` if it is binary and `0` otherwise. -/
theorem binaryCost_eq_ite (op : Op) : binaryCost op = if op.IsBinary then 1 else 0 := by
  cases op <;> simp [Op.IsBinary]

/-- Every operation in the De Morgan basis has arity at most `1 + binaryCost op`: constants have
arity `0`, negations have arity `1`, and binary AND/OR gates have arity `2 = 1 + 1`. -/
theorem arity_le_one_add_binaryCost (op : Op) :
    signature.Arity op ≤ 1 + binaryCost op := by
  cases op <;> simp [binaryCost]

end Boolean

open Boolean

/-- The number of binary gates of a program is at most its number of gates. -/
theorem Program.cost_binaryCost_le (p : Program Boolean.signature n g) :
    p.cost Boolean.binaryCost ≤ g :=
  (p.cost_le_mul Boolean.binaryCost_le_one).trans_eq (one_mul g)

/-- In a De Morgan program, the number of inputs supporting a frontier of wires is at most the size
of the frontier plus the number of binary (AND/OR) gates in the program. -/
theorem Program.card_biUnion_wireSupport_le_cost_binaryCost
    (p : Program signature n g) (frontier : Finset (Wire n g)) :
    (frontier.biUnion p.wireSupport).card ≤ frontier.card + p.cost binaryCost :=
  p.card_biUnion_wireSupport_le_cost binaryCost arity_le_one_add_binaryCost frontier

/-- A De Morgan circuit with `m` outputs has at most `m + c.program.cost binaryCost` supporting
inputs, since only binary AND and OR gates increase the number of reachable inputs. -/
theorem Circuit.card_inputSupport_le_cost_binaryCost (c : Circuit signature n m) :
    c.inputSupport.card ≤ m + c.program.cost binaryCost := by
  have hsub : c.inputSupport ⊆ (Finset.univ.image c.outputs).biUnion c.program.wireSupport := by
    intro i hi
    rw [Circuit.mem_inputSupport] at hi
    obtain ⟨o, ho⟩ := hi
    exact Finset.mem_biUnion.mpr ⟨c.outputs o, Finset.mem_image_of_mem _ (Finset.mem_univ o), ho⟩
  have hfront : (Finset.univ.image c.outputs).card ≤ m := by
    simpa using (Finset.card_image_le :
      (Finset.univ.image c.outputs).card ≤ (Finset.univ : Finset (Fin m)).card)
  calc c.inputSupport.card
      ≤ ((Finset.univ.image c.outputs).biUnion c.program.wireSupport).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.image c.outputs).card + c.program.cost binaryCost :=
        c.program.card_biUnion_wireSupport_le_cost_binaryCost _
    _ ≤ m + c.program.cost binaryCost := Nat.add_le_add_right hfront _

/-- If a De Morgan circuit computes `target` and every coordinate in `selected` is essential to
`target`, then `selected.card ≤ m + c.program.cost binaryCost`. -/
theorem Circuit.essential_le_cost_binaryCost (c : Circuit signature n m)
    {target : (Fin n → Bool) → Fin m → Bool} {selected : Finset (Fin n)}
    (hc : c.Computes interpretation target) (h : ∀ k ∈ selected, EssentialAt target k) :
    selected.card ≤ m + c.program.cost binaryCost :=
  (Finset.card_le_card fun k hk => (h k hk).mem_support hc.dependsOn).trans
    c.card_inputSupport_le_cost_binaryCost

/-- A De Morgan program has `binaryCost` equal to its gate count `g` if and only if every gate in
the program is a binary AND or OR gate. -/
theorem Program.cost_binaryCost_eq_iff_forall_isBinary {p : Program signature n g} :
    p.cost binaryCost = g ↔ ∀ k : Fin g, (p.lines k).op.IsBinary := by
  induction p with
  | empty =>
    simp only [Program.cost_empty, true_iff]
    exact fun k => k.elim0
  | @gate g p line ih =>
    rw [Program.cost_gate]
    have hp := p.cost_binaryCost_le
    have hline := binaryCost_le_one line.op
    constructor
    · intro h k
      have hp_eq : p.cost binaryCost = g := by omega
      have hline_eq : binaryCost line.op = 1 := by omega
      refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Program.lines_gate_last, Line.mapWires_op]
        rw [binaryCost_eq_ite] at hline_eq
        split_ifs at hline_eq with hb
        exact hb
      · rw [Program.lines_gate_castSucc, Line.mapWires_op]
        exact ih.mp hp_eq j
    · intro h
      have hp_eq : p.cost binaryCost = g := ih.mpr fun j => by
        simpa [Program.lines_gate_castSucc, Line.mapWires_op] using h j.castSucc
      have hbin : line.op.IsBinary := by
        simpa [Program.lines_gate_last, Line.mapWires_op] using h (Fin.last g)
      have hline_eq : binaryCost line.op = 1 := by
        simp [binaryCost_eq_ite, hbin]
      omega

/-- In a one-output De Morgan circuit whose input support has size at least `n`, if `c.size + 1 ≤ n`
then `c` has size `n - 1`, binary cost `n - 1`, and every gate of `c` is a binary AND or OR gate. -/
theorem Circuit.cost_binaryCost_eq_size_of_size_le {c : Circuit signature n 1}
    (hsupp : n ≤ c.inputSupport.card) (hsize : c.size + 1 ≤ n) :
    c.program.cost binaryCost = c.size ∧ c.size = n - 1 ∧
      ∀ k : Fin c.size, (c.program.lines k).op.IsBinary := by
  have hbin := c.card_inputSupport_le_cost_binaryCost
  have hle := c.program.cost_binaryCost_le
  have hcost_eq : c.program.cost binaryCost = c.size := by omega
  exact ⟨hcost_eq, by omega, Program.cost_binaryCost_eq_iff_forall_isBinary.mp hcost_eq⟩

end Cslib.Circuits
