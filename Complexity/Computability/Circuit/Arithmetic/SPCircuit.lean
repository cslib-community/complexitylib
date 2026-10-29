/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Arithmetic.SumFlatten
public import Complexity.Computability.Circuit.Unfolding

/-!
# Constant-depth arithmetic circuits of unbounded fan-in

Circuits in the model of Limaye, Srinivasan and Tavenas [LimayeSrinivasanTavenas2021, §1, p. 1, and
footnote 1] (paraphrased): a directed acyclic graph whose leaves are variables or constants from
the field, whose sum gates compute linear combinations of their children with constants on the
edges, and whose product gates compute products of their children; the *size* is the number of
nodes and the *product-depth* the largest number of product gates on a path from the root to a
leaf.

Here a circuit is a straight-line program of the library over `sigmaPiSignature K` with one output
(`SPCircuit K N`, a `Cslib.Circuits.Circuit`), the formulas of
`Complexity.Computability.Circuit.Arithmetic.SigmaPi` with sharing. It computes a polynomial
formally (`SPCircuit.polynomial`): it is evaluated in `MvPolynomial (Fin N) K` at the variables,
as formulas are. Its product-depth (`SPCircuit.productDepth`) is the generic weighted depth
`Cslib.Circuits.Circuit.depthWith` in which product gates cost one and the other operations
nothing.

**Size.** `Cslib.Circuits.Circuit.size` counts the gates, constants included, but not the `N`
input wires, so the node count of the source is `C.size + N`. The source's circuits are directed
acyclic graphs without multiple edges (our reading of §1 and footnote 1). A program line, in
contrast, may read a wire several times. For sum gates this is harmless: the edge constants of
repeated wires add up. For product gates it is not: a single product gate reading the same input
`m` times computes `x ^ m` at cost one, which a graph without multiple edges cannot do. So product
gates read pairwise distinct wires (`SPCircuit.IsSimple`), this formalization's rendering of the
absence of multiple edges, an original convention. Measuring the size instead by the wires read
would allow multiple edges without a hypothesis, but would depart from the source's node count.

**Unfolding.** A circuit unfolds into a formula computing the same polynomial
(`SPCircuit.toSPFormula`): unfold its output into a tree (`Cslib.Circuits.Circuit.toFormula`) and
merge consecutive sum gates (`SPFormula.flatten`). The product-depth does not increase
(`SPCircuit.productDepth_toSPFormula_le`) and a simple circuit of product-depth `Δ` unfolds into at
most `(C.size + N + 1) ^ (2 Δ + 1)` nodes (`SPCircuit.nodeCount_toSPFormula_le`, original): along a
path of the formula sum and product gates alternate, a sum gate reads at most one formula for each
of the `C.size + N` wires and a product gate at most `C.size + N` distinct wires. The source uses
such a step without proof, with the bound `s ^ (2Δ)` [LimayeSrinivasanTavenas2021, proof of
Lemma 15, §5, p. 12], which depends on the size convention.

## Main definitions

* `Cslib.Circuits.Arithmetic.SPCircuit`: circuits of unbounded fan-in with one output.
* `Cslib.Circuits.Arithmetic.SPCircuit.IsSimple`: product gates read pairwise distinct wires.
* `Cslib.Circuits.Arithmetic.SPFormula.IsSimple`: product gates of a formula have pairwise
  distinct arguments.
* `Cslib.Circuits.Arithmetic.SPCircuit.productDepth`,
  `Cslib.Circuits.Arithmetic.SPCircuit.polynomial`: product-depth and the computed polynomial.
* `Cslib.Circuits.Arithmetic.SPCircuit.toSPFormula`: the unfolded formula.

## Main results

* `Cslib.Circuits.Arithmetic.SPCircuit.polynomial_toSPFormula`: the unfolded formula computes the
  polynomial of the circuit.
* `Cslib.Circuits.Arithmetic.SPCircuit.productDepth_toSPFormula_le`: it is no deeper in products.
* `Cslib.Circuits.Arithmetic.SPCircuit.nodeCount_toSPFormula_le` (original): it has at most
  `(C.size + N + 1) ^ (2 * C.productDepth + 1)` nodes.
* `Cslib.Circuits.Arithmetic.SPCircuit.isSimple_toCircuit`: conversely, the circuit of a simple
  formula is simple, computes its polynomial (`SPCircuit.polynomial_toCircuit`) and is no deeper
  in products (`SPCircuit.productDepth_toCircuit_le`).

## References

* [N. Limaye, S. Srinivasan, S. Tavenas, *Superpolynomial lower bounds against low-depth algebraic
  circuits*][LimayeSrinivasanTavenas2021], ECCC TR21-081 revision 1, §1, p. 1, footnote 1, and
  the proof of Lemma 15 (§5, p. 12)
-/

@[expose] public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial

universe u

variable (K : Type u) in
/-- Arithmetic circuits of unbounded fan-in over `K` in `N` variables, with one output. -/
abbrev SPCircuit (N : ℕ) : Type u :=
  Circuit (sigmaPiSignature K) N 1

namespace SPFormula

variable {K : Type u} {N : ℕ}

/-- A formula is *simple* when the arguments of each of its product gates are pairwise distinct
formulas. Its circuit is then simple (`SPCircuit.isSimple_toCircuit`). -/
inductive IsSimple : SPFormula K N → Prop
  /-- An input is simple. -/
  | input (i : Fin N) : IsSimple (.input i)
  /-- An operation node is simple when its arguments are, and pairwise distinct if it is a product
  gate. -/
  | gate (op : SigmaPiOp K) (args : Fin op.arity → SPFormula K N)
      (hmul : ∀ m, op = .mul m → Function.Injective args) (hargs : ∀ j, IsSimple (args j)) :
      IsSimple (.gate op args)

end SPFormula

namespace SPCircuit

variable {K : Type u} {N : ℕ}

/-- A circuit is *simple* when each of its product gates reads pairwise distinct wires, as in a
graph without multiple edges. Sum gates may read a wire several times. -/
def IsSimple (C : SPCircuit K N) : Prop :=
  ∀ k m, (C.program.lines k).op = .mul m → Function.Injective (C.program.lines k).wires

/-- The product-depth: the largest number of product gates on a path from the output to an
input. -/
def productDepth (C : SPCircuit K N) : ℕ :=
  C.depthWith SigmaPiOp.mulCost

/-- The polynomial computed formally by a circuit: the circuit evaluated in
`MvPolynomial (Fin N) K` at the variables, a constant `a` denoting `C a`. -/
noncomputable def polynomial [CommSemiring K] (C : SPCircuit K N) : MvPolynomial (Fin N) K :=
  C.eval (sigmaPiInterpretationWith K MvPolynomial.C) X 0

/-- The formula unfolding the output computes the polynomial of the circuit. -/
theorem polynomial_toFormula [CommSemiring K] (C : SPCircuit K N) :
    SPFormula.polynomial (C.toFormula 0) = C.polynomial :=
  C.eval_toFormula 0 _ _

/-- **The unfolded formula** of a circuit: its output unfolded into a tree, with consecutive sum
gates merged. -/
noncomputable def toSPFormula [Semiring K] (C : SPCircuit K N) : SPFormula K N :=
  SPFormula.flatten (C.toFormula 0)

/-- The unfolded formula computes the polynomial of the circuit. -/
@[simp] theorem polynomial_toSPFormula [CommSemiring K] (C : SPCircuit K N) :
    C.toSPFormula.polynomial = C.polynomial := by
  rw [toSPFormula, SPFormula.polynomial_flatten, polynomial_toFormula]

/-- The unfolded formula is no deeper in products than the circuit. -/
theorem productDepth_toSPFormula_le [Semiring K] (C : SPCircuit K N) :
    C.toSPFormula.productDepth ≤ C.productDepth :=
  (SPFormula.productDepth_flatten_le _).trans (C.depthWith_toFormula_le 0 _)

/-- **Size of the unfolded formula** (original): a simple circuit with `C.size` gates and `N`
inputs, of product-depth `Δ`, unfolds into a formula of at most `(C.size + N + 1) ^ (2 Δ + 1)`
nodes. -/
theorem nodeCount_toSPFormula_le [Semiring K] {C : SPCircuit K N} (hC : C.IsSimple) :
    C.toSPFormula.nodeCount ≤ (C.size + N + 1) ^ (2 * C.productDepth + 1) := by
  classical
  set p := C.program
  set S : Finset (SPFormula K N) := Finset.univ.image p.wireFormula
  have hS : ∀ op args, Formula.gate op args ∈ S → ∀ j, args j ∈ S := by
    intro op args h j
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
    obtain ⟨w', hw'⟩ := p.exists_wireFormula_eq_of_eq_gate hw j
    exact Finset.mem_image.mpr ⟨w', Finset.mem_univ _, hw'⟩
  have hB : S.card ≤ C.size + N :=
    Finset.card_image_le.trans (by rw [Finset.card_univ, Wire.card, Nat.add_comm])
  have hmul : ∀ m args, Formula.gate (SigmaPiOp.mul m) args ∈ S → m ≤ C.size + N := by
    intro m args h
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp h
    cases w with
    | input i => cases hw
    | gate k =>
      rw [Program.wireFormula_gate, p.gateFormula_eq_gate] at hw
      have hop : (p.lines k).op = .mul m := (Formula.gate.inj hw).1
      have hcard := Fintype.card_le_of_injective _ (hC k m hop)
      rw [Fintype.card_fin, Wire.card, hop] at hcard
      exact (show m ≤ N + C.size from hcard).trans_eq (Nat.add_comm _ _)
  have hF : C.toFormula 0 ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ _)
  refine (SPFormula.nodeCount_flatten_le hS hB hmul hF).trans
    (Nat.pow_le_pow_right (Nat.succ_pos _) ?_)
  have := C.depthWith_toFormula_le 0 SigmaPiOp.mulCost
  unfold SPFormula.productDepth productDepth
  omega

/-! ### Formulas as circuits -/

/-- The circuit of a formula computes the polynomial of the formula. -/
@[simp] theorem polynomial_toCircuit [CommSemiring K] (F : SPFormula K N) :
    SPCircuit.polynomial F.toCircuit = F.polynomial :=
  F.eval_toCircuit _ _ 0

/-- The circuit of a formula is no deeper in products than the formula. -/
theorem productDepth_toCircuit_le (F : SPFormula K N) :
    SPCircuit.productDepth F.toCircuit ≤ F.productDepth :=
  F.depthWith_toCircuit_le _

/-- The circuit of a simple formula is simple. -/
theorem isSimple_toCircuit {F : SPFormula K N} (hF : F.IsSimple) :
    SPCircuit.IsSimple F.toCircuit := by
  intro k m hop
  have h := Formula.gateFormula_toCircuit_of_closed SPFormula.IsSimple
    (fun _ _ j h => by cases h with | gate _ _ _ h => exact h j) hF k
  rw [Program.gateFormula_eq_gate] at h
  cases h with
  | gate _ _ hmul _ => exact (hmul m hop).of_comp

end SPCircuit

end Cslib.Circuits.Arithmetic
