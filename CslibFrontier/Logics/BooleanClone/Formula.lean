/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.BooleanClone.Post
public import CslibFrontier.Computability.Circuit.Formula

/-!
# Realizing generated Boolean operations by formulas and circuits

The signature of a family `G` has one operation symbol for each positive-arity generator.
A finite superposition derivation is equivalent to a formula over this signature. Thus Post's
criterion constructs formulas and circuits for every positive number of inputs. No circuit-size
bound or nullary synthesis claim is made: unary constant functions still need an input leaf.
In particular this permits a NAND-only signature, whereas circuit `Interpretation.IsComplete`
quantifies over zero inputs too and does not hold for that signature.

## Main definitions

* `Cslib.Logic.BooleanClone.signature`: the signature of the positive-arity generators.
* `Cslib.Logic.BooleanClone.interpretation`: their Boolean truth-table interpretation.

## Main results

* `Cslib.Logic.BooleanClone.generated_iff_exists_formula`: finite derivations are formulas.
* `Cslib.Logic.BooleanClone.exists_formula_of_postCriterion`: positive-arity formula realization.
* `Cslib.Logic.BooleanClone.exists_circuit_of_postCriterion`: positive-arity circuit realization.
* `Cslib.Logic.BooleanClone.not_isComplete_interpretation`: no zero-input circuit completeness.
-/

public section

namespace Cslib.Logic.BooleanClone

open Cslib.Circuits

/-- One symbol per positive-arity member of the generating family. -/
@[expose] def signature (G : (n : ℕ) → Set ((Fin n → Bool) → Bool)) : Signature where
  Op := Σ n, {f : (Fin n → Bool) → Bool // 0 < n ∧ f ∈ G n}
  Arity op := op.1

/-- Interpret every generator symbol by its given truth table. -/
@[expose] def interpretation (G : (n : ℕ) → Set ((Fin n → Bool) → Bool)) :
    Interpretation (signature G) Bool := fun ⟨_, f, _⟩ => f

/-- Finite superposition derivations are exactly formulas over the generators, at positive
input arity. -/
theorem generated_iff_exists_formula (G : (n : ℕ) → Set ((Fin n → Bool) → Bool))
    {n : ℕ} (f : (Fin n → Bool) → Bool) :
    Generated G f ↔ 0 < n ∧ ∃ F : Formula (signature G) n, F.Computes (interpretation G) f := by
  classical
  constructor
  · intro h
    refine ⟨h.arity_pos, ?_⟩
    induction h with
    | of_mem hn hf => exact ⟨.gate ⟨_, _, hn, hf⟩ Formula.input, fun _ => rfl⟩
    | projection i => exact ⟨.input i, fun _ => rfl⟩
    | @comp m n hm hn f g hf hg ihf ihg =>
      obtain ⟨F, hF⟩ := ihf
      let args (i) := Classical.choose (ihg i)
      have hargs (i) := Classical.choose_spec (ihg i)
      refine ⟨F.bind args, fun a => ?_⟩
      rw [Formula.eval_bind]
      convert hF (fun i => g i a) using 1
      congr 1
      exact funext (fun i => hargs i a)
  · rintro ⟨hn, F, hF⟩
    have hgen : Generated G (F.eval (interpretation G)) := by
      clear hF
      induction F with
      | input i => exact .projection i
      | gate op args ih =>
        exact .comp op.2.property.1 hn
          (.of_mem op.2.property.1 op.2.property.2) ih
    simpa only [Formula.computes_iff.mp hF] using hgen

/-- Post's criterion supplies a formula for every positive-arity Boolean function. -/
theorem exists_formula_of_postCriterion {G : (n : ℕ) → Set ((Fin n → Bool) → Bool)}
    (hG : PostCriterion G) {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    ∃ F : Formula (signature G) n, F.Computes (interpretation G) f :=
  ((generated_iff_exists_formula G f).mp ((functionallyComplete_iff G).mpr hG n hn f)).2

/-- Post's criterion supplies a circuit for every positive-arity Boolean function.
Zero-input functions and quantitative circuit bounds are not claimed. -/
theorem exists_circuit_of_postCriterion {G : (n : ℕ) → Set ((Fin n → Bool) → Bool)}
    (hG : PostCriterion G) {n : ℕ} (hn : 0 < n) (f : (Fin n → Bool) → Bool) :
    ∃ c : Circuit (signature G) n 1, c.Computes (interpretation G) (single f) := by
  obtain ⟨F, hF⟩ := exists_formula_of_postCriterion hG hn f
  exact ⟨F.toCircuit, hF.toCircuit⟩

/-- A signature containing only positive-arity gates has no circuit with zero inputs and
one output: there is no wire to supply the first gate or to select as an output. -/
theorem not_nonempty_circuit_zero (G : (n : ℕ) → Set ((Fin n → Bool) → Bool)) :
    ¬ Nonempty (Circuit (signature G) 0 1) := by
  have emptyWire : Wire 0 0 → False := by
    intro w
    cases w with
    | input i => exact Fin.elim0 i
    | gate i => exact Fin.elim0 i
  have hsize {k : ℕ} (p : Program (signature G) 0 k) : k = 0 := by
    induction p with
    | empty => rfl
    | @gate k p line ih =>
      subst k
      exact False.elim (emptyWire (line.wires ⟨0, line.op.2.property.1⟩))
  rintro ⟨c⟩
  have hw := c.outputs 0
  rw [hsize c.program] at hw
  exact emptyWire hw

/-- The positive-arity generator signature never satisfies the circuit notion that also
requires zero-input functions, even when it is functionally complete at positive arities. -/
theorem not_isComplete_interpretation (G : (n : ℕ) → Set ((Fin n → Bool) → Bool)) :
    ¬ (interpretation G).IsComplete := by
  intro h
  let _ := h
  obtain ⟨c, _⟩ := Interpretation.IsComplete.exists_computes_single
    (I := interpretation G) (fun _ : Fin 0 → Bool => false)
  exact not_nonempty_circuit_zero G ⟨c⟩

end Cslib.Logic.BooleanClone
