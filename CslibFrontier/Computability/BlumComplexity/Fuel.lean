/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.BlumComplexity.Basic

/-!
# The fuel of `evaln` as a Blum complexity measure

Mathlib's `Nat.Partrec.Code.evaln k c n` evaluates the code `c` on `n` with fuel `k`. It fails when
the evaluation recurses too deeply or meets a number `≥ k`. The fuel is monotone
(`Code.evaln_mono`) and sufficient fuel always exists for halting computations
(`Code.evaln_complete`). The *fuel* of `c` on `n`, `evalnFuel c n`, is the least `k` for which
`evaln k c n` succeeds. It satisfies Blum's axioms [Blum1967]: it is defined exactly when `c` halts
on `n`, and `evalnFuel c n = k` is decidable because `evaln` is primitive recursive
(`Code.primrec_evaln`). This gives the complexity measure `fuelMeasure`.

The fuel bounds both the recursion depth of the evaluation and the size of every number it
inspects. In particular `n < evalnFuel c n` whenever it is defined (`lt_of_mem_evalnFuel`), so
complexity classes of bounds `t ≤ id` are empty for this measure. The fuel is not the step count
of a machine model; it is the natural cost measure of Mathlib's evaluator.

## Main definitions

* `Cslib.BlumComplexity.evalnFuel`: the least fuel with which `evaln` succeeds.
* `Cslib.BlumComplexity.fuelMeasure`: the Blum complexity measure given by `evalnFuel`.

## Main results

* `Cslib.BlumComplexity.mem_evalnFuel_iff`: `evalnFuel c n = k` exactly when `evaln k c n`
  succeeds and `evaln j c n` fails for every `j < k`.
* `Cslib.BlumComplexity.dom_evalnFuel_iff`: Blum's first axiom.
* `Cslib.BlumComplexity.computablePred_mem_evalnFuel`: Blum's second axiom.
* `Cslib.BlumComplexity.lt_of_mem_evalnFuel`: the fuel exceeds the input.

## References

* [M. Blum, *A machine-independent theory of the complexity of recursive functions*][Blum1967]
-/

public section

namespace Cslib.BlumComplexity

open Nat.Partrec

/-- The least fuel `k` with which `Code.evaln k c n` succeeds. It is defined exactly when `c` halts
on `n`. -/
def evalnFuel (c : Code) (n : ℕ) : Part ℕ :=
  Nat.rfind fun k => Part.some (Code.evaln k c n).isSome

/-- `evalnFuel c n = k` exactly when `evaln k c n` succeeds and `evaln j c n` fails for every
`j < k`. -/
theorem mem_evalnFuel_iff {c : Code} {n k : ℕ} :
    k ∈ evalnFuel c n ↔
      (Code.evaln k c n).isSome ∧ ∀ j < k, (Code.evaln j c n).isSome = false := by
  refine Nat.mem_rfind.trans ?_
  simp only [Part.mem_some_iff, eq_comm (a := true), eq_comm (a := false)]

/-- Blum's first axiom for the fuel: it is defined exactly when the code halts. -/
theorem dom_evalnFuel_iff (c : Code) (n : ℕ) : (evalnFuel c n).Dom ↔ (c.eval n).Dom := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Part.dom_iff_mem.1 h
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (mem_evalnFuel_iff.1 hk).1
    exact Part.dom_iff_mem.2 ⟨x, Code.evaln_sound hx⟩
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.1 h
    obtain ⟨k, hk⟩ := Code.evaln_complete.1 hx
    obtain ⟨j, hj, -⟩ := Nat.rfind_min' (p := fun k => (Code.evaln k c n).isSome) (m := k)
      (by simp [Option.mem_def.1 hk])
    exact Part.dom_iff_mem.2 ⟨j, hj⟩

private theorem computablePred_evaln_isSome {α : Type*} [Primcodable α] {k : α → ℕ}
    {c : α → Code} {n : α → ℕ} (hk : Computable k) (hc : Computable c) (hn : Computable n) :
    ComputablePred fun a => (Code.evaln (k a) (c a) (n a)).isSome := by
  refine ComputablePred.computable_iff.2 ⟨_, ?_, rfl⟩
  exact Primrec.option_isSome.to_comp.comp (Code.primrec_evaln.to_comp.comp ((hk.pair hc).pair hn))

/-- Blum's second axiom for the fuel: `evalnFuel c n = k` is decidable. -/
theorem computablePred_mem_evalnFuel :
    ComputablePred fun (((c, n), k) : (Code × ℕ) × ℕ) => k ∈ evalnFuel c n := by
  have hc : Computable fun x : (Code × ℕ) × ℕ => x.1.1 := Computable.fst.comp Computable.fst
  have hn : Computable fun x : (Code × ℕ) × ℕ => x.1.2 := Computable.snd.comp Computable.fst
  refine ((computablePred_evaln_isSome Computable.snd hc hn).and ?_).of_eq fun x =>
    mem_evalnFuel_iff.symm
  refine ComputablePred.forall_lt
    (p := fun (x : (Code × ℕ) × ℕ) j => (Code.evaln j x.1.1 x.1.2).isSome = false) ?_
    Computable.snd
  exact (computablePred_evaln_isSome Computable.snd (hc.comp Computable.fst)
    (hn.comp Computable.fst)).not.of_eq fun _ => by
      rw [Bool.not_eq_true]
      rfl

/-- The **fuel measure**: the Blum complexity measure whose cost is the least fuel with which
`Code.evaln` succeeds. -/
@[expose] def fuelMeasure : BlumMeasure where
  cost := evalnFuel
  dom_cost_iff := dom_evalnFuel_iff
  computablePred_mem_cost := computablePred_mem_evalnFuel

/-- The cost of the fuel measure is `evalnFuel`. -/
@[simp]
theorem fuelMeasure_cost : fuelMeasure.cost = evalnFuel :=
  rfl

/-- The fuel exceeds the input, since `evaln k c n` fails unless `n < k`. -/
theorem lt_of_mem_evalnFuel {c : Code} {n k : ℕ} (h : k ∈ evalnFuel c n) : n < k := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (mem_evalnFuel_iff.1 h).1
  exact Code.evaln_bound hx

end Cslib.BlumComplexity
