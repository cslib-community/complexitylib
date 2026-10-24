/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.ShannonConstruction
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Shannon synthesis

Choosing `⌊log₂ n⌋ - 1` address bits in the shared-column construction yields a circuit
with at most `27 * 2 ^ n / n` gates for every Boolean function on `n ≥ 16` inputs.
The natural-number division is applied after multiplying by 27. All gates, including
constants and negations, are counted.

The synthesizer is a computable function of a supplied truth table. This module bounds
the resulting circuit's size; it does not certify the synthesizer's running time.

## Main definitions

* `Cslib.Circuits.Boolean.ShannonSynthesis.addressWidth`,
  `Cslib.Circuits.Boolean.ShannonSynthesis.dataWidth`: widths of the address and data blocks in the
  finite Shannon split.
* `Cslib.Circuits.Boolean.ShannonSynthesis.synthesize`: choose the split and build a circuit.

## Main results

* `Cslib.Circuits.Boolean.ShannonSynthesis.computes_synthesize`: correctness of synthesis.
* `Cslib.Circuits.Boolean.ShannonSynthesis.size_synthesize_le`: the finite `27 * 2 ^ n / n` bound.
* `Cslib.Circuits.Boolean.ShannonSynthesis.exists_circuit`: the corresponding existence theorem.

## References

* [C. E. Shannon, *The Synthesis of Two-Terminal Switching Circuits*][Shannon1949].
* The parameter choice and finite constant follow MassProduction/ShannonParameters.lean
  and MassProduction/ShannonSynthesis.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.ShannonSynthesis

variable {n : ℕ}

/-- Width of the address block in finite Shannon synthesis. -/
def addressWidth (n : ℕ) : ℕ := Nat.log 2 n - 1

/-- Width of the remaining data block. -/
def dataWidth (n : ℕ) : ℕ := n - addressWidth n

/-- The address width and data width sum to the total input width `n`. -/
@[simp] theorem addressWidth_add_dataWidth (n : ℕ) : addressWidth n + dataWidth n = n :=
  Nat.add_sub_of_le ((Nat.sub_le _ _).trans (Nat.log_le_self 2 n))

private theorem address_estimates (hn : 16 ≤ n) :
    2 * 2 ^ addressWidth n ≤ n ∧ n < 4 * 2 ^ addressWidth n := by
  have hlog : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) (by lia)
  have heq : Nat.log 2 n = addressWidth n + 1 := by unfold addressWidth; lia
  have hlo := Nat.pow_log_le_self 2 (show n ≠ 0 by lia)
  have hhi := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  rw [heq, pow_succ] at hlo
  rw [heq, pow_succ, pow_succ] at hhi
  lia

private theorem square_le_two_pow (hn : 4 ≤ n) : n * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    nlinarith

private theorem four_mul_le_two_pow (hn : 4 ≤ n) : 4 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ]
    lia

/-- The chosen split bounds the complete gate ledger, with natural division after scaling. -/
theorem bound_le (hn : 16 ≤ n) :
    bound (addressWidth n) (dataWidth n) ≤ 27 * 2 ^ n / n := by
  have ⟨haddr, hinput⟩ := address_estimates hn
  have hsplit : 2 ^ dataWidth n * 2 ^ addressWidth n = 2 ^ n := by
    rw [← pow_add, Nat.add_comm, addressWidth_add_dataWidth]
  have hdata : 6 * 2 ^ dataWidth n * n ≤ 24 * 2 ^ n := calc
    _ ≤ 6 * 2 ^ dataWidth n * (4 * 2 ^ addressWidth n) :=
      Nat.mul_le_mul_left _ hinput.le
    _ = 24 * (2 ^ dataWidth n * 2 ^ addressWidth n) := by ring
    _ = 24 * 2 ^ n := by rw [hsplit]
  have haddress : 4 * 2 ^ addressWidth n * n ≤ 2 * 2 ^ n := calc
    _ = 2 * ((2 * 2 ^ addressWidth n) * n) := by ring
    _ ≤ 2 * (n * n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right n haddr)
    _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (square_le_two_pow (by lia))
  have hlog : 4 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by decide) hn
  have hquarter : 4 * Nat.log 2 n ≤ n :=
    (four_mul_le_two_pow hlog).trans (Nat.pow_log_le_self 2 (by lia))
  have hexponent : 2 ^ addressWidth n + addressWidth n + (Nat.log 2 n + 1) ≤ n := by
    dsimp only [addressWidth] at haddr ⊢
    lia
  have hlibrary : (2 ^ (2 ^ addressWidth n) * 2 ^ addressWidth n) * n ≤ 2 ^ n := calc
    _ ≤ (2 ^ (2 ^ addressWidth n) * 2 ^ addressWidth n) * 2 ^ (Nat.log 2 n + 1) :=
      Nat.mul_le_mul_left _ (Nat.lt_pow_succ_log_self (by decide) n).le
    _ = 2 ^ (2 ^ addressWidth n + addressWidth n + (Nat.log 2 n + 1)) := by
      rw [← pow_add, ← pow_add]
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hexponent
  apply (Nat.le_div_iff_mul_le (by lia : 0 < n)).mpr
  calc
    bound (addressWidth n) (dataWidth n) * n =
        4 * 2 ^ addressWidth n * n + 6 * 2 ^ dataWidth n * n +
          (2 ^ (2 ^ addressWidth n) * 2 ^ addressWidth n) * n := by
      simp only [bound]
      ring
    _ ≤ 27 * 2 ^ n := by lia

/-- Build a circuit from a truth table, using the chosen address/data split. -/
def synthesize (f : BooleanFunction n) : Circuit signature n 1 :=
  (circuit (fun x => f (x ∘ Fin.cast (addressWidth_add_dataWidth n).symm))).comp
    (Circuit.wiring signature (Fin.cast (addressWidth_add_dataWidth n)))

/-- `synthesize f` evaluates to `f x` at its single output wire. -/
@[simp] theorem eval_synthesize (f : BooleanFunction n) (x : BitString n) (i : Fin 1) :
    (synthesize f).eval interpretation x i = f x := by
  simp [synthesize, Function.comp_def]

/-- The synthesized circuit computes the supplied Boolean function. -/
theorem computes_synthesize (f : BooleanFunction n) :
    (synthesize f).Computes interpretation (single f) := by
  intro x
  funext i
  exact eval_synthesize f x i

/-- Every gate is counted, including constants and negations. -/
theorem size_synthesize_le (hn : 16 ≤ n) (f : BooleanFunction n) :
    (synthesize f).size ≤ 27 * 2 ^ n / n := by
  simp only [synthesize, Circuit.size_comp, Circuit.size_wiring, Nat.zero_add]
  exact (size_circuit_le _).trans (bound_le hn)

/-- A finite Shannon bound on the total number of gates, valid at every width at least 16. -/
theorem exists_circuit (hn : 16 ≤ n) (f : BooleanFunction n) :
    ∃ c : Circuit signature n 1, c.Computes interpretation (single f) ∧
      c.size ≤ 27 * 2 ^ n / n :=
  ⟨synthesize f, computes_synthesize f, size_synthesize_le hn f⟩

end Cslib.Circuits.Boolean.ShannonSynthesis
