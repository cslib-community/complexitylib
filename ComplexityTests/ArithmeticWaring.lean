/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Arithmetic.Waring
import Mathlib.Tactic.LinearCombination

/-!
# Waring sums and their circuit representation

The quadratic product attains the two-term bound. Tests also exercise degree zero, an odd-degree
representation, boundary splits, selected outputs before unused gates, shared terms, free
zero-feature inputs, nonuniform term weights, and independent coefficient-field universes.
-/

namespace ComplexityTests.ArithmeticWaring

universe u v

open Cslib.Circuits MvPolynomial

private def plusTerm : Waring.Term ℚ 2 := ⟨1 / 4, ![1, 1]⟩
private def minusTerm : Waring.Term ℚ 2 := ⟨-(1 / 4), ![1, -1]⟩

private theorem representsProduct : plusTerm.polynomial + minusTerm.polynomial =
    ∏ i : Fin 2, (X i : MvPolynomial (Fin 2) ℚ) := by
  have h : C (1 / 4 : ℚ) * (4 : MvPolynomial (Fin 2) ℚ) = 1 := by
    rw [← map_ofNat C, ← map_mul]
    norm_num
  norm_num [Waring.Term.polynomial, plusTerm, minusTerm, Fin.sum_univ_two, Fin.prod_univ_two]
  linear_combination (X 0 * X 1) * h

private def productCircuit : Circuit (SumOfTerms.signature (Waring.Term ℚ 2)) 0 2 where
  size := 4
  program := ((((Program.empty : Program (SumOfTerms.signature (Waring.Term ℚ 2)) 0 0).gate
    ⟨.term plusTerm, Fin.elim0⟩).gate ⟨.term minusTerm, Fin.elim0⟩).gate
      ⟨.add, ![.gate 0, .gate 1]⟩).gate ⟨.add, fun _ => .gate 0⟩
  outputs := ![.gate 2, .gate 0]

private theorem productCircuit_computes :
    productCircuit.eval (SumOfTerms.interpretation Waring.Term.polynomial) Fin.elim0 0 =
      ∏ i : Fin 2, X i :=
  representsProduct

-- Callers can use ordinary sums without supplying a circuit or a feature certificate.
private theorem product_sum :
    ∑ i : Fin 2, C (![1 / 4, -(1 / 4)] i : ℚ) *
      (∑ j : Fin 2, C (!![1, 1; 1, -1] i j : ℚ) * X j) ^ 2 =
        ∏ j : Fin 2, X j := by
  simpa [Fin.sum_univ_two, Waring.Term.polynomial, plusTerm, minusTerm, smul_eq_C_mul]
    using representsProduct

-- Degree zero still requires one constant power term to produce the empty product, 1.
private def constantCircuit : Circuit (SumOfTerms.signature (Waring.Term ℚ 0)) 0 1 :=
  Circuit.oneGate (.term ⟨1, Fin.elim0⟩) Fin.elim0

-- The output precedes an unused addition, a power term is read more than once, and splits zero,
-- full degree, and beyond the degree are all supported alongside degree zero.
example :
    productCircuit.program.cost SumOfTerms.termCost = 2 ∧
      2 ≤ productCircuit.program.cost SumOfTerms.termCost ∧
      Nat.centralBinom 1 ≤ (Finset.univ : Finset (Fin 2)).card ∧
      Nat.choose 2 0 ≤ productCircuit.program.cost SumOfTerms.termCost ∧
      Nat.choose 2 2 ≤ productCircuit.program.cost SumOfTerms.termCost ∧
      Nat.choose 2 3 ≤ productCircuit.program.cost SumOfTerms.termCost ∧
      constantCircuit.program.cost SumOfTerms.termCost = 1 ∧
      Nat.centralBinom 0 ≤ constantCircuit.program.cost SumOfTerms.termCost :=
  ⟨rfl,
    Waring.centralBinom_le_cost 1 productCircuit 0 productCircuit_computes,
    Waring.centralBinom_le_card 1 Finset.univ ![1 / 4, -(1 / 4)] !![1, 1; 1, -1] product_sum,
    Waring.choose_le_cost productCircuit 0 0 productCircuit_computes,
    Waring.choose_le_cost productCircuit 2 0 productCircuit_computes,
    Waring.choose_le_cost productCircuit 3 0 productCircuit_computes,
    rfl,
    by apply Waring.centralBinom_le_cost 0 constantCircuit 0
       simp [constantCircuit, Waring.Term.polynomial]⟩

-- An odd-degree product has a concrete four-term representation and a split-one bound of 3.
private def cubicCoefficients : Fin 4 → Fin 3 → ℚ :=
  ![![1, 1, 1], ![1, -1, -1], ![-1, 1, -1], ![-1, -1, 1]]

private theorem cubic_sum :
    ∑ i : Fin 4, C (1 / 24 : ℚ) *
      (∑ j : Fin 3, C (cubicCoefficients i j) * X j) ^ 3 = ∏ j : Fin 3, X j := by
  have h : C (1 / 24 : ℚ) * (24 : MvPolynomial (Fin 3) ℚ) = 1 := by
    rw [← map_ofNat C, ← map_mul]
    norm_num
  norm_num [cubicCoefficients, Fin.sum_univ_succ, Fin.prod_univ_succ]
  linear_combination (X 0 * X 1 * X 2) * h

-- Each term has its own rank budget; zero-valued dictionary entries can have weight zero.
private def weightedProgram : Program (SumOfTerms.signature ℚ) 0 4 :=
  ((((Program.empty : Program (SumOfTerms.signature ℚ) 0 0).gate ⟨.term 3, Fin.elim0⟩).gate
    ⟨.add, fun _ => .gate 0⟩).gate ⟨.add, ![.gate 0, .gate 1]⟩).gate
      ⟨.term 0, Fin.elim0⟩

-- Odd-degree Waring bound, free zero-feature inputs and weighted dictionary costs.
example :
    Nat.choose 3 1 ≤ (Finset.univ : Finset (Fin 4)).card ∧
      ((LinearMap.lsmul ℚ ℚ) ((Program.empty : Program (SumOfTerms.signature ℚ) 1 0).trace
        (SumOfTerms.interpretation id) (fun _ => 0) (.input 0))).rank ≤ 0 ∧
      weightedProgram.trace (SumOfTerms.interpretation id) Fin.elim0 (.gate 2) = 9 ∧
      weightedProgram.cost (SumOfTerms.dictionaryCost fun t => if t = 0 then 0 else 1) = 1 ∧
      ((LinearMap.lsmul ℚ ℚ)
        (weightedProgram.trace (SumOfTerms.interpretation id) Fin.elim0 (.gate 2))).rank ≤ 1 := by
  refine ⟨Waring.choose_le_card 1 Finset.univ (fun _ => 1 / 24) cubicCoefficients cubic_sum,
    ?_, by change (3 : ℚ) + (3 + 3) = 9; norm_num, rfl, ?_⟩
  · apply SumOfTerms.rank_trace_le (weight := fun _ => 1)
    · intro t
      exact (LinearMap.rank_le_domain _).trans_eq (Module.rank_self ℚ)
    · intro i
      simp
  · change _ ≤ (weightedProgram.cost
      (SumOfTerms.dictionaryCost fun t => if t = 0 then 0 else 1) : Cardinal)
    apply SumOfTerms.rank_trace_le
    · intro t
      by_cases ht : t = 0
      · simp [ht]
      · simpa [ht] using
          (LinearMap.rank_le_domain ((LinearMap.lsmul ℚ ℚ) t)).trans_eq (Module.rank_self ℚ)
    · exact fun i => i.elim0

-- The coefficient field need not be in the same universe as the finite matrix indices.
example {K : Type u} [Field K] [CharZero K] {ι : Type v} (indices : Finset ι)
    (scale : ι → K) (a : ι → Fin 2 → K)
    (h : ∑ i ∈ indices, C (scale i) * (∑ j, C (a i j) * X j) ^ 2 = ∏ j : Fin 2, X j) :
    2 ≤ indices.card :=
  Waring.choose_le_card 1 indices scale a h

end ComplexityTests.ArithmeticWaring
