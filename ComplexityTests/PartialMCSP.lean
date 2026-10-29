/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Computability.Complexity.FineGrained.PermutationIndependentSet
import Complexity.Computability.MCSP.PartialETH
import Complexity.Computability.MCSP.PartialNP

/-!
# Tests: Partial-Function MCSP (`MCSP*`) and Bipartite Permutation Independent Set

Concrete tests for `PartialMCSP`, `PartialMCSP.BinaryGate`, `PartialMCSP.MonotoneReadOnce`,
the binary-gate fan-in and threshold-$n-1$ rigidity bridges, `PartialMCSP.verifier` certificates,
`BipartitePermutationIndependentSet` (directed and undirected LMS formulations), and Ilango's
$6n$-variable reduction (`ilangoGamma` Clauses (1)–(7), `ilangoPosFormula`, and `ilangoReduction`).
-/

namespace ComplexityTests.PartialMCSP

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Complexity Turing.MultiTapeTM

/-! ### Partial MCSP and binary-gate rigidity -/

/-- A partial truth table with all `*` (`none`) entries is computed by a 0-gate wire circuit for
`1 ≤ n`. -/
example : (⟨1, fun _ => none, 0⟩ : PartialMCSP.Instance) ∈ PartialMCSP := by
  rw [PartialMCSP.mem_iff_exists_circuit]
  exact ⟨⟨.empty, fun _ => Wire.input 0⟩, le_rfl,
    fun _ _ h => by simp [PartialMCSP.Instance.partialFunction] at h⟩

/-- The all-`none` 1-variable instance also maps to a yes-instance of `SuccinctMCSP`. -/
example : (⟨1, fun _ => none, 0⟩ : PartialMCSP.Instance).toSuccinct ∈ SuccinctMCSP := by
  rw [PartialMCSP.toSuccinct_mem_iff, PartialMCSP.mem_iff_exists_circuit]
  exact ⟨⟨.empty, fun _ => Wire.input 0⟩, le_rfl,
    fun _ _ h => by simp [PartialMCSP.Instance.partialFunction] at h⟩

/-- The 1-variable negation circuit with one `NOT` gate. -/
def notCircuit : Circuit signature 1 1 :=
  ⟨Program.empty.gate ⟨Op.not, ![Wire.input 0]⟩, fun _ => Wire.gate 0⟩

/-- The 2-variable conjunction circuit with one binary `AND` gate. -/
def andCircuit : Circuit signature 2 1 :=
  ⟨Program.empty.gate ⟨Op.and, ![Wire.input 0, Wire.input 1]⟩, fun _ => Wire.gate 0⟩

example :
    notCircuit.program.cost binaryCost = 0 ∧
      andCircuit.program.cost binaryCost = 1 ∧
      (¬∀ k : Fin notCircuit.size, (notCircuit.program.lines k).op.IsBinary) ∧
      (∀ k : Fin andCircuit.size, (andCircuit.program.lines k).op.IsBinary) ∧
      andCircuit.inputSupport.card = 1 + andCircuit.program.cost binaryCost := by
  refine ⟨by decide, by decide, ?_, ?_, by decide⟩
  · rw [← Program.cost_binaryCost_eq_iff_forall_isBinary]
    decide
  · rw [← Program.cost_binaryCost_eq_iff_forall_isBinary]
    decide

/-- Coordinate 0 is essential for the single-variable negation table. -/
example : (⟨1, ![some true, some false], 0⟩ : PartialMCSP.Instance).EssentialAt 0 := by
  refine ⟨![false], ![true], true, false, fun k hk => ?_, rfl, rfl, by decide⟩
  fin_cases k
  contradiction

/-- Under the binary-gate measure, unary gates (like `NOT`) carry zero cost, so single-variable
negation has binary-gate complexity 0. -/
example : (⟨1, ![some true, some false], 0⟩ : PartialMCSP.Instance) ∈ PartialMCSP.BinaryGate := by
  refine ⟨notCircuit, by decide, ?_⟩
  intro y b hy
  have hy_cases : y = ![false] ∨ y = ![true] := by
    cases h : y 0
    · left; ext i; fin_cases i; exact h
    · right; ext i; fin_cases i; exact h
  rcases hy_cases with rfl | rfl <;> cases hy <;> rfl

/-- Under the standard all-gates circuit size measure, single-variable negation requires at least 1
gate, so it cannot be computed at threshold 0. -/
example : (⟨1, ![some true, some false], 0⟩ : PartialMCSP.Instance) ∉ PartialMCSP := by
  intro hx
  obtain ⟨_ | ⟨b, _ | _⟩, hu, hV⟩ := PartialMCSP.exists_verifier_append hx
  · revert hu; decide
  · have := hV []; revert this; cases b <;> decide
  · simp [certLength, MCSP.budget] at hu

/-- By `PartialMCSP.ofTotal_mem_iff`, the total MCSP instance for 1-variable negation at threshold 0
is also outside `MCSP`. -/
example : (⟨1, ![true, false], 0⟩ : MCSP.Instance) ∉ MCSP := by
  rw [← PartialMCSP.ofTotal_mem_iff]
  have hEq : PartialMCSP.Instance.ofTotal ⟨1, ![true, false], 0⟩ =
      ⟨1, ![some true, some false], 0⟩ := by
    dsimp [PartialMCSP.Instance.ofTotal]
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [hEq]
  intro hx
  obtain ⟨_ | ⟨b, _ | _⟩, hu, hV⟩ := PartialMCSP.exists_verifier_append hx
  · revert hu; decide
  · have := hV []; revert this; cases b <;> decide
  · simp [certLength, MCSP.budget] at hu

/-- The all-gates and binary-gate cost measures separate on single-variable negation at threshold
zero: `BinaryGate` admits zero-cost unary negations, while `PartialMCSP` charges for every gate. -/
example : ∃ x : PartialMCSP.Instance, x ∈ PartialMCSP.BinaryGate ∧ x ∉ PartialMCSP :=
  ⟨⟨1, ![some true, some false], 0⟩, by
    refine ⟨⟨notCircuit, by decide, ?_⟩, ?_⟩
    · intro y b hy
      have hy_cases : y = ![false] ∨ y = ![true] := by
        cases h : y 0
        · left; ext i; fin_cases i; exact h
        · right; ext i; fin_cases i; exact h
      rcases hy_cases with rfl | rfl <;> cases hy <;> rfl
    · intro hx
      obtain ⟨_ | ⟨b, _ | _⟩, hu, hV⟩ := PartialMCSP.exists_verifier_append hx
      · revert hu; decide
      · have := hV []; revert this; cases b <;> decide
      · simp [certLength, MCSP.budget] at hu⟩

/-- The 2-variable `AND` table at threshold 0 has both variables essential and `0 + 1 < 2`, so it
cannot be computed with 0 binary gates (`not_mem_binaryGate_of_threshold_lt`). -/
example : (⟨2, ![some false, some false, some false, some true], 0⟩ : PartialMCSP.Instance) ∉
    PartialMCSP.BinaryGate := by
  refine PartialMCSP.not_mem_binaryGate_of_threshold_lt (fun i => ?_) (by decide)
  fin_cases i
  · refine ⟨![false, true], ![true, true], false, true, ?_, rfl, rfl, by decide⟩
    intro k hk
    fin_cases k <;> first | contradiction | rfl
  · refine ⟨![true, false], ![true, true], false, true, ?_, rfl, rfl, by decide⟩
    intro k hk
    fin_cases k <;> first | contradiction | rfl

/-! ### NP verifier certificates -/

-- Verifier evaluations for the 0-gate identity, 1-gate NOT, self-reading corrupted gate,
-- 0-gate rejection of NOT, and 1-gate 2-input AND.
example :
    PartialMCSP.verifier (⟨1, ![some false, some true], 0⟩, certificate 1 0 [] 0) = true ∧
      PartialMCSP.verifier
        (⟨1, ![some true, some false], 1⟩, certificate 1 1 [(.not, [0])] 1) = true ∧
      PartialMCSP.verifier
        (⟨1, ![some true, some false], 1⟩, certificate 1 1 [(.not, [1])] 1) = false ∧
      PartialMCSP.verifier
        (⟨1, ![some true, some false], 0⟩, certificate 1 0 [] 0) = false ∧
      PartialMCSP.verifier
        (⟨2, ![some false, some false, some false, some true], 1⟩,
          certificate 2 1 [(.and, [0, 1])] 2) = true := by decide

/-! ### Bipartite Permutation Independent Set -/

/-- An edgeless $n \times n$ bipartite permutation graph is always satisfiable, whereas a self-loop
on $(0, 0)$ for $n = 1$ (including `bpisOfColoring (([], []), 0)`) is unsatisfiable. -/
example (n : ℕ) :
    ((n, []) : BipartitePermutationGraph) ∈ BipartitePermutationIndependentSet ∧
      ((1, [((0, 0), (0, 0))]) : BipartitePermutationGraph) ∉
        BipartitePermutationIndependentSet ∧
      (BipartitePermutationIndependentSet.bpisOfColoring (([], []), 0)).1 = 1 ∧
      (BipartitePermutationIndependentSet.bpisOfColoring (([], []), 0)).2 =
        [((0, 0), (0, 0))] ∧
      BipartitePermutationIndependentSet.bpisOfColoring (([], []), 0) ∉
        BipartitePermutationIndependentSet := by
  refine ⟨⟨1, 1, fun _ h => by simp at h⟩, ?_, by decide, by decide, ?_⟩
  · rintro ⟨π₁, π₂, h⟩
    exact h ((0, 0), (0, 0)) (by simp) (by decide) (by decide) (by decide) (by decide)
      (Subsingleton.elim (π₁ 0) 0) (Subsingleton.elim (π₂ 0) 0)
  · have hG : BipartitePermutationIndependentSet.bpisOfColoring (([], []), 0) =
        (1, [((0, 0), (0, 0))]) := by decide
    rw [hG]
    rintro ⟨π₁, π₂, h⟩
    exact h ((0, 0), (0, 0)) (by simp) (by decide) (by decide) (by decide) (by decide)
      (Subsingleton.elim (π₁ 0) 0) (Subsingleton.elim (π₂ 0) 0)

/-! ### Ilango's $n = 2$ reduction: Clauses (1)–(7) of `ilangoGamma` and `ilangoPosFormula` -/

/-- Concrete $n = 2$ bipartite permutation graph with a single conflict edge $((0, 0), (1, 1))$
forbidding simultaneous assignments $\pi_1(0) = 0$ and $\pi_2(1) = 1$. -/
abbrev bpisG2 : BipartitePermutationGraph := (2, [((0, 0), (1, 1))])

/-- Block-preserving permutation $\pi_{\mathrm{swap}} = (2\;\;3) \in S_4$ that fixes the left
block $\{0, 1\}$ and swaps the right block $\{2, 3\}$. -/
abbrev bpisG2Perm : Equiv.Perm (Fin (2 * bpisG2.1)) :=
  Equiv.swap (2 : Fin 4) (3 : Fin 4)

/-- Evaluates Clauses (1)–(7) and the default `none` branch of `ilangoGamma` on $(1, [])$ and
`bpisG2`, and checks `ilangoPosFormula` on the Clause (7) probe input for $\pi = 1$ and
$\pi_{\mathrm{swap}}$. -/
example :
    PartialMCSP.ilangoGamma (1, []) (fun _ => false) = some false ∧
      PartialMCSP.ilangoGamma (1, [])
        (PartialMCSP.packXYZ PartialMCSP.ones2n (fun _ => false) (fun _ => true)) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ PartialMCSP.zeros2n ![true, false, false, false]
          ![true, false, false, false]) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ PartialMCSP.zeros2n ![true, false, false, false]
          ![false, true, false, false]) = some false ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ PartialMCSP.ones2n PartialMCSP.zeros2n
          ![false, false, true, false]) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ ![false, true, false, false] PartialMCSP.zeros2n
          PartialMCSP.ones2n) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ ![true, false, false, false] ![false, true, false, false]
          PartialMCSP.zeros2n) = some false ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ ![false, true, false, false] PartialMCSP.zeros2n
          PartialMCSP.leftHalfOnes) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ ![false, false, true, false] PartialMCSP.zeros2n
          PartialMCSP.leftHalfOnes) = some false ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ ![false, false, true, false] PartialMCSP.zeros2n
          PartialMCSP.rightHalfOnes) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ ![true, false, false, false] PartialMCSP.zeros2n
          PartialMCSP.rightHalfOnes) = some false ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ (PartialMCSP.antiUnitPair (n := 2) 0 1) PartialMCSP.zeros2n
          (PartialMCSP.unitPair (n := 2) 0 1)) = some true ∧
      PartialMCSP.ilangoGamma bpisG2
        (PartialMCSP.packXYZ (PartialMCSP.antiUnitPair (n := 2) 0 0) PartialMCSP.zeros2n
          (PartialMCSP.unitPair (n := 2) 0 1)) = none ∧
      (PartialMCSP.ilangoPosFormula (by decide : 0 < bpisG2.1) 1).eval
        (PartialMCSP.packXYZ (PartialMCSP.antiUnitPair (n := 2) 0 1) PartialMCSP.zeros2n
          (PartialMCSP.unitPair (n := 2) 0 1)) = false ∧
      (PartialMCSP.ilangoPosFormula (by decide : 0 < bpisG2.1) bpisG2Perm).eval
        (PartialMCSP.packXYZ (PartialMCSP.antiUnitPair (n := 2) 0 1) PartialMCSP.zeros2n
          (PartialMCSP.unitPair (n := 2) 0 1)) = true := by decide

/-- `bpisG2Perm` is block-preserving and avoids the conflict edge $((0, 0), (1, 1))$ of `bpisG2`. -/
theorem bpisG2_satisfiesUndirected : bpisG2.SatisfiesUndirected bpisG2Perm := by
  refine ⟨fun i => by fin_cases i <;> decide, ?_⟩
  intro e he
  simp only [List.mem_singleton] at he
  subst he
  decide +revert

/-- By `agreesWith_ilangoPosFormula_of_satisfiesUndirected`, the read-once positive formula
`ilangoPosFormula _ bpisG2Perm` of size $6 \cdot 2 - 1 = 11$ agrees with `ilangoInstance bpisG2`
on every defined entry. -/
example : (PartialMCSP.ilangoInstance bpisG2).AgreesWith
    (PartialMCSP.ilangoPosFormula (by decide : 0 < bpisG2.1) bpisG2Perm).eval :=
  PartialMCSP.agreesWith_ilangoPosFormula_of_satisfiesUndirected
    (by decide : 0 < bpisG2.1) bpisG2_satisfiesUndirected

/-- Consequently `bpisG2 ∈ BipartitePermutationIndependentSet` and `ilangoReduction bpisG2` belongs
to `PartialMCSP.MonotoneReadOnce`, `PartialMCSP.BinaryGate`, and `PartialMCSP`. -/
example : PartialMCSP.ilangoReduction bpisG2 ∈ PartialMCSP.MonotoneReadOnce ∧
    PartialMCSP.ilangoReduction bpisG2 ∈ PartialMCSP.BinaryGate ∧
    PartialMCSP.ilangoReduction bpisG2 ∈ PartialMCSP := by
  have hmem : bpisG2 ∈ BipartitePermutationIndependentSet :=
    (BipartitePermutationIndependentSet.mem_iff_exists_satisfiesUndirected bpisG2).mpr
      ⟨bpisG2Perm, bpisG2_satisfiesUndirected⟩
  have hRO :=
    PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_monotoneReadOnce
      bpisG2
  exact ⟨hRO.mp hmem,
    (PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem_binaryGate
      bpisG2).mp hmem,
    (PartialMCSP.mem_BipartitePermutationIndependentSet_iff_ilangoReduction_mem
      bpisG2).mp hmem⟩

/-- Unary-to-binary threshold re-encoding is polynomial-time computable. -/
example : ComputableInPolyTime id PartialMCSP.enc PartialMCSP.encBinary :=
  PartialMCSP.computableInPolyTime_id_enc_encBinary

/-- Under `ETH`, `PartialMCSP.MonotoneReadOnce` is not decidable in time $2^{o(m \log m)}$ under
either unary or binary threshold encoding. -/
example (h : ETH) :
    ¬DecidableInSubexpTime PartialMCSP.MonotoneReadOnce PartialMCSP.enc
      (fun I => I.arity * Nat.log 2 I.arity) ∧
    ¬DecidableInSubexpTime PartialMCSP.MonotoneReadOnce PartialMCSP.encBinary
      (fun I => I.arity * Nat.log 2 I.arity) :=
  ⟨h.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce,
    h.not_decidableInSubexpTime_PartialMCSP_monotoneReadOnce_encBinary⟩

end ComplexityTests.PartialMCSP
