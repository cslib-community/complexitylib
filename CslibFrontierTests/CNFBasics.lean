/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Logics.Propositional.CNF.StdSat
import CslibFrontier.Logics.Propositional.CNF.Simplification
import CslibFrontier.Logics.Propositional.CNF.UnitPropagation
import CslibFrontier.Computability.Complexity.Problems.SAT.Declared

/-!
# Kernel-checked tests for CNF bridges, restriction, simplification, unit propagation, and
declared encodings

Nonvacuous examples covering:
* `Std.Sat.CNF (Fin n)` and `Std.Sat.CNF.relabelFin` round trips and model-count identities.
* `CNF.restrict` evaluation, branching additivity when variables disappear, and occurrence bounds.
* `removeTautologies`, `dedup`, `reduce`, and `countingNormalize` size and scaling behavior.
* `unitPropagate` unit-cascade satisfiability, conflict detection, idempotence, and model counting.
* `DeclaredCNF` round-trip decoding and rejection of out-of-range and malformed words.
-/

namespace CslibFrontierTests.CNFBasics

open Cslib.Logic.PL Cslib.Complexity

/-! ### `Std.Sat.CNF` and `Fin n` model-counting controls -/

private def stdFinFormula : Std.Sat.CNF (Fin 3) :=
  let c0 := Std.Sat.CNF.Clause.unit (0 : Fin 3) true
  let c1 := (Std.Sat.CNF.Clause.unit (0 : Fin 3) false).add (1 : Fin 3) true
  ((Std.Sat.CNF.empty).add c0).add c1

example : CNF.toStdSat (CNF.ofStdSat stdFinFormula) = stdFinFormula :=
  CNF.toStdSat_ofStdSat stdFinFormula

example : (CNF.ofStdSat stdFinFormula).numVars = 2 := by
  decide

example : (CNF.ofStdSat stdFinFormula).modelCountOn Finset.univ = 2 := by
  decide

example : Fintype.card {a : Fin 3 → Bool // stdFinFormula.eval a = true} = 2 := by
  rw [CNF.card_eval_ofStdSat_eq_modelCountOn]
  decide

example : Fintype.card {a : Fin 3 → Bool // stdFinFormula.eval a = true} =
    2 ^ (3 - (CNF.ofStdSat stdFinFormula).numVars) * (CNF.ofStdSat stdFinFormula).modelCount :=
  CNF.card_eval_eq_two_pow_mul_modelCount stdFinFormula

private def stdNatUnsat : Std.Sat.CNF ℕ :=
  (Std.Sat.CNF.empty.add (.unit 0 true)).add (.unit 0 false)

example : ¬(CNF.ofStdSat stdNatUnsat.relabelFin).Satisfiable := by
  rw [CNF.satisfiable_ofStdSat_relabelFin_iff, ← CNF.unsat_iff_not_satisfiable_ofStdSat,
    Std.Sat.CNF.unsat_iff_not_sat]
  intro σ hσ
  have h1 := Std.Sat.CNF.sat_of_mem hσ (c := .unit 0 true) (by simp [stdNatUnsat])
  have h2 := Std.Sat.CNF.sat_of_mem hσ (c := .unit 0 false) (by simp [stdNatUnsat])
  simp only [Std.Sat.CNF.Clause.sat_unit_iff] at h1 h2
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ### General `CNF.restrict` branching and variable-elimination controls -/

private def branchingFormula : CNF ℕ :=
  [[(0, true), (1, true)], [(2, true)]]

example :
    branchingFormula.modelCountOn (Finset.range 3) =
      (branchingFormula.restrict 0 false).modelCountOn ((Finset.range 3).erase 0) +
        (branchingFormula.restrict 0 true).modelCountOn ((Finset.range 3).erase 0) :=
  CNF.modelCountOn_eq_add_restrict branchingFormula (Finset.range 3) (by decide)

example : (branchingFormula.restrict 0 true).numVars = 1 := by
  decide

example : (branchingFormula.restrict 0 true).occurrences 0 = 0 :=
  CNF.occurrences_restrict_self branchingFormula 0 true

example : branchingFormula.modelCount = 3 := by
  rw [CNF.modelCount_eq_add_restrict_of_mem_vars branchingFormula (v := 0) (by decide)]
  decide

/-! ### Simplification, subsumption, and deduplication bounds -/

private def noisyFormula : CNF ℕ :=
  [[(0, true), (0, true)], [(0, true), (1, false)], [(2, true), (2, false)], [(0, true)]]

example : CNF.Sparsification.countingNormalize noisyFormula = [[(0, true)]] := by
  decide

example : noisyFormula.modelCountOn (Finset.range 3) = 4 := by
  rw [← CNF.Sparsification.modelCountOn_countingNormalize noisyFormula (Finset.range 3)]
  decide

example :
    noisyFormula.modelCount =
      2 ^ (noisyFormula.numVars - (CNF.Sparsification.countingNormalize noisyFormula).numVars) *
        (CNF.Sparsification.countingNormalize noisyFormula).modelCount :=
  CNF.Sparsification.modelCount_countingNormalize noisyFormula

example :
    (CNF.Sparsification.normalize noisyFormula).vars.length ≤ noisyFormula.vars.length ∧
      (CNF.Sparsification.normalize noisyFormula).occurrences 1 ≤ noisyFormula.occurrences 1 :=
  ⟨CNF.Sparsification.vars_length_normalize_le noisyFormula,
   CNF.Sparsification.occurrences_normalize_le noisyFormula 1⟩

/-! ### Unit propagation cascade and conflict controls -/

private def cascadeSat : CNF ℕ :=
  [[(0, true)], [(0, false), (1, false)], [(1, true), (2, true)]]

example : cascadeSat.unitTrail = [(0, true), (1, false), (2, true)] := by
  decide

example : cascadeSat.unitPropagate = [] := by
  decide

example : cascadeSat.modelCountOn (Finset.range 3) = 1 := by
  rw [CNF.modelCountOn_unitPropagate_of_vars_subset cascadeSat (by decide)]
  decide

example : cascadeSat.unitPropagate.findUnit? = none :=
  CNF.findUnit?_unitPropagate cascadeSat

private def cascadeUnsat : CNF ℕ :=
  [[(0, true)], [(0, false), (1, true)], [(0, false), (1, false)]]

example : ¬cascadeUnsat.Satisfiable :=
  CNF.not_satisfiable_of_nil_mem_unitPropagate (by decide)

private def partialDrop : CNF ℕ :=
  [[(0, true)], [(0, true), (1, true)]]

example : partialDrop.modelCount = 2 := by
  rw [CNF.modelCount_unitPropagate partialDrop]
  decide

/-! ### DeclaredCNF round-trip and malformed-word rejection controls -/

private def goodDeclared : DeclaredCNF where
  numVars := 2
  formula := [[(0, true), (1, false)]]

private def outOfRangeDeclared : DeclaredCNF where
  numVars := 1
  formula := [[(1, true)]]

private theorem encDeclaredCNF_ne_malformed :
    ∀ x : DeclaredCNF, encDeclaredCNF x ≠ [true, false] := by
  rintro ⟨n, φ⟩ h
  rw [encDeclaredCNF_apply] at h
  change Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encUnary encCNF (n, φ) = [true, false] at h
  rw [Turing.MultiTapeTM.encPair_apply, Turing.MultiTapeTM.encUnary_apply] at h
  cases n with
  | zero =>
    have hc := congrArg List.head? h
    simp [Turing.MultiTapeTM.frame] at hc
  | succ k =>
    have htail := congrArg (List.getD · 1 true) h
    simp [Turing.MultiTapeTM.frame, List.replicate_succ] at htail

example : declaredCNFDecoder.decode (encDeclaredCNF goodDeclared) = goodDeclared :=
  declaredCNFDecoder_decode_enc goodDeclared

example : declaredCNFCode (encDeclaredCNF goodDeclared) = true := by
  rw [declaredCNFCode_encDeclaredCNF]
  decide

example : declaredCNFCode (encDeclaredCNF outOfRangeDeclared) = false := by
  rw [declaredCNFCode_encDeclaredCNF]
  decide

example : ¬∃ x : DeclaredCNF, x.WellFormed ∧ encDeclaredCNF x = [true, false] := by
  rintro ⟨x, _, hx⟩
  exact encDeclaredCNF_ne_malformed x hx

example : declaredCNFCode [true, false] = false := by
  rw [Bool.eq_false_iff, ne_eq, declaredCNFCode_eq_true_iff]
  rintro ⟨x, _, hx⟩
  exact encDeclaredCNF_ne_malformed x hx

example : (DeclaredCNF.ofStdSat stdFinFormula).modelCount = 2 := by
  rw [DeclaredCNF.modelCount_ofStdSat stdFinFormula, CNF.card_eval_ofStdSat_eq_modelCountOn]
  decide

/-! ### Strict `Equiv` transport controls (`equivStdSat`, `restrictModelsEquiv`, `modelsSplitEquiv`)
-/

example (c : Clause ℕ) : Clause.equivStdSat.symm (Clause.equivStdSat c) = c := by
  simp

example (φ : CNF ℕ) : CNF.equivStdSat.symm (CNF.equivStdSat φ) = φ := by
  simp

example
    (σ : {σ : ↥((Finset.range 3).erase 0) → Bool //
      (branchingFormula.restrict 0 true).eval
        (fun u => if h : u ∈ (Finset.range 3).erase 0 then σ ⟨u, h⟩ else false) = true}) :
    (CNF.restrictModelsEquiv branchingFormula (Finset.range 3) (by decide) true σ).1
        ⟨0, by decide⟩ = true ∧
      ((CNF.modelsSplitEquiv branchingFormula (Finset.range 3) (by decide)).symm
        ⟨(CNF.modelsSplitEquiv branchingFormula (Finset.range 3) (by decide) (Sum.inr σ)).1,
         (CNF.modelsSplitEquiv branchingFormula (Finset.range 3) (by decide)
           (Sum.inr σ)).2⟩) =
        Sum.inr σ := by
  refine ⟨by simp, ?_⟩
  have hzero :
      (CNF.modelsSplitEquiv branchingFormula (Finset.range 3) (by decide) (Sum.inr σ)).1
        ⟨0, by decide⟩ = true := by
    simp
  rw [CNF.modelsSplitEquiv_symm_of_eq_true _ _ _ _ hzero]
  congr 1
  ext ⟨u, hu⟩
  simp

example
    (σ : {σ : ↥((Finset.range 3).erase 0) → Bool //
      (branchingFormula.restrict 0 false).eval
        (fun u => if h : u ∈ (Finset.range 3).erase 0 then σ ⟨u, h⟩ else false) = true})
    (h1 : 1 ∈ Finset.range 3) :
    (CNF.restrictModelsEquiv branchingFormula (Finset.range 3) (by decide) false σ).1 ⟨1, h1⟩ =
      σ.1 ⟨1, by decide⟩ := by
  simp

end CslibFrontierTests.CNFBasics
