/-
Copyright (c) 2026 Erik Demaine, Stefan Langerman, GPT 5.6. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Complexity.Logics.Propositional.CNF.ThreeOccurrence
import Complexity.Logics.Propositional.CNF.ModelCount.Relabel
import Complexity.Logics.Propositional.CNF.ThreeOccurrence.PolyTime
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Logics.Propositional.CNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# 3SAT with at most three occurrences per variable

`ThreeSATThree` uses clauses of width at most three, allowing binary clauses. Every variable has
at most three literal occurrences, including repeated literals within a clause
[Papadimitriou, Proposition 9.3][Papadimitriou94]. Only the variable-occurrence restriction of
that proposition is formalized; its additional bound of two occurrences per signed literal is
not part of `ThreeSATThree` or the completeness theorem. The reduction
splits occurrences and connects the copies by binary implication cycles. It is total on all CNF
inputs: a formula having a clause longer than three maps to the unsatisfiable formula `[[]]`.
Original natural labels stay binary throughout; only syntactic positions use unary counters.

The construction is adapted from `lean-trominoes` revision
`6d5b36c15cec6cb18d30137b7f1c7fb92ea24332`,
[PeriodicThreeSATThree.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThree.lean),
[PeriodicThreeSATThreeCorrectness.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreeCorrectness.lean), and
[PeriodicThreeSATThreeExactSize.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreeExactSize.lean).
This endpoint imposes no planarity condition.

## Main definitions

* `Cslib.Complexity.ThreeSATThree`: satisfiable width-three, occurrence-three CNF formulas.
* `Cslib.Complexity.toThreeSATThree`: the total reduction from `ThreeSAT`.

## Main results

* `Cslib.Complexity.mem_ThreeSATThree_toThreeSATThree_iff`: correctness of the reduction.
* `Cslib.Complexity.modelCount_toThreeSATThree`: preservation of counts for width-three inputs.
* `Cslib.Complexity.computableInPolyTime_toThreeSATThree`: native polynomial time under `encCNF`.
* `Cslib.Complexity.ThreeSATThree_npComplete`: 3SAT-3 is NP-complete.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Proposition 9.3][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Satisfiable CNF formulas of width at most three, with at most three literal occurrences per
variable. Repetitions count, and binary clauses are permitted. -/
def ThreeSATThree : Set (CNF ℕ) :=
  {φ | (∀ c ∈ φ, c.length ≤ 3) ∧ (∀ v, φ.vars.count v ≤ 3) ∧ φ.Satisfiable}

namespace ThreeSATThree

/-- Injectively encode an original binary label and its two occurrence indices. -/
def numberCopy (x : ℕ × ℕ × ℕ) : ℕ := Nat.pair x.1 (Nat.pair x.2.1 x.2.2)

/-- Numbering copies is injective, independently of whether they occur in a formula. -/
theorem numberCopy_injective : Function.Injective numberCopy := by
  rintro ⟨a, b, c⟩ ⟨d, e, f⟩ h
  simp only [numberCopy, Nat.pair_eq_pair] at h
  rcases h with ⟨rfl, rfl, rfl⟩
  rfl

private theorem computableInPolyTime_pair :
    ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encNat encNat) encNat := by
  unfold Nat.pair
  fun_prop

/-- Numbering copies is polynomial-time without expanding the original binary label. -/
@[fun_prop]
theorem computableInPolyTime_numberCopy :
    ComputableInPolyTime numberCopy (encPair encNat (encPair encUnary encUnary)) encNat := by
  have hi : ComputableInPolyTime (fun p : ℕ × ℕ => Nat.pair p.1 p.2)
      (encPair encUnary encUnary) encNat :=
    computableInPolyTime_pair.comp
      ((ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _)))
  exact computableInPolyTime_pair.comp
    ((ComputableInPolyTime.fst _ _).prod (hi.comp (ComputableInPolyTime.snd _ _)))

/-- Check clause widths, literal-occurrence bounds, and a satisfying assignment. -/
def verifier (x : CNF ℕ × List Bool) : Bool :=
  (x.1.all fun c => decide (c.length ≤ 3)) &&
    (x.1.vars.all fun v => decide (x.1.vars.count v ≤ 3)) && SAT.verifier x

/-- The occurrence restriction is a polynomial-time guard on the usual SAT verifier. -/
theorem isVerifier : IsVerifier encCNF Polynomial.X verifier ThreeSATThree := by
  have he : ThreeSATThree = {φ | ((φ.all fun c => decide (c.length ≤ 3)) &&
      (φ.vars.all fun v => decide (φ.vars.count v ≤ 3))) = true ∧ φ ∈ SAT} := by
    ext φ
    simp only [ThreeSATThree, Set.mem_ofPred_eq, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq, mem_SAT]
    constructor
    · rintro ⟨hw, ho, hs⟩
      exact ⟨⟨hw, fun v _ => ho v⟩, hs⟩
    · rintro ⟨⟨hw, ho⟩, hs⟩
      refine ⟨hw, fun v => ?_, hs⟩
      by_cases hv : v ∈ φ.vars
      · exact ho v hv
      · simp [List.count_eq_zero.2 hv]
  rw [he]
  exact SAT.isVerifier.guard

/-- The width/occurrence tests and SAT evaluation run in native polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encCNF encBits) encBool := by
  unfold verifier
  simp only [List.count_eq_countP]
  fun_prop

/-- 3SAT-3 belongs to NP under the ordinary binary CNF encoding. -/
theorem mem_NP : ThreeSATThree ∈ NP encCNF :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end ThreeSATThree

/-- Reject non-width-three inputs, and otherwise split occurrences and number the copies. -/
def toThreeSATThree (φ : CNF ℕ) : CNF ℕ :=
  if φ.all (fun c => decide (c.length ≤ 3)) then
    φ.toThreeOccurrence.relabel ThreeSATThree.numberCopy
  else [[]]

/-- For a width-three input, numbering preserves the splitter's exact clause count. -/
theorem length_toThreeSATThree (φ : CNF ℕ) (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (toThreeSATThree φ).length = φ.length + φ.vars.length := by
  have hg : φ.all (fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
  simp [toThreeSATThree, hg, CNF.relabel, CNF.length_toThreeOccurrence]

/-- For a width-three input, numbering preserves the exact literal-occurrence count. -/
theorem length_vars_toThreeSATThree (φ : CNF ℕ) (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (toThreeSATThree φ).vars.length = 3 * φ.vars.length := by
  have hg : φ.all (fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
  simp [toThreeSATThree, hg, CNF.vars_relabel, CNF.length_vars_toThreeOccurrence]

/-- For a width-three input, occurrence splitting and injective numbering preserve the number of
satisfying assignments on occurring variables. -/
theorem modelCount_toThreeSATThree (φ : CNF ℕ) (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    (toThreeSATThree φ).modelCount = φ.modelCount := by
  have hg : φ.all (fun c => decide (c.length ≤ 3)) = true := by simpa using hφ
  simp only [toThreeSATThree, hg, ↓reduceIte]
  rw [CNF.modelCount_relabel ThreeSATThree.numberCopy_injective, CNF.modelCount_toThreeOccurrence]

/-- The total splitter is polynomial-time under binary `encCNF`. -/
@[fun_prop]
theorem computableInPolyTime_toThreeSATThree :
    ComputableInPolyTime toThreeSATThree encCNF encCNF := by
  have hr := CNF.computableInPolyTime_relabel ThreeSATThree.computableInPolyTime_numberCopy
  have hs := CNF.computableInPolyTime_toThreeOccurrence encNat
  have hc := hr.comp hs
  unfold toThreeSATThree
  fun_prop

/-- Correctness holds for all CNF inputs, including those outside the width-three restriction. -/
theorem mem_ThreeSATThree_toThreeSATThree_iff (φ : CNF ℕ) :
    toThreeSATThree φ ∈ ThreeSATThree ↔ φ ∈ ThreeSAT := by
  unfold toThreeSATThree
  split_ifs with hw
  · have hw' : ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
    have hs :=
      (CNF.satisfiable_relabel ThreeSATThree.numberCopy_injective φ.toThreeOccurrence).trans
        (CNF.satisfiable_toThreeOccurrence φ)
    change _ ∧ _ ∧ _ ↔ _ ∧ _
    refine ⟨fun h => ⟨hw', hs.1 h.2.2⟩, fun h => ⟨?_, ?_, hs.2 h.2⟩⟩
    · intro c hc
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
      simpa using CNF.width_toThreeOccurrence (by decide : 2 ≤ 3) hw' d hd
    · intro v
      rw [CNF.vars_relabel]
      by_cases hv : v ∈ φ.toThreeOccurrence.vars.map ThreeSATThree.numberCopy
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hv
        rw [List.count_map_of_injective _ _ ThreeSATThree.numberCopy_injective]
        exact CNF.count_vars_toThreeOccurrence_le φ x
      · simp [List.count_eq_zero.2 hv]
  · have hw' : ¬ ∀ c ∈ φ, c.length ≤ 3 := by simpa using hw
    simp [ThreeSATThree, ThreeSAT, hw', CNF.Satisfiable]

/-- `ThreeSAT` reduces to 3SAT-3. -/
theorem polyTimeReducible_ThreeSAT_ThreeSATThree :
    PolyTimeReducible encCNF encCNF ThreeSAT ThreeSATThree :=
  ⟨toThreeSATThree, computableInPolyTime_toThreeSATThree,
    fun φ => (mem_ThreeSATThree_toThreeSATThree_iff φ).symm⟩

/-- 3SAT-3 is NP-hard. -/
theorem ThreeSATThree_npHard : NPHard encCNF ThreeSATThree :=
  ThreeSAT_npHard.trans polyTimeReducible_ThreeSAT_ThreeSATThree

/-- 3SAT with at most three occurrences per variable is NP-complete
[Papadimitriou, Proposition 9.3][Papadimitriou94]. The additional per-signed-literal bound in that
proposition is not part of this statement. -/
theorem ThreeSATThree_npComplete : NPComplete encCNF ThreeSATThree :=
  ⟨ThreeSATThree.mem_NP, ThreeSATThree_npHard⟩

end Cslib.Complexity
