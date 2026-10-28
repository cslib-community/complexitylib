/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.Reduction.LogSpaceTruthTable
public import Complexity.Computability.Complexity.Reduction.OneOne
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Concrete examples of logspace one-one and truth-table reductions

Non-vacuity checks and concrete instances for `LogSpaceOneOneReducible`,
`LogSpaceTruthTableReducible`, `LogSpaceKTruthTableReducible`, `LogSpaceBTTReducible`,
`LogSpaceDTTReducible`, `LogSpaceCTTReducible`, and `LogSpacePTTReducible`.
-/

public section

namespace Cslib.Complexity.LogSpaceReductionsTest

open Turing.MultiTapeTM

/-! ### Logspace one-one reduction: prepending `true` -/

/-- Prepending `true` is a logspace one-one reduction from words of even length to words of odd
length. -/
example :
    LogSpaceOneOneReducible encBits encBits
      {xs : List Bool | xs.length % 2 = 0}
      {ys : List Bool | ys.length % 2 = 1} := by
  refine ⟨fun xs => true :: xs,
    ⟨ComputableInLogSpace.of_cons_true fun _ => rfl, fun _ _ h => (List.cons.inj h).2⟩,
    fun xs => ?_⟩
  simp only [Set.mem_ofPred_eq, List.length_cons]
  omega

/-! ### Two-query query generator for pairs in logarithmic space -/

private def pairQuery (p : (List Bool × List Bool) × ℕ) : List Bool :=
  if decide (p.2 ≤ 0) then p.1.1 else p.1.2

private theorem computableInLogSpace_pairQuery :
    ComputableInLogSpace pairQuery (encPair (encPair encBits encBits) encUnary) encBits :=
  ComputableInLogSpace.ite
    (ComputableInLogSpace.unaryLeConst 0 (ComputableInLogSpace.snd _ _))
    ((ComputableInLogSpace.fst _ _).comp (ComputableInLogSpace.fst _ _))
    ((ComputableInLogSpace.snd _ _).comp (ComputableInLogSpace.fst _ _))

/-! ### Disjunctive and conjunctive two-query reductions in logarithmic space -/

/-- A pair lies in `pairOr B` when at least one component lies in `B`. -/
def pairOr (B : Set (List Bool)) : Set (List Bool × List Bool) :=
  {p | p.1 ∈ B ∨ p.2 ∈ B}

/-- `pairOr B` disjunctive-truth-table reduces to `B` in logarithmic space with two queries. -/
theorem pairOr_logSpaceDTTReducible (B : Set (List Bool)) :
    LogSpaceDTTReducible (encPair encBits encBits) encBits (pairOr B) B := by
  refine ⟨fun _ => 2, pairQuery, ComputableInLogSpace.const 2, computableInLogSpace_pairQuery,
    fun p => ?_⟩
  simp only [pairOr, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h)
    · exact ⟨0, by omega, by simpa [pairQuery] using h⟩
    · exact ⟨1, by omega, by simpa [pairQuery] using h⟩
  · rintro ⟨i, hi, hq⟩
    rcases i with _ | _
    · exact Or.inl (by simpa [pairQuery] using hq)
    · exact Or.inr (by simpa [pairQuery] using hq)

/-- `pairOr B` positive-truth-table reduces to `B` in logarithmic space. -/
example (B : Set (List Bool)) :
    LogSpacePTTReducible (encPair encBits encBits) encBits (pairOr B) B :=
  (pairOr_logSpaceDTTReducible B).logSpacePTTReducible

/-- A pair lies in `pairAnd B` when both components lie in `B`. -/
def pairAnd (B : Set (List Bool)) : Set (List Bool × List Bool) :=
  {p | p.1 ∈ B ∧ p.2 ∈ B}

/-- `pairAnd B` conjunctive-truth-table reduces to `B` in logarithmic space with two queries. -/
theorem pairAnd_logSpaceCTTReducible (B : Set (List Bool)) :
    LogSpaceCTTReducible (encPair encBits encBits) encBits (pairAnd B) B := by
  refine ⟨fun _ => 2, pairQuery, ComputableInLogSpace.const 2, computableInLogSpace_pairQuery,
    fun p => ?_⟩
  simp only [pairAnd, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, h2⟩ i hi
    rcases i with _ | _
    · simpa [pairQuery] using h1
    · simpa [pairQuery] using h2
  · intro h
    exact ⟨by simpa [pairQuery] using h 0 (by omega),
      by simpa [pairQuery] using h 1 (by omega)⟩

/-! ### Non-monotone two-query `2-tt` reduction in logarithmic space (XOR) and composition -/

open Classical in
/-- A pair lies in `pairXor B` when exactly one of its components lies in `B`. -/
def pairXor (B : Set (List Bool)) : Set (List Bool × List Bool) :=
  {p | decide (p.1 ∈ B) ≠ decide (p.2 ∈ B)}

/-- `pairXor B` `2`-truth-table reduces to `B` in logarithmic space, with XOR evaluation. -/
theorem pairXor_logSpaceKTruthTableReducible (B : Set (List Bool)) :
    LogSpaceKTruthTableReducible 2 (encPair encBits encBits) encBits (pairXor B) B := by
  classical
  refine ⟨fun _ => 2, pairQuery, fun p => p.2.foldl xor false,
    ComputableInLogSpace.const 2, computableInLogSpace_pairQuery,
    (ComputableInLogSpace.bitsFoldl xor false).comp (ComputableInLogSpace.snd _ _),
    fun _ => le_rfl, fun p => ?_⟩
  rw [truthTableAnswers_eq_map_range]
  simp only [pairXor, Set.mem_ofPred_eq, Set.mem_preimage, List.range_succ, List.range_zero,
    List.nil_append, List.singleton_append, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, Bool.false_xor, pairQuery, le_refl, decide_true, ↓reduceIte,
    Nat.not_le_of_gt (by decide : 0 < 1), decide_false, Bool.false_eq_true]
  cases decide (p.1 ∈ B) <;> cases decide (p.2 ∈ B) <;> decide

open Classical in
/-- Composing two `2`-query logspace truth-table reductions yields a `4`-query logspace truth-table
reduction. -/
example (B : Set (List Bool)) :
    LogSpaceKTruthTableReducible 4
      (encPair (encPair encBits encBits) (encPair encBits encBits)) encBits
      {q : (List Bool × List Bool) × (List Bool × List Bool) |
        decide (q.1 ∈ pairXor B) ≠ decide (q.2 ∈ pairXor B)} B := by
  classical
  have h1 :
      LogSpaceKTruthTableReducible 2
        (encPair (encPair encBits encBits) (encPair encBits encBits))
        (encPair encBits encBits)
        {q : (List Bool × List Bool) × (List Bool × List Bool) |
          decide (q.1 ∈ pairXor B) ≠ decide (q.2 ∈ pairXor B)}
        (pairXor B) := by
    refine ⟨fun _ => 2,
      fun p => if decide (p.2 ≤ 0) then p.1.1 else p.1.2,
      fun p => p.2.foldl xor false,
      ComputableInLogSpace.const 2,
      ComputableInLogSpace.ite
        (ComputableInLogSpace.unaryLeConst 0 (ComputableInLogSpace.snd _ _))
        ((ComputableInLogSpace.fst _ _).comp (ComputableInLogSpace.fst _ _))
        ((ComputableInLogSpace.snd _ _).comp (ComputableInLogSpace.fst _ _)),
      (ComputableInLogSpace.bitsFoldl xor false).comp (ComputableInLogSpace.snd _ _),
      fun _ => le_rfl,
      fun q => ?_⟩
    rw [truthTableAnswers_eq_map_range]
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, List.range_succ, List.range_zero,
      List.nil_append, List.singleton_append, List.map_cons, List.map_nil, List.foldl_cons,
      List.foldl_nil, Bool.false_xor, le_refl, decide_true, ↓reduceIte,
      Nat.not_le_of_gt (by decide : 0 < 1), decide_false, Bool.false_eq_true]
    cases decide (q.1 ∈ pairXor B) <;> cases decide (q.2 ∈ pairXor B) <;> decide
  exact h1.trans (pairXor_logSpaceKTruthTableReducible B)

/-- `L`-closure: since `{xs : List Bool | xs.isEmpty = true} ∈ L encBits`, `pairXor` of it lies in
`L (encPair encBits encBits)`. -/
example :
    pairXor {xs : List Bool | xs.isEmpty = true} ∈ L (encPair encBits encBits) := by
  have hEmpty : {xs : List Bool | xs.isEmpty = true} ∈ L encBits :=
    ⟨List.isEmpty, ComputableInLogSpace.of_isEmpty fun _ => rfl, fun _ => Iff.rfl⟩
  exact (pairXor_logSpaceKTruthTableReducible _).mem_L hEmpty

end Cslib.Complexity.LogSpaceReductionsTest
