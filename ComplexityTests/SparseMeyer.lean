/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Computability.Complexity.Classes.Sparse.Meyer

/-!
# `P/poly = P^SPARSE = P^TALLY`

The tally language of a concrete advice function on members, non-members and bits past the end of
the advice; a nonvacuous instance of `P/poly ⊆ P^TALLY` for a language that may be undecidable; and
trading a sparse oracle for a tally one through `P/poly`.
-/

namespace ComplexityTests.SparseMeyer

open Cslib Cslib.Complexity Cslib.Circuits.Boolean Turing.MultiTapeTM

/-- The advice `[true, false, true]` at every length. -/
private def adv : ℕ → List Bool := fun _ => [true, false, true]

-- Bits `0` and `2` of the advice are members of its tally language; bit `1` and bits past the end
-- of the advice are not.
example : encUnary (Nat.pair 5 0) ∈ adviceTally adv ∧ encUnary (Nat.pair 5 1) ∉ adviceTally adv ∧
    encUnary (Nat.pair 5 2) ∈ adviceTally adv ∧ encUnary (Nat.pair 5 3) ∉ adviceTally adv := by
  simp only [encUnary_pair_mem_adviceTally, adv]
  decide

-- The tally language contains no word with a `false` letter.
example : [true, false] ∉ adviceTally adv := fun h => by
  simpa using adviceTally_mem_TALLY adv _ h false (by simp)

/-- The words whose length lies in `K`. -/
private def lengthIn (K : Set ℕ) : Language Bool := {w | w.length ∈ K}

open Classical in
/-- For every set `K` of lengths, decidable or not, the words whose length lies in `K` have circuits
of polynomial size: each slice is constant. -/
private theorem lengthIn_mem_PPoly (K : Set ℕ) : lengthIn K ∈ PPoly :=
  PPoly.of_slice_const (fun n => decide (n ∈ K)) fun n x => by
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, decide_eq_true_iff]
    change (List.ofFn x).length ∈ K ↔ n ∈ K
    rw [List.length_ofFn]

-- Nonvacuity: for every set `K` of lengths, decidable or not, the words whose length lies in `K`
-- have circuits of polynomial size (each slice is constant), so they are decided in polynomial
-- time relative to a tally oracle language.
example (K : Set ℕ) : ∃ T ∈ TALLY, {w : List Bool | w.length ∈ K} ∈ PWithOracle T encBits :=
  exists_mem_TALLY_mem_PWithOracle_of_mem_PPolyOn
    (mem_PPolyOn_encBits_iff.mpr (lengthIn_mem_PPoly K))

-- The same language has a polynomial-time truth-table reduction to a tally language.
example (K : Set ℕ) :
    ∃ T ∈ TALLY, PolyTimeTruthTableReducible encBits encBits {w : List Bool | w.length ∈ K} T :=
  mem_PPolyOn_iff_exists_mem_TALLY_polyTimeTruthTableReducible.mp
    (mem_PPolyOn_encBits_iff.mpr (lengthIn_mem_PPoly K))

-- A sparse oracle can be traded for a tally oracle, through `P/poly`.
example {S A : Set (List Bool)} (hS : S ∈ SPARSE encBits) (hA : A ∈ PWithOracle S encBits) :
    ∃ T ∈ TALLY, A ∈ PWithOracle T encBits :=
  mem_PPolyOn_iff_exists_mem_TALLY_mem_PWithOracle.mp
    (mem_PPolyOn_iff_exists_mem_SPARSE_mem_PWithOracle.mpr ⟨S, hS, hA⟩)

-- The two class equalities agree: `P^SPARSE = P^TALLY` for every instance encoding.
example {α : Type} (enc : α ↪ List Bool) :
    ⋃ S ∈ SPARSE encBits, PWithOracle S enc = ⋃ T ∈ TALLY, PWithOracle T enc := by
  rw [← PPolyOn_eq_iUnion_PWithOracle_SPARSE, PPolyOn_eq_iUnion_PWithOracle_TALLY]

end ComplexityTests.SparseMeyer
