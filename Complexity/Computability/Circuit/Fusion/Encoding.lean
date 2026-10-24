/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Fusion.Quadratic
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite descriptions of semifilter covers

The quadratic compiler only needs inclusion flags, not the actual subsets in a pair cover.
A `t`-pair cover over `n` inputs has a description of `(2*t+1)*(n+t+1)` bits. Decode the
flags by synchronous propagation and the target is recovered. This gives an unconditional
count of the sets having a small cover, for any fixed supplied input family.

## Main definitions

* `Cslib.Circuits.Fusion.CoverCode`, `Cslib.Circuits.Fusion.CoverCode.read`,
  `Cslib.Circuits.Fusion.CoverCode.stages`, `Cslib.Circuits.Fusion.CoverCode.decode`: the
  finite inclusion-pattern description and its staged decoder.
* `Cslib.Circuits.Fusion.PairClosureCompiler.coordinate`,
  `Cslib.Circuits.Fusion.PairClosureCompiler.encode`: encode a pair list into a `CoverCode`.

## Main results

* `Cslib.Circuits.Fusion.PairCover.exists_code`: every cover admits a finite description.
* `Cslib.Circuits.Fusion.card_small_covers_le`: a bound on all targets of small cover complexity.

## References

* [B. P. Cavalar and I. C. Oliveira, *Boolean Circuit Complexity and Two-Dimensional Cover
  Problems*, Theorem 37][CavalarOliveira2025].
-/

@[expose] public section

namespace Cslib.Circuits.Fusion

universe u

/-- Each of the two operands per pair and the final output records a top flag, an input mask,
and a pair-value mask. No ambient subsets occur in this finite description. -/
abbrev CoverCode (n t : ℕ) := Fin (t + t + 1) → Bool × (Fin n → Bool) × (Fin t → Bool)

namespace CoverCode

variable {U : Type u} {n t : ℕ}

/-- Read one coordinate from its top/input/pair inclusion flags. -/
def read (code : CoverCode n t) (input : Fin n → Set U) (state : Fin t → Set U)
    (i : Fin (t + t + 1)) : Set U :=
  {x | (code i).1 = true ∨ (∃ j, (code i).2.1 j = true ∧ x ∈ input j) ∨
    ∃ j, (code i).2.2 j = true ∧ x ∈ state j}

/-- Propagate the described pair values from the empty initial state. -/
def stages (code : CoverCode n t) (input : Fin n → Set U) : ℕ → Fin t → Set U
  | 0 => ⊥
  | k + 1 => fun j =>
    code.read input (stages code input k) (Fin.castAdd t j).castSucc ∩
      code.read input (stages code input k) (Fin.natAdd t j).castSucc

/-- Decode a description using one propagation round per pair and a final free read. -/
def decode (code : CoverCode n t) (input : Fin n → Set U) : Set U :=
  code.read input (code.stages input t) (Fin.last (t + t))

/-- The description has exactly `(2*t+1)*(n+t+1)` independent bits. -/
private theorem card (n t : ℕ) :
    Fintype.card (CoverCode n t) = 2 ^ ((2 * t + 1) * (n + t + 1)) := by
  simp only [CoverCode, Fintype.card_fun, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_add, ← pow_succ', ← pow_mul]
  congr 1
  rw [two_mul, Nat.mul_comm]

end CoverCode

namespace PairClosureCompiler

variable {U : Type u} {n : ℕ}
variable (target : Set U) (input : Fin n → Set U)
  (pairs : List (Set ↥(targetᶜ) × Set ↥(targetᶜ)))

/-- The coordinates needed by the finite compiler: two operands per pair, then the empty set. -/
def coordinate : Fin (pairs.length + pairs.length + 1) → Set ↥(targetᶜ) :=
  Fin.lastCases ∅ (Fin.append (fun j => (pairs.get j).1) (fun j => (pairs.get j).2))

open scoped Classical in
/-- Record just the subset tests used in the quadratic compiler. -/
noncomputable def encode : CoverCode n pairs.length :=
  fun i => ⟨decide (coordinate target pairs i = Set.univ),
    (fun j => decide (Subtype.val ⁻¹' input j ⊆ coordinate target pairs i)),
    (fun j => decide ((pairs.get j).1 ∩ (pairs.get j).2 ⊆ coordinate target pairs i))⟩

/-- Encoded reads are the original compiler's reconstructed closure coordinates. -/
private theorem read_encode (state : Fin pairs.length → Set U)
    (i : Fin (pairs.length + pairs.length + 1)) :
    (encode target input pairs).read input state i =
      readState target input pairs state (coordinate target pairs i) := by
  classical
  ext x
  change (_ ∨ _ ∨ _) ↔ (_ ∨ _ ∨ _)
  simp only [encode, decide_eq_true_eq]

/-- Encoded propagation agrees with the original compiler at every stage. -/
private theorem stages_encode (k : ℕ) :
    (encode target input pairs).stages input k = stages target input pairs k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext j
    simp only [CoverCode.stages, ih, read_encode, coordinate, Fin.lastCases_castSucc,
      Fin.append_left, Fin.append_right, stages, step]

/-- Decode the original generated closure at its empty coordinate. -/
theorem decode_encode :
    (encode target input pairs).decode input = pairClosure target input pairs ∅ := by
  rw [CoverCode.decode, stages_encode, read_encode, coordinate, Fin.lastCases_last,
    readState_stages]

end PairClosureCompiler

variable {U : Type u} {n : ℕ} {target : Set U} {input : Fin n → Set U}

/-- Every cover has a finite description recovering its target. -/
theorem PairCover.exists_code (c : PairCover target input) :
    ∃ code : CoverCode n c.pairs.length, code.decode input = target :=
  ⟨PairClosureCompiler.encode target input c.pairs,
    (PairClosureCompiler.decode_encode target input c.pairs).trans c.pairClosure_empty⟩

/-- A cover fitting a budget has a description of the budget's fixed length. -/
theorem PairCover.exists_code_of_length_le (c : PairCover target input) {t : ℕ}
    (h : c.pairs.length ≤ t) : ∃ code : CoverCode n t, code.decode input = target := by
  have hcode := (c.pad t).exists_code
  rw [c.length_pad h] at hcode
  exact hcode

/-- The number of targets with a cover of at most `t` pairs is at most the number of
inclusion-pattern descriptions; no hypothesis about the existence of such descriptions remains. -/
theorem card_small_covers_le [Fintype U] (input : Fin n → Set U) (t : ℕ) :
    (Finset.univ.filter (fun target : Set U => pairCoverComplexity target input ≤ t)).card ≤
      2 ^ ((2 * t + 1) * (n + t + 1)) := by
  classical
  have hsub : Finset.univ.filter (fun target : Set U => pairCoverComplexity target input ≤ t) ⊆
      Finset.univ.image (fun code : CoverCode n t => code.decode input) := by
    intro target ht
    obtain ⟨c, hc⟩ := pairCoverComplexity_le_iff.mp (Finset.mem_filter.mp ht).2
    obtain ⟨code, hcode⟩ := c.exists_code_of_length_le hc
    exact Finset.mem_image.mpr ⟨code, Finset.mem_univ _, hcode⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by
    rw [Finset.card_univ, CoverCode.card]))

end Cslib.Circuits.Fusion
