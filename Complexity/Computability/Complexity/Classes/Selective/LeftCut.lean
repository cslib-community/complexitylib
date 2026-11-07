/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Selective
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Set.Countable
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Lex
import Complexity.Foundations.Data.List.Lex

/-!
# Left cuts: uncountably many P-selective sets

The *left cut* of an infinite binary sequence `r` (`Cslib.Complexity.leftCut`) is the set of bit
strings `x` that are lexicographically at most the prefix of `r` of the same length; read as binary
fractions, `0.x ≤ 0.r₀r₁r₂…`. Left cuts are the standard examples of P-selective sets [Selman1979];
see also [Hemaspaandra and Torenvliet, *Introduction to Semi-Feasible
Computation*][HemaspaandraTorenvliet2003]. A left cut is a
lower set of the lexicographic order (`Cslib.Complexity.isLowerSet_leftCut`), which is compared in
polynomial time, so the lexicographic minimum is a polynomial-time selector, for every sequence
`r`, however hard `r` is to compute (`Cslib.Complexity.leftCut_mem_PSel`).

Different sequences have different left cuts (`Cslib.Complexity.leftCut_injective`), so there are
uncountably many P-selective sets (`Cslib.Complexity.not_countable_PSel`). In contrast, only
countably many sets are decidable by machines, so P-selective sets need not be decidable; that
count of machines is not formalized here.

## Main definitions

* `Cslib.Complexity.leftCut`: the left cut of an infinite binary sequence.

## Main results

* `Cslib.Complexity.mem_leftCut_iff_exists`: `x` is in the left cut of `r` exactly when it is
  lexicographically at most some prefix of `r`.
* `Cslib.Complexity.isLowerSet_leftCut`: left cuts are lexicographic lower sets.
* `Cslib.Complexity.leftCut_mem_PSel`: every left cut is P-selective.
* `Cslib.Complexity.leftCut_injective`: the left cut determines the sequence.
* `Cslib.Complexity.not_countable_PSel`: there are uncountably many P-selective sets.

## References

* [A. L. Selman, *P-selective sets, tally languages, and the behavior of polynomial time
  reducibilities on NP*][Selman1979]
* [L. A. Hemaspaandra and L. Torenvliet, *Theory of Semi-Feasible Algorithms*, chapter
  *Introduction to Semi-Feasible Computation*][HemaspaandraTorenvliet2003]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The *left cut* of an infinite binary sequence `r`: the bit strings that are lexicographically
at most the prefix of `r` of the same length. -/
def leftCut (r : ℕ → Bool) : Set (List Bool) :=
  {x | x ≤ (List.range x.length).map r}

variable {r : ℕ → Bool} {x : List Bool}

theorem mem_leftCut : x ∈ leftCut r ↔ x ≤ (List.range x.length).map r := Iff.rfl

/-- Shorter prefixes of a sequence are prefixes of longer ones. -/
private theorem map_range_prefix (r : ℕ → Bool) {m n : ℕ} (h : m ≤ n) :
    (List.range m).map r <+: (List.range n).map r := by
  rw [List.prefix_iff_eq_take, List.length_map, List.length_range, ← List.map_take,
    List.take_range, Nat.min_eq_left h]

/-- A bit string is in the left cut of `r` exactly when it is lexicographically at most some
prefix of `r`. -/
theorem mem_leftCut_iff_exists : x ∈ leftCut r ↔ ∃ n, x ≤ (List.range n).map r := by
  refine ⟨fun h => ⟨_, h⟩, fun ⟨n, h⟩ => ?_⟩
  rw [mem_leftCut]
  rcases le_total n x.length with hn | hn
  · exact h.trans (List.isPrefix_le (map_range_prefix r hn))
  · by_contra hlt
    rw [not_le] at hlt
    have hlen : ((List.range x.length).map r).length = x.length := by simp
    have h' := List.append_lt_append_of_lt_of_length_eq hlt hlen
      (((List.range n).map r).drop x.length) []
    have htake : (List.range x.length).map r = ((List.range n).map r).take x.length :=
      List.prefix_iff_eq_take.1 (map_range_prefix r hn) |>.trans (by rw [hlen])
    rw [htake, List.take_append_drop, List.append_nil] at h'
    exact absurd h (not_le.2 h')

/-- Every prefix of `r` is in the left cut of `r`. -/
theorem map_range_mem_leftCut (r : ℕ → Bool) (n : ℕ) : (List.range n).map r ∈ leftCut r :=
  mem_leftCut_iff_exists.2 ⟨n, le_rfl⟩

/-- Left cuts are lower sets of the lexicographic order. -/
theorem isLowerSet_leftCut (r : ℕ → Bool) : IsLowerSet (leftCut r) := fun _ _ hba ha =>
  mem_leftCut_iff_exists.2 ⟨_, hba.trans ha⟩

/-- **Left cuts are P-selective**, for every sequence `r`: the lexicographic minimum of two bit
strings is a polynomial-time selector [Selman1979]. -/
theorem leftCut_mem_PSel (r : ℕ → Bool) : leftCut r ∈ PSel encBits :=
  mem_PSel_of_isLowerSet (isLowerSet_leftCut r) ComputableInPolyTime.bits_lex_le

/-- **The left cut determines the sequence**: two sequences with the same left cut have the same
prefixes. -/
theorem leftCut_injective : Function.Injective leftCut := by
  intro r r' h
  have hpre (n : ℕ) : (List.range n).map r = (List.range n).map r' := by
    have h₁ : (List.range n).map r ∈ leftCut r' := h ▸ map_range_mem_leftCut r n
    have h₂ : (List.range n).map r' ∈ leftCut r := h ▸ map_range_mem_leftCut r' n
    rw [mem_leftCut, List.length_map, List.length_range] at h₁ h₂
    exact le_antisymm h₁ h₂
  funext i
  simpa using congrArg (·[i]?) (hpre (i + 1))

/-- **There are uncountably many P-selective sets**: the left cuts of the uncountably many infinite
binary sequences are distinct and P-selective. -/
theorem not_countable_PSel : ¬(PSel encBits).Countable := by
  classical
  intro h
  have := h.to_subtype
  have hcut : Function.Injective
      fun r : ℕ → Bool => (⟨leftCut r, leftCut_mem_PSel r⟩ : PSel encBits) :=
    fun r r' hr => leftCut_injective (congrArg Subtype.val hr)
  have := hcut.countable
  have hset : Function.Injective fun (s : Set ℕ) (n : ℕ) => decide (n ∈ s) := fun s t hst => by
    ext n
    simpa using congrFun hst n
  have := hset.countable
  obtain ⟨f, hf⟩ := exists_injective_nat (Set ℕ)
  exact Function.cantor_injective f hf

end Cslib.Complexity
