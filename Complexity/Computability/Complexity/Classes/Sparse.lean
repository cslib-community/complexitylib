/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List
public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Data.Set.Card
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# Sparse problems

A problem is *sparse* when it has only polynomially many members of each size. With instances
encoded as binary words, `S ∈ SPARSE enc` when, for a polynomially bounded `p`, at most `p n`
members of `S` have encodings of length at most `n`. This is the census form of the definition
[Fluet, Hemaspaandra and Homan, Assignment page 5][FluetHemaspaandraHoman2026]. Counting
encodings of length exactly `n` gives the same class, the form taken by
`Cslib.Circuits.Boolean.PPoly.of_sparse`, which `Cslib.Circuits.Boolean.PPoly.of_mem_SPARSE`
connects to this definition. The count is an extended natural number (`Set.encard`), so that an
infinite set of members is not counted as `0`; since an encoding is injective, every such set is
finite.

Sparse problems cannot be hard for `coNP` (Fortune) or for `NP` (Mahaney), even under one-query
truth-table reductions, unless `P = NP`; see
`Complexity/Computability/Complexity/Classes/Sparse/Fortune.lean`,
`Complexity/Computability/Complexity/Classes/Sparse/Mahaney.lean` and
`Complexity/Computability/Complexity/Classes/Sparse/OneQuery.lean`.

## Main definitions

* `Cslib.Complexity.SPARSE`: the sparse problems.

## Main results

* `Cslib.Complexity.exists_card_le_of_mem_SPARSE`: a polynomial bound on every finite set of
  members of bounded encoded length.
* `Cslib.Complexity.mem_SPARSE_of_subset`: subsets of sparse problems are sparse.
* `Cslib.Complexity.image_mem_SPARSE_encBits_iff`: a problem is sparse exactly when the language
  of encodings of its members is.
* `Set.Finite.mem_SPARSE`: finite problems are sparse.
* `Cslib.Complexity.mem_SPARSE_of_unary`: languages of words consisting only of `true`s are
  sparse.
* `Cslib.Complexity.univ_notMem_SPARSE`: the language of all words is not sparse.

## References

* [K. Fluet, L. A. Hemaspaandra, C. M. Homan, *Fortune's Bounty: Taming Complexity by Trimming
  Trees*][FluetHemaspaandraHoman2026]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*}

/-- The sparse problems with respect to the encoding `enc`: `S ∈ SPARSE enc` when, for some
polynomially bounded `p`, at most `p n` members of `S` have encodings of length at most `n`
[Fluet, Hemaspaandra and Homan, Assignment page 5][FluetHemaspaandraHoman2026]. -/
def SPARSE (enc : α ↪ List Bool) : Set (Set α) :=
  {S | ∃ p : ℕ → ℕ, PolynomiallyBounded p ∧ ∀ n, {a ∈ S | (enc a).length ≤ n}.encard ≤ p n}

theorem mem_SPARSE {enc : α ↪ List Bool} {S : Set α} :
    S ∈ SPARSE enc ↔
      ∃ p : ℕ → ℕ, PolynomiallyBounded p ∧ ∀ n, {a ∈ S | (enc a).length ≤ n}.encard ≤ p n :=
  Iff.rfl

section

variable {enc : α ↪ List Bool} {S T : Set α}

/-- A sparse problem has at most `c (n + 1) ^ d` members of encoded length at most `n`, in every
finite set of them. -/
theorem exists_card_le_of_mem_SPARSE (h : S ∈ SPARSE enc) :
    ∃ c d : ℕ, ∀ n (s : Finset α), (∀ a ∈ s, a ∈ S ∧ (enc a).length ≤ n) →
      s.card ≤ c * (n + 1) ^ d := by
  obtain ⟨p, hp, hS⟩ := h
  obtain ⟨c, d, hpcd⟩ := polynomiallyBounded_iff_le.mp hp
  refine ⟨c, d, fun n s hs => ?_⟩
  have hsub : (s : Set α) ⊆ {a ∈ S | (enc a).length ≤ n} := fun a ha => hs a ha
  have hcard : (s.card : ℕ∞) ≤ p n := by
    rw [← Set.encard_coe_eq_coe_finsetCard]
    exact (Set.encard_le_encard hsub).trans (hS n)
  exact (Nat.cast_le.mp hcard).trans (hpcd n)

/-- Subsets of sparse problems are sparse. -/
theorem mem_SPARSE_of_subset (hTS : T ⊆ S) (h : S ∈ SPARSE enc) : T ∈ SPARSE enc := by
  obtain ⟨p, hp, hS⟩ := h
  refine ⟨p, hp, fun n => le_trans (Set.encard_le_encard ?_) (hS n)⟩
  exact fun a ha => ⟨hTS ha.1, ha.2⟩

end

/-- A problem is sparse exactly when the language of the encodings of its members is. -/
theorem image_mem_SPARSE_encBits_iff {enc : α ↪ List Bool} {S : Set α} :
    enc '' S ∈ SPARSE encBits ↔ S ∈ SPARSE enc := by
  have himage (n : ℕ) :
      {w ∈ enc '' S | (encBits w).length ≤ n} = enc '' {a ∈ S | (enc a).length ≤ n} := by
    ext w
    simp only [encBits_apply, Set.mem_sep_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, hn⟩
      exact ⟨a, ⟨ha, hn⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hn⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, hn⟩
  simp only [mem_SPARSE, himage, enc.injective.encard_image]

/-- Finite problems are sparse. -/
theorem _root_.Set.Finite.mem_SPARSE {enc : α ↪ List Bool} {S : Set α} (h : S.Finite) :
    S ∈ SPARSE enc := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, S.encard = k := ⟨S.ncard, h.cast_ncard_eq.symm⟩
  refine ⟨fun _ => k, .const k, fun n => le_trans (Set.encard_le_encard ?_) hk.le⟩
  exact fun a ha => ha.1

/-- **Unary languages are sparse:** a language of words consisting only of `true`s has at most
`n + 1` words of length at most `n`. -/
theorem mem_SPARSE_of_unary {L : Set (List Bool)} (hL : ∀ w ∈ L, ∀ b ∈ w, b = true) :
    L ∈ SPARSE encBits := by
  refine ⟨fun n => n + 1, by fun_prop, fun n => ?_⟩
  have hsub : {w ∈ L | (encBits w).length ≤ n} ⊆
      ((Finset.range (n + 1)).image fun k => List.replicate k true : Finset (List Bool)) := by
    rintro w ⟨hw, hn⟩
    rw [encBits_apply] at hn
    simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨w.length, by omega, (List.eq_replicate_iff.mpr ⟨rfl, hL w hw⟩).symm⟩
  calc {w ∈ L | (encBits w).length ≤ n}.encard
      ≤ (((Finset.range (n + 1)).image fun k => List.replicate k true : Finset (List Bool)) :
          Set (List Bool)).encard := Set.encard_le_encard hsub
    _ ≤ ((n + 1 : ℕ) : ℕ∞) := by
      rw [Set.encard_coe_eq_coe_finsetCard]
      exact Nat.cast_le.mpr (Finset.card_image_le.trans (Finset.card_range _).le)

/-- **The language of all words is not sparse:** it has `2 ^ n` words of each length `n`, more
than any polynomial bound allows. -/
theorem univ_notMem_SPARSE : (Set.univ : Set (List Bool)) ∉ SPARSE encBits := by
  rintro ⟨p, hp, h⟩
  obtain ⟨n, hn⟩ := hp.eventually_lt_two_pow.exists
  have hsub : (((Finset.univ : Finset (Fin n → Bool)).image List.ofFn : Finset (List Bool)) :
      Set (List Bool)) ⊆ {w ∈ Set.univ | (encBits w).length ≤ n} := by
    intro w hw
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hw
    obtain ⟨x, rfl⟩ := hw
    simp
  have hcard : ((Finset.univ : Finset (Fin n → Bool)).image List.ofFn).card = 2 ^ n := by
    rw [Finset.card_image_of_injective _ List.ofFn_injective, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have hle := (Set.encard_le_encard hsub).trans (h n)
  rw [Set.encard_coe_eq_coe_finsetCard, hcard] at hle
  exact absurd (Nat.cast_le.mp hle) (not_le.mpr hn)

end Cslib.Complexity
