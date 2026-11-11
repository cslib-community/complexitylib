/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.TimeBounded
public import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Counting objects of small time-bounded Kolmogorov complexity

For every step budget `t`, fewer than `2 ^ (s + 1)` strings `y` satisfy `K^t(y) ≤ s`, since each
has a program of length at most `s`. This module transfers that bound along an injective encoding
into strings, and specializes it to the truth tables of Boolean functions. The bound holds for
every `t`, so a counting argument that uses it needs no time bound.

The truth table of `h : BooleanFunction L` lists its `2 ^ L` values in the order of
`BitString.equivFin`, as `List.ofFn fun i => h ((BitString.equivFin L).symm i)`. This is the order
of `MCSP.truthTable` and of the partial tables of `PartialMCSP`.

## Main results

* `Cslib.Kolmogorov.encard_setOf_timeBoundedAt_le_lt`: fewer than `2 ^ (s + 1)` objects of any
  type have `K^t(enc a) ≤ s` under an injective encoding `enc`.
* `Cslib.Kolmogorov.card_filter_timeBoundedAt_le_lt`: the same bound for the elements of a finite
  type, counted as a `Finset`.
* `Cslib.Kolmogorov.card_filter_timeBoundedAt_truthTable_le_lt`: fewer than `2 ^ (s + 1)` Boolean
  functions on `L` inputs have truth tables of `K^t` at most `s`.

## References

The truth-table count is used in the no case of the library's proof of the `MINKT*` clause of
[Hirahara2022, Theorem I.2] (`MINKTStar.rpHard`), where a count of programs replaces the source's
argument.
-/

public section

namespace Cslib.Kolmogorov

open DescriptionMethod

/-- Under an injective encoding into strings, fewer than `2 ^ (s + 1)` objects have encodings of
time-bounded complexity at most `s`, for every step budget `t`. -/
theorem encard_setOf_timeBoundedAt_le_lt {α : Type*} {enc : α → List Bool}
    (henc : enc.Injective) (t s : ℕ) :
    {a | timeBoundedAt t (enc a) ≤ s}.encard < 2 ^ (s + 1) := by
  rw [← henc.encard_image]
  refine (Set.encard_le_encard ?_).trans_lt
    (universalTM.encard_setOf_etimeBoundedComplexity_lt t (s + 1))
  rintro _ ⟨a, ha, rfl⟩
  change universalTM.etimeBoundedComplexity t (enc a) < ((s + 1 : ℕ) : ℕ∞)
  rw [Nat.cast_add, Nat.cast_one, ENat.lt_add_one_iff (ENat.natCast_ne_top s)]
  exact ha

/-- Under an injective encoding of a finite type into strings, fewer than `2 ^ (s + 1)` elements
have encodings of time-bounded complexity at most `s`, for every step budget `t`. -/
theorem card_filter_timeBoundedAt_le_lt {α : Type*} [Fintype α] {enc : α → List Bool}
    (henc : enc.Injective) (t s : ℕ) :
    (Finset.univ.filter fun a => timeBoundedAt t (enc a) ≤ s).card < 2 ^ (s + 1) := by
  have h := encard_setOf_timeBoundedAt_le_lt henc t s
  rw [← Finset.coe_filter_univ, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-- **Counting truth tables of small `K^t`.** For every step budget `t`, fewer than `2 ^ (s + 1)`
Boolean functions on `L` inputs have truth tables, listed in the order of `BitString.equivFin`, of
time-bounded complexity at most `s`. -/
theorem card_filter_timeBoundedAt_truthTable_le_lt (L t s : ℕ) :
    (Finset.univ.filter fun h : BooleanFunction L =>
      timeBoundedAt t (List.ofFn fun i => h ((BitString.equivFin L).symm i)) ≤ s).card <
      2 ^ (s + 1) := by
  refine card_filter_timeBoundedAt_le_lt (fun h₁ h₂ heq => ?_) t s
  funext x
  simpa using congrFun (List.ofFn_injective heq) (BitString.equivFin L x)

end Cslib.Kolmogorov
