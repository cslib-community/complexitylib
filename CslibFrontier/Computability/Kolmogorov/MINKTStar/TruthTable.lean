/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Kolmogorov.MINKTStar
public import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.List

/-!
# `MINKT*` on indexed patterns and truth tables

A pattern of `MINKT*` with `N` entries is often given as a table `T : Fin N → Option Bool`, as
`List.ofFn T`. This module states consistency and membership for such patterns without lists:
a total table `y : BitString N` is consistent with `List.ofFn T` exactly when `y` agrees with `T`
at every specified entry. When `N = 2 ^ L`, total tables are truth tables of Boolean functions on
`L` inputs, listed in the order of `BitString.equivFin`, as in `MCSP.truthTable` and in the partial
tables of `PartialMCSP`. The agreement condition is then the right-hand side of
`PartialMCSP.Instance.agreesWith_iff_table`.

## Main results

* `Cslib.Kolmogorov.MINKTStar.consistent_ofFn_iff`: consistency of a table with an indexed
  pattern, entrywise.
* `Cslib.Kolmogorov.MINKTStar.consistent_ofFn_iff_exists`: the strings consistent with an indexed
  pattern are the lists of the tables that agree with it.
* `Cslib.Kolmogorov.MINKTStar.mk_ofFn_mem_iff`: membership of an indexed pattern, via tables.
* `Cslib.Kolmogorov.MINKTStar.mk_ofFn_mem_iff_exists_booleanFunction`: membership of a pattern of
  length `2 ^ L`, via the truth tables of Boolean functions on `L` inputs.

## References

The truth-table form is used in the no case of the library's proof of the `MINKT*` clause of
[Hirahara2022, Theorem I.2], `MINKTStar.rpHard` in `Hardness.lean`. There, a count of programs
replaces the source's argument.
-/

public section

namespace Cslib.Kolmogorov.MINKTStar

/-- A table `y` is consistent with the indexed pattern `T` exactly when it agrees with `T` at every
specified entry. -/
theorem consistent_ofFn_iff {N : ℕ} {T : Fin N → Option Bool} {y : BitString N} :
    Consistent (List.ofFn T) (List.ofFn y) ↔ ∀ i b, T i = some b → y i = b := by
  rw [consistent_iff]
  simp only [List.length_ofFn, List.getElem_ofFn, true_and]
  refine ⟨fun h i b hb => (h i i.isLt i.isLt b hb).symm, fun h i hi _ b hb => (h ⟨i, hi⟩ b hb).symm⟩

/-- The strings consistent with an indexed pattern are the lists of the tables that agree with it.
-/
theorem consistent_ofFn_iff_exists {N : ℕ} {T : Fin N → Option Bool} {y : List Bool} :
    Consistent (List.ofFn T) y ↔
      ∃ z : BitString N, List.ofFn z = y ∧ ∀ i b, T i = some b → z i = b := by
  constructor
  · intro h
    have hlen : y.length = N := by simpa using h.length_eq.symm
    refine ⟨BitString.ofList N y, BitString.ofFn_ofList hlen, ?_⟩
    rw [← consistent_ofFn_iff, BitString.ofFn_ofList hlen]
    exact h
  · rintro ⟨z, rfl, hz⟩
    exact consistent_ofFn_iff.mpr hz

/-- An indexed pattern is a yes-instance of `MINKT*` exactly when some table that agrees with it
has `K^t` at most the threshold. -/
theorem mk_ofFn_mem_iff {N t s : ℕ} {T : Fin N → Option Bool} :
    (⟨List.ofFn T, t, s⟩ : Instance) ∈ MINKTStar ↔
      ∃ z : BitString N, (∀ i b, T i = some b → z i = b) ∧ timeBoundedAt t (List.ofFn z) ≤ s := by
  simp only [mk_mem_iff, consistent_ofFn_iff_exists]
  constructor
  · rintro ⟨_, ⟨z, rfl, hz⟩, hK⟩
    exact ⟨z, hz, hK⟩
  · rintro ⟨z, hz, hK⟩
    exact ⟨_, ⟨z, rfl, hz⟩, hK⟩

/-- **Truth-table form.** A pattern of length `2 ^ L`, indexed in the order of
`BitString.equivFin`, is a yes-instance of `MINKT*` exactly when some Boolean function on `L`
inputs agrees with it at every specified entry and has a truth table of `K^t` at most the
threshold. -/
theorem mk_ofFn_mem_iff_exists_booleanFunction {L t s : ℕ} {T : Fin (2 ^ L) → Option Bool} :
    (⟨List.ofFn T, t, s⟩ : Instance) ∈ MINKTStar ↔
      ∃ h : BooleanFunction L, (∀ i b, T i = some b → h ((BitString.equivFin L).symm i) = b) ∧
        timeBoundedAt t (List.ofFn fun i => h ((BitString.equivFin L).symm i)) ≤ s := by
  rw [mk_ofFn_mem_iff]
  constructor
  · rintro ⟨z, hz, hK⟩
    exact ⟨fun x => z (BitString.equivFin L x), by simpa using hz, by simpa using hK⟩
  · rintro ⟨h, hh, hK⟩
    exact ⟨fun i => h ((BitString.equivFin L).symm i), hh, hK⟩

end Cslib.Kolmogorov.MINKTStar
