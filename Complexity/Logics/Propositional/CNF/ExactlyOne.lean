/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF

/-!
# Exactly-one constraints

`CNF.exactlyOne vs` holds exactly when one variable of the list `vs` is true: one clause asks
for at least one of them, and one binary clause for each pair of distinct variables forbids two.
This is the standard one-hot encoding of a finite-valued quantity by Boolean variables.

`CNF.atMostOne` emits a clause for every ordered pair of distinct variables, so each pair appears
twice. The quadratic size is the same as for unordered pairs, and the semantics
(`CNF.eval_atMostOne`) then holds for lists with repetitions too, without a `Nodup` hypothesis.

## Main definitions

* `Cslib.Logic.PL.CNF.atLeastOne`, `Cslib.Logic.PL.CNF.atMostOne`, `Cslib.Logic.PL.CNF.exactlyOne`.

## Main results

* `Cslib.Logic.PL.CNF.eval_exactlyOne`: the semantics.
* `Cslib.Logic.PL.CNF.eq_true_iff_of_eval_exactlyOne`: once one variable of the list is known to
  be true, every variable of the list is true exactly when it is that one.
* `Cslib.Logic.PL.CNF.fst_mem_of_mem_exactlyOne`: the variables of the constraints are those of
  the list.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

variable {V : Type*}

/-- At least one variable of `vs` is true. -/
def CNF.atLeastOne (vs : List V) : CNF V := [vs.map (·, true)]

/-- `CNF.atLeastOne vs` holds under `σ` if and only if some variable in `vs` is true. -/
theorem CNF.eval_atLeastOne (σ : V → Bool) (vs : List V) :
    (CNF.atLeastOne vs).eval σ = true ↔ ∃ x ∈ vs, σ x = true := by
  simp [CNF.atLeastOne, Clause.eval_eq_true_iff]

variable [DecidableEq V]

/-- No two distinct variables of `vs` are true. -/
def CNF.atMostOne (vs : List V) : CNF V :=
  vs.flatMap fun x => (vs.filter (· ≠ x)).map fun y => [(x, false), (y, false)]

/-- Exactly one variable of `vs` is true. -/
def CNF.exactlyOne (vs : List V) : CNF V := CNF.atLeastOne vs ++ CNF.atMostOne vs

/-- `CNF.atMostOne vs` holds under `σ` if and only if no two distinct variables in `vs` are both
true. -/
theorem CNF.eval_atMostOne (σ : V → Bool) (vs : List V) :
    (CNF.atMostOne vs).eval σ = true ↔
      ∀ x ∈ vs, ∀ y ∈ vs, σ x = true → σ y = true → x = y := by
  rw [CNF.atMostOne, CNF.eval_flatMap_eq_true_iff]
  refine forall₂_congr fun x _ => ?_
  simp only [CNF.eval_eq_true_iff, List.forall_mem_map, List.mem_filter, Clause.eval_eq_true_iff,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
    decide_eq_true_eq, and_imp]
  constructor
  · intro h y hy hσx hσy
    by_contra hne
    rcases h y hy (Ne.symm hne) with h' | h' <;> simp_all
  · intro h y hy hne
    by_cases hσx : σ x = true
    · right
      by_contra hσy
      exact hne (h y hy hσx (by simpa using hσy)).symm
    · left
      simpa using hσx

/-- The variables of `CNF.atMostOne vs` are among `vs`. -/
theorem CNF.fst_mem_of_mem_atMostOne {vs : List V} {c : Clause V} (hc : c ∈ CNF.atMostOne vs)
    {l : Literal V} (hl : l ∈ c) : l.1 ∈ vs := by
  simp only [CNF.atMostOne, List.mem_flatMap, List.mem_map, List.mem_filter] at hc
  obtain ⟨x, hx, y, ⟨hy, -⟩, rfl⟩ := hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  exacts [hx, hy]

/-- The variables of `CNF.exactlyOne vs` are among `vs`. -/
theorem CNF.fst_mem_of_mem_exactlyOne {vs : List V} {c : Clause V}
    (hc : c ∈ CNF.exactlyOne vs) {l : Literal V} (hl : l ∈ c) : l.1 ∈ vs := by
  rcases List.mem_append.1 hc with hc | hc
  · obtain rfl := List.mem_singleton.1 hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hl
    exact hv
  · exact CNF.fst_mem_of_mem_atMostOne hc hl

/-- `CNF.exactlyOne vs` holds exactly when some variable of `vs` is true and no two distinct
variables of `vs` are. -/
theorem CNF.eval_exactlyOne (σ : V → Bool) (vs : List V) :
    (CNF.exactlyOne vs).eval σ = true ↔
      (∃ x ∈ vs, σ x = true) ∧ ∀ x ∈ vs, ∀ y ∈ vs, σ x = true → σ y = true → x = y := by
  simp [CNF.exactlyOne, CNF.eval_atLeastOne, CNF.eval_atMostOne]

/-- If exactly one variable of `vs` is true and `x ∈ vs` is true, then each `y ∈ vs` is true
exactly when `y = x`. -/
theorem CNF.eq_true_iff_of_eval_exactlyOne {σ : V → Bool} {vs : List V}
    (h : (CNF.exactlyOne vs).eval σ = true) {x : V} (hx : x ∈ vs) (hσx : σ x = true)
    {y : V} (hy : y ∈ vs) : σ y = true ↔ y = x :=
  ⟨fun hσy => ((CNF.eval_exactlyOne σ vs).1 h).2 y hy x hx hσy hσx, fun h => h ▸ hσx⟩

/-- An assignment that makes exactly the variable `x ∈ vs` true among `vs` satisfies
`CNF.exactlyOne vs`. -/
theorem CNF.eval_exactlyOne_of_iff {σ : V → Bool} {vs : List V} {x : V} (hx : x ∈ vs)
    (h : ∀ y ∈ vs, σ y = true ↔ y = x) : (CNF.exactlyOne vs).eval σ = true := by
  refine (CNF.eval_exactlyOne σ vs).2 ⟨⟨x, hx, (h x hx).2 rfl⟩, ?_⟩
  intro y hy y' hy' hσy hσy'
  rw [(h y hy).1 hσy, (h y' hy').1 hσy']

/-- `CNF.eq_true_iff_of_eval_exactlyOne` for the one-hot encoding `l.map f` of a quantity ranging
over `l`, along an injective naming `f` of its values. -/
theorem CNF.eq_true_iff_of_eval_exactlyOne_map {ι : Type*} {σ : V → Bool} {f : ι → V}
    (hf : Function.Injective f) {l : List ι} (h : (CNF.exactlyOne (l.map f)).eval σ = true)
    {x : ι} (hx : x ∈ l) (hσx : σ (f x) = true) {y : ι} (hy : y ∈ l) :
    σ (f y) = true ↔ y = x := by
  rw [CNF.eq_true_iff_of_eval_exactlyOne h (List.mem_map_of_mem hx) hσx (List.mem_map_of_mem hy),
    hf.eq_iff]

/-- `CNF.eval_exactlyOne_of_iff` for the one-hot encoding `l.map f`. -/
theorem CNF.eval_exactlyOne_map_of_iff {ι : Type*} {σ : V → Bool} {f : ι → V}
    (hf : Function.Injective f) {l : List ι} {x : ι} (hx : x ∈ l)
    (h : ∀ y ∈ l, σ (f y) = true ↔ y = x) : (CNF.exactlyOne (l.map f)).eval σ = true := by
  refine CNF.eval_exactlyOne_of_iff (List.mem_map_of_mem hx) fun v hv => ?_
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
  rw [h y hy, hf.eq_iff]

end Cslib.Logic.PL
