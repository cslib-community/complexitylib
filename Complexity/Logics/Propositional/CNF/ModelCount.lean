/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Data.List.SelectDistinct
public import Complexity.Logics.Propositional.CNF
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting satisfying assignments

`CNF.modelCount φ` is the number of satisfying assignments of a formula `φ` in conjunctive normal
form: the assignments of the variables occurring in `φ` (`CNF.vars`) that satisfy it. Variables
not occurring in `φ` are not counted, so the count does not depend on the type of variables.
Relabelling results are in `CNF.ModelCount.Relabel`. As a function of the formula this is the
counting problem `#SAT` [Valiant][Valiant1979].

The distinct variables of `φ` in order of their first occurrence are listed by `CNF.distinctVars`,
of length `CNF.numVars` (`CNF.length_distinctVars`), and the literal occurrences with their clause
and position indices are listed by `occurrences`. On any list of variables `vs`,
`bitsAssignment vs i` assigns to the variable at position `j` of `vs` the binary digit `j` of `i`,
so satisfiability of a formula whose variables lie in `vs` is a search over `i < 2 ^ |vs|`
(`CNF.satisfiable_iff_exists_bitsAssignment`).

Counts are usually computed through a map `f` from assignments to some finite type: if two
satisfying assignments have the same image exactly when they agree on the variables of `φ`, then
`φ` has as many satisfying assignments as there are images of satisfying assignments
(`CNF.modelCount_eq_card_filter`). A formula has a satisfying assignment exactly when its count
is positive (`CNF.modelCount_pos_iff`), and exactly one when every satisfying assignment agrees
with a given one on the variables of the formula (`CNF.modelCount_eq_one_iff`).

## Main definitions

* `Cslib.Logic.PL.CNF.numVars`: the number of distinct variables of a formula.
* `Cslib.Logic.PL.CNF.distinctVars`: the distinct variables of a formula, in order of first
  occurrence.
* `Cslib.Logic.PL.Occurrence`, `Cslib.Logic.PL.occurrences`: the occurrences of literals in a
  formula.
* `Cslib.Logic.PL.bitsAssignment`: the assignment numbered by `i` on a list of variables.
* `Cslib.Logic.PL.CNF.extendAssignment`: an assignment of the variables of a formula, extended by
  `false` to all variables.
* `Cslib.Logic.PL.CNF.modelCount`: the number of satisfying assignments.

## Main results

* `Cslib.Logic.PL.CNF.mem_distinctVars`, `Cslib.Logic.PL.CNF.nodup_distinctVars`,
  `Cslib.Logic.PL.CNF.distinctVars_toFinset`, `Cslib.Logic.PL.CNF.length_distinctVars`:
  `φ.distinctVars` lists the `φ.numVars` variables of `φ` without repetition.
* `Cslib.Logic.PL.mem_occurrences`, `Cslib.Logic.PL.map_occurrences`,
  `Cslib.Logic.PL.length_occurrences`: the literal occurrences of `φ` and their variables.
* `Cslib.Logic.PL.exists_lt_two_pow_bitsAssignment_eq`,
  `Cslib.Logic.PL.CNF.satisfiable_iff_exists_bitsAssignment`: satisfiability is a search over
  `2 ^ |vs|` numbered assignments.
* `Cslib.Logic.PL.CNF.modelCount_le_two_pow_numVars`: at most `2 ^ φ.numVars` satisfying
  assignments.
* `Cslib.Logic.PL.CNF.modelCount_eq_card_filter`: counting satisfying assignments through a map.
* `Cslib.Logic.PL.CNF.modelCount_pos_iff`, `Cslib.Logic.PL.CNF.modelCount_eq_one_iff`.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 2.3][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Logic.PL

open Cslib.Complexity

variable {V : Type*}

/-- An occurrence of a literal in a formula: its clause, its position in the clause, and the
literal. -/
abbrev Occurrence (V : Type*) : Type _ := ℕ × ℕ × Literal V

/-- The occurrences of literals in a formula. -/
def occurrences (φ : CNF V) : List (Occurrence V) :=
  φ.zipIdx.flatMap fun c => c.1.zipIdx.map fun l => (c.2, l.2, l.1)

/-- Membership in `occurrences φ` as valid clause and literal indices. -/
theorem mem_occurrences {φ : CNF V} {o : Occurrence V} :
    o ∈ occurrences φ ↔ ∃ (h₁ : o.1 < φ.length) (h₂ : o.2.1 < φ[o.1].length),
      o.2.2 = φ[o.1][o.2.1] := by
  obtain ⟨i, j, l⟩ := o
  simp only [occurrences, List.mem_flatMap, List.mem_map, List.mem_zipIdx_iff_getElem?]
  constructor
  · rintro ⟨⟨c, i'⟩, hc, ⟨l', j'⟩, hl, he⟩
    simp only [Prod.mk.injEq] at he hc hl
    obtain ⟨rfl, rfl, rfl⟩ := he
    obtain ⟨hi, hci⟩ := List.getElem?_eq_some_iff.1 hc
    subst hci
    obtain ⟨hj, hlj⟩ := List.getElem?_eq_some_iff.1 hl
    exact ⟨hi, hj, hlj.symm⟩
  · rintro ⟨hi, hj, hl⟩
    exact ⟨(φ[i], i), by simp [hi], (φ[i][j], j), by simp [hj], by rw [hl]⟩

/-- The variables of the occurrences, in order, are the variables of the formula. -/
theorem map_occurrences (φ : CNF V) : (occurrences φ).map (fun o => o.2.2.1) = φ.vars := by
  have hc : ∀ c : Clause V × ℕ, (c.1.zipIdx.map fun l => (c.2, l.2, l.1).2.2.1) =
      c.1.map Prod.fst := fun c => by
    calc (c.1.zipIdx.map fun l => (c.2, l.2, l.1).2.2.1) =
        (c.1.zipIdx.map Prod.fst).map Prod.fst := by rw [List.map_map]; rfl
      _ = c.1.map Prod.fst := by rw [List.zipIdx_map_fst]
  calc (occurrences φ).map (fun o => o.2.2.1)
      = φ.zipIdx.flatMap fun c => c.1.map Prod.fst := by
        simp only [occurrences, List.map_flatMap, List.map_map, Function.comp_def, hc]
    _ = (φ.zipIdx.map Prod.fst).flatMap fun c => c.map Prod.fst := by rw [List.flatMap_map]
    _ = φ.vars := by
        rw [List.zipIdx_map_fst, CNF.vars, List.map_flatten, List.flatMap_def]

/-- A formula has one occurrence for each occurrence of a variable. -/
theorem length_occurrences (φ : CNF V) : (occurrences φ).length = φ.vars.length := by
  rw [← map_occurrences, List.length_map]

variable [DecidableEq V]

/-- The number of distinct variables of a formula. -/
def CNF.numVars (φ : CNF V) : ℕ := φ.vars.toFinset.card

/-- A formula has at most as many distinct variables as occurrences of variables. -/
theorem CNF.numVars_le_length_vars (φ : CNF V) : φ.numVars ≤ φ.vars.length :=
  List.toFinset_card_le _

/-- A formula with `m` clauses of at most `k` literals has at most `k m` variables. -/
theorem CNF.numVars_le_mul_length {k : ℕ} {φ : CNF V} (h : ∀ c ∈ φ, c.length ≤ k) :
    φ.numVars ≤ k * φ.length :=
  φ.numVars_le_length_vars.trans (CNF.length_vars_le_mul_length h)

/-- The variables of `φ` without repetitions, in the order of their first occurrences. -/
def CNF.distinctVars (φ : CNF V) : List V :=
  selectDistinct φ.vars (List.replicate φ.vars.length true)

/-- The distinct variables of `φ` are the variables of `φ`. -/
theorem CNF.mem_distinctVars {φ : CNF V} {v : V} : v ∈ φ.distinctVars ↔ v ∈ φ.vars :=
  mem_selectDistinct_replicate

/-- `φ.distinctVars` lists each variable once. -/
theorem CNF.nodup_distinctVars (φ : CNF V) : φ.distinctVars.Nodup :=
  nodup_selectDistinct _ _

/-- The finite set of distinct variables of `φ` is the finite set of variables of `φ`. -/
theorem CNF.distinctVars_toFinset (φ : CNF V) : φ.distinctVars.toFinset = φ.vars.toFinset := by
  ext v
  simp [CNF.mem_distinctVars]

/-- A formula has `numVars` distinct variables. -/
theorem CNF.length_distinctVars (φ : CNF V) : φ.distinctVars.length = φ.numVars :=
  length_selectDistinct_replicate φ.vars

/-- The assignment numbered by `i` on the list of variables `vs`: the variable at position `j` of
`vs` takes the binary digit `j` of `i`. -/
def bitsAssignment (vs : List V) (i : ℕ) (v : V) : Bool := i.testBit (vs.idxOf v)

/-- **Every assignment is numbered.** The assignments of the variables of a duplicate-free list
`vs` are the numbered assignments `bitsAssignment vs i` for `i < 2 ^ |vs|`. -/
theorem exists_lt_two_pow_bitsAssignment_eq {vs : List V} (σ : V → Bool) :
    ∃ i < 2 ^ vs.length, ∀ v ∈ vs, bitsAssignment vs i v = σ v := by
  refine ⟨(BitVec.ofBoolListLE (vs.map σ)).toNat, (BitVec.isLt _).trans_eq (by simp),
    fun v hv => ?_⟩
  have hlt : vs.idxOf v < vs.length := List.idxOf_lt_length_iff.mpr hv
  rw [bitsAssignment, BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlt,
    List.getElem_idxOf hlt]
  rfl

/-- **Satisfiability by exhaustive search.** A formula whose variables are all in the list `vs` is
satisfiable exactly when it is satisfied by an assignment numbered by some `i < 2 ^ |vs|`. -/
theorem CNF.satisfiable_iff_exists_bitsAssignment {φ : CNF V} {vs : List V}
    (hφ : ∀ v ∈ φ.vars, v ∈ vs) :
    φ.Satisfiable ↔ ∃ i < 2 ^ vs.length, φ.eval (bitsAssignment vs i) = true := by
  refine ⟨fun ⟨σ, hσ⟩ => ?_, fun ⟨i, _, hi⟩ => ⟨_, hi⟩⟩
  obtain ⟨i, hi, hiσ⟩ := exists_lt_two_pow_bitsAssignment_eq (vs := vs) σ
  exact ⟨i, hi, (CNF.eval_congr fun v hv => hiσ v (hφ v hv)).trans hσ⟩

/-- The numbered assignment `bitsAssignment vs i` looks up the binary digit of `i` in `i.bits` at
the index of `v` in `vs`, defaulting to `false`. -/
theorem bitsAssignment_eq_getD (vs : List V) (i : ℕ) (v : V) :
    bitsAssignment vs i v = i.bits.getD (vs.idxOf v) false := by
  rw [bitsAssignment, Nat.testBit_eq_inth]
  rfl

/-- The assignment of all variables extending an assignment `τ` of the variables of `φ` by
`false`. -/
def CNF.extendAssignment (φ : CNF V) (τ : φ.vars.toFinset → Bool) (v : V) : Bool :=
  if h : v ∈ φ.vars.toFinset then τ ⟨v, h⟩ else false

/-- `φ.extendAssignment τ` agrees with `τ` on every variable occurring in `φ`. -/
theorem CNF.extendAssignment_of_mem {φ : CNF V} (τ : φ.vars.toFinset → Bool) {v : V}
    (hv : v ∈ φ.vars) : φ.extendAssignment τ v = τ ⟨v, List.mem_toFinset.2 hv⟩ := by
  simp [CNF.extendAssignment, hv]

/-- **The number of satisfying assignments** of `φ`: the assignments of the variables occurring
in `φ` that satisfy it. -/
def CNF.modelCount (φ : CNF V) : ℕ :=
  (Finset.univ.filter fun τ : φ.vars.toFinset → Bool => φ.eval (φ.extendAssignment τ) = true).card

/-- A formula has at most `2 ^ φ.numVars` satisfying assignments of its occurring variables. -/
theorem CNF.modelCount_le_two_pow_numVars (φ : CNF V) : φ.modelCount ≤ 2 ^ φ.numVars := by
  rw [CNF.modelCount, CNF.numVars]
  refine (Finset.card_filter_le _ _).trans ?_
  simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, le_rfl]

/-- An assignment of all variables satisfies `φ` exactly when its restriction to the variables of
`φ`, extended by `false`, does. -/
theorem CNF.eval_extendAssignment_restrict (φ : CNF V) (σ : V → Bool) :
    φ.eval (φ.extendAssignment fun v => σ v) = φ.eval σ :=
  CNF.eval_congr fun _ hv => CNF.extendAssignment_of_mem _ hv

/-- **Counting satisfying assignments through a map.** Let `f` send assignments to a finite type
so that two satisfying assignments have the same image exactly when they agree on the variables
of `φ`. Then the satisfying assignments of `φ` are as many as the images of satisfying
assignments, described by `P`. -/
theorem CNF.modelCount_eq_card_filter {ι : Type*} [Fintype ι] {φ : CNF V}
    (f : (V → Bool) → ι) (P : ι → Prop) [DecidablePred P]
    (hf : ∀ σ τ, φ.eval σ = true → φ.eval τ = true → (f σ = f τ ↔ ∀ v ∈ φ.vars, σ v = τ v))
    (hP : ∀ i, P i ↔ ∃ σ, φ.eval σ = true ∧ f σ = i) :
    φ.modelCount = (Finset.univ.filter P).card := by
  refine Finset.card_bij (fun τ _ => f (φ.extendAssignment τ)) (fun τ hτ => ?_)
    (fun τ₁ h₁ τ₂ h₂ h => ?_) fun i hi => ?_
  · rw [Finset.mem_filter] at hτ ⊢
    exact ⟨Finset.mem_univ _, (hP _).2 ⟨_, hτ.2, rfl⟩⟩
  · have h' := (hf _ _ (Finset.mem_filter.1 h₁).2 (Finset.mem_filter.1 h₂).2).1 h
    funext ⟨v, hv⟩
    have hv' := List.mem_toFinset.1 hv
    simpa only [CNF.extendAssignment_of_mem _ hv'] using h' v hv'
  · obtain ⟨σ, hσ, rfl⟩ := (hP i).1 (Finset.mem_filter.1 hi).2
    have he : φ.eval (φ.extendAssignment fun v => σ v) = true := by
      rw [CNF.eval_extendAssignment_restrict, hσ]
    exact ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, he⟩,
      (hf _ _ he hσ).2 fun _ hv => CNF.extendAssignment_of_mem _ hv⟩

/-- A formula has a satisfying assignment exactly when its count is positive. -/
theorem CNF.modelCount_pos_iff {φ : CNF V} : 0 < φ.modelCount ↔ φ.Satisfiable := by
  rw [CNF.modelCount, Finset.card_pos, Finset.filter_nonempty_iff]
  constructor
  · rintro ⟨τ, -, hτ⟩
    exact ⟨_, hτ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨fun v => σ v, Finset.mem_univ _, by rw [CNF.eval_extendAssignment_restrict, hσ]⟩

/-- A formula has exactly one satisfying assignment when some assignment satisfies it and every
satisfying assignment agrees with it on the variables of the formula. -/
theorem CNF.modelCount_eq_one_iff {φ : CNF V} :
    φ.modelCount = 1 ↔ ∃ σ : V → Bool, φ.eval σ = true ∧
      ∀ τ : V → Bool, φ.eval τ = true → ∀ v ∈ φ.vars, τ v = σ v := by
  rw [CNF.modelCount, Finset.card_eq_one]
  constructor
  · rintro ⟨τ₀, h⟩
    have hτ₀ : φ.eval (φ.extendAssignment τ₀) = true := by
      have := Finset.mem_singleton_self τ₀
      rw [← h, Finset.mem_filter] at this
      exact this.2
    refine ⟨_, hτ₀, fun τ hτ v hv => ?_⟩
    have hmem : (fun v => τ v : φ.vars.toFinset → Bool) ∈ ({τ₀} : Finset _) := by
      rw [← h, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [CNF.eval_extendAssignment_restrict, hτ]⟩
    rw [Finset.mem_singleton] at hmem
    rw [CNF.extendAssignment_of_mem _ hv, ← hmem]
  · rintro ⟨σ, hσ, h⟩
    refine ⟨fun v => σ v, Finset.eq_singleton_iff_unique_mem.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [CNF.eval_extendAssignment_restrict, hσ]⟩,
        fun τ hτ => funext fun ⟨v, hv⟩ => ?_⟩⟩
    have hv' := List.mem_toFinset.1 hv
    rw [← CNF.extendAssignment_of_mem τ hv']
    exact h _ (Finset.mem_filter.1 hτ).2 v hv'

end Cslib.Logic.PL
