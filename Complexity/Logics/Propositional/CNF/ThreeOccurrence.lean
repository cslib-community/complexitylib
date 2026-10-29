/-
Copyright (c) 2026 Erik Demaine, Stefan Langerman, GPT 5.6. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.ImplicationCycle
public import Complexity.Logics.Propositional.CNF.ModelCount
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Occurrence splitting

Each literal occurrence receives its own copy of its variable, indexed by its clause and literal
positions. Binary implication cycles force all copies of an original variable to agree.
Literal occurrences include repetitions within one clause. This is the construction in
[Papadimitriou, Proposition 9.3][Papadimitriou94]. Only the bound on occurrences of each variable
is formalized here; the additional bound of two occurrences per signed literal is not claimed.

Adapted from `lean-trominoes` at `6d5b36c15cec6cb18d30137b7f1c7fb92ea24332`,
[PeriodicThreeSATThree.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThree.lean),
[PeriodicThreeSATThreeCorrectness.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreeCorrectness.lean), and
[PeriodicThreeSATThreeExactSize.lean](https://github.com/edemaine/lean-trominoes/blob/6d5b36c15cec6cb18d30137b7f1c7fb92ea24332/LeanTrominoes/SAT/ThreeSAT/PeriodicThreeSATThreeExactSize.lean).
This construction uses ordinary CNF formulas and Boolean assignments.

The model-count preservation proof is original here, an elementary consequence of `copies_agree`.

## Main definitions

* `Cslib.Logic.PL.CNF.occurrenceClauses`: separate the literal occurrences.
* `Cslib.Logic.PL.CNF.toThreeOccurrence`: add implication cycles to the separated clauses.

## Main results

* `Cslib.Logic.PL.CNF.eval_toThreeOccurrence_iff`: correspondence of satisfying assignments.
* `Cslib.Logic.PL.CNF.satisfiable_toThreeOccurrence`: equisatisfiability.
* `Cslib.Logic.PL.CNF.modelCount_toThreeOccurrence`: preservation of satisfying-assignment counts.
* `Cslib.Logic.PL.CNF.width_toThreeOccurrence`: preservation of width bounds of at least two.
* `Cslib.Logic.PL.CNF.count_vars_toThreeOccurrence_le`: at most three literal occurrences.
* `Cslib.Logic.PL.CNF.length_toThreeOccurrence`,
  `Cslib.Logic.PL.CNF.length_vars_toThreeOccurrence`,
  `Cslib.Logic.PL.CNF.numVars_toThreeOccurrence`: exact linear clause, literal and variable counts.

## References

* [C. H. Papadimitriou, *Computational Complexity*, Proposition 9.3][Papadimitriou94]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*}

/-- Replace each literal by a copy named by its original variable and its two positions.

`Cslib.Logic.PL.occurrences` enumerates the same positions as a flat list of triples
`(clause index, literal index, literal)`. This clause-preserving traversal instead names each
copy `(original variable, clause index, literal index)`, retaining the original clause
boundaries. -/
def occurrenceClauses (φ : CNF V) : CNF (V × ℕ × ℕ) :=
  φ.zipIdx.map fun c => c.1.zipIdx.map fun l => ((l.1.1, c.2, l.2), l.1.2)

/-- The copies belonging to one variable, in their original occurrence order. -/
def occurrenceCopies [DecidableEq V] (φ : CNF V) (v : V) : List (V × ℕ × ℕ) :=
  φ.occurrenceClauses.vars.filter (fun x => x.1 == v)

/-- Split literal occurrences, then add one directed implication cycle per original variable. -/
def toThreeOccurrence [DecidableEq V] (φ : CNF V) : CNF (V × ℕ × ℕ) :=
  φ.occurrenceClauses ++ φ.distinctVars.flatMap (fun v => implicationCycle (φ.occurrenceCopies v))

/-- Copying literals preserves the list of clause lengths. -/
theorem map_length_occurrenceClauses (φ : CNF V) :
    φ.occurrenceClauses.map List.length = φ.map List.length := by
  simp only [occurrenceClauses, List.map_map, Function.comp_def, List.length_map,
    List.length_zipIdx]
  simpa only [List.map_map, Function.comp_def] using
    congrArg (List.map List.length) (List.zipIdx_map_fst 0 φ)

/-- Forgetting copy indices recovers the original formula. -/
theorem relabel_occurrenceClauses (φ : CNF V) :
    φ.occurrenceClauses.relabel Prod.fst = φ := by
  simp only [occurrenceClauses, relabel, Clause.relabel, List.map_map, Function.comp_def]
  have hc (c : Clause V × ℕ) :
      (c.1.zipIdx.map fun l => (l.1.1, l.1.2)) = c.1 := by
    simp
  change (φ.zipIdx.map fun c => c.1.zipIdx.map fun l => (l.1.1, l.1.2)) = φ
  simp_rw [hc]
  exact List.zipIdx_map_fst 0 φ

/-- Forgetting copy indices recovers the original variable-occurrence list. -/
theorem map_fst_vars_occurrenceClauses (φ : CNF V) :
    φ.occurrenceClauses.vars.map Prod.fst = φ.vars := by
  rw [← vars_relabel, relabel_occurrenceClauses]

/-- Copied clauses evaluated by an original assignment have the original value. -/
theorem eval_occurrenceClauses (φ : CNF V) (σ : V → Bool) :
    φ.occurrenceClauses.eval (σ ∘ Prod.fst) = φ.eval σ := by
  rw [← eval_relabel, relabel_occurrenceClauses]

/-- Every cycle block forces its copies to agree. -/
theorem copies_agree [DecidableEq V] {φ : CNF V} {τ : V × ℕ × ℕ → Bool}
    (h : φ.toThreeOccurrence.eval τ = true) {x y : V × ℕ × ℕ}
    (hx : x ∈ φ.occurrenceClauses.vars) (hy : y ∈ φ.occurrenceClauses.vars)
    (he : x.1 = y.1) : τ x = τ y := by
  have hv : x.1 ∈ φ.distinctVars := by
    rw [mem_distinctVars, ← map_fst_vars_occurrenceClauses]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  have ht := h
  simp only [toThreeOccurrence, eval_append, Bool.and_eq_true] at ht
  have hc := (eval_flatMap_eq_true_iff τ _ _).1 ht.2 _ hv
  apply (eval_implicationCycle τ _).1 hc x _ y _
  · simp [occurrenceCopies, hx]
  · simp [occurrenceCopies, hy, he]

/-- An assignment satisfies the split formula exactly when its occurring copies agree with a
satisfying assignment of the original formula. Together with `copies_agree`, this retains the
assignment correspondence, rather than just equisatisfiability. -/
theorem eval_toThreeOccurrence_iff [DecidableEq V] (φ : CNF V) (τ : V × ℕ × ℕ → Bool) :
    φ.toThreeOccurrence.eval τ = true ↔
      ∃ σ : V → Bool, φ.eval σ = true ∧ ∀ x ∈ φ.occurrenceClauses.vars, σ x.1 = τ x := by
  constructor
  · intro hτ
    classical
    let σ : V → Bool := fun v =>
      if h : ∃ x ∈ φ.occurrenceClauses.vars, x.1 = v then τ (Classical.choose h) else false
    have he : ∀ x ∈ φ.occurrenceClauses.vars, σ x.1 = τ x := by
      intro x hx
      have hex : ∃ y ∈ φ.occurrenceClauses.vars, y.1 = x.1 := ⟨x, hx, rfl⟩
      simp only [σ, dite_eq_left hex]
      exact copies_agree hτ (Classical.choose_spec hex).1 hx (Classical.choose_spec hex).2
    refine ⟨σ, ?_, he⟩
    rw [← eval_occurrenceClauses]
    have ht := hτ
    simp only [toThreeOccurrence, eval_append, Bool.and_eq_true] at ht
    exact (eval_congr he).trans ht.1
  · rintro ⟨σ, hσ, he⟩
    rw [toThreeOccurrence, eval_append, Bool.and_eq_true]
    refine ⟨(eval_congr he).symm.trans ((eval_occurrenceClauses φ σ).trans hσ),
      (eval_flatMap_eq_true_iff _ _ _).2 fun v _ => ?_⟩
    rw [eval_implicationCycle]
    intro x hx y hy
    obtain ⟨hx, hxv⟩ := List.mem_filter.1 hx
    obtain ⟨hy, hyv⟩ := List.mem_filter.1 hy
    simp only [beq_iff_eq] at hxv hyv
    calc τ x = σ x.1 := (he x hx).symm
      _ = σ y.1 := congrArg σ (hxv.trans hyv.symm)
      _ = τ y := he y hy

/-- Occurrence splitting preserves satisfiability, including empty clauses and formulas. -/
theorem satisfiable_toThreeOccurrence [DecidableEq V] (φ : CNF V) :
    φ.toThreeOccurrence.Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨τ, hτ⟩
    obtain ⟨σ, hσ, _⟩ := (eval_toThreeOccurrence_iff φ τ).1 hτ
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ ∘ Prod.fst, (eval_toThreeOccurrence_iff φ _).2 ⟨σ, hσ, fun _ _ => rfl⟩⟩

/-- Cycles are binary, so a width bound of at least two is preserved. -/
theorem width_toThreeOccurrence [DecidableEq V] {φ : CNF V} {k : ℕ} (hk : 2 ≤ k)
    (hφ : ∀ c ∈ φ, c.length ≤ k) : ∀ c ∈ φ.toThreeOccurrence, c.length ≤ k := by
  intro c hc
  rcases List.mem_append.1 hc with hc | hc
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hc
    simpa using hφ d.1 (List.fst_mem_of_mem_zipIdx hd)
  · obtain ⟨v, _, hc⟩ := List.mem_flatMap.1 hc
    rw [length_of_mem_implicationCycle _ hc]
    exact hk

/-- Every literal occurrence gets a distinct copy, even repeated literals in one clause. -/
theorem nodup_vars_occurrenceClauses (φ : CNF V) : φ.occurrenceClauses.vars.Nodup := by
  have he : φ.occurrenceClauses.vars = φ.zipIdx.flatMap
      (fun c => c.1.zipIdx.map fun l => (l.1.1, c.2, l.2)) := by
    simp [occurrenceClauses, vars, List.map_flatten, List.flatMap, List.map_map,
      Function.comp_def]
  rw [he, List.nodup_flatMap]
  constructor
  · intro c _
    apply List.Nodup.of_map (f := fun x : V × ℕ × ℕ => x.2.2)
    simpa only [List.map_map, Function.comp_def] using List.nodup_zipIdx_map_snd c.1
  · have h : φ.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) := by
      simpa only [List.Nodup, List.pairwise_map] using List.nodup_zipIdx_map_snd φ
    apply h.imp
    intro a b hab
    rw [Function.onFun, List.disjoint_left]
    intro x hx hy
    obtain ⟨i, _, hi⟩ := List.mem_map.1 hx
    obtain ⟨j, _, hj⟩ := List.mem_map.1 hy
    exact hab (congrArg (fun x : V × ℕ × ℕ => x.2.1) (hi.trans hj.symm))

/-- A copy occurs exactly three times in the output: once in a source clause, once as the
antecedent of an implication, and once as its consequent. -/
theorem count_vars_toThreeOccurrence [DecidableEq V] (φ : CNF V) (x : V × ℕ × ℕ) :
    φ.toThreeOccurrence.vars.count x = 3 * φ.occurrenceClauses.vars.count x := by
  have hf (v : V) : (φ.occurrenceCopies v).count x =
      if v = x.1 then φ.occurrenceClauses.vars.count x else 0 := by
    by_cases h : v = x.1
    · subst v
      simp [occurrenceCopies]
    · rw [ite_eq_right h]
      apply List.count_eq_zero.2
      simp only [occurrenceCopies, List.mem_filter, beq_iff_eq]
      intro hx
      exact h hx.2.symm
  have hs : (φ.distinctVars.map (fun v => (φ.occurrenceCopies v).count x)).sum =
      φ.occurrenceClauses.vars.count x := by
    simp_rw [hf]
    by_cases hx : x ∈ φ.occurrenceClauses.vars
    · rw [List.sum_map_eq_nsmul_single x.1 _ (fun _ h _ => by simp [h])]
      have hm : x.1 ∈ φ.vars := by
        rw [← map_fst_vars_occurrenceClauses]
        exact List.mem_map.2 ⟨x, hx, rfl⟩
      simp [nodup_distinctVars, mem_distinctVars, hm]
    · simp [List.count_eq_zero.2 hx]
  have hv (a b : CNF (V × ℕ × ℕ)) : (a ++ b).vars = a.vars ++ b.vars := by
    simp [vars]
  have hflat (l : List V) :
      CNF.vars (l.flatMap fun v => implicationCycle (φ.occurrenceCopies v)) =
        l.flatMap (fun v => (implicationCycle (φ.occurrenceCopies v)).vars) := by
    induction l with
    | nil => rfl
    | cons v l ih => simp [hv, ih]
  rw [toThreeOccurrence, hv, List.count_append, hflat, List.count_flatMap]
  simp_rw [Function.comp_def, count_vars_implicationCycle]
  rw [List.sum_map_mul_left, hs]
  omega

/-- Every variable has at most three literal occurrences, counting repetitions. -/
theorem count_vars_toThreeOccurrence_le [DecidableEq V] (φ : CNF V) (x : V × ℕ × ℕ) :
    φ.toThreeOccurrence.vars.count x ≤ 3 := by
  rw [count_vars_toThreeOccurrence]
  have := (List.nodup_iff_count_le_one.1 (nodup_vars_occurrenceClauses φ)) x
  omega

/-- The number of copies belonging to an original variable is its literal-occurrence count. -/
theorem length_occurrenceCopies [DecidableEq V] (φ : CNF V) (v : V) :
    (φ.occurrenceCopies v).length = φ.vars.count v := by
  change (φ.occurrenceClauses.vars.filter (fun x => x.1 == v)).length = _
  rw [← List.countP_eq_length_filter]
  conv_rhs => rw [← map_fst_vars_occurrenceClauses]
  rw [List.count_eq_countP, List.countP_map]
  rfl

private theorem sum_count_distinctVars [DecidableEq V] (φ : CNF V) :
    (φ.distinctVars.map fun v => φ.vars.count v).sum = φ.vars.length := by
  have hp : φ.distinctVars.Perm φ.vars.dedup :=
    (List.perm_ext_iff_of_nodup (nodup_distinctVars φ) (List.nodup_dedup _)).2
      (fun v => by simp [mem_distinctVars])
  rw [(hp.map _).sum_eq, List.sum_map_count_dedup_eq_length]

/-- Splitting adds exactly one binary clause per input literal occurrence. -/
theorem length_toThreeOccurrence [DecidableEq V] (φ : CNF V) :
    φ.toThreeOccurrence.length = φ.length + φ.vars.length := by
  simp only [toThreeOccurrence, List.length_append, occurrenceClauses, List.length_map,
    List.length_zipIdx, List.length_flatMap]
  simp_rw [length_implicationCycle, length_occurrenceCopies]
  rw [sum_count_distinctVars]

/-- Splitting triples the total number of literal occurrences. -/
theorem length_vars_toThreeOccurrence [DecidableEq V] (φ : CNF V) :
    φ.toThreeOccurrence.vars.length = 3 * φ.vars.length := by
  rw [length_vars, toThreeOccurrence, List.map_append, List.sum_append,
    map_length_occurrenceClauses, ← length_vars]
  have hc (vs : List (V × ℕ × ℕ)) :
      ((implicationCycle vs).map List.length).sum = 2 * vs.length := by
    rw [List.sum_eq_length_nsmul _ 2]
    · simp [Nat.mul_comm]
    · intro n hn
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn
      exact length_of_mem_implicationCycle vs hc
  simp only [List.flatMap, List.map_flatten, List.sum_flatten, List.map_map,
    Function.comp_def]
  simp_rw [hc, length_occurrenceCopies]
  rw [List.sum_map_mul_left, sum_count_distinctVars]
  omega

/-- There is exactly one distinct output variable per input literal occurrence. -/
theorem numVars_toThreeOccurrence [DecidableEq V] (φ : CNF V) :
    φ.toThreeOccurrence.numVars = φ.vars.length := by
  have he : φ.toThreeOccurrence.vars.toFinset = φ.occurrenceClauses.vars.toFinset := by
    ext x
    simp only [List.mem_toFinset, ← List.count_pos_iff, count_vars_toThreeOccurrence]
    omega
  rw [numVars, he, List.toFinset_card_of_nodup (nodup_vars_occurrenceClauses φ)]
  simpa using congrArg List.length (map_fst_vars_occurrenceClauses φ)

/-- Occurrence splitting preserves the number of satisfying assignments on occurring variables,
including empty formulas, empty clauses, and repeated literals. -/
theorem modelCount_toThreeOccurrence [DecidableEq V] (φ : CNF V) :
    φ.toThreeOccurrence.modelCount = φ.modelCount := by
  classical
  have hmem (x : V × ℕ × ℕ) :
      x ∈ φ.toThreeOccurrence.vars ↔ x ∈ φ.occurrenceClauses.vars := by
    simp only [← List.count_pos_iff, count_vars_toThreeOccurrence]
    omega
  have hfst {x : V × ℕ × ℕ} (hx : x ∈ φ.occurrenceClauses.vars) : x.1 ∈ φ.vars := by
    rw [← map_fst_vars_occurrenceClauses]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  have hex (v : φ.vars.toFinset) : ∃ x ∈ φ.occurrenceClauses.vars, x.1 = v := by
    apply List.mem_map.1
    simpa only [map_fst_vars_occurrenceClauses] using List.mem_toFinset.1 v.2
  let copy (v : φ.vars.toFinset) : V × ℕ × ℕ := Classical.choose (hex v)
  have hcopy (v : φ.vars.toFinset) : copy v ∈ φ.occurrenceClauses.vars ∧ (copy v).1 = v :=
    Classical.choose_spec (hex v)
  let f (τ : V × ℕ × ℕ → Bool) (v : φ.vars.toFinset) : Bool := τ (copy v)
  refine modelCount_eq_card_filter f (fun τ => φ.eval (φ.extendAssignment τ) = true)
    (fun σ τ hσ hτ => ?_) fun τ => ?_
  · constructor
    · intro he x hx
      have hx := (hmem x).1 hx
      let v : φ.vars.toFinset := ⟨x.1, List.mem_toFinset.2 (hfst hx)⟩
      calc σ x = σ (copy v) := copies_agree hσ hx (hcopy v).1 (hcopy v).2.symm
        _ = τ (copy v) := congrFun he v
        _ = τ x := copies_agree hτ (hcopy v).1 hx (hcopy v).2
    · intro he
      exact funext fun v => he (copy v) ((hmem _).2 (hcopy v).1)
  · constructor
    · intro hτ
      refine ⟨φ.extendAssignment τ ∘ Prod.fst, ?_, funext fun v => ?_⟩
      · exact (eval_toThreeOccurrence_iff φ _).2 ⟨φ.extendAssignment τ, hτ, fun _ _ => rfl⟩
      · change φ.extendAssignment τ (copy v).1 = τ v
        rw [(hcopy v).2, extendAssignment_of_mem _ (List.mem_toFinset.1 v.2)]
    · rintro ⟨σ, hσ, rfl⟩
      rw [← eval_occurrenceClauses]
      have he : ∀ x ∈ φ.occurrenceClauses.vars,
          (φ.extendAssignment (f σ) ∘ Prod.fst) x = σ x := by
        intro x hx
        change φ.extendAssignment (f σ) x.1 = σ x
        rw [extendAssignment_of_mem _ (hfst hx)]
        exact copies_agree hσ (hcopy _).1 hx (hcopy _).2
      have ht := hσ
      simp only [toThreeOccurrence, eval_append, Bool.and_eq_true] at ht
      exact (eval_congr he).trans ht.1

end Cslib.Logic.PL.CNF
