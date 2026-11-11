/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.ClauseSet.Sparsification.CountingList

/-!
# General CNF simplification, subsumption, and deduplication bounds

This module supplies width-free semantic, model-counting, variable-support, size, and occurrence
lemmas for the formula simplification operations defined in `ClauseSet/Sparsification`:
tautology elimination (`removeTautologies`), literal deduplication (`dedup`), clause
deduplication (`dedupClauses`), subset-minimal subsumption reduction (`reduce`), and combined
normalizations (`normalize`, `countingNormalize`).

It also provides standalone clause subsumption lemmas and a general counting-scaling bridge
(`CNF.modelCount_eq_two_pow_mul_of_eval_eq`) tracking unused-variable powers of two when a
simplification drops variables from `CNF.vars`.

## Main results

* `Cslib.Logic.PL.CNF.modelCount_eq_two_pow_mul_of_eval_eq`: occurring-variable model count
  scaling under any semantic equivalence with shrinking variable support.
* `Cslib.Logic.PL.Clause.eval_eq_true_of_subclause`,
  `Cslib.Logic.PL.CNF.eval_filter_ne_of_subsumed`: general clause subsumption lemmas.
* `Cslib.Logic.PL.CNF.Sparsification.eval_dedup`, `eval_dedupClauses`, `eval_reduce`,
  `eval_normalize`: width-free evaluation preservation for every normalization stage.
* `Cslib.Logic.PL.CNF.Sparsification.modelCountOn_normalize`, `modelCount_normalize`,
  `modelCount_countingNormalize`, `modelCount_removeTautologies`: exact declared-universe and
  occurring-variable model count conservation.
* `Cslib.Logic.PL.CNF.Sparsification.length_normalize_le`, `vars_length_normalize_le`,
  `occurrences_normalize_le`: clause-count, total-literal-count, and occurrence bounds.
-/

public section

namespace Cslib.Logic.PL

open scoped List

variable {V : Type*}

/-! ### Generic semantic conservation and subsumption -/

/-- Any two formulas with identical Boolean evaluation have the same satisfiability. -/
theorem CNF.satisfiable_iff_of_eval_eq {φ ψ : CNF V} (h : ∀ σ : V → Bool, ψ.eval σ = φ.eval σ) :
    ψ.Satisfiable ↔ φ.Satisfiable := by
  simp [CNF.Satisfiable, h]

/-- Any two formulas with identical Boolean evaluation have the same declared-universe model
count. -/
theorem CNF.modelCountOn_eq_of_eval_eq [DecidableEq V] {φ ψ : CNF V}
    (h : ∀ σ : V → Bool, ψ.eval σ = φ.eval σ) (declared : Finset V) :
    ψ.modelCountOn declared = φ.modelCountOn declared := by
  simp only [CNF.modelCountOn, h]

/-- If `ψ` evaluates identically to `φ` and uses a subset of `φ`'s variables, `φ.modelCount`
scales `ψ.modelCount` by `2 ^ (φ.numVars - ψ.numVars)`. -/
theorem CNF.modelCount_eq_two_pow_mul_of_eval_eq [DecidableEq V] {φ ψ : CNF V}
    (hvars : ψ.vars.toFinset ⊆ φ.vars.toFinset)
    (h : ∀ σ : V → Bool, ψ.eval σ = φ.eval σ) :
    φ.modelCount = 2 ^ (φ.numVars - ψ.numVars) * ψ.modelCount := by
  rw [← CNF.modelCountOn_vars φ, ← CNF.modelCountOn_eq_of_eval_eq h φ.vars.toFinset,
    CNF.modelCountOn_eq_mul_modelCount ψ φ.vars.toFinset hvars]
  rfl

/-- If every literal of `c` belongs to `d`, any assignment satisfying `c` satisfies `d`. -/
theorem Clause.eval_eq_true_of_subset [DecidableEq V] {c d : Clause V}
    (hsub : c.toFinset ⊆ d.toFinset) {σ : V → Bool} (hc : c.eval σ = true) :
    d.eval σ = true := by
  obtain ⟨l, hl, hσ⟩ := (Clause.eval_eq_true_iff σ c).mp hc
  exact (Clause.eval_eq_true_iff σ d).mpr
    ⟨l, List.mem_toFinset.mp (hsub (List.mem_toFinset.mpr hl)), hσ⟩

/-- Subclause subsumption preserves clause truth. -/
theorem Clause.eval_eq_true_of_subclause [DecidableEq V] {c d : Clause V}
    (hsub : CNF.Sparsification.subclause c d = true) {σ : V → Bool} (hc : c.eval σ = true) :
    d.eval σ = true :=
  Clause.eval_eq_true_of_subset (CNF.Sparsification.subclause_eq_true_iff.mp hsub) hc

/-- Prepending a clause subsumed by an existing clause does not change formula evaluation. -/
theorem CNF.eval_cons_of_subsumed [DecidableEq V] {φ : CNF V} {c d : Clause V} (hd : d ∈ φ)
    (hsub : CNF.Sparsification.subclause d c = true) (σ : V → Bool) :
    CNF.eval σ (c :: φ) = φ.eval σ := by
  rw [CNF.eval_cons]
  cases hφ : φ.eval σ
  · simp
  · have hd_true : d.eval σ = true := (CNF.eval_eq_true_iff σ φ).mp hφ d hd
    have hc_true : c.eval σ = true := Clause.eval_eq_true_of_subclause hsub hd_true
    simp [hc_true]

/-- Removing a clause subsumed by another distinct clause of `φ` preserves evaluation. -/
theorem CNF.eval_filter_ne_of_subsumed [DecidableEq V] {φ : CNF V} {c d : Clause V}
    (hd : d ∈ φ) (hne : d ≠ c) (hsub : CNF.Sparsification.subclause d c = true) (σ : V → Bool) :
    CNF.eval σ (φ.filter (· ≠ c)) = φ.eval σ := by
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  constructor
  · intro h e he
    by_cases hec : e = c
    · subst hec
      have hd' : d ∈ φ.filter (· ≠ e) := List.mem_filter.mpr ⟨hd, by simpa using hne⟩
      exact Clause.eval_eq_true_of_subclause hsub (h d hd')
    · exact h e (List.mem_filter.mpr ⟨he, by simpa using hec⟩)
  · intro h e he
    exact h e (List.mem_filter.mp he).1

/-- Removing a subsumed clause preserves satisfiability. -/
theorem CNF.satisfiable_filter_ne_of_subsumed [DecidableEq V] {φ : CNF V} {c d : Clause V}
    (hd : d ∈ φ) (hne : d ≠ c) (hsub : CNF.Sparsification.subclause d c = true) :
    CNF.Satisfiable (φ.filter (· ≠ c)) ↔ φ.Satisfiable :=
  CNF.satisfiable_iff_of_eval_eq (CNF.eval_filter_ne_of_subsumed hd hne hsub)

/-- Removing a subsumed clause preserves `CNF.modelCountOn`. -/
theorem CNF.modelCountOn_filter_ne_of_subsumed [DecidableEq V] {φ : CNF V} {c d : Clause V}
    (hd : d ∈ φ) (hne : d ≠ c) (hsub : CNF.Sparsification.subclause d c = true)
    (declared : Finset V) :
    CNF.modelCountOn (φ.filter (· ≠ c)) declared = φ.modelCountOn declared :=
  CNF.modelCountOn_eq_of_eval_eq (CNF.eval_filter_ne_of_subsumed hd hne hsub) declared

namespace CNF.Sparsification

open Finset
variable [DecidableEq V]

/-! ### Normalization duplicate-freedom -/

/-- Every clause of `normalize φ` is duplicate-free. -/
theorem nodup_of_mem_normalize {φ : CNF V} {C : Clause V} (hC : C ∈ normalize φ) :
    C.Nodup := by
  have hsub : normalize φ <+ φ.map dedup :=
    (reduce_sublist _).trans (dedupClauses_sublist _)
  obtain ⟨D, _, rfl⟩ := List.mem_map.mp (hsub.subset hC)
  exact nodup_dedup D

/-- Every clause of `countingNormalize φ` is duplicate-free. -/
theorem nodup_of_mem_countingNormalize {φ : CNF V} {C : Clause V}
    (hC : C ∈ countingNormalize φ) : C.Nodup :=
  nodup_of_mem_normalize hC

/-! ### Width-free evaluation, satisfiability, and model-count preservation -/

/-- Literal deduplication preserves clause evaluation. -/
@[simp] theorem eval_dedup (C : Clause V) (σ : V → Bool) :
    Clause.eval σ (dedup C) = C.eval σ := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  simp only [mem_dedup]

/-- Literal deduplication across all clauses preserves formula evaluation. -/
@[simp] theorem eval_map_dedup (φ : CNF V) (σ : V → Bool) :
    CNF.eval σ (φ.map dedup) = φ.eval σ := by
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, eval_dedup]

/-- Clause deduplication preserves formula evaluation. -/
@[simp] theorem eval_dedupClauses (φ : CNF V) (σ : V → Bool) :
    (dedupClauses φ).eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff, ← CNF.sat_toClauseSet_iff, toClauseSet_dedupClauses,
    CNF.sat_toClauseSet_iff]

/-- Subsumption reduction preserves formula evaluation. -/
@[simp] theorem eval_reduce (φ : CNF V) (σ : V → Bool) :
    (reduce φ).eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff, ← CNF.sat_toClauseSet_iff, toClauseSet_reduce,
    ClauseSet.Sparsification.sat_reduce_iff, CNF.sat_toClauseSet_iff]

/-- Normalization (`normalize`) preserves formula evaluation. -/
@[simp] theorem eval_normalize (φ : CNF V) (σ : V → Bool) :
    (normalize φ).eval σ = φ.eval σ := by
  rw [normalize, eval_reduce, eval_dedupClauses, eval_map_dedup]

/-- `modelCountOn` is preserved by literal deduplication. -/
@[simp] theorem modelCountOn_map_dedup (φ : CNF V) (declared : Finset V) :
    CNF.modelCountOn (φ.map dedup) declared = φ.modelCountOn declared :=
  CNF.modelCountOn_eq_of_eval_eq (eval_map_dedup φ) declared

/-- `modelCountOn` is preserved by clause deduplication. -/
@[simp] theorem modelCountOn_dedupClauses (φ : CNF V) (declared : Finset V) :
    (dedupClauses φ).modelCountOn declared = φ.modelCountOn declared :=
  CNF.modelCountOn_eq_of_eval_eq (eval_dedupClauses φ) declared

/-- `modelCountOn` is preserved by subsumption reduction. -/
@[simp] theorem modelCountOn_reduce (φ : CNF V) (declared : Finset V) :
    (reduce φ).modelCountOn declared = φ.modelCountOn declared :=
  CNF.modelCountOn_eq_of_eval_eq (eval_reduce φ) declared

/-- `modelCountOn` is preserved by `normalize`. -/
@[simp] theorem modelCountOn_normalize (φ : CNF V) (declared : Finset V) :
    (normalize φ).modelCountOn declared = φ.modelCountOn declared :=
  CNF.modelCountOn_eq_of_eval_eq (eval_normalize φ) declared

/-- Satisfiability is preserved by `removeTautologies`. -/
theorem satisfiable_removeTautologies_iff (φ : CNF V) :
    (removeTautologies φ).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_iff_of_eval_eq (eval_removeTautologies φ)

/-- Satisfiability is preserved by `dedupClauses`. -/
theorem satisfiable_dedupClauses_iff (φ : CNF V) :
    (dedupClauses φ).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_iff_of_eval_eq (eval_dedupClauses φ)

/-- Satisfiability is preserved by `reduce`. -/
theorem satisfiable_reduce_iff (φ : CNF V) :
    (reduce φ).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_iff_of_eval_eq (eval_reduce φ)

/-- Satisfiability is preserved by `normalize`. -/
theorem satisfiable_normalize_iff (φ : CNF V) :
    (normalize φ).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_iff_of_eval_eq (eval_normalize φ)

/-- Satisfiability is preserved by `countingNormalize`. -/
theorem satisfiable_countingNormalize_iff (φ : CNF V) :
    (countingNormalize φ).Satisfiable ↔ φ.Satisfiable :=
  CNF.satisfiable_iff_of_eval_eq (eval_countingNormalize φ)

/-! ### Variable support and occurring-variable `modelCount` scaling -/

private theorem vars_toFinset_sublist {ψ φ : CNF V} (hsub : ψ <+ φ) :
    ψ.vars.toFinset ⊆ φ.vars.toFinset := by
  intro v hv
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
  exact List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨c, hsub.subset hc, b, hb⟩)

/-- Literal deduplication preserves the occurring variable set. -/
@[simp] theorem vars_toFinset_map_dedup (φ : CNF V) :
    (CNF.vars (φ.map dedup)).toFinset = φ.vars.toFinset := by
  ext v
  simp only [List.mem_toFinset, CNF.mem_vars, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, b, hb⟩
    exact ⟨c, hc, b, mem_dedup.mp hb⟩
  · rintro ⟨c, hc, b, hb⟩
    exact ⟨dedup c, ⟨c, hc, rfl⟩, b, mem_dedup.mpr hb⟩

/-- Clause deduplication preserves the occurring variable set. -/
@[simp] theorem vars_toFinset_dedupClauses (φ : CNF V) :
    (dedupClauses φ).vars.toFinset = φ.vars.toFinset := by
  refine Subset.antisymm (vars_toFinset_sublist (dedupClauses_sublist φ)) ?_
  intro v hv
  obtain ⟨c, hc, b, hb⟩ := CNF.mem_vars.mp (List.mem_toFinset.mp hv)
  have hmem : c.toFinset ∈ (dedupClauses φ).toClauseSet := by
    rw [toClauseSet_dedupClauses]
    exact mem_toClauseSet.mpr ⟨c, hc, rfl⟩
  obtain ⟨d, hd, hdeq⟩ := mem_toClauseSet.mp hmem
  have hbd : (v, b) ∈ d := List.mem_toFinset.mp (hdeq ▸ List.mem_toFinset.mpr hb)
  exact List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨d, hd, b, hbd⟩)

/-- `removeTautologies` never introduces new variables. -/
theorem vars_toFinset_removeTautologies_subset (φ : CNF V) :
    (removeTautologies φ).vars.toFinset ⊆ φ.vars.toFinset :=
  vars_toFinset_sublist (removeTautologies_sublist φ)

/-- `reduce` never introduces new variables. -/
theorem vars_toFinset_reduce_subset (φ : CNF V) :
    (reduce φ).vars.toFinset ⊆ φ.vars.toFinset :=
  vars_toFinset_sublist (reduce_sublist φ)

/-- `normalize` never introduces new variables. -/
theorem vars_toFinset_normalize_subset (φ : CNF V) :
    (normalize φ).vars.toFinset ⊆ φ.vars.toFinset := by
  rw [normalize]
  exact (vars_toFinset_reduce_subset _).trans
    (by rw [vars_toFinset_dedupClauses, vars_toFinset_map_dedup])

/-- `countingNormalize` never introduces new variables. -/
theorem vars_toFinset_countingNormalize_subset (φ : CNF V) :
    (countingNormalize φ).vars.toFinset ⊆ φ.vars.toFinset :=
  (vars_toFinset_normalize_subset _).trans (vars_toFinset_removeTautologies_subset φ)

/-- Literal deduplication preserves `CNF.modelCount` exactly. -/
@[simp] theorem modelCount_map_dedup (φ : CNF V) :
    CNF.modelCount (φ.map dedup) = φ.modelCount := by
  have h1 := CNF.modelCountOn_vars (φ.map dedup)
  rw [← h1, vars_toFinset_map_dedup, modelCountOn_map_dedup, CNF.modelCountOn_vars]

/-- Clause deduplication preserves `CNF.modelCount` exactly. -/
@[simp] theorem modelCount_dedupClauses (φ : CNF V) :
    (dedupClauses φ).modelCount = φ.modelCount := by
  rw [← CNF.modelCountOn_vars, vars_toFinset_dedupClauses, modelCountOn_dedupClauses,
    CNF.modelCountOn_vars]

/-- Tautology elimination scales `CNF.modelCount` by `2` for each variable dropped because all its
clauses were tautological. -/
theorem modelCount_removeTautologies (φ : CNF V) :
    φ.modelCount =
      2 ^ (φ.numVars - (removeTautologies φ).numVars) * (removeTautologies φ).modelCount :=
  CNF.modelCount_eq_two_pow_mul_of_eval_eq
    (vars_toFinset_removeTautologies_subset φ) (eval_removeTautologies φ)

/-- Subsumption reduction scales `CNF.modelCount` by `2` for each variable appearing only in
subsumed clauses. -/
theorem modelCount_reduce (φ : CNF V) :
    φ.modelCount = 2 ^ (φ.numVars - (reduce φ).numVars) * (reduce φ).modelCount :=
  CNF.modelCount_eq_two_pow_mul_of_eval_eq (vars_toFinset_reduce_subset φ) (eval_reduce φ)

/-- `normalize` scales `CNF.modelCount` by `2` for each variable eliminated by subsumption. -/
theorem modelCount_normalize (φ : CNF V) :
    φ.modelCount = 2 ^ (φ.numVars - (normalize φ).numVars) * (normalize φ).modelCount :=
  CNF.modelCount_eq_two_pow_mul_of_eval_eq (vars_toFinset_normalize_subset φ) (eval_normalize φ)

/-- `countingNormalize` scales `CNF.modelCount` by `2` for each variable eliminated by tautology
removal or subsumption. -/
theorem modelCount_countingNormalize (φ : CNF V) :
    φ.modelCount =
      2 ^ (φ.numVars - (countingNormalize φ).numVars) * (countingNormalize φ).modelCount :=
  CNF.modelCount_eq_two_pow_mul_of_eval_eq
    (vars_toFinset_countingNormalize_subset φ) (eval_countingNormalize φ)

/-! ### Size and occurrence bounds after deduplication and normalization -/

/-- `removeTautologies` never increases clause count. -/
theorem length_removeTautologies_le (φ : CNF V) :
    (removeTautologies φ).length ≤ φ.length :=
  (removeTautologies_sublist φ).length_le

/-- `dedupClauses` never increases clause count. -/
theorem length_dedupClauses_le (φ : CNF V) :
    (dedupClauses φ).length ≤ φ.length :=
  (dedupClauses_sublist φ).length_le

/-- `reduce` never increases clause count. -/
theorem length_reduce_le (φ : CNF V) :
    (reduce φ).length ≤ φ.length :=
  (reduce_sublist φ).length_le

/-- `normalize` never increases clause count. -/
theorem length_normalize_le (φ : CNF V) :
    (normalize φ).length ≤ φ.length := by
  rw [normalize]
  exact (length_reduce_le _).trans ((length_dedupClauses_le _).trans (List.length_map _).le)

omit [DecidableEq V] in
private theorem vars_length_sublist_le {ψ φ : CNF V} (hsub : ψ <+ φ) :
    ψ.vars.length ≤ φ.vars.length := by
  rw [CNF.length_vars, CNF.length_vars]
  induction hsub with
  | slnil => exact le_rfl
  | cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.map_cons, List.sum_cons]; omega

/-- Literal deduplication does not increase total literal occurrences (`φ.vars.length`). -/
theorem vars_length_map_dedup_le (φ : CNF V) :
    (CNF.vars (φ.map dedup)).length ≤ φ.vars.length := by
  rw [CNF.length_vars, CNF.length_vars, List.map_map]
  induction φ with
  | nil => exact le_rfl
  | cons c ψ ih =>
    simp only [List.map_cons, Function.comp_apply, List.sum_cons]
    exact Nat.add_le_add (length_dedup_le c) ih

/-- Clause deduplication does not increase total literal occurrences. -/
theorem vars_length_dedupClauses_le (φ : CNF V) :
    (dedupClauses φ).vars.length ≤ φ.vars.length :=
  vars_length_sublist_le (dedupClauses_sublist φ)

/-- Subsumption reduction does not increase total literal occurrences. -/
theorem vars_length_reduce_le (φ : CNF V) :
    (reduce φ).vars.length ≤ φ.vars.length :=
  vars_length_sublist_le (reduce_sublist φ)

/-- Tautology elimination does not increase total literal occurrences. -/
theorem vars_length_removeTautologies_le (φ : CNF V) :
    (removeTautologies φ).vars.length ≤ φ.vars.length :=
  vars_length_sublist_le (removeTautologies_sublist φ)

/-- `normalize` does not increase total literal occurrences. -/
theorem vars_length_normalize_le (φ : CNF V) :
    (normalize φ).vars.length ≤ φ.vars.length := by
  rw [normalize]
  exact (vars_length_reduce_le _).trans
    ((vars_length_dedupClauses_le _).trans (vars_length_map_dedup_le φ))

/-- `countingNormalize` does not increase total literal occurrences. -/
theorem vars_length_countingNormalize_le (φ : CNF V) :
    (countingNormalize φ).vars.length ≤ φ.vars.length :=
  (vars_length_normalize_le _).trans (vars_length_removeTautologies_le φ)

/-- Any sublist of a CNF formula has at most as many clause occurrences of each variable. -/
theorem occurrences_sublist_le {ψ φ : CNF V} (hsub : ψ <+ φ) (v : V) :
    ψ.occurrences v ≤ φ.occurrences v := by
  unfold CNF.occurrences
  exact hsub.countP_le

/-- Literal deduplication preserves the number of clauses mentioning `v`. -/
@[simp] theorem occurrences_map_dedup (φ : CNF V) (v : V) :
    CNF.occurrences (φ.map dedup) v = φ.occurrences v := by
  unfold CNF.occurrences
  rw [List.countP_map]
  congr 1
  funext c
  dsimp only [Function.comp_apply]
  rw [decide_eq_decide]
  simp only [mem_dedup]

/-- Tautology elimination never increases clause occurrences. -/
theorem occurrences_removeTautologies_le (φ : CNF V) (v : V) :
    (removeTautologies φ).occurrences v ≤ φ.occurrences v :=
  occurrences_sublist_le (removeTautologies_sublist φ) v

/-- Clause deduplication never increases clause occurrences. -/
theorem occurrences_dedupClauses_le (φ : CNF V) (v : V) :
    (dedupClauses φ).occurrences v ≤ φ.occurrences v :=
  occurrences_sublist_le (dedupClauses_sublist φ) v

/-- Subsumption reduction never increases clause occurrences. -/
theorem occurrences_reduce_le (φ : CNF V) (v : V) :
    (reduce φ).occurrences v ≤ φ.occurrences v :=
  occurrences_sublist_le (reduce_sublist φ) v

/-- `normalize` never increases clause occurrences. -/
theorem occurrences_normalize_le (φ : CNF V) (v : V) :
    (normalize φ).occurrences v ≤ φ.occurrences v := by
  rw [normalize]
  exact (occurrences_reduce_le _ v).trans
    ((occurrences_dedupClauses_le _ v).trans (occurrences_map_dedup φ v).le)

/-- `countingNormalize` never increases clause occurrences. -/
theorem occurrences_countingNormalize_le (φ : CNF V) (v : V) :
    (countingNormalize φ).occurrences v ≤ φ.occurrences v :=
  (occurrences_normalize_le _ v).trans (occurrences_removeTautologies_le φ v)

end CNF.Sparsification

end Cslib.Logic.PL
