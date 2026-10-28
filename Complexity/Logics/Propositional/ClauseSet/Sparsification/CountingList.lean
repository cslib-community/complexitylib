/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Counting
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.List

/-!
# Counting sparsification on CNF formulas

List-level operations for the counting sparsification refinement of Appendix A.1 [OpenAI2026ETH]:
tautology removal (`removeTautologies`), nontautological normalization (`countingNormalize`),
singleton negated-heart unit clauses (`negatedHeartUnits`), the disjoint counting children
(`countingChild`), and one deterministic counting-sparsification step (`countingNext`).

Initial preprocessing (`countingNormalize φ = normalize (removeTautologies φ)`) removes tautologies,
deduplicates literals and clauses, and reduces to a subset-minimal antichain. At each branching step
on a heavy heart `H` satisfying `deg_c(H) ≥ θ_{c - |H|}` (equation (A.1), p. 44, with the
unnumbered threshold schedule `θ j = M ^ j`), the `false` (A) branch adds `H` while the `true` (B)
branch adds both the petals `petals ψ c H` and the singleton negated-heart units
`negatedHeartUnits H` [OpenAI2026ETH, Appendix A.1, equation (A.2), pp. 44–45]. Applying
`dedupClauses` before `reduce` restores the duplicate-free antichain (`CountingNormalized`) across
steps without re-running tautology removal, while computing the exact clause-set operation
`ClauseSet.Sparsification.countingChild` (`toClauseSet_countingChild`) and conserving the
declared-variable model count (`modelCountOn_countingChild`).

## Main definitions

* `Cslib.Logic.PL.CNF.Sparsification.Clause.isTautology`,
  `Cslib.Logic.PL.CNF.Sparsification.removeTautologies`,
  `Cslib.Logic.PL.CNF.Sparsification.countingNormalize`: tautology removal and normalization.
* `Cslib.Logic.PL.CNF.Sparsification.negatedHeartUnits`,
  `Cslib.Logic.PL.CNF.Sparsification.countingIntro`,
  `Cslib.Logic.PL.CNF.Sparsification.countingChild`,
  `Cslib.Logic.PL.CNF.Sparsification.countingNext`: the list-level counting step.
* `Cslib.Logic.PL.CNF.Sparsification.countingThreshold`: the counting thresholds `θ j = M ^ j`.
* `Cslib.Logic.PL.CNF.Sparsification.Nontautological`,
  `Cslib.Logic.PL.CNF.Sparsification.CountingNormalized`: the nontautological normal form.

## Main results

* `Cslib.Logic.PL.CNF.Sparsification.eval_countingNormalize`,
  `Cslib.Logic.PL.CNF.Sparsification.modelCountOn_countingNormalize`,
  `Cslib.Logic.PL.CNF.Sparsification.countingNormalized_countingNormalize`: nontautological
  normalization preserves evaluation and declared-variable model counts.
* `Cslib.Logic.PL.CNF.Sparsification.toClauseSet_countingChild`,
  `Cslib.Logic.PL.CNF.Sparsification.toClauseSet_countingNext`: the list-level counting children
  compute the clause-set counting children.
* `Cslib.Logic.PL.CNF.Sparsification.modelCountOn_countingChild`,
  `Cslib.Logic.PL.CNF.Sparsification.modelCountOn_countingNext`: additive conservation of
  `CNF.modelCountOn` across both branches.
* `Cslib.Logic.PL.CNF.Sparsification.countingNormalized_countingChild`,
  `Cslib.Logic.PL.CNF.Sparsification.countingNormalized_countingNext`: the counting step preserves
  the nontautological normal form.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Appendix A.1][OpenAI2026ETH]
-/

@[expose] public section

namespace Cslib.Logic.PL.CNF.Sparsification

open Finset ClauseSet.Sparsification
open scoped List

variable {V : Type*} [DecidableEq V]

/-! ### Tautology removal and counting normalization -/

/-- Whether a clause contains both a literal and its negation. -/
def Clause.isTautology (C : Clause V) : Bool :=
  C.any fun l => C.any (· == Std.Sat.Literal.negate l)

/-- Remove tautological clauses from a CNF formula. -/
def removeTautologies (φ : CNF V) : CNF V :=
  φ.filter fun C => !Clause.isTautology C

/-- Bring a formula into nontautological normal form: remove tautological clauses, deduplicate
literals and clauses, and reduce by strict subset containment. -/
def countingNormalize (φ : CNF V) : CNF V :=
  normalize (removeTautologies φ)

/-- Singleton clauses `[-l]` for each literal `l` of a heart `H`. -/
def negatedHeartUnits (H : Clause V) : CNF V :=
  H.map fun l => [Std.Sat.Literal.negate l]

/-- The clauses introduced by a counting-sparsification branch: the heart (`false`) or the petals
together with the singleton negated-heart units (`true`). -/
def countingIntro (ψ : CNF V) (c : ℕ) (H : Clause V) (b : Bool) : CNF V :=
  if b then petals ψ c H ++ negatedHeartUnits H else [H]

/-- A counting child of a branching node: append the introduced clauses, deduplicate clauses with
identical literal sets, and reduce by strict subset containment. -/
def countingChild (ψ : CNF V) (c : ℕ) (H : Clause V) (b : Bool) : CNF V :=
  reduce (dedupClauses (ψ ++ countingIntro ψ c H b))

/-- One deterministic counting-sparsification step using the computed choice `choice θ k ψ`. -/
def countingNext (θ : ℕ → ℕ) (k : ℕ) (ψ : CNF V) (b : Bool) : CNF V :=
  countingChild ψ (choice θ k ψ).1 (choice θ k ψ).2 b

/-- The counting-sparsification threshold schedule `θ j = M ^ j` (defined on p. 44 of
[OpenAI2026ETH, Appendix A.1] for `0 ≤ j < k`, extended here to a total function on `ℕ`, and used
in the heavy-heart branching inequality `deg_c(H) ≥ θ_{c - |H|}` of equation (A.1)). -/
def countingThreshold (M j : ℕ) : ℕ := M ^ j

/-- For `1 ≤ M`, every counting threshold is positive. -/
theorem one_le_countingThreshold {M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    1 ≤ countingThreshold M j :=
  Nat.one_le_pow j M hM

/-! ### Nontautological normal form -/

/-- A CNF formula is *nontautological* if no clause contains both a literal and its negation. -/
def Nontautological (ψ : CNF V) : Prop :=
  ∀ C ∈ ψ, ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C

/-- The normal form for list-level counting sparsification at width `k`: `Normalized k ψ` together
with `Nontautological ψ`. -/
structure CountingNormalized (k : ℕ) (ψ : CNF V) : Prop extends Normalized k ψ where
  nontautological : Nontautological ψ

theorem Clause.isTautology_eq_true_iff {C : Clause V} :
    Clause.isTautology C = true ↔ ∃ l ∈ C, Std.Sat.Literal.negate l ∈ C := by
  simp [Clause.isTautology]

theorem Clause.isTautology_eq_false_iff {C : Clause V} :
    Clause.isTautology C = false ↔ ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
  rw [← Bool.not_eq_true, Clause.isTautology_eq_true_iff]
  push Not
  rfl

/-- Any tautological clause evaluates to `true` under every assignment. -/
theorem eval_eq_true_of_isTautology {C : Clause V} (h : Clause.isTautology C = true)
    (σ : V → Bool) : C.eval σ = true := by
  obtain ⟨⟨v, b⟩, hl, hneg⟩ := Clause.isTautology_eq_true_iff.mp h
  rw [Clause.eval_eq_true_iff]
  by_cases hσ : σ v = b
  · exact ⟨(v, b), hl, hσ⟩
  · refine ⟨Std.Sat.Literal.negate (v, b), hneg, ?_⟩
    cases b <;> cases hσ' : σ v <;> simp_all [Std.Sat.Literal.negate]

/-- `removeTautologies φ` is a sublist of `φ`. -/
theorem removeTautologies_sublist (φ : CNF V) : removeTautologies φ <+ φ :=
  List.filter_sublist

/-- Removing tautological clauses preserves evaluation under every assignment. -/
@[simp]
theorem eval_removeTautologies (φ : CNF V) (σ : V → Bool) :
    (removeTautologies φ).eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff, CNF.eval_eq_true_iff, CNF.eval_eq_true_iff]
  constructor
  · intro h C hC
    rcases Bool.eq_false_or_eq_true (Clause.isTautology C) with htrue | hfalse
    · exact eval_eq_true_of_isTautology htrue σ
    · exact h C (List.mem_filter.mpr ⟨hC, by simp [hfalse]⟩)
  · intro h C hC
    exact h C (List.mem_filter.mp hC).1

/-- Removing tautological clauses preserves the declared-variable model count. -/
@[simp]
theorem modelCountOn_removeTautologies (φ : CNF V) (declared : Finset V) :
    (removeTautologies φ).modelCountOn declared = φ.modelCountOn declared := by
  simp only [CNF.modelCountOn, eval_removeTautologies]

/-- `removeTautologies φ` is nontautological. -/
theorem nontautological_removeTautologies (φ : CNF V) :
    Nontautological (removeTautologies φ) := by
  intro C hC
  have h := (List.mem_filter.mp hC).2
  rw [Bool.not_eq_true'] at h
  exact Clause.isTautology_eq_false_iff.mp h

/-- The clause set of `countingNormalize φ` has the same satisfying assignments as `φ`. -/
theorem sat_toClauseSet_countingNormalize_iff (φ : CNF V) (σ : V → Bool) :
    (countingNormalize φ).toClauseSet.Sat σ ↔ φ.eval σ = true := by
  rw [countingNormalize, sat_toClauseSet_normalize_iff, eval_removeTautologies]

/-- `countingNormalize φ` evaluates identically to `φ` under every assignment. -/
@[simp]
theorem eval_countingNormalize (φ : CNF V) (σ : V → Bool) :
    (countingNormalize φ).eval σ = φ.eval σ := by
  rw [Bool.eq_iff_iff, ← CNF.sat_toClauseSet_iff, sat_toClauseSet_countingNormalize_iff]

/-- `countingNormalize φ` preserves the declared-variable model count. -/
@[simp]
theorem modelCountOn_countingNormalize (φ : CNF V) (declared : Finset V) :
    (countingNormalize φ).modelCountOn declared = φ.modelCountOn declared := by
  simp only [CNF.modelCountOn, eval_countingNormalize]

/-- Every clause of `countingNormalize φ` has the literals of a nontautological clause of `φ`. -/
theorem exists_of_mem_countingNormalize {φ : CNF V} {C : Clause V}
    (hC : C ∈ countingNormalize φ) :
    ∃ D ∈ removeTautologies φ, C.toFinset = D.toFinset := by
  have hsub : countingNormalize φ <+ (removeTautologies φ).map dedup :=
    (reduce_sublist _).trans (dedupClauses_sublist _)
  obtain ⟨D, hD, rfl⟩ := List.mem_map.mp (hsub.subset hC)
  exact ⟨D, hD, toFinset_dedup D⟩

/-- The number of clauses of `countingNormalize φ` is at most that of `φ`. -/
theorem length_countingNormalize_le (φ : CNF V) :
    (countingNormalize φ).length ≤ φ.length :=
  ((reduce_sublist _).trans (dedupClauses_sublist _)).length_le.trans
    ((List.length_map _).le.trans (removeTautologies_sublist φ).length_le)

/-- Every variable occurring in `countingNormalize φ` occurs in `φ`. -/
theorem mem_vars_of_mem_countingNormalize {φ : CNF V} :
    ∀ C ∈ (countingNormalize φ).toClauseSet, ∀ l ∈ C, l.1 ∈ φ.vars.toFinset := by
  intro C hC l hl
  obtain ⟨C', hC', rfl⟩ := mem_toClauseSet.mp hC
  obtain ⟨D, hD, hDeq⟩ := exists_of_mem_countingNormalize hC'
  rw [hDeq, List.mem_toFinset] at hl
  have hDφ := (removeTautologies_sublist φ).subset hD
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨l, List.mem_flatten.mpr ⟨D, hDφ, hl⟩, rfl⟩)

/-- Every formula of width `k` is brought into nontautological normal form by
`countingNormalize`. -/
theorem countingNormalized_countingNormalize {k : ℕ} {φ : CNF V}
    (hφ : ∀ C ∈ φ, C.length ≤ k) : CountingNormalized k (countingNormalize φ) := by
  refine ⟨normalized_normalize fun C hC => hφ C ((removeTautologies_sublist φ).subset hC),
    fun C hC l hl hneg => ?_⟩
  obtain ⟨D, hD, hCD⟩ := exists_of_mem_countingNormalize hC
  have hlD : l ∈ D := List.mem_toFinset.mp (hCD ▸ List.mem_toFinset.mpr hl)
  have hnegD : Std.Sat.Literal.negate l ∈ D :=
    List.mem_toFinset.mp (hCD ▸ List.mem_toFinset.mpr hneg)
  exact nontautological_removeTautologies φ D hD l hlD hnegD

/-! ### Agreement with clause-set counting operations -/

/-- The clause set of `negatedHeartUnits H` is `ClauseSet.Sparsification.negatedHeartUnits`. -/
theorem toClauseSet_negatedHeartUnits (H : Clause V) :
    (negatedHeartUnits H).toClauseSet =
      ClauseSet.Sparsification.negatedHeartUnits H.toFinset := by
  ext C
  simp [negatedHeartUnits, ClauseSet.Sparsification.negatedHeartUnits, CNF.toClauseSet]

/-- The list-level counting children compute the clause-set counting children. -/
theorem toClauseSet_countingChild {ψ : CNF V} (hnd : ∀ C ∈ ψ, C.Nodup) (c : ℕ) (H : Clause V)
    (b : Bool) :
    (countingChild ψ c H b).toClauseSet =
      ClauseSet.Sparsification.countingChild ψ.toClauseSet c H.toFinset b := by
  rw [countingChild, toClauseSet_reduce, toClauseSet_dedupClauses, toClauseSet_append]
  cases b
  · simp [countingIntro, ClauseSet.Sparsification.countingChild,
      ClauseSet.Sparsification.child, ClauseSet.Sparsification.intro, CNF.toClauseSet]
  · simp only [countingIntro, ite_true, toClauseSet_append, toClauseSet_petals hnd,
      toClauseSet_negatedHeartUnits, ClauseSet.Sparsification.countingChild, Finset.union_assoc]

/-- The clause set of `countingNext θ k ψ b` equals the clause-set counting child for the computed
choice. -/
theorem toClauseSet_countingNext {θ : ℕ → ℕ} {k : ℕ} {ψ : CNF V} (h : Normalized k ψ) (b : Bool) :
    (countingNext θ k ψ b).toClauseSet = ClauseSet.Sparsification.countingChild ψ.toClauseSet
      (choice θ k ψ).1 (choice θ k ψ).2.toFinset b :=
  toClauseSet_countingChild h.nodup _ _ b

/-- **Additive model-count conservation for `countingChild`.** On any formula `ψ` without repeated
literals in its clauses, the declared-variable model count equals the sum of the counts of its two
counting children. -/
theorem modelCountOn_countingChild {ψ : CNF V} (hnd : ∀ C ∈ ψ, C.Nodup) (c : ℕ) (H : Clause V)
    (declared : Finset V) :
    ψ.modelCountOn declared =
      (countingChild ψ c H false).modelCountOn declared +
      (countingChild ψ c H true).modelCountOn declared := by
  rw [← modelCountOn_toCNF_toClauseSet ψ,
    ← modelCountOn_toCNF_toClauseSet (countingChild ψ c H false),
    ← modelCountOn_toCNF_toClauseSet (countingChild ψ c H true),
    toClauseSet_countingChild hnd c H false,
    toClauseSet_countingChild hnd c H true]
  exact ClauseSet.Sparsification.modelCountOn_countingChild ψ.toClauseSet c H.toFinset declared

/-- **Additive model-count conservation for `countingNext`.** On any `k`-normalized formula `ψ`,
one deterministic counting-sparsification step splits the declared-variable model count additively
across its `false` and `true` branches. -/
theorem modelCountOn_countingNext {θ : ℕ → ℕ} {k : ℕ} {ψ : CNF V} (h : Normalized k ψ)
    (declared : Finset V) :
    ψ.modelCountOn declared =
      (countingNext θ k ψ false).modelCountOn declared +
      (countingNext θ k ψ true).modelCountOn declared :=
  modelCountOn_countingChild h.nodup _ _ declared

/-! ### Preservation of normal form under the counting step -/

omit [DecidableEq V] in
private theorem literal_negate_ne_self (l : Literal V) : Std.Sat.Literal.negate l ≠ l := by
  rcases l with ⟨v, b⟩
  cases b <;> simp [Std.Sat.Literal.negate]

/-- The counting children preserve `CountingNormalized k` whenever `1 ≤ k` and the heart `H` is a
duplicate-free nontautological clause of width at most `k`. -/
theorem countingNormalized_countingChild {k : ℕ} {ψ : CNF V} (hk : 1 ≤ k)
    (h : CountingNormalized k ψ) {c : ℕ} {H : Clause V} (hH_nodup : H.Nodup)
    (hH_len : H.length ≤ k) (hH_nontaut : ∀ l ∈ H, Std.Sat.Literal.negate l ∉ H) (b : Bool) :
    CountingNormalized k (countingChild ψ c H b) := by
  have hsub : countingChild ψ c H b <+ ψ ++ countingIntro ψ c H b :=
    (reduce_sublist _).trans (dedupClauses_sublist _)
  have hintro : ∀ C ∈ countingIntro ψ c H b,
      C.Nodup ∧ C.length ≤ k ∧ ∀ l ∈ C, Std.Sat.Literal.negate l ∉ C := by
    intro C hC
    cases b
    · simp only [countingIntro, Bool.false_eq_true, ite_false, List.mem_singleton] at hC
      subst hC
      exact ⟨hH_nodup, hH_len, hH_nontaut⟩
    · simp only [countingIntro, ite_true, List.mem_append, petals, negatedHeartUnits,
        List.mem_map] at hC
      rcases hC with ⟨D, hD, rfl⟩ | ⟨l₀, _, rfl⟩
      · have hDψ : D ∈ ψ := List.filter_sublist.subset hD
        refine ⟨(h.nodup D hDψ).filter _, ?_, fun l hl hneg => ?_⟩
        · exact (List.length_filter_le _ D).trans (h.length_le D hDψ)
        · exact h.nontautological D hDψ l (List.mem_filter.mp hl).1 (List.mem_filter.mp hneg).1
      · refine ⟨List.nodup_singleton _, by simpa using hk, fun l hl hneg => ?_⟩
        rw [List.mem_singleton] at hl hneg
        subst hl
        exact literal_negate_ne_self _ hneg
  refine ⟨⟨fun C hC => ?_, fun C hC => ?_, ?_, ?_⟩, fun C hC => ?_⟩
  · rcases List.mem_append.mp (hsub.subset hC) with hC | hC
    · exact h.nodup C hC
    · exact (hintro C hC).1
  · rcases List.mem_append.mp (hsub.subset hC) with hC | hC
    · exact h.length_le C hC
    · exact (hintro C hC).2.1
  · exact ((reduce_sublist _).map _).nodup (nodup_toFinset_dedupClauses _)
  · rw [countingChild, toClauseSet_reduce]
    exact reduced_reduce _
  · rcases List.mem_append.mp (hsub.subset hC) with hC | hC
    · exact h.nontautological C hC
    · exact (hintro C hC).2.2

private theorem choice_snd_sublist_or_nil (θ : ℕ → ℕ) (k : ℕ) (ψ : CNF V) :
    (choice θ k ψ).2 = [] ∨ ∃ C ∈ ψ, (choice θ k ψ).2 <+ C := by
  unfold choice
  rcases hhead : ((List.range ((k + 1) * (k + 1) + 1)).flatMap fun r =>
      ((candidates k ψ).filter (heavy θ ψ)).filter fun x => rank k x == r).head? with _ | x
  · exact Or.inl rfl
  · refine Or.inr ?_
    have hx := List.mem_of_mem_head? hhead
    obtain ⟨r, -, hxr⟩ := List.mem_flatMap.mp hx
    have hxcand := (List.mem_filter.mp (List.mem_filter.mp hxr).1).1
    obtain ⟨C, hC, hxH⟩ := List.mem_flatMap.mp hxcand
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hxH
    exact ⟨C, hC, mem_hearts hH⟩

/-- **One counting-sparsification step preserves `CountingNormalized k`.** -/
theorem countingNormalized_countingNext (θ : ℕ → ℕ) {k : ℕ} (hk : 1 ≤ k) {ψ : CNF V}
    (h : CountingNormalized k ψ) (b : Bool) :
    CountingNormalized k (countingNext θ k ψ b) := by
  rcases choice_snd_sublist_or_nil θ k ψ with hnil | ⟨C, hC, hsub⟩
  · refine countingNormalized_countingChild hk h ?_ ?_ ?_ b <;> simp [hnil]
  · refine countingNormalized_countingChild hk h (hsub.nodup (h.nodup C hC))
      (hsub.length_le.trans (h.length_le C hC))
      (fun l hl hneg => h.nontautological C hC l (hsub.subset hl) (hsub.subset hneg)) b

/-- Every literal occurring in `countingChild ψ c H b` occurs in `ψ` or has its variable in `H`. -/
theorem support_countingChild {ψ : CNF V} {c : ℕ} {H : Clause V} {declared : Finset V}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) (hH : ∀ l ∈ H, l.1 ∈ declared) (b : Bool) :
    ∀ C ∈ countingChild ψ c H b, ∀ l ∈ C, l.1 ∈ declared := by
  have hsub : countingChild ψ c H b <+ ψ ++ countingIntro ψ c H b :=
    (reduce_sublist _).trans (dedupClauses_sublist _)
  intro C hC l hl
  rcases List.mem_append.mp (hsub.subset hC) with hC | hC
  · exact hψ C hC l hl
  · cases b
    · simp only [countingIntro, Bool.false_eq_true, ite_false, List.mem_singleton] at hC
      subst hC
      exact hH l hl
    · simp only [countingIntro, ite_true, List.mem_append, petals, negatedHeartUnits,
        List.mem_map] at hC
      rcases hC with ⟨D, hD, rfl⟩ | ⟨l₀, hl₀, rfl⟩
      · exact hψ D (List.filter_sublist.subset hD) l (List.mem_filter.mp hl).1
      · rw [List.mem_singleton] at hl
        subst hl
        exact hH l₀ hl₀

/-- Every literal occurring in `countingNext θ k ψ b` has its variable in `declared` whenever `ψ`
does. -/
theorem support_countingNext (θ : ℕ → ℕ) (k : ℕ) {ψ : CNF V} {declared : Finset V}
    (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared) (b : Bool) :
    ∀ C ∈ countingNext θ k ψ b, ∀ l ∈ C, l.1 ∈ declared := by
  refine support_countingChild hψ (fun l hl => ?_) b
  rcases choice_snd_sublist_or_nil θ k ψ with hnil | ⟨C, hC, hsub⟩
  · simp [hnil] at hl
  · exact hψ C hC l (hsub.subset hl)

end Cslib.Logic.PL.CNF.Sparsification
