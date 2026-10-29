/-
Copyright (c) 2026 Anton Kovsharov, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Sparsification.Step
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared

/-!
# Disjoint sparsification branches

The decision branches cover the parent's solutions but need not be disjoint. For counting, the
petal branch also requires every heart literal to be false, using singleton negated literals.
This is the local partition in Appendix A.1, equation (A.2) [OpenAI2026ETH]. We retain the parent's
clauses before reduction: under the selected case this has the same solutions as removing the
flower and replacing it by the heart or petals.

Both counts use the same declared finite variable set, including unused variables. These local
semantic identities require neither a heavy heart nor a nonempty variable type. They do not give
termination, insertion, size or leaf-count bounds for the refined branching procedure.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.negatedHeartUnits`: enforce the falsity of a heart.
* `Cslib.Logic.PL.ClauseSet.Sparsification.countingChild`: the disjoint counting refinement.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.sat_countingChild_false_iff`: the heart case.
* `Cslib.Logic.PL.ClauseSet.Sparsification.sat_countingChild_true_iff`: the complementary case.
* `Cslib.Logic.PL.ClauseSet.Sparsification.modelCountOn_toCNF_toClauseSet`: round-tripping a CNF
  formula through `toClauseSet` and `toCNF` preserves `modelCountOn`.
* `Cslib.Logic.PL.ClauseSet.Sparsification.modelCountOn_countingChild`: the additive count identity.
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

variable {V : Type*} [DecidableEq V]

/-- Singleton clauses requiring each literal of `H` to be false. -/
def negatedHeartUnits (H : Finset (Literal V)) : ClauseSet V :=
  H.image fun l => {Std.Sat.Literal.negate l}

/-- The heart branch is unchanged; the petal branch additionally falsifies every heart literal.
Reduction removes redundant clauses without changing the solutions. -/
def countingChild (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : Bool → ClauseSet V
  | false => child ψ c H false
  | true => reduce (ψ ∪ petals ψ c H ∪ negatedHeartUnits H)

private theorem sat_union_iff (ψ χ : ClauseSet V) (x : V → Bool) :
    (ψ ∪ χ).Sat x ↔ ψ.Sat x ∧ χ.Sat x := by
  constructor
  · exact fun h => ⟨fun C hC => h C (Finset.mem_union_left _ hC),
      fun C hC => h C (Finset.mem_union_right _ hC)⟩
  · rintro ⟨hψ, hχ⟩ C hC
    exact (Finset.mem_union.mp hC).elim (hψ C) (hχ C)

/-- The negated units express exactly the failure of the heart clause. -/
theorem sat_negatedHeartUnits_iff (H : Finset (Literal V)) (x : V → Bool) :
    (negatedHeartUnits H).Sat x ↔ ¬ ∃ l ∈ H, x l.1 = l.2 := by
  have hbool (a b : Bool) : a = !b ↔ a ≠ b := by cases a <;> cases b <;> decide
  simp only [negatedHeartUnits, ClauseSet.Sat, Finset.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, Finset.mem_singleton,
    exists_eq_left, Std.Sat.Literal.negate, hbool, not_exists, not_and]

/-- The heart child consists exactly of parent solutions satisfying the heart. -/
theorem sat_countingChild_false_iff (ψ : ClauseSet V) (c : ℕ)
    (H : Finset (Literal V)) (x : V → Bool) :
    (countingChild ψ c H false).Sat x ↔ ψ.Sat x ∧ ∃ l ∈ H, x l.1 = l.2 := by
  rw [countingChild, child, sat_reduce_iff, sat_union_iff]
  simp [intro, ClauseSet.Sat]

/-- The petal child consists exactly of parent solutions falsifying the heart. -/
theorem sat_countingChild_true_iff (ψ : ClauseSet V) (c : ℕ)
    (H : Finset (Literal V)) (x : V → Bool) :
    (countingChild ψ c H true).Sat x ↔ ψ.Sat x ∧ ¬ ∃ l ∈ H, x l.1 = l.2 := by
  rw [countingChild, sat_reduce_iff, sat_union_iff, sat_union_iff,
    sat_negatedHeartUnits_iff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hψ, hH⟩
    refine ⟨⟨hψ, ?_⟩, hH⟩
    intro C hC
    obtain ⟨D, hD, rfl⟩ := mem_petals.mp hC
    obtain ⟨l, hl, htrue⟩ := hψ D (flower_subset ψ c H hD)
    exact ⟨l, Finset.mem_sdiff.mpr ⟨hl, fun hlH => hH ⟨l, hlH, htrue⟩⟩, htrue⟩

/-- Every parent solution satisfies exactly one child, even for an empty or contradictory heart.
-/
theorem sat_countingChild_partition (ψ : ClauseSet V) (c : ℕ)
    (H : Finset (Literal V)) (x : V → Bool) :
    ψ.Sat x ↔ ((countingChild ψ c H false).Sat x ∨
      (countingChild ψ c H true).Sat x) := by
  rw [sat_countingChild_false_iff, sat_countingChild_true_iff]
  constructor
  · intro hψ
    by_cases hH : ∃ l ∈ H, x l.1 = l.2
    · exact Or.inl ⟨hψ, hH⟩
    · exact Or.inr ⟨hψ, hH⟩
  · rintro (h | h) <;> exact h.1

/-- No assignment satisfies both counting children. -/
theorem not_sat_both_countingChild (ψ : ClauseSet V) (c : ℕ)
    (H : Finset (Literal V)) (x : V → Bool) :
    ¬ ((countingChild ψ c H false).Sat x ∧ (countingChild ψ c H true).Sat x) := by
  rw [sat_countingChild_false_iff, sat_countingChild_true_iff]
  exact fun h => h.2.2 h.1.2

/-- The parent and heart support hypotheses preserve the declared-variable invariant in both
children. This is separate from the unconditional semantic partition. -/
theorem support_countingChild (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V))
    (declared : Finset V) (hψ : ∀ C ∈ ψ, ∀ l ∈ C, l.1 ∈ declared)
    (hH : ∀ l ∈ H, l.1 ∈ declared) (b : Bool) :
    ∀ C ∈ countingChild ψ c H b, ∀ l ∈ C, l.1 ∈ declared := by
  intro C hC l hl
  cases b with
  | false =>
    rcases Finset.mem_union.mp (child_subset ψ c H false hC) with hC | hC
    · exact hψ C hC l hl
    · have hCH : C = H := by simpa only [intro, Finset.mem_singleton] using hC
      exact hH l (hCH ▸ hl)
  | true =>
    rcases Finset.mem_union.mp (reduce_subset _ hC) with hC | hC
    · rcases Finset.mem_union.mp hC with hC | hC
      · exact hψ C hC l hl
      · obtain ⟨D, hD, rfl⟩ := mem_petals.mp hC
        exact hψ D (flower_subset ψ c H hD) l (Finset.mem_sdiff.mp hl).1
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
      have hl : l = Std.Sat.Literal.negate a := Finset.mem_singleton.mp hl
      subst l
      exact hH a ha

/-- Counting both children over the same declared variables recovers the parent count.
No support premise is needed for this identity because all three evaluations use the same
extension by `false`. For a declared-input interpretation, support containment is a separate
invariant; unused declared variables must not be discarded between branches. -/
theorem modelCountOn_countingChild (ψ : ClauseSet V) (c : ℕ)
    (H : Finset (Literal V)) (declared : Finset V) :
    ψ.toCNF.modelCountOn declared =
      (countingChild ψ c H false).toCNF.modelCountOn declared +
      (countingChild ψ c H true).toCNF.modelCountOn declared := by
  classical
  let extend (σ : declared → Bool) (v : V) :=
    if h : v ∈ declared then σ ⟨v, h⟩ else false
  let S := Finset.univ.filter fun σ : declared → Bool => ψ.Sat (extend σ)
  let p (σ : declared → Bool) := ∃ l ∈ H, extend σ l.1 = l.2
  have hA : (Finset.univ.filter fun σ : declared → Bool =>
      (countingChild ψ c H false).toCNF.eval (extend σ) = true) = S.filter p := by
    ext σ
    simp [S, p, eval_toCNF_eq_true_iff, sat_countingChild_false_iff]
  have hB : (Finset.univ.filter fun σ : declared → Bool =>
      (countingChild ψ c H true).toCNF.eval (extend σ) = true) =
      S.filter fun σ => ¬ p σ := by
    ext σ
    simp [S, p, eval_toCNF_eq_true_iff, sat_countingChild_true_iff]
  have hparent : ψ.toCNF.modelCountOn declared = S.card := by
    unfold CNF.modelCountOn
    congr 1
    ext σ
    simp [S, extend, eval_toCNF_eq_true_iff]
  rw [hparent]
  unfold CNF.modelCountOn
  change S.card = (Finset.univ.filter fun σ =>
    (countingChild ψ c H false).toCNF.eval (extend σ) = true).card +
    (Finset.univ.filter fun σ =>
      (countingChild ψ c H true).toCNF.eval (extend σ) = true).card
  rw [hA, hB]
  exact (Finset.card_filter_add_card_filter_not p).symm

/-- Round-tripping `φ : CNF V` through `toClauseSet` and `toCNF` preserves `modelCountOn` on any
declared variable set. -/
@[simp]
theorem modelCountOn_toCNF_toClauseSet (φ : CNF V) (declared : Finset V) :
    φ.toClauseSet.toCNF.modelCountOn declared = φ.modelCountOn declared := by
  simp only [CNF.modelCountOn]
  congr 1
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ClauseSet.eval_toCNF_eq_true_iff,
    CNF.sat_toClauseSet_iff]

end Cslib.Logic.PL.ClauseSet.Sparsification
