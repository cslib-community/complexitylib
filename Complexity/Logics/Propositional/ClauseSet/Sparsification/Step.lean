/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.ClauseSet.Basic
public import Mathlib.Order.Antichain
public import Mathlib.Order.Minimal
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Tactic.Positivity

/-!
# Sparsification -- the branching step

The sparsification procedure of Impagliazzo, Paturi and Zane [ImpagliazzoPaturiZane2001], in the
presentation of Calabro, Impagliazzo and Paturi [CalabroImpagliazzoPaturi2006] and of Calabro's
thesis [Calabro, Chapter 5][Calabro2009].

Clause sets are kept *reduced*: no clause strictly contains another (`reduce`). For thresholds
`θ`, a set `H` of `h ≥ 1` literals is a *heavy heart* for clause size `c > h` when at least
`θ (c - h)` clauses of size `c` contain it (`Heavy`); those clauses form its *flower*. A clause
set without heavy hearts is *sparse*. Otherwise the procedure picks a heavy heart with `c` as
small as possible and then `h` as large as possible (`Choice`), and branches: either `H` is
satisfied (add the clause `H`, the *heart branch*), or it is not, and then every *petal* `C \ H`
of the flower is satisfied (add the petals, the *petal branch*). Both branches are reduced again.

This file proves the local facts: the two branches cover the solutions and only lose solutions
of the original clause set, they preserve the width and reducedness, and the potential
`∑_{C ∈ ψ} 2 ^ |C|` strictly decreases, so the procedure terminates.

## Main definitions

* `Cslib.Logic.PL.ClauseSet.Sparsification.reduce`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Reduced`: remove the clauses containing others, and
  reduced clause sets.
* `Cslib.Logic.PL.ClauseSet.Sparsification.flower`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.petals`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Heavy`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Sparse`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.Choice`: flowers, petals, heavy hearts, sparse clause
  sets and valid choices.
* `Cslib.Logic.PL.ClauseSet.Sparsification.intro`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.child`: introduced clauses and the children of a
  branching node.
* `Cslib.Logic.PL.ClauseSet.Sparsification.potential`: the potential `∑_{C ∈ ψ} 2 ^ |C|`.

## Main results

* `Cslib.Logic.PL.ClauseSet.Sparsification.sat_child_of_sat`,
  `Cslib.Logic.PL.ClauseSet.Sparsification.sat_of_sat_child`: the branches cover the solutions
  and only lose solutions of the parent.
* `Cslib.Logic.PL.ClauseSet.Sparsification.potential_child_lt`: termination.

## References

* [R. Impagliazzo, R. Paturi, F. Zane, *Which problems have strongly exponential
  complexity?*][ImpagliazzoPaturiZane2001]
* [C. Calabro, R. Impagliazzo, R. Paturi, *A duality between clause width and clause density for
  SAT*][CalabroImpagliazzoPaturi2006]
* [C. Calabro, *The Exponential Complexity of Satisfiability Problems*][Calabro2009]
-/

@[expose] public section

namespace Cslib.Logic.PL.ClauseSet.Sparsification

open Finset

variable {V : Type*} [DecidableEq V]

/-- Remove every clause that strictly contains another clause, keeping the minimal clauses
(`mem_reduce_iff_minimal`). -/
def reduce (ψ : ClauseSet V) : ClauseSet V :=
  ψ.filter fun C => ∀ D ∈ ψ, ¬ D ⊂ C

/-- No clause strictly contains another: the clauses form an antichain
(`reduced_iff_isAntichain`). -/
def Reduced (ψ : ClauseSet V) : Prop :=
  ∀ C ∈ ψ, ∀ D ∈ ψ, ¬ D ⊂ C

/-- The *flower* of `H` at clause size `c`: the clauses of size `c` that contain `H`. -/
def flower (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : ClauseSet V :=
  ψ.filter fun C => C.card = c ∧ H ⊆ C

/-- `H` is a *heavy heart* for clause size `c`: `1 ≤ |H| < c` and at least `θ (c - |H|)`
clauses of size `c` contain `H`. -/
def Heavy (θ : ℕ → ℕ) (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : Prop :=
  1 ≤ H.card ∧ H.card < c ∧ θ (c - H.card) ≤ (flower ψ c H).card

/-- A clause set is *sparse* for the thresholds `θ` when it has no heavy heart. -/
def Sparse (θ : ℕ → ℕ) (ψ : ClauseSet V) : Prop :=
  ∀ c H, ¬ Heavy θ ψ c H

/-- A valid branching choice: a heavy heart with the smallest clause size, and among those the
largest heart. -/
def Choice (θ : ℕ → ℕ) (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : Prop :=
  Heavy θ ψ c H ∧ (∀ c' H', Heavy θ ψ c' H' → c ≤ c') ∧
    ∀ H', Heavy θ ψ c H' → H'.card ≤ H.card

/-- The petals `C \ H` of the flower of `H`. -/
def petals (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : ClauseSet V :=
  (flower ψ c H).image (· \ H)

/-- The clauses a branch introduces: the heart (`false`) or the petals (`true`). -/
def intro (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) : Bool → ClauseSet V
  | false => {H}
  | true => petals ψ c H

/-- A child of a branching node: add the introduced clauses and reduce. -/
def child (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) (b : Bool) :
    ClauseSet V :=
  reduce (ψ ∪ intro ψ c H b)

/-- The potential `∑_{C ∈ ψ} 2 ^ |C|`, which every branching step decreases. -/
def potential (ψ : ClauseSet V) : ℕ :=
  ∑ C ∈ ψ, 2 ^ C.card

/-! ### Reduction -/

/-- A clause `C` belongs to `reduce ψ` if and only if `C ∈ ψ` and no clause of `ψ` is a strict
subset of `C`. -/
theorem mem_reduce {ψ : ClauseSet V} {C : Finset (Literal V)} :
    C ∈ reduce ψ ↔ C ∈ ψ ∧ ∀ D ∈ ψ, ¬ D ⊂ C := by
  simp only [reduce, mem_filter]

/-- The reduction keeps the minimal clauses. -/
theorem mem_reduce_iff_minimal {ψ : ClauseSet V} {C : Finset (Literal V)} :
    C ∈ reduce ψ ↔ Minimal (· ∈ ψ) C := by
  rw [mem_reduce, Minimal]
  refine and_congr_right fun _ => ⟨fun h D hD hDC => ?_, fun h D hD hDC => ?_⟩
  · by_contra hCD
    exact h D hD (ssubset_of_subset_not_subset hDC hCD)
  · exact hDC.2 (h hD hDC.1)

omit [DecidableEq V] in
/-- A reduced clause set is an antichain for inclusion. -/
theorem reduced_iff_isAntichain {ψ : ClauseSet V} :
    Reduced ψ ↔ IsAntichain (· ⊆ ·) (ψ : Set (Finset (Literal V))) := by
  refine ⟨fun h C hC D hD hne hCD => h D hD C hC (ssubset_of_subset_of_ne hCD hne), fun h C hC D hD
    hDC => h hD hC (ne_of_ssubset hDC) hDC.subset⟩

/-- `reduce ψ` is a subset of `ψ`. -/
theorem reduce_subset (ψ : ClauseSet V) : reduce ψ ⊆ ψ := fun _ h => (mem_reduce.mp h).1

/-- The reduction `reduce ψ` of any clause set is reduced. -/
theorem reduced_reduce (ψ : ClauseSet V) : Reduced (reduce ψ) := by
  intro C hC D hD hDC
  exact (mem_reduce.mp hC).2 D (reduce_subset ψ hD) hDC

/-- Every clause contains a clause of the reduction. -/
theorem exists_mem_reduce_subset {ψ : ClauseSet V} {C : Finset (Literal V)}
    (hC : C ∈ ψ) : ∃ D ∈ reduce ψ, D ⊆ C := by
  obtain ⟨D, hDC, hD⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ ψ) C hC
  exact ⟨D, mem_reduce_iff_minimal.2 hD, hDC⟩

/-- Reduction does not change the solutions. -/
theorem sat_reduce_iff {ψ : ClauseSet V} {x : V → Bool} : (reduce ψ).Sat x ↔ ψ.Sat x := by
  constructor
  · intro hx C hC
    obtain ⟨D, hD, hDC⟩ := exists_mem_reduce_subset hC
    obtain ⟨l, hl, htrue⟩ := hx D hD
    exact ⟨l, hDC hl, htrue⟩
  · exact fun hx C hC => hx C (reduce_subset ψ hC)

/-- A clause of a reduced set that is not in the reduction of a larger set strictly contains one
of the added clauses. -/
theorem exists_ssubset_of_notMem_reduce {ψ X : ClauseSet V} (hred : Reduced ψ)
    {a : Finset (Literal V)} (ha : a ∈ ψ) (hna : a ∉ reduce (ψ ∪ X)) : ∃ b ∈ X, b ⊂ a := by
  rw [mem_reduce] at hna
  push Not at hna
  obtain ⟨D, hD, hDa⟩ := hna (mem_union_left _ ha)
  rcases mem_union.mp hD with hD | hD
  · exact absurd hDa (hred a ha D hD)
  · exact ⟨D, hD, hDa⟩

/-! ### Flowers, petals and choices -/

/-- A clause `C` belongs to `flower ψ c H` if and only if `C ∈ ψ`, `C.card = c`, and `H ⊆ C`. -/
theorem mem_flower {ψ : ClauseSet V} {c : ℕ} {H C : Finset (Literal V)} :
    C ∈ flower ψ c H ↔ C ∈ ψ ∧ C.card = c ∧ H ⊆ C := mem_filter

/-- `flower ψ c H` is a subset of `ψ`. -/
theorem flower_subset (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) :
    flower ψ c H ⊆ ψ := filter_subset _ _

/-- A clause `p` belongs to `petals ψ c H` if and only if `p = C \ H` for some
`C ∈ flower ψ c H`. -/
theorem mem_petals {ψ : ClauseSet V} {c : ℕ} {H p : Finset (Literal V)} :
    p ∈ petals ψ c H ↔ ∃ C ∈ flower ψ c H, C \ H = p := mem_image

/-- The petal map `C ↦ C \ H` is injective on the flower. -/
theorem card_petals (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) :
    (petals ψ c H).card = (flower ψ c H).card := by
  refine card_image_of_injOn fun C hC C' hC' h => ?_
  have hH : H ⊆ C := (mem_flower.mp hC).2.2
  have hH' : H ⊆ C' := (mem_flower.mp hC').2.2
  rw [← sdiff_union_of_subset hH, ← sdiff_union_of_subset hH', h]

/-- Every petal in `petals ψ c H` has cardinality `c - H.card`. -/
theorem card_of_mem_petals {ψ : ClauseSet V} {c : ℕ} {H p : Finset (Literal V)}
    (hp : p ∈ petals ψ c H) : p.card = c - H.card := by
  obtain ⟨C, hC, rfl⟩ := mem_petals.mp hp
  obtain ⟨-, hcard, hH⟩ := mem_flower.mp hC
  rw [card_sdiff_of_subset hH, hcard]

/-- When all thresholds are at least `1`, the flower of a heavy heart is nonempty. -/
theorem Heavy.flower_nonempty {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) : (flower ψ c H).Nonempty := by
  rw [← card_pos]
  exact lt_of_lt_of_le (hθ _) h.2.2

/-- Every introduced clause is nonempty and smaller than the flower's clause size. -/
theorem card_of_mem_intro {θ : ℕ → ℕ} {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    (h : Heavy θ ψ c H) {b : Bool} {a : Finset (Literal V)} (ha : a ∈ intro ψ c H b) :
    1 ≤ a.card ∧ a.card < c := by
  obtain ⟨h1, hlt, -⟩ := h
  cases b with
  | false =>
    rw [intro, mem_singleton] at ha
    subst ha
    exact ⟨h1, hlt⟩
  | true =>
    rw [card_of_mem_petals ha]
    omega

/-- Every introduced clause is strictly contained in a clause of the flower. -/
theorem exists_flower_ssuperset {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) {b : Bool} {a : Finset (Literal V)}
    (ha : a ∈ intro ψ c H b) : ∃ C ∈ flower ψ c H, a ⊂ C := by
  cases b with
  | false =>
    rw [intro, mem_singleton] at ha
    subst ha
    obtain ⟨C, hC⟩ := h.flower_nonempty hθ
    obtain ⟨-, hcard, hH⟩ := mem_flower.mp hC
    exact ⟨C, hC, ssubset_of_subset_of_ne hH fun heq => by
      have := h.2.1; rw [heq, hcard] at this; exact lt_irrefl _ this⟩
  | true =>
    obtain ⟨C, hC, rfl⟩ := mem_petals.mp ha
    obtain ⟨-, -, hH⟩ := mem_flower.mp hC
    refine ⟨C, hC, sdiff_ssubset hH ?_⟩
    rw [← card_pos]
    exact h.1

/-- When all thresholds are at least `1`, the set of clauses `intro ψ c H b` introduced at a heavy
heart is nonempty. -/
theorem intro_nonempty {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) (b : Bool) : (intro ψ c H b).Nonempty := by
  cases b with
  | false => exact singleton_nonempty H
  | true =>
    rw [intro, petals]
    exact (h.flower_nonempty hθ).image _

/-! ### The children of a branching node -/

/-- Every child `child ψ c H b` of a branching step is reduced. -/
theorem reduced_child (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) (b : Bool) :
    Reduced (child ψ c H b) := reduced_reduce _

/-- Every child `child ψ c H b` is contained in `ψ ∪ intro ψ c H b`. -/
theorem child_subset (ψ : ClauseSet V) (c : ℕ) (H : Finset (Literal V)) (b : Bool) :
    child ψ c H b ⊆ ψ ∪ intro ψ c H b := reduce_subset _

/-- A child only loses solutions: its solutions are solutions of the parent. -/
theorem sat_of_sat_child {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)} {b : Bool}
    {x : V → Bool} (hx : (child ψ c H b).Sat x) : ψ.Sat x :=
  fun C hC => sat_reduce_iff.mp hx C (mem_union_left _ hC)

/-- **The branches cover.** A solution of the parent satisfying the heart is a solution of the
heart child; a solution falsifying it is a solution of the petal child. -/
theorem sat_child_of_sat {ψ : ClauseSet V} {c : ℕ} {H : Finset (Literal V)}
    {x : V → Bool} (hx : ψ.Sat x) :
    child ψ c H (decide ¬ ∃ l ∈ H, x l.1 = l.2) |>.Sat x := by
  rw [child, sat_reduce_iff]
  intro C hC
  rcases mem_union.mp hC with hC | hC
  · exact hx C hC
  · by_cases hH : ∃ l ∈ H, x l.1 = l.2
    · simp only [hH, not_true_eq_false, decide_false, intro, mem_singleton] at hC
      exact hC ▸ hH
    · simp only [hH, not_false_eq_true, decide_true, intro] at hC
      obtain ⟨D, hD, rfl⟩ := mem_petals.mp hC
      obtain ⟨l, hl, htrue⟩ := hx D (flower_subset ψ c H hD)
      refine ⟨l, mem_sdiff.mpr ⟨hl, fun hlH => hH ⟨l, hlH, htrue⟩⟩, htrue⟩

/-- Children keep the width. -/
theorem card_le_of_mem_child {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V} {c k : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) (hk : ∀ C ∈ ψ, C.card ≤ k) {b : Bool}
    {C : Finset (Literal V)} (hC : C ∈ child ψ c H b) : C.card ≤ k := by
  rcases mem_union.mp (child_subset ψ c H b hC) with hC | hC
  · exact hk C hC
  · obtain ⟨D, hD, hCD⟩ := exists_flower_ssuperset hθ h hC
    exact (card_le_card hCD.subset).trans (hk D (flower_subset ψ c H hD))

/-- The flower disappears from both children. -/
private theorem disjoint_flower_child {θ : ℕ → ℕ} {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) (b : Bool) :
    Disjoint (flower ψ c H) (child ψ c H b) := by
  rw [Finset.disjoint_left]
  intro C hC hCchild
  obtain ⟨-, hcard, hH⟩ := mem_flower.mp hC
  have hmin := (mem_reduce.mp hCchild).2
  cases b with
  | false =>
    refine hmin H (mem_union_right _ (by simp [intro])) (ssubset_of_subset_of_ne hH ?_)
    intro heq
    have := h.2.1
    rw [heq, hcard] at this
    exact lt_irrefl _ this
  | true =>
    refine hmin (C \ H) (mem_union_right _ (mem_petals.mpr ⟨C, hC, rfl⟩)) (sdiff_ssubset hH ?_)
    rw [← card_pos]
    exact h.1

/-- **Termination.** Each branching step strictly decreases the potential. -/
theorem potential_child_lt {θ : ℕ → ℕ} (hθ : ∀ j, 1 ≤ θ j) {ψ : ClauseSet V} {c : ℕ}
    {H : Finset (Literal V)} (h : Heavy θ ψ c H) (b : Bool) :
    potential (child ψ c H b) < potential ψ := by
  set F := flower ψ c H
  have hsub : child ψ c H b ⊆ (ψ \ F) ∪ intro ψ c H b := by
    intro C hC
    rcases mem_union.mp (child_subset ψ c H b hC) with hCψ | hCX
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hCψ, fun hF =>
        disjoint_left.mp (disjoint_flower_child h b) hF hC⟩)
    · exact mem_union_right _ hCX
  have hFsplit : potential ψ = potential (ψ \ F) + potential F := by
    unfold potential
    rw [← sum_sdiff (flower_subset ψ c H)]
  have hF : potential F = F.card * 2 ^ c := by
    unfold potential
    rw [sum_congr rfl fun C hC => by rw [(mem_flower.mp hC).2.1], sum_const, smul_eq_mul]
  have hFpos : 0 < F.card := card_pos.mpr (h.flower_nonempty hθ)
  have hX : potential (intro ψ c H b) < F.card * 2 ^ c := by
    cases b with
    | false =>
      unfold potential
      rw [intro, sum_singleton]
      calc 2 ^ H.card < 2 ^ c := Nat.pow_lt_pow_right (by norm_num) h.2.1
        _ ≤ F.card * 2 ^ c := Nat.le_mul_of_pos_left _ hFpos
    | true =>
      unfold potential
      calc ∑ C ∈ intro ψ c H true, 2 ^ C.card
          = ∑ _C ∈ petals ψ c H, 2 ^ (c - H.card) :=
            sum_congr rfl fun C hC => by rw [card_of_mem_petals hC]
        _ = F.card * 2 ^ (c - H.card) := by rw [sum_const, card_petals, smul_eq_mul]
        _ < F.card * 2 ^ c :=
            Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num)
              (by have := h.1; have := h.2.1; omega)) hFpos
  calc potential (child ψ c H b) ≤ potential ((ψ \ F) ∪ intro ψ c H b) :=
        sum_le_sum_of_subset hsub
    _ ≤ potential (ψ \ F) + potential (intro ψ c H b) := by
        unfold potential
        have := sum_union_inter (s₁ := ψ \ F) (s₂ := intro ψ c H b)
          (f := fun C : Finset (Literal V) => 2 ^ C.card)
        omega
    _ < potential (ψ \ F) + potential F := by rw [hF]; exact Nat.add_lt_add_left hX _
    _ = potential ψ := hFsplit.symm

end Cslib.Logic.PL.ClauseSet.Sparsification
