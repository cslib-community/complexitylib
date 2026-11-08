/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.VanEmdeBoas.Basic
import Mathlib.Tactic.Linarith

/-!
# Strict van Emde Boas predecessor

This module defines and verifies strict predecessor lookup on recursive minimum-excluded
van Emde Boas trees ([CLRS2009], Section 20.3, p. 552). [Demaine2015VanEmdeBoas] gives only
`Successor` (p. 4), which this mirrors. The algorithm returns the greatest represented key
strictly less than its query, or `none` when every represented key is at least the query.
Queries need not lie inside `[0, universeSize d)`.

Because each internal node stores its minimum `m` outside its clusters, `predecessor` is slightly
asymmetric with `successor`: when `m < x ≤ M` and neither `x`'s cluster nor any earlier nonempty
cluster recorded in `summary` contains a key below `x`, `predecessor` falls back to returning
`some m` in `O(1)`. These are mathematical correctness statements, without a machine cost claim.

## Main definitions

* `Tree.predecessor`: strict predecessor query on `Tree d`.

## Main results

* `Tree.predecessor_empty`: predecessor lookup on `empty d` returns `none`.
* `Tree.predecessor_spec`: the successful and unsuccessful result specifications.
* `Tree.predecessor_eq_some_iff`: success is equivalent to being the greatest smaller stored key.
* `Tree.predecessor_eq_none_iff`: failure is equivalent to having no smaller stored key.
* `Tree.predecessor_isSome_of_gt_min`: a query strictly above the cached minimum always has a
  strict predecessor in `[0, universeSize d)`.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 20.3][CLRS2009]
-/

public section

namespace Cslib.DataStructure.VanEmdeBoas.Tree

/-- The greatest stored key strictly less than the query, or `none` if it does not exist.
The cached cluster minimum chooses between one cluster recursion and one summary recursion;
when no cluster entry precedes `x > m`, the excluded node minimum `m` is returned
([CLRS2009], Section 20.3, p. 552; it mirrors `Successor` in [Demaine2015VanEmdeBoas], p. 4). -/
@[expose] def predecessor : {d : ℕ} → Tree d → ℕ → Option ℕ
  | 0, .leaf b, x => match b with
    | none => none
    | some (m, M) => if M < x then some M else if m < x then some m else none
  | d + 1, .node b s c, x => match b with
    | none => none
    | some (m, M) =>
      if M < x then some M
      else if x ≤ m then none
      else if h : x / universeSize d < universeSize d then
        let i : Fin (universeSize d) := ⟨x / universeSize d, h⟩
        let low := x % universeSize d
        if (c i).minimum.any (· < low) then
          (predecessor (c i) low).map (i.val * universeSize d + ·)
        else
          match predecessor s i.val with
          | some j =>
            if hj : j < universeSize d then
              (c ⟨j, hj⟩).maximum.map (j * universeSize d + ·)
            else none
          | none => some m
      else none

/-- Predecessor lookup on the empty tree at depth `d` always returns `none`. -/
@[simp] theorem predecessor_empty (d x : ℕ) : (empty d).predecessor x = none := by
  cases d <;> rfl

/-- The cached minimum lies below `x` exactly when some represented key does. -/
private theorem Valid.minimum_any_lt_iff {d x : ℕ} {t : Tree d} (ht : t.Valid) :
    t.minimum.any (· < x) = true ↔ ∃ a, t.Contains a ∧ a < x := by
  cases hb : t.bounds with
  | none => simp [minimum, hb, not_contains_of_bounds_none hb]
  | some b =>
    obtain ⟨m, M⟩ := b
    simp only [minimum, hb, Option.map_some, Option.any_some, decide_eq_true_eq]
    exact ⟨fun h => ⟨m, ht.contains_minimum hb, h⟩,
      fun ⟨a, ha, hax⟩ => (ht.min_le_of_contains hb ha).trans_lt hax⟩

/-- A cluster key lies below a query exactly when its cluster is earlier, or it is the same
cluster with a smaller low part. -/
private theorem cluster_key_lt_query_iff {u x j a : ℕ} (hu : 0 < u) (ha : a < u) :
    j * u + a < x ↔ j < x / u ∨ j = x / u ∧ a < x % u := by
  conv_lhs => rw [← Nat.div_add_mod' x u]
  exact cluster_key_lt_iff ha (Nat.mod_lt x hu)

/-- A returned key is the greatest represented key strictly below the query; failure certifies
that every represented key is at least the query. No bound on the query is required. -/
theorem predecessor_spec {d : ℕ} {t : Tree d} (ht : t.Valid) (x : ℕ) :
    match t.predecessor x with
    | some y => t.Contains y ∧ y < x ∧ ∀ z, t.Contains z → z < x → z ≤ y
    | none => ∀ z, t.Contains z → x ≤ z := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none => simp [predecessor, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        have hmM := ht.min_le_of_contains rfl (ht.contains_maximum rfl)
        simp only [predecessor]
        split_ifs <;>
          simp only [contains_leaf_some, forall_eq_or_imp, forall_eq, true_or, or_true,
            true_and] <;>
          omega
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => simp [predecessor, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        have hmin := ht.contains_minimum rfl
        by_cases hM : M < x
        · -- The query is above the cached maximum, which is therefore the answer.
          rw [predecessor, ite_eq_left hM]
          exact ⟨ht.contains_maximum rfl, hM, fun z hz _ => ht.le_max_of_contains rfl hz⟩
        by_cases hm : x ≤ m
        · -- The query is at or below the cached minimum: there is no predecessor.
          rw [predecessor, ite_eq_right hM, ite_eq_left hm]
          exact fun z hz => hm.trans (ht.min_le_of_contains rfl hz)
        -- Otherwise `m < x ≤ M`; split `x` into its cluster `i` and low part.
        have hu := universeSize_pos d
        have hi : x / universeSize d < universeSize d :=
          (Nat.div_lt_iff_lt_mul hu).mpr
            ((Nat.le_of_not_lt hM).trans_lt (ht.contains_lt (ht.contains_maximum rfl)))
        let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
        /- A cluster key lies below `x` iff its cluster is earlier than `i`, or it is in `i`
        itself with a smaller low part. -/
        have hbelow : ∀ j a, (c j).Contains a →
            (j.val * universeSize d + a < x ↔
              j.val < i.val ∨ j = i ∧ a < x % universeSize d) := by
          intro j a ha
          rw [cluster_key_lt_query_iff hu ((ht.cluster j).contains_lt ha), Fin.ext_iff]
        rw [predecessor, ite_eq_right hM, ite_eq_right hm, dite_eq_left hi]
        by_cases hc : (c i).minimum.any (· < x % universeSize d) = true
        · -- Some key of cluster `i` is below the low part: recurse into cluster `i`.
          rw [ite_eq_left hc]
          have hp := ih (ht.cluster i) (x % universeSize d)
          cases hpred : (c i).predecessor (x % universeSize d) with
          | none =>
            simp only [hpred] at hp
            obtain ⟨a, ha, hlt⟩ := ((ht.cluster i).minimum_any_lt_iff).mp hc
            have := hp a ha
            omega
          | some y =>
            simp only [hpred] at hp
            obtain ⟨hy, hlow, hgreatest⟩ := hp
            simp only [Option.map_some, contains_node_some]
            refine ⟨Or.inr ⟨i, y, hy, rfl⟩, (hbelow i y hy).mpr (Or.inr ⟨rfl, hlow⟩), ?_⟩
            rintro z (rfl | ⟨j, a, ha, rfl⟩) hzx
            · exact (ht.min_lt_cluster hy).le
            rcases (hbelow j a ha).mp hzx with hji | ⟨rfl, hlow'⟩
            · exact (cluster_key_lt_of_lt ((ht.cluster j).contains_lt ha) hji).le
            · exact Nat.add_le_add_left (hgreatest a ha hlow') _
        · -- No key of cluster `i` is below the low part: find the previous occupied cluster.
          rw [ite_eq_right hc]
          have hearlier : ∀ j a, (c j).Contains a →
              j.val * universeSize d + a < x → j.val < i.val := by
            intro j a ha hax
            rcases (hbelow j a ha).mp hax with hji | ⟨rfl, hlow⟩
            · exact hji
            · exact absurd ((ht.cluster i).minimum_any_lt_iff.mpr ⟨a, ha, hlow⟩) hc
          have hp := ih ht.summary i.val
          cases hpred : s.predecessor i.val with
          | none =>
            -- No earlier cluster is occupied, so the excluded minimum is the answer.
            simp only [hpred] at hp
            refine ⟨hmin, by omega, ?_⟩
            simp only [contains_node_some]
            rintro z (rfl | ⟨j, a, ha, rfl⟩) hzx
            · exact le_rfl
            · have := hearlier j a ha hzx
              have := hp j.val (ht.summary_contains ha)
              omega
          | some j =>
            simp only [hpred] at hp
            obtain ⟨hjs, hji, hprev⟩ := hp
            have hj := ht.summary.contains_lt hjs
            let k : Fin (universeSize d) := ⟨j, hj⟩
            obtain ⟨⟨cm, cM⟩, hb⟩ :=
              Option.isSome_iff_exists.mp ((ht.summary_contains_iff k).mp hjs)
            have hcM := (ht.cluster k).contains_maximum hb
            dsimp only
            rw [dite_eq_left hj, maximum, hb]
            simp only [Option.map_some, contains_node_some]
            refine ⟨Or.inr ⟨k, cM, hcM, rfl⟩, (hbelow k cM hcM).mpr (Or.inl hji), ?_⟩
            rintro z (rfl | ⟨l, a, ha, rfl⟩) hzx
            · exact (ht.min_lt_cluster hcM).le
            have hlk := hprev l.val (ht.summary_contains ha) (hearlier l a ha hzx)
            rcases Nat.lt_or_eq_of_le hlk with hlk | hlk
            · exact (cluster_key_lt_of_lt ((ht.cluster l).contains_lt ha) hlk).le
            · obtain rfl : l = k := Fin.ext hlk
              exact Nat.add_le_add_left ((ht.cluster k).le_max_of_contains hb ha) _

/-- A successful result is exactly the greatest represented key strictly less than the query. -/
theorem predecessor_eq_some_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    t.predecessor x = some y ↔
      t.Contains y ∧ y < x ∧ ∀ z, t.Contains z → z < x → z ≤ y := by
  have hp := predecessor_spec ht x
  cases h : t.predecessor x with
  | none =>
    simp only [h] at hp
    simp only [reduceCtorEq, false_iff]
    intro hy
    have := hp y hy.1
    omega
  | some z =>
    simp only [h] at hp
    constructor
    · intro hy
      cases hy
      exact hp
    · intro hy
      have := hp.2.2 y hy.1 hy.2.1
      have := hy.2.2 z hp.1 hp.2.1
      congr 1
      omega

/-- Failure is exactly the absence of a represented key strictly below the query. -/
theorem predecessor_eq_none_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.predecessor x = none ↔ ∀ z, t.Contains z → x ≤ z := by
  have hp := predecessor_spec ht x
  cases h : t.predecessor x with
  | none => simp only [h] at hp; exact ⟨fun _ => hp, fun _ => rfl⟩
  | some y =>
    simp only [h] at hp
    simp only [reduceCtorEq, false_iff]
    intro hn
    have := hn y hp.1
    omega

/-- A valid node with a query strictly above its cached minimum always has a strict predecessor
in `[0, universeSize d)`. -/
theorem predecessor_isSome_of_gt_min {d m M query : ℕ} {tree : Tree d}
    (ht : tree.Valid) (hb : tree.bounds = some (m, M)) (hq : m < query) :
    ∃ ans < universeSize d, tree.predecessor query = some ans := by
  cases hp : tree.predecessor query with
  | none =>
    have hge := (predecessor_eq_none_iff ht query).mp hp m (ht.contains_minimum hb)
    omega
  | some ans =>
    have hspec := (predecessor_eq_some_iff ht query ans).mp hp
    exact ⟨ans, ht.contains_lt hspec.1, rfl⟩

end Cslib.DataStructure.VanEmdeBoas.Tree
