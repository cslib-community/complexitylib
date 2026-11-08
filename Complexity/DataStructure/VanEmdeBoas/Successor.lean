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
# Correctness of strict van Emde Boas successor

The recursive algorithm returns the least represented key strictly greater than its query.
Queries may lie outside the represented universe; failure means that every represented key is
at most the query. These are mathematical correctness statements, without a machine cost claim.

## Main definitions

The algorithm and recursive invariant are `Tree.successor` and `Tree.Valid`, imported from `Basic`.

## Main results

* `Tree.successor_spec`: the successful and unsuccessful result specifications.
* `Tree.successor_eq_some_iff`: success is equivalent to being the least greater stored key.
* `Tree.successor_eq_none_iff`: failure is equivalent to having no greater stored key.
* `Tree.successor_isSome_of_lt_max`: a query strictly below the cached maximum always has a
  strict successor in `[0, universeSize d)`.

## References

* [E. Demaine, *Divide and conquer: van Emde Boas trees*, Lecture 4][Demaine2015VanEmdeBoas]
-/

@[expose] public section

namespace Cslib.DataStructure.VanEmdeBoas.Tree

/-- The cached maximum exceeds `x` exactly when some represented key does. -/
private theorem Valid.maximum_any_lt_iff {d x : ℕ} {t : Tree d} (ht : t.Valid) :
    t.maximum.any (x < ·) = true ↔ ∃ a, t.Contains a ∧ x < a := by
  cases hb : t.bounds with
  | none => simp [maximum, hb, not_contains_of_bounds_none hb]
  | some b =>
    obtain ⟨m, M⟩ := b
    simp only [maximum, hb, Option.map_some, Option.any_some, decide_eq_true_eq]
    exact ⟨fun h => ⟨M, ht.contains_maximum hb, h⟩,
      fun ⟨a, ha, hxa⟩ => hxa.trans_le (ht.le_max_of_contains hb ha)⟩

/-- A query lies below a cluster key exactly when its cluster is earlier, or it is the same
cluster with a smaller low part. -/
private theorem lt_cluster_key_iff {u x j a : ℕ} (hu : 0 < u) (ha : a < u) :
    x < j * u + a ↔ x / u < j ∨ x / u = j ∧ x % u < a := by
  conv_lhs => rw [← Nat.div_add_mod' x u]
  exact cluster_key_lt_iff (Nat.mod_lt x hu) ha

/-- A returned key is the least represented key strictly above the query; failure certifies
that every represented key is at most the query. No bound on the query is required. -/
theorem successor_spec {d : ℕ} {t : Tree d} (ht : t.Valid) (x : ℕ) :
    match t.successor x with
    | some y => t.Contains y ∧ x < y ∧ ∀ z, t.Contains z → x < z → y ≤ z
    | none => ∀ z, t.Contains z → z ≤ x := by
  induction d generalizing x with
  | zero =>
    cases t with
    | leaf b =>
      cases b with
      | none => simp [successor, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        have hmM := ht.min_le_of_contains rfl (ht.contains_maximum rfl)
        simp only [successor]
        split_ifs <;>
          simp only [contains_leaf_some, forall_eq_or_imp, forall_eq, true_or, or_true,
            true_and] <;>
          omega
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => simp [successor, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        have hmin := ht.contains_minimum rfl
        by_cases hm : x < m
        · -- The query is below the cached minimum, which is therefore the answer.
          rw [successor, ite_eq_left hm]
          exact ⟨hmin, hm, fun z hz _ => ht.min_le_of_contains rfl hz⟩
        by_cases hM : M ≤ x
        · -- The query is at or above the cached maximum: there is no successor.
          rw [successor, ite_eq_right hm, ite_eq_left hM]
          exact fun z hz => (ht.le_max_of_contains rfl hz).trans hM
        -- Otherwise `m ≤ x < M`; split `x` into its cluster `i` and low part.
        have hu := universeSize_pos d
        have hi : x / universeSize d < universeSize d :=
          (Nat.div_lt_iff_lt_mul hu).mpr
            ((Nat.lt_of_not_le hM).trans (ht.contains_lt (ht.contains_maximum rfl)))
        let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
        /- A cluster key exceeds `x` iff its cluster is later than `i`, or it is in `i` itself
        with a larger low part. -/
        have habove : ∀ j a, (c j).Contains a →
            (x < j.val * universeSize d + a ↔
              i.val < j.val ∨ i = j ∧ x % universeSize d < a) := by
          intro j a ha
          rw [lt_cluster_key_iff hu ((ht.cluster j).contains_lt ha), Fin.ext_iff]
        rw [successor, ite_eq_right hm, ite_eq_right hM, dite_eq_left hi]
        by_cases hc : (c i).maximum.any (x % universeSize d < ·) = true
        · -- Some key of cluster `i` exceeds the low part: recurse into cluster `i`.
          rw [ite_eq_left hc]
          have hs := ih (ht.cluster i) (x % universeSize d)
          cases hsuc : (c i).successor (x % universeSize d) with
          | none =>
            simp only [hsuc] at hs
            obtain ⟨a, ha, hlt⟩ := ((ht.cluster i).maximum_any_lt_iff).mp hc
            have := hs a ha
            omega
          | some y =>
            simp only [hsuc] at hs
            obtain ⟨hy, hlow, hleast⟩ := hs
            simp only [Option.map_some, contains_node_some]
            refine ⟨Or.inr ⟨i, y, hy, rfl⟩, (habove i y hy).mpr (Or.inr ⟨rfl, hlow⟩), ?_⟩
            rintro z (rfl | ⟨j, a, ha, rfl⟩) hxz
            · omega
            rcases (habove j a ha).mp hxz with hij | ⟨rfl, hlow'⟩
            · exact (cluster_key_lt_of_lt ((ht.cluster i).contains_lt hy) hij).le
            · exact Nat.add_le_add_left (hleast a ha hlow') _
        · -- No key of cluster `i` exceeds the low part: find the next occupied cluster.
          rw [ite_eq_right hc]
          have hlater : ∀ j a, (c j).Contains a →
              x < j.val * universeSize d + a → i.val < j.val := by
            intro j a ha hxa
            rcases (habove j a ha).mp hxa with hij | ⟨rfl, hlow⟩
            · exact hij
            · exact absurd ((ht.cluster i).maximum_any_lt_iff.mpr ⟨a, ha, hlow⟩) hc
          have hs := ih ht.summary i.val
          cases hsuc : s.successor i.val with
          | none =>
            simp only [hsuc] at hs
            simp only [bind, Option.bind_none, contains_node_some]
            rintro z (rfl | ⟨j, a, ha, rfl⟩)
            · omega
            · by_contra hn
              have := hlater j a ha (by omega)
              have := hs j.val (ht.summary_contains ha)
              omega
          | some j =>
            simp only [hsuc] at hs
            obtain ⟨hjs, hij, hnext⟩ := hs
            have hj := ht.summary.contains_lt hjs
            let k : Fin (universeSize d) := ⟨j, hj⟩
            obtain ⟨⟨cm, cM⟩, hb⟩ :=
              Option.isSome_iff_exists.mp ((ht.summary_contains_iff k).mp hjs)
            have hcm := (ht.cluster k).contains_minimum hb
            simp only [bind, Option.bind_some]
            rw [dite_eq_left hj, minimum, hb]
            simp only [Option.map_some, contains_node_some]
            refine ⟨Or.inr ⟨k, cm, hcm, rfl⟩, (habove k cm hcm).mpr (Or.inl hij), ?_⟩
            rintro z (rfl | ⟨l, a, ha, rfl⟩) hxz
            · omega
            have hkl := hnext l.val (ht.summary_contains ha) (hlater l a ha hxz)
            rcases Nat.lt_or_eq_of_le hkl with hkl | hkl
            · exact (cluster_key_lt_of_lt ((ht.cluster k).contains_lt hcm) hkl).le
            · obtain rfl : k = l := Fin.ext hkl
              exact Nat.add_le_add_left ((ht.cluster k).min_le_of_contains hb ha) _

/-- A successful result is exactly the least represented key strictly greater than the query. -/
theorem successor_eq_some_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    t.successor x = some y ↔
      t.Contains y ∧ x < y ∧ ∀ z, t.Contains z → x < z → y ≤ z := by
  have hs := successor_spec ht x
  cases h : t.successor x with
  | none =>
    simp only [h] at hs
    simp only [reduceCtorEq, false_iff]
    intro hy
    have := hs y hy.1
    omega
  | some z =>
    simp only [h] at hs
    constructor
    · intro hy
      cases hy
      exact hs
    · intro hy
      have := hs.2.2 y hy.1 hy.2.1
      have := hy.2.2 z hs.1 hs.2.1
      congr 1
      omega

/-- Failure is exactly the absence of a represented key strictly above the query. -/
theorem successor_eq_none_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.successor x = none ↔ ∀ z, t.Contains z → z ≤ x := by
  have hs := successor_spec ht x
  cases h : t.successor x with
  | none => simp only [h] at hs; exact ⟨fun _ => hs, fun _ => rfl⟩
  | some y =>
    simp only [h] at hs
    simp only [reduceCtorEq, false_iff]
    intro hn
    have := hn y hs.1
    omega

/-- A valid node with a query strictly below its cached maximum always has a strict successor
in `[0, universeSize d)`. -/
theorem successor_isSome_of_lt_max {d m M query : ℕ} {tree : Tree d}
    (ht : tree.Valid) (hb : tree.bounds = some (m, M)) (hq : query < M) :
    ∃ ans < universeSize d, tree.successor query = some ans := by
  cases hs : tree.successor query with
  | none =>
    have hle := (successor_eq_none_iff ht query).mp hs M (ht.contains_maximum hb)
    omega
  | some ans =>
    have hspec := (successor_eq_some_iff ht query ans).mp hs
    exact ⟨ans, ht.contains_lt hspec.1, rfl⟩

end Cslib.DataStructure.VanEmdeBoas.Tree
