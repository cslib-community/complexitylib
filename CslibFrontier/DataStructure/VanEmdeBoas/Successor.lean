/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.VanEmdeBoas.Basic
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

public section

namespace Cslib.DataStructure.VanEmdeBoas.Tree

private theorem maximum_any_iff {d x : ℕ} {t : Tree d} :
    t.maximum.any (x < ·) = true ↔ ∃ m M, t.bounds = some (m, M) ∧ x < M := by
  cases hb : t.bounds with
  | none => simp [maximum, hb]
  | some b => obtain ⟨m, M⟩ := b; simp [maximum, hb]

private theorem succ_of_lt_min {d m M x : ℕ} {t : Tree d} (ht : t.Valid)
    (hb : t.bounds = some (m, M)) (hm : x < m) :
    t.Contains m ∧ x < m ∧ ∀ z, t.Contains z → x < z → m ≤ z :=
  have he := ht.extrema_of_bounds hb
  ⟨he.2.2.1, hm, fun z hz _ => (he.2.2.2.2 z hz).1⟩

private theorem succ_cluster_ans {d m M x : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} (ht : (node (some (m, M)) s c).Valid) (hm : ¬x < m)
    {k : Fin (universeSize d)} {b : ℕ} (hb : (c k).Contains b)
    (hlt : x < k.val * universeSize d + b)
    (hle : ∀ l a, (c l).Contains a → x < l.val * universeSize d + a →
      k.val ≤ l.val ∧ (k = l → b ≤ a)) :
    (node (some (m, M)) s c).Contains (k.val * universeSize d + b) ∧
      x < k.val * universeSize d + b ∧
      ∀ z, (node (some (m, M)) s c).Contains z → x < z → k.val * universeSize d + b ≤ z := by
  refine ⟨⟨m, M, rfl, Or.inr ⟨k, b, hb, rfl⟩⟩, hlt, fun z hz hxz => ?_⟩
  rcases hz with ⟨_, _, ⟨⟩, rfl | ⟨l, a, ha, rfl⟩⟩
  · omega
  · obtain ⟨hkl, hab⟩ := hle l a ha hxz
    rcases Nat.lt_or_eq_of_le hkl with hlt | hEq
    · exact (index_lt_index ((ht.2.2.1 k).contains_lt hb) hlt).le
    · obtain rfl : k = l := Fin.ext hEq
      exact Nat.add_le_add_left (hab rfl) _

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
      rcases b with _ | ⟨m, M⟩
      · simp [successor, Contains]
      · have he := ht.extrema_of_bounds rfl
        simp only [successor]
        split_ifs with hm hM
        · exact succ_of_lt_min ht rfl hm
        · refine ⟨he.2.2.2.1, hM, fun z hz hxz => ?_⟩
          obtain ⟨_, _, hb, rfl | rfl⟩ := hz <;> cases hb <;> omega
        · exact fun z hz => by have := (he.2.2.2.2 z hz).2; omega
  | succ d ih =>
    cases t with
    | node b s c =>
      rcases b with _ | ⟨m, M⟩
      · simp [successor, Contains]
      · have he := ht.extrema_of_bounds rfl
        by_cases hm : x < m
        · rw [successor, ite_eq_left hm]
          exact succ_of_lt_min ht rfl hm
        · by_cases hM : M ≤ x
          · rw [successor, ite_eq_right hm, ite_eq_left hM]
            exact fun z hz => (he.2.2.2.2 z hz).2.trans hM
          · have hi : x / universeSize d < universeSize d :=
              (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr ((show x < M by omega).trans he.2.1)
            let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
            have hx : x = i.val * universeSize d + x % universeSize d := by
              simpa only [i, Nat.mul_comm] using (Nat.div_add_mod x (universeSize d)).symm
            have hoc : ∀ j y, (c j).Contains y → s.Contains j.val :=
              fun j y hy => (ht.2.2.2.1 j).mpr (bounds_isSome_of_contains hy)
            rw [successor, ite_eq_right hm, ite_eq_right hM, dite_eq_left hi]
            by_cases hc : (c i).maximum.any (x % universeSize d < ·) = true
            · rw [ite_eq_left hc]
              have hs := ih (ht.2.2.1 i) (x % universeSize d)
              cases hsuc : (c i).successor (x % universeSize d) with
              | none =>
                simp only [hsuc] at hs
                obtain ⟨_, cM, hb, hlt⟩ := maximum_any_iff.mp hc
                exact absurd (hs cM ((ht.2.2.1 i).contains_maximum hb)) (by omega)
              | some y =>
                simp only [hsuc, Option.map_some] at hs ⊢
                refine succ_cluster_ans ht hm hs.1
                  (hx.trans_lt (Nat.add_lt_add_left hs.2.1 _)) fun l a ha hxz => ?_
                rcases cluster_lt_split ((ht.2.2.1 l).contains_lt ha)
                    (hx ▸ hxz) with hlt | ⟨rfl, hlow⟩
                · exact ⟨hlt.le, fun h => absurd (congrArg Fin.val h) (by omega)⟩
                · exact ⟨le_rfl, fun _ => hs.2.2 a ha hlow⟩
            · rw [ite_eq_right hc]
              have hle : ∀ a, (c i).Contains a → a ≤ x % universeSize d := by
                intro a ha
                obtain ⟨⟨cm, cM⟩, hb⟩ := Option.isSome_iff_exists.mp (bounds_isSome_of_contains ha)
                have hcM : ¬x % universeSize d < cM := fun h =>
                  hc (maximum_any_iff.mpr ⟨cm, cM, hb, h⟩)
                have := ((ht.2.2.1 i).extrema_of_bounds hb).2.2.2.2 a ha
                omega
              have hlater : ∀ j a, (c j).Contains a →
                  x < j.val * universeSize d + a → i.val < j.val := by
                intro j a ha hxa
                rcases cluster_lt_split ((ht.2.2.1 j).contains_lt ha)
                    (hx ▸ hxa) with hlt | ⟨rfl, hlow⟩
                · exact hlt
                · exact absurd (hle a ha) (by omega)
              have hs := ih ht.2.1 i.val
              cases hsuc : s.successor i.val with
              | none =>
                simp only [hsuc, bind, Option.bind_none] at hs ⊢
                intro z hz
                rcases hz with ⟨_, _, ⟨⟩, rfl | ⟨j, a, ha, rfl⟩⟩
                · omega
                · by_contra hn
                  have := hlater j a ha (by omega)
                  have := hs j.val (hoc j a ha)
                  omega
              | some j =>
                simp only [hsuc, bind, Option.bind_some] at hs ⊢
                have hj := ht.2.1.contains_lt hs.1
                let k : Fin (universeSize d) := ⟨j, hj⟩
                obtain ⟨⟨cm, cM⟩, hb⟩ := Option.isSome_iff_exists.mp ((ht.2.2.2.1 k).mp hs.1)
                have hce := (ht.2.2.1 k).extrema_of_bounds hb
                rw [dite_eq_left hj, minimum, hb]
                simp only [Option.map_some]
                exact succ_cluster_ans ht hm hce.2.2.1
                  (hx ▸ index_lt_index (Nat.mod_lt _ (universeSize_pos d)) hs.2.1) fun l a ha hxz =>
                  ⟨hs.2.2 l.val (hoc l a ha) (hlater l a ha hxz),
                    fun hkl => (hce.2.2.2.2 a (hkl ▸ ha)).1⟩

/-- A successful result is exactly the least represented key strictly greater than the query. -/
theorem successor_eq_some_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    t.successor x = some y ↔
      t.Contains y ∧ x < y ∧ ∀ z, t.Contains z → x < z → y ≤ z := by
  have hs := successor_spec ht x
  cases h : t.successor x with
  | none =>
    simp only [h, reduceCtorEq, false_iff] at hs ⊢
    exact fun hy => absurd (hs y hy.1) (by omega)
  | some z =>
    simp only [h, Option.some.injEq] at hs ⊢
    exact ⟨fun hzy => hzy ▸ hs, fun hy =>
      Nat.le_antisymm (hs.2.2 y hy.1 hy.2.1) (hy.2.2 z hs.1 hs.2.1)⟩

/-- Failure is exactly the absence of a represented key strictly above the query. -/
theorem successor_eq_none_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.successor x = none ↔ ∀ z, t.Contains z → z ≤ x := by
  have hs := successor_spec ht x
  cases h : t.successor x with
  | none => simp only [h] at hs; exact ⟨fun _ => hs, fun _ => rfl⟩
  | some y =>
    simp only [h, reduceCtorEq, false_iff] at hs ⊢
    exact fun hn => absurd (hn y hs.1) (by omega)

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
