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

private theorem minimum_any_iff {d x : ℕ} {t : Tree d} :
    t.minimum.any (· < x) = true ↔ ∃ m M, t.bounds = some (m, M) ∧ m < x := by
  cases hb : t.bounds with
  | none => simp [minimum, hb]
  | some b => obtain ⟨m, M⟩ := b; simp [minimum, hb]

private theorem pred_of_max_lt {d m M x : ℕ} {t : Tree d} (ht : t.Valid)
    (hb : t.bounds = some (m, M)) (hM : M < x) :
    t.Contains M ∧ M < x ∧ ∀ z, t.Contains z → z < x → z ≤ M :=
  have he := ht.extrema_of_bounds hb
  ⟨he.2.2.2.1, hM, fun z hz _ => (he.2.2.2.2 z hz).2⟩

private theorem pred_cluster_ans {d m M x : ℕ} {s : Tree d}
    {c : Fin (universeSize d) → Tree d} (ht : (node (some (m, M)) s c).Valid)
    {k : Fin (universeSize d)} {b : ℕ} (hb : (c k).Contains b)
    (hlt : k.val * universeSize d + b < x)
    (hle : ∀ l a, (c l).Contains a → l.val * universeSize d + a < x →
      l.val ≤ k.val ∧ (l = k → a ≤ b)) :
    (node (some (m, M)) s c).Contains (k.val * universeSize d + b) ∧
      k.val * universeSize d + b < x ∧
      ∀ z, (node (some (m, M)) s c).Contains z → z < x → z ≤ k.val * universeSize d + b := by
  refine ⟨⟨m, M, rfl, Or.inr ⟨k, b, hb, rfl⟩⟩, hlt, fun z hz hzx => ?_⟩
  rcases hz with ⟨_, _, ⟨⟩, rfl | ⟨l, a, ha, rfl⟩⟩
  · exact (ht.2.2.2.2 k b hb).le
  · obtain ⟨hlk, hab⟩ := hle l a ha hzx
    rcases Nat.lt_or_eq_of_le hlk with hlt | hEq
    · exact (index_lt_index ((ht.2.2.1 l).contains_lt ha) hlt).le
    · obtain rfl : l = k := Fin.ext hEq
      exact Nat.add_le_add_left (hab rfl) _

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
      rcases b with _ | ⟨m, M⟩
      · simp [predecessor, Contains]
      · have he := ht.extrema_of_bounds rfl
        by_cases hM : M < x
        · rw [predecessor, ite_eq_left hM]; exact pred_of_max_lt ht rfl hM
        · by_cases hm : m < x
          · rw [predecessor, ite_eq_right hM, ite_eq_left hm]
            refine ⟨he.2.2.1, hm, fun z hz hzx => ?_⟩
            obtain ⟨_, _, hb, rfl | rfl⟩ := hz <;> cases hb <;> omega
          · rw [predecessor, ite_eq_right hM, ite_eq_right hm]
            exact fun z hz => by have := (he.2.2.2.2 z hz).1; omega
  | succ d ih =>
    cases t with
    | node b s c =>
      rcases b with _ | ⟨m, M⟩
      · simp [predecessor, Contains]
      · have he := ht.extrema_of_bounds rfl
        by_cases hM : M < x
        · rw [predecessor, ite_eq_left hM]
          exact pred_of_max_lt ht rfl hM
        · by_cases hm : x ≤ m
          · rw [predecessor, ite_eq_right hM, ite_eq_left hm]
            exact fun z hz => hm.trans (he.2.2.2.2 z hz).1
          · have hi : x / universeSize d < universeSize d :=
              (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr
                (Nat.lt_of_le_of_lt (show x ≤ M by omega) he.2.1)
            let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
            have hx : x = i.val * universeSize d + x % universeSize d := by
              simpa only [i, Nat.mul_comm] using (Nat.div_add_mod x (universeSize d)).symm
            have hoc : ∀ j y, (c j).Contains y → s.Contains j.val :=
              fun j y hy => (ht.2.2.2.1 j).mpr (bounds_isSome_of_contains hy)
            rw [predecessor, ite_eq_right hM, ite_eq_right hm, dite_eq_left hi]
            by_cases hc : (c i).minimum.any (· < x % universeSize d) = true
            · rw [ite_eq_left hc]
              have hp := ih (ht.2.2.1 i) (x % universeSize d)
              cases hpred : (c i).predecessor (x % universeSize d) with
              | none =>
                simp only [hpred] at hp
                obtain ⟨cm, _, hb, hlt⟩ := minimum_any_iff.mp hc
                exact absurd (hp cm ((ht.2.2.1 i).contains_minimum hb)) (by omega)
              | some y =>
                simp only [hpred, Option.map_some] at hp ⊢
                refine pred_cluster_ans ht hp.1
                  ((Nat.add_lt_add_left hp.2.1 _).trans_eq hx.symm) fun l a ha hzx => ?_
                rcases cluster_lt_split (Nat.mod_lt _ (universeSize_pos d))
                    (hx ▸ hzx) with hlt | ⟨rfl, hlow⟩
                · exact ⟨hlt.le, fun h => absurd (congrArg Fin.val h) (by omega)⟩
                · exact ⟨le_rfl, fun _ => hp.2.2 a ha hlow⟩
            · rw [ite_eq_right hc]
              have hge : ∀ a, (c i).Contains a → x % universeSize d ≤ a := by
                intro a ha
                obtain ⟨⟨cm, cM⟩, hb⟩ := Option.isSome_iff_exists.mp (bounds_isSome_of_contains ha)
                have hcm : ¬cm < x % universeSize d := fun h =>
                  hc (minimum_any_iff.mpr ⟨cm, cM, hb, h⟩)
                have := ((ht.2.2.1 i).extrema_of_bounds hb).2.2.2.2 a ha
                omega
              have hearlier : ∀ j a, (c j).Contains a →
                  j.val * universeSize d + a < x → j.val < i.val := by
                intro j a ha hax
                rcases cluster_lt_split (Nat.mod_lt _ (universeSize_pos d))
                    (hx ▸ hax) with hlt | ⟨rfl, hlow⟩
                · exact hlt
                · exact absurd (hge a ha) (by omega)
              have hp := ih ht.2.1 i.val
              cases hpred : s.predecessor i.val with
              | none =>
                simp only [hpred] at hp
                refine ⟨he.2.2.1, by omega, fun z hz hzx => ?_⟩
                rcases hz with ⟨_, _, ⟨⟩, rfl | ⟨j, a, ha, rfl⟩⟩
                · exact le_rfl
                · have := hearlier j a ha hzx
                  have := hp j.val (hoc j a ha)
                  omega
              | some j =>
                simp only [hpred] at hp
                have hj := ht.2.1.contains_lt hp.1
                let k : Fin (universeSize d) := ⟨j, hj⟩
                obtain ⟨⟨cm, cM⟩, hb⟩ := Option.isSome_iff_exists.mp ((ht.2.2.2.1 k).mp hp.1)
                have hce := (ht.2.2.1 k).extrema_of_bounds hb
                dsimp only
                rw [dite_eq_left hj, maximum, hb]
                simp only [Option.map_some]
                exact pred_cluster_ans ht hce.2.2.2.1
                  ((index_lt_index hce.2.1 hp.2.1).trans_eq hx.symm) fun l a ha hzx =>
                  ⟨hp.2.2 l.val (hoc l a ha) (hearlier l a ha hzx),
                    fun hlk => (hce.2.2.2.2 a (hlk ▸ ha)).2⟩

/-- A successful result is exactly the greatest represented key strictly less than the query. -/
theorem predecessor_eq_some_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x y : ℕ) :
    t.predecessor x = some y ↔
      t.Contains y ∧ y < x ∧ ∀ z, t.Contains z → z < x → z ≤ y := by
  have hp := predecessor_spec ht x
  cases h : t.predecessor x with
  | none =>
    simp only [h, reduceCtorEq, false_iff] at hp ⊢
    exact fun hy => absurd (hp y hy.1) (by omega)
  | some z =>
    simp only [h, Option.some.injEq] at hp ⊢
    exact ⟨fun hzy => hzy ▸ hp, fun hy =>
      Nat.le_antisymm (hy.2.2 z hp.1 hp.2.1) (hp.2.2 y hy.1 hy.2.1)⟩

/-- Failure is exactly the absence of a represented key strictly below the query. -/
theorem predecessor_eq_none_iff {d : ℕ} {t : Tree d} (ht : t.Valid) (x : ℕ) :
    t.predecessor x = none ↔ ∀ z, t.Contains z → x ≤ z := by
  have hp := predecessor_spec ht x
  cases h : t.predecessor x with
  | none => simp only [h] at hp; exact ⟨fun _ => hp, fun _ => rfl⟩
  | some y =>
    simp only [h, reduceCtorEq, false_iff] at hp ⊢
    exact fun hn => absurd (hn y hp.1) (by omega)

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
