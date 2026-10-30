/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.VanEmdeBoas.Basic
import Mathlib.Tactic.Linarith

/-!
# Strict van Emde Boas predecessor

This module defines and verifies strict predecessor lookup on recursive minimum-excluded
van Emde Boas trees ([Demaine2015VanEmdeBoas], p. 5; [CLRS2009], Section 20.3, p. 552).
The algorithm returns the greatest represented key strictly less than its query, or `none` when
every represented key is at least the query. Queries need not lie inside `[0, universeSize d)`.

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

namespace Cslib.Algorithms.Lean.VanEmdeBoas.Tree

/-- The greatest stored key strictly less than the query, or `none` if it does not exist.
The cached cluster minimum chooses between one cluster recursion and one summary recursion;
when no cluster entry precedes `x > m`, the excluded node minimum `m` is returned
([Demaine2015VanEmdeBoas], p. 5; [CLRS2009], Section 20.3, p. 552). -/
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

private theorem index_lt_index {u i j a b : ℕ} (ha : a < u) (hij : i < j) :
    i * u + a < j * u + b := by
  have h := Nat.mul_le_mul_right u (show i + 1 ≤ j by omega)
  nlinarith

private theorem bounds_isSome_of_contains {d : ℕ} {t : Tree d} {x : ℕ}
    (hx : t.Contains x) : t.bounds.isSome = true := by
  cases hb : t.bounds with
  | none => exact False.elim (not_contains_of_bounds_none hb x hx)
  | some _ => rfl

private theorem minimum_any_iff {d x : ℕ} {t : Tree d} :
    t.minimum.any (· < x) = true ↔ ∃ m M, t.bounds = some (m, M) ∧ m < x := by
  cases hb : t.bounds with
  | none => simp [minimum, hb]
  | some b => obtain ⟨m, M⟩ := b; simp [minimum, hb]

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
        have he := ht.extrema
        simp only [Extrema, bounds] at he
        by_cases hM : M < x
        · rw [predecessor, ite_eq_left hM]
          exact ⟨he.2.2.2.1, hM, fun z hz _ => (he.2.2.2.2 z hz).2⟩
        · by_cases hm : m < x
          · rw [predecessor, ite_eq_right hM, ite_eq_left hm]
            refine ⟨he.2.2.1, hm, ?_⟩
            intro z hz hzx
            obtain ⟨m', M', hb, hz⟩ := hz
            cases hb
            rcases hz with rfl | rfl <;> omega
          · rw [predecessor, ite_eq_right hM, ite_eq_right hm]
            intro z hz
            have := (he.2.2.2.2 z hz).1
            omega
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => simp [predecessor, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        have he := ht.extrema
        simp only [Extrema, bounds] at he
        by_cases hM : M < x
        · rw [predecessor, ite_eq_left hM]
          exact ⟨he.2.2.2.1, hM, fun z hz _ => (he.2.2.2.2 z hz).2⟩
        · by_cases hm : x ≤ m
          · rw [predecessor, ite_eq_right hM, ite_eq_left hm]
            intro z hz
            exact hm.trans (he.2.2.2.2 z hz).1
          · have hi : x / universeSize d < universeSize d := by
              apply (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr
              exact Nat.lt_of_le_of_lt (show x ≤ M by omega) he.2.1
            let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
            have hx : x = i.val * universeSize d + x % universeSize d := by
              simpa only [i, Nat.mul_comm] using (Nat.div_add_mod x (universeSize d)).symm
            have hoc : ∀ j y, (c j).Contains y → s.Contains j.val := by
              intro j y hy
              exact (ht.2.2.2.1 j).mpr (bounds_isSome_of_contains hy)
            rw [predecessor, ite_eq_right hM, ite_eq_right hm, dite_eq_left hi]
            by_cases hc : (c i).minimum.any (· < x % universeSize d) = true
            · rw [ite_eq_left hc]
              have hp := ih (ht.2.2.1 i) (x % universeSize d)
              cases hpred : (c i).predecessor (x % universeSize d) with
              | none =>
                simp only [hpred] at hp
                obtain ⟨cm, cM, hb, hlt⟩ := minimum_any_iff.mp hc
                have := hp cm ((ht.2.2.1 i).contains_minimum hb)
                omega
              | some y =>
                simp only [hpred] at hp
                simp only [Option.map_some]
                refine ⟨⟨m, M, rfl, Or.inr ⟨i, y, hp.1, rfl⟩⟩, ?_, ?_⟩
                · exact (Nat.add_lt_add_left hp.2.1 (i.val * universeSize d)).trans_eq hx.symm
                · intro z hz hzx
                  obtain ⟨m', M', hb, hz⟩ := hz
                  cases hb
                  rcases hz with rfl | ⟨j, a, ha, rfl⟩
                  · exact (ht.2.2.2.2 i y hp.1).le
                  · have hja := cluster_coordinates (i := j.val) (universeSize_pos d)
                      ((ht.2.2.1 j).contains_lt ha)
                    have hji : j.val ≤ i.val := by
                      have h := Nat.div_le_div_right (c := universeSize d) (Nat.le_of_lt hzx)
                      simpa only [i, hja.1] using h
                    by_cases hij' : j = i
                    · subst j
                      have hlow : a < x % universeSize d := by omega
                      exact Nat.add_le_add_left (hp.2.2 a ha hlow) (i.val * universeSize d)
                    · have hlt : j.val < i.val := by
                        have : j.val ≠ i.val := fun h => hij' (Fin.ext h)
                        omega
                      exact (index_lt_index ((ht.2.2.1 j).contains_lt ha) hlt).le
            · rw [ite_eq_right hc]
              have hge : ∀ a, (c i).Contains a → x % universeSize d ≤ a := by
                intro a ha
                have hce := (ht.2.2.1 i).extrema
                cases hb : (c i).bounds with
                | none => exact False.elim (not_contains_of_bounds_none hb a ha)
                | some b =>
                  obtain ⟨cm, cM⟩ := b
                  simp only [Extrema, hb] at hce
                  have hn : ¬cm < x % universeSize d := by
                    intro hlt
                    exact hc (minimum_any_iff.mpr ⟨cm, cM, hb, hlt⟩)
                  have := (hce.2.2.2.2 a ha).1
                  omega
              have hearlier : ∀ j a, (c j).Contains a →
                  j.val * universeSize d + a < x → j.val < i.val := by
                intro j a ha hax
                have hja := cluster_coordinates (i := j.val) (universeSize_pos d)
                  ((ht.2.2.1 j).contains_lt ha)
                have hji : j.val ≤ i.val := by
                  have h := Nat.div_le_div_right (c := universeSize d) (Nat.le_of_lt hax)
                  simpa only [i, hja.1] using h
                by_cases hlt : j.val < i.val
                · exact hlt
                · have hij' : i = j := Fin.ext (by omega)
                  subst j
                  have := hge a ha
                  omega
              have hp := ih ht.2.1 i.val
              cases hpred : s.predecessor i.val with
              | none =>
                simp only [hpred] at hp
                refine ⟨he.2.2.1, by omega, ?_⟩
                intro z hz hzx
                obtain ⟨m', M', hb, hz⟩ := hz
                cases hb
                rcases hz with rfl | ⟨j, a, ha, rfl⟩
                · exact le_rfl
                · have := hearlier j a ha hzx
                  have := hp j.val (hoc j a ha)
                  omega
              | some j =>
                simp only [hpred] at hp
                have hj := ht.2.1.contains_lt hp.1
                let k : Fin (universeSize d) := ⟨j, hj⟩
                have hk : (c k).bounds.isSome = true := (ht.2.2.2.1 k).mp hp.1
                cases hb : (c k).bounds with
                | none => simp [hb] at hk
                | some b =>
                  obtain ⟨cm, cM⟩ := b
                  have hce := (ht.2.2.1 k).extrema
                  simp only [Extrema, hb] at hce
                  dsimp only
                  rw [dite_eq_left hj, maximum, hb]
                  simp only [Option.map_some]
                  refine ⟨⟨m, M, rfl, Or.inr ⟨k, cM, hce.2.2.2.1, rfl⟩⟩, ?_, ?_⟩
                  · exact (index_lt_index (b := x % universeSize d) hce.2.1 hp.2.1).trans_eq hx.symm
                  · intro z hz hzx
                    obtain ⟨m', M', hb', hz⟩ := hz
                    cases hb'
                    rcases hz with rfl | ⟨l, a, ha, rfl⟩
                    · exact (ht.2.2.2.2 k cM hce.2.2.2.1).le
                    · have hli := hearlier l a ha hzx
                      have hlk := hp.2.2 l.val (hoc l a ha) hli
                      by_cases hlk' : l = k
                      · subst l
                        exact Nat.add_le_add_left (hce.2.2.2.2 a ha).2
                          (k.val * universeSize d)
                      · have hlt : l.val < k.val := by
                          have : l.val ≠ k.val := fun h => hlk' (Fin.ext h)
                          change l.val < j
                          change l.val ≠ j at this
                          omega
                        exact (index_lt_index ((ht.2.2.1 l).contains_lt ha) hlt).le

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

end Cslib.Algorithms.Lean.VanEmdeBoas.Tree
