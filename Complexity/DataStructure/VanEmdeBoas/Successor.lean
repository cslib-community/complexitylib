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

private theorem index_lt_index {u i j a b : ℕ} (ha : a < u) (hij : i < j) :
    i * u + a < j * u + b := by
  have h := Nat.mul_le_mul_right u (show i + 1 ≤ j by omega)
  nlinarith

private theorem bounds_isSome_of_contains {d : ℕ} {t : Tree d} {x : ℕ}
    (hx : t.Contains x) : t.bounds.isSome = true := by
  cases hb : t.bounds with
  | none => exact False.elim (not_contains_of_bounds_none hb x hx)
  | some b => rfl

private theorem maximum_any_iff {d x : ℕ} {t : Tree d} :
    t.maximum.any (x < ·) = true ↔ ∃ m M, t.bounds = some (m, M) ∧ x < M := by
  cases hb : t.bounds with
  | none => simp [maximum, hb]
  | some b => obtain ⟨m, M⟩ := b; simp [maximum, hb]

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
        have he := ht.extrema
        simp only [Extrema, bounds] at he
        by_cases hm : x < m
        · rw [successor, ite_eq_left hm]
          exact ⟨he.2.2.1, hm, fun z hz _ => (he.2.2.2.2 z hz).1⟩
        · by_cases hM : x < M
          · rw [successor, ite_eq_right hm, ite_eq_left hM]
            refine ⟨he.2.2.2.1, hM, ?_⟩
            intro z hz hxz
            obtain ⟨m', M', hb, hz⟩ := hz
            cases hb
            rcases hz with rfl | rfl <;> omega
          · rw [successor, ite_eq_right hm, ite_eq_right hM]
            intro z hz
            have := (he.2.2.2.2 z hz).2
            omega
  | succ d ih =>
    cases t with
    | node b s c =>
      cases b with
      | none => simp [successor, Contains]
      | some b =>
        obtain ⟨m, M⟩ := b
        have he := ht.extrema
        simp only [Extrema, bounds] at he
        by_cases hm : x < m
        · rw [successor, ite_eq_left hm]
          exact ⟨he.2.2.1, hm, fun z hz _ => (he.2.2.2.2 z hz).1⟩
        · by_cases hM : M ≤ x
          · rw [successor, ite_eq_right hm, ite_eq_left hM]
            intro z hz
            exact ((he.2.2.2.2 z hz).2).trans hM
          · have hi : x / universeSize d < universeSize d := by
              apply (Nat.div_lt_iff_lt_mul (universeSize_pos d)).mpr
              exact (show x < M by omega).trans he.2.1
            let i : Fin (universeSize d) := ⟨x / universeSize d, hi⟩
            have hx : x = i.val * universeSize d + x % universeSize d := by
              simpa only [i, Nat.mul_comm] using (Nat.div_add_mod x (universeSize d)).symm
            have hoc : ∀ j y, (c j).Contains y → s.Contains j.val := by
              intro j y hy
              exact (ht.2.2.2.1 j).mpr (bounds_isSome_of_contains hy)
            rw [successor, ite_eq_right hm, ite_eq_right hM, dite_eq_left hi]
            by_cases hc : (c i).maximum.any (x % universeSize d < ·) = true
            · rw [ite_eq_left hc]
              have hs := ih (ht.2.2.1 i) (x % universeSize d)
              cases hsuc : (c i).successor (x % universeSize d) with
              | none =>
                simp only [hsuc] at hs
                obtain ⟨cm, cM, hb, hlt⟩ := maximum_any_iff.mp hc
                have := hs cM ((ht.2.2.1 i).contains_maximum hb)
                omega
              | some y =>
                simp only [hsuc] at hs
                simp only [Option.map_some]
                refine ⟨⟨m, M, rfl, Or.inr ⟨i, y, hs.1, rfl⟩⟩, ?_, ?_⟩
                · exact hx.trans_lt (Nat.add_lt_add_left hs.2.1 (i.val * universeSize d))
                · intro z hz hxz
                  obtain ⟨m', M', hb, hz⟩ := hz
                  cases hb
                  rcases hz with rfl | ⟨j, a, ha, rfl⟩
                  · omega
                  · have hja := cluster_coordinates (i := j.val) (universeSize_pos d)
                      ((ht.2.2.1 j).contains_lt ha)
                    have hij : i.val ≤ j.val := by
                      have h := Nat.div_le_div_right (c := universeSize d) (Nat.le_of_lt hxz)
                      simpa only [i, hja.1] using h
                    by_cases hij' : i = j
                    · subst j
                      have hlow : x % universeSize d < a := by omega
                      exact Nat.add_le_add_left (hs.2.2 a ha hlow) (i.val * universeSize d)
                    · have hlt : i.val < j.val := by
                        have : i.val ≠ j.val := fun h => hij' (Fin.ext h)
                        omega
                      exact (index_lt_index ((ht.2.2.1 i).contains_lt hs.1) hlt).le
            · rw [ite_eq_right hc]
              have hle : ∀ a, (c i).Contains a → a ≤ x % universeSize d := by
                intro a ha
                have hce := (ht.2.2.1 i).extrema
                cases hb : (c i).bounds with
                | none => exact False.elim (not_contains_of_bounds_none hb a ha)
                | some b =>
                  obtain ⟨cm, cM⟩ := b
                  simp only [Extrema, hb] at hce
                  have hn : ¬x % universeSize d < cM := by
                    intro hlt
                    exact hc (maximum_any_iff.mpr ⟨cm, cM, hb, hlt⟩)
                  have := (hce.2.2.2.2 a ha).2
                  omega
              have hlater : ∀ j a, (c j).Contains a →
                  x < j.val * universeSize d + a → i.val < j.val := by
                intro j a ha hxa
                have hja := cluster_coordinates (i := j.val) (universeSize_pos d)
                  ((ht.2.2.1 j).contains_lt ha)
                have hij : i.val ≤ j.val := by
                  have h := Nat.div_le_div_right (c := universeSize d) (Nat.le_of_lt hxa)
                  simpa only [i, hja.1] using h
                by_contra hn
                have hij' : i = j := Fin.ext (by omega)
                subst j
                have := hle a ha
                omega
              have hs := ih ht.2.1 i.val
              cases hsuc : s.successor i.val with
              | none =>
                simp only [hsuc] at hs
                simp only [bind, Option.bind_none]
                intro z hz
                obtain ⟨m', M', hb, hz⟩ := hz
                cases hb
                rcases hz with rfl | ⟨j, a, ha, rfl⟩
                · omega
                · by_contra hn
                  have := hlater j a ha (by omega)
                  have := hs j.val (hoc j a ha)
                  omega
              | some j =>
                simp only [hsuc] at hs
                have hj := ht.2.1.contains_lt hs.1
                let k : Fin (universeSize d) := ⟨j, hj⟩
                have hk : (c k).bounds.isSome = true := (ht.2.2.2.1 k).mp hs.1
                cases hb : (c k).bounds with
                | none => simp [hb] at hk
                | some b =>
                  obtain ⟨cm, cM⟩ := b
                  have hce := (ht.2.2.1 k).extrema
                  simp only [Extrema, hb] at hce
                  simp only [bind, Option.bind_some]
                  rw [dite_eq_left hj, minimum, hb]
                  simp only [Option.map_some]
                  refine ⟨⟨m, M, rfl, Or.inr ⟨k, cm, hce.2.2.1, rfl⟩⟩, ?_, ?_⟩
                  · rw [hx]
                    exact index_lt_index (Nat.mod_lt _ (universeSize_pos d)) hs.2.1
                  · intro z hz hxz
                    obtain ⟨m', M', hb', hz⟩ := hz
                    cases hb'
                    rcases hz with rfl | ⟨l, a, ha, rfl⟩
                    · omega
                    · have hil := hlater l a ha hxz
                      have hjl := hs.2.2 l.val (hoc l a ha) hil
                      by_cases hkl : k = l
                      · subst l
                        exact Nat.add_le_add_left (hce.2.2.2.2 a ha).1
                          (k.val * universeSize d)
                      · have hlt : k.val < l.val := by
                          have : k.val ≠ l.val := fun h => hkl (Fin.ext h)
                          change j < l.val
                          change j ≠ l.val at this
                          omega
                        exact (index_lt_index ((ht.2.2.1 k).contains_lt hce.2.2.1) hlt).le

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
