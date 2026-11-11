/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.DisjointSet.UnionFind
public import CslibFrontier.Foundations.Data.Nat.LogStar

public section

namespace Cslib.DataStructure.DisjointSet.UnionFind

@[expose] def RankCount (uf : Batteries.UnionFind) : Prop :=
  ∀ ⦃r a : ℕ⦄, r < uf.size → uf.parent r = r →
    2 ^ a * ((equivClass uf r).filter (fun x => a ≤ uf.rank x)).card ≤ 2 * (equivClass uf r).card

namespace RankCount

private theorem unionFind_ext {u v : Batteries.UnionFind} (h : u.arr = v.arr) : u = v := by
  cases u; cases v; cases h; rfl

private theorem rank_link (uf : Batteries.UnionFind) (x y : Fin uf.size)
    (hy : uf.parent y.1 = y.1) (i : ℕ) :
    (uf.link x y hy).rank i =
      if x.1 ≠ y.1 ∧ uf.rank x.1 = uf.rank y.1 ∧ y.1 = i then
        uf.rank y.1 + 1
      else
        uf.rank i := by
  simp only [Batteries.UnionFind.rank, Batteries.UnionFind.arr_link, Batteries.UnionFind.linkAux]
  by_cases hxy : x.1 = y.1
  · simp [hxy]
  · simp only [hxy, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
    have hrx : Batteries.UnionFind.rankD uf.arr x.1 = uf.arr[x.1].rank :=
      Batteries.UnionFind.rankD_eq x.2
    have hry : Batteries.UnionFind.rankD uf.arr y.1 = uf.arr[y.1].rank :=
      Batteries.UnionFind.rankD_eq y.2
    rw [hrx, hry]
    by_cases hlt : uf.arr[y.1].rank < uf.arr[x.1].rank
    · have hne_rk : uf.arr[x.1].rank ≠ uf.arr[y.1].rank := Nat.ne_of_gt hlt
      simp only [hlt, ↓reduceIte, hne_rk, false_and, Batteries.UnionFind.rankD_set]
      by_cases hyi : y.1 = i
      · subst hyi
        simp [hry]
      · simp [hyi]
    · simp only [hlt, ↓reduceIte]
      by_cases heq_rk : uf.arr[x.1].rank = uf.arr[y.1].rank
      · simp only [heq_rk, ↓reduceIte, true_and, Batteries.UnionFind.rankD_set]
        by_cases hyi : y.1 = i
        · simp [hyi]
        · simp only [hyi, ↓reduceIte]
          by_cases hxi : x.1 = i
          · subst hxi
            simp [heq_rk, hrx]
          · simp [hxi]
      · simp only [heq_rk, ↓reduceIte, false_and, Batteries.UnionFind.rankD_set]
        by_cases hxi : x.1 = i
        · subst hxi
          simp [hrx]
        · simp [hxi]

theorem link {uf : Batteries.UnionFind} (h : RankCount uf) (h_valid : ValidRank uf) {x y : Fin uf.size}
    (hx : uf.parent x.1 = x.1) (hy : uf.parent y.1 = y.1) :
    RankCount (uf.link x y hy) := by
  intro r a hr hp'
  have hsize : (uf.link x y hy).size = uf.size := by simp [Batteries.UnionFind.size]
  rw [hsize] at hr
  by_cases hxy : x.1 = y.1
  · have heq : uf.link x y hy = uf := by
      apply unionFind_ext
      simp [Batteries.UnionFind.linkAux, hxy]
    rw [heq] at hp' ⊢
    exact h hr hp'
  · obtain ⟨r₀, hr₀, hroot⟩ := Batteries.UnionFind.root_link hx hy
    have hx_rootD : uf.rootD x.1 = x.1 := Batteries.UnionFind.rootD_eq_self.mpr hx
    have hr₀_eq : (uf.link x y hy).rootD x.1 = r₀.1 := by
      simpa [hx_rootD] using hroot x.1
    have hr₀_parent : (uf.link x y hy).parent r₀.1 = r₀.1 := by
      rw [← hr₀_eq]
      exact Batteries.UnionFind.parent_rootD _ _
    by_cases hlt : uf.rank y.1 < uf.rank x.1
    · have hparent : ∀ i, (uf.link x y hy).parent i = if y.1 = i then x.1 else uf.parent i := by
        intro i
        rw [Batteries.UnionFind.parent_link hy]
        simp [hxy, hlt]
      have hy_not_root : (uf.link x y hy).parent y.1 ≠ y.1 := by
        rw [hparent y.1, ite_eq_left rfl]
        exact hxy
      have hr₀_x : r₀ = x := by
        rcases hr₀ with hrx | hry
        · exact hrx
        · rw [hry] at hr₀_parent
          exact absurd hr₀_parent hy_not_root
      rw [hr₀_x] at hroot
      have hyr : y.1 ≠ r := fun heq => by
        rw [← heq] at hp'
        exact hy_not_root hp'
      have hp : uf.parent r = r := by
        have hp₁ := hp'
        rw [hparent r, ite_eq_right hyr] at hp₁
        exact hp₁
      have hrank : ∀ i, (uf.link x y hy).rank i = uf.rank i := by
        intro i
        rw [rank_link]
        split
        · next hcond =>
          obtain ⟨_, heq_rk, hyr'⟩ := hcond
          exact absurd heq_rk (ne_of_gt hlt)
        · rfl
      have heq_class : equivClass (uf.link x y hy) r = if r = x.1 then equivClass uf x.1 ∪ equivClass uf y.1 else equivClass uf r := by
        ext i
        simp only [mem_equivClass, hsize, Finset.mem_union, ite_eq_left_iff]
        by_cases hxr : r = x.1
        · simp [hxr, hroot]
        · simp [hxr, hroot]
          constructor
          · intro h
            exact h
          · intro h
            by_cases hyi : uf.rootD i = y.1
            · rw [hyi] at h
              exact absurd h (Ne.symm hxr)
            · exact h
      by_cases hxr : r = x.1
      · rw [hxr] at hp heq_class ⊢
        rw [heq_class, if_pos rfl]
        have h_filter_eq : ((equivClass uf x.1 ∪ equivClass uf y.1).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                           ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ∪
                           ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_union]
          rw [hrank i]
          tauto
        rw [h_filter_eq]
        have h_disj : Disjoint (equivClass uf x.1) (equivClass uf y.1) := disjoint_equivClass_of_ne uf hxy
        have h_disj_filter : Disjoint ((equivClass uf x.1).filter (fun z => a ≤ uf.rank z)) ((equivClass uf y.1).filter (fun z => a ≤ uf.rank z)) :=
          Finset.disjoint_filter_filter h_disj
        rw [Finset.card_union_of_disjoint h_disj_filter, Finset.card_union_of_disjoint h_disj, mul_add, mul_add]
        exact Nat.add_le_add (h hr hp) (h y.2 hy)
      · rw [heq_class, if_neg hxr]
        have h_filter_eq : ((equivClass uf r).filter (fun z => a ≤ (uf.link x y hy).rank z)) =
                           ((equivClass uf r).filter (fun z => a ≤ uf.rank z)) := by
          ext i
          simp only [Finset.mem_filter]
          rw [hrank i]
        rw [h_filter_eq]
        exact h hr hp
    · sorry
end RankCount
end Cslib.DataStructure.DisjointSet.UnionFind
