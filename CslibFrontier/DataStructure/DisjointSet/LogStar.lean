/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.DisjointSet.UnionFind
public import CslibFrontier.DataStructure.StateTransition.Amortized
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
  sorry

end RankCount

@[expose] def block (rank : ℕ) : ℕ := Nat.logStar rank

@[expose] def nodeCredit (uf : Batteries.UnionFind) (x : Fin uf.size) : ℕ :=
  if uf.parent x.1 = x.1 then 0 else
    let b := block (uf.rank (uf.parent x.1))
    if block (uf.rank x.1) = b then
      Nat.twoTower b - uf.rank (uf.parent x.1)
    else 0

@[expose] def nodeCreditSum (uf : Batteries.UnionFind) : ℕ :=
  ((List.finRange uf.size).map (fun x => nodeCredit uf x)).sum

@[expose] def nonRootInBlock (uf : Batteries.UnionFind) (b : ℕ) : Finset (Fin uf.size) :=
  Finset.filter (fun x => uf.parent x.1 ≠ x.1 ∧ block (uf.rank x.1) = b) Finset.univ

@[expose] def blockBudget (uf : Batteries.UnionFind) : ℕ → ℕ
  | 0 => 2 * uf.size - 2 * (nonRootInBlock uf 0).card
  | b + 1 => 2 * uf.size - Nat.twoTower (b + 1) * (nonRootInBlock uf (b + 1)).card

@[expose] def potential (uf : Batteries.UnionFind) : ℕ :=
  nodeCreditSum uf + ((List.range (Nat.logStar uf.size + 2)).map (fun b => blockBudget uf b)).sum

theorem amortizedBound (n : ℕ) :
    Cslib.DataStructure.Amortized (impl n) id (fun _ c => potential c.uf) (fun _ _ => 2 * Nat.logStar n + 3) := by
  sorry

end Cslib.DataStructure.DisjointSet.UnionFind
