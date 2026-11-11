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
import all Batteries.Data.UnionFind.Basic

/-!
# Iterated-logarithm amortized bound for union-find

This module establishes the `O(log* n)` per-operation amortized step bound for
`Cslib.DataStructure.DisjointSet.UnionFind.impl` using the Hopcroft–Ullman block potential function.

## Main definitions

* `block`, `nodeCredit`, `nodeCreditSum`, `nonRootInBlock`, `blockBudget`, `potential`:
  the block-tower potential function over `Batteries.UnionFind`.

## Main results

* `compressWithSteps_potential_tight`, `compressWithSteps_potential`: path-compression potential
  step bounds.
* `link_potential`: root-link potential bound.
* `amortizedBound`: uniform `2 * Nat.logStar n + 3` per-operation amortized certificate for
  `impl n`.
-/

public section

namespace Cslib.DataStructure.DisjointSet.UnionFind

@[expose] def block (rank : ℕ) : ℕ := Nat.logStar rank

@[expose] def nodeCredit (uf : Batteries.UnionFind) (x : Fin uf.size) : ℕ :=
  if uf.parent x.1 = x.1 then 0 else
    let b := block (uf.rank (uf.parent x.1))
    if block (uf.rank x.1) = b then
      Nat.twoTower b + 1 - uf.rank (uf.parent x.1)
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

namespace CompressPotential

private def nodeCreditAt (uf : Batteries.UnionFind) (i : ℕ) : ℕ :=
  if uf.parent i = i then 0 else
    let b := block (uf.rank (uf.parent i))
    if block (uf.rank i) = b then
      Nat.twoTower b + 1 - uf.rank (uf.parent i)
    else 0

private theorem nodeCreditSum_eq_sum_range (uf : Batteries.UnionFind) :
    nodeCreditSum uf = ((List.range uf.size).map (nodeCreditAt uf)).sum := by
  unfold nodeCreditSum
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  rfl

private theorem sum_range_swap {f g : ℕ → ℕ} :
    ∀ {n k : ℕ}, k < n → (∀ i, i ≠ k → f i = g i) →
      ((List.range n).map f).sum + g k = ((List.range n).map g).sum + f k
  | 0, _, hk, _ => by omega
  | n + 1, k, hk, hfg => by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt | rfl
    · have ih := sum_range_swap hlt hfg
      have hn : f n = g n := hfg n (Nat.ne_of_gt hlt)
      omega
    · have hmap : List.map f (List.range k) = List.map g (List.range k) := by
        refine List.map_congr_left fun i hi => hfg i (Nat.ne_of_lt (List.mem_range.mp hi))
      rw [hmap]
      omega

private theorem find_parent_eq_self_iff (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (uf.find x).1.parent i = i ↔ uf.parent i = i := by
  rw [← Batteries.UnionFind.rootD_eq_self, ← Batteries.UnionFind.rootD_eq_self,
    Batteries.UnionFind.find_root_1]

private theorem card_nonRootInBlock_find (uf : Batteries.UnionFind) (x : Fin uf.size) (b : ℕ) :
    (nonRootInBlock (uf.find x).1 b).card = (nonRootInBlock uf b).card := by
  have hsz : (uf.find x).1.size = uf.size := Batteries.UnionFind.find_size uf x
  refine Finset.card_bij (fun z _ => z.cast hsz) (fun z hz => ?_)
    (fun z₁ _ z₂ _ h => Fin.ext (by simpa using congrArg Fin.val h)) (fun z hz => ?_)
  · simp only [nonRootInBlock, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_cast,
      ne_eq] at hz ⊢
    rwa [find_parent_eq_self_iff, find_rank] at hz
  · refine ⟨z.cast hsz.symm, ?_, by simp⟩
    simp only [nonRootInBlock, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_cast,
      ne_eq] at hz ⊢
    rwa [find_parent_eq_self_iff, find_rank]

theorem blockBudget_find (uf : Batteries.UnionFind) (x : Fin uf.size) (b : ℕ) :
    blockBudget (uf.find x).1 b = blockBudget uf b := by
  cases b <;> simp [blockBudget, card_nonRootInBlock_find]

private theorem find_parent_eq_ite (uf : Batteries.UnionFind) (x : Fin uf.size) (i : ℕ) :
    (uf.find x).1.parent i =
      if i = x.1 then uf.rootD x.1
      else (uf.find ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩).1.parent i :=
  Batteries.UnionFind.parentD_findAux

private theorem find_parent_of_root (uf : Batteries.UnionFind) (x : Fin uf.size)
    (hx : uf.arr[x.1].parent = x.1) (i : ℕ) :
    (uf.find x).1.parent i = uf.parent i := by
  change Batteries.UnionFind.parentD (uf.findAux x).s i = uf.parent i
  rw [Batteries.UnionFind.findAux_s, ite_eq_left hx]

private theorem find_parent_of_rank_lt (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (z : Fin uf.size) {i : ℕ},
      uf.rankMax - uf.rank z.1 ≤ fuel →
      uf.rank i < uf.rank z.1 →
      (uf.find z).1.parent i = uf.parent i
  | 0, z, _, _, _ => by
    have := uf.lt_rankMax z.1
    omega
  | fuel + 1, z, i, _, hlt => by
    by_cases hz : uf.arr[z.1].parent = z.1
    · exact find_parent_of_root uf z hz i
    · rw [find_parent_eq_ite]
      have hne : i ≠ z.1 := fun h => by subst h; exact Nat.lt_irrefl _ hlt
      rw [ite_eq_right hne]
      let z' : Fin uf.size := ⟨uf.arr[z.1].parent, uf.parent'_lt z.1 z.2⟩
      have hrank : uf.rank z.1 < uf.rank z'.1 := uf.rank'_lt z.1 z.2 hz
      have hmax := uf.lt_rankMax z.1
      exact find_parent_of_rank_lt uf fuel z' (by omega) (Nat.lt_trans hlt hrank)

private theorem nodeCreditAt_congr {u v : Batteries.UnionFind} {i : ℕ}
    (hp : u.parent i = v.parent i) (hr : ∀ k, u.rank k = v.rank k) :
    nodeCreditAt u i = nodeCreditAt v i := by
  simp only [nodeCreditAt, hp, hr]

theorem nodeCreditSum_find_add_findSteps (uf : Batteries.UnionFind) :
    ∀ (fuel : ℕ) (x : Fin uf.size),
      uf.rankMax - uf.rank x.1 ≤ fuel →
      nodeCreditSum (uf.find x).1 + findSteps uf x ≤
        nodeCreditSum uf +
          (block (uf.rank (uf.rootD x.1)) - block (uf.rank x.1) +
            if uf.parent x.1 = x.1 then 1 else 2)
  | 0, x, _ => by
    have := uf.lt_rankMax x.1
    omega
  | fuel + 1, x, _ => by
    by_cases hx_arr : uf.arr[x.1].parent = x.1
    · have hx : uf.parent x.1 = x.1 := by
        rw [Batteries.UnionFind.parent, Batteries.UnionFind.parentD_eq x.2, hx_arr]
      have hsteps : findSteps uf x = 1 := by
        rw [findSteps_eq, ite_eq_left hx_arr]
      have hsum : nodeCreditSum (uf.find x).1 = nodeCreditSum uf := by
        rw [nodeCreditSum_eq_sum_range, nodeCreditSum_eq_sum_range, Batteries.UnionFind.find_size]
        refine congrArg List.sum (List.map_congr_left fun i _ => ?_)
        exact nodeCreditAt_congr (find_parent_of_root uf x hx_arr i) (find_rank uf x)
      rw [hsum, hsteps, ite_eq_left hx]
      omega
    · have hx : uf.parent x.1 ≠ x.1 := by
        rw [Batteries.UnionFind.parent, Batteries.UnionFind.parentD_eq x.2]
        exact hx_arr
      let y : Fin uf.size := ⟨uf.arr[x.1].parent, uf.parent'_lt x.1 x.2⟩
      have hy_eq : y.1 = uf.parent x.1 := (Batteries.UnionFind.parentD_eq x.2).symm
      have hrank : uf.rank x.1 < uf.rank y.1 := uf.rank'_lt x.1 x.2 hx_arr
      have hmax := uf.lt_rankMax x.1
      have hroot : uf.rootD y.1 = uf.rootD x.1 := by
        rw [hy_eq, Batteries.UnionFind.rootD_parent]
      have hsteps : findSteps uf x = findSteps uf y + 1 := by
        rw [findSteps_eq, ite_eq_right hx_arr]
      have ih := nodeCreditSum_find_add_findSteps uf fuel y (by omega)
      rw [hroot] at ih
      have hswap :
          nodeCreditSum (uf.find x).1 + nodeCreditAt uf x.1 =
            nodeCreditSum (uf.find y).1 + nodeCreditAt (uf.find x).1 x.1 := by
        rw [nodeCreditSum_eq_sum_range (uf.find x).1, nodeCreditSum_eq_sum_range (uf.find y).1,
          Batteries.UnionFind.find_size, Batteries.UnionFind.find_size]
        have hx_y : nodeCreditAt (uf.find y).1 x.1 = nodeCreditAt uf x.1 := by
          refine nodeCreditAt_congr ?_ (find_rank uf y)
          exact find_parent_of_rank_lt uf (uf.rankMax - uf.rank y.1) y (Nat.le_refl _) hrank
        rw [← hx_y]
        refine sum_range_swap x.2 fun i hi => ?_
        refine nodeCreditAt_congr ?_ (fun k => by rw [find_rank, find_rank])
        rw [find_parent_eq_ite, ite_eq_right hi]
      have hmono₁ : block (uf.rank x.1) ≤ block (uf.rank y.1) :=
        Nat.logStar_mono (Nat.le_of_lt hrank)
      have hmono₂ : block (uf.rank y.1) ≤ block (uf.rank (uf.rootD x.1)) := by
        rw [← hroot]
        exact Nat.logStar_mono Batteries.UnionFind.le_rank_root
      by_cases hpy : uf.parent y.1 = y.1
      · have hroot_eq : uf.rootD x.1 = y.1 := by
          rw [← hroot, Batteries.UnionFind.rootD_eq_self.mpr hpy]
        have hx_same : nodeCreditAt (uf.find x).1 x.1 = nodeCreditAt uf x.1 := by
          refine nodeCreditAt_congr ?_ (find_rank uf x)
          rw [Batteries.UnionFind.find_parent_1, hroot_eq, hy_eq]
        rw [ite_eq_left hpy] at ih
        rw [ite_eq_right hx, hsteps]
        omega
      · rw [ite_eq_right hpy] at ih
        rw [ite_eq_right hx, hsteps]
        have hlt_root : uf.rank y.1 < uf.rank (uf.rootD x.1) := by
          rw [← hroot]
          exact Batteries.UnionFind.lt_rank_root.mpr hpy
        by_cases hb : block (uf.rank x.1) = block (uf.rank y.1)
        · have hle_tower : uf.rank y.1 ≤ Nat.twoTower (block (uf.rank y.1)) :=
            Nat.le_twoTower_logStar (uf.rank y.1)
          have hcred_uf :
              nodeCreditAt uf x.1 = Nat.twoTower (block (uf.rank y.1)) + 1 - uf.rank y.1 := by
            unfold nodeCreditAt
            rw [ite_eq_right hx, ← hy_eq, ite_eq_left hb]
          have hcred_fx :
              nodeCreditAt (uf.find x).1 x.1 + 1 ≤ nodeCreditAt uf x.1 := by
            have hfx_ne : (uf.find x).1.parent x.1 ≠ x.1 := by
              rwa [ne_eq, find_parent_eq_self_iff]
            rw [hcred_uf]
            unfold nodeCreditAt
            rw [ite_eq_right hfx_ne, Batteries.UnionFind.find_parent_1,
              find_rank, find_rank, hb]
            dsimp only
            split
            · next hbr =>
              rw [← hbr]
              omega
            · omega
          omega
        · have hlt_block : block (uf.rank x.1) < block (uf.rank y.1) :=
            Nat.lt_of_le_of_ne hmono₁ hb
          have hcred_uf : nodeCreditAt uf x.1 = 0 := by
            unfold nodeCreditAt
            rw [ite_eq_right hx, ← hy_eq, ite_eq_right hb]
          have hcred_fx : nodeCreditAt (uf.find x).1 x.1 = 0 := by
            have hfx_ne : (uf.find x).1.parent x.1 ≠ x.1 := by
              rwa [ne_eq, find_parent_eq_self_iff]
            have hne_root : block (uf.rank x.1) ≠ block (uf.rank (uf.rootD x.1)) :=
              Nat.ne_of_lt (Nat.lt_of_lt_of_le hlt_block hmono₂)
            unfold nodeCreditAt
            rw [ite_eq_right hfx_ne, Batteries.UnionFind.find_parent_1,
              find_rank, find_rank]
            dsimp only
            rw [ite_eq_right hne_root]
          omega

end CompressPotential

theorem compressWithSteps_potential_tight {uf : Batteries.UnionFind} (h : ValidRank uf)
    (_hc : RankCount uf) (x : Fin uf.size) :
    potential (compressWithSteps uf x).1 + findSteps uf x ≤
      potential uf + (Nat.logStar uf.size + 1) := by
  rw [compressWithSteps_fst]
  unfold potential
  have hbudget :
      ((List.range (Nat.logStar (uf.find x).1.size + 2)).map
        (fun b => blockBudget (uf.find x).1 b)).sum =
        ((List.range (Nat.logStar uf.size + 2)).map (fun b => blockBudget uf b)).sum := by
    rw [Batteries.UnionFind.find_size]
    refine congrArg List.sum
      (List.map_congr_left fun b _ => CompressPotential.blockBudget_find uf x b)
  have hcred :=
    CompressPotential.nodeCreditSum_find_add_findSteps uf
      (uf.rankMax - uf.rank x.1) x (Nat.le_refl _)
  by_cases hx : uf.parent x.1 = x.1
  · have hroot : uf.rootD x.1 = x.1 := Batteries.UnionFind.rootD_eq_self.mpr hx
    rw [hroot, ite_eq_left hx] at hcred
    omega
  · rw [ite_eq_right hx] at hcred
    have hlt_rk : 0 < uf.rank (uf.rootD x.1) :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) (Batteries.UnionFind.lt_rank_root.mpr hx)
    have hpow_le : 2 ^ uf.rank (uf.rootD x.1) ≤ uf.size :=
      h.two_pow_rank_le_size (Batteries.UnionFind.rootD_lt.mpr x.2)
    have hsize_ge : 2 ≤ uf.size :=
      (Nat.pow_le_pow_right (by decide) hlt_rk).trans hpow_le
    have hpow_clog : uf.size ≤ 2 ^ Nat.clog 2 uf.size :=
      Nat.le_pow_clog (by decide) uf.size
    have hrk_le_clog : uf.rank (uf.rootD x.1) ≤ Nat.clog 2 uf.size :=
      (Nat.pow_le_pow_iff_right (by decide)).mp (hpow_le.trans hpow_clog)
    have hblock_le : block (uf.rank (uf.rootD x.1)) ≤ Nat.logStar (Nat.clog 2 uf.size) :=
      Nat.logStar_mono hrk_le_clog
    have hlogstar : Nat.logStar uf.size = Nat.logStar (Nat.clog 2 uf.size) + 1 :=
      Nat.logStar_of_two_le hsize_ge
    omega

theorem compressWithSteps_potential {uf : Batteries.UnionFind} (h : ValidRank uf)
    (hc : RankCount uf) (x : Fin uf.size) :
    potential (compressWithSteps uf x).1 + findSteps uf x ≤
      potential uf + (Nat.logStar uf.size + 2) := by
  have := compressWithSteps_potential_tight h hc x
  omega

namespace LinkPotential

private def nodeCreditNat (uf : Batteries.UnionFind) (i : ℕ) : ℕ :=
  if uf.parent i = i then 0 else
    let b := block (uf.rank (uf.parent i))
    if block (uf.rank i) = b then
      Nat.twoTower b + 1 - uf.rank (uf.parent i)
    else 0

private def nonRootInBlockNat (uf : Batteries.UnionFind) (b : ℕ) : Finset ℕ :=
  (Finset.range uf.size).filter (fun i => uf.parent i ≠ i ∧ block (uf.rank i) = b)

private theorem sum_map_le {α : Type*} {l : List α} (f g : α → ℕ)
    (hle : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, List.sum_cons]
    have ha := hle a List.mem_cons_self
    have ht := ih (fun x hx => hle x (List.mem_cons_of_mem a hx))
    omega

private theorem sum_map_add_le_of_mem {α : Type*} [DecidableEq α] {l : List α} (hnodup : l.Nodup)
    {k : α} (hk : k ∈ l) (f g : α → ℕ) (hle : ∀ x ∈ l, x ≠ k → f x ≤ g x) :
    (l.map f).sum + g k ≤ (l.map g).sum + f k := by
  induction l with
  | nil => cases hk
  | cons a t ih =>
    rw [List.nodup_cons] at hnodup
    obtain ⟨hat, htnodup⟩ := hnodup
    simp only [List.map_cons, List.sum_cons]
    by_cases hka : k = a
    · subst hka
      have ht : (t.map f).sum ≤ (t.map g).sum := by
        refine sum_map_le f g (fun x hx => hle x (List.mem_cons_of_mem k hx) ?_)
        rintro rfl
        exact hat hx
      omega
    · have hkt : k ∈ t := by
        rcases List.mem_cons.mp hk with rfl | hkt
        · exact absurd rfl hka
        · exact hkt
      have ha : f a ≤ g a := hle a List.mem_cons_self (Ne.symm hka)
      have ht := ih htnodup hkt (fun x hx hxk => hle x (List.mem_cons_of_mem a hx) hxk)
      omega

private theorem map_val_finRange (n : ℕ) : (List.finRange n).map Fin.val = List.range n := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

private theorem nodeCreditSum_eq_range (uf : Batteries.UnionFind) :
    nodeCreditSum uf = ((List.range uf.size).map (nodeCreditNat uf)).sum := by
  unfold nodeCreditSum
  have h1 : (List.finRange uf.size).map (fun x => nodeCredit uf x) =
      ((List.finRange uf.size).map Fin.val).map (nodeCreditNat uf) := by
    rw [List.map_map]
    rfl
  rw [h1, map_val_finRange]

private theorem card_nonRootInBlock_eq (uf : Batteries.UnionFind) (b : ℕ) :
    (nonRootInBlock uf b).card = (nonRootInBlockNat uf b).card := by
  have hmap : (nonRootInBlock uf b).map ⟨Fin.val, Fin.val_injective⟩ = nonRootInBlockNat uf b := by
    ext i
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, nonRootInBlock, Finset.mem_filter,
      Finset.mem_univ, true_and, nonRootInBlockNat, Finset.mem_range]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hi, hx⟩
      exact ⟨⟨i, hi⟩, hx, rfl⟩
  rw [← hmap, Finset.card_map]

private theorem blockBudget_eq_nat (uf : Batteries.UnionFind) (b : ℕ) :
    blockBudget uf b =
      match b with
      | 0 => 2 * uf.size - 2 * (nonRootInBlockNat uf 0).card
      | k + 1 => 2 * uf.size - Nat.twoTower (k + 1) * (nonRootInBlockNat uf (k + 1)).card := by
  cases b <;> simp [blockBudget, card_nonRootInBlock_eq]

private theorem mul_card_filter_roots_le {uf : Batteries.UnionFind} (hc : RankCount uf)
    (a : ℕ) (R : Finset ℕ) (hR : ∀ r ∈ R, r < uf.size ∧ uf.parent r = r) :
    2 ^ a * ((Finset.range uf.size).filter (fun i => uf.rootD i ∈ R ∧ a ≤ uf.rank i)).card ≤
      2 * ((Finset.range uf.size).filter (fun i => uf.rootD i ∈ R)).card := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert r R hrR ih =>
    have hr : r < uf.size ∧ uf.parent r = r := hR r (Finset.mem_insert_self r R)
    have hR' : ∀ r' ∈ R, r' < uf.size ∧ uf.parent r' = r' :=
      fun r' hr' => hR r' (Finset.mem_insert_of_mem hr')
    have h_eq1 : (Finset.range uf.size).filter (fun i => uf.rootD i ∈ insert r R) =
        equivClass uf r ∪ (Finset.range uf.size).filter (fun i => uf.rootD i ∈ R) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_union,
        mem_equivClass]
      tauto
    have h_disj1 : Disjoint (equivClass uf r)
        ((Finset.range uf.size).filter (fun i => uf.rootD i ∈ R)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [mem_equivClass] at hi1
      rw [Finset.mem_filter] at hi2
      rw [hi1.2] at hi2
      exact hrR hi2.2
    have h_eq2 : (Finset.range uf.size).filter (fun i => uf.rootD i ∈ insert r R ∧ a ≤ uf.rank i) =
        (equivClass uf r).filter (fun i => a ≤ uf.rank i) ∪
          (Finset.range uf.size).filter (fun i => uf.rootD i ∈ R ∧ a ≤ uf.rank i) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_union,
        mem_equivClass]
      tauto
    have h_disj2 : Disjoint ((equivClass uf r).filter (fun i => a ≤ uf.rank i))
        ((Finset.range uf.size).filter (fun i => uf.rootD i ∈ R ∧ a ≤ uf.rank i)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      rw [Finset.mem_filter, mem_equivClass] at hi1
      rw [Finset.mem_filter] at hi2
      rw [hi1.1.2] at hi2
      exact hrR hi2.2.1
    rw [h_eq1, h_eq2, Finset.card_union_of_disjoint h_disj1,
      Finset.card_union_of_disjoint h_disj2, Nat.mul_add, Nat.mul_add]
    exact Nat.add_le_add (hc hr.1 hr.2) (ih hR')

private theorem mul_card_filter_rank_le {uf : Batteries.UnionFind} (hc : RankCount uf)
    (a : ℕ) :
    2 ^ a * ((Finset.range uf.size).filter (fun i => a ≤ uf.rank i)).card ≤ 2 * uf.size := by
  let R := (Finset.range uf.size).filter (fun r => uf.parent r = r)
  have hR : ∀ r ∈ R, r < uf.size ∧ uf.parent r = r := by
    intro r hr
    simpa [R] using hr
  have h1 : (Finset.range uf.size).filter (fun i => uf.rootD i ∈ R ∧ a ≤ uf.rank i) =
      (Finset.range uf.size).filter (fun i => a ≤ uf.rank i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, R]
    constructor
    · rintro ⟨hi, _, ha⟩
      exact ⟨hi, ha⟩
    · rintro ⟨hi, ha⟩
      exact ⟨hi, ⟨⟨Batteries.UnionFind.rootD_lt.mpr hi, Batteries.UnionFind.parent_rootD uf i⟩, ha⟩⟩
  have h2 : (Finset.range uf.size).filter (fun i => uf.rootD i ∈ R) = Finset.range uf.size := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, R]
    constructor
    · rintro ⟨hi, _⟩
      exact hi
    · intro hi
      exact ⟨hi, Batteries.UnionFind.rootD_lt.mpr hi, Batteries.UnionFind.parent_rootD uf i⟩
  have hle := mul_card_filter_roots_le hc a R hR
  rw [h1, h2, Finset.card_range] at hle
  exact hle

private theorem card_nonRootInBlockNat_succ_le {uf : Batteries.UnionFind}
    (hc : RankCount uf) (k : ℕ) :
    Nat.twoTower (k + 1) * (nonRootInBlockNat uf (k + 1)).card ≤ 2 * uf.size := by
  rw [Nat.twoTower_succ]
  have hsub : nonRootInBlockNat uf (k + 1) ⊆
      (Finset.range uf.size).filter (fun i => Nat.twoTower k ≤ uf.rank i) := by
    intro i hi
    rw [nonRootInBlockNat, Finset.mem_filter, Finset.mem_range] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hi.1, ?_⟩
    by_contra hle
    have hls : Nat.logStar (uf.rank i) ≤ k := Nat.logStar_le_iff.mpr (Nat.le_of_not_le hle)
    have hblk : Nat.logStar (uf.rank i) = k + 1 := hi.2.2
    omega
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans (mul_card_filter_rank_le hc _)

private theorem card_nonRootInBlockNat_zero_le (uf : Batteries.UnionFind) :
    2 * (nonRootInBlockNat uf 0).card ≤ 2 * uf.size := by
  have hsub : nonRootInBlockNat uf 0 ⊆ Finset.range uf.size := Finset.filter_subset _ _
  have hle : (nonRootInBlockNat uf 0).card ≤ uf.size :=
    (Finset.card_le_card hsub).trans (by simp)
  omega

private theorem potential_le_of_link_step {uf uf' : Batteries.UnionFind}
    (h_valid : ValidRank uf) (hc' : RankCount uf')
    {u v : Fin uf.size} (hu : uf.parent u.1 = u.1) (hv : uf.parent v.1 = v.1)
    (huv : u.1 ≠ v.1) (hsize : uf'.size = uf.size)
    (hparent : ∀ i, uf'.parent i = if u.1 = i then v.1 else uf.parent i)
    (hrank_other : ∀ i, i ≠ v.1 → uf'.rank i = uf.rank i)
    (hrank_v : uf.rank v.1 ≤ uf'.rank v.1) :
    potential uf' ≤ potential uf := by
  let bu := block (uf.rank u.1)
  have hrank_u : uf'.rank u.1 = uf.rank u.1 := hrank_other u.1 huv
  have hu_notMem : u.1 ∉ nonRootInBlockNat uf bu := by
    simp [nonRootInBlockNat, hu]
  have h_nrib_eq : ∀ b, nonRootInBlockNat uf' b =
      if b = bu then insert u.1 (nonRootInBlockNat uf bu) else nonRootInBlockNat uf b := by
    intro b
    ext i
    simp only [nonRootInBlockNat, Finset.mem_filter, Finset.mem_range, hsize, hparent]
    by_cases hui : u.1 = i
    · subst hui
      rw [hrank_u]
      simp only [↓reduceIte]
      by_cases hbbu : b = bu
      · subst hbbu
        simp [u.2, hu, bu, Ne.symm huv]
      · simp only [hbbu, ↓reduceIte, Finset.mem_filter, Finset.mem_range, hu, ne_eq,
          not_true_eq_false, false_and, and_false, iff_false]
        rintro ⟨_, _, hblk⟩
        exact hbbu hblk.symm
    · simp only [hui, ↓reduceIte]
      by_cases hvi : i = v.1
      · subst hvi
        by_cases hbbu : b = bu
        · subst hbbu
          simp [hv, Ne.symm huv]
        · simp [hbbu, hv]
      · rw [hrank_other i hvi]
        by_cases hbbu : b = bu
        · subst hbbu
          simp [Ne.symm hui]
        · simp [hbbu]
  have h_card_bu : (nonRootInBlockNat uf' bu).card = (nonRootInBlockNat uf bu).card + 1 := by
    rw [h_nrib_eq bu, ite_eq_left rfl, Finset.card_insert_of_notMem hu_notMem]
  have h_budget_other : ∀ b, b ≠ bu → blockBudget uf' b = blockBudget uf b := by
    intro b hb
    rw [blockBudget_eq_nat, blockBudget_eq_nat, hsize]
    cases b with
    | zero =>
      dsimp only
      rw [h_nrib_eq 0, ite_eq_right hb]
    | succ k =>
      dsimp only
      rw [h_nrib_eq (k + 1), ite_eq_right hb]
  have h_credit_u_uf : nodeCreditNat uf u.1 = 0 := by
    simp [nodeCreditNat, hu]
  have h_credit_u_le : nodeCreditNat uf' u.1 ≤ Nat.twoTower bu := by
    unfold nodeCreditNat
    rw [hrank_u]
    change (if uf'.parent u.1 = u.1 then 0 else
      let b := block (uf'.rank (uf'.parent u.1))
      if bu = b then Nat.twoTower b + 1 - uf'.rank (uf'.parent u.1) else 0) ≤ Nat.twoTower bu
    split
    · exact Nat.zero_le _
    · next hne =>
      have hrk_pos : 0 < uf'.rank (uf'.parent u.1) :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) (Batteries.UnionFind.rank_lt hne)
      dsimp only
      split
      · next hbe =>
        rw [← hbe]
        omega
      · exact Nat.zero_le _
  have h_credit_other : ∀ i, i ≠ u.1 → nodeCreditNat uf' i ≤ nodeCreditNat uf i := by
    intro i hi
    unfold nodeCreditNat
    rw [hparent i, ite_eq_right (Ne.symm hi)]
    by_cases hpi : uf.parent i = i
    · simp [hpi]
    · simp only [hpi, ↓reduceIte]
      have hvi : i ≠ v.1 := by
        rintro rfl
        exact hpi hv
      rw [hrank_other i hvi]
      by_cases hpv : uf.parent i = v.1
      · rw [hpv]
        have hrk_lt : uf.rank i < uf.rank v.1 := by
          rw [← hpv]
          exact Batteries.UnionFind.rank_lt hpi
        have hblk1 : block (uf.rank i) ≤ block (uf.rank v.1) :=
          Nat.logStar_mono (Nat.le_of_lt hrk_lt)
        have hblk2 : block (uf.rank v.1) ≤ block (uf'.rank v.1) :=
          Nat.logStar_mono hrank_v
        split
        · next hbe' =>
          have hbe : block (uf.rank i) = block (uf.rank v.1) := by omega
          rw [ite_eq_left hbe, ← hbe', ← hbe]
          omega
        · exact Nat.zero_le _
      · rw [hrank_other (uf.parent i) hpv]
  have h_budget_bu : blockBudget uf' bu + nodeCreditNat uf' u.1 ≤ blockBudget uf bu := by
    rw [blockBudget_eq_nat, blockBudget_eq_nat]
    cases hbu : bu with
    | zero =>
      dsimp only
      rw [hbu] at h_card_bu h_credit_u_le
      have h_z := card_nonRootInBlockNat_zero_le uf'
      rw [hsize, h_card_bu] at h_z ⊢
      have ht0 : Nat.twoTower 0 = 1 := rfl
      omega
    | succ k =>
      dsimp only
      rw [hbu] at h_card_bu h_credit_u_le
      have h_s := card_nonRootInBlockNat_succ_le hc' k
      rw [hsize, h_card_bu, Nat.mul_add, Nat.mul_one] at h_s ⊢
      omega
  have h_bu_mem : bu ∈ List.range (Nat.logStar uf.size + 2) := by
    rw [List.mem_range]
    have hrk_le : uf.rank u.1 ≤ uf.size :=
      (h_valid.rank_le_log u.1).trans (Nat.log_le_self 2 uf.size)
    have hls_le : bu ≤ Nat.logStar uf.size := Nat.logStar_mono hrk_le
    omega
  have h_u_mem : u.1 ∈ List.range uf.size := List.mem_range.mpr u.2
  have h_sum_credit := sum_map_add_le_of_mem List.nodup_range h_u_mem
    (nodeCreditNat uf') (nodeCreditNat uf) (fun i _ hi => h_credit_other i hi)
  rw [h_credit_u_uf, Nat.add_zero] at h_sum_credit
  have h_sum_budget := sum_map_add_le_of_mem List.nodup_range h_bu_mem
    (fun b => blockBudget uf' b) (fun b => blockBudget uf b)
    (fun b _ hb => (h_budget_other b hb).le)
  unfold potential
  rw [nodeCreditSum_eq_range, nodeCreditSum_eq_range, hsize]
  omega

end LinkPotential

theorem link_potential {uf : Batteries.UnionFind} (h : ValidRank uf) (hc : RankCount uf)
    {x y : Fin uf.size} (hx : uf.parent x.1 = x.1) (hy : uf.parent y.1 = y.1) :
    potential (uf.link x y hy) + 1 ≤ potential uf + 1 := by
  refine Nat.add_le_add_right ?_ 1
  by_cases hxy : x.1 = y.1
  · have heq : uf.link x y hy = uf := by
      apply unionFind_ext
      simp [Batteries.UnionFind.linkAux, hxy]
    rw [heq]
  · have hc' : RankCount (uf.link x y hy) := hc.link h hx hy
    have hsize : (uf.link x y hy).size = uf.size := by simp [Batteries.UnionFind.size]
    by_cases hlt : uf.rank y.1 < uf.rank x.1
    · refine LinkPotential.potential_le_of_link_step h hc' hy hx (Ne.symm hxy) hsize ?_ ?_ ?_
      · intro i
        rw [Batteries.UnionFind.parent_link hy]
        simp [hxy, hlt]
      · intro i _
        rw [rank_link, ite_eq_right]
        rintro ⟨_, heq_rk, _⟩
        exact absurd heq_rk (ne_of_gt hlt)
      · rw [rank_link, ite_eq_right]
        rintro ⟨_, heq_rk, _⟩
        exact absurd heq_rk (ne_of_gt hlt)
    · refine LinkPotential.potential_le_of_link_step h hc' hx hy hxy hsize ?_ ?_ ?_
      · intro i
        rw [Batteries.UnionFind.parent_link hy]
        simp [hxy, hlt]
      · intro i hiv
        rw [rank_link, ite_eq_right]
        rintro ⟨_, _, hyi⟩
        exact hiv hyi.symm
      · rw [rank_link]
        split <;> omega


private theorem step_potential {n : ℕ} (s : State n) (o : Op n)
    (hrank : ValidRank s.uf) (hc : RankCount s.uf) :
    (step s o).2.2 + potential (step s o).1.uf ≤ 2 * Nat.logStar n + 3 + potential s.uf := by
  cases o with
  | numComponents =>
    change 1 + potential s.uf ≤ 2 * Nat.logStar n + 3 + potential s.uf
    omega
  | same x y =>
    unfold step
    dsimp only
    let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := by
      change (compressWithSteps s.uf x').1.size = n
      rw [compressWithSteps_fst, Batteries.UnionFind.find_size, s.size_eq]
    let y' : Fin c₁.1.size := ⟨y.1, by rw [hsz₁]; exact y.2⟩
    have hrank₁ : ValidRank c₁.1 := by
      change ValidRank (compressWithSteps s.uf x').1
      rw [compressWithSteps_fst]
      exact hrank.find x'
    have hc₁ : RankCount c₁.1 := by
      change RankCount (compressWithSteps s.uf x').1
      rw [compressWithSteps_fst]
      exact hc.find x'
    have hp₁ : potential c₁.1 + findSteps s.uf x' ≤ potential s.uf + (Nat.logStar s.uf.size + 1) :=
      compressWithSteps_potential_tight hrank hc x'
    have hp₂ : potential (compressWithSteps c₁.1 y').1 + findSteps c₁.1 y' ≤
        potential c₁.1 + (Nat.logStar c₁.1.size + 1) :=
      compressWithSteps_potential_tight hrank₁ hc₁ y'
    have hls₁ : Nat.logStar s.uf.size = Nat.logStar n := congrArg Nat.logStar s.size_eq
    have hls₂ : Nat.logStar c₁.1.size = Nat.logStar n := congrArg Nat.logStar hsz₁
    change findSteps s.uf x' + findSteps c₁.1 y' + potential (compressWithSteps c₁.1 y').1 ≤
      2 * Nat.logStar n + 3 + potential s.uf
    omega
  | union x y =>
    unfold step
    dsimp only
    let x' : Fin s.uf.size := ⟨x.1, by rw [s.size_eq]; exact x.2⟩
    let c₁ := compressWithSteps s.uf x'
    have hsz₁ : c₁.1.size = n := by
      change (compressWithSteps s.uf x').1.size = n
      rw [compressWithSteps_fst, Batteries.UnionFind.find_size, s.size_eq]
    let y' : Fin c₁.1.size := ⟨y.1, by rw [hsz₁]; exact y.2⟩
    let c₂ := compressWithSteps c₁.1 y'
    have hsz₂ : c₂.1.size = c₁.1.size := by
      change (compressWithSteps c₁.1 y').1.size = c₁.1.size
      rw [compressWithSteps_fst, Batteries.UnionFind.find_size]
    let rx : Fin c₂.1.size := ⟨c₁.2.1.1, by
      rw [hsz₂]
      change c₁.2.1.1 < (compressWithSteps s.uf x').1.size
      rw [compressWithSteps_fst, Batteries.UnionFind.find_size]
      exact c₁.2.1.2⟩
    let ry : Fin c₂.1.size := ⟨c₂.2.1.1, by
      rw [hsz₂]
      exact c₂.2.1.2⟩
    have hrank₁ : ValidRank c₁.1 := by
      change ValidRank (compressWithSteps s.uf x').1
      rw [compressWithSteps_fst]
      exact hrank.find x'
    have hc₁ : RankCount c₁.1 := by
      change RankCount (compressWithSteps s.uf x').1
      rw [compressWithSteps_fst]
      exact hc.find x'
    have hrank₂ : ValidRank c₂.1 := by
      change ValidRank (compressWithSteps c₁.1 y').1
      rw [compressWithSteps_fst]
      exact hrank₁.find y'
    have hc₂ : RankCount c₂.1 := by
      change RankCount (compressWithSteps c₁.1 y').1
      rw [compressWithSteps_fst]
      exact hc₁.find y'
    have hxroot : c₂.1.parent rx.1 = rx.1 := by
      have hr : c₁.2.1.1 = s.uf.rootD x.1 := compressWithSteps_root s.uf x'
      have hf₁ : c₁.1.rootD c₁.2.1.1 = s.uf.rootD c₁.2.1.1 := by
        change (compressWithSteps s.uf x').1.rootD c₁.2.1.1 = s.uf.rootD c₁.2.1.1
        rw [compressWithSteps_fst]
        exact Batteries.UnionFind.find_root_1 s.uf x' c₁.2.1.1
      have hf₂ : c₂.1.rootD c₁.2.1.1 = c₁.1.rootD c₁.2.1.1 := by
        change (compressWithSteps c₁.1 y').1.rootD c₁.2.1.1 = c₁.1.rootD c₁.2.1.1
        rw [compressWithSteps_fst]
        exact Batteries.UnionFind.find_root_1 c₁.1 y' c₁.2.1.1
      change c₂.1.parent c₁.2.1.1 = c₁.2.1.1
      rw [← Batteries.UnionFind.rootD_eq_self, hf₂, hf₁, hr, Batteries.UnionFind.rootD_rootD]
    have hyroot : c₂.1.parent ry.1 = ry.1 := by
      have hr : c₂.2.1.1 = c₁.1.rootD y.1 := compressWithSteps_root c₁.1 y'
      have hf : c₂.1.rootD c₂.2.1.1 = c₁.1.rootD c₂.2.1.1 := by
        change (compressWithSteps c₁.1 y').1.rootD c₂.2.1.1 = c₁.1.rootD c₂.2.1.1
        rw [compressWithSteps_fst]
        exact Batteries.UnionFind.find_root_1 c₁.1 y' c₂.2.1.1
      change c₂.1.parent c₂.2.1.1 = c₂.2.1.1
      rw [← Batteries.UnionFind.rootD_eq_self, hf, hr, Batteries.UnionFind.rootD_rootD]
    have hp₁ : potential c₁.1 + findSteps s.uf x' ≤ potential s.uf + (Nat.logStar s.uf.size + 1) :=
      compressWithSteps_potential_tight hrank hc x'
    have hp₂ : potential c₂.1 + findSteps c₁.1 y' ≤ potential c₁.1 + (Nat.logStar c₁.1.size + 1) :=
      compressWithSteps_potential_tight hrank₁ hc₁ y'
    have hlink := link_potential hrank₂ hc₂ (x := rx) (y := ry) hxroot hyroot
    have hls₁ : Nat.logStar s.uf.size = Nat.logStar n := congrArg Nat.logStar s.size_eq
    have hls₂ : Nat.logStar c₁.1.size = Nat.logStar n := congrArg Nat.logStar hsz₁
    change findSteps s.uf x' + findSteps c₁.1 y' + 1 + potential (c₂.1.link rx ry hyroot) ≤
      2 * Nat.logStar n + 3 + potential s.uf
    omega

theorem amortizedBound (n : ℕ) :
    Cslib.DataStructure.Amortized (impl n) id (fun _ c => potential c.uf)
      (fun _ _ => 2 * Nat.logStar n + 3) := by
  refine Cslib.DataStructure.Amortized.ofFn fun {p s o a s' steps} hr _ he => ?_
  have hs : s' = (step s o).1 := (Prod.ext_iff.mp he).1.symm
  have hsteps : steps = (step s o).2.2 := (Prod.ext_iff.mp (Prod.ext_iff.mp he).2).2.symm
  rw [id, hs, hsteps]
  have hr_rep : Rep p s := hr
  exact step_potential s o hr_rep.validRank hr_rep.rankCount

end Cslib.DataStructure.DisjointSet.UnionFind
