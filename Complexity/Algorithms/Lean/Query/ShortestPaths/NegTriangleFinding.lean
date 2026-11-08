/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Query.FreeM.Tabulate
public import Complexity.Algorithms.ShortestPaths.NegativeTriangle
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Finding negative triangles from detection, and all pairs on negative triangles

The first two steps of the reduction of Vassilevska Williams and Williams from the (min,+) product
to negative triangle detection, as programs in the query model `FreeM Q` that call subroutines.

* **Finding from detection** (Lemma 4.1). `Cslib.Query.findNegTri det L` finds a negative
  triangle in a tripartite graph with three parts of size `2 ^ L`, or reports that there is none,
  using a detection subroutine `det`. It halves each part, runs `det` on the `8` induced
  sub-instances, and recurses into one sub-instance on which `det` answers yes; on parts of size
  `1` it calls `det` once. If every call of `det m` costs at most `τ m`, the program costs at most
  `τ 1 + ∑_{l < L} 8 τ (2 ^ l)`, which is `O(τ (2 ^ L))` for polynomial `τ` of degree above `1`.
* **All pairs on negative triangles** (Lemma 4.2). `Cslib.Query.allPairsNegTri find` decides,
  for every pair `(x, y)`, whether it lies on a negative triangle, in a graph whose parts are
  `Fin t × κ` (`t` blocks of size `|κ|`). For every triple of blocks it repeatedly calls the
  finding subroutine `find` on the sub-instance induced by the three blocks, records the pair
  of each triangle found and removes that edge (sets the `I`–`J` weight to `⊤`), until `find`
  reports none. Every successful call removes a new edge, so there are at most
  `t ^ 3 + (t |κ|) ^ 2` calls in total: with `n = t |κ|` vertices per part this is
  `t ^ 3 + n ^ 2` calls on instances with `n / t` vertices per part.

Correctness assumes that the subroutine is correct under the given oracle; the cost bounds hold
under every oracle (given nonnegative per-call bounds, since a call that is skipped costs `0`).

**What is charged.** `FreeM` charges only the subroutine calls. Building the sub-instances
(relabelling, masking removed edges), the loops over octants and block triples and the
bookkeeping of the removed edges are pure code and are free, as in the other query-model
reductions in this library. In a RAM implementation that passes sub-instances as views, this
overhead is `O(L)` per finding call for halving and `O(t ^ 3 + n ^ 2)` for blocking, matching the
accounting of Lemma 4.2.

`Cslib.Query.padAPNT` runs an all-pairs program on a graph padded with isolated vertices, so that
the blocking reduction applies to any number of vertices.

## Main definitions

* `Cslib.Query.halves`: `Fin 2 × Fin (2 ^ L) ≃ Fin (2 ^ (L + 1))`.
* `Cslib.Query.findNegTri`: finding a negative triangle with a detection subroutine.
* `Cslib.Query.drainBlock`, `Cslib.Query.allPairsNegTri`: all pairs on negative triangles with a
  finding subroutine.
* `Cslib.Query.padAPNT`: an all-pairs program on a padded graph.

## Main results

* `Cslib.Query.isNegTriangleAnswer_findNegTri`, `Cslib.Query.cost_findNegTri_le`: Lemma 4.1.
* `Cslib.Query.allPairsNegTri_eval`, `Cslib.Query.cost_allPairsNegTri_le`: Lemma 4.2.
* `Cslib.Query.padAPNT_eval`, `Cslib.Query.cost_padAPNT`: padding.

## References

* [Vassilevska Williams and Williams, *Subcubic Equivalences Between Path, Matrix, and Triangle
  Problems*][VassilevskaWilliamsWilliams2018], Lemma 4.1 and Lemma 4.2.
-/

public section

open MinTropical Cslib.Algorithms.ShortestPaths

namespace Cslib.Query

variable {Q : Type → Type} {S : Type}

/-! ### Finding a negative triangle from detection (Lemma 4.1) -/

section Finding

/-- Split `Fin (2 ^ (L + 1))` into two halves of size `2 ^ L`. -/
@[expose] def halves (L : ℕ) : Fin 2 × Fin (2 ^ L) ≃ Fin (2 ^ (L + 1)) :=
  finProdFinEquiv.trans (finCongr (pow_succ' 2 L).symm)

/-- The `8` octants: a choice of half for each of the three parts. -/
@[expose] def octant : Fin (2 * (2 * 2)) ≃ Fin 2 × Fin 2 × Fin 2 :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

/-- **Finding a negative triangle from detection** (Vassilevska Williams–Williams, Lemma 4.1).
On parts of size `2 ^ (L + 1)`, run the detection subroutine `det` on all `8` sub-instances
induced by a choice of halves, and recurse into the first one on which it answers yes. On parts
of size `1`, call `det` once. -/
@[expose] def findNegTri
    (det : (m : ℕ) → Matrix (Fin m) (Fin m) S → Matrix (Fin m) (Fin m) S →
      Matrix (Fin m) (Fin m) S → FreeM Q Bool) :
    (L : ℕ) → Matrix (Fin (2 ^ L)) (Fin (2 ^ L)) S → Matrix (Fin (2 ^ L)) (Fin (2 ^ L)) S →
      Matrix (Fin (2 ^ L)) (Fin (2 ^ L)) S →
        FreeM Q (Option (Fin (2 ^ L) × Fin (2 ^ L) × Fin (2 ^ L)))
  | 0, A, B, C => do
    let b ← det (2 ^ 0) A B C
    return if b then some (0, 0, 0) else none
  | L + 1, A, B, C => do
    let h : Fin 2 → Fin (2 ^ L) → Fin (2 ^ (L + 1)) := fun a i => halves L (a, i)
    let sub : Fin 2 × Fin 2 × Fin 2 → _ := fun o =>
      (A.submatrix (h o.1) (h o.2.2), B.submatrix (h o.2.2) (h o.2.1),
        C.submatrix (h o.1) (h o.2.1))
    let r ← FreeM.tabulate (2 * (2 * 2)) fun x =>
      det (2 ^ L) (sub (octant x)).1 (sub (octant x)).2.1 (sub (octant x)).2.2
    match (List.finRange (2 * (2 * 2))).find? r with
    | none => return none
    | some x => do
      let res ← findNegTri det L (sub (octant x)).1 (sub (octant x)).2.1 (sub (octant x)).2.2
      return res.map fun (i, j, k) =>
        (h (octant x).1 i, h (octant x).2.1 j, h (octant x).2.2 k)

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R]

/-- **Lemma 4.1, correctness.** If `det` decides negative triangles under `oracle`, then
`findNegTri det L` finds a negative triangle or correctly reports that there is none. -/
theorem isNegTriangleAnswer_findNegTri (oracle : {ι : Type} → Q ι → ι)
    {det : (m : ℕ) → Matrix (Fin m) (Fin m) (MinTropical R) →
      Matrix (Fin m) (Fin m) (MinTropical R) → Matrix (Fin m) (Fin m) (MinTropical R) →
      FreeM Q Bool}
    (hdet : ∀ m A B C, (det m A B C).eval oracle = decide (HasNegTriangle A B C)) :
    ∀ (L : ℕ) (A B C : Matrix (Fin (2 ^ L)) (Fin (2 ^ L)) (MinTropical R)),
      IsNegTriangleAnswer A B C ((findNegTri det L A B C).eval oracle)
  | 0, A, B, C => by
    simp only [findNegTri, FreeM.eval_bind, FreeM.eval_pure, hdet]
    by_cases h : HasNegTriangle A B C
    · simp only [h, decide_true, ite_true, IsNegTriangleAnswer]
      obtain ⟨i, j, k, hijk⟩ := h
      have h0 : ∀ x : Fin (2 ^ 0), x = 0 := fun x => Fin.ext (by have := x.2; simp at this; omega)
      rwa [h0 i, h0 j, h0 k] at hijk
    · simp only [h, decide_false, Bool.false_eq_true, ite_false, IsNegTriangleAnswer]
      exact not_false
  | L + 1, A, B, C => by
    simp only [findNegTri, FreeM.eval_bind, FreeM.eval_tabulate]
    split
    · next hnone =>
      rw [FreeM.eval_pure, IsNegTriangleAnswer]
      rintro ⟨i, j, k, hijk⟩
      set o : Fin 2 × Fin 2 × Fin 2 :=
        ((halves L).symm i |>.1, (halves L).symm j |>.1, (halves L).symm k |>.1)
      have hx := List.find?_eq_none.1 hnone (octant.symm o) (List.mem_finRange _)
      rw [Equiv.apply_symm_apply, hdet, decide_eq_true_iff] at hx
      apply hx
      refine ⟨((halves L).symm i).2, ((halves L).symm j).2, ((halves L).symm k).2, ?_⟩
      rw [isNegTriangle_submatrix]
      simpa only [o, Prod.mk.eta, Equiv.apply_symm_apply] using hijk
    · next x hx =>
      have hdx := List.find?_some hx
      rw [hdet, decide_eq_true_iff] at hdx
      rw [FreeM.eval_bind, FreeM.eval_pure]
      have ih := isNegTriangleAnswer_findNegTri oracle hdet L
        (A.submatrix (fun i => halves L ((octant x).1, i))
          (fun i => halves L ((octant x).2.2, i)))
        (B.submatrix (fun i => halves L ((octant x).2.2, i))
          (fun i => halves L ((octant x).2.1, i)))
        (C.submatrix (fun i => halves L ((octant x).1, i))
          (fun i => halves L ((octant x).2.1, i)))
      revert ih
      generalize (findNegTri det L _ _ _).eval oracle = res
      rcases res with _ | ⟨i, j, k⟩
      · exact fun ih => absurd hdx ih
      · intro ih
        exact ih

variable {T : Type} [AddCommMonoid T] [PartialOrder T] [IsOrderedAddMonoid T]

/-- The cost bound of `findNegTri det L` from per-call bounds `τ m` for `det m`:
`τ 1 + ∑_{l < L} 8 τ (2 ^ l)`. -/
@[expose] def findNegTriCost (τ : ℕ → T) (L : ℕ) : T :=
  τ 1 + ∑ l ∈ Finset.range L, 8 • τ (2 ^ l)

omit [PartialOrder T] [IsOrderedAddMonoid T] in
theorem findNegTriCost_zero (τ : ℕ → T) : findNegTriCost τ 0 = τ 1 := by
  rw [findNegTriCost, Finset.sum_range_zero, add_zero]

omit [PartialOrder T] [IsOrderedAddMonoid T] in
theorem findNegTriCost_succ (τ : ℕ → T) (L : ℕ) :
    findNegTriCost τ (L + 1) = 8 • τ (2 ^ L) + findNegTriCost τ L := by
  rw [findNegTriCost, findNegTriCost, Finset.sum_range_succ]
  abel

theorem findNegTriCost_nonneg {τ : ℕ → T} (hτ : ∀ m, 0 ≤ τ m) (L : ℕ) : 0 ≤ findNegTriCost τ L :=
  add_nonneg (hτ 1) (Finset.sum_nonneg fun _ _ => nsmul_nonneg (hτ _) _)

/-- **Lemma 4.1, cost.** If every call of `det m` costs at most `τ m ≥ 0` under `oracle`, then
`findNegTri det L` costs at most `τ 1 + ∑_{l < L} 8 τ (2 ^ l)`. -/
theorem cost_findNegTri_le (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {det : (m : ℕ) → Matrix (Fin m) (Fin m) S → Matrix (Fin m) (Fin m) S →
      Matrix (Fin m) (Fin m) S → FreeM Q Bool}
    {τ : ℕ → T} (hτ : ∀ m, 0 ≤ τ m) (hdet : ∀ m A B C, (det m A B C).cost oracle weight ≤ τ m) :
    ∀ (L : ℕ) (A B C : Matrix (Fin (2 ^ L)) (Fin (2 ^ L)) S),
      (findNegTri det L A B C).cost oracle weight ≤ findNegTriCost τ L
  | 0, A, B, C => by
    simp only [findNegTri, FreeM.cost_bind, FreeM.cost_pure, add_zero, findNegTriCost_zero]
    exact hdet _ A B C
  | L + 1, A, B, C => by
    simp only [findNegTri, FreeM.cost_bind, FreeM.cost_tabulate]
    rw [findNegTriCost_succ]
    refine add_le_add ((Finset.sum_le_card_nsmul _ _ _ fun x _ => hdet _ _ _ _).trans
      (le_of_eq (by rw [Finset.card_univ, Fintype.card_fin]))) ?_
    split
    · rw [FreeM.cost_pure]
      exact findNegTriCost_nonneg hτ L
    · rw [FreeM.cost_bind, FreeM.cost_pure, add_zero]
      exact cost_findNegTri_le oracle weight hτ hdet L _ _ _

end Finding

/-! ### All pairs on negative triangles by blocking (Lemma 4.2) -/

section Blocking

variable [Zero S] {t : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

/-- The sub-instance of the block triple `(a, b, c)`: the parts are blocks `a` of `I`, `b` of `J`
and `c` of `K`, and the `I`–`J` edges recorded in `P` are removed (set to `0`, no edge). -/
@[expose] def blockSub (A B C : Matrix (Fin t × κ) (Fin t × κ) S)
    (P : Fin t × κ → Fin t × κ → Bool) (a b c : Fin t) :
    Matrix κ κ S × Matrix κ κ S × Matrix κ κ S :=
  (Matrix.of fun i k => A (a, i) (c, k), Matrix.of fun k j => B (c, k) (b, j),
    Matrix.of fun i j => if P (a, i) (b, j) then 0 else C (a, i) (b, j))

/-- Record the pair `(x, y)`. -/
@[expose] def markPair (P : Fin t × κ → Fin t × κ → Bool) (x y : Fin t × κ) :
    Fin t × κ → Fin t × κ → Bool :=
  fun x' y' => if x' = x ∧ y' = y then true else P x' y'

/-- Repeatedly find a negative triangle in the sub-instance of the block triple `(a, b, c)` with
the recorded pairs removed, record its pair, and stop when `find` reports none, or after `fuel`
calls. -/
@[expose] def drainBlock
    (find : Matrix κ κ S → Matrix κ κ S → Matrix κ κ S → FreeM Q (Option (κ × κ × κ)))
    (A B C : Matrix (Fin t × κ) (Fin t × κ) S) (a b c : Fin t) :
    ℕ → (Fin t × κ → Fin t × κ → Bool) → FreeM Q (Fin t × κ → Fin t × κ → Bool)
  | 0, P => pure P
  | f + 1, P => do
    let r ← find (blockSub A B C P a b c).1 (blockSub A B C P a b c).2.1
      (blockSub A B C P a b c).2.2
    match r with
    | none => pure P
    | some (i, j, _) =>
      if P (a, i) (b, j) then pure P else drainBlock find A B C a b c f (markPair P (a, i) (b, j))

/-- All triples of blocks. -/
@[expose] def blockTriples (t : ℕ) : List (Fin t × Fin t × Fin t) :=
  List.finRange t ×ˢ (List.finRange t ×ˢ List.finRange t)

theorem mem_blockTriples (abc : Fin t × Fin t × Fin t) : abc ∈ blockTriples t := by
  obtain ⟨a, b, c⟩ := abc
  simp [blockTriples, List.mem_product]

theorem length_blockTriples (t : ℕ) : (blockTriples t).length = t ^ 3 := by
  simp only [blockTriples, List.length_product, List.length_finRange]
  ring

/-- **All pairs on negative triangles** (Vassilevska Williams–Williams, Lemma 4.2): drain every
block triple in turn, with `|κ| ^ 2 + 1` calls of fuel each. The result maps `(x, y)` to whether
the pair was recorded. -/
@[expose] def allPairsNegTri
    (find : Matrix κ κ S → Matrix κ κ S → Matrix κ κ S → FreeM Q (Option (κ × κ × κ)))
    (A B C : Matrix (Fin t × κ) (Fin t × κ) S) :
    FreeM Q (Fin t × κ → Fin t × κ → Bool) :=
  (blockTriples t).foldlM
    (fun P abc => drainBlock find A B C abc.1 abc.2.1 abc.2.2 (Fintype.card κ ^ 2 + 1) P)
    (fun _ _ => false)

/-! #### Cost -/

section Cost

variable {T : Type} [AddCommMonoid T] [PartialOrder T] [IsOrderedAddMonoid T]

/-- The number of pairs not yet recorded. -/
private def unmarked (P : Fin t × κ → Fin t × κ → Bool) : ℕ :=
  (Finset.univ.filter fun p : (Fin t × κ) × (Fin t × κ) => P p.1 p.2 = false).card

private theorem unmarked_markPair {P : Fin t × κ → Fin t × κ → Bool} {x y : Fin t × κ}
    (h : P x y = false) : unmarked P = unmarked (markPair P x y) + 1 := by
  rw [unmarked, unmarked]
  have : (Finset.univ.filter fun p : (Fin t × κ) × (Fin t × κ) => markPair P x y p.1 p.2 = false) =
      (Finset.univ.filter fun p : (Fin t × κ) × (Fin t × κ) => P p.1 p.2 = false).erase (x, y) := by
    ext ⟨x', y'⟩
    rw [Finset.mem_filter, Finset.mem_erase, Finset.mem_filter]
    simp only [markPair, Finset.mem_univ, true_and, ne_eq, Prod.mk.injEq]
    by_cases hxy : x' = x ∧ y' = y
    · obtain ⟨rfl, rfl⟩ := hxy
      simp
    · rw [ite_eq_right hxy]
      exact ⟨fun h => ⟨hxy, h⟩, fun h => h.2⟩
  rw [this, Finset.card_erase_of_mem (by simpa using h), Nat.sub_add_cancel]
  exact Finset.card_pos.2 ⟨(x, y), by simpa using h⟩

private theorem cost_drainBlock_le (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T)
    {find : Matrix κ κ S → Matrix κ κ S → Matrix κ κ S → FreeM Q (Option (κ × κ × κ))}
    {τ : T} (hτ : 0 ≤ τ) (hfind : ∀ A B C, (find A B C).cost oracle weight ≤ τ)
    (A B C : Matrix (Fin t × κ) (Fin t × κ) S) (a b c : Fin t) :
    ∀ (f : ℕ) (P : Fin t × κ → Fin t × κ → Bool),
      (drainBlock find A B C a b c f P).cost oracle weight +
          unmarked ((drainBlock find A B C a b c f P).eval oracle) • τ ≤
        τ + unmarked P • τ
  | 0, P => by
    simp only [drainBlock, FreeM.cost_pure, FreeM.eval_pure, zero_add]
    exact le_add_of_nonneg_left hτ
  | f + 1, P => by
    simp only [drainBlock, FreeM.cost_bind, FreeM.eval_bind]
    generalize (find _ _ _).eval oracle = r
    have hc := hfind (blockSub A B C P a b c).1 (blockSub A B C P a b c).2.1
      (blockSub A B C P a b c).2.2
    rcases r with _ | ⟨i, j, k⟩
    · simp only [FreeM.cost_pure, FreeM.eval_pure, add_zero]
      exact add_le_add hc le_rfl
    · by_cases hP : P (a, i) (b, j) = true
      · simp only [hP, ite_true, FreeM.cost_pure, FreeM.eval_pure, add_zero]
        exact add_le_add hc le_rfl
      · simp only [hP, Bool.false_eq_true, ite_false]
        have ih := cost_drainBlock_le oracle weight hτ hfind A B C a b c f
          (markPair P (a, i) (b, j))
        rw [unmarked_markPair (P := P) (Bool.eq_false_iff.2 hP), _root_.succ_nsmul]
        calc _ = (find _ _ _).cost oracle weight +
              ((drainBlock find A B C a b c f (markPair P (a, i) (b, j))).cost oracle weight +
                unmarked ((drainBlock find A B C a b c f
                  (markPair P (a, i) (b, j))).eval oracle) • τ) := by abel
          _ ≤ τ + (τ + unmarked (markPair P (a, i) (b, j)) • τ) := add_le_add hc ih
          _ = _ := by abel

private theorem cost_foldlM_drainBlock_le (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T)
    {find : Matrix κ κ S → Matrix κ κ S → Matrix κ κ S → FreeM Q (Option (κ × κ × κ))}
    {τ : T} (hτ : 0 ≤ τ) (hfind : ∀ A B C, (find A B C).cost oracle weight ≤ τ)
    (A B C : Matrix (Fin t × κ) (Fin t × κ) S) (f : ℕ) :
    ∀ (l : List (Fin t × Fin t × Fin t)) (P : Fin t × κ → Fin t × κ → Bool),
      (l.foldlM (fun P abc => drainBlock find A B C abc.1 abc.2.1 abc.2.2 f P) P).cost oracle
          weight ≤ l.length • τ + unmarked P • τ
  | [], P => by
    simp only [List.foldlM_nil, FreeM.cost_pure, List.length_nil, zero_smul, zero_add]
    exact nsmul_nonneg hτ _
  | abc :: l, P => by
    simp only [List.foldlM_cons, FreeM.cost_bind, List.length_cons, _root_.succ_nsmul]
    have h1 := cost_drainBlock_le oracle weight hτ hfind A B C abc.1 abc.2.1 abc.2.2 f P
    have h2 := cost_foldlM_drainBlock_le oracle weight hτ hfind A B C f l
      ((drainBlock find A B C abc.1 abc.2.1 abc.2.2 f P).eval oracle)
    calc _ ≤ (drainBlock find A B C abc.1 abc.2.1 abc.2.2 f P).cost oracle weight +
          (l.length • τ + unmarked ((drainBlock find A B C abc.1 abc.2.1 abc.2.2 f P).eval
            oracle) • τ) := add_le_add le_rfl h2
      _ = l.length • τ + ((drainBlock find A B C abc.1 abc.2.1 abc.2.2 f P).cost oracle weight +
          unmarked ((drainBlock find A B C abc.1 abc.2.1 abc.2.2 f P).eval oracle) • τ) := by
        abel
      _ ≤ l.length • τ + (τ + unmarked P • τ) := add_le_add le_rfl h1
      _ = _ := by abel

/-- **Lemma 4.2, cost.** If every call of `find` costs at most `τ ≥ 0` under `oracle`, then
`allPairsNegTri find` costs at most `(t ^ 3 + (t |κ|) ^ 2) τ`: one unsuccessful call per block
triple and at most one successful call per pair. -/
theorem cost_allPairsNegTri_le (oracle : {ι : Type} → Q ι → ι) (weight : {ι : Type} → Q ι → T)
    {find : Matrix κ κ S → Matrix κ κ S → Matrix κ κ S → FreeM Q (Option (κ × κ × κ))}
    {τ : T} (hτ : 0 ≤ τ) (hfind : ∀ A B C, (find A B C).cost oracle weight ≤ τ)
    (A B C : Matrix (Fin t × κ) (Fin t × κ) S) :
    (allPairsNegTri find A B C).cost oracle weight ≤ (t ^ 3 + (t * Fintype.card κ) ^ 2) • τ := by
  refine (cost_foldlM_drainBlock_le oracle weight hτ hfind A B C _ _ _).trans (le_of_eq ?_)
  have : unmarked (t := t) (κ := κ) (fun _ _ => false) = (t * Fintype.card κ) ^ 2 := by
    simp [unmarked, Fintype.card_prod, sq]
  rw [length_blockTriples, this, add_nsmul]

end Cost

/-! #### Correctness -/

section Correctness

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R]

/-- Every recorded pair lies on a negative triangle. -/
private def Sound (A B C : Matrix (Fin t × κ) (Fin t × κ) (MinTropical R))
    (P : Fin t × κ → Fin t × κ → Bool) : Prop :=
  ∀ x y, P x y = true → OnNegTriangle A B C x y

/-- Every negative triangle through the block triple `(a, b, c)` has its pair recorded. -/
private def BlockDone (A B C : Matrix (Fin t × κ) (Fin t × κ) (MinTropical R))
    (P : Fin t × κ → Fin t × κ → Bool) (a b c : Fin t) : Prop :=
  ∀ i j k, IsNegTriangle A B C (a, i) (b, j) (c, k) → P (a, i) (b, j) = true

/-- The number of pairs between blocks `a` and `b` not yet recorded. -/
private def blockUnmarked (P : Fin t × κ → Fin t × κ → Bool) (a b : Fin t) : ℕ :=
  (Finset.univ.filter fun p : κ × κ => P (a, p.1) (b, p.2) = false).card

omit [DecidableEq κ] in
private theorem blockUnmarked_le (P : Fin t × κ → Fin t × κ → Bool) (a b : Fin t) :
    blockUnmarked P a b ≤ Fintype.card κ ^ 2 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ, Fintype.card_prod, sq])

private theorem blockUnmarked_markPair {P : Fin t × κ → Fin t × κ → Bool} {a b : Fin t}
    {i j : κ} (h : P (a, i) (b, j) = false) :
    blockUnmarked P a b = blockUnmarked (markPair P (a, i) (b, j)) a b + 1 := by
  rw [blockUnmarked, blockUnmarked]
  have : (Finset.univ.filter fun p : κ × κ => markPair P (a, i) (b, j) (a, p.1) (b, p.2) = false) =
      (Finset.univ.filter fun p : κ × κ => P (a, p.1) (b, p.2) = false).erase (i, j) := by
    ext ⟨i', j'⟩
    simp only [markPair, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
      Prod.mk.injEq]
    by_cases hij : i' = i ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := hij
      simp
    · rw [ite_eq_right hij]
      exact ⟨fun h => ⟨hij, h⟩, fun h => h.2⟩
  rw [this, Finset.card_erase_of_mem (by simpa using h), Nat.sub_add_cancel]
  exact Finset.card_pos.2 ⟨(i, j), by simpa using h⟩

private theorem drainBlock_spec (oracle : {ι : Type} → Q ι → ι)
    {find : Matrix κ κ (MinTropical R) → Matrix κ κ (MinTropical R) →
      Matrix κ κ (MinTropical R) → FreeM Q (Option (κ × κ × κ))}
    (hfind : ∀ A B C, IsNegTriangleAnswer A B C ((find A B C).eval oracle))
    (A B C : Matrix (Fin t × κ) (Fin t × κ) (MinTropical R)) (a b c : Fin t) :
    ∀ (f : ℕ) (P : Fin t × κ → Fin t × κ → Bool), Sound A B C P → blockUnmarked P a b < f →
      Sound A B C ((drainBlock find A B C a b c f P).eval oracle) ∧
        (∀ x y, P x y = true → (drainBlock find A B C a b c f P).eval oracle x y = true) ∧
        BlockDone A B C ((drainBlock find A B C a b c f P).eval oracle) a b c
  | 0, P, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, P, hP, hf => by
    simp only [drainBlock, FreeM.eval_bind]
    have hr := hfind (blockSub A B C P a b c).1 (blockSub A B C P a b c).2.1
      (blockSub A B C P a b c).2.2
    revert hr
    generalize (find _ _ _).eval oracle = r
    rcases r with _ | ⟨i, j, k⟩
    · intro hr
      simp only [FreeM.eval_pure]
      refine ⟨hP, fun _ _ h => h, fun i j k hijk => ?_⟩
      by_contra hPij
      refine hr ⟨i, j, k, ?_⟩
      simpa [IsNegTriangle, blockSub, hPij] using hijk
    · intro hr
      have hr' : IsNegTriangle (blockSub A B C P a b c).1 (blockSub A B C P a b c).2.1
          (blockSub A B C P a b c).2.2 i j k := hr
      by_cases hPij : P (a, i) (b, j) = true
      · exfalso
        have := hr'.ne_zero_right
        simp [blockSub, hPij] at this
      · simp only [hPij, Bool.false_eq_true, ite_false]
        have htri : IsNegTriangle A B C (a, i) (b, j) (c, k) := by
          simpa [IsNegTriangle, blockSub, hPij] using hr'
        have hP' : Sound A B C (markPair P (a, i) (b, j)) := by
          intro x y hxy
          by_cases h : x = (a, i) ∧ y = (b, j)
          · obtain ⟨rfl, rfl⟩ := h
            exact ⟨_, htri⟩
          · simp only [markPair, h, ite_false] at hxy
            exact hP x y hxy
        have hf' : blockUnmarked (markPair P (a, i) (b, j)) a b < f := by
          have := blockUnmarked_markPair (Bool.eq_false_iff.2 hPij)
          omega
        obtain ⟨h1, h2, h3⟩ := drainBlock_spec oracle hfind A B C a b c f _ hP' hf'
        refine ⟨h1, fun x y hxy => h2 x y ?_, h3⟩
        simp [markPair, hxy]

private theorem foldlM_drainBlock_spec (oracle : {ι : Type} → Q ι → ι)
    {find : Matrix κ κ (MinTropical R) → Matrix κ κ (MinTropical R) →
      Matrix κ κ (MinTropical R) → FreeM Q (Option (κ × κ × κ))}
    (hfind : ∀ A B C, IsNegTriangleAnswer A B C ((find A B C).eval oracle))
    (A B C : Matrix (Fin t × κ) (Fin t × κ) (MinTropical R)) :
    ∀ (l : List (Fin t × Fin t × Fin t)) (P : Fin t × κ → Fin t × κ → Bool), Sound A B C P →
      let Q' := (l.foldlM (fun P abc => drainBlock find A B C abc.1 abc.2.1 abc.2.2
        (Fintype.card κ ^ 2 + 1) P) P).eval oracle
      Sound A B C Q' ∧ (∀ x y, P x y = true → Q' x y = true) ∧
        ∀ abc ∈ l, BlockDone A B C Q' abc.1 abc.2.1 abc.2.2
  | [], P, hP => by
    simp only [List.foldlM_nil, FreeM.eval_pure, List.not_mem_nil, false_imp_iff,
      implies_true, and_true]
    exact ⟨hP, fun _ _ h => h⟩
  | abc :: l, P, hP => by
    simp only [List.foldlM_cons, FreeM.eval_bind, List.mem_cons]
    obtain ⟨h1, h2, h3⟩ := drainBlock_spec oracle hfind A B C abc.1 abc.2.1 abc.2.2
      (Fintype.card κ ^ 2 + 1) P hP (Nat.lt_succ_of_le (blockUnmarked_le P _ _))
    obtain ⟨g1, g2, g3⟩ := foldlM_drainBlock_spec oracle hfind A B C l _ h1
    refine ⟨g1, fun x y h => g2 x y (h2 x y h), ?_⟩
    rintro abc' (rfl | habc)
    · exact fun i j k hijk => g2 _ _ (h3 i j k hijk)
    · exact g3 abc' habc

/-- **Lemma 4.2, correctness.** If `find` finds negative triangles under `oracle`, then
`allPairsNegTri find A B C` maps `(x, y)` to whether the pair lies on a negative triangle. -/
theorem allPairsNegTri_eval (oracle : {ι : Type} → Q ι → ι)
    {find : Matrix κ κ (MinTropical R) → Matrix κ κ (MinTropical R) →
      Matrix κ κ (MinTropical R) → FreeM Q (Option (κ × κ × κ))}
    (hfind : ∀ A B C, IsNegTriangleAnswer A B C ((find A B C).eval oracle))
    (A B C : Matrix (Fin t × κ) (Fin t × κ) (MinTropical R)) (x y : Fin t × κ) :
    (allPairsNegTri find A B C).eval oracle x y = decide (OnNegTriangle A B C x y) := by
  obtain ⟨hS, -, hD⟩ := foldlM_drainBlock_spec oracle hfind A B C (blockTriples t)
    (fun _ _ => false) (fun _ _ h => absurd h Bool.false_ne_true)
  rw [allPairsNegTri, Bool.eq_iff_iff, decide_eq_true_iff]
  refine ⟨hS x y, ?_⟩
  rintro ⟨⟨c, k⟩, hk⟩
  obtain ⟨a, i⟩ := x
  obtain ⟨b, j⟩ := y
  exact hD (a, b, c) (mem_blockTriples _) i j k hk

end Correctness

end Blocking

/-! ### Padding with isolated vertices -/

section Pad

variable [Zero S] {I U I₁ : Type}

/-- Run the all-pairs program `apnt` on the graph padded along `e : U ≃ I ⊕ I₁` with isolated
vertices, and read off the pairs of original vertices. -/
@[expose] def padAPNT (e : U ≃ I ⊕ I₁)
    (apnt : Matrix U U S → Matrix U U S → Matrix U U S → FreeM Q (U → U → Bool))
    (A B C : Matrix I I S) : FreeM Q (I → I → Bool) := do
  let P ← apnt (padIsolated e e A) (padIsolated e e B) (padIsolated e e C)
  return fun i j => P (e.symm (.inl i)) (e.symm (.inl j))

theorem cost_padAPNT {T : Type} [AddMonoid T] (oracle : {ι : Type} → Q ι → ι)
    (weight : {ι : Type} → Q ι → T) (e : U ≃ I ⊕ I₁)
    (apnt : Matrix U U S → Matrix U U S → Matrix U U S → FreeM Q (U → U → Bool))
    (A B C : Matrix I I S) :
    (padAPNT e apnt A B C).cost oracle weight =
      (apnt (padIsolated e e A) (padIsolated e e B) (padIsolated e e C)).cost oracle weight := by
  rw [padAPNT, FreeM.cost_bind, FreeM.cost_pure, add_zero]

variable {R : Type} [LinearOrderedAddCommMonoidWithTop R] [Fintype I] [Fintype U]

/-- Padding is correct: if `apnt` decides the pairs on negative triangles of the padded graph,
`padAPNT e apnt` decides those of the original graph. -/
theorem padAPNT_eval (oracle : {ι : Type} → Q ι → ι) (e : U ≃ I ⊕ I₁)
    {apnt : Matrix U U (MinTropical R) → Matrix U U (MinTropical R) →
      Matrix U U (MinTropical R) → FreeM Q (U → U → Bool)}
    (A B C : Matrix I I (MinTropical R))
    (happnt : ∀ x y, (apnt (padIsolated e e A) (padIsolated e e B) (padIsolated e e C)).eval
      oracle x y = decide (OnNegTriangle (padIsolated e e A) (padIsolated e e B)
        (padIsolated e e C) x y)) (i j : I) :
    (padAPNT e apnt A B C).eval oracle i j = decide (OnNegTriangle A B C i j) := by
  rw [padAPNT, FreeM.eval_bind, FreeM.eval_pure, happnt]
  exact decide_eq_decide.2 (onNegTriangle_padIsolated e e e A B C i j)

end Pad

end Cslib.Query
