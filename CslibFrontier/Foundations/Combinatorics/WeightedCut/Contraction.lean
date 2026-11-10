/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Combinatorics.WeightedCut

/-!
# Contracting two supervertices

Contraction of a weighted multigraph `W : Fin (m + 1) → Fin (m + 1) → ℕ`
(`Cslib.WeightedCut.IsMultigraph`) along a pair of distinct supervertices `u ≠ v`, keeping the
supervertices as `Fin m`. Merging `v` into `u` (`mergePair`) redirects the edges at `v` to `u` and
drops the edges between them. Swap-compaction (`embedCompact`, `compactIdx`) then moves the last
supervertex `Fin.last m` into the freed slot `v`, so that a contraction step on `m + 1` active
supervertices only touches rows and columns `0, …, m`, as in the `O(n)`-time matrix update of
[Karger and Stein, Section 3.2][KargerStein1996]. The contracted matrix is `contractMatrix W u v`,
the updated map from the original vertices to supervertices is `contractPart part u v huv`, and a
cut of `Fin (m + 1)` that does not separate `u` and `v` becomes the cut `contractCut v B` of
`Fin m`.

Contraction preserves `Cslib.WeightedCut.IsContractionOf` (`isContractionOf_contract`), so pulled
back cuts keep their weight, and a cut that does not separate `u` and `v` keeps its weight
(`cutWeight_contractCut`). The randomized algorithms of Karger and Karger–Stein
(`CslibFrontier.Algorithms.WordRAM.Karger.Graph`) and the deterministic Stoer–Wagner algorithm
(`CslibFrontier.Algorithms.Lean.StoerWagner.Basic`) are built on this API.

## Main definitions

* `Cslib.WeightedCut.mergePair`: the weight matrix after merging `v` into `u`.
* `Cslib.WeightedCut.embedCompact`, `Cslib.WeightedCut.compactIdx`: swap-compaction of the slots
  other than `v`, and its inverse.
* `Cslib.WeightedCut.contractMatrix`, `Cslib.WeightedCut.contractPart`,
  `Cslib.WeightedCut.contractCut`: the contracted matrix, supervertex map and cut.

## Main results

* `Cslib.WeightedCut.isMultigraph_contractMatrix`: the contracted matrix is a multigraph.
* `Cslib.WeightedCut.rowDeg_contractMatrix`, `Cslib.WeightedCut.totalDoubledWeight_contractMatrix`:
  degrees after contraction; the total doubled weight drops by `2 * W u v`.
* `Cslib.WeightedCut.isContractionOf_contract`: contracting a distinct pair `(u, v)` and
  swap-compacting the last active slot preserves `Cslib.WeightedCut.IsContractionOf`.
* `Cslib.WeightedCut.pullbackCut_contractCut`, `Cslib.WeightedCut.cutWeight_contractCut`: a cut
  that does not separate `u` and `v` pulls back to the same set, with the same weight.
* `Cslib.WeightedCut.pullbackCut_id`: pulling a cut back along the identity gives the same cut.

## References

* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

@[expose] public section

namespace Cslib.WeightedCut

/-! ### Merging (`mergePair`) and swap-compaction (`embedCompact` / `contractMatrix`) -/

/-- Matrix update when merging active supervertex `v` into `u` (`u ≠ v`): edges incident to `v` are
redirected to `u`, self-loops at `u` are cleared, and row/column `v` become isolated. -/
def mergePair {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) (i j : Fin k) : ℕ :=
  if i = j ∨ i = v ∨ j = v then 0
  else if i = u then W u j + W v j
  else if j = u then W i u + W i v
  else W i j

theorem isMultigraph_mergePair {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    (u v : Fin k) :
    IsMultigraph (mergePair W u v) := by
  constructor
  · intro i j
    unfold mergePair
    by_cases hij : i = j
    · subst hij; simp
    · have hji : j ≠ i := Ne.symm hij
      by_cases hiv : i = v
      · simp [hiv]
      · by_cases hjv : j = v
        · simp [hjv]
        · simp only [hij, hji, hiv, hjv, false_or, ↓reduceIte]
          by_cases hiu : i = u
          · have hju : j ≠ u := fun h => hij (hiu.trans h.symm)
            simp [hiu, hju, hW.1 u j, hW.1 v j]
          · by_cases hju : j = u
            · simp [hiu, hju, hW.1 i u, hW.1 i v]
            · simp [hiu, hju, hW.1 i j]
  · intro i
    simp [mergePair]

theorem mergePair_isolated_left {k : ℕ} (W : Fin k → Fin k → ℕ) (u v j : Fin k) :
    mergePair W u v v j = 0 := by
  simp [mergePair]

theorem mergePair_isolated_right {k : ℕ} (W : Fin k → Fin k → ℕ) (u v i : Fin k) :
    mergePair W u v i v = 0 := by
  simp [mergePair]

/-- A row sum split off at two distinct columns `u` and `v`. -/
private theorem sum_eq_add_add_sum_erase_erase {k : ℕ} {u v : Fin k} (huv : u ≠ v)
    (f : Fin k → ℕ) :
    ∑ y : Fin k, f y = f u + f v + ∑ y ∈ (Finset.univ.erase u).erase v, f y := by
  rw [← Finset.add_sum_erase _ f (Finset.mem_univ u),
    ← Finset.add_sum_erase _ f (Finset.mem_erase.mpr ⟨huv.symm, Finset.mem_univ v⟩), add_assoc]

theorem rowDeg_mergePair_other {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {u v x : Fin k} (huv : u ≠ v) (hxu : x ≠ u) (hxv : x ≠ v) :
    rowDeg (mergePair W u v) x = rowDeg W x := by
  unfold rowDeg
  rw [sum_eq_add_add_sum_erase_erase huv (mergePair W u v x),
    sum_eq_add_add_sum_erase_erase huv (W x)]
  have h1 : mergePair W u v x u = W x u + W x v := by
    unfold mergePair
    simp [hxu, hxv, huv]
  have h2 : mergePair W u v x v = 0 := mergePair_isolated_right W u v x
  have h3 : ∑ y ∈ (Finset.univ.erase u).erase v, mergePair W u v x y =
      ∑ y ∈ (Finset.univ.erase u).erase v, W x y := by
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy_v : y ≠ v := (Finset.mem_erase.mp hy).1
    have hy_u : y ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
    unfold mergePair
    by_cases hxy : x = y
    · subst hxy; simp [hW.2 x]
    · simp [hxy, hxv, hy_v, hxu, hy_u]
  rw [h1, h2, h3, add_zero]

theorem rowDeg_mergePair_u {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {u v : Fin k} (huv : u ≠ v) :
    rowDeg (mergePair W u v) u = (rowDeg W u - W u v) + (rowDeg W v - W v u) := by
  unfold rowDeg
  rw [sum_eq_add_add_sum_erase_erase huv (mergePair W u v u),
    sum_eq_add_add_sum_erase_erase huv (W u), sum_eq_add_add_sum_erase_erase huv (W v)]
  have h_uu : mergePair W u v u u = 0 := by simp [mergePair]
  have h_uv : mergePair W u v u v = 0 := mergePair_isolated_right W u v u
  have h_rest : ∑ y ∈ (Finset.univ.erase u).erase v, mergePair W u v u y =
      (∑ y ∈ (Finset.univ.erase u).erase v, W u y) +
        ∑ y ∈ (Finset.univ.erase u).erase v, W v y := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy_v : y ≠ v := (Finset.mem_erase.mp hy).1
    have hy_u : y ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
    have huy : u ≠ y := hy_u.symm
    unfold mergePair
    simp [huy, huv, hy_v]
  rw [h_uu, h_uv, h_rest, hW.2 u, hW.2 v]
  omega

theorem rowDeg_mergePair_v {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) :
    rowDeg (mergePair W u v) v = 0 := by
  unfold rowDeg
  simp [mergePair_isolated_left]

/-- Embedding `Fin m → Fin (m + 1)` corresponding to replacing removed slot `v` with `Fin.last m`
and keeping all other slots `< m` in place. -/
def embedCompact {m : ℕ} (v : Fin (m + 1)) (i : Fin m) : Fin (m + 1) :=
  if i.val = v.val then Fin.last m else i.castSucc

theorem embedCompact_ne {m : ℕ} (v : Fin (m + 1)) (i : Fin m) :
    embedCompact v i ≠ v := by
  unfold embedCompact
  split_ifs with h
  · intro hlast
    have hv : v.val = m := by simpa [Fin.ext_iff] using hlast.symm
    omega
  · intro hcast
    exact h (by simpa [Fin.ext_iff] using hcast)

theorem embedCompact_injective {m : ℕ} (v : Fin (m + 1)) :
    Function.Injective (embedCompact v) := by
  intro i j hij
  unfold embedCompact at hij
  by_cases hi : i.val = v.val <;> by_cases hj : j.val = v.val
  · exact Fin.ext (hi.trans hj.symm)
  · simp only [hi, hj, ↓reduceIte, Fin.ext_iff, Fin.val_last, Fin.val_castSucc] at hij
    omega
  · simp only [hi, hj, ↓reduceIte, Fin.ext_iff, Fin.val_last, Fin.val_castSucc] at hij
    omega
  · simp only [hi, hj, ↓reduceIte, Fin.castSucc_inj] at hij
    exact hij

/-- Inverse of `embedCompact v` on `{a : Fin (m + 1) // a ≠ v}`. -/
def compactIdx {m : ℕ} (v : Fin (m + 1)) (a : Fin (m + 1)) (ha : a ≠ v) : Fin m :=
  if h : a.val = m then
    ⟨v.val, by
      have hva : v.val ≠ m := fun hvm => ha (Fin.ext (h.trans hvm.symm))
      omega⟩
  else
    ⟨a.val, by omega⟩

@[simp]
theorem embedCompact_compactIdx {m : ℕ} (v : Fin (m + 1)) (a : Fin (m + 1)) (ha : a ≠ v) :
    embedCompact v (compactIdx v a ha) = a := by
  unfold embedCompact compactIdx
  by_cases ham : a.val = m
  · simp only [ham, ↓reduceDIte, ↓reduceIte]
    exact Fin.ext ham.symm
  · simp only [ham, ↓reduceDIte]
    have hav : a.val ≠ v.val := fun h => ha (Fin.ext h)
    simp only [hav, ↓reduceIte]
    exact Fin.ext rfl

@[simp]
theorem compactIdx_embedCompact {m : ℕ} (v : Fin (m + 1)) (i : Fin m) :
    compactIdx v (embedCompact v i) (embedCompact_ne v i) = i :=
  embedCompact_injective v (embedCompact_compactIdx v _ _)

/-- Swap-compacted `m × m` adjacency matrix after merging `v` into `u` (`u ≠ v`) and moving active
supervertex `Fin.last m` into slot `v` (when `v ≠ Fin.last m`). -/
def contractMatrix {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ) (u v : Fin (m + 1))
    (i j : Fin m) : ℕ :=
  mergePair W u v (embedCompact v i) (embedCompact v j)

theorem isMultigraph_contractMatrix {m : ℕ} {W : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW : IsMultigraph W) (u v : Fin (m + 1)) :
    IsMultigraph (contractMatrix W u v) := by
  have hm := isMultigraph_mergePair hW u v
  exact ⟨fun i j => hm.1 _ _, fun i => hm.2 _⟩

theorem sum_embedCompact_eq_sum_erase {m : ℕ} (v : Fin (m + 1)) (f : Fin (m + 1) → ℕ) :
    ∑ i : Fin m, f (embedCompact v i) = ∑ a ∈ Finset.univ.erase v, f a := by
  refine Finset.sum_bij (fun i _ => embedCompact v i) ?_ ?_ ?_ ?_
  · intro i _
    exact Finset.mem_erase.mpr ⟨embedCompact_ne v i, Finset.mem_univ _⟩
  · intro i _ j _ hij
    exact embedCompact_injective v hij
  · intro a ha
    have hav : a ≠ v := (Finset.mem_erase.mp ha).1
    exact ⟨compactIdx v a hav, Finset.mem_univ _, embedCompact_compactIdx v a hav⟩
  · intros
    rfl

theorem rowDeg_contractMatrix {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ)
    (u v : Fin (m + 1)) (i : Fin m) :
    rowDeg (contractMatrix W u v) i = rowDeg (mergePair W u v) (embedCompact v i) := by
  unfold rowDeg contractMatrix
  rw [sum_embedCompact_eq_sum_erase v]
  have hv_zero : mergePair W u v (embedCompact v i) v = 0 :=
    mergePair_isolated_right W u v (embedCompact v i)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin (m + 1)))
    (mergePair W u v (embedCompact v i)) (Finset.mem_univ v)
  omega

theorem totalDoubledWeight_contractMatrix {m : ℕ} {W : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW : IsMultigraph W) {u v : Fin (m + 1)} (huv : u ≠ v) :
    totalDoubledWeight (contractMatrix W u v) + 2 * W u v = totalDoubledWeight W := by
  unfold totalDoubledWeight
  have hrows : ∑ i : Fin m, rowDeg (contractMatrix W u v) i =
      ∑ a ∈ Finset.univ.erase v, rowDeg (mergePair W u v) a := by
    calc
      ∑ i : Fin m, rowDeg (contractMatrix W u v) i
        = ∑ i : Fin m, rowDeg (mergePair W u v) (embedCompact v i) :=
          Finset.sum_congr rfl fun i _ => rowDeg_contractMatrix W u v i
      _ = ∑ a ∈ Finset.univ.erase v, rowDeg (mergePair W u v) a :=
          sum_embedCompact_eq_sum_erase v (rowDeg (mergePair W u v))
  rw [hrows]
  have hu_mem : u ∈ (Finset.univ : Finset (Fin (m + 1))).erase v :=
    Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩
  rw [← Finset.add_sum_erase _ _ hu_mem]
  have h_other : ∑ a ∈ (Finset.univ.erase v).erase u, rowDeg (mergePair W u v) a =
      ∑ a ∈ (Finset.univ.erase v).erase u, rowDeg W a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have hau : a ≠ u := (Finset.mem_erase.mp ha).1
    have hav : a ≠ v := (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).1
    exact rowDeg_mergePair_other hW huv hau hav
  rw [h_other, rowDeg_mergePair_u hW huv]
  have htot_split : ∑ a : Fin (m + 1), rowDeg W a =
      rowDeg W v + (rowDeg W u + ∑ a ∈ (Finset.univ.erase v).erase u, rowDeg W a) := by
    rw [← Finset.add_sum_erase _ (rowDeg W) (Finset.mem_univ v),
      ← Finset.add_sum_erase _ (rowDeg W) hu_mem]
  rw [htot_split]
  have huv_le : W u v ≤ rowDeg W u := entry_le_rowDeg W u v
  have hvu_le : W v u ≤ rowDeg W v := entry_le_rowDeg W v u
  have hvu_eq : W v u = W u v := hW.1 v u
  omega

/-- Updated supervertex partition `Fin n → Fin m` after merging `v` into `u` (`u ≠ v`) and
swap-compacting slot `v`. -/
def contractPart {n m : ℕ} (part : Fin n → Fin (m + 1)) (u v : Fin (m + 1)) (huv : u ≠ v)
    (x : Fin n) : Fin m :=
  compactIdx v (if part x = v then u else part x) (by split_ifs with h <;> [exact huv; exact h])

@[simp]
theorem embedCompact_contractPart {n m : ℕ} (part : Fin n → Fin (m + 1))
    (u v : Fin (m + 1)) (huv : u ≠ v) (x : Fin n) :
    embedCompact v (contractPart part u v huv x) = if part x = v then u else part x :=
  embedCompact_compactIdx v _ _

theorem filter_contractPart_eq {n m : ℕ} (part : Fin n → Fin (m + 1))
    (u v : Fin (m + 1)) (huv : u ≠ v) (i : Fin m) :
    (Finset.univ.filter fun x => contractPart part u v huv x = i) =
      if embedCompact v i = u then
        (Finset.univ.filter (part · = u)) ∪ (Finset.univ.filter (part · = v))
      else
        Finset.univ.filter (part · = embedCompact v i) := by
  have h_iff : ∀ x, (contractPart part u v huv x = i) ↔
      (if part x = v then u else part x) = embedCompact v i := by
    intro x
    constructor
    · rintro rfl
      exact (embedCompact_contractPart part u v huv x).symm
    · intro h
      exact embedCompact_injective v ((embedCompact_contractPart part u v huv x).trans h)
  split_ifs with hiu
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, h_iff, hiu]
    by_cases hxv : part x = v
    · simp [hxv]
    · simp [hxv]
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, h_iff]
    by_cases hxv : part x = v
    · have hiv : embedCompact v i ≠ v := embedCompact_ne v i
      simp [hxv, Ne.symm hiu, Ne.symm hiv]
    · simp [hxv]

theorem isContractionOf_contract {n m : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {part : Fin n → Fin (m + 1)} {W : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hC : IsContractionOf W₀ part W) {u v : Fin (m + 1)} (huv : u ≠ v) :
    IsContractionOf W₀ (contractPart part u v huv) (contractMatrix W u v) where
  surj i := by
    rcases hC.surj (embedCompact v i) with ⟨x, hx⟩
    refine ⟨x, embedCompact_injective v ?_⟩
    rw [embedCompact_contractPart, hx]
    simp [embedCompact_ne v i]
  multigraph := isMultigraph_contractMatrix hC.multigraph u v
  offDiag i j hij := by
    have he_ij : embedCompact v i ≠ embedCompact v j := fun h => hij (embedCompact_injective v h)
    have he_iv : embedCompact v i ≠ v := embedCompact_ne v i
    have he_jv : embedCompact v j ≠ v := embedCompact_ne v j
    have hdisj : Disjoint (Finset.univ.filter (part · = u)) (Finset.univ.filter (part · = v)) := by
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro x rfl hxv
      exact huv hxv
    rw [filter_contractPart_eq, filter_contractPart_eq]
    unfold contractMatrix mergePair
    simp only [he_ij, he_iv, he_jv, false_or, ↓reduceIte]
    by_cases hiu : embedCompact v i = u
    · have hju : embedCompact v j ≠ u := fun h => he_ij (hiu.trans h.symm)
      simp only [hiu, hju, ↓reduceIte, Finset.sum_union hdisj]
      rw [hC.offDiag u (embedCompact v j) (Ne.symm hju),
        hC.offDiag v (embedCompact v j) he_jv.symm]
    · by_cases hju : embedCompact v j = u
      · simp only [hiu, hju, ↓reduceIte]
        have hsum_union : ∀ x : Fin n,
            ∑ y ∈ Finset.univ.filter (part · = u) ∪ Finset.univ.filter (part · = v), W₀ x y =
              (∑ y ∈ Finset.univ.filter (part · = u), W₀ x y) +
                ∑ y ∈ Finset.univ.filter (part · = v), W₀ x y :=
          fun x => Finset.sum_union hdisj
        simp_rw [hsum_union, Finset.sum_add_distrib]
        rw [hC.offDiag (embedCompact v i) u hiu, hC.offDiag (embedCompact v i) v he_iv]
      · simp only [hiu, hju, ↓reduceIte]
        exact hC.offDiag (embedCompact v i) (embedCompact v j) he_ij

/-- Active cut induced on `Fin m` after contracting a non-crossing pair `(u, v)`. -/
def contractCut {m : ℕ} (v : Fin (m + 1)) (B : Finset (Fin (m + 1))) : Finset (Fin m) :=
  Finset.univ.filter fun i => embedCompact v i ∈ B

theorem pullbackCut_contractCut {n m : ℕ} (part : Fin n → Fin (m + 1))
    {u v : Fin (m + 1)} (huv : u ≠ v) {B : Finset (Fin (m + 1))}
    (hsame : u ∈ B ↔ v ∈ B) :
    pullbackCut (contractPart part u v huv) (contractCut v B) = pullbackCut part B := by
  ext x
  simp only [mem_pullbackCut, contractCut, Finset.mem_filter, Finset.mem_univ, true_and,
    embedCompact_contractPart]
  split_ifs with hxv
  · rw [hxv]
    exact hsame
  · rfl

/-- Pulling a cut back along the identity gives the same cut. -/
theorem pullbackCut_id {V : Type*} [Fintype V] [DecidableEq V] (C : Finset V) :
    pullbackCut id C = C := by
  ext x
  simp [pullbackCut]

/-- Merging `t` into `s` preserves the weight of the cuts that do not separate `s` and `t`. -/
theorem cutWeight_contractCut {k : ℕ} {W : Fin (k + 1) → Fin (k + 1) → ℕ} (hW : IsMultigraph W)
    {s t : Fin (k + 1)} (hst : s ≠ t) {C : Finset (Fin (k + 1))} (hC : s ∈ C ↔ t ∈ C) :
    cutWeight (contractMatrix W s t) (contractCut t C) = cutWeight W C := by
  have hc := isContractionOf_contract (isContractionOf_id hW) hst
  rw [← cutWeight_pullbackCut hc, pullbackCut_contractCut id hst hC, pullbackCut_id]

end Cslib.WeightedCut
