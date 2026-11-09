/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Pebbling.Blocking

/-!
# Black pebbling of pyramids

The pyramid `Π_h` of height `h` has levels `0, …, h`, with `h + 1 - k` vertices on level `k`.
The vertex at level `k + 1` and position `j` has the two predecessors at level `k` and positions
`j` and `j + 1`. Level `0` holds the sources and level `h` the single sink.

Cook proved that pebbling the sink of `Π_h` requires `h + 2` pebbles; we follow the formulation of
[Nordstrom2015Survey], Theorem 4.8, in the game without sliding. We
derive this from the path-blocking engine in `Complexity.Computability.Pebbling.Blocking`:
blocking the column path into one predecessor and the diagonal path into the other gives the
extra pebble at each level. The matching upper bound pebbles the two predecessors of a vertex one
after the other.

## Main definitions

* `Cslib.Pebbling.PyramidVertex h`, `Cslib.Pebbling.pyramid h`: the pyramid graph.
* `Cslib.Pebbling.PyramidVertex.top h`: its sink.
* `Cslib.Pebbling.PyramidVertex.below v`: the sub-pyramid with sink `v`.

## Main results

* `Cslib.Pebbling.blackPebblable_pyramid`: a vertex at level `k` is pebblable with `k + 2`
  pebbles.
* `Cslib.Pebbling.forcesPebbles_pyramid`: a vertex at level `k ≥ 1` forces `k + 2` pebbles on its
  sub-pyramid.
* `Cslib.Pebbling.blackPebblingPrice_pyramid_top`: **Cook's theorem**, the pyramid of height
  `h ≥ 1` has black pebbling price `h + 2`.

## References

* [S. A. Cook, *An observation on time-storage trade off*][Cook1974].
* [J. Nordström, *New wine into old wineskins*][Nordstrom2015Survey], Definition 4.5 and
  Theorem 4.8.
* [J. E. Savage, *Models of Computation*][Savage1998], Section 10.2 (with sliding, so its bound
  is one lower).
-/

public section

namespace Cslib.Pebbling

/-! ## Pyramids -/

/-- A vertex of the pyramid of height `h`: level `level ≤ h` (sources at level `0`, the sink at
level `h`) and position `pos` with `level + pos ≤ h`. -/
@[ext]
structure PyramidVertex (h : ℕ) where
  /-- The level, from `0` at the sources to `h` at the sink. -/
  level : ℕ
  /-- The position within the level. -/
  pos : ℕ
  /-- Level `k` has positions `0, …, h - k`. -/
  le : level + pos ≤ h
  deriving DecidableEq

/-- The pyramid graph `Π_h`. -/
def pyramid (h : ℕ) : Digraph (PyramidVertex h) where
  Adj u v := v.level = u.level + 1 ∧ (u.pos = v.pos ∨ u.pos = v.pos + 1)

/-- The sink of `Π_h`. -/
@[expose] def PyramidVertex.top (h : ℕ) : PyramidVertex h := ⟨h, 0, by omega⟩

@[simp] theorem pyramid_adj {h : ℕ} {u v : PyramidVertex h} :
    (pyramid h).Adj u v ↔ v.level = u.level + 1 ∧ (u.pos = v.pos ∨ u.pos = v.pos + 1) :=
  Iff.rfl

theorem blackPebblable_pyramid {h : ℕ} (v : PyramidVertex h) :
    BlackPebblable (pyramid h) (v.level + 2) v := by
  obtain ⟨k, j, hkj⟩ := v
  induction k generalizing j with
  | zero =>
    refine BlackPebblable.of_forall_adj (s := 1) ∅ (fun u hu => ?_) (by simp) (by simp)
      (by simp)
    simp only [pyramid_adj] at hu
    omega
  | succ k ih =>
    let y : PyramidVertex h := ⟨k, j, by omega⟩
    let z : PyramidVertex h := ⟨k, j + 1, by omega⟩
    have hyz := Finset.card_le_two (a := y) (b := z)
    change BlackPebblable _ (k + 1 + 2) _
    refine BlackPebblable.of_forall_adj (s := k + 2) {y, z} (fun u hu => ?_) ?_
      (by omega) (by omega)
    · simp only [pyramid_adj] at hu
      simp only [Finset.mem_insert, Finset.mem_singleton, PyramidVertex.ext_iff, y, z]
      omega
    · intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact ih j _
      · exact ih (j + 1) _

/-- The vertices of the sub-pyramid with sink `v`. -/
def PyramidVertex.below {h : ℕ} (v : PyramidVertex h) : Set (PyramidVertex h) :=
  {u | u.level ≤ v.level ∧ v.pos ≤ u.pos ∧ u.level + u.pos ≤ v.level + v.pos}

@[simp] theorem PyramidVertex.mem_below {h : ℕ} {u v : PyramidVertex h} :
    u ∈ v.below ↔ u.level ≤ v.level ∧ v.pos ≤ u.pos ∧ u.level + u.pos ≤ v.level + v.pos :=
  Iff.rfl

@[simp] theorem PyramidVertex.top_level (h : ℕ) : (PyramidVertex.top h).level = h := rfl

@[simp] theorem PyramidVertex.top_pos (h : ℕ) : (PyramidVertex.top h).pos = 0 := rfl

/-- The straight path into `v` from the source below it is open when `P` has no pebble on it. -/
private theorem pyramid_unblocked_column {h : ℕ} {P : Finset (PyramidVertex h)}
    (v : PyramidVertex h) (hP : ∀ w ∈ P, w.pos = v.pos → v.level < w.level) :
    Unblocked (pyramid h) P v := by
  obtain ⟨k, j, hkj⟩ := v
  induction k with
  | zero =>
    refine .source (fun u hu => ?_) (fun hv => lt_irrefl _ (hP _ hv rfl))
    simp only [pyramid_adj] at hu
    omega
  | succ k ih =>
    refine .step (u := ⟨k, j, by omega⟩) (ih (by omega) fun w hw hwj => ?_)
      (pyramid_adj.2 ⟨rfl, .inl rfl⟩) (fun hv => lt_irrefl _ (hP _ hv rfl))
    have := hP w hw hwj
    dsimp only at this ⊢
    omega

/-- The diagonal path into `v` is open when `P` has no pebble on it. -/
private theorem pyramid_unblocked_diagonal {h : ℕ} {P : Finset (PyramidVertex h)}
    (v : PyramidVertex h) (hP : ∀ w ∈ P, w.level + w.pos = v.level + v.pos → v.level < w.level) :
    Unblocked (pyramid h) P v := by
  obtain ⟨k, j, hkj⟩ := v
  induction k generalizing j with
  | zero =>
    refine .source (fun u hu => ?_) (fun hv => lt_irrefl _ (hP _ hv rfl))
    simp only [pyramid_adj] at hu
    omega
  | succ k ih =>
    refine .step (u := ⟨k, j + 1, by omega⟩) (ih (j + 1) (by omega) fun w hw hwj => ?_)
      (pyramid_adj.2 ⟨rfl, .inr rfl⟩) (fun hv => lt_irrefl _ (hP _ hv rfl))
    have := hP w hw (by dsimp only at hwj ⊢; omega)
    dsimp only at this ⊢
    omega

private theorem forcesPebbles_pyramid_aux {h : ℕ} (k j : ℕ) (hkj : k + 1 + j ≤ h) :
    ForcesPebbles (pyramid h) (PyramidVertex.below ⟨k + 1, j, hkj⟩) ⟨k + 1, j, hkj⟩ (k + 3) := by
  induction k generalizing j with
  | zero =>
    refine forcesPebbles_three (y := ⟨0, j, by omega⟩) (z := ⟨0, j + 1, by omega⟩)
      (pyramid_adj.2 ⟨rfl, .inl rfl⟩) (pyramid_adj.2 ⟨rfl, .inr rfl⟩)
      (fun h => absurd (congrArg PyramidVertex.pos h) (by dsimp only; omega)) ?_ ?_ ?_ <;>
    simp only [PyramidVertex.mem_below] <;> omega
  | succ k ih =>
    let y : PyramidVertex h := ⟨k + 1, j, by omega⟩
    let z : PyramidVertex h := ⟨k + 1, j + 1, by omega⟩
    rw [show k + 1 + 3 = k + 3 + 1 by omega]
    refine ForcesPebbles.step (y := y) (z := z) (Ry := y.below) (Rz := z.below)
      (pyramid_adj.2 ⟨rfl, .inl rfl⟩) (pyramid_adj.2 ⟨rfl, .inr rfl⟩) (fun u hu => ?_)
      (fun w hw => ?_) (fun w hw => ?_) (fun P hP => ?_) (fun P hP => ?_) (ih j _) (ih (j + 1) _)
    · simp only [pyramid_adj] at hu
      simp only [PyramidVertex.ext_iff, y, z]
      omega
    · simp only [PyramidVertex.mem_below, y] at hw ⊢
      omega
    · simp only [PyramidVertex.mem_below, z] at hw ⊢
      omega
    · by_contra hcon
      refine hP (pyramid_unblocked_column y fun w hw hwj => ?_)
      by_contra hlt
      refine hcon ⟨w, hw, ?_, ?_⟩ <;> simp only [PyramidVertex.mem_below, y, z] at hwj hlt ⊢ <;>
        omega
    · by_contra hcon
      refine hP (pyramid_unblocked_diagonal z fun w hw hwj => ?_)
      by_contra hlt
      refine hcon ⟨w, hw, ?_, ?_⟩ <;> simp only [PyramidVertex.mem_below, y, z] at hwj hlt ⊢ <;>
        omega

/-- Cook's path-blocking argument: every vertex `v` of `Π_h` above the sources forces
`v.level + 2` pebbles on the sub-pyramid below it. -/
theorem forcesPebbles_pyramid {h : ℕ} (v : PyramidVertex h) (hv : v.level ≠ 0) :
    ForcesPebbles (pyramid h) v.below v (v.level + 2) := by
  obtain ⟨_ | k, j, hkj⟩ := v
  · exact absurd rfl hv
  · exact forcesPebbles_pyramid_aux k j hkj

theorem unblocked_pyramid_empty {h : ℕ} (v : PyramidVertex h) : Unblocked (pyramid h) ∅ v :=
  pyramid_unblocked_column v fun w hw => absurd hw (Finset.notMem_empty w)

/-- Every successful budget for a vertex of `Π_h` at level `k ≥ 1` is at least `k + 2`. -/
theorem PyramidVertex.le_of_blackPebblable {h s : ℕ} {v : PyramidVertex h} (hv : v.level ≠ 0)
    (hs : BlackPebblable (pyramid h) s v) : v.level + 2 ≤ s :=
  (forcesPebbles_pyramid v hv).le_of_blackPebblable (unblocked_pyramid_empty v) hs

/-- The black pebbling price of a vertex of `Π_h` at level `k ≥ 1` is `k + 2`. -/
theorem blackPebblingPrice_pyramid {h : ℕ} (v : PyramidVertex h) (hv : v.level ≠ 0) :
    blackPebblingPrice (pyramid h) v = v.level + 2 :=
  blackPebblingPrice_eq (blackPebblable_pyramid v) fun _ => PyramidVertex.le_of_blackPebblable hv

/-- **Cook's theorem.** The pyramid of height `h ≥ 1` has black pebbling price `h + 2`. -/
theorem blackPebblingPrice_pyramid_top {h : ℕ} (hh : h ≠ 0) :
    blackPebblingPrice (pyramid h) (PyramidVertex.top h) = h + 2 :=
  blackPebblingPrice_pyramid _ hh

end Cslib.Pebbling
