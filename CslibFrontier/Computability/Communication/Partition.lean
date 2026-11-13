/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import CslibFrontier.Foundations.Data.ENat.IInf
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-!
# Arbitrary labelled rectangle partitions and monochromatic tilings

A `RectanglePartition X Y Z` is a finite family of labelled Cartesian rectangles covering
`X × Y` exactly once. It need not arise from a protocol tree. Its `run` function is constant
on each rectangle; conversely, `p.run = f` says that it is a monochromatic tiling of `f`.
Empty pieces are allowed and count toward `size`, but cannot improve the minimum.

The minimum `tilingNumber f` is the infimum of all such sizes in `ℕ∞`, with value `⊤` if
there is no finite tiling. For finite input types, singleton rectangles supply a tiling,
including the zero-piece tiling of an empty input domain, and the minimum is attained.
This is the partition notion of [AroraBarak07, Definition 12.6].

## Main definitions

* `Cslib.Communication.RectanglePartition`: labelled rectangle partitions.
* `Cslib.Communication.RectanglePartition.part`: the unique piece containing an input pair.
* `Cslib.Communication.RectanglePartition.run`: the label of that piece.
* `Cslib.Communication.tilingNumber`: the minimum number of monochromatic rectangles.

## Main results

* `Cslib.Communication.RectanglePartition.sum_eq_sum_rectangles`: sums split over the pieces.
* `Cslib.Communication.exists_minimal_tiling`: finite inputs admit a minimum-size tiling.
* `Cslib.Communication.le_tilingNumber_iff`: lower bounds reduce to arbitrary tilings.
-/

public section

namespace Cslib.Communication

variable {X Y Z : Type*}

/-- A finite labelled partition into Cartesian rectangles, independently of protocol trees. -/
structure RectanglePartition (X Y Z : Type*) where
  /-- Number of pieces, including any empty rectangles. -/
  size : ℕ
  /-- Alice's side of each rectangle. -/
  alice : Fin size → Set X
  /-- Bob's side of each rectangle. -/
  bob : Fin size → Set Y
  /-- Output label of each rectangle. -/
  output : Fin size → Z
  /-- Each input pair belongs to exactly one rectangle. -/
  partition : ∀ x y, ∃! i, x ∈ alice i ∧ y ∈ bob i

namespace RectanglePartition

/-- The unique rectangle containing a pair of inputs. -/
noncomputable def part (p : RectanglePartition X Y Z) (x : X) (y : Y) : Fin p.size :=
  (p.partition x y).choose

/-- Each input pair belongs to the rectangle selected by `part`. -/
theorem part_mem (p : RectanglePartition X Y Z) (x : X) (y : Y) :
    x ∈ p.alice (p.part x y) ∧ y ∈ p.bob (p.part x y) :=
  (p.partition x y).choose_spec.1

/-- Membership in a rectangle characterizes the selected piece. -/
theorem part_eq_iff {p : RectanglePartition X Y Z} {x : X} {y : Y} {i : Fin p.size} :
    p.part x y = i ↔ x ∈ p.alice i ∧ y ∈ p.bob i :=
  ⟨fun h => h ▸ p.part_mem x y, fun h => ((p.partition x y).choose_spec.2 i h).symm⟩

/-- The function computed by the labels of a rectangle partition. -/
noncomputable def run (p : RectanglePartition X Y Z) (x : X) (y : Y) : Z :=
  p.output (p.part x y)

/-- The value is the label of the unique containing rectangle. -/
theorem run_eq_output_part (p : RectanglePartition X Y Z) (x : X) (y : Y) :
    p.run x y = p.output (p.part x y) := by rfl

/-- The function is constant on each rectangle. -/
theorem run_eq_output {p : RectanglePartition X Y Z} {x : X} {y : Y} {i : Fin p.size}
    (hx : x ∈ p.alice i) (hy : y ∈ p.bob i) : p.run x y = p.output i := by
  rw [run_eq_output_part, part_eq_iff.mpr ⟨hx, hy⟩]

open Classical in
/-- Sums over the input domain split exactly over all rectangle pieces. -/
theorem sum_eq_sum_rectangles [Fintype X] [Fintype Y] {M : Type*} [AddCommMonoid M]
    (p : RectanglePartition X Y Z) (g : X → Y → M) :
    ∑ x, ∑ y, g x y =
      ∑ i, ∑ x with x ∈ p.alice i, ∑ y with y ∈ p.bob i, g x y := by
  classical
  rw [← Fintype.sum_prod_type', ← Finset.sum_fiberwise Finset.univ
    (fun q : X × Y => p.part q.1 q.2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_product']
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext q
  simp [part_eq_iff]

/-- A constant function has a one-rectangle tiling, also when the input domain is empty. -/
@[expose] def constant (X Y : Type*) (z : Z) : RectanglePartition X Y Z where
  size := 1
  alice _ := Set.univ
  bob _ := Set.univ
  output _ := z
  partition _ _ := ⟨0, ⟨trivial, trivial⟩, fun i _ => Subsingleton.elim i 0⟩

/-- The whole-domain rectangle computes its constant label. -/
theorem run_constant (X Y : Type*) (z : Z) :
    (constant X Y z).run = fun _ _ => z := by
  funext x y
  rw [run_eq_output_part]
  rfl

/-- Singleton rectangles give a tiling of any function on finite inputs. -/
@[expose] noncomputable def singletons [Fintype X] [Fintype Y] (f : X → Y → Z) :
    RectanglePartition X Y Z where
  size := Fintype.card (X × Y)
  alice i := {((Fintype.equivFin (X × Y)).symm i).1}
  bob i := {((Fintype.equivFin (X × Y)).symm i).2}
  output i := f ((Fintype.equivFin (X × Y)).symm i).1
    ((Fintype.equivFin (X × Y)).symm i).2
  partition x y := by
    refine ⟨Fintype.equivFin (X × Y) (x, y), by simp, ?_⟩
    intro i hi
    apply (Fintype.equivFin (X × Y)).symm.injective
    simpa only [Equiv.symm_apply_apply] using Prod.ext hi.1.symm hi.2.symm

/-- The singleton tiling computes the original function, even on an empty input domain. -/
theorem run_singletons [Fintype X] [Fintype Y] (f : X → Y → Z) :
    (singletons f).run = f := by
  funext x y
  have h := run_eq_output (p := singletons f) (x := x) (y := y)
    (i := Fintype.equivFin (X × Y) (x, y)) (by simp [singletons]) (by simp [singletons])
  simpa [singletons] using h

end RectanglePartition

/-- The minimum number of rectangles in a monochromatic tiling of `f`, or `⊤` if there is no
finite tiling. Empty pieces are counted, so including them cannot lower the infimum. -/
noncomputable def tilingNumber (f : X → Y → Z) : ℕ∞ :=
  ⨅ p : {p : RectanglePartition X Y Z // p.run = f}, (p.val.size : ℕ∞)

/-- Any monochromatic tiling bounds the minimum tiling number. -/
theorem RectanglePartition.tilingNumber_le (p : RectanglePartition X Y Z) {f : X → Y → Z}
    (hp : p.run = f) : tilingNumber f ≤ p.size :=
  iInf_le (fun p : {p : RectanglePartition X Y Z // p.run = f} => (p.val.size : ℕ∞)) ⟨p, hp⟩

/-- Lower bounds on the tiling number are exactly bounds on every monochromatic tiling. -/
theorem le_tilingNumber_iff {f : X → Y → Z} {c : ℕ∞} :
    c ≤ tilingNumber f ↔ ∀ p : RectanglePartition X Y Z, p.run = f → c ≤ p.size := by
  simp only [tilingNumber, le_iInf_iff, Subtype.forall]

/-- A finite bound on the tiling number is witnessed by a tiling of at most that size. -/
theorem tilingNumber_le_iff {f : X → Y → Z} {n : ℕ} :
    tilingNumber f ≤ n ↔ ∃ p : RectanglePartition X Y Z, p.run = f ∧ p.size ≤ n := by
  simp only [tilingNumber, ENat.iInf_natCast_le_natCast_iff, Subtype.exists, exists_prop]

/-- On finite input types the minimum is attained; no protocol realization is assumed. -/
theorem exists_minimal_tiling [Finite X] [Finite Y] (f : X → Y → Z) :
    ∃ p : RectanglePartition X Y Z, p.run = f ∧ (p.size : ℕ∞) = tilingNumber f := by
  let := Fintype.ofFinite X
  let := Fintype.ofFinite Y
  have : Nonempty {p : RectanglePartition X Y Z // p.run = f} :=
    ⟨⟨RectanglePartition.singletons f, RectanglePartition.run_singletons f⟩⟩
  obtain ⟨p, hp⟩ := ENat.exists_eq_iInf
    (fun p : {p : RectanglePartition X Y Z // p.run = f} => (p.val.size : ℕ∞))
  exact ⟨p.val, p.property, hp⟩

end Cslib.Communication
