/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Protocol
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Cslib.Foundations.Data.Fin.Tuple

/-!
# Protocols partition the inputs into rectangles

A *combinatorial rectangle* is a product `A ×ˢ B` of a set `A` of Alice's inputs and a set `B` of
Bob's inputs. The inputs on which a deterministic protocol reaches a given leaf form a rectangle:
a bit sent by Alice splits only Alice's side, and a bit sent by Bob only Bob's side. Numbering the
leaves from left to right, the protocol reaches leaf `i` on `x` and `y` exactly when `x` lies in
Alice's side `leafAlice i` and `y` in Bob's side `leafBob i` (`Protocol.leaf_eq_iff`), and its
output there is the label `leafOutput i` of the leaf (`Protocol.run_eq_leafOutput`). So a protocol
sending `d` bits partitions `X × Y` into at most `2 ^ d` rectangles on each of which its output is
constant (`Protocol.exists_rectangle_partition`); some of them may be empty
[Kushilevitz and Nisan, Chapter 1][KushilevitzNisan1997]. When the protocol solves a relation on
`A × B`, the label of each leaf is a valid answer on the part of its rectangle inside `A × B`
(`Protocol.Solves.solves_leafOutput`).

Sums over all pairs of inputs split into sums over the leaf rectangles
(`Protocol.sum_eq_sum_leaves`); so if each leaf rectangle labelled `z` has weight at most `K`, the
inputs on which the protocol answers `z` have weight at most `K` times the number of such leaves
(`Protocol.sum_filter_run_le_mul`). A protocol *computes* `f : X → Y → Z` when its output is `f`,
which is solving the relation `f x y = z` on all inputs (`Protocol.solves_univ_iff`). Counting
leaves by their labels turns bounds on rectangles into lower bounds on protocols: if `f` is
constantly `z` only on rectangles of weight at most `K`, the inputs where `f` is `z` have weight at
most `K` times the number of leaves labelled `z`, for every protocol computing `f`
(`Protocol.sum_filter_le_mul`). Counting every input once, `|f⁻¹(z)| ≤ K · #{leaves labelled z}`
when `f` is constantly `z` only on rectangles with at most `K` entries
(`Protocol.card_filter_le_mul`).

## Main definitions

* `Cslib.Communication.Protocol.leaf`: the leaf a protocol reaches.
* `Cslib.Communication.Protocol.leafOutput`: the labels of the leaves.
* `Cslib.Communication.Protocol.leafAlice`, `Cslib.Communication.Protocol.leafBob`: the sides of
  the rectangles of the leaves.

## Main results

* `Cslib.Communication.Protocol.leaf_eq_iff`: the inputs reaching a leaf form a rectangle.
* `Cslib.Communication.Protocol.run_eq_leafOutput`: the output is constant on each rectangle.
* `Cslib.Communication.Protocol.exists_rectangle_partition`: a protocol sending `d` bits
  partitions the inputs into at most `2 ^ d` monochromatic rectangles.
* `Cslib.Communication.Protocol.Solves.solves_leafOutput`: leaf rectangles inside the inputs of a
  solved relation are monochromatic.
* `Cslib.Communication.Protocol.sum_eq_sum_leaves`: sums over the leaf rectangles.
* `Cslib.Communication.Protocol.sum_filter_run_le_mul`: weights of the leaves with a given label.
* `Cslib.Communication.Protocol.sum_filter_le_mul`: the weighted area bound.
* `Cslib.Communication.Protocol.card_filter_le_mul`: the area bound.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication.Protocol

open Finset

variable {X Y Z : Type*}

/-- The leaf a protocol reaches when Alice holds `x` and Bob holds `y`, numbering the leaves from
left to right. -/
def leaf : (p : Protocol X Y Z) → X → Y → Fin p.leafCount
  | output _, _, _ => (0 : Fin 1)
  | alice send p₀ p₁, x, y =>
    cond (send x) (Fin.natAdd p₀.leafCount (p₁.leaf x y)) (Fin.castAdd p₁.leafCount (p₀.leaf x y))
  | bob send p₀ p₁, x, y =>
    cond (send y) (Fin.natAdd p₀.leafCount (p₁.leaf x y)) (Fin.castAdd p₁.leafCount (p₀.leaf x y))

/-- The label of each leaf, numbering the leaves from left to right. -/
def leafOutput : (p : Protocol X Y Z) → Fin p.leafCount → Z
  | output z => fun _ => z
  | alice _ p₀ p₁ => Fin.append p₀.leafOutput p₁.leafOutput
  | bob _ p₀ p₁ => Fin.append p₀.leafOutput p₁.leafOutput

/-- Alice's side of the rectangle of each leaf: the inputs of Alice consistent with the bits she
sends on the path to the leaf. -/
def leafAlice : (p : Protocol X Y Z) → Fin p.leafCount → Set X
  | output _ => fun _ => Set.univ
  | alice send p₀ p₁ => Fin.append (fun i => {x | send x = false} ∩ p₀.leafAlice i)
      (fun i => {x | send x = true} ∩ p₁.leafAlice i)
  | bob _ p₀ p₁ => Fin.append p₀.leafAlice p₁.leafAlice

/-- Bob's side of the rectangle of each leaf: the inputs of Bob consistent with the bits he sends
on the path to the leaf. -/
def leafBob : (p : Protocol X Y Z) → Fin p.leafCount → Set Y
  | output _ => fun _ => Set.univ
  | alice _ p₀ p₁ => Fin.append p₀.leafBob p₁.leafBob
  | bob send p₀ p₁ => Fin.append (fun i => {y | send y = false} ∩ p₀.leafBob i)
      (fun i => {y | send y = true} ∩ p₁.leafBob i)

section Simp

variable (z : Z) (send : X → Bool) (send' : Y → Bool) (p₀ p₁ : Protocol X Y Z) (x : X) (y : Y)

@[simp] theorem leaf_output : (output z : Protocol X Y Z).leaf x y = ⟨0, Nat.zero_lt_one⟩ :=
  rfl

@[simp] theorem leaf_alice : (alice send p₀ p₁).leaf x y =
    cond (send x) (Fin.natAdd p₀.leafCount (p₁.leaf x y))
      (Fin.castAdd p₁.leafCount (p₀.leaf x y)) :=
  rfl

@[simp] theorem leaf_bob : (bob send' p₀ p₁).leaf x y =
    cond (send' y) (Fin.natAdd p₀.leafCount (p₁.leaf x y))
      (Fin.castAdd p₁.leafCount (p₀.leaf x y)) :=
  rfl

@[simp] theorem leafOutput_output (i : Fin (output z : Protocol X Y Z).leafCount) :
    (output z : Protocol X Y Z).leafOutput i = z :=
  rfl

@[simp] theorem leafOutput_alice_castAdd (i : Fin p₀.leafCount) :
    (alice send p₀ p₁).leafOutput (Fin.castAdd p₁.leafCount i) = p₀.leafOutput i :=
  Fin.append_left _ _ i

@[simp] theorem leafOutput_alice_natAdd (i : Fin p₁.leafCount) :
    (alice send p₀ p₁).leafOutput (Fin.natAdd p₀.leafCount i) = p₁.leafOutput i :=
  Fin.append_right _ _ i

@[simp] theorem leafOutput_bob_castAdd (i : Fin p₀.leafCount) :
    (bob send' p₀ p₁).leafOutput (Fin.castAdd p₁.leafCount i) = p₀.leafOutput i :=
  Fin.append_left _ _ i

@[simp] theorem leafOutput_bob_natAdd (i : Fin p₁.leafCount) :
    (bob send' p₀ p₁).leafOutput (Fin.natAdd p₀.leafCount i) = p₁.leafOutput i :=
  Fin.append_right _ _ i

@[simp] theorem leafAlice_output (i : Fin (output z : Protocol X Y Z).leafCount) :
    (output z : Protocol X Y Z).leafAlice i = Set.univ :=
  rfl

@[simp] theorem leafAlice_alice_castAdd (i : Fin p₀.leafCount) :
    (alice send p₀ p₁).leafAlice (Fin.castAdd p₁.leafCount i) =
      {x | send x = false} ∩ p₀.leafAlice i :=
  Fin.append_left _ _ i

@[simp] theorem leafAlice_alice_natAdd (i : Fin p₁.leafCount) :
    (alice send p₀ p₁).leafAlice (Fin.natAdd p₀.leafCount i) =
      {x | send x = true} ∩ p₁.leafAlice i :=
  Fin.append_right _ _ i

@[simp] theorem leafAlice_bob_castAdd (i : Fin p₀.leafCount) :
    (bob send' p₀ p₁).leafAlice (Fin.castAdd p₁.leafCount i) = p₀.leafAlice i :=
  Fin.append_left _ _ i

@[simp] theorem leafAlice_bob_natAdd (i : Fin p₁.leafCount) :
    (bob send' p₀ p₁).leafAlice (Fin.natAdd p₀.leafCount i) = p₁.leafAlice i :=
  Fin.append_right _ _ i

@[simp] theorem leafBob_output (i : Fin (output z : Protocol X Y Z).leafCount) :
    (output z : Protocol X Y Z).leafBob i = Set.univ :=
  rfl

@[simp] theorem leafBob_alice_castAdd (i : Fin p₀.leafCount) :
    (alice send p₀ p₁).leafBob (Fin.castAdd p₁.leafCount i) = p₀.leafBob i :=
  Fin.append_left _ _ i

@[simp] theorem leafBob_alice_natAdd (i : Fin p₁.leafCount) :
    (alice send p₀ p₁).leafBob (Fin.natAdd p₀.leafCount i) = p₁.leafBob i :=
  Fin.append_right _ _ i

@[simp] theorem leafBob_bob_castAdd (i : Fin p₀.leafCount) :
    (bob send' p₀ p₁).leafBob (Fin.castAdd p₁.leafCount i) = {y | send' y = false} ∩ p₀.leafBob i :=
  Fin.append_left _ _ i

@[simp] theorem leafBob_bob_natAdd (i : Fin p₁.leafCount) :
    (bob send' p₀ p₁).leafBob (Fin.natAdd p₀.leafCount i) = {y | send' y = true} ∩ p₁.leafBob i :=
  Fin.append_right _ _ i

end Simp

/-- **The inputs reaching a leaf form a rectangle**: the protocol reaches leaf `i` on `x` and `y`
exactly when `x` is on Alice's side and `y` on Bob's side of its rectangle. -/
theorem leaf_eq_iff {p : Protocol X Y Z} {x : X} {y : Y} {i : Fin p.leafCount} :
    p.leaf x y = i ↔ x ∈ p.leafAlice i ∧ y ∈ p.leafBob i := by
  induction p with
  | output z =>
    simp only [leaf, leafAlice, leafBob, Set.mem_univ, and_self, iff_true]
    exact Subsingleton.elim (α := Fin 1) _ _
  | alice send p₀ p₁ ih₀ ih₁ =>
    induction i using Fin.addCases with
    | left i =>
      cases h : send x <;>
        simp [leaf, leafAlice, leafBob, h, ih₀, Fin.castAdd_inj, (Fin.castAdd_ne_natAdd _ _).symm]
    | right i =>
      cases h : send x <;>
        simp [leaf, leafAlice, leafBob, h, ih₁, Fin.natAdd_inj, Fin.castAdd_ne_natAdd]
  | bob send p₀ p₁ ih₀ ih₁ =>
    induction i using Fin.addCases with
    | left i =>
      cases h : send y <;>
        simp [leaf, leafAlice, leafBob, h, ih₀, Fin.castAdd_inj, (Fin.castAdd_ne_natAdd _ _).symm]
    | right i =>
      cases h : send y <;>
        simp [leaf, leafAlice, leafBob, h, ih₁, Fin.natAdd_inj, Fin.castAdd_ne_natAdd]

variable {p : Protocol X Y Z} {x : X} {y : Y}

theorem mem_leafAlice_leaf : x ∈ p.leafAlice (p.leaf x y) :=
  (leaf_eq_iff.mp rfl).1

theorem mem_leafBob_leaf : y ∈ p.leafBob (p.leaf x y) :=
  (leaf_eq_iff.mp rfl).2

/-- The output of a protocol is the label of the leaf it reaches. -/
theorem run_eq_leafOutput_leaf (p : Protocol X Y Z) (x : X) (y : Y) :
    p.run x y = p.leafOutput (p.leaf x y) := by
  induction p with
  | output z => rfl
  | alice send p₀ p₁ ih₀ ih₁ =>
    cases h : send x <;> simp [leaf, leafOutput, h, ih₀, ih₁]
  | bob send p₀ p₁ ih₀ ih₁ =>
    cases h : send y <;> simp [leaf, leafOutput, h, ih₀, ih₁]

/-- **The output is constant on each leaf rectangle.** -/
theorem run_eq_leafOutput {i : Fin p.leafCount} (hx : x ∈ p.leafAlice i) (hy : y ∈ p.leafBob i) :
    p.run x y = p.leafOutput i := by
  rw [run_eq_leafOutput_leaf, leaf_eq_iff.mpr ⟨hx, hy⟩]

/-- **A protocol sending `d` bits partitions `X × Y` into at most `2 ^ d` monochromatic
rectangles**: there are at most `2 ^ d` rectangles `A i ×ˢ B i`, possibly empty, such that every
pair of inputs lies in exactly one of them and the output of the protocol is constant on each. -/
theorem exists_rectangle_partition (p : Protocol X Y Z) :
    ∃ (n : ℕ) (A : Fin n → Set X) (B : Fin n → Set Y) (z : Fin n → Z), n ≤ 2 ^ p.depth ∧
      (∀ x y, ∃! i, x ∈ A i ∧ y ∈ B i) ∧ ∀ i, ∀ x ∈ A i, ∀ y ∈ B i, p.run x y = z i :=
  ⟨p.leafCount, p.leafAlice, p.leafBob, p.leafOutput, p.leafCount_le_two_pow_depth,
    fun x y => ⟨p.leaf x y, leaf_eq_iff.mp rfl, fun _ hi => (leaf_eq_iff.mpr hi).symm⟩,
    fun _ _ hx _ hy => run_eq_leafOutput hx hy⟩

variable {R : X → Y → Z → Prop} {A : Set X} {B : Set Y}

/-- **Leaf rectangles are monochromatic**: if a protocol solves `R` on `A × B`, the label of each
leaf is a valid answer on the part of the leaf's rectangle inside `A × B`. -/
theorem Solves.solves_leafOutput (hp : p.Solves R A B) (i : Fin p.leafCount) :
    Communication.Solves (fun _ _ => p.leafOutput i) R (A ∩ p.leafAlice i) (B ∩ p.leafBob i) :=
  fun x hx y hy => run_eq_leafOutput hx.2 hy.2 ▸ hp x hx.1 y hy.1

/-! ### Sums over leaf rectangles -/

section Sums

variable [Fintype X] [Fintype Y]

open Classical in
/-- **Sums over leaf rectangles.** A sum over all pairs of inputs is the sum, over the leaves of a
protocol, of the sums over their rectangles. -/
theorem sum_eq_sum_leaves {M : Type*} [AddCommMonoid M] (p : Protocol X Y Z) (g : X → Y → M) :
    ∑ x, ∑ y, g x y =
      ∑ i, ∑ x with x ∈ p.leafAlice i, ∑ y with y ∈ p.leafBob i, g x y := by
  rw [← Fintype.sum_prod_type', ← sum_fiberwise univ (fun q : X × Y => p.leaf q.1 q.2)]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_product']
  refine sum_congr ?_ fun _ _ => rfl
  ext q
  simp [leaf_eq_iff]

open Classical in
/-- **Weights of the leaves with a given label.** If every leaf rectangle labelled `z` has weight
at most `K` under `w`, the inputs on which the protocol answers `z` have weight at most `K` times
the number of leaves labelled `z`. The weights take values in an ordered semiring such as `ℕ` or
`ℝ`, and may be negative. -/
theorem sum_filter_run_le_mul {M : Type*} [Semiring M] [PartialOrder M] [IsOrderedAddMonoid M]
    [DecidableEq Z] (p : Protocol X Y Z) (z : Z) (w : X → Y → M) {K : M}
    (hK : ∀ i, p.leafOutput i = z →
      ∑ x with x ∈ p.leafAlice i, ∑ y with y ∈ p.leafBob i, w x y ≤ K) :
    ∑ q : X × Y with p.run q.1 q.2 = z, w q.1 q.2 ≤ #{i | p.leafOutput i = z} * K := by
  rw [sum_filter, Fintype.sum_prod_type' (fun x y => if p.run x y = z then w x y else 0),
    p.sum_eq_sum_leaves, card_eq_sum_ones, Nat.cast_sum, sum_mul, sum_filter]
  refine sum_le_sum fun i _ => ?_
  have hrect : ∀ x ∈ ({x | x ∈ p.leafAlice i} : Finset X),
      ∀ y ∈ ({y | y ∈ p.leafBob i} : Finset Y), p.run x y = p.leafOutput i := fun x hx y hy =>
    run_eq_leafOutput (mem_filter.mp hx).2 (mem_filter.mp hy).2
  split_ifs with hi
  · rw [Nat.cast_one, one_mul]
    refine le_of_eq_of_le (sum_congr rfl fun x hx => sum_congr rfl fun y hy => ?_) (hK i hi)
    simp [hrect x hx y hy, hi]
  · refine (sum_eq_zero fun x hx => sum_eq_zero fun y hy => ?_).le
    simp [hrect x hx y hy, hi]

/-- **The weighted area bound.** If `f` is constantly `z` only on rectangles of weight at most `K`
under `w`, then for every protocol computing `f` the inputs where `f` is `z` have weight at most
`K` times the number of leaves labelled `z`. The weights take values in an ordered semiring such
as `ℕ` or `ℝ`, and may be negative. -/
theorem sum_filter_le_mul {M : Type*} [Semiring M] [PartialOrder M] [IsOrderedAddMonoid M]
    [DecidableEq Z] {f : X → Y → Z} (hp : p.run = f) (z : Z) (w : X → Y → M) {K : M}
    (hK : ∀ (A : Finset X) (B : Finset Y), (∀ x ∈ A, ∀ y ∈ B, f x y = z) →
      ∑ x ∈ A, ∑ y ∈ B, w x y ≤ K) :
    ∑ q : X × Y with f q.1 q.2 = z, w q.1 q.2 ≤ #{i | p.leafOutput i = z} * K := by
  subst hp
  classical
  exact p.sum_filter_run_le_mul z w fun i hi => hK _ _ fun x hx y hy => by
    rw [run_eq_leafOutput (mem_filter.mp hx).2 (mem_filter.mp hy).2, hi]

/-- **The area bound.** If `f` is constantly `z` only on rectangles with at most `K` entries, every
protocol computing `f` has at least `|f⁻¹(z)| / K` leaves labelled `z`. -/
theorem card_filter_le_mul [DecidableEq Z] {f : X → Y → Z} (hp : p.run = f) (z : Z) {K : ℕ}
    (hK : ∀ (A : Finset X) (B : Finset Y), (∀ x ∈ A, ∀ y ∈ B, f x y = z) → #A * #B ≤ K) :
    #{q : X × Y | f q.1 q.2 = z} ≤ #{i | p.leafOutput i = z} * K := by
  have h := sum_filter_le_mul hp z (fun _ _ => 1) fun A B hAB => by
    simpa only [sum_const, smul_eq_mul, mul_one] using hK A B hAB
  simpa only [sum_const, smul_eq_mul, mul_one, Nat.cast_id] using h

end Sums

end Cslib.Communication.Protocol
