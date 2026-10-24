/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Allocation
public import Mathlib.Data.Finset.Union

/-!
# Finite-footprint memory assertions

Assertions record a finite footprint and depend only on its cells. Separating conjunction
requires disjoint footprints. This is an assertion and frame calculus over the RAM's total
memory, not a new allocator or a claim that inaccessible cells cease to exist.

## Main definitions

* `Block.footprint`: the finite set of memory cells owned by a contiguous block.
* `HeapAssertion`: a memory predicate supported on a finite footprint.
* `HeapAssertion.pure`, `HeapAssertion.sep`, `HeapAssertion.pointsto`, `HeapAssertion.array`:
  representation primitives.
* `Modifies`: equality outside a permitted set of writes.

## Main results

* `HeapAssertion.frame`: writes to a disjoint region preserve an assertion.
* `HeapAssertion.sep_comm`: separating conjunction is commutative at the predicate level.

## References

The footprint/frame principle is the standard locality principle of separation logic;
this file uses explicit finite supports rather than partial-heap semantics. See
[J. C. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*][Reynolds2002].
-/

@[expose] public section

namespace Cslib.WordRAM

/-- The finite set of memory cells owned by the block. -/
def Block.footprint (b : Block) : Finset ℕ :=
  (Finset.range b.length).image (b.base + ·)

/-- An address belongs to `b.footprint` if and only if `b` owns it. -/
@[simp]
theorem Block.mem_footprint {b : Block} {a : ℕ} : a ∈ b.footprint ↔ b.Owns a := by
  simp only [Block.footprint, Finset.mem_image, Finset.mem_range, Block.Owns]
  exact ⟨fun ⟨i, hi, ha⟩ => ⟨by omega, by omega⟩,
    fun ⟨hlo, hhi⟩ => ⟨a - b.base, by omega, by omega⟩⟩

/-- The cardinality of `b.footprint` equals `b.length`. -/
@[simp]
theorem Block.card_footprint (b : Block) : b.footprint.card = b.length := by
  rw [Block.footprint, Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
    Finset.card_range]

/-- A predicate depending only on a finite set of memory cells. -/
structure HeapAssertion where
  /-- Cells on which the predicate may depend. -/
  footprint : Finset ℕ
  /-- The asserted property of total RAM memory. -/
  holds : (ℕ → ℕ) → Prop
  /-- Agreement on owned cells transports the assertion. -/
  supported : ∀ {m m'}, (∀ a ∈ footprint, m a = m' a) → holds m → holds m'

/-- The two memories agree outside the permitted write footprint. -/
def Modifies (writes : Finset ℕ) (m m' : ℕ → ℕ) : Prop :=
  ∀ a ∉ writes, m' a = m a

namespace Modifies

/-- An unchanged memory modifies no cells. -/
theorem refl (F : Finset ℕ) (m : ℕ → ℕ) : Modifies F m m := fun _ _ => rfl

/-- Sequential writes use the union of the permitted regions. -/
theorem trans {F G : Finset ℕ} {m m' m'' : ℕ → ℕ}
    (h : Modifies F m m') (h' : Modifies G m' m'') : Modifies (F ∪ G) m m'' := by
  intro a ha
  have ha' := Finset.notMem_union.mp ha
  exact (h' a ha'.2).trans (h a ha'.1)

/-- A single write modifies at most its destination. -/
theorem update (m : ℕ → ℕ) (a v : ℕ) : Modifies {a} m (Function.update m a v) := by
  intro b hb
  exact Function.update_of_ne (by simpa using hb) v m

/-- Writing a cell owned by a block modifies at most the block's footprint. -/
theorem write_of_owns {base n a : ℕ} {m : ℕ → ℕ} (ha : base ≤ a ∧ a < base + n) (v : ℕ) :
    Modifies (Block.mk base n).footprint m (Function.update m a v) := by
  intro c hc
  have hne : c ≠ a := fun h => hc (Block.mem_footprint.mpr (h ▸ ha))
  exact Function.update_of_ne hne v m

/-- Modifying at most a block's footprint is equivalent to preserving all cells outside its
address interval. -/
theorem block_iff {b : Block} {m m' : ℕ → ℕ} :
    Modifies b.footprint m m' ↔ ∀ a, a < b.base ∨ b.base + b.length ≤ a → m' a = m a := by
  simp only [Modifies, Block.mem_footprint, Block.Owns]
  constructor <;> intro h a ha <;> exact h a (by omega)

end Modifies

namespace HeapAssertion

/-- A memory-free assertion. -/
def pure (P : Prop) : HeapAssertion where
  footprint := ∅
  holds _ := P
  supported _ h := h

/-- A single owned cell with specified contents. -/
def pointsto (a v : ℕ) : HeapAssertion where
  footprint := {a}
  holds m := m a = v
  supported h hm := (h a (Finset.mem_singleton_self a)).symm.trans hm

/-- A record, or array, of consecutive owned cells. -/
def array (base n : ℕ) (values : Fin n → ℕ) : HeapAssertion where
  footprint := (Block.mk base n).footprint
  holds m := (Block.mk base n).Realizes m values
  supported h hm i := by
    dsimp only [Block.Realizes, Block.read] at hm ⊢
    exact (h (base + i) (Block.mem_footprint.mpr
      ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt _⟩)).symm.trans (hm i)

/-- Conjunction of assertions with disjoint ownership. -/
def sep (P Q : HeapAssertion) : HeapAssertion where
  footprint := P.footprint ∪ Q.footprint
  holds m := Disjoint P.footprint Q.footprint ∧ P.holds m ∧ Q.holds m
  supported h hm := ⟨hm.1,
    P.supported (fun a ha => h a (Finset.mem_union_left _ ha)) hm.2.1,
    Q.supported (fun a ha => h a (Finset.mem_union_right _ ha)) hm.2.2⟩

/-- Separating conjunction can be reordered. -/
theorem sep_comm (P Q : HeapAssertion) (m : ℕ → ℕ) :
    (P.sep Q).holds m ↔ (Q.sep P).holds m :=
  ⟨fun h => ⟨h.1.symm, h.2.2, h.2.1⟩, fun h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩

/-- A disjoint write preserves every assertion supported on the framed region. -/
theorem frame {P : HeapAssertion} {F : Finset ℕ} {m m' : ℕ → ℕ}
    (hP : P.holds m) (hF : Disjoint P.footprint F) (hm : Modifies F m m') : P.holds m' := by
  apply P.supported _ hP
  intro a ha
  exact (hm a (fun hf => Finset.disjoint_left.mp hF ha hf)).symm

/-- Updating an unowned cell preserves an assertion. -/
theorem frame_update {P : HeapAssertion} {m : ℕ → ℕ} (hP : P.holds m)
    {a : ℕ} (ha : a ∉ P.footprint) (v : ℕ) : P.holds (Function.update m a v) := by
  apply P.supported _ hP
  intro b hb
  have hba : b ≠ a := fun h => ha (h ▸ hb)
  exact (Function.update_of_ne hba v m).symm

/-- A point assertion is updated by the corresponding store. -/
theorem pointsto_update (m : ℕ → ℕ) (a v : ℕ) :
    (pointsto a v).holds (Function.update m a v) := by
  simp [pointsto]

end HeapAssertion

end Cslib.WordRAM
