/-
Copyright (c) 2026 András Z. Salamon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: András Z. Salamon
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Order.Setoid.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Set partitions and their blocks

Partitions of a type `α` are equivalence relations `Setoid α`, ordered by refinement: `r ≤ s` when
every block of `r` lies in a block of `s`. The discrete partition is `⊥` and the partition with one
block is `⊤`. Mathlib's complete lattice on `Setoid α` provides the join and meet.

The number of blocks of `s` is `blocks s`, defined as `Nat.card (Quotient s)`. Coarsening a
partition can only decrease its number of blocks, and a partition is determined by any coarser
partition with as many blocks; so on a finite type the number of blocks is strictly antitone in the
refinement order.

Mathlib declares no finiteness instance on `Setoid α`. This file adds `Finite (Setoid α)` for
finite `α` and no `Fintype` instance: statements that sum over the partitions assume
`[Fintype (Setoid α)]`, which `Fintype.ofFinite` provides, and counts are stated with `Nat.card`.

## Main definitions

* `Cslib.SetPartition.instFiniteSetoid`: a finite type has finitely many partitions.
* `Cslib.SetPartition.blocks`: the number of blocks of a partition.

## Main results

* `Cslib.SetPartition.blocks_eq_one_iff`: on a nonempty type, `⊤` is the only partition with one
  block.
* `Cslib.SetPartition.blocks_le_of_le`: a coarser partition has at most as many blocks.
* `Cslib.SetPartition.eq_of_le_of_blocks_eq`: a partition equals any coarser partition with as
  many blocks.
* `Cslib.SetPartition.blocks_lt_of_lt`: on a finite type, a strictly coarser partition has strictly
  fewer blocks.
* `Cslib.SetPartition.blocks_le_card`: a partition has at most as many blocks as elements.
* `Cslib.SetPartition.blocks_ker`: the fibers of `f` are as many as the values of `f`.
* `Cslib.SetPartition.pow_le_card_setoid`: $j^{N-j} \le B_N$, where $B_N$ is the number of
  partitions of $N$ elements.
-/

public section

namespace Cslib.SetPartition

variable {α : Type*}

/-- There are finitely many partitions of a finite type. Where a `Fintype (Setoid α)` instance is
needed, any will do, for example the noncomputable `Fintype.ofFinite`. -/
instance instFiniteSetoid [Finite α] : Finite (Setoid α) :=
  Finite.of_injective (fun s : Setoid α => (⇑s : α → α → Prop)) fun _ _ h =>
    Setoid.ext fun a b => iff_of_eq (congrFun (congrFun h a) b)

/-- The number of blocks of a partition, that is, of its equivalence classes. -/
@[expose] noncomputable def blocks (s : Setoid α) : ℕ :=
  Nat.card (Quotient s)

/-! ### Blocks -/

section Blocks

/-- The discrete partition has one block for each element. -/
theorem blocks_bot : blocks (⊥ : Setoid α) = Nat.card α :=
  Nat.card_congr Setoid.quotientBotEquiv

/-- A partition of a finite nonempty type has at least one block. -/
theorem blocks_pos [Finite α] [Nonempty α] (s : Setoid α) : 0 < blocks s :=
  have : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary α)⟩
  Nat.card_pos

/-- A partition of a nonempty type has one block exactly when it is the one-block partition `⊤`. -/
theorem blocks_eq_one_iff [Nonempty α] {s : Setoid α} : blocks s = 1 ↔ s = ⊤ := by
  have : Nonempty (Quotient s) := ⟨Quotient.mk s (Classical.arbitrary α)⟩
  rw [blocks, Nat.card_eq_one_iff_unique, ← Quotient.subsingleton_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, inferInstance⟩⟩

/-- A coarser partition has at most as many blocks. -/
theorem blocks_le_of_le [Finite α] {r s : Setoid α} (h : r ≤ s) : blocks s ≤ blocks r :=
  Nat.card_le_card_of_surjective (Setoid.map_of_le h) (Quot.map_surjective h Function.surjective_id)

/-- A partition is determined by any coarser partition with as many blocks. -/
theorem eq_of_le_of_blocks_eq [Finite α] {r s : Setoid α} (h : r ≤ s)
    (hb : blocks r = blocks s) : r = s := by
  have hinj : Function.Injective (Setoid.map_of_le h) :=
    (Function.Surjective.bijective_of_nat_card_le
      (Quot.map_surjective h Function.surjective_id) hb.le).1
  refine le_antisymm h fun a b hab => ?_
  exact Quotient.exact (hinj (Quotient.sound hab : Quotient.mk s a = Quotient.mk s b))

/-- A strictly coarser partition of a finite type has strictly fewer blocks. -/
theorem blocks_lt_of_lt [Finite α] {r s : Setoid α} (h : r < s) : blocks s < blocks r :=
  (blocks_le_of_le h.le).lt_of_ne fun hb => h.ne (eq_of_le_of_blocks_eq h.le hb.symm)

/-- A partition of a finite type has at most as many blocks as there are elements. -/
theorem blocks_le_card [Finite α] (s : Setoid α) : blocks s ≤ Nat.card α :=
  blocks_bot (α := α) ▸ blocks_le_of_le bot_le

/-- The blocks of the kernel of `f`, the partition into the fibers of `f`, correspond to the
values of `f`. -/
theorem blocks_ker {β : Type*} (f : α → β) : blocks (Setoid.ker f) = Nat.card (Set.range f) :=
  Nat.card_congr (Setoid.quotientKerEquivRange f)

end Blocks

/-! ### A lower bound on the number of partitions -/

section Many

/-- The map that is the identity on the first `j` elements of `Fin N` and `f` on the rest. -/
private def extendMap {N j : ℕ} (f : Fin (N - j) → Fin j) (i : Fin N) : Fin j :=
  if h : (i : ℕ) < j then ⟨i, h⟩ else f ⟨i - j, by omega⟩

private theorem extendMap_injective_ker {N j : ℕ} :
    Function.Injective fun f : Fin (N - j) → Fin j => Setoid.ker (extendMap f) := by
  intro f₁ f₂ h
  funext t
  have hp : j + (t : ℕ) < N := by omega
  have key : ∀ f : Fin (N - j) → Fin j, ∀ i : Fin j,
      Setoid.ker (extendMap f) ⟨j + t, hp⟩ ⟨i, by omega⟩ ↔ f t = i := by
    intro f i
    rw [Setoid.ker_def]
    simp only [extendMap, show ¬(j + (t : ℕ) < j) by omega, i.2, ↓reduceDIte]
    simp only [add_tsub_cancel_left, Fin.eta]
  have h1 : Setoid.ker (extendMap f₁) ⟨j + t, hp⟩ ⟨f₁ t, by omega⟩ := (key f₁ (f₁ t)).mpr rfl
  simp only at h
  rw [h] at h1
  exact ((key f₂ (f₁ t)).mp h1).symm

/-- **Many partitions**: $j^{N-j} \le B_N$, by placing the first $j$ elements in distinct blocks
and each of the others in one of these blocks (and trivially $j^0 = 1 \le B_N$ when $N \le j$). -/
theorem pow_le_card_setoid (N j : ℕ) :
    j ^ (N - j) ≤ Nat.card (Setoid (Fin N)) := by
  have h := Nat.card_le_card_of_injective _ (extendMap_injective_ker (N := N) (j := j))
  rwa [Nat.card_fun, Nat.card_fin, Nat.card_fin] at h

end Many

end Cslib.SetPartition
