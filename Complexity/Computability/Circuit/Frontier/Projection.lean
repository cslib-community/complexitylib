/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.Network

/-!
# Hiding the inputs of a constraint network

A constraint network on the inputs `ι ⊕ κ` *hides* the inputs in `κ` (`Network.hide`) by
quantifying them existentially in each local constraint, on the same multigraph. Since each
hidden input is read at no more than one vertex, local witnesses for the hidden inputs assemble
into one global witness (`Network.satisfies_hide_iff`). So the hidden network accepts exactly the
projection of the accepted set (`Network.accepted_hide`). Witnesses need not be unique.

Hiding keeps the multigraph, and with it every degree, frontier and width; it only forgets the
hidden inputs, so it reads no more inputs than before. Inputs can also be renamed along an
equivalence (`Network.reindex`), for instance to hide the last `k` of `n + k` inputs.

## Main definitions

* `Cslib.Circuits.Frontier.Network.reindex`: renaming the inputs of a network.
* `Cslib.Circuits.Frontier.Network.hide`: hiding the inputs in `κ` of a network on `ι ⊕ κ`.

## Main results

* `Cslib.Circuits.Frontier.Network.accepted_reindex`: renaming the inputs renames the accepted
  set.
* `Cslib.Circuits.Frontier.Network.satisfies_hide_iff`: local witnesses assemble into a global
  one.
* `Cslib.Circuits.Frontier.Network.accepted_hide`: hiding inputs projects the accepted set.
* `Cslib.Circuits.Frontier.Network.ncard_readAt_hide_le`,
  `Cslib.Circuits.Frontier.Network.ncard_read_hide_le`: hiding inputs reads fewer inputs.
-/

@[expose] public section

namespace Cslib.Circuits.Frontier.Network

open Set

variable {U ι ι' κ V E : Type*}

/-! ### Renaming inputs -/

section Reindex

variable (N : Network U ι V E) (e : ι ≃ ι')

/-- Rename the inputs of a network along an equivalence `e : ι ≃ ι'`: the input `e i` is read
where `i` was, and the constraints see an input `x` on `ι'` as the input `x ∘ e` on `ι`. -/
def reindex : Network U ι' V E where
  toMultigraph := N.toMultigraph
  site i := N.site (e.symm i)
  Constraint v x α := N.Constraint v (x ∘ e) α
  constraint_congr v x x' α α' hx hα :=
    N.constraint_congr v _ _ α α' (fun i hi => hx (e i) (by simpa using hi)) hα

/-- Reindexing the inputs preserves the underlying multigraph. -/
@[simp] theorem reindex_toMultigraph : (N.reindex e).toMultigraph = N.toMultigraph :=
  rfl

/-- An assignment satisfies the reindexed network on `x` if and only if it satisfies `N` on
`x ∘ e`. -/
theorem satisfies_reindex_iff {x : ι' → U} {α : E → U} :
    (N.reindex e).Satisfies x α ↔ N.Satisfies (x ∘ e) α :=
  Iff.rfl

/-- Renaming the inputs renames the accepted set. -/
theorem accepted_reindex : (N.reindex e).accepted = {x | x ∘ e ∈ N.accepted} :=
  rfl

private theorem readAt_reindex (v : V) : (N.reindex e).readAt v = e '' N.readAt v := by
  rw [e.image_eq_preimage_symm]
  rfl

private theorem read_reindex : (N.reindex e).read = e '' N.read := by
  rw [e.image_eq_preimage_symm]
  rfl

/-- Reindexing the inputs preserves the number of inputs read at each vertex. -/
@[simp] theorem ncard_readAt_reindex (v : V) :
    ((N.reindex e).readAt v).ncard = (N.readAt v).ncard := by
  rw [readAt_reindex, ncard_image_of_injective _ e.injective]

/-- Reindexing the inputs preserves the total number of inputs read. -/
@[simp] theorem ncard_read_reindex : (N.reindex e).read.ncard = N.read.ncard := by
  rw [read_reindex, ncard_image_of_injective _ e.injective]

end Reindex

/-! ### Hiding inputs -/

section Hide

variable (N : Network U (ι ⊕ κ) V E)

/-- **Hiding inputs.** The network on the inputs `ι` obtained from a network on `ι ⊕ κ` by
quantifying the inputs in `κ` existentially in each local constraint, on the same multigraph.
The visible inputs are read where they were. -/
def hide : Network U ι V E where
  toMultigraph := N.toMultigraph
  site i := N.site (.inl i)
  Constraint v x α := ∃ y : κ → U, N.Constraint v (Sum.elim x y) α
  constraint_congr v x x' α α' hx hα := by
    rintro ⟨y, hy⟩
    refine ⟨y, N.constraint_congr v _ _ _ _ ?_ hα hy⟩
    rintro (i | j) hi
    · exact hx i hi
    · rfl

/-- Hiding inputs preserves the underlying multigraph. -/
@[simp] theorem hide_toMultigraph : N.hide.toMultigraph = N.toMultigraph :=
  rfl

/-- **Local witnesses assemble into a global one.** An assignment satisfies the hidden network
on `x` exactly when it satisfies the original network on `x` and some values of the hidden
inputs. Each hidden input is read at no more than one vertex, so it takes the value that the
witness of that vertex gives it. -/
theorem satisfies_hide_iff [Nonempty U] {x : ι → U} {α : E → U} :
    N.hide.Satisfies x α ↔ ∃ y : κ → U, N.Satisfies (Sum.elim x y) α := by
  refine ⟨fun h => ?_, fun ⟨y, hy⟩ v => ⟨y, hy v⟩⟩
  choose ys hys using h
  refine ⟨fun j => (N.site (.inr j)).elim (Classical.arbitrary U) fun v => ys v j,
    fun v => N.constraint_congr v _ _ _ _ ?_ (fun _ _ => rfl) (hys v)⟩
  rintro (i | j) hj
  · rfl
  · simp [hj]

/-- **Hiding inputs projects the accepted set.** -/
theorem accepted_hide [Nonempty U] :
    N.hide.accepted = {x | ∃ y : κ → U, Sum.elim x y ∈ N.accepted} := by
  ext x
  simp only [accepted, mem_ofPred_eq, satisfies_hide_iff]
  exact exists_comm

/-- The visible inputs read at a vertex `v` in `N.hide` are the `.inl` inputs read at `v` in `N`. -/
theorem readAt_hide (v : V) : N.hide.readAt v = Sum.inl ⁻¹' N.readAt v :=
  rfl

/-- The visible inputs read in `N.hide` are the `.inl` inputs read in `N`. -/
theorem read_hide : N.hide.read = Sum.inl ⁻¹' N.read :=
  rfl

/-- The visible inputs read at a vertex are among the inputs it read before hiding. -/
theorem ncard_readAt_hide_le (v : V) (hv : (N.readAt v).Finite := by toFinite_tac) :
    (N.hide.readAt v).ncard ≤ (N.readAt v).ncard :=
  ncard_le_ncard_of_injOn Sum.inl (fun _ hi => hi) Sum.inl_injective.injOn hv

/-- Hiding inputs can only decrease the number of inputs read. -/
theorem ncard_read_hide_le (hN : N.read.Finite := by toFinite_tac) :
    N.hide.read.ncard ≤ N.read.ncard :=
  ncard_le_ncard_of_injOn Sum.inl (fun _ hi => hi) Sum.inl_injective.injOn hN

end Hide

end Cslib.Circuits.Frontier.Network
