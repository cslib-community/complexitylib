/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Backend
public import CslibFrontier.DataStructure.Memory.Region

/-!
# Framed backends: frames, products over one memory, and allocation

A backend that implements a framed refinement (`Memory.Framed`) inherits its frame. A native
operation leaves its method's final memory (`Backend.exec_memoryState`), so it writes only the
refinement's region, its footprint and the room reserved above the frontier
(`Backend.modifies`). An assertion on other cells survives it (`Backend.frame_heap`), and so
does every framed structure kept apart from it (`Backend.frame`). Backends of two framed
refinements run their product over one memory (`Implements.prod_framed`). The product is framed
again by the union of the footprints and the sum of the rooms, so products iterate, and
`Memory.Framed.amortized_prod` adds their costs for `Backend.amortized`.

**Allocation.** An allocator (`Memory.Allocator`) sets a structure up in memory with a program
that returns a handle, such as a layout of named fields. A `Backend.Allocation` names the tag
whose body runs that program, and reads the handle off the body's result. After uncharged
argument installation, the body runs from bounded data with the allocator's precondition and
room within the certified bound. It returns the handle, writes only the room it takes above the
frontier, and leaves data that the handle's backend represents at the allocator's initial state
(`Allocation.exec`). The bound is the allocator's memory cost and the body's local work. When
allocation reserves memory without clearing it (`Memory.allocDirty`), as the array stack does,
both are constant.

**Base-relative layouts.** A family `F : A.Handle → Backend D C` uses one fixed finite
certificate family `C`, whose bodies, register layout and exchange factor precede the runtime
handle. The handle supplies arguments to those bodies. The selected tag `(F h).tag o` may depend
on `h`. If the tag is handle-independent for each operation, that operation uses the same body
across layouts. The general guarantee is a fixed finite code family; uniform local-work bounds
must also hold across handles.

The frame is that of the memory-level refinement (`Memory.Framed.region`). The frame argument
follows the block frame of #2273 (Codex), and allocation without clearing follows the queue
allocation of #2271 (Codex).

## Main definitions

* `Backend.Allocation`: the tag, argument and handle of a realized allocation.

## Main results

* `Backend.clientRun_exec`: a native operation runs its method between the memories it holds.
* `Backend.modifies`: a native operation writes only its structure's region.
* `Backend.frame_heap`, `Backend.frame`: disjoint assertions, and structures kept apart, survive.
* `Backend.Implements.prod_framed`: backends of framed refinements run their product over one
  memory.
* `Backend.modifies_inl`, `Backend.modifies_inr`: each operation of a product writes only its own
  structure's region.
* `Backend.Allocation.exec`: allocation from arbitrary memory, within the allocator's cost.
-/

public section

namespace Cslib.WordRAM.Realization.Backend

open Cslib.DataStructure

variable {B : Basis} {ι : Type} {C : ι → Certificate B} {D : StateTransitionSpec.{0, 0, 0}}
  {w : ℕ} {S : Backend D C} {M : Memory.Framed D w}

/-! ## The frame of a native operation -/

section Frame

variable [Fintype ι]

/-- A native operation runs its method from the memory it holds to the memory it leaves. -/
theorem clientRun_exec (hS : S.Implements M.toRefinement) {s : D.State}
    {x y : Data (registers C)} {o : D.Op} {a : D.Result o} {n : ℕ}
    (hr : (implementation hS).rep s x) (hv : D.valid s o) (he : S.exec w x o a y n) :
    ∃ b tr, (Memory.spec w).ClientRun (memoryState (frontier C) x) (M.methods o) b
      (memoryState (frontier C) y) tr := by
  have hm := exec_memoryState hS hr hv he
  obtain ⟨hi, rfl, -⟩ := (rep_iff hS s x).mp hr
  rw [hm]
  exact ⟨_, _, (Memory.spec w).clientRun_canonical _ _
    (((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp (M.valid o hi hv))⟩

/-- **The frame of a native operation.** An operation of a backend that implements a framed
refinement writes only the refinement's region: its footprint, and the room reserved above the
frontier. Without room (`Memory.Framed.region_eq_footprint`) it writes only the footprint. -/
theorem modifies (hS : S.Implements M.toRefinement) {s : D.State} {x y : Data (registers C)}
    {o : D.Op} {a : D.Result o} {n : ℕ} (hr : (implementation hS).rep s x) (hv : D.valid s o)
    (he : S.exec w x o a y n) : Modifies (M.region (memoryState (frontier C) x)) x.mem y.mem := by
  obtain ⟨b, tr, hrun⟩ := clientRun_exec hS hr hv he
  obtain ⟨hi, rfl, -⟩ := (rep_iff hS s x).mp hr
  exact fun c hc => M.mem_eq_of_not_mem_region o hi hv hrun hc

/-- A native operation keeps every assertion on cells outside its structure's region. -/
theorem frame_heap (hS : S.Implements M.toRefinement) {s : D.State} {x y : Data (registers C)}
    {o : D.Op} {a : D.Result o} {n : ℕ} (hr : (implementation hS).rep s x) (hv : D.valid s o)
    (he : S.exec w x o a y n) {Q : HeapAssertion} (hQ : Q.holds x.mem)
    (hd : Disjoint Q.footprint (M.region (memoryState (frontier C) x))) : Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies hS hr hv he)

/-- **A native operation keeps a structure apart from its own**: the other structure's
abstraction and invariant are unchanged, and the two stay apart, with disjoint footprints and
room for both. -/
theorem frame (hS : S.Implements M.toRefinement) {D' : StateTransitionSpec.{0, 0, 0}}
    (N : Memory.Framed D' w) {s : D.State} {x y : Data (registers C)} {o : D.Op}
    {a : D.Result o} {n : ℕ} (hr : (implementation hS).rep s x) (hv : D.valid s o)
    (he : S.exec w x o a y n) (hN : N.inv (memoryState (frontier C) x))
    (hJ : M.Apart N (memoryState (frontier C) x)) :
    N.abs (memoryState (frontier C) y) = N.abs (memoryState (frontier C) x) ∧
      N.inv (memoryState (frontier C) y) ∧ M.Apart N (memoryState (frontier C) y) := by
  obtain ⟨b, tr, hrun⟩ := clientRun_exec hS hr hv he
  obtain ⟨hi, rfl, -⟩ := (rep_iff hS s x).mp hr
  exact Memory.Framed.prod_frame_left M N o hi hN hJ hv hrun

end Frame

/-! ## Products over one memory -/

section Product

variable {ι' : Type} {C' : ι' → Certificate B} {D' : StateTransitionSpec.{0, 0, 0}}
  {S' : Backend D' C'} {M' : Memory.Framed D' w}

/-- **Products over one memory.** Backends of two framed refinements run their product
(`Memory.Framed.prod`), whose frame is the union of the footprints and the sum of the rooms. -/
theorem Implements.prod_framed (hS : S.Implements M.toRefinement)
    (hS' : S'.Implements M'.toRefinement) : (S.sum S').Implements (M.prod M').toRefinement :=
  hS.prod (frame₁ := Memory.Framed.prod_frame_left M M')
    (frame₂ := Memory.Framed.prod_frame_right M M') hS'

variable [Fintype ι] [Fintype ι']

/-- **Each side keeps its own frame.** An operation of the left structure of a product writes
only that structure's region. -/
theorem modifies_inl (hS : S.Implements M.toRefinement) (hS' : S'.Implements M'.toRefinement)
    {s : (product D D').State} {x y : Data (registers (Sum.elim C C'))} {o : D.Op}
    {a : (product D D').Result (.inl o)} {n : ℕ}
    (hr : (implementation (hS.prod_framed hS')).rep s x) (hv : (product D D').valid s (.inl o))
    (he : (S.sum S').exec w x (.inl o) a y n) :
    Modifies (M.region (memoryState (frontier (Sum.elim C C')) x)) x.mem y.mem := by
  obtain ⟨b, tr, hrun⟩ := clientRun_exec (hS.prod_framed hS') hr hv he
  obtain ⟨⟨hi, -, -⟩, rfl, -⟩ := (rep_iff _ s x).mp hr
  exact fun c hc => M.mem_eq_of_not_mem_region o hi hv hrun hc

/-- An operation of the right structure of a product writes only that structure's region. -/
theorem modifies_inr (hS : S.Implements M.toRefinement) (hS' : S'.Implements M'.toRefinement)
    {s : (product D D').State} {x y : Data (registers (Sum.elim C C'))} {o : D'.Op}
    {a : (product D D').Result (.inr o)} {n : ℕ}
    (hr : (implementation (hS.prod_framed hS')).rep s x) (hv : (product D D').valid s (.inr o))
    (he : (S.sum S').exec w x (.inr o) a y n) :
    Modifies (M'.region (memoryState (frontier (Sum.elim C C')) x)) x.mem y.mem := by
  obtain ⟨b, tr, hrun⟩ := clientRun_exec (hS.prod_framed hS') hr hv he
  obtain ⟨⟨-, hi, -⟩, rfl, -⟩ := (rep_iff _ s x).mp hr
  exact fun c hc => M'.mem_eq_of_not_mem_region o hi hv hrun hc

end Product

/-! ## Allocation -/

/-- **A realized allocation** for the allocator `A`: the body of tag `tag`, on arguments `arg`,
runs the allocation program, and `handle` reads the allocated handle off its result. From memory
the allocator can allocate from, the arguments fit words and the tag's domain holds. -/
structure Allocation (A : Memory.Allocator D w) (C : ι → Certificate B) where
  /-- The tag whose body allocates. -/
  tag : ι
  /-- Its arguments, such as a capacity. -/
  arg : (C tag).Arg
  /-- The handle, read off the body's result. -/
  handle : (C tag).Res → A.Handle
  /-- The tag's program is the allocation, with the handle read off its result. -/
  run : ∀ s, (Memory.spec w).runClient s A.alloc =
    Prod.map handle id ((Memory.spec w).runClient s ((C tag).prog arg))
  /-- From memory the allocator can allocate from, the arguments fit words and the tag's domain
  holds. -/
  entry : ∀ {s}, Memory.WellFormed w s → A.Pre s → Fits w (s.frontier + A.room) →
    (∀ j, Fits w ((C tag).input arg j)) ∧ (C tag).safe w arg s

variable [Fintype ι]

/-- **Allocation from arbitrary memory.** From bounded data whose memory the allocator can
allocate from, with its room fitting a word, the allocation body runs within
`factor C * (A.cost + work + 1)` instructions, where `work` is its local work. It returns the
allocated handle in its result registers, writes only the room it takes above the frontier, and
leaves data that the handle's backend represents at the allocator's initial state.

Execution starts after the uncharged `install` has supplied the argument registers. A raw-data
initializer must separately pay native argument installation and any allocation-cursor setup. -/
theorem Allocation.exec {A : Memory.Allocator D w} (I : Allocation A C)
    {F : A.Handle → Backend D C}
    (hF : ∀ s (hs : A.Pre s) (hroom : Fits w (s.frontier + A.room)),
      (F ((Memory.spec w).clientResult s A.alloc)).Implements (A.framed s hs hroom).toRefinement)
    {x : Data (registers C)} (hx : x.Bounded w) (hs : A.Pre (memoryState (frontier C) x))
    (hroom : Fits w ((memoryState (frontier C) x).frontier + A.room)) :
    ∃ y n b, Exec w (code C I.tag) (install C I.tag I.arg x) y n ∧
      n ≤ factor C * (A.cost + (C I.tag).work I.arg (memoryState (frontier C) x) + 1) ∧
      (∀ j, y.regs (tmp C I.tag (Fin.castAdd ((C I.tag).realizes.scratchSize + 1) j)) =
        (C I.tag).output b j) ∧
      I.handle b = (Memory.spec w).clientResult (memoryState (frontier C) x) A.alloc ∧
      Modifies (Finset.Ico (memoryState (frontier C) x).frontier
        ((memoryState (frontier C) x).frontier + A.room)) x.mem y.mem ∧
      (implementation (hF _ hs hroom)).rep A.init y := by
  have hal := A.allocates _ hs hroom
  have hrun := I.run (memoryState (frontier C) x)
  have hhist : (Memory.spec w).clientHistory (memoryState (frontier C) x) A.alloc =
      (Memory.spec w).clientHistory (memoryState (frontier C) x) ((C I.tag).prog I.arg) :=
    congrArg (fun t => t.2.2) hrun
  have hstate : (Memory.spec w).clientState (memoryState (frontier C) x) A.alloc =
      (Memory.spec w).clientState (memoryState (frontier C) x) ((C I.tag).prog I.arg) :=
    congrArg (fun t => t.2.1) hrun
  obtain ⟨hin, hsafe⟩ := I.entry (wellFormed_memoryState hx) hs hroom
  obtain ⟨y, n, hex, hn, hm, hout, hb⟩ :=
    exists_exec C I.tag I.arg hx hin hsafe (hhist ▸ hal.validHistory)
  have hy : memoryState (frontier C) y =
      (Memory.spec w).clientState (memoryState (frontier C) x) A.alloc := hm.trans hstate.symm
  refine ⟨y, n, _, hex, hn.trans (Nat.mul_le_mul_left _ ?_), hout,
    (congrArg Prod.fst hrun).symm, fun c hc => ?_, (rep_iff _ _ _).mpr ⟨?_, ?_, hb⟩⟩
  · have := hal.cost_le
    rw [memoryCost_eq_totalCost w, ← hhist]
    omega
  · have := hal.mem_eq_of_not_mem hc
    rw [← hy] at this
    exact this
  · rw [hy]
    exact hal.inv
  · rw [hy]
    exact hal.abs_eq

end Cslib.WordRAM.Realization.Backend
