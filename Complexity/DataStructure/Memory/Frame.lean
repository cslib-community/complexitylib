/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Spec
public import Complexity.DataStructure.StateTransition.Refinement

/-!
# Footprints, and products of data structures sharing one memory

A `Memory.Framed D w` is a refinement of `D` over `Memory.spec w` together with a footprint: the
finite set of allocated cells that holds the representation of each memory state. Three
obligations make the footprint honest.

* `congr`: the invariant, the abstraction and the footprint itself read only the footprint's
  cells, and survive a growing frontier.
* `modifies`: a method run changes no allocated cell outside the footprint, and the footprint
  grows only into cells that the run allocated.
* `lt_frontier`: the footprint is allocated.

Footprints may change from state to state, so that a structure can grow into cells it allocates
inside its operations. A structure laid out in fixed blocks has a constant footprint, and
`Framed.ofStatic` asks for less. Allocating inside an operation also needs room, since
`Memory.valid` asks the new frontier to fit a word. Neither the abstract state nor the structure's
own cells determine the frontier, and the other side of a product moves it, so such a structure
needs a shared budget of room, which this file does not provide. The structures built so far
allocate their storage once, up front.

Two framed refinements implement the product of their specifications over one shared memory,
as long as their footprints are disjoint (`Framed.prod`). Disjointness is part of the product's
invariant. It holds after each method run because a run of one side writes only its own cells
and fresh ones, and the other side's footprint is allocated, hence not fresh. The product is
framed again, with the union of the footprints, so products iterate:
`(M₁.prod M₂).prod M₃` implements three structures in one memory. A potential that reads only the
footprint (`Framed.Local`) is left unchanged by the other side's methods, so amortized
certificates add across the product (`Framed.amortized_prod`), and so do worst-case
`Module.ChargeBound`s, as the case of zero potentials.

Allocation is a memory program like any other. A run that leaves every allocated cell unchanged,
such as the allocation of a further structure, preserves a framed refinement (`Framed.of_fresh`),
and `Framed.prod_of_fresh` sets up a product from structures allocated one after the other.

## Main definitions

* `Memory.Framed`: a refinement over memory with a footprint.
* `Memory.Framed.ofStatic`: the constructor for a constant footprint.
* `Memory.Framed.Local`: a function of memory that reads only the footprint.
* `Memory.Framed.prod`: two framed refinements with disjoint footprints implement the product.

## Main results

* `Memory.frontier_le_of_clientRun`: a run never lowers the frontier.
* `Memory.mem_run_of_lt_frontier`, `Memory.mem_clientState_of_lt_frontier`: a run changes an
  allocated cell only by writing it.
* `Memory.Framed.frame`: a method run of one structure leaves a structure with a disjoint
  footprint unchanged.
* `Memory.Framed.prod_methods`: the product's methods are the two sides' methods.
* `Memory.Framed.amortized_prod`: potentials and charges add across the product.
* `Memory.Framed.of_fresh`, `Memory.Framed.prod_of_fresh`: allocation preserves structures and
  sets up products.

## References

The footprint and frame discipline is the locality principle of separation logic, here with
explicit finite footprints as in `Cslib.WordRAM.HeapAssertion`; see
[J. C. Reynolds, *Separation Logic: A Logic for Shared Mutable Data Structures*][Reynolds2002].
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

variable {w : ℕ}

/-! ## Runs and allocated cells -/

/-- No run of a memory program lowers the frontier. -/
theorem frontier_le_of_clientRun {α : Type} {s s' : State} {p : Prog α} {a : α}
    {tr : (spec w).Transcript} (h : (spec w).ClientRun s p a s' tr) :
    s.frontier ≤ s'.frontier := by
  obtain ⟨_, _, rfl, _⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp h
  rw [← (spec w).run_runClient]
  exact frontier_le_run s _

/-- A sequence of operations changes an allocated cell only by writing it. -/
theorem mem_run_of_lt_frontier (s : State) (os : List Op) {a : ℕ} (ha : a < s.frontier)
    (hw : ∀ v, Op.write a v ∉ os) : ((spec w).run s os).1.mem a = s.mem a := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    have hw' : ∀ v, Op.write a v ∉ os := fun v hv => hw v (List.mem_cons_of_mem o hv)
    change ((spec w).run (step s o).1 os).1.mem a = s.mem a
    rw [ih _ (ha.trans_le (frontier_le_step s o)) hw']
    exact mem_step_of_lt_frontier s o ha fun v h => hw v (h ▸ List.mem_cons_self)

/-- A memory program changes an allocated cell only by writing it. -/
theorem mem_clientState_of_lt_frontier {α : Type} (s : State) (p : Prog α) {a : ℕ}
    (ha : a < s.frontier) (hw : ∀ v, Op.write a v ∉ (spec w).clientHistory s p) :
    ((spec w).clientState s p).mem a = s.mem a := by
  rw [← (spec w).run_runClient]
  exact mem_run_of_lt_frontier s _ ha hw

/-! ## Framed refinements -/

/-- A refinement of `D` over memory whose representation lives in a footprint of allocated
cells. The invariant, the abstraction and the footprint read only the footprint's cells; a
method run changes no allocated cell outside the footprint; and the footprint grows only into
cells at or above the old frontier, which the run allocated. -/
structure Framed (D : StateTransitionSpec.{0, 0, 0}) (w : ℕ) extends Refinement D (spec w) where
  /-- The cells holding the representation. -/
  footprint : State → Finset ℕ
  /-- The footprint is allocated. -/
  lt_frontier : ∀ {s a}, inv s → a ∈ footprint s → a < s.frontier
  /-- The invariant, the abstraction and the footprint read only the footprint's cells, and
  survive a growing frontier. -/
  congr : ∀ {s s'}, inv s → (∀ a ∈ footprint s, s'.mem a = s.mem a) →
    s.frontier ≤ s'.frontier → inv s' ∧ abs s' = abs s ∧ footprint s' = footprint s
  /-- A method run changes no allocated cell outside the footprint, and the footprint grows
  only into fresh cells. -/
  modifies : ∀ {s} o {a s' tr}, inv s → D.valid (abs s) o →
    (spec w).ClientRun s (methods o) a s' tr →
      (∀ b < s.frontier, b ∉ footprint s → s'.mem b = s.mem b) ∧
        ∀ b ∈ footprint s', b ∈ footprint s ∨ s.frontier ≤ b

namespace Framed

variable {D D₁ D₂ : StateTransitionSpec.{0, 0, 0}}

/-- The constructor for a constant footprint `fp`: the invariant and abstraction read only `fp`,
and each method's final state agrees with its initial state on the allocated cells outside
`fp`. -/
def ofStatic (M : Refinement D (spec w)) (fp : Finset ℕ)
    (lt_frontier : ∀ {s a}, M.inv s → a ∈ fp → a < s.frontier)
    (congr : ∀ {s s'}, M.inv s → (∀ a ∈ fp, s'.mem a = s.mem a) →
      s.frontier ≤ s'.frontier → M.inv s' ∧ M.abs s' = M.abs s)
    (modifies : ∀ {s} o, M.inv s → D.valid (M.abs s) o → ∀ b < s.frontier, b ∉ fp →
      ((spec w).clientState s (M.methods o)).mem b = s.mem b) :
    Framed D w where
  toRefinement := M
  footprint _ := fp
  lt_frontier := lt_frontier
  congr hs h hf := ⟨(congr hs h hf).1, (congr hs h hf).2, rfl⟩
  modifies {s} o {a s' tr} hs hv hrun := by
    obtain ⟨_, _, rfl, _⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
    exact ⟨modifies o hs hv, fun b hb => .inl hb⟩

variable (M : Framed D w)

/-- A function of memory reads only the footprint: it is unchanged when the footprint's cells
are and the frontier grows. The abstraction is one (`Local.abs`); so are potentials that a
product must keep apart. -/
def Local {β : Type*} (f : State → β) : Prop :=
  ∀ {s s'}, M.inv s → (∀ a ∈ M.footprint s, s'.mem a = s.mem a) →
    s.frontier ≤ s'.frontier → f s' = f s

/-- The abstraction reads only the footprint. -/
theorem Local.abs : M.Local M.abs := fun hs h hf => (M.congr hs h hf).2.1

/-- A constant reads no cell. -/
theorem Local.const {β : Type*} (b : β) : M.Local fun _ => b := fun _ _ _ => rfl

/-- Sums of local functions are local. -/
theorem Local.add {f g : State → ℕ} (hf : M.Local f) (hg : M.Local g) :
    M.Local fun s => f s + g s := fun hs h hfr =>
  congrArg₂ (· + ·) (hf hs h hfr) (hg hs h hfr)

/-- A run that leaves every allocated cell unchanged preserves a framed refinement. Allocating
another structure is such a run. -/
theorem of_fresh {s s' : State} (hs : M.inv s)
    (hmem : ∀ a < s.frontier, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier) :
    M.inv s' ∧ M.abs s' = M.abs s ∧ M.footprint s' = M.footprint s :=
  M.congr hs (fun a ha => hmem a (M.lt_frontier hs ha)) hf

variable {M} (N : Framed D₂ w)

/-- A method run of `M` keeps every cell of a disjoint, allocated footprint. -/
theorem agree_of_run {s : State} (o : D.Op) {a : D.Result o} {s' : State}
    {tr : (spec w).Transcript} (hM : M.inv s) (hN : N.inv s)
    (hd : Disjoint (M.footprint s) (N.footprint s)) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) :
    ∀ b ∈ N.footprint s, s'.mem b = s.mem b := fun b hb =>
  (M.modifies o hM hv hrun).1 b (N.lt_frontier hN hb) (Finset.disjoint_right.mp hd hb)

/-- **The frame of a framed refinement.** A method run of `M` leaves a framed refinement with a
disjoint footprint unchanged, and the footprints stay disjoint. -/
theorem frame {s : State} (o : D.Op) {a : D.Result o} {s' : State}
    {tr : (spec w).Transcript} (hM : M.inv s) (hN : N.inv s)
    (hd : Disjoint (M.footprint s) (N.footprint s)) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) :
    N.abs s' = N.abs s ∧ N.inv s' ∧ N.footprint s' = N.footprint s ∧
      Disjoint (M.footprint s') (N.footprint s') := by
  have hf := frontier_le_of_clientRun hrun
  obtain ⟨hN', habs, hfp⟩ := N.congr hN (agree_of_run N o hM hN hd hv hrun) hf
  refine ⟨habs, hN', hfp, Finset.disjoint_left.mpr fun b hb hb' => ?_⟩
  rw [hfp] at hb'
  rcases (M.modifies o hM hv hrun).2 b hb with hb | hb
  · exact Finset.disjoint_left.mp hd hb hb'
  · exact absurd (N.lt_frontier hN hb') (Nat.not_lt.mpr hb)

/-- A method run of `M` leaves unchanged every function that reads only a disjoint footprint. -/
theorem Local.frame {β : Type*} {f : State → β} (hf : N.Local f) {s : State} (o : D.Op)
    {a : D.Result o} {s' : State} {tr : (spec w).Transcript} (hM : M.inv s) (hN : N.inv s)
    (hd : Disjoint (M.footprint s) (N.footprint s)) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) : f s' = f s :=
  hf hN (agree_of_run N o hM hN hd hv hrun) (frontier_le_of_clientRun hrun)

/-! ## Products -/

variable (M₁ : Framed D₁ w) (M₂ : Framed D₂ w)

/-- A method run of the left side keeps the right side and the disjointness of the footprints. -/
theorem prod_frame_left {s : State} (o : D₁.Op) {a : D₁.Result o} {s' : State}
    {tr : (spec w).Transcript} (h₁ : M₁.inv s) (h₂ : M₂.inv s)
    (hd : Disjoint (M₁.footprint s) (M₂.footprint s)) (hv : D₁.valid (M₁.abs s) o)
    (hrun : (spec w).ClientRun s (M₁.methods o) a s' tr) :
    M₂.abs s' = M₂.abs s ∧ M₂.inv s' ∧ Disjoint (M₁.footprint s') (M₂.footprint s') :=
  have h := frame M₂ o h₁ h₂ hd hv hrun
  ⟨h.1, h.2.1, h.2.2.2⟩

/-- A method run of the right side keeps the left side and the disjointness of the footprints. -/
theorem prod_frame_right {s : State} (o : D₂.Op) {a : D₂.Result o} {s' : State}
    {tr : (spec w).Transcript} (h₁ : M₁.inv s) (h₂ : M₂.inv s)
    (hd : Disjoint (M₁.footprint s) (M₂.footprint s)) (hv : D₂.valid (M₂.abs s) o)
    (hrun : (spec w).ClientRun s (M₂.methods o) a s' tr) :
    M₁.abs s' = M₁.abs s ∧ M₁.inv s' ∧ Disjoint (M₁.footprint s') (M₂.footprint s') :=
  have h := frame M₁ o h₂ h₁ hd.symm hv hrun
  ⟨h.1, h.2.1, h.2.2.2.symm⟩

/-- **Products over one memory.** Two framed refinements implement the product of their
specifications over one memory, with the union of their footprints, while the footprints are
disjoint. Disjointness is part of the product's invariant. -/
def prod : Framed (product D₁ D₂) w where
  toRefinement := M₁.toRefinement.prod M₂.toRefinement
    (fun s => Disjoint (M₁.footprint s) (M₂.footprint s))
    (prod_frame_left M₁ M₂) (prod_frame_right M₁ M₂)
  footprint s := M₁.footprint s ∪ M₂.footprint s
  lt_frontier {_ _} hs ha := by
    rcases Finset.mem_union.mp ha with ha | ha
    · exact M₁.lt_frontier hs.1 ha
    · exact M₂.lt_frontier hs.2.1 ha
  congr {_ _} hs h hf := by
    obtain ⟨h₁, h₂, hd⟩ := hs
    obtain ⟨h₁', habs₁, hfp₁⟩ := M₁.congr h₁ (fun a ha => h a (Finset.mem_union_left _ ha)) hf
    obtain ⟨h₂', habs₂, hfp₂⟩ := M₂.congr h₂ (fun a ha => h a (Finset.mem_union_right _ ha)) hf
    refine ⟨⟨h₁', h₂', ?_⟩, ?_, ?_⟩
    · change Disjoint (M₁.footprint _) (M₂.footprint _)
      rwa [hfp₁, hfp₂]
    · change (M₁.abs _, M₂.abs _) = (M₁.abs _, M₂.abs _)
      rw [habs₁, habs₂]
    · rw [hfp₁, hfp₂]
  modifies {s} o {a s' tr} hs hv hrun := by
    obtain ⟨h₁, h₂, hd⟩ := hs
    cases o with
    | inl o =>
      obtain ⟨hmod, hgrow⟩ := M₁.modifies o h₁ hv hrun
      obtain ⟨-, -, hfp₂, -⟩ := frame M₂ o h₁ h₂ hd hv hrun
      refine ⟨fun b hb hb' => hmod b hb fun h => hb' (Finset.mem_union_left _ h),
        fun b hb => ?_⟩
      change b ∈ M₁.footprint s' ∪ M₂.footprint s' at hb
      rw [hfp₂] at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact (hgrow b hb).imp_left (Finset.mem_union_left _)
      · exact .inl (Finset.mem_union_right _ hb)
    | inr o =>
      obtain ⟨hmod, hgrow⟩ := M₂.modifies o h₂ hv hrun
      obtain ⟨-, -, hfp₁, -⟩ := frame M₁ o h₂ h₁ hd.symm hv hrun
      refine ⟨fun b hb hb' => hmod b hb fun h => hb' (Finset.mem_union_right _ h),
        fun b hb => ?_⟩
      change b ∈ M₁.footprint s' ∪ M₂.footprint s' at hb
      rw [hfp₁] at hb
      rcases Finset.mem_union.mp hb with hb | hb
      · exact .inl (Finset.mem_union_left _ hb)
      · exact (hgrow b hb).imp_left (Finset.mem_union_right _)

/-- The product's methods run each side's methods. They do not depend on the proofs. -/
theorem prod_methods : (M₁.prod M₂).methods = Methods.prod M₁.methods M₂.methods := rfl

/-- The product represents each side by its own abstraction. -/
@[simp] theorem prod_abs (s : State) : (M₁.prod M₂).abs s = (M₁.abs s, M₂.abs s) := rfl

/-- The product's invariant: both sides' invariants, and disjoint footprints. -/
theorem prod_inv_iff (s : State) :
    (M₁.prod M₂).inv s ↔
      M₁.inv s ∧ M₂.inv s ∧ Disjoint (M₁.footprint s) (M₂.footprint s) := Iff.rfl

/-- The product's footprint is the union of the footprints. -/
@[simp] theorem prod_footprint (s : State) :
    (M₁.prod M₂).footprint s = M₁.footprint s ∪ M₂.footprint s := rfl

variable {M₁ M₂}

/-- A function local to the left side is local to the product. -/
theorem Local.prod_left {β : Type*} {f : State → β} (hf : M₁.Local f) :
    (M₁.prod M₂).Local f := fun hs h hfr =>
  hf hs.1 (fun a ha => h a (Finset.mem_union_left _ ha)) hfr

/-- A function local to the right side is local to the product. -/
theorem Local.prod_right {β : Type*} {f : State → β} (hf : M₂.Local f) :
    (M₁.prod M₂).Local f := fun hs h hfr =>
  hf hs.2.1 (fun a ha => h a (Finset.mem_union_right _ ha)) hfr

/-- **Potentials add across a product over one memory.** Certificates of the two sides against
one lower charge, with potentials that read only their own footprints, give a certificate of
the product with componentwise upper charges and the sum of the potentials. -/
theorem amortized_prod {lower : State → Op → ℕ} {upper₁ : D₁.State → D₁.Op → ℕ}
    {upper₂ : D₂.State → D₂.Op → ℕ} {Φ₁ Φ₂ : State → ℕ}
    (A₁ : M₁.Amortized lower upper₁ Φ₁) (A₂ : M₂.Amortized lower upper₂ Φ₂)
    (hΦ₁ : M₁.Local Φ₁) (hΦ₂ : M₂.Local Φ₂) :
    (M₁.prod M₂).Amortized lower (productCharge upper₁ upper₂) fun s => Φ₁ s + Φ₂ s :=
  Refinement.Amortized.prod (frame₁ := prod_frame_left M₁ M₂) (frame₂ := prod_frame_right M₁ M₂)
    A₁ A₂ (fun {_} o {_ _ _} h₁ h₂ hd hv hrun => hΦ₂.frame M₂ o h₁ h₂ hd hv hrun)
    (fun {_} o {_ _ _} h₁ h₂ hd hv hrun => hΦ₁.frame M₁ o h₂ h₁ hd.symm hv hrun)

/-- Setting up a product from structures allocated one after the other: `M₁` holds at `s`; a
run from `s` to `s'` leaves the cells below `s.frontier` unchanged; and `M₂` holds at `s'` on a
footprint at or above `s.frontier`. Then the product holds at `s'`, with `M₁`'s abstraction
unchanged. -/
theorem prod_of_fresh {s s' : State} (h₁ : M₁.inv s)
    (hmem : ∀ a < s.frontier, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier)
    (h₂ : M₂.inv s') (hfp : ∀ a ∈ M₂.footprint s', s.frontier ≤ a) :
    (M₁.prod M₂).inv s' ∧ (M₁.prod M₂).abs s' = (M₁.abs s, M₂.abs s') := by
  obtain ⟨h₁', habs, hfp₁⟩ := M₁.of_fresh h₁ hmem hf
  refine ⟨⟨h₁', h₂, Finset.disjoint_left.mpr fun a ha ha' => ?_⟩, by rw [prod_abs, habs]⟩
  rw [hfp₁] at ha
  exact absurd (M₁.lt_frontier h₁ ha) (Nat.not_lt.mpr (hfp a ha'))

end Framed

end Cslib.DataStructure.Memory
