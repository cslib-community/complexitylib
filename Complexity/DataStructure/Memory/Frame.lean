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
# Footprints, room, and products of data structures sharing one memory

A `Memory.Framed D w` is a refinement of `D` over `Memory.spec w` together with a footprint, the
finite set of allocated cells that holds the representation of each memory state, and a room,
the number of cells the structure has reserved for its future allocations. Three obligations make
them honest.

* `congr`: the invariant, the abstraction, the footprint and the room read only the footprint's
  cells, and survive a growing frontier that leaves the reserved room fitting a word.
* `modifies`: a method run changes no allocated cell outside the footprint, the footprint grows
  only into cells that the run allocated, and the frontier advances by at most the room the run
  gives up.
* `lt_frontier`: the footprint is allocated.

A structure laid out in fixed blocks has a constant footprint and no room, and `Framed.ofStatic`
asks for less. A structure that allocates inside its operations, such as a growing array,
reserves room for all of its future growth. Its invariant may then ask that the frontier plus its
room fit a word, which is what `Memory.valid` needs of each allocation. That fact is not
preserved by other structures' allocations on its own, so the product keeps it for everybody.

**Products.** Two framed refinements implement the product of their specifications over one
shared memory (`Framed.prod`). The product's invariant asks that the footprints be disjoint and
that the frontier plus both rooms fit a word. This is the shared room budget: a method run of one
side writes only its own cells and fresh ones, and advances the frontier by at most the room it
gives up, so the other side keeps its cells and its room, and the budget still fits. The product
is framed again, with the union of the footprints and the sum of the rooms, so products iterate:
`(M₁.prod M₂).prod M₃` implements three structures in one memory. A potential that reads only
the footprint (`Framed.Local`) is left unchanged by the other side's methods, so amortized
certificates add across the product (`Framed.amortized_prod`), and so do worst-case
`Module.ChargeBound`s, as the case of zero potentials.

**Composition.** A refinement of `D` over `E` composed with a framed refinement of `E` is framed
by the same footprint and room (`Framed.comp`), since a whole linked client keeps the frame of its
calls (`Framed.modifies_demonic`). So a structure built on others, such as a queue over two
stacks, joins a product like any other.

**Allocation** is a memory program like any other. A run that leaves every allocated cell
unchanged and leaves the room fitting, such as the allocation of a further structure, preserves a
framed refinement (`Framed.of_fresh`), and `Framed.prod_of_fresh` sets up a product from
structures allocated one after the other. `Memory.Allocator` packages this.

## Main definitions

* `Memory.Framed`: a refinement over memory with a footprint and a room.
* `Memory.Framed.ofStatic`: the constructor for a constant footprint and no room.
* `Memory.Framed.Local`: a function of memory that reads only the footprint.
* `Memory.Framed.prod`: two framed refinements with disjoint footprints implement the product.
* `Memory.Framed.comp`: a refinement over a framed refinement is framed.

## Main results

* `Memory.frontier_le_of_clientRun`, `Memory.frontier_le_clientState`: a run never lowers the
  frontier.
* `Memory.mem_run_of_lt_frontier`, `Memory.mem_clientState_of_lt_frontier`: a run changes an
  allocated cell only by writing it.
* `Memory.mem_run_of_frontier_le`, `Memory.mem_clientState_of_frontier_le`: an admissible run
  changes no cell at or above its final frontier.
* `Memory.Framed.modifies_demonic`: a linked client keeps the frame of its calls.
* `Memory.Framed.frame`: a method run of one structure leaves a structure with a disjoint
  footprint unchanged, and the shared room budget fitting.
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

open Cslib.WordRAM

variable {w : ℕ}

/-! ## Runs and allocated cells -/

/-- No run of a memory program lowers the frontier. -/
theorem frontier_le_of_clientRun {α : Type} {s s' : State} {p : Prog α} {a : α}
    {tr : (spec w).Transcript} (h : (spec w).ClientRun s p a s' tr) :
    s.frontier ≤ s'.frontier := by
  obtain ⟨_, _, rfl, _⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp h
  rw [← (spec w).run_runClient]
  exact frontier_le_run s _

/-- No memory program lowers the frontier. -/
theorem frontier_le_clientState {α : Type} (s : State) (p : Prog α) :
    s.frontier ≤ ((spec w).clientState s p).frontier := by
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

/-- An admissible sequence of operations changes no cell at or above its final frontier: writes
go below the frontier, and an allocation clears only the block that it hands out. -/
theorem mem_run_of_frontier_le {s : State} {os : List Op} (hv : (spec w).ValidHistory s os)
    {a : ℕ} (ha : ((spec w).run s os).1.frontier ≤ a) : ((spec w).run s os).1.mem a = s.mem a := by
  induction os generalizing s with
  | nil => rfl
  | cons o os ih =>
    obtain ⟨hvo, hvs⟩ := hv
    change ((spec w).run (step s o).1 os).1.frontier ≤ a at ha
    change ((spec w).run (step s o).1 os).1.mem a = s.mem a
    rw [ih hvs ha]
    have hf : (step s o).1.frontier ≤ a := (frontier_le_run _ os).trans ha
    cases o with
    | read => rfl
    | write b v =>
      have hb : b < s.frontier := hvo.1
      simp only [step_write] at hf
      have hab : a ≠ b := by omega
      exact Function.update_of_ne hab v s.mem
    | alloc k =>
      simp only [step_alloc] at hf
      exact clear_of_not_owns (by simp only [Block.Owns]; omega)
    | allocDirty => rfl

/-- An admissible memory program changes no cell at or above its final frontier. -/
theorem mem_clientState_of_frontier_le {α : Type} (s : State) (p : Prog α)
    (hv : (spec w).ValidHistory s ((spec w).clientHistory s p)) {a : ℕ}
    (ha : ((spec w).clientState s p).frontier ≤ a) :
    ((spec w).clientState s p).mem a = s.mem a := by
  rw [← (spec w).run_runClient] at ha ⊢
  exact mem_run_of_frontier_le hv ha

/-! ## Framed refinements -/

/-- A refinement of `D` over memory whose representation lives in a footprint of allocated cells,
with room reserved for its growth. The invariant, the abstraction, the footprint and the room
read only the footprint's cells; a method run changes no allocated cell outside the footprint;
the footprint grows only into cells at or above the old frontier, which the run allocated; and
the frontier advances by at most the room the run gives up. -/
structure Framed (D : StateTransitionSpec.{0, 0, 0}) (w : ℕ) extends Refinement D (spec w) where
  /-- The cells holding the representation. -/
  footprint : State → Finset ℕ
  /-- The cells reserved for the structure's future allocations. -/
  room : State → ℕ
  /-- The footprint is allocated. -/
  lt_frontier : ∀ {s a}, inv s → a ∈ footprint s → a < s.frontier
  /-- The invariant, the abstraction, the footprint and the room read only the footprint's
  cells, and survive a growing frontier that leaves the room fitting a word. -/
  congr : ∀ {s s'}, inv s → (∀ a ∈ footprint s, s'.mem a = s.mem a) →
    s.frontier ≤ s'.frontier → Fits w (s'.frontier + room s) →
      inv s' ∧ abs s' = abs s ∧ footprint s' = footprint s ∧ room s' = room s
  /-- A method run changes no allocated cell outside the footprint, the footprint grows only
  into fresh cells, and the frontier advances by at most the room given up. -/
  modifies : ∀ {s} o {a s' tr}, inv s → D.valid (abs s) o →
    (spec w).ClientRun s (methods o) a s' tr →
      (∀ b < s.frontier, b ∉ footprint s → s'.mem b = s.mem b) ∧
        (∀ b ∈ footprint s', b ∈ footprint s ∨ s.frontier ≤ b) ∧
        s'.frontier + room s' ≤ s.frontier + room s

namespace Framed

variable {D D₁ D₂ E : StateTransitionSpec.{0, 0, 0}}

/-- The constructor for a constant footprint `fp` and no room: the invariant and abstraction read
only `fp`, and each method's final state agrees with its initial state on the allocated cells
outside `fp` and has the same frontier. -/
def ofStatic (M : Refinement D (spec w)) (fp : Finset ℕ)
    (lt_frontier : ∀ {s a}, M.inv s → a ∈ fp → a < s.frontier)
    (congr : ∀ {s s'}, M.inv s → (∀ a ∈ fp, s'.mem a = s.mem a) →
      s.frontier ≤ s'.frontier → M.inv s' ∧ M.abs s' = M.abs s)
    (modifies : ∀ {s} o, M.inv s → D.valid (M.abs s) o → ∀ b < s.frontier, b ∉ fp →
      ((spec w).clientState s (M.methods o)).mem b = s.mem b)
    (frontier_eq : ∀ {s} o, M.inv s → D.valid (M.abs s) o →
      ((spec w).clientState s (M.methods o)).frontier = s.frontier) :
    Framed D w where
  toRefinement := M
  footprint _ := fp
  room _ := 0
  lt_frontier := lt_frontier
  congr hs h hf _ := ⟨(congr hs h hf).1, (congr hs h hf).2, rfl, rfl⟩
  modifies {s} o {a s' tr} hs hv hrun := by
    obtain ⟨_, _, rfl, _⟩ := ((spec w).clientRun_iff_runClient _ _ _ _ _).mp hrun
    exact ⟨modifies o hs hv, fun b hb => .inl hb, (frontier_eq o hs hv).le⟩

variable (M : Framed D w)

/-- A function of memory reads only the footprint: it is unchanged when the footprint's cells
are and the frontier grows, leaving the room fitting a word. The abstraction is one
(`Local.abs`), and so is the room (`Local.room`); so are potentials that a product must keep
apart. -/
def Local {β : Type*} (f : State → β) : Prop :=
  ∀ {s s'}, M.inv s → (∀ a ∈ M.footprint s, s'.mem a = s.mem a) →
    s.frontier ≤ s'.frontier → Fits w (s'.frontier + M.room s) → f s' = f s

/-- The abstraction reads only the footprint. -/
theorem Local.abs : M.Local M.abs := fun hs h hf hr => by
  obtain ⟨-, habs, -⟩ := M.congr hs h hf hr
  exact habs

/-- The room reads only the footprint. -/
theorem Local.room : M.Local M.room := fun hs h hf hr => by
  obtain ⟨-, -, -, hroom⟩ := M.congr hs h hf hr
  exact hroom

/-- A constant reads no cell. -/
theorem Local.const {β : Type*} (b : β) : M.Local fun _ => b := fun _ _ _ _ => rfl

/-- Sums of local functions are local. -/
theorem Local.add {M : Framed D w} {f g : State → ℕ} (hf : M.Local f) (hg : M.Local g) :
    M.Local fun s => f s + g s := fun hs h hfr hr =>
  congrArg₂ (· + ·) (hf hs h hfr hr) (hg hs h hfr hr)

/-- A function of the abstract state is local. -/
theorem Local.comp_abs {β : Type*} (f : D.State → β) : M.Local fun s => f (M.abs s) :=
  fun hs h hfr hr => congrArg f (Local.abs M hs h hfr hr)

/-- A run that leaves every allocated cell unchanged and leaves the room fitting preserves a
framed refinement. Allocating another structure is such a run. -/
theorem of_fresh {s s' : State} (hs : M.inv s)
    (hmem : ∀ a < s.frontier, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier)
    (hroom : Fits w (s'.frontier + M.room s)) :
    M.inv s' ∧ M.abs s' = M.abs s ∧ M.footprint s' = M.footprint s ∧ M.room s' = M.room s :=
  M.congr hs (fun a ha => hmem a (M.lt_frontier hs ha)) hf hroom

/-- **The frame of a client.** A run of a linked admissible client changes no cell outside the
footprint that was allocated before it, grows the footprint only into fresh cells, and advances
the frontier by at most the room it gives up, as each method run does. -/
theorem modifies_demonic {α : Type} (p : D.Client α) {s s' : State} {a : α}
    {tr : (spec w).Transcript} (hs : M.inv s) (hv : D.DemonicValid (M.abs s) p)
    (hrun : (spec w).ClientRun s (link M.methods p) a s' tr) :
    (∀ b < s.frontier, b ∉ M.footprint s → s'.mem b = s.mem b) ∧
      (∀ b ∈ M.footprint s', b ∈ M.footprint s ∨ s.frontier ≤ b) ∧
      s'.frontier + M.room s' ≤ s.frontier + M.room s := by
  induction p generalizing s tr with
  | pure b =>
    obtain ⟨-, rfl, -⟩ := ((spec w).clientRun_pure_iff _ _ _ _ _).mp hrun
    exact ⟨fun _ _ _ => rfl, fun _ hb => .inl hb, le_rfl⟩
  | liftBind o k ih =>
    obtain ⟨hv_o, hv_k⟩ := (D.demonicValid_liftBind_iff _ o k).mp hv
    have heq : link M.methods (.liftBind o k) =
        (M.methods o).bind (fun r => link M.methods (k r)) := rfl
    rw [heq] at hrun
    obtain ⟨r, s₁, tr₁, tr₂, hrun₁, hrun₂, rfl⟩ := (spec w).clientRun_bind_iff.mp hrun
    obtain ⟨hstep, hs₁⟩ := M.correct o hs hv_o hrun₁
    obtain ⟨hmod₁, hgrow₁, hroom₁⟩ := M.modifies o hs hv_o hrun₁
    obtain ⟨hmod₂, hgrow₂, hroom₂⟩ := ih r hs₁ (hv_k _ r hstep) hrun₂
    have hf₁ := frontier_le_of_clientRun hrun₁
    refine ⟨fun b hb hb' => ?_, fun b hb => ?_, by omega⟩
    · have hb₁ : b ∉ M.footprint s₁ := fun h =>
        (hgrow₁ b h).elim hb' fun h' => absurd hb (Nat.not_lt.mpr h')
      rw [hmod₂ b (hb.trans_le hf₁) hb₁, hmod₁ b hb hb']
    · rcases hgrow₂ b hb with h | h
      · exact hgrow₁ b h
      · exact .inr (hf₁.trans h)

/-! ## Composition -/

/-- **A refinement over a framed refinement is framed**, by the same footprint and room: the
upper invariant and abstraction read the lower state only through its abstraction, and each
upper method is a linked client of the lower methods. -/
def comp (R : Refinement D E) (M : Framed E w) : Framed D w where
  toRefinement := R.comp M.toRefinement
  footprint := M.footprint
  room := M.room
  lt_frontier hs ha := M.lt_frontier hs.1 ha
  congr {s _} hs h hf hr := by
    obtain ⟨hM, hR⟩ := hs
    obtain ⟨hM', habs, hfp, hroom⟩ := M.congr hM h hf hr
    refine ⟨⟨hM', ?_⟩, ?_, hfp, hroom⟩
    · rwa [habs]
    · change R.abs (M.abs _) = R.abs (M.abs s)
      rw [habs]
  modifies {_} o {_ _ _} hs hv hrun :=
    M.modifies_demonic (R.methods o) hs.1 (R.valid o hs.2 hv) hrun

/-- The composite's methods link the upper methods through the lower ones. -/
theorem comp_methods (R : Refinement D E) (M : Framed E w) :
    (comp R M).methods = fun o => link M.methods (R.methods o) := rfl

/-- The composite is the composition of the refinements. -/
theorem comp_toRefinement (R : Refinement D E) (M : Framed E w) :
    (comp R M).toRefinement = R.comp M.toRefinement := rfl

/-- The composite's invariant: the lower invariant, and the upper invariant of the lower
abstraction. -/
theorem comp_inv_iff (R : Refinement D E) (M : Framed E w) (s : State) :
    (comp R M).inv s ↔ M.inv s ∧ R.inv (M.abs s) := Iff.rfl

/-- The composite represents a memory state by the upper abstraction of the lower one. -/
@[simp] theorem comp_abs (R : Refinement D E) (M : Framed E w) (s : State) :
    (comp R M).abs s = R.abs (M.abs s) := rfl

/-- The composite's footprint is the lower footprint. -/
@[simp] theorem comp_footprint (R : Refinement D E) (M : Framed E w) (s : State) :
    (comp R M).footprint s = M.footprint s := rfl

/-- The composite's room is the lower room. -/
@[simp] theorem comp_room (R : Refinement D E) (M : Framed E w) (s : State) :
    (comp R M).room s = M.room s := rfl

/-- A function local to the lower framed refinement is local to the composite. -/
theorem Local.comp {R : Refinement D E} {M : Framed E w} {β : Type*} {f : State → β}
    (hf : M.Local f) : (comp R M).Local f := fun hs h hfr hr => hf hs.1 h hfr hr

/-- **Potentials stack across composition** with a framed refinement, as for refinements
(`Refinement.Amortized.comp`). -/
theorem amortized_comp {R : Refinement D E} {M : Framed E w} {lower : State → Op → ℕ}
    {middle : E.State → E.Op → ℕ} {upper : D.State → D.Op → ℕ} {Φ : E.State → ℕ}
    {Ψ : State → ℕ} (A : R.Amortized middle upper Φ) (B : M.Amortized lower middle Ψ) :
    (comp R M).Amortized lower upper fun s => Φ (M.abs s) + Ψ s :=
  A.comp B

/-! ## Frames of disjoint structures -/

variable {M} (N : Framed D₂ w)

/-- A method run of `M` keeps every cell of a disjoint, allocated footprint. -/
theorem agree_of_run {s : State} (o : D.Op) {a : D.Result o} {s' : State}
    {tr : (spec w).Transcript} (hM : M.inv s) (hN : N.inv s)
    (hd : Disjoint (M.footprint s) (N.footprint s)) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) :
    ∀ b ∈ N.footprint s, s'.mem b = s.mem b := fun b hb =>
  (M.modifies o hM hv hrun).1 b (N.lt_frontier hN hb) (Finset.disjoint_right.mp hd hb)

/-- A method run of `M` leaves room for `N` when both rooms fitted before. -/
theorem room_of_run {s : State} (o : D.Op) {a : D.Result o} {s' : State}
    {tr : (spec w).Transcript} (hM : M.inv s) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) {r : ℕ}
    (hroom : Fits w (s.frontier + (M.room s + r))) : Fits w (s'.frontier + (M.room s' + r)) :=
  hroom.of_le (by obtain ⟨-, -, h⟩ := M.modifies o hM hv hrun; omega)

/-- **The frame of a framed refinement.** A method run of `M` leaves a framed refinement with a
disjoint footprint unchanged, and the footprints disjoint and the shared room budget fitting. -/
theorem frame {s : State} (o : D.Op) {a : D.Result o} {s' : State}
    {tr : (spec w).Transcript} (hM : M.inv s) (hN : N.inv s)
    (hd : Disjoint (M.footprint s) (N.footprint s))
    (hroom : Fits w (s.frontier + (M.room s + N.room s))) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) :
    N.abs s' = N.abs s ∧ N.inv s' ∧ N.footprint s' = N.footprint s ∧ N.room s' = N.room s ∧
      Disjoint (M.footprint s') (N.footprint s') ∧
      Fits w (s'.frontier + (M.room s' + N.room s')) := by
  have hf := frontier_le_of_clientRun hrun
  have hroom' := room_of_run o hM hv hrun hroom
  obtain ⟨hN', habs, hfp, hr⟩ := N.congr hN (agree_of_run N o hM hN hd hv hrun) hf
    (hroom'.of_le (by omega))
  refine ⟨habs, hN', hfp, hr, Finset.disjoint_left.mpr fun b hb hb' => ?_, hr ▸ hroom'⟩
  rw [hfp] at hb'
  obtain ⟨-, hgrow, -⟩ := M.modifies o hM hv hrun
  rcases hgrow b hb with hb | hb
  · exact Finset.disjoint_left.mp hd hb hb'
  · exact absurd (N.lt_frontier hN hb') (Nat.not_lt.mpr hb)

/-- A method run of `M` leaves unchanged every function that reads only a disjoint footprint. -/
theorem Local.frame {β : Type*} {f : State → β} (hf : N.Local f) {s : State} (o : D.Op)
    {a : D.Result o} {s' : State} {tr : (spec w).Transcript} (hM : M.inv s) (hN : N.inv s)
    (hd : Disjoint (M.footprint s) (N.footprint s))
    (hroom : Fits w (s.frontier + (M.room s + N.room s))) (hv : D.valid (M.abs s) o)
    (hrun : (spec w).ClientRun s (M.methods o) a s' tr) : f s' = f s :=
  hf hN (agree_of_run N o hM hN hd hv hrun) (frontier_le_of_clientRun hrun)
    ((room_of_run o hM hv hrun hroom).of_le (by omega))

/-! ## Products -/

variable (M₁ : Framed D₁ w) (M₂ : Framed D₂ w)

/-- What keeps two framed refinements apart in one memory: disjoint footprints, and room for
both. -/
def Apart (s : State) : Prop :=
  Disjoint (M₁.footprint s) (M₂.footprint s) ∧ Fits w (s.frontier + (M₁.room s + M₂.room s))

/-- A method run of the left side keeps the right side and keeps the two apart. -/
theorem prod_frame_left {s : State} (o : D₁.Op) {a : D₁.Result o} {s' : State}
    {tr : (spec w).Transcript} (h₁ : M₁.inv s) (h₂ : M₂.inv s) (hJ : Apart M₁ M₂ s)
    (hv : D₁.valid (M₁.abs s) o) (hrun : (spec w).ClientRun s (M₁.methods o) a s' tr) :
    M₂.abs s' = M₂.abs s ∧ M₂.inv s' ∧ Apart M₁ M₂ s' := by
  obtain ⟨habs, hinv, -, -, hapart⟩ := frame M₂ o h₁ h₂ hJ.1 hJ.2 hv hrun
  exact ⟨habs, hinv, hapart⟩

/-- A method run of the right side keeps the left side and keeps the two apart. -/
theorem prod_frame_right {s : State} (o : D₂.Op) {a : D₂.Result o} {s' : State}
    {tr : (spec w).Transcript} (h₁ : M₁.inv s) (h₂ : M₂.inv s) (hJ : Apart M₁ M₂ s)
    (hv : D₂.valid (M₂.abs s) o) (hrun : (spec w).ClientRun s (M₂.methods o) a s' tr) :
    M₁.abs s' = M₁.abs s ∧ M₁.inv s' ∧ Apart M₁ M₂ s' := by
  obtain ⟨habs, hinv, -, -, hd, hroom⟩ :=
    frame M₁ o h₂ h₁ hJ.1.symm (by rw [Nat.add_comm (M₂.room s)]; exact hJ.2) hv hrun
  exact ⟨habs, hinv, hd.symm, by rw [Nat.add_comm (M₁.room s')]; exact hroom⟩

/-- **Products over one memory.** Two framed refinements implement the product of their
specifications over one memory, with the union of their footprints and the sum of their rooms,
while they are apart: their footprints are disjoint and the frontier plus both rooms fits a word.
Being apart is part of the product's invariant. -/
def prod : Framed (product D₁ D₂) w where
  toRefinement := M₁.toRefinement.prod M₂.toRefinement (Apart M₁ M₂)
    (prod_frame_left M₁ M₂) (prod_frame_right M₁ M₂)
  footprint s := M₁.footprint s ∪ M₂.footprint s
  room s := M₁.room s + M₂.room s
  lt_frontier {_ _} hs ha := by
    obtain ⟨h₁, h₂, -⟩ := hs
    rcases Finset.mem_union.mp ha with ha | ha
    · exact M₁.lt_frontier h₁ ha
    · exact M₂.lt_frontier h₂ ha
  congr {_ _} hs h hf hr := by
    obtain ⟨h₁, h₂, hd, -⟩ := hs
    obtain ⟨h₁', habs₁, hfp₁, hr₁⟩ := M₁.congr h₁
      (fun a ha => h a (Finset.mem_union_left _ ha)) hf (hr.of_le (by omega))
    obtain ⟨h₂', habs₂, hfp₂, hr₂⟩ := M₂.congr h₂
      (fun a ha => h a (Finset.mem_union_right _ ha)) hf (hr.of_le (by omega))
    refine ⟨⟨h₁', h₂', ?_, ?_⟩, ?_, ?_, ?_⟩
    · rwa [hfp₁, hfp₂]
    · rwa [hr₁, hr₂]
    · change (M₁.abs _, M₂.abs _) = (M₁.abs _, M₂.abs _)
      rw [habs₁, habs₂]
    · rw [hfp₁, hfp₂]
    · rw [hr₁, hr₂]
  modifies {s} o {a s' tr} hs hv hrun := by
    obtain ⟨h₁, h₂, hd, hroom⟩ := hs
    cases o with
    | inl o =>
      obtain ⟨hmod, hgrow, hr⟩ := M₁.modifies o h₁ hv hrun
      obtain ⟨-, -, hfp₂, hr₂, -⟩ := frame M₂ o h₁ h₂ hd hroom hv hrun
      refine ⟨fun b hb hb' => hmod b hb fun h => hb' (Finset.mem_union_left _ h),
        fun b hb => ?_, ?_⟩
      · change b ∈ M₁.footprint s' ∪ M₂.footprint s' at hb
        rw [hfp₂] at hb
        rcases Finset.mem_union.mp hb with hb | hb
        · exact (hgrow b hb).imp_left (Finset.mem_union_left _)
        · exact .inl (Finset.mem_union_right _ hb)
      · omega
    | inr o =>
      obtain ⟨hmod, hgrow, hr⟩ := M₂.modifies o h₂ hv hrun
      obtain ⟨-, -, hfp₁, hr₁, -⟩ := frame M₁ o h₂ h₁ hd.symm
        (by rw [Nat.add_comm (M₂.room s)]; exact hroom) hv hrun
      refine ⟨fun b hb hb' => hmod b hb fun h => hb' (Finset.mem_union_right _ h),
        fun b hb => ?_, ?_⟩
      · change b ∈ M₁.footprint s' ∪ M₂.footprint s' at hb
        rw [hfp₁] at hb
        rcases Finset.mem_union.mp hb with hb | hb
        · exact .inl (Finset.mem_union_left _ hb)
        · exact (hgrow b hb).imp_left (Finset.mem_union_right _)
      · omega

/-- The product's methods run each side's methods. They do not depend on the proofs. -/
theorem prod_methods : (M₁.prod M₂).methods = Methods.prod M₁.methods M₂.methods := rfl

/-- The product represents each side by its own abstraction. -/
@[simp] theorem prod_abs (s : State) : (M₁.prod M₂).abs s = (M₁.abs s, M₂.abs s) := rfl

/-- The product's invariant: both sides' invariants, and the two sides apart. -/
theorem prod_inv_iff (s : State) :
    (M₁.prod M₂).inv s ↔ M₁.inv s ∧ M₂.inv s ∧ Apart M₁ M₂ s := Iff.rfl

/-- The product's footprint is the union of the footprints. -/
@[simp] theorem prod_footprint (s : State) :
    (M₁.prod M₂).footprint s = M₁.footprint s ∪ M₂.footprint s := rfl

/-- The product's room is the sum of the rooms. -/
@[simp] theorem prod_room (s : State) : (M₁.prod M₂).room s = M₁.room s + M₂.room s := rfl

variable {M₁ M₂}

/-- A function local to the left side is local to the product. -/
theorem Local.prod_left {β : Type*} {f : State → β} (hf : M₁.Local f) :
    (M₁.prod M₂).Local f := fun ⟨h₁, _, _⟩ h hfr hr =>
  hf h₁ (fun a ha => h a (Finset.mem_union_left _ ha)) hfr
    (hr.of_le (Nat.add_le_add_left (Nat.le_add_right _ _) _))

/-- A function local to the right side is local to the product. -/
theorem Local.prod_right {β : Type*} {f : State → β} (hf : M₂.Local f) :
    (M₁.prod M₂).Local f := fun ⟨_, h₂, _⟩ h hfr hr =>
  hf h₂ (fun a ha => h a (Finset.mem_union_right _ ha)) hfr
    (hr.of_le (Nat.add_le_add_left (Nat.le_add_left _ _) _))

/-- **Potentials add across a product over one memory.** Certificates of the two sides against
one lower charge, with potentials that read only their own footprints, give a certificate of
the product with componentwise upper charges and the sum of the potentials. -/
theorem amortized_prod {lower : State → Op → ℕ} {upper₁ : D₁.State → D₁.Op → ℕ}
    {upper₂ : D₂.State → D₂.Op → ℕ} {Φ₁ Φ₂ : State → ℕ}
    (A₁ : M₁.Amortized lower upper₁ Φ₁) (A₂ : M₂.Amortized lower upper₂ Φ₂)
    (hΦ₁ : M₁.Local Φ₁) (hΦ₂ : M₂.Local Φ₂) :
    (M₁.prod M₂).Amortized lower (productCharge upper₁ upper₂) fun s => Φ₁ s + Φ₂ s :=
  Refinement.Amortized.prod (frame₁ := prod_frame_left M₁ M₂) (frame₂ := prod_frame_right M₁ M₂)
    A₁ A₂ (fun {_} o {_ _ _} h₁ h₂ hJ hv hrun => hΦ₂.frame M₂ o h₁ h₂ hJ.1 hJ.2 hv hrun)
    (fun {_} o {_ _ _} h₁ h₂ hJ hv hrun => hΦ₁.frame M₁ o h₂ h₁ hJ.1.symm
      (by rw [Nat.add_comm (M₂.room _)]; exact hJ.2) hv hrun)

/-- Setting up a product from structures allocated one after the other: `M₁` holds at `s`; a
run from `s` to `s'` leaves the cells below `s.frontier` unchanged; `M₂` holds at `s'` on a
footprint disjoint from `M₁`'s, such as one at or above `s.frontier`; and the frontier plus both
rooms fits. Then the product holds at `s'`, with `M₁`'s abstraction, footprint and room
unchanged. -/
theorem prod_of_fresh {s s' : State} (h₁ : M₁.inv s)
    (hmem : ∀ a < s.frontier, s'.mem a = s.mem a) (hf : s.frontier ≤ s'.frontier)
    (h₂ : M₂.inv s') (hd : Disjoint (M₁.footprint s) (M₂.footprint s'))
    (hroom : Fits w (s'.frontier + (M₁.room s + M₂.room s'))) :
    (M₁.prod M₂).inv s' ∧ (M₁.prod M₂).abs s' = (M₁.abs s, M₂.abs s') ∧
      (M₁.prod M₂).footprint s' = M₁.footprint s ∪ M₂.footprint s' ∧
      (M₁.prod M₂).room s' = M₁.room s + M₂.room s' := by
  obtain ⟨h₁', habs, hfp₁, hr₁⟩ := M₁.of_fresh h₁ hmem hf (hroom.of_le (by omega))
  exact ⟨⟨h₁', h₂, by rwa [hfp₁], by rwa [hr₁]⟩, by rw [prod_abs, habs],
    by rw [prod_footprint, hfp₁], by rw [prod_room, hr₁]⟩

end Framed

end Cslib.DataStructure.Memory
