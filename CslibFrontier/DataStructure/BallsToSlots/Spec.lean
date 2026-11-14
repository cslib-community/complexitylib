/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.StateTransition
public import CslibFrontier.Init
public import CslibFrontier.Probability.KWiseIndependent
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Order.Lattice.Nat
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Data.Nat.Bitwise.CommonPrefix
import CslibFrontier.Probability.KWiseIndependent.Concentration
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Balls-to-Slots Problem Specification

This module formalizes the pure *balls-to-slots* (probe-complexity) problem of Bender,
Farach-Colton, J. Kuszmaul, W. Kuszmaul, and Liu, *"On the Optimal Time/Space Tradeoff for Hash
Tables"*, *Proc. 54th ACM STOC*, pp. 1284–1297, 2022 (`arXiv:2111.00602v2`, Section 2.1, printed
p. 3 / PDF p. 4, and Section 3, printed p. 8 / PDF p. 9)
[BenderFarachColtonKuszmaulKuszmaulLiu2022], aligned with `Cslib`'s `StateTransitionSpec` grid:
* **Slot assignments (`SlotAssignment α M`)**: injective maps `Fin M → Option α` with `slotOf`,
  `present`, `freeSlots`, `delete`, and `put`. *(Adaptation: Section 3 permits `M` special slots
  of cost `log₂ M`; since Section 3.1's `k`-kick tree uses zero special slots, `SlotAssignment α M`
  stores all balls in primary slots `Fin M`.)*
* **Operations & costs**: `Op α` (`insert`, `delete`, `query`), 0-indexed `probeIndex` with integer
  floor probe cost `slotProbeComplexity = 1 + Nat.log 2 (probeIndex + 1)` (differing from Section
  2.1's real-logarithm `1 + log₂ i` by `< 1` per ball), and `switchingCost` (Section 2.1, printed
  p. 3 / PDF p. 4, and Section 3.1, printed p. 8 / PDF p. 9).

General `k`-wise fiber conditioning, disjoint-restriction concentration, and two-stage product
union-tail bounds live in `CslibFrontier.Probability.KWiseIndependent.Restriction`,
`CslibFrontier.Probability.KWiseIndependent.Concentration`, and
`CslibFrontier.Foundations.Probability.TwoStage`.

## Main definitions

* `Cslib.DataStructure.BallsToSlots.Op`, `stepSet`, `activeSetFrom`, `activeSet`, `opsBalls`,
  `ValidOp`, `ValidOpSeqFrom`, `ValidOpSeq`, `SlotAssignment`, `RespectsProbeSeq`, `probeIndex`,
  `slotProbeComplexity`, `ballProbeComplexity`, `totalProbeComplexity`, `xorProbeSeq`,
  `dyadicSplitEquiv`, `switchingCost`, `displacedBalls`, `changedSlots`, `spec`, `schemeSpec`.

## Main results

* `SlotAssignment.slotOf_eq_some_iff`, `SlotAssignment.card_present_add_card_freeSlots`,
  `totalProbeComplexity_eq_sum_present`, `card_activeSet_le`,
  `exists_split_last_insert_of_mem_activeSet`.
* `dens_sum_totalProbeComplexity_gt_le_of_snapshotBound`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*,
  Sections 2.1 and 3][BenderFarachColtonKuszmaulKuszmaulLiu2022]
-/

public section

namespace Cslib.DataStructure.BallsToSlots
open Finset
open scoped BigOperators

/-- Operations on a balls-to-slots scheme over ball universe `α`. -/
inductive Op (α : Type*) where
  /-- Insert ball `x` into the active set (no-op if `x` is already present). -/
  | insert (x : α)
  /-- Delete ball `x` from the active set (no-op if `x` is absent). -/
  | delete (x : α)
  /-- Query the slot currently assigned to ball `x` (`none` if `x` is absent). -/
  | query (x : α)
  deriving DecidableEq, Repr
/-- Observation type returned by each `Op α` over `M` slots `Fin M`. -/
abbrev Op.Result {α : Type*} (M : ℕ) : Op α → Type
  | .insert _ | .delete _ => Unit
  | .query _ => Option (Fin M)

section ActiveSet
variable {α : Type*} [DecidableEq α]
/-- Single-step evolution of the finite set of present balls. -/
@[expose] def stepSet (S : Finset α) : Op α → Finset α
  | .insert x => insert x S | .delete x => S.erase x | .query _ => S
@[simp] theorem stepSet_insert (S : Finset α) (x : α) : stepSet S (.insert x) = insert x S := rfl
@[simp] theorem stepSet_delete (S : Finset α) (x : α) : stepSet S (.delete x) = S.erase x := rfl
@[simp] theorem stepSet_query (S : Finset α) (x : α) : stepSet S (.query x) = S := rfl
/-- Active set of balls after executing `ops` starting from `S`. -/
@[expose] def activeSetFrom (S : Finset α) (ops : List (Op α)) : Finset α := ops.foldl stepSet S
@[simp] theorem activeSetFrom_nil (S : Finset α) : activeSetFrom S [] = S := rfl
@[simp] theorem activeSetFrom_cons (S : Finset α) (o : Op α) (ops : List (Op α)) :
    activeSetFrom S (o :: ops) = activeSetFrom (stepSet S o) ops := rfl
theorem activeSetFrom_append (S : Finset α) (ops₁ ops₂ : List (Op α)) :
    activeSetFrom S (ops₁ ++ ops₂) = activeSetFrom (activeSetFrom S ops₁) ops₂ := by
  simp only [activeSetFrom, List.foldl_append]
/-- Active set of balls after executing `ops` starting from `∅`. -/
@[expose] def activeSet (ops : List (Op α)) : Finset α := activeSetFrom ∅ ops
@[simp] theorem activeSet_nil : activeSet ([] : List (Op α)) = ∅ := rfl
/-- Finite set of balls mentioned anywhere in `ops`. -/
@[expose] def opsBalls : List (Op α) → Finset α
  | [] => ∅
  | .insert x :: ops | .delete x :: ops | .query x :: ops => insert x (opsBalls ops)

/-- Single-step operation admissibility at active set `S` under capacity `n_max`. -/
@[expose] def ValidOp (n_max : ℕ) (S : Finset α) : Op α → Prop
  | .insert x => #S < n_max ∨ x ∈ S
  | .delete _ | .query _ => True
/-- Admissibility of an oblivious operation sequence `ops` starting from active set `S`. -/
@[expose] def ValidOpSeqFrom (n_max : ℕ) : Finset α → List (Op α) → Prop
  | _, [] => True
  | S, o :: ops => ValidOp n_max S o ∧ ValidOpSeqFrom n_max (stepSet S o) ops
/-- Admissibility of an oblivious operation sequence `ops` starting from `∅`. -/
@[expose] def ValidOpSeq (n_max : ℕ) (ops : List (Op α)) : Prop := ValidOpSeqFrom n_max ∅ ops

theorem card_stepSet_le {n_max : ℕ} {S : Finset α} {o : Op α}
    (hS : #S ≤ n_max) (ho : ValidOp n_max S o) : #(stepSet S o) ≤ n_max := by
  cases o with
  | insert x =>
    rcases ho with hlt | hx
    · exact (card_insert_le x S).trans (by omega)
    · simpa [stepSet, insert_eq_of_mem hx] using hS
  | delete x => exact card_erase_le.trans hS
  | query _ => exact hS
theorem card_activeSetFrom_le {n_max : ℕ} {S : Finset α} {ops : List (Op α)} (hS : #S ≤ n_max)
    (hval : ValidOpSeqFrom n_max S ops) : #(activeSetFrom S ops) ≤ n_max := by
  induction ops generalizing S with
  | nil => exact hS
  | cons _ _ ih => exact ih (card_stepSet_le hS hval.1) hval.2
/-- Every admissible operation sequence from `∅` maintains at most `n_max` present balls. -/
theorem card_activeSet_le {n_max : ℕ} {ops : List (Op α)} (hval : ValidOpSeq n_max ops) :
    #(activeSet ops) ≤ n_max := card_activeSetFrom_le (by simp) hval
theorem validOpSeqFrom_append {n_max : ℕ} {S : Finset α} {ops₁ ops₂ : List (Op α)} :
    ValidOpSeqFrom n_max S (ops₁ ++ ops₂) ↔
      ValidOpSeqFrom n_max S ops₁ ∧ ValidOpSeqFrom n_max (activeSetFrom S ops₁) ops₂ := by
  induction ops₁ generalizing S with
  | nil => simp [ValidOpSeqFrom]
  | cons _ _ ih => simp only [List.cons_append, ValidOpSeqFrom, activeSetFrom_cons, ih, and_assoc]
theorem activeSetFrom_subset_union_opsBalls (S : Finset α) (ops : List (Op α)) :
    activeSetFrom S ops ⊆ S ∪ opsBalls ops := by
  induction ops generalizing S with
  | nil => simp [opsBalls]
  | cons o _ ih =>
    intro z hz; have hz' := ih (stepSet S o) hz
    cases o <;> simp only [stepSet, opsBalls, mem_union, mem_insert, mem_erase] at hz' ⊢ <;> tauto
theorem activeSet_subset_opsBalls (ops : List (Op α)) : activeSet ops ⊆ opsBalls ops := by
  simpa [activeSet] using activeSetFrom_subset_union_opsBalls ∅ ops
theorem opsBalls_append (ops₁ ops₂ : List (Op α)) :
    opsBalls (ops₁ ++ ops₂) = opsBalls ops₁ ∪ opsBalls ops₂ := by
  induction ops₁ with
  | nil => simp [opsBalls]
  | cons o _ ih => cases o <;> simp [opsBalls, ih, insert_union]

/-- Every ball `x ∈ activeSet ops` of an admissible sequence `ops` has a last absent-to-present
insertion split `ops = pre ++ .insert x :: suf` where `ValidOpSeq n_max pre`, `x ∉ activeSet pre`,
`#(activeSet pre) < n_max`, and `suf` contains no `.delete x`. -/
theorem exists_split_last_insert_of_mem_activeSet {n_max : ℕ} {ops : List (Op α)}
    (hval : ValidOpSeq n_max ops) {x : α} (hx : x ∈ activeSet ops) :
    ∃ pre suf : List (Op α), ops = pre ++ .insert x :: suf ∧
      ValidOpSeq n_max pre ∧ x ∉ activeSet pre ∧ #(activeSet pre) < n_max ∧
      ∀ o ∈ suf, o ≠ .delete x := by
  induction ops using List.reverseRecOn with
  | nil => simp at hx
  | append_singleton init o ih =>
    obtain ⟨hinit, ho, -⟩ := (validOpSeqFrom_append (S := ∅)).mp hval
    rw [activeSet, activeSetFrom_append, activeSetFrom_cons, activeSetFrom_nil, ← activeSet] at hx
    by_cases hx_init : x ∈ activeSet init
    · have hne : o ≠ .delete x := by rintro rfl; simp at hx
      obtain ⟨pre, suf, heq, hpre, hx_pre, hlt_pre, hsuf⟩ := ih hinit hx_init
      refine ⟨pre, suf ++ [o], by rw [heq, List.append_assoc, List.cons_append],
        hpre, hx_pre, hlt_pre, fun o' ho' => ?_⟩
      rcases List.mem_append.mp ho' with ho' | ho'
      · exact hsuf o' ho'
      · rwa [List.mem_singleton.mp ho']
    · cases o with
      | insert _ =>
        rcases Finset.mem_insert.mp hx with rfl | hmem
        · exact ⟨init, [], rfl, hinit, hx_init, ho.resolve_right hx_init, by simp⟩
        · exact (hx_init hmem).elim
      | delete _ => exact (hx_init (Finset.mem_of_mem_erase hx)).elim
      | query _ => exact (hx_init hx).elim
end ActiveSet

/-! ### Injective slot assignments -/

/-- An injective assignment of balls from `α` into `M` unit-capacity primary slots `Fin M`. -/
@[ext] structure SlotAssignment (α : Type*) (M : ℕ) where
  /-- Partial map giving the ball stored in each slot (`none` if the slot is free). -/
  occupant : Fin M → Option α
  /-- Slot-wise injectivity: each ball occupies at most one slot. -/
  injective : ∀ ⦃r₁ r₂ : Fin M⦄ ⦃x : α⦄,
    occupant r₁ = some x → occupant r₂ = some x → r₁ = r₂

namespace SlotAssignment

/-- The empty slot assignment over `M` free slots. -/
@[expose] def empty (α : Type*) (M : ℕ) : SlotAssignment α M where
  occupant _ := none
  injective _ _ _ h := by cases h
/-- Finite set of currently unoccupied slots in `s`. -/
@[expose] def freeSlots {α : Type*} {M : ℕ} (s : SlotAssignment α M) : Finset (Fin M) :=
  Finset.univ.filter fun r => (s.occupant r).isNone

section Decidable
variable {α : Type*} [DecidableEq α] {M : ℕ}

/-- Computable lookup of the unique slot holding ball `x` (`none` if `x` is absent). -/
@[expose] def slotOf (s : SlotAssignment α M) (x : α) : Option (Fin M) :=
  (List.finRange M).find? fun r => decide (s.occupant r = some x)
/-- Finite set of balls currently present in `s`. -/
@[expose] def present (s : SlotAssignment α M) : Finset α :=
  Finset.univ.biUnion fun r => (s.occupant r).toFinset

@[simp] theorem slotOf_eq_some_iff (s : SlotAssignment α M) (x : α) (r : Fin M) :
    s.slotOf x = some r ↔ s.occupant r = some x := by
  unfold slotOf; refine ⟨fun h => ?_, fun hr => ?_⟩
  · have hd := List.find?_some h; exact of_decide_eq_true hd
  · cases hfind : (List.finRange M).find? (fun r' => decide (s.occupant r' = some x)) with
    | none =>
      have hnone := (List.find?_eq_none.mp hfind) r (List.mem_finRange r); simp [hr] at hnone
    | some r' =>
      have hd := List.find?_some hfind
      exact congrArg some (s.injective (of_decide_eq_true hd) hr)

@[simp] theorem slotOf_eq_none_iff (s : SlotAssignment α M) (x : α) :
    s.slotOf x = none ↔ ∀ r : Fin M, s.occupant r ≠ some x := by simp [slotOf, List.find?_eq_none]
@[simp] theorem mem_present_iff (s : SlotAssignment α M) (x : α) :
    x ∈ s.present ↔ ∃ r : Fin M, s.occupant r = some x := by simp [present]
theorem mem_present_iff_slotOf_isSome (s : SlotAssignment α M) (x : α) :
    x ∈ s.present ↔ (s.slotOf x).isSome := by
  rw [mem_present_iff, Option.isSome_iff_exists]
  exact exists_congr fun r => (s.slotOf_eq_some_iff x r).symm
@[simp] theorem present_empty (α : Type*) [DecidableEq α] (M : ℕ) : (empty α M).present = ∅ := by
  ext x; simp [empty]
@[simp] theorem slotOf_empty (α : Type*) [DecidableEq α] (M : ℕ) (x : α) :
    (empty α M).slotOf x = none := by simp [empty]

theorem card_present_eq_card_occupied (s : SlotAssignment α M) :
    #s.present = #(Finset.univ.filter fun r : Fin M => (s.occupant r).isSome) := by
  refine Finset.card_bij' (fun x hx => (s.slotOf x).get ((s.mem_present_iff_slotOf_isSome x).mp hx))
      (fun r hr => (s.occupant r).get (mem_filter.mp hr).2) ?_ ?_ ?_ ?_
  · intro x hx; have hsome := (s.mem_present_iff_slotOf_isSome x).mp hx
    simp [(s.slotOf_eq_some_iff x _).mp (Option.eq_some_of_isSome hsome)]
  · intro r hr; exact (s.mem_present_iff _).mpr ⟨r, Option.eq_some_of_isSome (mem_filter.mp hr).2⟩
  · intro x hx; have hsome := (s.mem_present_iff_slotOf_isSome x).mp hx
    exact Option.get_of_mem _ ((s.slotOf_eq_some_iff x _).mp (Option.eq_some_of_isSome hsome))
  · intro r hr; have hsome := (mem_filter.mp hr).2
    exact Option.get_of_mem _ ((s.slotOf_eq_some_iff _ r).mpr (Option.eq_some_of_isSome hsome))

/-- Occupied balls and free slots partition all `M` slots. -/
theorem card_present_add_card_freeSlots (s : SlotAssignment α M) :
    #s.present + #s.freeSlots = M := by
  rw [card_present_eq_card_occupied, freeSlots]
  have hcompl : (Finset.univ.filter fun r : Fin M => (s.occupant r).isNone) =
      (Finset.univ.filter fun r : Fin M => ¬ (s.occupant r).isSome) := by
    ext r; cases s.occupant r <;> simp
  rw [hcompl, Finset.card_filter_add_card_filter_not]; simp

theorem card_present_le (s : SlotAssignment α M) : #s.present ≤ M := by
  have := s.card_present_add_card_freeSlots; omega

/-- Strictly fewer than `M` balls are present if and only if at least one slot is free. -/
theorem card_present_lt_iff_freeSlots_nonempty (s : SlotAssignment α M) :
    #s.present < M ↔ s.freeSlots.Nonempty := by
  rw [← Finset.card_pos]; have := s.card_present_add_card_freeSlots; omega

/-- Delete ball `x` by vacating its slot (leaving all other slots untouched). -/
@[expose] def delete (s : SlotAssignment α M) (x : α) : SlotAssignment α M where
  occupant r := if s.occupant r = some x then none else s.occupant r
  injective _ _ _ h₁ h₂ := by split_ifs at h₁ h₂; exact s.injective h₁ h₂

@[simp] theorem slotOf_delete_self (s : SlotAssignment α M) (x : α) :
    (s.delete x).slotOf x = none := by rw [slotOf_eq_none_iff]; intro r; simp [delete]
theorem slotOf_delete_of_ne (s : SlotAssignment α M) {x y : α} (hne : y ≠ x) :
    (s.delete x).slotOf y = s.slotOf y := by
  cases h : s.slotOf y with
  | none =>
    rw [slotOf_eq_none_iff] at h ⊢; intro r; simp only [delete]
    split_ifs with hrx; · simp
    · exact h r
  | some r => rw [slotOf_eq_some_iff] at h ⊢; simp [delete, h, hne]
@[simp] theorem present_delete (s : SlotAssignment α M) (x : α) :
    (s.delete x).present = s.present.erase x := by
  ext y; rw [mem_erase, mem_present_iff_slotOf_isSome, mem_present_iff_slotOf_isSome]
  rcases eq_or_ne y x with rfl | hyx <;> simp [slotOf_delete_of_ne, *]

/-- Place ball `y` into slot `r`, preserving `injective` unconditionally. -/
@[expose] def put (s : SlotAssignment α M) (r : Fin M) (y : α) : SlotAssignment α M where
  occupant r' := if r' = r then some y else if s.occupant r' = some y then none else s.occupant r'
  injective r₁ r₂ z h₁ h₂ := by
    by_cases hr₁ : r₁ = r <;> by_cases hr₂ : r₂ = r
    · exact hr₁.trans hr₂.symm
    · subst hr₁; simp only [↓reduceIte, hr₂] at h₁ h₂; cases h₁; split_ifs at h₂; contradiction
    · subst hr₂; simp only [↓reduceIte, hr₁] at h₁ h₂; cases h₂; split_ifs at h₁; contradiction
    · simp only [hr₁, hr₂, ↓reduceIte] at h₁ h₂; split_ifs at h₁ h₂; exact s.injective h₁ h₂

theorem occupant_put_of_absent (s : SlotAssignment α M) (r : Fin M) {y : α}
    (hy : ∀ r', s.occupant r' ≠ some y) :
    (s.put r y).occupant = Function.update s.occupant r (some y) := by
  funext r'; rcases eq_or_ne r' r with rfl | hr'; · simp [put]
  · simp [put, hr', hy r']
@[simp] theorem slotOf_put_self (s : SlotAssignment α M) (r : Fin M) (y : α) :
    (s.put r y).slotOf y = some r := by rw [slotOf_eq_some_iff]; simp [put]
theorem slotOf_put_of_ne (s : SlotAssignment α M) (r : Fin M) (y : α) {z : α} (hzy : z ≠ y)
    (hrz : s.occupant r ≠ some z) : (s.put r y).slotOf z = s.slotOf z := by
  cases h : s.slotOf z with
  | none =>
    rw [slotOf_eq_none_iff] at h ⊢; intro r'; rcases eq_or_ne r' r with rfl | hr'
    · simp [put, hzy.symm]
    · simp only [put, hr', ↓reduceIte]; split_ifs; · simp
      · exact h r'
  | some r' =>
    have hr'z := (s.slotOf_eq_some_iff z r').mp h
    have hr'r : r' ≠ r := fun heq => hrz (heq ▸ hr'z)
    rw [slotOf_eq_some_iff]; simp [put, hr'r, hr'z, hzy]
theorem put_occupant_ne_old (s : SlotAssignment α M) {r : Fin M} {y y' : α}
    (hy : ∀ r', s.occupant r' ≠ some y) (hocc : s.occupant r = some y') :
    ∀ r' : Fin M, (s.put r y).occupant r' ≠ some y' := by
  intro r'; rw [s.occupant_put_of_absent r hy]; rcases eq_or_ne r' r with rfl | hr'
  · simp [show y ≠ y' from fun heq => hy r' (heq ▸ hocc)]
  · rw [Function.update_of_ne hr']; exact fun h => hr' (s.injective h hocc)
theorem present_put_of_isNone (s : SlotAssignment α M) {r : Fin M} (hr : s.occupant r = none)
    (y : α) : (s.put r y).present = insert y s.present := by
  ext z; rw [Finset.mem_insert, mem_present_iff_slotOf_isSome, mem_present_iff_slotOf_isSome]
  rcases eq_or_ne z y with rfl | hzy
  · simp
  · simp [s.slotOf_put_of_ne r y hzy (by simp [hr]), hzy]
theorem present_put_of_some (s : SlotAssignment α M) {r : Fin M} {y y' : α}
    (hy : ∀ r', s.occupant r' ≠ some y) (hocc : s.occupant r = some y') :
    (s.put r y).present = insert y (s.present.erase y') := by
  ext z; rw [Finset.mem_insert, Finset.mem_erase, mem_present_iff_slotOf_isSome,
    mem_present_iff_slotOf_isSome]
  rcases eq_or_ne z y with rfl | hzy
  · simp
  · rcases eq_or_ne z y' with rfl | hzy'
    · simp [(slotOf_eq_none_iff _ z).mpr (s.put_occupant_ne_old hy hocc), hzy]
    · simp [s.slotOf_put_of_ne r y hzy (by rw [hocc]; exact fun h => hzy' (Option.some.inj h).symm),
        hzy, hzy']
end Decidable
end SlotAssignment

/-! ### Probe sequences, probe complexity, and switching cost -/

/-- A slot assignment `s` respects `probeSeq` when every present ball sits at a slot appearing on
its probe sequence. -/
@[expose] def RespectsProbeSeq {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M)
    (s : SlotAssignment α M) : Prop :=
  ∀ r : Fin M, ∀ x : α, s.occupant r = some x → ∃ idx : ℕ, probeSeq x idx = r

theorem respectsProbeSeq_empty {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M) :
    RespectsProbeSeq probeSeq (SlotAssignment.empty α M) := fun _ _ h => by cases h
theorem RespectsProbeSeq.delete {α : Type*} [DecidableEq α] {M : ℕ} {probeSeq : α → ℕ → Fin M}
    {s : SlotAssignment α M} (hs : RespectsProbeSeq probeSeq s) (x : α) :
    RespectsProbeSeq probeSeq (s.delete x) := fun r y hy => by
  simp only [SlotAssignment.delete] at hy; split_ifs at hy; exact hs r y hy

/-- Minimum 0-based probe offset at which `probeSeq x` reaches slot `r`. -/
noncomputable def probeIndex {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M) (x : α)
    (r : Fin M) : ℕ := sInf {idx : ℕ | probeSeq x idx = r}
theorem probeIndex_le {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M) (x : α)
    {idx : ℕ} {r : Fin M} (h : probeSeq x idx = r) : probeIndex probeSeq x r ≤ idx := Nat.sInf_le h
theorem probeSeq_probeIndex {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M) (x : α)
    {r : Fin M} (h : ∃ idx : ℕ, probeSeq x idx = r) :
    probeSeq x (probeIndex probeSeq x r) = r :=
  let ⟨idx, hidx⟩ := h; Nat.sInf_mem (s := {idx : ℕ | probeSeq x idx = r}) ⟨idx, hidx⟩

/-- Integer probe complexity `1 + ⌊log₂ (probeIndex + 1)⌋` of storing ball `x` in slot `r`.
Uses the floor logarithm `Nat.log 2` for 1-based probe index `i = probeIndex + 1`, differing from
the real-logarithm measure `1 + log₂ i` of [BenderFarachColtonKuszmaulKuszmaulLiu2022] (Section 2.1,
printed p. 3 / PDF p. 4, and Section 3, printed p. 8 / PDF p. 9) by strictly less than `1` per ball
and agreeing asymptotically. -/
noncomputable def slotProbeComplexity {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M)
    (x : α) (r : Fin M) : ℕ := 1 + Nat.log 2 (probeIndex probeSeq x r + 1)
theorem slotProbeComplexity_le_of_probeIndex_lt_two_pow {α : Type*} {M : ℕ}
    (probeSeq : α → ℕ → Fin M) (x : α) (r : Fin M) {e : ℕ}
    (h : probeIndex probeSeq x r < 2 ^ e) : slotProbeComplexity probeSeq x r ≤ 1 + e :=
  Nat.add_le_add_left ((Nat.log_mono_right (Nat.add_one_le_iff.mpr h)).trans_eq
    (Nat.log_pow Nat.one_lt_two e)) 1

/-- Canonical deduplicated XOR probe sequence `idx ↦ g(x) ^^^ (idx % 2 ^ m)` around `g(x)`. -/
@[expose] def xorProbeSeq {α : Type*} (m : ℕ) (g : α → Fin (2 ^ m)) (x : α)
    (idx : ℕ) : Fin (2 ^ m) :=
  ⟨(g x).val ^^^ (idx % 2 ^ m), Nat.xor_lt_two_pow (g x).isLt (Nat.mod_lt _ (by positivity))⟩
theorem xorProbeSeq_xor_self {α : Type*} (m : ℕ) (g : α → Fin (2 ^ m)) (x : α) (r : Fin (2 ^ m)) :
    xorProbeSeq m g x ((g x).val ^^^ r.val) = r := by
  have hlt := Nat.xor_lt_two_pow (g x).isLt r.isLt; apply Fin.ext
  simp only [xorProbeSeq, Nat.mod_eq_of_lt hlt, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
theorem respectsProbeSeq_xorProbeSeq {α : Type*} (m : ℕ) (g : α → Fin (2 ^ m))
    (s : SlotAssignment α (2 ^ m)) : RespectsProbeSeq (xorProbeSeq m g) s :=
  fun r x _ => ⟨(g x).val ^^^ r.val, xorProbeSeq_xor_self m g x r⟩
theorem slotProbeComplexity_xorProbeSeq_le_of_div_eq {α : Type*} (m : ℕ) (g : α → Fin (2 ^ m))
    (x : α) {e : ℕ} {r : Fin (2 ^ m)} (hr : r.val / 2 ^ e = (g x).val / 2 ^ e) :
    slotProbeComplexity (xorProbeSeq m g) x r ≤ 1 + e :=
  slotProbeComplexity_le_of_probeIndex_lt_two_pow (xorProbeSeq m g) x r
    ((probeIndex_le (xorProbeSeq m g) x (xorProbeSeq_xor_self m g x r)).trans_lt
      ((Nat.div_two_pow_eq_iff_xor_lt _ _ _).mp hr.symm))

/-- Canonical bijection splitting an `(m + c)`-bit word into `(low m bits, high c bits)`, built
from `finProdFinEquiv`. -/
@[expose] def dyadicSplitEquiv (m c : ℕ) : Fin (2 ^ (m + c)) ≃ Fin (2 ^ m) × Fin (2 ^ c) :=
  (finCongr ((Nat.pow_add 2 m c).trans (Nat.mul_comm (2 ^ m) (2 ^ c)))).trans
    (finProdFinEquiv.symm.trans (Equiv.prodComm (Fin (2 ^ c)) (Fin (2 ^ m))))

@[simp] theorem val_dyadicSplitEquiv_fst (m c : ℕ) (u : Fin (2 ^ (m + c))) :
    (dyadicSplitEquiv m c u).1.val = u.val % 2 ^ m := rfl

@[simp] theorem val_dyadicSplitEquiv_snd (m c : ℕ) (u : Fin (2 ^ (m + c))) :
    (dyadicSplitEquiv m c u).2.val = u.val / 2 ^ m := rfl

@[simp] theorem val_dyadicSplitEquiv_symm (m c : ℕ) (p : Fin (2 ^ m) × Fin (2 ^ c)) :
    ((dyadicSplitEquiv m c).symm p).val = p.1.val + 2 ^ m * p.2.val := rfl

/-- Probe complexity of ball `x` in assignment `s` (`0` if `x` is absent). -/
noncomputable def ballProbeComplexity {α : Type*} [DecidableEq α] {M : ℕ}
    (probeSeq : α → ℕ → Fin M) (s : SlotAssignment α M) (x : α) : ℕ :=
  match s.slotOf x with | none => 0 | some r => slotProbeComplexity probeSeq x r
@[simp] theorem ballProbeComplexity_of_slotOf_eq_none {α : Type*} [DecidableEq α] {M : ℕ}
    (probeSeq : α → ℕ → Fin M) {s : SlotAssignment α M} {x : α} (h : s.slotOf x = none) :
    ballProbeComplexity probeSeq s x = 0 := by simp [ballProbeComplexity, h]
@[simp] theorem ballProbeComplexity_of_slotOf_eq_some {α : Type*} [DecidableEq α] {M : ℕ}
    (probeSeq : α → ℕ → Fin M) {s : SlotAssignment α M} {x : α} {r : Fin M}
    (h : s.slotOf x = some r) :
    ballProbeComplexity probeSeq s x = slotProbeComplexity probeSeq x r := by
  simp [ballProbeComplexity, h]

/-- Total probe complexity summed across all occupied slots of `s`. -/
noncomputable def totalProbeComplexity {α : Type*} {M : ℕ} (probeSeq : α → ℕ → Fin M)
    (s : SlotAssignment α M) : ℕ :=
  ∑ r : Fin M, match s.occupant r with | none => 0 | some x => slotProbeComplexity probeSeq x r

/-- Total probe complexity over occupied slots equals the sum of `ballProbeComplexity` over
`s.present`. -/
theorem totalProbeComplexity_eq_sum_present {α : Type*} [DecidableEq α] {M : ℕ}
    (probeSeq : α → ℕ → Fin M) (s : SlotAssignment α M) :
    totalProbeComplexity probeSeq s = ∑ x ∈ s.present, ballProbeComplexity probeSeq s x := by
  unfold totalProbeComplexity
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun r : Fin M => (s.occupant r).isSome)]
  have hzero : (∑ r ∈ Finset.univ.filter (fun r : Fin M => ¬ (s.occupant r).isSome),
      match s.occupant r with | none => 0 | some x => slotProbeComplexity probeSeq x r) = 0 :=
    Finset.sum_eq_zero fun r hr => by
      have hnone := (mem_filter.mp hr).2; cases h : s.occupant r <;> simp [h] at hnone ⊢
  rw [hzero, add_zero]
  refine Finset.sum_bij' (fun r hr => (s.occupant r).get (mem_filter.mp hr).2)
    (fun x hx => (s.slotOf x).get ((s.mem_present_iff_slotOf_isSome x).mp hx)) ?_ ?_ ?_ ?_ ?_
  · intro r hr; exact (s.mem_present_iff _).mpr ⟨r, Option.eq_some_of_isSome (mem_filter.mp hr).2⟩
  · intro x hx; have hsome := (s.mem_present_iff_slotOf_isSome x).mp hx
    simp [(s.slotOf_eq_some_iff x _).mp (Option.eq_some_of_isSome hsome)]
  · intro r hr; have hsome := (mem_filter.mp hr).2
    exact Option.get_of_mem _ ((s.slotOf_eq_some_iff _ r).mpr (Option.eq_some_of_isSome hsome))
  · intro x hx; have hsome := (s.mem_present_iff_slotOf_isSome x).mp hx
    exact Option.get_of_mem _ ((s.slotOf_eq_some_iff x _).mp (Option.eq_some_of_isSome hsome))
  · intro r hr
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (mem_filter.mp hr).2
    simp only [hx, Option.get_some,
      ballProbeComplexity_of_slotOf_eq_some _ ((s.slotOf_eq_some_iff x r).mpr hx)]

section SwitchingCost
variable {α : Type*} [DecidableEq α] {M : ℕ}

/-- Deterministic switching cost between `s` and `s'`: balls in `s.present ∪ s'.present` whose
assigned slot changed. -/
@[expose] def switchingCost (s s' : SlotAssignment α M) : ℕ :=
  #{x ∈ s.present ∪ s'.present | s.slotOf x ≠ s'.slotOf x}
/-- Number of balls present in both `s` and `s'` that moved to a different slot. -/
@[expose] def displacedBalls (s s' : SlotAssignment α M) : ℕ :=
  #{x ∈ s.present ∩ s'.present | s.slotOf x ≠ s'.slotOf x}
/-- Number of slots `r : Fin M` whose occupant changed between `s` and `s'`. -/
@[expose] def changedSlots (s s' : SlotAssignment α M) : ℕ :=
  #{r : Fin M | s.occupant r ≠ s'.occupant r}

@[simp] theorem switchingCost_self (s : SlotAssignment α M) : switchingCost s s = 0 := by
  simp [switchingCost]
@[simp] theorem changedSlots_self (s : SlotAssignment α M) : changedSlots s s = 0 := by
  simp [changedSlots]
theorem changedSlots_triangle (s₁ s₂ s₃ : SlotAssignment α M) :
    changedSlots s₁ s₃ ≤ changedSlots s₁ s₂ + changedSlots s₂ s₃ := by
  refine (Finset.card_le_card fun r hr => ?_).trans (Finset.card_union_le _ _)
  simp only [mem_filter, mem_univ, true_and, mem_union] at hr ⊢
  by_contra h; push Not at h; exact hr (h.1.trans h.2)
theorem SlotAssignment.changedSlots_put_le (s : SlotAssignment α M) (r : Fin M) {y : α}
    (hy : ∀ r', s.occupant r' ≠ some y) : changedSlots s (s.put r y) ≤ 1 := by
  refine (Finset.card_le_card (t := {r}) fun r' hr' => ?_).trans (by simp)
  rw [Finset.mem_singleton]; by_contra hne
  exact (Finset.mem_filter.mp hr').2
    (by rw [s.occupant_put_of_absent r hy, Function.update_of_ne hne])

/-- When `s.present ⊆ s'.present`, `switchingCost s s' ≤ changedSlots s s'`. -/
theorem switchingCost_le_changedSlots_of_subset {s s' : SlotAssignment α M}
    (hsub : s.present ⊆ s'.present) : switchingCost s s' ≤ changedSlots s s' := by
  unfold switchingCost changedSlots; rw [Finset.union_eq_right.mpr hsub]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [Finset.card_eq_zero.mp (Nat.le_zero.mp s'.card_present_le)]
  · refine Finset.card_le_card_of_injOn (fun z => (s'.slotOf z).getD ⟨0, hM⟩) ?_ ?_
    · intro z hz; rw [Finset.mem_coe, Finset.mem_filter] at hz ⊢
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp ((s'.mem_present_iff_slotOf_isSome z).mp hz.1)
      simp only [hr, Option.getD_some, Finset.mem_univ, true_and]; intro heq
      exact hz.2 (((s.slotOf_eq_some_iff z r).mpr
        (heq.trans ((s'.slotOf_eq_some_iff z r).mp hr))).trans hr.symm)
    · intro z₁ hz₁ z₂ hz₂ heq; rw [Finset.mem_coe, Finset.mem_filter] at hz₁ hz₂
      obtain ⟨r₁, hr₁⟩ :=
        Option.isSome_iff_exists.mp ((s'.mem_present_iff_slotOf_isSome z₁).mp hz₁.1)
      obtain ⟨r₂, hr₂⟩ :=
        Option.isSome_iff_exists.mp ((s'.mem_present_iff_slotOf_isSome z₂).mp hz₂.1)
      simp only [hr₁, hr₂, Option.getD_some] at heq; subst heq
      exact Option.some.inj (((s'.slotOf_eq_some_iff z₁ r₁).mp hr₁).symm.trans
        ((s'.slotOf_eq_some_iff z₂ r₁).mp hr₂))

theorem displacedBalls_add_one_le_switchingCost {s s' : SlotAssignment α M} {y : α}
    (hy_old : y ∉ s.present) (hy_new : y ∈ s'.present) :
    displacedBalls s s' + 1 ≤ switchingCost s s' := by
  unfold displacedBalls switchingCost
  rw [← Finset.card_insert_of_notMem (a := y) (by simp [hy_old])]
  refine Finset.card_le_card fun z hz => ?_
  rw [Finset.mem_insert] at hz; rw [Finset.mem_filter]
  rcases hz with rfl | hz
  · refine ⟨Finset.mem_union_right _ hy_new, ?_⟩
    have h1 : s.slotOf z = none := by
      by_contra hsome
      exact hy_old ((s.mem_present_iff_slotOf_isSome z).mpr (Option.ne_none_iff_isSome.mp hsome))
    rw [h1]
    exact (Option.ne_none_iff_isSome.mpr ((s'.mem_present_iff_slotOf_isSome z).mp hy_new)).symm
  · rw [Finset.mem_filter, Finset.mem_inter] at hz; exact ⟨Finset.mem_union_left _ hz.1.1, hz.2⟩

/-- Deleting `x` displaces `0` remaining balls. -/
@[simp] theorem SlotAssignment.displacedBalls_delete_eq_zero (s : SlotAssignment α M) (x : α) :
    displacedBalls s (s.delete x) = 0 := by
  rw [displacedBalls, Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro y hy
  rw [SlotAssignment.present_delete, Finset.mem_inter, Finset.mem_erase] at hy
  exact absurd (s.slotOf_delete_of_ne hy.2.1).symm
/-- Deleting `x` has switching cost at most `1`. -/
theorem SlotAssignment.switchingCost_delete_le (s : SlotAssignment α M) (x : α) :
    switchingCost s (s.delete x) ≤ 1 := by
  refine (Finset.card_le_card (t := {x}) fun y hy => ?_).trans (by simp)
  rw [Finset.mem_singleton]; by_contra hne
  exact (Finset.mem_filter.mp hy).2 (s.slotOf_delete_of_ne hne).symm
/-- Deleting `x` modifies at most `1` slot. -/
theorem SlotAssignment.changedSlots_delete_le (s : SlotAssignment α M) (x : α) :
    changedSlots s (s.delete x) ≤ 1 := by
  cases h : s.slotOf x with
  | none =>
    have heq : ({r : Fin M | s.occupant r ≠ (s.delete x).occupant r} : Finset (Fin M)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun r _ => by
        simp [SlotAssignment.delete, (s.slotOf_eq_none_iff x).mp h r]
    simp [changedSlots, heq]
  | some r₀ =>
    refine (Finset.card_le_card (t := {r₀}) fun r hr => ?_).trans (by simp)
    rw [Finset.mem_singleton]; by_contra hne
    exact (Finset.mem_filter.mp hr).2 (by
      simp [SlotAssignment.delete, show s.occupant r ≠ some x from
        fun hx => hne (s.injective hx ((s.slotOf_eq_some_iff x r₀).mp h))])
end SwitchingCost

/-- Relational `StateTransitionSpec` for a balls-to-slots scheme over `α`, `M` slots, and capacity
`n_max`. -/
@[expose] def spec (α : Type*) [DecidableEq α] (M n_max : ℕ) : StateTransitionSpec where
  State := SlotAssignment α M
  Op := Op α
  Result := Op.Result M
  valid s o := ValidOp n_max s.present o
  step s o s' res := match o, res with
    | .insert x, () => s'.present = insert x s.present
    | .delete x, () => s'.present = s.present.erase x
    | .query x, out => s' = s ∧ out = s.slotOf x
/-- Relational `StateTransitionSpec` additionally enforcing probe-sequence validity and worst-case
per-operation switching-cost bound `B_switch`. -/
@[expose] def schemeSpec (α : Type*) [DecidableEq α] (M n_max B_switch : ℕ)
    (probeSeq : α → ℕ → Fin M) : StateTransitionSpec where
  State := SlotAssignment α M
  Op := Op α
  Result := Op.Result M
  valid s o := ValidOp n_max s.present o ∧ RespectsProbeSeq probeSeq s
  step s o s' res := RespectsProbeSeq probeSeq s' ∧ switchingCost s s' ≤ B_switch ∧
    (spec α M n_max).step s o s' res

section Probability
open Cslib.Probability Fintype

/-- `2m`-th moment concentration for total probe complexity across a collection `R` of admissible
histories `ops b` with pairwise disjoint `opsBalls (ops b)`, given a per-ball snapshot bound. -/
theorem dens_sum_totalProbeComplexity_gt_le_of_snapshotBound {ι α β Y : Type*} [Fintype ι]
    [DecidableEq α] [Fintype Y] [DecidableEq Y] [Nonempty Y] {m M B_max k_indep : ℕ}
    (hm : 1 ≤ m) (hM : 0 < M) (hB_max : 0 < B_max) {h : ι → α → Y}
    (hh : IsKWiseIndependentHash k_indep h) (hk : 2 * m * (M * M) ≤ k_indep)
    (probe : (α → Y) → α → ℕ → Fin M) (assign : (α → Y) → List (Op α) → SlotAssignment α M)
    (bound : (α → Y) → Finset α → α → ℕ) (hbound_le : ∀ f S x, bound f S x ≤ B_max)
    (hbound_congr : ∀ {f₁ f₂ : α → Y} {S : Finset α} {x : α},
      (∀ a ∈ insert x S, f₁ a = f₂ a) → bound f₁ S x = bound f₂ S x)
    (hpres : ∀ f {l}, ValidOpSeq M l → (assign f l).present = activeSet l)
    (hdom : ∀ f {l} (hl : ValidOpSeq M l) {x} (hx : x ∈ activeSet l),
      ballProbeComplexity (probe f) (assign f l) x ≤
        bound f (activeSet (exists_split_last_insert_of_mem_activeSet hl hx).choose) x)
    (R : Finset β) (ops : β → List (Op α)) (hval : ∀ b ∈ R, ValidOpSeq M (ops b))
    (hdisj : (R : Set β).Pairwise fun b₁ b₂ => Disjoint (opsBalls (ops b₁)) (opsBalls (ops b₂)))
    {c μ Δ : ℝ} (hexp : ∀ {S : Finset α}, #S ≤ M → ∀ {x : α}, x ∉ S →
      𝔼 θ, (bound (h θ) S x : ℝ) ≤ c)
    (hμ : c * (∑ b ∈ R, (#(activeSet (ops b)) : ℝ)) ≤ μ)
    (hmμ : 2 * (m : ℝ) * (M : ℝ) * B_max ≤ 3 * μ) (hΔ : 0 < Δ) :
    (dens {θ : ι | μ + Δ ≤ ∑ b ∈ R,
      (totalProbeComplexity (probe (h θ)) (assign (h θ) (ops b)) : ℝ)} : ℝ) ≤
      2 * (3 * (m : ℝ) * (M : ℝ) * B_max * μ / Δ ^ 2) ^ m := by
  classical
  let y₀ : Y := Classical.arbitrary Y
  let M_cap : ℝ := (M : ℝ) * B_max
  have hM_pos : 0 < M_cap := by positivity
  let preOf (b : β) (hb : b ∈ R) (x : activeSet (ops b)) : List (Op α) :=
    (exists_split_last_insert_of_mem_activeSet (hval b hb) x.2).choose
  let B (b : β) : Finset α := if hb : b ∈ R then
    (activeSet (ops b)).attach.biUnion fun x => insert x.1 (activeSet (preOf b hb x)) else ∅
  have hB_sub (b : β) (hb : b ∈ R) : B b ⊆ opsBalls (ops b) := by
    simp only [B, hb, ↓reduceDIte]; refine Finset.biUnion_subset.mpr fun x _ a ha => ?_
    obtain ⟨_, heq, _, _, _, _⟩ :=
      (exists_split_last_insert_of_mem_activeSet (hval b hb) x.2).choose_spec
    rcases Finset.mem_insert.mp ha with rfl | ha_pre
    · exact activeSet_subset_opsBalls (ops b) x.2
    · rw [heq, opsBalls_append]; exact Finset.mem_union_left _ (activeSet_subset_opsBalls _ ha_pre)
  have hB_card (b : β) (hb : b ∈ R) : #(B b) ≤ M * M := by
    simp only [B, hb, ↓reduceDIte]
    refine Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (g := fun _ => M) fun x _ => ?_).trans ?_)
    · obtain ⟨_, _, _, _, hlt_pre, _⟩ :=
        (exists_split_last_insert_of_mem_activeSet (hval b hb) x.2).choose_spec
      exact (Finset.card_insert_le _ _).trans hlt_pre
    · rw [Finset.sum_const, Finset.card_attach, smul_eq_mul]
      exact Nat.mul_le_mul_right M (card_activeSet_le (hval b hb))
  let extHash {U : Finset α} (u : U → Y) (a : α) : Y := if ha : a ∈ U then u ⟨a, ha⟩ else y₀
  let score (b : β) (u : B b → Y) : ℝ := if hb : b ∈ R then
    (∑ x ∈ (activeSet (ops b)).attach, (bound (extHash u) (activeSet (preOf b hb x)) x.1 : ℝ)) /
      M_cap else 0
  have hscore_Icc (b : β) (hb : b ∈ R) (u) : score b u ∈ Set.Icc 0 1 := by
    simp only [score, hb, ↓reduceDIte]; refine ⟨by positivity, (div_le_one hM_pos).mpr ?_⟩
    refine (Finset.sum_le_sum (g := fun _ => (B_max : ℝ)) fun _ _ => by
      exact_mod_cast hbound_le _ _ _).trans ?_
    rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_activeSet_le (hval b hb)) (by positivity)
  have hscore_restrict (b : β) (hb : b ∈ R) (θ : ι) : score b ((B b).restrict (h θ)) =
      (∑ x ∈ (activeSet (ops b)).attach,
        (bound (h θ) (activeSet (preOf b hb x)) x.1 : ℝ)) / M_cap := by
    simp only [score, hb, ↓reduceDIte]; congr 1; refine Finset.sum_congr rfl fun x hx => ?_
    have hsub : insert x.1 (activeSet (preOf b hb x)) ⊆ B b := by
      simp only [B, hb, ↓reduceDIte]; exact Finset.subset_biUnion_of_mem
        (fun x : activeSet (ops b) => insert x.1 (activeSet (preOf b hb x))) hx
    exact_mod_cast hbound_congr fun a ha => by simp [extHash, hsub ha, Finset.restrict]
  have hdom_tree (b : β) (hb : b ∈ R) (θ : ι) :
      (totalProbeComplexity (probe (h θ)) (assign (h θ) (ops b)) : ℝ) ≤
      M_cap * score b ((B b).restrict (h θ)) := by
    rw [hscore_restrict b hb θ, mul_div_cancel₀ _ hM_pos.ne', totalProbeComplexity_eq_sum_present,
      hpres (h θ) (hval b hb)]
    push_cast; rw [← Finset.sum_attach (activeSet (ops b))]
    exact Finset.sum_le_sum fun x _ => by exact_mod_cast hdom (h θ) (hval b hb) x.2
  have hmean_score : ∑ b ∈ R, (𝔼 θ, score b ((B b).restrict (h θ))) ≤ μ / M_cap := by
    rw [le_div_iff₀ hM_pos, Finset.sum_mul]
    calc ∑ b ∈ R, (𝔼 θ, score b ((B b).restrict (h θ))) * M_cap
        ≤ ∑ b ∈ R, c * (#(activeSet (ops b)) : ℝ) := Finset.sum_le_sum fun b hb => by
          rw [Finset.expect_mul, Finset.expect_congr rfl fun θ _ => by
            rw [hscore_restrict b hb θ, div_mul_cancel₀ _ hM_pos.ne'], Finset.expect_sum_comm]
          calc ∑ x ∈ (activeSet (ops b)).attach, 𝔼 θ, (bound (h θ) _ x.1 : ℝ)
              ≤ ∑ _ ∈ (activeSet (ops b)).attach, c := Finset.sum_le_sum fun x _ => by
                obtain ⟨_, _, _, hx_pre, hlt_pre, _⟩ :=
                  (exists_split_last_insert_of_mem_activeSet (hval b hb) x.2).choose_spec
                exact hexp hlt_pre.le hx_pre
            _ = c * (#(activeSet (ops b)) : ℝ) := by
                rw [Finset.sum_const, Finset.card_attach, nsmul_eq_mul]; ring
      _ = c * ∑ b ∈ R, (#(activeSet (ops b)) : ℝ) := (Finset.mul_sum _ _ _).symm
      _ ≤ μ := hμ
  have hmμ' : 2 * (m : ℝ) ≤ 3 * (μ / M_cap) := by
    rw [← mul_div_assoc, le_div_iff₀ hM_pos]; dsimp only [M_cap]; linarith
  have hconc := dens_abs_sum_restrict_sub_expect_le hm hh hk R B hB_card
    (fun b₁ hb₁ b₂ hb₂ hne => (hdisj hb₁ hb₂ hne).mono (hB_sub b₁ hb₁) (hB_sub b₂ hb₂))
    score hscore_Icc hmean_score hmμ' (div_pos hΔ hM_pos)
  have hsub_ev : ({θ : ι | μ + Δ ≤ ∑ b ∈ R,
      (totalProbeComplexity (probe (h θ)) (assign (h θ) (ops b)) : ℝ)} : Finset ι) ⊆
      ({θ : ι | Δ / M_cap ≤ |∑ b ∈ R,
        (score b ((B b).restrict (h θ)) - 𝔼 θ', score b ((B b).restrict (h θ')))|} : Finset ι) := by
    intro θ hθ; rw [Finset.mem_filter] at hθ ⊢; refine ⟨Finset.mem_univ _, ?_⟩
    have hd := hθ.2.trans ((Finset.sum_le_sum fun b hb => hdom_tree b hb θ).trans_eq
      (Finset.mul_sum _ _ _).symm)
    have hdiv : μ / M_cap + Δ / M_cap ≤ ∑ b ∈ R, score b ((B b).restrict (h θ)) := by
      rw [← add_div, div_le_iff₀ hM_pos]; linarith
    rw [Finset.sum_sub_distrib]; exact (by linarith : Δ / M_cap ≤ _).trans (le_abs_self _)
  refine (show (dens _ : ℝ) ≤ dens _ by exact_mod_cast Finset.dens_le_dens hsub_ev).trans
    (hconc.trans_eq ?_)
  congr 2; dsimp only [M_cap]; field_simp [hM_pos.ne']

end Probability

end Cslib.DataStructure.BallsToSlots
