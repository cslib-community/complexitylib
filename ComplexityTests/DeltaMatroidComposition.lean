/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: local-only (tests of local candidate modules)

import Complexity.Logics.Propositional.CSP.Table.DeltaMatroid

/-! Checked clients for compatible composition and the actual guarded table contraction.
These tests assert local closure, not the edge solver or the full planar dichotomy. -/

open Cslib Cslib.BitString Cslib.Logic.PL.CSP

namespace DeltaMatroidCompositionTests

-- Compatible singleton inputs, with an explicit common-coordinate witness.
example : IsEvenDeltaMatroid
    (comp ({fun _ : Unit ⊕ Unit => true} : Set ((Unit ⊕ Unit) → Bool))
      ({fun _ : Unit ⊕ Unit => true} : Set ((Unit ⊕ Unit) → Bool))) := by
  apply (isEvenDeltaMatroid_singleton _).comp (isEvenDeltaMatroid_singleton _)
  refine ⟨fun _ => true, fun _ => true, ?_, ?_⟩ <;>
    apply Set.mem_singleton_iff.mpr <;> ext (i | i) <;> rfl

-- The general closure theorem also permits non-even inputs with single-coordinate exchange.
example : IsDeltaMatroid (comp (Set.univ : Set ((Unit ⊕ Unit) → Bool))
    (Set.univ : Set ((Unit ⊕ Unit) → Bool))) := by
  apply isDeltaMatroid_univ.comp isDeltaMatroid_univ
  exact ⟨fun _ => false, fun _ => false, Set.mem_univ _, Set.mem_univ _⟩

-- Nonempty inputs can be incompatible. The generic nonempty-output premise matters.
example : comp ({fun _ : Unit ⊕ Unit => false} : Set ((Unit ⊕ Unit) → Bool))
    ({fun _ : Unit ⊕ Unit => true} : Set ((Unit ⊕ Unit) → Bool)) = ∅ := by
  ext x
  constructor
  · rintro ⟨z, hz, hw⟩
    have hzero := congrFun (Set.mem_singleton_iff.mp hz) (.inr ())
    have hone := congrFun (Set.mem_singleton_iff.mp hw) (.inl ())
    simp_all
  · simp

-- Empty external and shared coordinate sets are permitted when there is a witness.
example : IsEvenDeltaMatroid
    (comp ({fun _ : Empty ⊕ Empty => false} : Set ((Empty ⊕ Empty) → Bool))
      ({fun _ : Empty ⊕ Empty => false} : Set ((Empty ⊕ Empty) → Bool))) := by
  apply (isEvenDeltaMatroid_singleton _).comp (isEvenDeltaMatroid_singleton _)
  refine ⟨fun _ => false, fun _ => false, ?_, ?_⟩ <;>
    apply Set.mem_singleton_iff.mpr <;> ext (i | i) <;> exact i.elim

-- Odd singleton input and no shared coordinates.
example : IsEvenDeltaMatroid
    (comp ({fun _ : Unit ⊕ Empty => true} : Set ((Unit ⊕ Empty) → Bool))
      ({fun _ : Empty ⊕ Empty => false} : Set ((Empty ⊕ Empty) → Bool))) := by
  apply (isEvenDeltaMatroid_singleton _).comp (isEvenDeltaMatroid_singleton _)
  refine ⟨Sum.elim (fun _ => true) (fun _ => false), fun _ => false, ?_, ?_⟩ <;>
    apply Set.mem_singleton_iff.mpr <;> ext (i | i)
  · rfl
  · exact i.elim
  · exact i.elim
  · exact i.elim

-- The star with no internal ports accepts just the zero connector.
example : (fun _ : Empty ⊕ Unit => false) ∈ star Empty := by
  exact mem_star_iff.mpr (Or.inl ⟨fun i => i.elim, rfl⟩)

-- With an internal port, the star accepts 00 and 11, not the exactly-one rows 01 and 10.
example : (Sum.elim (fun _ : Unit => true) (fun _ : Unit => true)) ∈ star Unit := by
  exact mem_star_iff.mpr (Or.inr ⟨(), fun j => by cases j; rfl, rfl⟩)

example : (Sum.elim (fun _ : Unit => false) (fun _ : Unit => true)) ∉ star Unit := by
  rw [mem_star_iff]
  simp

-- Arbitrary arity, including odd common parity and repeated scope names.
example {V : Type*} (head : V) (tail : List V) :
    IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem (Table.exactlyOne (head :: tail))) :=
  Table.isEvenDeltaMatroid_exactlyOne _ (List.cons_ne_nil _ _)

example : IsEvenDeltaMatroid
    (booleanRelation Table.arity Table.sem (Table.exactlyOne [0, 0, 0])) :=
  Table.isEvenDeltaMatroid_exactlyOne _ (by decide)

example : parityOn Finset.univ (fun _ : Fin 1 => true) = true := by decide

example : ¬ IsDeltaMatroid
    (booleanRelation Table.arity Table.sem (Table.exactlyOne ([] : List Nat))) :=
  Table.not_isDeltaMatroid_exactlyOne_nil

-- This contraction keeps the outside coordinate in order and puts the connector last.
-- Its two output rows are 00 and 11; the two-deviation input is discarded.
example : Table.contract (Table.exactlyOne [0, 1, 2]) [true, false, false] [0, 2] =
    ⟨2, [[false, false], [true, true]]⟩ := by rfl

example : IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem
    (Table.contract (Table.exactlyOne [0, 1, 2]) [true, false, false] [0, 2])) := by
  exact Table.isEvenDeltaMatroid_contract
    (Table.isEvenDeltaMatroid_exactlyOne _ (by decide)) (by decide)

-- A non-increasing internal selection retains both outside coordinates in their original order.
example : Table.contract (Table.exactlyOne [0, 1, 2, 3]) [true, false, false, false] [2, 0] =
    ⟨3, [[false, false, false], [true, false, true], [false, true, true]]⟩ := by rfl

-- Empty internal selection still adds a zero connector, and has a feasible output.
example : IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem
    (Table.contract (Table.exactlyOne [0]) [true] [])) := by
  exact Table.isEvenDeltaMatroid_contract
    (Table.isEvenDeltaMatroid_exactlyOne _ (by decide)) (by decide)

example : (Table.contract (Table.exactlyOne [0]) [true] []).sem [true, false] = true := by
  decide

-- A nonempty nullary table also contracts, yielding a single zero connector.
example : IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem
    (Table.contract ⟨0, [[]]⟩ [] [])) := by
  have hR : IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem ⟨0, [[]]⟩) := by
    convert isEvenDeltaMatroid_singleton (fun _ : Fin 0 => false) using 1
    ext x
    constructor
    · intro _
      apply Set.mem_singleton_iff.mpr
      funext i
      exact i.elim0
    · intro _
      rfl
  exact Table.isEvenDeltaMatroid_contract hR (by decide)

-- Duplicate/out-of-range positions and an infeasible reference reject through the native guard.
example : (Table.exactlyOne [0, 1]).canContract [true, false] [0, 0] = false := by decide
example : Table.contract (Table.exactlyOne [0, 1]) [true, false] [2] = ⟨0, []⟩ := by rfl
example : Table.contract (Table.exactlyOne [0, 1]) [false, false] [0] = ⟨0, []⟩ := by rfl
example : (Table.exactlyOne ([] : List Nat)).canContract [] [] = false := by decide

end DeltaMatroidCompositionTests
