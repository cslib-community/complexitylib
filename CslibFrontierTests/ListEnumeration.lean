/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Foundations.Data.List.Equiv

/-! Ordered occurrences survive products, noninjective maps, appends and reindexing. -/

namespace ComplexityTests.ListEnumeration

private def reversedBits : List.Enumeration [true, false] (id : Bool → Bool) :=
  .ofNodup _ (by decide) (by intro b; cases b <;> simp)

private def repeated : List.Enumeration [0, 0, 1, 1]
    (fun p : Fin 2 × Bool => p.1.val) :=
  ((List.Enumeration.range 2).prod reversedBits).map Prod.fst

example : List.ofFn (fun i : Fin 4 => repeated.equiv i) =
    [(0, true), (0, false), (1, true), (1, false)] := by decide

example (i : Fin 4) : [0, 0, 1, 1].get i = (repeated.equiv i).1.val :=
  repeated.get_eq i

example : repeated.equiv 0 ≠ repeated.equiv 1 := by decide

example : List.ofFn (fun i : Fin 4 =>
    (repeated.reindex (Equiv.prodComm _ _)).equiv i) =
      [(true, 0), (false, 0), (true, 1), (false, 1)] := by decide

private def appended : List.Enumeration [7, 7] (Sum.elim (fun _ : Unit => 7) (fun _ : Unit => 7)) :=
  (List.Enumeration.singleton 7).append (List.Enumeration.singleton 7)

example : appended.equiv 0 = Sum.inl () := by decide
example : appended.equiv 1 = Sum.inr () := by decide
example : [7, 7].get 0 = [7, 7].get 1 := rfl
example : appended.equiv 0 ≠ appended.equiv 1 := by decide

-- Both empty factors and either empty summand work without nonemptiness assumptions.
example : List.Enumeration ([] : List (ℕ × Bool))
    (fun p : Fin 0 × Bool => (p.1.val, p.2)) :=
  (List.Enumeration.range 0).prod reversedBits

example : List.Enumeration ([] : List (Bool × ℕ))
    (fun p : Bool × Fin 0 => (p.1, p.2.val)) :=
  reversedBits.prod (List.Enumeration.range 0)

example : ((List.Enumeration.range 0).append (List.Enumeration.singleton 9)).equiv ⟨0, by decide⟩ =
    Sum.inr () := by decide

example : ((List.Enumeration.singleton 9).append (List.Enumeration.range 0)).equiv ⟨0, by decide⟩ =
    Sum.inl () := by decide

end ComplexityTests.ListEnumeration
