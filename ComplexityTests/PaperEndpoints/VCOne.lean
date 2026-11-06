/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.VCOneTables
meta import Complexity.Logics.Propositional.CNF.VCOneTables
meta import Complexity.Logics.Propositional.CNF.VCOne
meta import Mathlib.Data.Fintype.Basic
meta import Mathlib.Data.Fintype.Card
meta import Mathlib.Data.Finset.Empty
import Mathlib.Tactic.FinCases

/-! Actual table inputs, greedy separators, overlapping scopes and degenerate tables. -/

public section

open Cslib.Logic.PL Cslib.Logic.PL.VCOne

/-- The table consists of all tuples with exactly one literal of the chosen sign. -/
@[expose] def oneTable (b : Bool) : Finset (Fin 3 → Bool) :=
  Finset.univ.filter fun x => ExactOne.Holds Finset.univ (fun _ => b) x

/-- No coordinate pair realizes the pattern with two true signed literals. -/
theorem oneTable_dimension (b : Bool) : DimensionOne (oneTable b) := by
  apply dimensionOne_of_missing
  intro i j hij
  refine ⟨b, b, fun x hx h => ?_⟩
  obtain ⟨k, _, _, hu⟩ := (Finset.mem_filter.mp hx).2
  exact hij ((hu i (Finset.mem_univ _) h.1).trans (hu j (Finset.mem_univ _) h.2).symm)

/-- This table has three distinct rows. -/
example : (oneTable true).card = 3 := by decide +kernel

/-- Zero is a genuine missing table tuple. -/
example : (fun _ : Fin 3 => false) ∉ oneTable true := by decide +kernel

/-- Every unary/binary projection of zero occurs in the table. -/
theorem zero_in_closure : (fun _ : Fin 3 => false) ∈ closure (oneTable true) := by
  rw [mem_closure]
  decide +kernel

/-- The concrete greedy algorithm selects all three coordinates. -/
example : greedyScope (oneTable true) (fun _ => false) = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have h := (greedy_separator (oneTable true) (oneTable_dimension true)
    (fun _ => false) zero_in_closure (by decide +kernel)).1
  simpa using h

/-- Exactly one unwanted closure point produces exactly one equation. -/
example : (closure (oneTable true) \ oneTable true).card = 1 := by
  have hcard : (oneTable true).card = 3 := by decide +kernel
  have he : insert (fun _ : Fin 3 => false) (oneTable true) = closure (oneTable true) := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset zero_in_closure (subset_closure _)
    · have hc := card_le _ (dimensionOne_closure _ (oneTable_dimension true))
      simpa [Finset.card_insert_of_notMem (show (fun _ : Fin 3 => false) ∉ oneTable true by
        decide +kernel), hcard] using hc
  rw [Finset.card_sdiff_of_subset (subset_closure _), ← he,
    Finset.card_insert_of_notMem (show (fun _ : Fin 3 => false) ∉ oneTable true by
      decide +kernel), hcard]

/-- The actual greedy scope, without a supplied separator, represents this table. -/
example : 3 ≤ (greedyScope (oneTable true) (fun _ => false)).card ∧
    (∀ x ∈ oneTable true, ExactOne.Holds
      (greedyScope (oneTable true) (fun _ => false)) (fun _ => true) x) ∧
    ¬ ExactOne.Holds (greedyScope (oneTable true) (fun _ => false))
      (fun _ => true) (fun _ => false) := by
  simpa using greedy_separator (oneTable true) (oneTable_dimension true)
    (fun _ => false) zero_in_closure (by decide +kernel)

/-- Each tuple is characterized pointwise, with no auxiliary extensions. -/
example (x : Fin 3 → Bool) : x ∈ oneTable true ↔
    (binary (oneTable true)).eval x = true ∧
      ∀ y : ↥(closure (oneTable true) \ oneTable true),
        ExactOne.Holds (separatorScope (oneTable true) y) (fun i => !(y.val i)) x :=
  representation_iff _ (oneTable_dimension true) x

/-- Offset scopes overlap on two global columns; column four is declared but unused. -/
@[expose] def overlapScope (t : Fin 2) : Fin 3 ↪ Fin 5 :=
  ⟨fun i => ⟨i.val + t.val, by omega⟩, fun i j h => by
    apply Fin.ext
    have he := congrArg Fin.val h
    dsimp at he
    omega⟩

/-- The second table has the opposite polarity on the overlapping coordinates. -/
@[expose] def overlapTable (t : Fin 2) := oneTable (t == 0)

/-- The global source has four solutions, including both values of the unused bit. -/
example : Fintype.card {x : Fin 5 → Bool //
    ∀ t : Fin 2, x ∘ overlapScope t ∈ overlapTable t} = 4 := by decide +kernel

open scoped Classical in
/-- The all-cases reduction derives the same global budget from these actual tables. -/
example : ∃ k : ℕ, ∃ Q : Bool → CNF (Fin 5 ⊕ Fin k),
    Fintype.card {x : Fin 5 → Bool // Satisfies (fun _ : Fin 2 => 3)
      overlapScope overlapTable x} =
      Fintype.card {x : Fin 5 ⊕ Fin k → Bool // (Q false).eval x = true} -
      Fintype.card {x : Fin 5 ⊕ Fin k → Bool // (Q true).eval x = true} ∧
    (∀ β c, c ∈ Q β → c.length ≤ 3) ∧
    (∀ β, (Q β).length ≤ 13 * Fintype.card (Fin 5) ^ 2) ∧
    Fintype.card (Fin 5 ⊕ Fin k) ≤ 2 * Fintype.card (Fin 5) - 2 :=
  tables_queries (fun _ => 3) overlapScope overlapTable
    (fun t => oneTable_dimension (t == 0)) (by decide)

/-- Width zero has exactly one possible tuple; its nonempty table is a tautology. -/
example (x : Fin 0 → Bool) : x ∈ (Finset.univ : Finset (Fin 0 → Bool)) := Finset.mem_univ _

/-- Empty tables have no closure points, on zero coordinates too. -/
example : closure (∅ : Finset (Fin 0 → Bool)) = ∅ := by
  ext x
  simp only [mem_closure, Finset.notMem_empty, iff_false]
  intro h
  obtain ⟨y, hy, _⟩ := h ∅ (by simp)
  exact hy

/-- Repeated rows in a listed singleton table are identified, not counted twice. -/
example : ([fun _ : Fin 2 => false, fun _ : Fin 2 => false].toFinset).card = 1 := by
  decide +kernel

/-- Constant coordinates in a singleton table remain fixed. -/
example (x : Fin 2 → Bool) : x ∈ closure {fun _ => false} ↔ x = fun _ => false := by
  rw [mem_closure]
  constructor
  · intro h
    funext i
    obtain ⟨y, hy, he⟩ := h {i} (by simp)
    have hy' : y = fun _ => false := Finset.mem_singleton.mp hy
    simpa [hy'] using (@he i (by simp)).symm
  · intro he
    subst x
    exact fun _ _ => ⟨_, Finset.mem_singleton_self _, fun _ _ => rfl⟩

/-- The full two-bit cube fails the promise, so it is not accepted vacuously. -/
example : ¬ DimensionOne (Finset.univ : Finset (Fin 2 → Bool)) := by
  intro h
  have hc := card_le _ h
  norm_num at hc

open scoped Classical in
/-- The direct small-instance branch is also available on zero global bits. -/
example (w : Fin 0 → ℕ) (scope : (i : Fin 0) → Fin (w i) ↪ Fin 0)
    (R : (i : Fin 0) → Finset (Fin (w i) → Bool)) :
    directCount w scope R = Fintype.card {x : Fin 0 → Bool // Satisfies w scope R x} ∧
      directCount w scope R ≤ 2 :=
  ⟨directCount_correct w scope R, directCount_small w scope R (by decide)⟩

-- Runtime regression checks intentionally execute the listing and compiler;
-- they supplement the kernel-checked correctness and frontier-size theorems.
set_option linter.hashCommand false

/-- A 32-coordinate input with only two listed rows. This exercises the listing
without even constructing the set of all `2^32` tuples. -/
@[expose] def wideTwoRows : Finset (Fin 32 → Bool) := {fun _ => false, fun _ => true}

/- Executed listing retains the two constant rows. -/
/-- info: 2 -/
#guard_msgs in
#eval (listedClosure wideTwoRows).card

/- The traversal really attempts 126 one-bit extensions on this input. -/
/-- info: 126 -/
#guard_msgs in
#eval prefixCandidates wideTwoRows (List.finRange 32)

/-- The table's missing pair patterns establish its VC promise. -/
theorem wideTwoRows_dimension : DimensionOne wideTwoRows := by
  apply dimensionOne_of_missing
  intro i j _
  refine ⟨false, true, fun x hx he => ?_⟩
  rcases Finset.mem_insert.mp hx with rfl | hx
  · simp at he
  · have hx := Finset.mem_singleton.mp hx
    subst x
    simp at he

/-- The proved traversal bound applies to a 32-coordinate input. -/
example : prefixCandidates wideTwoRows (List.finRange 32) ≤ 2 * 32 * 33 := by
  simpa using prefixCandidates_le wideTwoRows wideTwoRows_dimension
    (List.finRange 32) (List.nodup_finRange 32)

/-- The same executable listing agrees with the semantic closure. -/
example : listedClosure (oneTable true) = closure (oneTable true) := listedClosure_eq _

/- Empty and nonempty zero-width inputs keep their distinct meanings. -/
/-- info: (0, 1) -/
#guard_msgs in
#eval ((listedClosure (∅ : Finset (Fin 0 → Bool))).card,
  (listedClosure ({fun _ => false} : Finset (Fin 0 → Bool))).card)

/- Enumeration of the actual global equation index uses the listed closure. -/
/-- info: 1 -/
#guard_msgs in
#eval Fintype.card (EquationIndex (fun _ : Fin 1 => 3) (fun _ => oneTable true))

/- The executed overlapping compilation derives scopes, not supplied equations. -/
/-- info: {3} -/
#guard_msgs in
#eval (Finset.univ : Finset (EquationIndex (fun _ : Fin 2 => 3) overlapTable)).image
  fun j => (tableScope (fun _ => 3) overlapScope overlapTable j).card

/- Opposite local signs survive the shared-column lookup; unused bits default false. -/
/-- info: {(true, false), (false, false)} -/
#guard_msgs in
#eval (Finset.univ : Finset (EquationIndex (fun _ : Fin 2 => 3) overlapTable)).image
  fun j => (tablePolarity (fun _ => 3) overlapScope overlapTable j 1,
    tablePolarity (fun _ => 3) overlapScope overlapTable j 4)

end
