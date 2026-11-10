/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.PolyTime.Rational.RowSelection
import Mathlib.Tactic.NormNum
meta import CslibFrontier.Computability.PolyTime.Rational.RowSelection

/-!
# Actual binary rational original-row selection

Execute admission, denominator compilation, Gram consistency/selection and original-index
output. Tiny Boolean enumeration is only an independent test oracle; the production selector
uses no assignment enumeration or rational normalization.
-/

public section

namespace RationalRowSelectionTests

open Cslib.LinearSystem RationalFrontend Turing.MultiTapeTM Matrix

set_option linter.hashCommand false

/-- Three original rational equations, the second redundant, with unique solution (1,1). -/
@[expose] def exampleSystem : Input :=
  (2, [[(1, 2), (1, 3), (5, 6)], [(1, 1), (2, 3), (5, 3)], [(0, 1), (1, 7), (1, 7)]])
/-- Equal rational coefficients but unequal right-hand sides; neither row can be discarded. -/
@[expose] def contradiction : Input := (1, [[(1, 2), (1, 1)], [(2, 4), (2, 1)]])

/-- info: (some [2, 0], true, some [1, 0], false, some [0], true) -/
#guard_msgs in
#eval (select exampleSystem, consistent exampleSystem,
  select contradiction, consistent contradiction,
  select (1, [[(-2, -4), (-3, -3)], [(3, 6), (4, 4)]]),
  admit (1, [[(-2, -4), (-3, -3)], [(3, 6), (4, 4)]]))

/- Zero-width contradictions retain their one original row; absent entries are valid zeroes. -/
/-- info: (some [], some [], some [0], none, some [], some []) -/
#guard_msgs in
#eval (select (40, []), select (0, [[(0, 7)]]), select (0, [[(1, 2)]]),
  select (1, [[(1, 0), (1, 1)]]), select (2, [[]]),
  select (1, [[(0, 1), (0, 1), (7, 0)]]))

/- Large coefficients/denominators are binary and unreduced, not unary occurrences. -/
/-- info: (some [0], some [0], true) -/
#guard_msgs in
#eval (select (1, [[(2 ^ 128, 2 ^ 128), (1, 1)]]),
  select (1, [[(1, 2 ^ 128), (1, 2 ^ 128)]]),
  admit (1, [[(1, -(2 ^ 128)), (1, -(2 ^ 128))]]))

/-- Test-only rational interpretation of one original equation on an original Boolean word. -/
@[expose] def rowTest (x : Input) (seed i : ℕ) : Bool :=
  ((List.range (width x)).map fun j =>
    let p := entry x i j
    ((p.1 : ℚ) / (p.2 : ℚ)) * if Nat.testBit seed j then 1 else 0).sum ==
      let p := entry x i (width x)
      (p.1 : ℚ) / (p.2 : ℚ)
/-- Tiny independent original-assignment oracle, before row selection. -/
@[expose] def originalCount (x : Input) : ℕ :=
  (List.range (2 ^ width x)).countP fun seed =>
    (List.range (rows x).length).all (rowTest x seed)
/-- Same tiny words after the actual row selector; production never enumerates these words. -/
@[expose] def selectedCount (x : Input) : ℕ :=
  match select x with
  | none => 0
  | some ids => (List.range (2 ^ width x)).countP fun seed => ids.all (rowTest x seed)

/-- info: (1, 1, 0, 0, 4, 4) -/
#guard_msgs in
#eval (originalCount exampleSystem, selectedCount exampleSystem,
  originalCount contradiction, selectedCount contradiction,
  originalCount (2, [[]]), selectedCount (2, [[]]))

/- Genuine negative coefficients/RHS and a negative common denominator; cancellation is exact. -/
/-- info: (some [0], 0, 0, 2, 2) -/
#guard_msgs in
#eval (select (1, [[(1, -2), (1, 1)]]),
  originalCount (1, [[(1, 2), (-1, 1)]]), selectedCount (1, [[(1, -2), (1, 1)]]),
  originalCount (2, [[(1, 2), (-1, 2), (0, 1)]]),
  selectedCount (2, [[(1, 2), (-1, 2), (0, 1)]]))

/- All 36 ordered two-row systems over genuine fractional coefficient/RHS choices. -/
/-- info: true -/
#guard_msgs in
#eval let rs : List (List Fraction) :=
    [(0, 1), (1, 2), (-1, 3)].flatMap fun a => [(0, 1), (1, 2)].map fun b => [a, b]
  rs.all fun a => rs.all fun b =>
    let x : Input := (1, [a, b])
    originalCount x == selectedCount x && (basis x).length ≤ 2 &&
      (basis x).all (fun i => i < 2)

/- A formal contradiction client uses the general selected/original equivalence. -/
example (y : Fin 0 → ℚ) :
    ¬ ∀ i ∈ basis (0, [[(1, 2)]]), Satisfies (0, [[(1, 2)]]) y i := by
  intro h
  have hh := (basis_selected_iff (0, [[(1, 2)]]) (by decide) y).mp h
  have h0 := hh ⟨0, by decide⟩
  norm_num [Satisfies, coefficientRow, rightHandSide, rationalRow, entry, rows, width,
    dotProduct] at h0

/- Declared unused bits retain all original Boolean assignments, without enumerating 2^40 words. -/
open Classical in
example : Fintype.card {z : Fin 40 → Bool //
    ∀ i ∈ basis (40, []), Satisfies (40, []) (fun j => if z j then 1 else 0) i} = 2 ^ 40 := by
  have hb : basis (40, []) = [] := by decide
  simp [hb]

/- The canonical arbitrary-rational matrix interface gives the sharper consistent row bound. -/
example {m n : ℕ} (A : Fin m → Fin n → ℚ) (b : Fin m → ℚ)
    (hc : ∃ y : Fin n → ℚ, ∀ i, A i ⬝ᵥ y = b i) :
    ∃ ids, select (ofData A b) = some ids ∧ ids.length ≤ n ∧
      ∀ y : Fin n → ℚ, (∀ i : Fin m, i.val ∈ ids → A i ⬝ᵥ y = b i) ↔ ∀ i, A i ⬝ᵥ y = b i := by
  obtain ⟨ids, hs, _, _, he, hr⟩ := select_ofData A b
  refine ⟨ids, hs, ?_, he⟩
  rw [hr hc]
  simpa using (Submodule.finrank_le (Submodule.span ℚ (Set.range A)))

end RationalRowSelectionTests
