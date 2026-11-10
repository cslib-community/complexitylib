/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.PolyTime.CNF.VCOneFrontend
public import CslibFrontierTests.PaperEndpoints.VCOne
meta import CslibFrontier.Computability.PolyTime.CNF.VCOneFrontend
meta import CslibFrontier.Computability.PolyTime.CNF.VCOneSeparator
meta import CslibFrontier.Computability.PolyTime.CNF.VCOneClosure
meta import CslibFrontierTests.PaperEndpoints.VCOne

/-! # Actual resource-certified table constructors and overlapping scopes

Small exhaustive checks are test oracles only. The 32-coordinate constructor does not enumerate
its cube. The non-VC-one input demonstrates that the explicit cap has a material promise.
-/

public section

open Cslib.Logic.PL Cslib.Logic.PL.VCOne
open Turing.MultiTapeTM

set_option linter.hashCommand false

/-- Three explicit one-hot rows, with one unwanted closure tuple. -/
@[expose] def oneRows : BinaryClosure.Input :=
  (3, [[false, false, true], [false, true, false], [true, false, false]])

/-- info: [[0, 0, 0], [0, 0, 1], [0, 1, 0], [1, 0, 0]] -/
#guard_msgs in
#eval (BinaryClosure.enumerate oneRows).map (List.map Bool.toNat)

/-- info: ([[false, false, false]], [[(0, true), (1, true), (2, true)]], 12) -/
#guard_msgs in
#eval (BinaryClosure.missing oneRows, BinarySeparator.equations oneRows,
  (BinaryFrontend.side oneRows).length)

/- Empty tables reject even at width zero; a nonempty zero-width relation is a tautology. -/
/-- info: ([], [[]], [], []) -/
#guard_msgs in
#eval (BinaryClosure.enumerate (0, []), BinaryFrontend.side (0, []),
  BinaryFrontend.side (0, [[]]), BinarySeparator.equations (0, [[]]))

/- A wide explicit relation with no unwanted closure points. -/
/-- info: (2, 0) -/
#guard_msgs in
#eval (BinaryClosure.enumerate (32, [List.replicate 32 false, List.replicate 32 true]) |>.length,
  BinarySeparator.equations (32, [List.replicate 32 false, List.replicate 32 true]) |>.length)

/- Outside VC-one, the capped output has three rather than four rows. -/
/-- info: 3 -/
#guard_msgs in
#eval (BinaryClosure.enumerate (2, [[false, false], [false, true],
  [true, false], [true, true]])).length

/- Overlaps have opposite signs on common columns, and the fifth global bit is unused. -/
/-- info: ([[0, 1, 2], [1, 2, 3]], [[true, true, true], [false, false, false]], true) -/
#guard_msgs in
#eval let p := tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable
      let es := (BinaryFrontend.payload p).2
      (es.map (List.map Prod.fst), es.map (List.map Prod.snd), BinaryFrontend.consistent p)

/- A width-zero empty table creates an actual empty side clause, with no invented scope bits. -/
/-- info: ([[]], [], true) -/
#guard_msgs in
#eval let p := (5, [(0, ([] : List (List Bool)), ([] : List ℕ))])
      let (side, es) := BinaryFrontend.payload p
      (side, es, BinaryFrontend.consistent p)

/- The actual derived equations satisfy exact-one iff the original overlapping tables do.
All 32 assignments are considered here, including both values of the unused bit. -/
/-- info: 4 -/
#guard_msgs in
#eval let p := BinaryFrontend.payload (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)
      (Finset.univ.filter fun x : Fin 5 → Bool =>
        let σ := fun i => (List.ofFn x).getD i false
        p.1.eval σ && p.2.evalOne σ).card

example : ComputableInPolyTime BinaryClosure.enumerate BinaryClosure.encInput
    (encList encBits) := BinaryClosure.enumerate_polytime

example : ComputableInPolyTime BinaryFrontend.consistent encTablePayload encBool :=
  BinaryFrontend.consistent_polytime

/-- Source correspondence applies to the actual row relation, not an output/rank hypothesis. -/
example : (BinaryClosure.enumerate (3, BinaryClosure.rows (oneTable true))).toFinset =
    (closure (oneTable true)).image List.ofFn :=
  BinaryClosure.enumerate_rows _ (oneTable_dimension true)

example : (BinarySeparator.equations (3, BinaryClosure.rows (oneTable true))).length ≤ 1 := by
  have h := BinarySeparator.equations_length _ (oneTable_dimension true)
  have hc : (oneTable true).card = 3 := by decide +kernel
  simpa only [hc] using h

/-- Global side budget depends on declared columns, rather than number/overlap of tables. -/
example : (BinaryFrontend.payload
    (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)).1.length ≤ 111 := by
  simpa using BinaryFrontend.payload_side_length
    (fun _ : Fin 2 => 3) overlapScope overlapTable

/-- Full pointwise relation equivalence for the overlapping original table payload. -/
example (σ : ℕ → Bool) :
    (∀ i : Fin 2, (fun j => σ (overlapScope i j).val) ∈ overlapTable i) ↔
      (BinaryFrontend.payload
        (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)).1.eval σ =
        true ∧ (BinaryFrontend.payload
          (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)).2.evalOne σ = true :=
  BinaryFrontend.payload_tables _ _ _ (fun i => oneTable_dimension (i == 0)) σ

/- Opposite equations on the identical scope are inconsistent; overlap alone is permitted. -/
/-- info: (false, 1) -/
#guard_msgs in
#eval let p := (3, [(3, oneRows.2, [0, 1, 2]),
        (3, oneRows.2.map (List.map Bool.not), [0, 1, 2])])
      (BinaryFrontend.consistent p, (BinaryFrontend.basis p).length)

example : ComputableInPolyTime BinaryFrontend.basis encTablePayload (encList encUnary) :=
  BinaryFrontend.basis_polytime

open Classical in
/-- Exact cardinal transfer keeps all five declared bits in the actual compiled payload. -/
example : Fintype.card {x : Fin 5 → Bool // Satisfies (fun _ : Fin 2 => 3)
      overlapScope overlapTable x} =
    Fintype.card {x : Fin 5 → Bool //
      let σ := Function.extend Fin.val x (fun _ => false)
      (BinaryFrontend.payload
        (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)).1.eval σ = true ∧
      (BinaryFrontend.payload
        (tablePayload (fun _ : Fin 2 => 3) overlapScope overlapTable)).2.evalOne σ = true} :=
  BinaryFrontend.payload_count _ _ _ (fun i => oneTable_dimension (i == 0))
