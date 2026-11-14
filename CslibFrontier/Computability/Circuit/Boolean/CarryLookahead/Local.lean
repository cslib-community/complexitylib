/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Circuit.Boolean.EvaluationTime

/-!
# Local decoding of carry-lookahead cells

A query specifies the width, distance, cell number, and whether to read the generate or propagate
component. All numeric parameters are binary. The decoder constructs only the existing two-gate
or one-gate cell, never a row or the complete adder. Consequently its native multitape polynomial
time is measured in the binary parameter lengths, even for exponentially wide rows.

`cellCode_eq` and `eval_cell` connect this local decoder to `CarryLookahead.step`; `cellGate`
selects one gate of the constant-sized block, including a total default for malformed indices.
The initial carry cells have the same local interface.

This does not yet decode a flattened gate number of the complete adder or give a local interface
for its finishing XORs. Cross-layer routing and the alternating evaluator are separate obligations.
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.CarryLookahead

open Turing.MultiTapeTM ComputableInPolyTime

/-- The existing scalar cell: `true` selects generate, `false` selects propagate. -/
def cell (k distance : ℕ) (i : Fin k) (generate : Bool) : Circuit signature (k + k) 1 :=
  if generate then (generateFormula k distance i).toCircuit
  else (propagateFormula k distance i).toCircuit

/-- Decode one scalar cell from binary coordinates; this never materializes the row. -/
def cellCode (k distance i : ℕ) (generate : Bool) : List (Op × List ℕ) × List ℕ :=
  if generate then generateCode k distance i else propagateCode k distance i

/-- On valid coordinates the decoder returns exactly the typed scalar circuit's code. -/
theorem cellCode_eq (k distance : ℕ) (i : Fin k) (generate : Bool) :
    cellCode k distance i.val generate = (cell k distance i generate).code := by
  cases generate <;> simp [cellCode, cell, generateCode_eq, propagateCode_eq]

/-- A local block has at most two gates, independently of the row width and distance. -/
theorem length_cellCode_le (k distance : ℕ) (i : Fin k) (generate : Bool) :
    (cellCode k distance i.val generate).1.length ≤ 2 := by
  rw [cellCode_eq, Circuit.length_code_fst]
  cases generate <;> simp [cell, generateFormula, propagateFormula]

/-- The local output is the selected output of the existing parallel doubling layer. -/
theorem eval_cell (k distance : ℕ) (i : Fin k) (generate : Bool)
    (row : BitString (k + k)) :
    (cell k distance i generate).eval interpretation row 0 =
      (step k distance).eval interpretation row
        (if generate then Fin.castAdd k i else Fin.natAdd k i) := by
  cases generate <;>
    simp only [cell, Bool.false_eq_true, ↓reduceIte, step,
      Circuit.eval_append, Fin.append_left, Fin.append_right, Circuit.eval_pi]

/-- Local cell decoding is polynomial-time in binary widths, distances, and indices. -/
theorem cellCode_polyTime {α : Type} {enc : α ↪ List Bool}
    {k distance i : α → ℕ} {generate : α → Bool}
    (hk : ComputableInPolyTime k enc encNat)
    (hd : ComputableInPolyTime distance enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hg : ComputableInPolyTime generate enc encBool) :
    ComputableInPolyTime (fun a => cellCode (k a) (distance a) (i a) (generate a))
      enc encCode :=
  hg.ite (generateCode_polyTime hk hd hi) (propagateCode_polyTime hk hd hi)

/-- Read one gate of the local block; an unavailable gate is constant false. -/
def cellGate (k distance i : ℕ) (generate : Bool) (gate : ℕ) : Op × List ℕ :=
  (cellCode k distance i generate).1.getD gate (.const false, [])

/-- Local gate lookup charges the binary gate index and never scans a whole row. -/
theorem cellGate_polyTime {α : Type} {enc : α ↪ List Bool}
    {k distance i gate : α → ℕ} {generate : α → Bool}
    (hk : ComputableInPolyTime k enc encNat)
    (hd : ComputableInPolyTime distance enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hg : ComputableInPolyTime generate enc encBool)
    (hj : ComputableInPolyTime gate enc encNat) :
    ComputableInPolyTime (fun a => cellGate (k a) (distance a) (i a) (generate a) (gate a))
      enc encGate :=
  listGetD_binary (encA := encGate) (Op.const false, [])
    (cellCode_polyTime hk hd hi hg).fst' hj

/-- The gate decoder agrees with the existing scalar circuit, including out-of-range defaults. -/
theorem cellGate_eq (k distance : ℕ) (i : Fin k) (generate : Bool) (gate : ℕ) :
    cellGate k distance i.val generate gate =
      (cell k distance i generate).code.1.getD gate (.const false, []) := by
  rw [cellGate, cellCode_eq]

/-- Decode one initial carry cell; `true` selects generate, `false` selects propagate. -/
def initialCellCode (w i : ℕ) (generate : Bool) : List (Op × List ℕ) × List ℕ :=
  if generate then initialGenerateCode w i else initialPropagateCode w i

/-- Initial cell decoding is also polynomial-time in binary parameters. -/
theorem initialCellCode_polyTime {α : Type} {enc : α ↪ List Bool}
    {w i : α → ℕ} {generate : α → Bool}
    (hw : ComputableInPolyTime w enc encNat)
    (hi : ComputableInPolyTime i enc encNat)
    (hg : ComputableInPolyTime generate enc encBool) :
    ComputableInPolyTime (fun a => initialCellCode (w a) (i a) (generate a)) enc encCode := by
  unfold initialCellCode initialGenerateCode initialPropagateCode
  fun_prop

/-- The initial decoder agrees with the typed circuit at every valid cell. -/
theorem initialCellCode_eq (w : ℕ) (i : Fin (w + 1)) (generate : Bool) :
    initialCellCode w i.val generate =
      (if generate then initialGenerate w i else initialPropagate w i).code := by
  cases generate <;> simp [initialCellCode, initialGenerateCode_eq, initialPropagateCode_eq]

/-- Each initial cell uses exactly one gate, even at the incoming-carry boundary. -/
theorem length_initialCellCode (w : ℕ) (i : Fin (w + 1)) (generate : Bool) :
    (initialCellCode w i.val generate).1.length = 1 := by
  rw [initialCellCode_eq, Circuit.length_code_fst]
  cases generate <;> simp

end Cslib.Circuits.Boolean.CarryLookahead
