/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.FixedPrime.Accounting
public import Complexity.Algorithms.WordRAM.ExactTriangle.BoxFixedPrime.Program

/-!
# Box-backed charges for actual catalogue records

Each block is decoded from the real protected producer memory, in its original rank order.
The mathematical products are those computed by the concrete native product; their answer
correctness is proved, not assumed. Failed occurrences in distinct records therefore share
one global false-positive budget. These value lemmas supply the native loop invariant.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxFixedPrime

open FixedPrime

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Real per-record product, root, query and controller charges, excluding interval scans.
The constant includes the outer loop's two control instructions. -/
@[expose] noncomputable def recordBase {m n p : ℕ} (hn : 0 < n)
    (values : ℕ → ℤ) (mem : ℕ → ℕ) (idx : InstanceIndex p) : ℕ :=
  let Q := RecordProduct.recordQueryCount n (D m) p values idx
  let qs := RecordProduct.decodedQueries hn mem (RecordProduct.recordQueries n (D m) p idx) Q
  RecordBoxProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q + 61

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxFixedPrime
