/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.PriorityQueue.WordRAM.Basic

/-!
# Decoding indexed priority-queue answers

These equations apply the existing `PQCode.decode` to actual output-register values. Presence
flags may be any nonzero word; keys and handles are unshifted, and extraction retains the
decoder's handle-range check. No program execution or word-fit hypothesis follows from decoding.

## Main results

* `PQCode.decode_isEmpty`: decode a Boolean flag.
* `PQCode.decode_getKey_none`, `PQCode.decode_getKey_some`: decode an optional key.
* `PQCode.decode_extractMin_none`, `PQCode.decode_extractMin_some`: decode an optional typed entry.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.WordRAM.PQCode

open Cslib.WordRAM Cslib.DataStructure.PriorityQueue

variable {B : Basis} {r n K : ℕ} (P : PQCode B r) (regs : Fin r → ℕ)

/-- A canonical Boolean output flag decodes to that Boolean. -/
theorem decode_isEmpty {b : Bool} (hflag : regs P.outFlag = b.toNat) :
    P.decode (n := n) (K_max := K) .isEmpty regs = some b := by
  cases b <;> simp [decode, hflag]

/-- A zero flag decodes to an absent key, regardless of the unused key register. -/
theorem decode_getKey_none (v : Fin n) (hflag : regs P.outFlag = 0) :
    P.decode (K_max := K) (.getKey v) regs = some none := by
  simp [decode, hflag]

/-- A nonzero flag decodes the actual unshifted key register. -/
theorem decode_getKey_some (v : Fin n) {k : ℕ} (hflag : regs P.outFlag ≠ 0)
    (hkey : regs P.outK = k) :
    P.decode (K_max := K) (.getKey v) regs = some (some k) := by
  simp [decode, hflag, hkey]

/-- A zero flag decodes to no extracted entry, even when no handle exists. -/
theorem decode_extractMin_none (hflag : regs P.outFlag = 0) :
    P.decode (n := n) (K_max := K) .extractMin regs = some none := by
  simp [decode, hflag]

/-- A nonzero flag with an actual in-range handle and key decodes to that typed entry. -/
theorem decode_extractMin_some (v : Fin n) {k : ℕ} (hflag : regs P.outFlag ≠ 0)
    (hhandle : regs P.outV = v.val) (hkey : regs P.outK = k) :
    P.decode (K_max := K) .extractMin regs = some (some (v, k)) := by
  simp [decode, hflag, hhandle, hkey, v.isLt]

end Cslib.DataStructure.PriorityQueue.WordRAM.PQCode
