/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Readback
import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.NumericBounds

/-!
# Pure record readback without initialized product execution

The decoded list retains ordered duplicate occurrences and ignores arbitrary dirty memory
outside its span. Numerical width clients need neither initialized product backend.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleRecordReadback

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle

private def dirtyWords (a : ℕ) : ℕ :=
  if a = 10 || a = 12 then 2 else if a = 11 || a = 13 then 1
  else if a = 14 then 0 else if a = 15 then 2 else 999

#guard ((RecordProduct.decodedQueries (by decide : 0 < 3) dirtyWords 10 3).map
  (fun pair => (pair.1.val, pair.2.val))) == [(2, 1), (2, 1), (0, 2)]

-- In-range words are returned exactly; the total decoder's modulo does not alter them.
example : ((RecordProduct.decodedQueries (by decide : 0 < 3) dirtyWords 10 3).get
    ⟨1, by decide⟩).1.val = 2 ∧
    ((RecordProduct.decodedQueries (by decide : 0 < 3) dirtyWords 10 3).get
      ⟨1, by decide⟩).2.val = 1 :=
  RecordProduct.decodedQueries_get_val (by decide) dirtyWords 10 3 ⟨1, by decide⟩
    (by decide) (by decide)

-- The source-only numeric API still supplies the full envelope, with its original constant.
example {n D g p A κ : ℕ} (hn : 1 ≤ n) (hD : D ≤ n) (hg : g ≤ n)
    (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    2 ^ RecordWitness.admissionWidth n D g p A ≤ (n + 2) ^ (514 * κ + 11818) := by
  exact RecordWitness.wordBound_le_pow hn hD hg hp hA

end ComplexityTests.WordRAMExactTriangleRecordReadback
