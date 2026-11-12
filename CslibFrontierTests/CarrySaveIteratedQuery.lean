/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module

import CslibFrontier.Computability.Circuit.Boolean.CarrySave.IteratedQuery

open Cslib Cslib.Circuits.Boolean Cslib.Circuits.Boolean.CarrySaveQuery

-- The fourth source word belongs to the right child and its carry component.
example : descend ⟨[], 3, false, 8⟩ 0 = some ⟨[true], 2, true, 8⟩ := by decide

-- A carry-of-carry port shifts by two and selects the left sum component.
example : descend ⟨[true], 2, true, 9⟩ 4 = some ⟨[true, false], 1, false, 7⟩ := by decide

-- Underflow and exhausted trees do not manufacture child queries.
example : descend ⟨[], 1, true, 0⟩ 4 = none := by decide
example : descend ⟨[], 0, false, 5⟩ 0 = none := by decide

-- The theorem applies to arbitrary leaf providers without materializing their rows in queries.
example (leaves : List Bool → BitString (4 + 4)) (q : List Bool) (carry : Bool) :
    value leaves ⟨q, 3, carry, 2⟩ =
      (CarrySaveLocal.formula carry).eval interpretation
        (fun port => (descend ⟨q, 3, carry, 2⟩ port).elim false (value leaves)) :=
  value_layer leaves q 2 carry ⟨2, by decide⟩
