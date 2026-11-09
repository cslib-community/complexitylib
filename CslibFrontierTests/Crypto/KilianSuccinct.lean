/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Kilian.Succinct

/-!
# Tests for the succinctness of Kilian's protocol

A toy PCP verifier uses one random bit and one query, so its compact table has two entries and the
committed tree has depth one. Under a hash with `n`-bit digests at `n = 2`, the honest transcript
on both random strings has `2 + 2 + 2 + 2 * 3 = 12` payload bits, which is exactly the bound
`2 * n + n * r + n * (q * (1 + (r + ⌈log₂ q⌉) * n))` of `kilianCommunication_honest_le`.
-/

namespace CslibFrontierTests.Crypto.KilianSuccinct

open Cslib Cslib.Complexity Cslib.Crypto

/-- A hash with `k.length`-bit digests: the key itself. -/
def constHash (k _ : List Bool) : List Bool := k

theorem length_constHash (k x : List Bool) : (constHash k x).length = k.length := rfl

/-- A toy PCP verifier: one random bit chooses the address `1000` or `5`, and the bit read must be
`true`. -/
def toyVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict := fun (_, answers) => answers == [true]

/-- The statement. -/
abbrev x : List Bool := [true, false]

/-- The key at security parameter `2`. -/
abbrev key : List Bool := [false, true]

/-- Both random strings. -/
abbrev challenges : List (List Bool) := [[false], [true]]

-- The table has `2 ^ 1 * 1` entries and the tree depth `1 + ⌈log₂ 1⌉`.
example : (toyVerifier.queryTable x).length = 2 := by decide
example : kilianDepth toyVerifier x = 1 := by decide

-- The honest transcript has twelve payload bits: two openings of one bit and one two-bit label.
example : kilianResponseBits (kilianRespond constHash toyVerifier key x [true, true] challenges) =
    6 := by decide
example : kilianCommunication key (kilianCommit constHash toyVerifier key x [true, true]) challenges
    (kilianRespond constHash toyVerifier key x [true, true] challenges) = 12 := by decide

-- The general bound is attained here.
example : kilianCommunication key (kilianCommit constHash toyVerifier key x [true, true]) challenges
    (kilianRespond constHash toyVerifier key x [true, true] challenges) ≤
      2 * 2 + 2 * 1 + 2 * (1 * (1 + (1 + Nat.clog 2 1) * 2)) :=
  kilianCommunication_honest_le length_constHash rfl rfl (by decide) (q := 1)
    (fun _ _ => by simp [toyVerifier])

example : 2 * 2 + 2 * 1 + 2 * (1 * (1 + (1 + Nat.clog 2 1) * 2)) = 12 := by decide

end CslibFrontierTests.Crypto.KilianSuccinct
