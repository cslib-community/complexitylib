/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Kilian
import CslibFrontier.Tactic.PolyTime

/-!
# Tests for Kilian's protocol

A toy PCP verifier reads one random bit and queries one of two far-apart binary addresses, `1000`
or `5`, accepting when the bit read is `true`. Its compact table has two entries, so the committed
tree has depth one. Under a hash that returns its message, the honest prover's commitment and
openings for the all-`true` table are accepted, while flipping an opened bit, opening the right bit
with a short path, giving too few openings, or committing to a table that the PCP verifier rejects
are all rejected. The completeness theorem applies to the honest execution.
-/

namespace CslibFrontierTests.Crypto.Kilian

open Cslib Cslib.Complexity Cslib.Crypto Turing.MultiTapeTM

/-- A hash that returns its message. -/
def idHash (_ x : List Bool) : List Bool := x

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

/-- Both random strings, one repetition each. -/
abbrev challenges : List (List Bool) := [[false], [true]]

-- The compact table has the two addresses, and the tree over it has depth one.
example : toyVerifier.queryTable x = [1000, 5] := by decide
example : kilianDepth toyVerifier x = 1 := by decide
example : kilianPosition toyVerifier x 5 = 1 := by decide

-- The all-`true` table is a witness; a table with a `false` entry is not.
example : toyVerifier.tableVerifier (x, [true, true]) = true := by decide
example : toyVerifier.tableVerifier (x, [true, false]) = false := by decide

-- The honest prover is accepted on the witness table.
example : kilianVerify idHash toyVerifier key x (kilianCommit idHash toyVerifier key x [true, true])
    challenges (kilianRespond idHash toyVerifier key x [true, true] challenges) = true := by
  decide

-- The same, from the completeness theorem, which also covers a table longer than the address
-- table: `[true, true, false]` is a witness, since its padding is never read. A shorter table is
-- read with `false` for the missing entries, so `[true]` is not a witness.
example : kilianVerify idHash toyVerifier key x
    (kilianCommit idHash toyVerifier key x [true, true, false]) challenges
    (kilianRespond idHash toyVerifier key x [true, true, false] challenges) = true :=
  kilianVerify_kilianRespond (by decide) key (by decide)

example : toyVerifier.tableVerifier (x, [true]) = false := by decide

/-- The honest response on the witness table. -/
abbrev honest : KilianResponse := kilianRespond idHash toyVerifier key x [true, true] challenges

/-- The honest root on the witness table. -/
abbrev root : List Bool := kilianCommit idHash toyVerifier key x [true, true]

-- Flipping the bit opened in the second repetition is rejected by the Merkle check (and by the
-- PCP verifier).
example : kilianVerify idHash toyVerifier key x root challenges
    [honest.getD 0 [], [⟨false, ((honest.getD 1 []).getD 0 ⟨false, []⟩).path⟩]] = false := by
  decide

-- Opening the right bit with a path of the wrong length is rejected.
example : kilianVerify idHash toyVerifier key x root challenges
    [honest.getD 0 [], [⟨true, []⟩]] = false := by decide

-- A missing repetition, or a missing opening, is rejected.
example : kilianVerify idHash toyVerifier key x root challenges [honest.getD 0 []] = false := by
  decide
example : kilianVerify idHash toyVerifier key x root challenges [honest.getD 0 [], []] = false := by
  decide

-- An honest commitment to a table that the PCP verifier rejects is rejected on the random string
-- that reads the `false` entry, although every opening is consistent with the root.
example : kilianCheck idHash toyVerifier key x (kilianCommit idHash toyVerifier key x [true, false])
    [true] (kilianOpen idHash toyVerifier key x [true, false] [true]) = false := by decide
example : kilianCheck idHash toyVerifier key x (kilianCommit idHash toyVerifier key x [true, false])
    [false] (kilianOpen idHash toyVerifier key x [true, false] [false]) = true := by decide

-- Perfect completeness of the honest execution, at every security parameter.
example (n : ℕ) :
    ProbComp.eval (kilianHonestGame idHash toyVerifier x [true, true] n) = PMF.pure true :=
  eval_kilianHonestGame idHash toyVerifier (by decide) n

-- Extensionality and compositional polynomial-time certificates for `encKilianOpening`.
example (o₁ o₂ : MerkleOpening Bool) (hbit : o₁.leaf = o₂.leaf) (hpath : o₁.path = o₂.path) :
    o₁ = o₂ := by
  ext1 <;> assumption

example : ComputableInPolyTime
    (fun p : Bool × MerkleOpening Bool => (⟨!p.1, p.2.path⟩ : MerkleOpening Bool))
    (encPair encBool encKilianOpening) encKilianOpening := by
  fun_prop

example : ComputableInPolyTime (fun o : MerkleOpening Bool => o.leaf) encKilianOpening encBool := by
  fun_prop

-- Encoded words unchanged: an opening keeps the former `KilianOpening` layout, the framed bit
-- followed by the framed path.
example (o : MerkleOpening Bool) :
    encKilianOpening o = encPair encBool (encList encBits) (o.leaf, o.path) := rfl

end CslibFrontierTests.Crypto.Kilian
