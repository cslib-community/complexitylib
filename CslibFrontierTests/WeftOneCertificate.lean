/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Unbounded.Certificate

/-!
# Tests: Kleene evaluation and certificates for circuits of weft one

Kleene evaluation of a conjunction of three inputs is false when one input is known false, true
when all are known true, and unknown otherwise.

The certificate check (`WeftOne.claimsValid`), evaluated by `decide`, runs on two gate lists. The
first is a conjunction of three inputs. Claiming the conjunction true is valid. The empty list of
claims is not valid, and neither is claiming the conjunction false, since a conjunction can only be
claimed true; such a claim has no checks. Validity does not read the input. The second gate list
puts a conjunction of three disjunctions of two inputs on top. Claiming the top conjunction true is
valid for depth bound `1`, since its checks lie on the small disjunctions, but not for depth
bound `0`.
-/

namespace CslibFrontierTests.WeftOneCertificate

open Cslib.Circuits.Boolean.Unbounded

/-! ### Kleene evaluation -/

example : kleeneOp (.and 3) [some true, none, some false] = some false := by decide

example : kleeneOp (.and 3) [some true, some true, some true] = some true := by decide

example : kleeneOp (.and 3) [some true, none, some true] = none := by decide

example : kleeneOp (.or 2) [none, some true] = some true := by decide

example : kleeneEval [some true, none] [(.not, [0]), (.or 2, [1, 2])] =
    [some true, none, some false, none] := by decide

/-! ### Certificates -/

/-- A conjunction of three inputs. -/
def and3 : List (Op × List ℕ) := [(.and 3, [0, 1, 2])]

-- Claiming the conjunction (wire `3`) true is valid; its checks are the three inputs.
example : WeftOne.claimsValid 0 3 and3 3 [(3, true)] = true := by decide

example : WeftOne.claimChecks 3 and3 (3, true) = [(0, true), (1, true), (2, true)] := by decide

-- Without claims, Kleene evaluation does not know the output.
example : WeftOne.claimsValid 0 3 and3 3 [] = false := by decide

-- A conjunction cannot be claimed false: the claim has no checks and does not replace the gate.
example : WeftOne.claimsValid 0 3 and3 3 [(3, false)] = false := by decide

example : WeftOne.claimChecks 3 and3 (3, false) = [] := by decide

-- Validity does not read the input: the valid claim above has checks that fail on the input
-- `(false, false, false)`, which the conjunction rejects.

/-- A conjunction of three disjunctions of two inputs each. -/
def andOfOrs : List (Op × List ℕ) :=
  [(.or 2, [0, 1]), (.or 2, [2, 3]), (.or 2, [4, 5]), (.and 3, [6, 7, 8])]

-- The checks of claiming the top conjunction true are the three disjunctions, of small depth `1`.
example : WeftOne.smallDepths 1 6 andOfOrs = [0, 0, 0, 0, 0, 0, 1, 1, 1, 2] := by decide

example : WeftOne.claimsValid 1 6 andOfOrs 9 [(9, true)] = true := by decide

example : WeftOne.claimsValid 0 6 andOfOrs 9 [(9, true)] = false := by decide

end CslibFrontierTests.WeftOneCertificate
