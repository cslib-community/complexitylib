/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Complexity.Classes.SharpP.MetricOracle
import CslibFrontier.Computability.Complexity.Problems.Permanent.Matching
import CslibFrontier.Computability.Complexity.Problems.Permanent.Membership

/-! Checked clients for the 0/1 permanent in #P, its perfect-matching form and the oracle form of
metric reductions. -/

namespace Cslib.Complexity.Tests.PermanentMembership

open Turing.MultiTapeTM Cslib.Complexity

/-- The identity permutation matrix of size two is accepted for the all-ones table; a matrix with
two entries in one row is rejected. -/
example : ZeroOnePermanent.verifier ([[true, true], [true, true]], [true, false, false, true]) =
    true := by decide

example : ZeroOnePermanent.verifier ([[true, true], [true, true]], [true, true, false, false]) =
    false := by decide

/-- A permutation matrix off the support of the table is rejected. -/
example : ZeroOnePermanent.verifier ([[true, false], [true, true]], [false, true, true, false]) =
    false := by decide

/-- The membership half of Valiant's theorem. -/
example : ZeroOnePermanent ∈ SharpP encBoolTable := ZeroOnePermanent.mem_SharpP

/-- The perfect-matching count is the 0/1 permanent, so it is in #P as well. -/
example : BipartitePerfectMatchingCount ∈ SharpP encBoolTable := by
  rw [show BipartitePerfectMatchingCount = ZeroOnePermanent from
    funext bipartitePerfectMatchingCount_eq_zeroOnePermanent]
  exact ZeroOnePermanent.mem_SharpP

/-- A #P-complete function under metric reductions is #P-complete in the oracle sense. -/
example {β α : Type} {encB : β ↪ List Bool} {enc : α ↪ List Bool} {g : β → ℕ}
    (hg : SharpPMetricComplete encB g) {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ComputableInPolyTimeWithOracle (bitGraph encB g) f enc encNat :=
  hg.computableInPolyTimeWithOracle hf

end Cslib.Complexity.Tests.PermanentMembership
