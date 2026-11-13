/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of the Valiant assembly)

import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant

/-! Checked clients of Valiant's theorem: hardness consequences used as a client would. -/

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A polynomial-time algorithm for counting bipartite perfect matchings would put every #P
function, here `#SAT`, in polynomial time. -/
example (h : ComputableInPolyTime BipartitePerfectMatchingCount encBoolTable encNat) :
    ComputableInPolyTime SharpSAT encCNF encNat :=
  bipartitePerfectMatchingCount_sharpPMetricComplete.2.computableInPolyTime h SharpSAT.mem_SharpP

/-- `#SAT` is computed in polynomial time relative to the bits of the 0/1 permanent. -/
example : ComputableInPolyTimeWithOracle (bitGraph encBoolTable ZeroOnePermanent) SharpSAT
    encCNF encNat :=
  zeroOnePermanent_computableInPolyTimeWithOracle SharpSAT.mem_SharpP

/-- Hardness transfers from the integer permanent along a metric reduction. -/
example : SharpPMetricHard encBoolTable encNat ZeroOnePermanent :=
  intPermanent_sharpPMetricHard.trans metricReducible_intPermanent_zeroOnePermanent

end Cslib.Complexity
