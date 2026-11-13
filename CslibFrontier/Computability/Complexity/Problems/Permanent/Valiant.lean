/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.MetricOracle
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Matching
public import CslibFrontier.Computability.Complexity.Problems.Permanent.Membership
public import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT
public import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne
import CslibFrontier.Computability.Complexity.Problems.SharpThreeSAT

/-!
# Valiant's theorem: the 0/1 permanent is #P-complete

The permanent of 0/1 matrices, equivalently the number of perfect matchings of a bipartite graph,
is #P-complete [Valiant][Valiant1979], [Arora and Barak, Theorem 9.8][AroraBarak07],
[Goldreich, Theorem 6.20][Goldreich2007Draft].

Membership is the permutation-matrix verifier `ZeroOnePermanent.mem_SharpP`. Hardness composes
three one-query (metric) reductions: #3SAT is parsimoniously #P-complete
(`SharpThreeSAT_sharpPComplete`); Goldreich's clause-gadget matrix has permanent `12 ^ m` times the
number of satisfying assignments (`metricReducible_sharpThreeSAT_intPermanent`, Proposition 6.21);
and an integer permanent is recovered from a 0/1 permanent
(`metricReducible_intPermanent_zeroOnePermanent`, Proposition 6.22). All maps are native
polynomial-time machines on the dense table encodings `encCNF`, `encIntTable`, `encBoolTable`.

The books define completeness by polynomial-time oracle reductions. `SharpPMetricComplete` is the
single-query strengthening, and `zeroOnePermanent_computableInPolyTimeWithOracle` derives Arora
and Barak's Definition 9.5 from it: every function in #P lies in `FP^perm`, computed by one
polynomial-time oracle program that reads the bits of the 0/1 permanent from its bit graph.

## Main results

* `Cslib.Complexity.zeroOnePermanent_sharpPMetricComplete`: Valiant's theorem for the 0/1
  permanent, under metric reductions.
* `Cslib.Complexity.intPermanent_sharpPMetricHard`: the integer permanent is #P-hard.
* `Cslib.Complexity.zeroOnePermanent_computableInPolyTimeWithOracle`: the oracle (Cook) form of
  Arora and Barak's Definition 9.5.
* `Cslib.Complexity.bipartitePerfectMatchingCount_sharpPMetricComplete`: Goldreich's Theorem
  6.20, counting perfect matchings of bipartite graphs.
* `Cslib.Complexity.bipartitePerfectMatchingCount_computableInPolyTimeWithOracle`: the
  corresponding oracle form for bipartite perfect-matching counts.

## References

* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2007 draft][AroraBarak07]
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, 2007 draft]
  [Goldreich2007Draft]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The permanent of integer tables is #P-hard under metric reductions. -/
theorem intPermanent_sharpPMetricHard : SharpPMetricHard encIntTable encIntBin IntPermanent :=
  SharpThreeSAT_sharpPComplete.2.sharpPMetricHard.trans metricReducible_sharpThreeSAT_intPermanent

/-- **Valiant's theorem** [Arora and Barak, Theorem 9.8][AroraBarak07]: the permanent of 0/1
tables is in #P and #P-hard under metric (one-query) reductions. -/
theorem zeroOnePermanent_sharpPMetricComplete :
    SharpPMetricComplete encBoolTable ZeroOnePermanent :=
  ⟨ZeroOnePermanent.mem_SharpP,
    intPermanent_sharpPMetricHard.trans metricReducible_intPermanent_zeroOnePermanent⟩

/-- **Valiant's theorem in Arora and Barak's oracle form** (Definition 9.5): every function in
#P, with any encoding of its instances, is computable in polynomial time with an oracle answering
the bits of the 0/1 permanent. -/
theorem zeroOnePermanent_computableInPolyTimeWithOracle {α : Type} {enc : α ↪ List Bool}
    {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ComputableInPolyTimeWithOracle (bitGraph encBoolTable ZeroOnePermanent) f enc encNat :=
  zeroOnePermanent_sharpPMetricComplete.computableInPolyTimeWithOracle hf

/-- **Goldreich's Theorem 6.20**: counting the perfect matchings of the bipartite graph of a 0/1
table is in #P and #P-hard under metric reductions. -/
theorem bipartitePerfectMatchingCount_sharpPMetricComplete :
    SharpPMetricComplete encBoolTable BipartitePerfectMatchingCount := by
  have h : BipartitePerfectMatchingCount = ZeroOnePermanent :=
    funext bipartitePerfectMatchingCount_eq_zeroOnePermanent
  rw [h]
  exact zeroOnePermanent_sharpPMetricComplete

/-- Goldreich's Theorem 6.20 in the oracle form: every function in #P is computable in polynomial
time with an oracle answering the bits of the bipartite perfect-matching count. -/
theorem bipartitePerfectMatchingCount_computableInPolyTimeWithOracle {α : Type}
    {enc : α ↪ List Bool} {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ComputableInPolyTimeWithOracle (bitGraph encBoolTable BipartitePerfectMatchingCount) f enc
      encNat :=
  bipartitePerfectMatchingCount_sharpPMetricComplete.computableInPolyTimeWithOracle hf

end Cslib.Complexity
