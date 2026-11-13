/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.PolyTime.Certificates
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Probabilistic.Fold
import CslibFrontier.Computability.Probabilistic.Finite
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Polynomial-Time Completeness of $\text{OT}_1^4$ for Semi-Honest Multi-Party Computation

This module formalizes a proper-coalition variant of Goldreich's semi-honest multi-party
completeness theorem for 1-out-of-4 bit oblivious transfer $\text{OT}_1^4$ (Section 7.5.2.4,
Theorem 7.5.12, print p. 707; generalizing Section 7.3.4, Theorem 7.3.11, print p. 648), with
uniform efficiency certificates for the joint word-level runner and coalition simulators.
Given any polynomial-time computable family of $m$-party randomized functionalities specified
by a word-level evaluator
`F : α × List Bool → List Bool` with polynomial-time unary input width `n : α → ℕ`, output width
`k : α → ℕ`, and shared-coin width `coins : α → ℕ`:

1. **Uniform Circuit Compilation:** `Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily`
   compiles `F` into a polynomial-time constructible family of Boolean circuits
   `C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a)` whose evaluation agrees
   with `wordRandomizedFunctionality m coins n k F a`.
2. **Word-Level Protocol Execution & Bridge Lemma:** `Protocol.runEncoded` executes any
   `ot14Spec`-hybrid protocol in `Cslib.Probability.WordOracleComp Unit (List Bool)` by translating
   each typed `ot14Spec` query to a 6-bit word query and reading the 1-bit reply prefix.
   `Protocol.eval_runEncoded_eq_evalWith_map` proves that running `Π.runEncoded` against
   `ot14WordHandler` yields the exact distribution of `(Π.evalWith ot14World x).map
   (encodeViewsAndOutputs encView encOut)`.
3. **Uniform Efficiency Certificates:** Over the family input records `FamilyRunInput` and
   `FamilySimInput`, `familyIsOraclePPT_gmwOT14RandomizedProtocol` certifies that the
   centralized joint word-encoded execution `Protocol.runEncoded` of
   `gmwOT14RandomizedProtocol` across all `m` parties is uniformly oracle-PPT
   (`Protocol.Family.IsOraclePPT`; note that this certifies the joint word-level runner rather
   than separate per-party local PPT strategies), and `familyIsPPT_gmwOT14RandomizedSim`
   certifies that for every static coalition `I : Finset (Fin m)`, the encoded view simulator
   `gmwOT14RandomizedSim` is uniformly PPT (`CoalitionSimulator.Family.IsPPT`). Because
   `gmwCircuitProtocol` (Construction 7.5.10, p. 706) includes one `sharedMulSpec m` share-refresh
   call per output coordinate `(r, j) : Fin m × Fin k a` in Step 3 in addition to one call per
   `.and`/`.or` gate in Step 2, composing with `multiPartyMulProtocol m` (Construction 7.5.8,
   p. 704) and `twoPartyMulProtocol` (Construction 7.3.7, pp. 643–644) expands each
   `sharedMulSpec m` call into $m(m-1)/2$ pairwise `ot14Spec` calls (adding
   $m \cdot k(a) \cdot m(m-1)/2$ calls in Step 3, polynomial in
   $m, n(a), k(a), (C\,a).\text{size}$).
4. **End-to-End Completeness (`exists_perfectSemiHonestPrivate_ot14_of_polyTime`):** Formalizes a
   **proper-coalition variant** of Goldreich's Theorem 7.5.12, combining uniform circuit
   compilation, proper-coalition perfect semi-honest privacy in `ot14World`
   (`PerfectSemiHonestPrivateProper`), and the uniform efficiency predicates above. The
   proper-coalition quantifier `I ≠ Finset.univ` is narrower than Goldreich's Definition 7.5.1 and
   Theorem 7.5.12 (which quantify over all `I ⊆ [m]`, p. 696; Goldreich's text on pp. 697 and 703
   treats `I = [m]` as trivial without restricting that remark to deterministic functionalities or
   to the view-only Eq. 7.39). Under the joint view-and-output equation Eq. 7.40 for randomized
   functionalities, `I = Finset.univ` is not vacuous: the canonical independent-coin-share simulator
   `randomizedWrapperSim` is refuted at `I = Finset.univ` by
   `not_perfectSemiHonestPrivate_coinEchoRandomizedWrapper_univ` in
   [CslibFrontierTests/Crypto/MPC.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/Crypto/MPC.lean),
   and any full-coalition simulator receiving only `(x, y)` would have to sample coin shares whose
   XOR `r` satisfies `g(r, x) = y`.

The development is split by stage:

* `Cslib.Crypto.Protocols.MPC.PolyTime.RunEncoded`: the word-level runner and its bridge lemma.
* `Cslib.Crypto.Protocols.MPC.PolyTime.Encoding`: family inputs, view encoders and the named
  efficiency predicates.
* `Cslib.Crypto.Protocols.MPC.PolyTime.Runner`: word-level runners and their certificates.
* `Cslib.Crypto.Protocols.MPC.PolyTime.InputProgEquiv`,
  `Cslib.Crypto.Protocols.MPC.PolyTime.Certificates`: equivalence of the word-level runners with
  the typed protocol and simulator, and the public certificates.

## Main results

* `Cslib.Crypto.Protocols.MPC.exists_perfectSemiHonestPrivate_ot14_of_polyTime`: proper-coalition
  variant of Theorem 7.5.12 (Section 7.5.2.4, print p. 707; generalizing Theorem 7.3.11, Section
  7.3.4, print p. 648), establishing polynomial-time completeness of $\text{OT}_1^4$ for $m$-party
  semi-honest computation against every proper coalition `I ≠ Finset.univ`.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.3.2 (Eq. 7.20, p. 640), Section 7.3.3 (Construction 7.3.7, pp. 643–644),
  Section 7.3.4 (Theorem 7.3.11, p. 648), Section 7.5.1.2 (Definition 7.5.1, Eqs. 7.39–7.40,
  p. 696; p. 697), Section 7.5.2.1 (p. 703), Section 7.5.2.2 (Construction 7.5.8, p. 704),
  Section 7.5.2.3 (Construction 7.5.10, p. 706), and Section 7.5.2.4 (Theorem 7.5.12, p. 707).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Cslib.ProbComp Cslib.Circuits Turing.MultiTapeTM

open Turing.MultiTapeTM Cslib.Circuits

/-- Proper-coalition variant of Theorem 7.5.12 (Goldreich Section 7.5.2.4, p. 707; generalizing
Theorem 7.3.11, Section 7.3.4, p. 648): every polynomial-time `m`-party randomized functionality
family `F` is privately reducible to $\text{OT}_1^4$ in the semi-honest model against every proper
static coalition `I ≠ Finset.univ`, with uniform polynomial-time circuit family `C`, uniform
`IsOraclePPTOn` joint word-level protocol execution via `Protocol.runEncoded` (linked to
`Protocol.evalWith ot14World` by `Protocol.eval_runEncoded_eq_evalWith_map`), and uniform
`IsPPTOn` coalition simulators.

Note that the proper-coalition quantifier `I ≠ Finset.univ` (`PerfectSemiHonestPrivateProper`) is
narrower than Goldreich's Definition 7.5.1 and Theorem 7.5.12 (which quantify over all `I ⊆ [m]`,
p. 696; Goldreich's text on pp. 697 and 703 treats `I = [m]` as trivial without restricting that
remark to deterministic functionalities or to the view-only Eq. 7.39). Under the joint
view-and-output equation Eq. 7.40 for randomized functionalities, `I = Finset.univ` is not vacuous:
the canonical independent-coin-share simulator `randomizedWrapperSim` is refuted at
`I = Finset.univ` by `not_perfectSemiHonestPrivate_coinEchoRandomizedWrapper_univ` in
[CslibFrontierTests/Crypto/MPC.lean](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/Crypto/MPC.lean),
and any full-coalition simulator receiving only `(x, y)` would have to sample coin shares whose
XOR `r` satisfies `g(r, x) = y`. -/
theorem exists_perfectSemiHonestPrivate_ot14_of_polyTime {α : Type} {enc : α ↪ List Bool}
    (m : ℕ) [NeZero m] {coins n k : α → ℕ} {F : α × List Bool → List Bool}
    (hcoins : ComputableInPolyTime coins enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hk : ComputableInPolyTime k enc encUnary)
    (hF : ComputableInPolyTime F (encPair enc encBits) encBits) :
    ∃ C : (a : α) → Circuit Boolean.signature (m * n a + coins a) (m * k a),
      ComputableInPolyTime (fun a => (C a).code) enc Boolean.encCode ∧
      (∀ a (xr : Fin (m * n a + coins a) → Bool) (j : Fin (m * k a)),
        (C a).eval Boolean.interpretation xr j =
          (F (a, List.ofFn xr)).getD j.val false) ∧
      (∀ a, PerfectSemiHonestPrivateProper
        (gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a)) ot14World
        (wordRandomizedFunctionality m coins n k F a)
        (gmwOT14RandomizedSim m (coins a) (n a) (k a) (C a))) ∧
      Protocol.Family.IsOraclePPT enc m n
        (fun a => gmwOT14RandomizedProtocol m (coins a) (n a) (k a) (C a))
        (fun a => encGMWPartyView m (coins a) (n a) (k a) (C a)) (fun _ _ y => List.ofFn y) ∧
      (∀ (I : Finset (Fin m)), I ≠ Finset.univ →
        CoalitionSimulator.Family.IsPPT enc m n k I
          (fun a => encGMWPartyView m (coins a) (n a) (k a) (C a))
          (fun a => gmwOT14RandomizedSim m (coins a) (n a) (k a) (C a) I)) := by
  have h_in : ComputableInPolyTime (fun a => m * n a + coins a) enc encUnary := by
    have hmn := ComputableTidilyInPolyTime.comp' ComputableTidilyInPolyTime.unary_mul
      ((ComputableTidilyInPolyTime.const m).prod hn.tidy)
    exact ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.comp' ComputableTidilyInPolyTime.unary_add
        (hmn.prod hcoins.tidy))
  have h_out : ComputableInPolyTime (fun a => m * k a) enc encUnary := by
    have hmk := ComputableTidilyInPolyTime.comp' ComputableTidilyInPolyTime.unary_mul
      ((ComputableTidilyInPolyTime.const m).prod hk.tidy)
    exact ComputableInPolyTime.of_tidy hmk
  obtain ⟨C, hC_code, hC_eval⟩ :=
    Cslib.Complexity.CircuitValue.exists_uniformCircuitFamily h_in h_out hF
  refine ⟨C, hC_code, hC_eval, fun a => ?_,
    familyIsOraclePPT_gmwOT14RandomizedProtocol m hcoins hn hk hC_code,
    fun I _ => familyIsPPT_gmwOT14RandomizedSim m hcoins hn hk hC_code I⟩
  have hfunc :
      randomizedFunctionality (coins a) (fun r x i =>
        Cslib.BitString.block
          ((C a).eval Boolean.interpretation
            (Fin.append
              ((Cslib.BitString.blocksEquiv (α := Bool) (m := m) (k := n a)).symm x) r)) i) =
      wordRandomizedFunctionality m coins n k F a := by
    unfold wordRandomizedFunctionality
    congr 1
    funext r x i j
    rw [Cslib.BitString.block, hC_eval a _ (finProdFinEquiv (i, j)), finProdFinEquiv_apply_val]
    dsimp only [encodeCoinsAndInputs]
    congr 1
    ring
  rw [← hfunc]
  exact perfectSemiHonestPrivateProper_gmwOT14Randomized m (coins a) (n a) (k a) (C a)

end Cslib.Crypto.Protocols.MPC
