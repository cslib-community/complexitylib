/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP
public import CslibFrontier.Computability.Complexity.Reduction
import CslibFrontier.Computability.Probabilistic.Oracle.Composition

/-!
# Probabilistically checkable proofs against a proof oracle

`PCPPoly` is the class of problems with an adaptive probabilistically checkable proof of
polynomial randomness and polynomially many queries: a strict oracle-PPT verifier
(`Cslib.Probability.IsOraclePPTOn`) queries a proof, a function from query words to bits served by
the stateless prover `Cslib.Complexity.Prover.ofProof`. Some proof is accepted with certainty on
every member, and every proof is accepted with probability at most `1 / 2` on every non-member
[Babai, Fortnow and Lund][BabaiFortnowLund1991], [Arora and Barak, Section 8.5][AroraBarak09].

Unlike `Cslib.Complexity.PCP`, whose verifier is nonadaptive and reads a finite proof string, the
verifier here may choose each query from the earlier answers, and the proof may have exponential
support. The class is the intermediate step of `NEXP ⊆ MIP`: `PCPPoly ⊆ MIP₂`
(`Cslib.Complexity.PCPPoly_subset_MIP₂`) is the oracularization of
`CslibFrontier/Computability/Complexity/Classes/MIP/Oracularization.lean`.

## Main definitions

* `Cslib.Complexity.Prover.ofProof`: the proof oracle of a bit-valued proof.
* `Cslib.Complexity.PCPPoly`: adaptive PCPs with polynomial randomness and queries.

## Main results

* `Cslib.Complexity.PolyTimeReducible.mem_PCPPoly`: closure under polynomial-time reductions.

## References

* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Probability Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- The **proof oracle** of the bit string `π : List Bool → Bool`, answering every query `q` by the
one-bit word `[π q]`, with no state. -/
noncomputable abbrev Prover.ofProof {Operation : Type} (π : List Bool → Bool) :
    Prover Operation where
  State := Unit
  init := ()
  respond q s := PMF.pure ([π q.2], s)

/-- **Probabilistically checkable proofs with polynomial randomness and queries**: the problems
with a strict oracle-PPT verifier that accepts some proof with certainty on every member, and every
proof with probability at most `1 / 2` on every non-member. A proof is a function from query words
to bits, possibly of exponential support. -/
def PCPPoly (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ verifier : α → WordOracleComp Unit Bool, IsOraclePPTOn enc encBool verifier ∧
    (∀ a ∈ A, ∃ π, acceptProb (verifier a) (Prover.ofProof π) = 1) ∧
    ∀ a ∉ A, ∀ π, acceptProb (verifier a) (Prover.ofProof π) ≤ 1 / 2}

/-- **`PCPPoly` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PCPPoly {β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (hred : PolyTimeReducible encA encB A B) (hB : B ∈ PCPPoly encB) :
    A ∈ PCPPoly encA := by
  obtain ⟨f, hf, hAB⟩ := hred
  obtain ⟨V, hV, hc, hs⟩ := hB
  refine ⟨fun a => V (f a), IsOraclePPTOn.preprocess' hV hf, fun a ha => hc _ ((hAB a).mp ha),
    fun a ha => hs _ fun h => ha ((hAB a).mpr h)⟩

end Cslib.Complexity
