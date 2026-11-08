/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.MIP.Defs
public import Complexity.Computability.Complexity.Classes.MIP.OptimalProver
public import Complexity.Computability.Complexity.Classes.MIP.NEXP
public import Complexity.Computability.Complexity.Classes.MIP.Oracularization
public import Complexity.Computability.Complexity.Classes.MIP.Repetition

/-!
# Multiprover interactive proofs (`MIP₂` and `MIP`)

This umbrella module re-exports the multiprover interactive proof development:

* `Complexity.Computability.Complexity.Classes.MIP.Defs`: non-communicating prover families
  (`Prover.independent`, `Prover.independent_state_eq_of_ne`), `IsMultiproverProof`, the classes
  `MIP₂` and `MIP`, closure under polynomial-time many-one reductions (`PolyTimeReducible.mem_MIP₂`,
  `PolyTimeReducible.mem_MIP`), and the embeddings `IP ⊆ MIP₂ ⊆ MIP`.
  The number of provers is constant for each language.
* `Complexity.Computability.Complexity.Classes.MIP.OptimalProver`: coordinatewise presampling and
  deterministic prover optimality (`MIP.exists_deterministic_prover_family`) using generic
  multi-channel coin-fixing (`Interaction.acceptProb_eq_sum`), and pairwise history consistency
  (`MIP.consistentHist`, `MIP.DetProver.ValidFrom.consistentHist`,
  `MIP.validFrom_candidateProver`).
* `Complexity.Computability.Complexity.Classes.MIP.NEXP`: polynomial-time multi-channel transcript
  verification, the exponential-padding translation in `Classes.Padding`, and the unconditional
  upper bounds
  `MIP_subset_NEXP : MIP enc ⊆ NEXP enc` and `MIP₂_subset_NEXP : MIP₂ enc ⊆ NEXP enc`.

* `Complexity.Computability.Complexity.Classes.MIP.Repetition`: sequential repetition against
  non-communicating provers (`acceptProb_sequentialRepeat_independent_le`).
* `Complexity.Computability.Complexity.Classes.MIP.Oracularization`: probabilistically checkable
  proofs against a proof oracle become two-prover interactive proofs,
  `PCPPoly_subset_MIP₂ : PCPPoly enc ⊆ MIP₂ enc`.

The converse inclusion `NEXP ⊆ MIP₂` reduces to `NEXP ⊆ PCPPoly` (Babai–Fortnow–Lund
multilinearity testing and arithmetization of `NEXP` verification tableaux), which remains open.

## References

* [M. Ben-Or, S. Goldwasser, J. Kilian, A. Wigderson, *Multi-prover interactive proofs: How to
  remove intractability assumptions*][BenOrGoldwasserKilianWigderson1988]
* [L. Babai, L. Fortnow, C. Lund, *Non-deterministic exponential time has two-prover interactive
  protocols*][BabaiFortnowLund1991]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/
