/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.CountingSimulation.EntryAnalysis
public import Complexity.Computability.Circuit.Frontier.TensorNetwork.TruncatedEntry

/-!
# Theorem D.1 at truncation order `ℓ` for entry procedures

The instance of the interface of Theorem D.1 at truncation order `ℓ`
(`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm`) for networks whose entries are
computed by procedures: for every native certificate `ce` of an entry procedure,
`CountingSimulation.truncEntryContractionAlgorithm ce` computes the contraction in
`B_{P,ℓ} = (ℤ / 2 ^ P)[V] / (V ^ ℓ)` of the networks admissible for `ce` with at most `C s` vertices
(`Cslib.Circuits.Frontier.TruncEntryAdmissible`), for `1 ≤ P, ℓ ≤ D s`, in time
`poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and polynomial space.

It combines the reduction of truncation order `ℓ` to `A_P = (ℤ / 2 ^ P)[U] / (f)`
(`Cslib.Circuits.Frontier.TruncatedContractionAlgorithm.ofEntry`) with the contraction algorithm
for entry procedures (`CountingSimulation.entryContractionAlgorithm`), applied to the specialized
entries.

This is Theorem D.1 of [OpenAI2026ETH] (p. 53) with one narrowing: the theorem asks for at most
polynomially many vertices in `s`, and admissibility here asks for at most `C s`. The networks of
Lemma D.2 (p. 56) and of the fixed-density bound (§D.2, p. 54) have that many. As for all the
interfaces of this development, admissibility also asks for at least `s` edges, which a caller
gets by padding (see `Cslib.Circuits.Frontier.EntryAdmissible`).

## Main definitions

* `Cslib.Complexity.CountingSimulation.truncEntryContractionAlgorithm`: Theorem D.1 at truncation
  order `ℓ` for entry procedures.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Theorem D.1 (p. 53).
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier Cslib.GenericRAM Turing.MultiTapeTM

variable {T : Type} {encT : T ↪ List Bool} {entry : T → List Bool → List ℕ}

/-- **Theorem D.1 at truncation order `ℓ` for entry procedures** ([OpenAI2026ETH], p. 53, for
networks with at most `C s` vertices): for every native certificate `ce` of an entry procedure,
the reduction of truncation order `ℓ` to `A_P` around the contraction algorithm for the
specialized entries is a truncated contraction algorithm for the networks admissible for `ce` with
at most `C s` vertices. It computes the contraction in `B_{P,ℓ}` from `(P, ℓ, r, G)` on every
input, and on admissible inputs with `1 ≤ P, ℓ ≤ D s` in time `poly(n) 2 ^ O(s / √⌊log₂ s⌋)` and
polynomial space. -/
noncomputable def truncEntryContractionAlgorithm
    (ce : NativeCertificate (fun q : T × List Bool => entry q.1 q.2) (encPair encT encBits)
      (encList encNat)) :
    TruncatedContractionAlgorithm encT entry (TruncEntryAdmissible ce) :=
  TruncatedContractionAlgorithm.ofEntry ce
    (entryContractionAlgorithm (specEntryCertificate entry ce))

end Cslib.Complexity.CountingSimulation
