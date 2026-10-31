/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (result registry collection)
import ComplexityResults.Registry
import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder
import Complexity.Computability.Complexity.Classes.LogSpace.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Lowness
import Complexity.Computability.Complexity.FineGrained.OrthogonalVectors
import Complexity.Computability.Complexity.FineGrained.PPZ
import Complexity.Computability.Complexity.FineGrained.Schoening
import Complexity.Computability.Complexity.FineGrained.Sparsification

/-!
# Collected results without selected formal abstracts

These scopes and source correspondences were inspected against existing repository statements
and citations. They are not a new primary-source audit. `unverified` means a source theorem
name/number or precise locator has not yet been collected; it must not be guessed.
-/

register_result "sharp-p-lowness" where
  title := "Exact characterization of #P oracle lowness"
  topic := "counting classes"
  sources := [
    { paper := KoeblerSchoeningTodaToran1992, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.SharpPWithOracle_eq_SharpP_iff
  ]
  scope := "Equality of #P^A and #P on binary words iff A is in UP ∩ coUP. Uses strict \
    polynomial-time adaptive word-oracle verifiers, with resource bounds for \
    arbitrary replies; does not assert an oracle-machine counting characterization."

register_result "gap-p-spp-lowness" where
  title := "GapP and SPP lowness characterize SPP"
  topic := "counting classes"
  sources := [
    { paper := FennerFortnowKurtz1994, theorem := unverified,
      locator := "Section 5" }
  ]
  theorems := [
    Cslib.Complexity.GapPWithOracle_eq_GapP_iff,
    Cslib.Complexity.SPPWithOracle_eq_SPP_iff
  ]
  scope := "Binary-word instances; strict adaptive oracle-verifier model. GapP is a \
    difference of two unsigned witness counts."

register_result "first-order-logspace" where
  title := "Fixed first-order queries are decidable in logarithmic space"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 3.1",
      locator := unverified }
  ]
  theorems := [
    Cslib.Logic.Vocabulary.queryLanguage_mem_L,
    Cslib.Logic.FO.Definable.queryLanguage_mem_L
  ]
  scope := "Fixed first-order sentences over finite relational vocabularies, with explicit \
    structure encoding and malformed-input rejection. Includes empty structures and \
    nullary relations; excludes constants and built-in order/BIT from the cited FO \
    convention."

register_result "nl-in-p" where
  title := "NL is contained in P"
  topic := "space complexity"
  sources := [
    { paper := Sipser2013, theorem := unverified,
      locator := "Section 8.5" },
    { paper := AroraBarak09, theorem := unverified,
      locator := "Section 4.1" }
  ]
  theorems := [
    Cslib.Complexity.NL_subset_P,
    Cslib.Complexity.mem_P_of_recognizesInSpace
  ]
  scope := "Finite-control native nondeterministic multi-tape machines and arbitrary \
    injective encodings. The stronger recognizer result permits nonterminating \
    branches with logarithmic workspace; deterministic polynomial-time \
    configuration reachability decides acceptance."

register_result "ppz-success" where
  title := "PPZ success probability for k-SAT"
  topic := "SAT algorithms"
  sources := [
    { paper := PPZ1997, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.PPZ.round_success_of_satisfiable,
    Cslib.Complexity.PPZ.round_success
  ]
  scope := "CNF over Fin n, clauses of length at most k ≥ 1. One-round success probability \
    at least 2^(-(1 - 1/k)n); also a unique-solution theorem. Probabilistic \
    semantics only: these declarations do not certify native runtime."

register_result "schoening-success" where
  title := "Schöning randomized k-SAT success bound"
  topic := "SAT algorithms"
  sources := [
    { paper := Schoening1999, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.Schoening.trial_success_of_length_le,
    Cslib.Complexity.Schoening.trial_success
  ]
  scope := "Satisfiable CNF over a finite variable type, width at most k ≥ 3, uniform start \
    and 3n local-search steps. Lower bound ((k-1)/k)^(k-3) · (k/(2(k-1)))^n / \
    (3n+1). Explicit factors are this formalization’s constants; no native runtime \
    assertion."

register_result "ov-sat-transfer" where
  title := "Williams split-and-list transfer from OV to SAT"
  topic := "fine-grained complexity"
  sources := [
    { paper := Williams2005, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.DecidableInTimeO.decidableInExpTime_SAT
  ]
  scope := "An OV decider of time N^(2-ε) times a polynomial in dimension yields native SAT \
    time of exponent 1 - min(ε,1)/2 in occurring variables, with polynomial \
    encoded-input overhead. This records the transfer, not the separate conditional \
    OVH result or logarithmic-dimension OVH."

register_result "native-sparsification" where
  title := "Native algorithmic consequence of sparsification"
  topic := "fine-grained complexity"
  sources := [
    { paper := ImpagliazzoPaturiZane2001, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.exists_decidableInExpTime_numVars_of_length
  ]
  scope := "For fixed width k and ε > 0, some natural c transfers a k-SAT decider of \
    clause-count exponent δ ≥ 0 to variable-count exponent ε + cδ. Native machines, \
    encCNF and polynomial encoded-length overhead; no new sharp sparsification \
    constant."

