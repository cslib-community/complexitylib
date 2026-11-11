/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Algorithms.Lean.MaxDicut.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamsonMaxTwoSAT
import CslibFrontier.Algorithms.WordRAM.Schoening.Amplify
import CslibFrontier.Computability.Circuit.Arithmetic.CircuitLowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters
import CslibFrontier.Computability.Circuit.Boolean.BarringtonClass
import CslibFrontier.Computability.Circuit.Boolean.Braverman.Fooling
import CslibFrontier.Computability.Circuit.Boolean.Formula.Andreev
import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
import CslibFrontier.Computability.Circuit.Boolean.Khrapchenko
import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.Generator
import CslibFrontier.Computability.Circuit.Boolean.Smolensky
import CslibFrontier.Computability.Communication.Discrepancy
import CslibFrontier.Computability.Communication.Disjointness
import CslibFrontier.Computability.Complexity.Classes.Alternation.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Alternation.SpaceGame
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Translational
import CslibFrontier.Computability.Complexity.Classes.IP.Shamir
import CslibFrontier.Computability.Complexity.Classes.Ladner.Density
import CslibFrontier.Computability.Complexity.Classes.LogSpace.Complement
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.DeterministicTransitiveClosure.Converse
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reachability
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Converse
import CslibFrontier.Computability.Complexity.Classes.LogSpace.PolyTime
import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
import CslibFrontier.Computability.Complexity.Classes.PH.SipserLautemann
import CslibFrontier.Computability.Complexity.Classes.SharpP.Lowness
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Savitch
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineCollapse
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SOPLCollapse
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Williams
import CslibFrontier.Computability.Complexity.Classes.Toda
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Fagin.Converse
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeEndpoint
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeModelCount
import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
import CslibFrontier.Computability.Complexity.FineGrained.PPZ
import CslibFrontier.Computability.Complexity.FineGrained.Schoening
import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
import CslibFrontier.Computability.Complexity.Gradel
import CslibFrontier.Computability.Complexity.ImmermanVardi
import CslibFrontier.Computability.Complexity.Problems.Primes
import CslibFrontier.Computability.Kolmogorov.Incompleteness
import CslibFrontier.Computability.Kolmogorov.MINKT
import CslibFrontier.Computability.Kolmogorov.MKtP
import CslibFrontier.Computability.Kolmogorov.SymmetryOfInformation
import CslibFrontier.Computability.MCSP.AntiChecker
import CslibFrontier.Computability.MCSP.FormulaMagnification
import CslibFrontier.Computability.MCSP.FormulaMagnification.AverageCase
import CslibFrontier.Computability.MCSP.FormulaMagnification.Locality
import CslibFrontier.Computability.MCSP.FormulaMagnification.StretchedExponential
import CslibFrontier.Computability.MCSP.FormulaMagnification.Subexponential
import CslibFrontier.Computability.MCSP.FormulaMagnification.SublinearAverageCase
import CslibFrontier.Computability.MCSP.HardnessConsequences
import CslibFrontier.Computability.MCSP.Magnification
import CslibFrontier.Computability.MCSP.Magnification.GapMCSP
import CslibFrontier.Computability.MCSP.PartialETH
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Computability.QueryComplexity.Quantum.NayakWuConsequences
import CslibFrontier.Crypto.Computational.Nonuniform.ZeroKnowledge
import CslibFrontier.Crypto.Computational.OneWay.LiuPass
import CslibFrontier.Crypto.Computational.OneWay.MCSP
import CslibFrontier.Crypto.Computational.OneWayToPRF
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CFI
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ColorRefinement
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.WeisfeilerLeman
import CslibFrontier.GameTheory.Bimatrix.Existence
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Median
import CslibFrontier.GameTheory.Strategic.Correlated
import CslibFrontier.GameTheory.Strategic.Nash
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.GraphProperties
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Monadic
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CFI
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
import CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka
import CslibFrontier.Logics.FirstOrder.FiniteVariable.WeisfeilerLeman
import CslibFrontier.Logics.FirstOrder.Locality.GraphProperties
import CslibFrontier.Logics.FirstOrder.Locality.Hanf
import CslibFrontier.Logics.FirstOrder.Locality.Reachability
import CslibFrontier.Logics.FirstOrder.Operator.TransitiveClosure.Expressiveness
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.CNF
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.Coloring
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.IndependentSetReduction
import CslibFrontier.Logics.FirstOrder.Ordered.Problems.SizedGraph
import CslibFrontier.Logics.FirstOrder.Ordered.Projection.Reduction
import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Binary
import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Sentence
import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Undecidability
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.BinomialRandomGraph
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Rado
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational
import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole
import CslibFrontier.Logics.SecondOrder.WordMSO.McNaughtonPapert
import CslibFrontier.Logics.SecondOrder.WordMSO.OfRegular
import CslibFrontier.Logics.SecondOrder.WordMSO.Separation
import CslibFrontier.Logics.SecondOrder.WordMSO.StarFree
import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import CslibFrontier.Probability.Extractor.TwoSource

/-!
# Collected results

These scopes and source correspondences were inspected against existing repository statements
and citations. They are not a new primary-source audit. `unverified` means a source theorem
name/number or precise locator has not yet been collected; it must not be guessed.

## Headline results

The results that the curated formal abstracts selected until their retirement on 2026-11-08,
registered against the library theorems that the abstracts' bridges applied. A group whose
theorems live in several modules is split into one entry per module. Bibliography keys come from
the citations of the defining modules. The depth-two threshold bounds for Andreev's function are
left out: they are original results, which `results/README.md` admits only once original results
have an explicit representation.
-/

register_result "cook-levin" where
  title := "Cook–Levin: SAT is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak09, theorem := unverified, locator := unverified },
    { paper := Papadimitriou94, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.CookLevin.SAT_npComplete,
    Cslib.Complexity.CookLevin.UNSAT_coNPComplete
  ]
  scope := "SAT and UNSAT over CNF formulas with natural-number variables under the explicit \
    framed encoding encCNF. NP uses one native multi-tape polynomial-time verifier with \
    certificates of exact polynomial length; hardness is under total native polynomial-time \
    many-one reductions from problems with arbitrary injective encodings. UNSAT \
    coNP-completeness follows by complementation."

register_result "pcp" where
  title := "The PCP theorem"
  topic := "interactive proofs"
  sources := [
    { paper := Dinur2007, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NP_eq_PCP_log
  ]
  scope := "NP = PCP(log n, 1) for every injective instance encoding. The verifier's coin \
    count, nonadaptive proof addresses and verdict are each computable in polynomial time; it \
    uses O(log n + 1) random bits and O(1) queries, with perfect completeness and soundness at \
    most one half. NP is the library's deterministic-verifier class. Construction constants \
    are large."

register_result "fagin" where
  title := "Fagin: logic captures NP"
  topic := "descriptive complexity"
  sources := [
    { paper := Fagin1974, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP
  ]
  scope := "A class of finite structures over a relational language with a finite vocabulary is \
    existential second-order definable iff it is isomorphism-closed and its query language is \
    in NP under the explicit structure encoding encStructure. No further hypotheses: empty \
    universes and nullary relations are included."

register_result "savitch" where
  title := "Savitch: NPSPACE equals PSPACE"
  topic := "space complexity"
  sources := [
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NPSPACE_eq_PSPACE
  ]
  scope := "Class equality for arbitrary injective encodings. PSPACE is total deterministic \
    decision by one native multi-tape machine in polynomial work space; NPSPACE uses one \
    finite-state nondeterministic machine whose every computation prefix respects a \
    polynomial space bound and whose branches all halt. The parameterized quadratic-space \
    simulation is the separate entry savitch-general."

register_result "savitch-general" where
  title := "Savitch: NSPACE(s) is contained in DSPACE(s²)"
  topic := "space complexity"
  sources := [
    { paper := Savitch1970, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := "Theorem 8.5",
      locator := "Section 8.4, final paragraph (p. 351)" },
    { paper := AroraBarak09, theorem := "Theorem 4.14", locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NSPACE_subset_DSPACE_sq,
    Cslib.Complexity.mem_DSPACE_sq_of_recognizesInSpace
  ]
  scope := "NSPACE(s) ⊆ DSPACE(s²) for every s with log₂ n ≤ s(n); no constructibility \
    assumed. One finite-state native nondeterministic machine per problem, work space \
    c₁·s(n) + c₂ along every computation prefix; the recognizer form permits nonterminating \
    branches. The deterministic machine halts on every input and reads its input in place; \
    arbitrary injective encodings."

register_result "space-hierarchy" where
  title := "Stearns–Hartmanis–Lewis: the deterministic space hierarchy"
  topic := "space complexity"
  sources := [
    { paper := StearnsHartmanisLewis1965, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.DSPACE_ssubset_DSPACE,
    Cslib.Complexity.L_ssubset_DSPACE_log2_sq
  ]
  scope := "DSPACE f ⊂ DSPACE g on binary words for space-constructible g with ⌊log₂ n⌋ ≤ g n \
    when every c·f(n)+c is eventually below g(n): the textbook gap and logarithmic threshold. \
    DSPACE is total deterministic decision by one native multi-tape machine within \
    O(s n) work cells. The nondeterministic space hierarchy is not part of this entry."

register_result "alternation" where
  title := "Chandra–Kozen–Stockmeyer: AP equals PSPACE"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.AP_eq_PSPACE
  ]
  scope := "One finite-state alternating multi-tape machine per problem (two transition \
    functions as in Arora–Barak, least-fixed-point acceptance), every computation path halting \
    within polynomial time; PSPACE is deterministic polynomial space; arbitrary injective \
    encodings. AL = P is not included: the library proves only AL ⊆ P."

register_result "alternation-apspace-exp" where
  title := "Chandra–Kozen–Stockmeyer: APSPACE equals EXP"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.APSPACE_eq_EXP
  ]
  scope := "One finite-state alternating multi-tape machine per problem with least-fixed-point \
    acceptance, polynomial work space along every computation prefix and every branch halting; \
    EXP is deterministic decision within c₁·2^(n^d) + c₂ steps, with any space bound; \
    arbitrary injective encodings."

register_result "alternation-aspace-dtime" where
  title := "Chandra–Kozen–Stockmeyer: alternating space s is within deterministic time 2^O(s)"
  topic := "space complexity"
  sources := [
    { paper := ChandraKozenStockmeyer1981, theorem := unverified, locator := "Section 3" },
    { paper := Sipser2013, theorem := unverified, locator := "Section 10.3" }
  ]
  theorems := [
    Turing.MultiTapeATM.RecognizesInSpace.mem_DTIME,
    Cslib.Complexity.exists_mem_DTIME_of_mem_ASPACE,
    Cslib.Complexity.exists_mem_DTIME_of_mem_ASPACE_of_log2_le
  ]
  scope := "One finite-state alternating multi-tape machine per problem with least-fixed-point \
    acceptance and work space s(n) (RecognizesInSpace.mem_DTIME, branches need not halt) or \
    c₁·s(n) + c₂ with every branch halting (ASPACE) along every computation prefix; DTIME is \
    deterministic decision within c₁·2^(c·(log₂ n + s(n) + 1)) + c₂ steps, or 2^(c·s(n)) when \
    log₂ n ≤ s(n); no constructibility hypothesis; the converse inclusion is not included; \
    arbitrary injective encodings."

register_result "nspace-dtime" where
  title := "Nondeterministic space s is within deterministic time 2^O(s)"
  topic := "space complexity"
  sources := [
    { paper := AroraBarak09, theorem := unverified, locator := "Section 4.1" },
    { paper := Sipser2013, theorem := unverified, locator := "Section 8.4" }
  ]
  theorems := [
    Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE,
    Cslib.Complexity.exists_mem_DTIME_of_mem_NSPACE_of_log2_le,
    Turing.MultiTapeNTM.RecognizesInSpace.mem_DTIME
  ]
  scope := "One finite-state binary nondeterministic multi-tape machine per problem with \
    work space c₁·s(n) + c₂ along every computation prefix; the recognizer form permits \
    nonterminating branches. DTIME is deterministic decision within \
    c₁·2^(c·(log₂ n + s(n) + 1)) + c₂ steps, or 2^(c·s(n)) when log₂ n ≤ s(n); no \
    constructibility hypothesis, unlike the source's space-constructible S; arbitrary \
    injective encodings."

register_result "reingold" where
  title := "Reingold: undirected reachability is in L"
  topic := "space complexity"
  sources := [
    { paper := Reingold2008, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.USTCON_mem_L
  ]
  scope := "Simple undirected graphs encoded by a unary header 1^n 0 1^s 0 1^t 0 and the \
    row-major adjacency matrix (encUSTCON). One native machine halts on and decides every \
    encoded instance of length L within c·(⌊log₂ L⌋ + 1) work cells; malformed inputs are \
    unconstrained. The reduction-defined SL = L corollary is not part of this entry."

register_result "primes" where
  title := "Agrawal–Kayal–Saxena: PRIMES is in P"
  topic := "algorithms"
  sources := [
    { paper := AKS2004, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.primes_mem_P
  ]
  scope := "Naturals in binary, least significant digit first (encNat); native multi-tape P \
    with polynomial time and space. The decider is the AKS algorithm with integer thresholds \
    on the word RAM, simulated by a Turing machine; no exponent is stated."

register_result "immerman-szelepcsenyi" where
  title := "Immerman–Szelepcsényi: nondeterministic space is closed under complement"
  topic := "space complexity"
  sources := [
    { paper := Immerman1988, theorem := unverified, locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NSPACE_eq_coNSPACE
  ]
  scope := "NSPACE(s) = coNSPACE(s) for every s with log₂ n ≤ s(n); no constructibility \
    assumed. One finite-state native machine per problem, work space c₁·s(n) + c₂ along every \
    computation prefix, every branch terminating, arbitrary injective encodings."

register_result "immerman-szelepcsenyi-nl" where
  title := "Immerman–Szelepcsényi: NL equals coNL"
  topic := "space complexity"
  sources := [
    { paper := Immerman1988, theorem := unverified, locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NL_eq_coNL
  ]
  scope := "NL = coNL for the native class NL (one finite-state machine, work space \
    c·(⌊log₂ n⌋ + 1) along every computation prefix, every branch halting) and arbitrary \
    injective encodings: the case s = log₂ of the nondeterministic-space theorem."

register_result "shamir" where
  title := "Shamir: IP equals PSPACE"
  topic := "interactive proofs"
  sources := [
    { paper := Shamir1992, theorem := unverified, locator := unverified },
    { paper := Shen1992, theorem := unverified, locator := unverified },
    { paper := LundFortnowKarloffNisan1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.IP_eq_PSPACE
  ]
  scope := "IP with private fair coins: one oracle-machine verifier under a strict polynomial \
    clock, completeness 2/3 and soundness 1/3 quantified over every stateful prover; PSPACE is \
    decided by one deterministic machine in polynomial space; arbitrary injective encodings."

register_result "toda" where
  title := "Toda: a counting oracle decides the polynomial hierarchy"
  topic := "counting classes"
  sources := [
    { paper := Toda1991, theorem := unverified, locator := unverified },
    { paper := AroraBarak09, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.PH_subset_PWithSharpPOracle
  ]
  scope := "PH ⊆ P^#P, where P^#P is one polynomial-time oracle program that is correct against \
    every oracle language answering the bits of some #P function (explicit witness counts). \
    The class does not count queries; the construction asks a single one. PH uses \
    polynomial-time alternating verifiers; arbitrary injective encodings."

register_result "bqp-pp" where
  title := "Adleman–DeMarrais–Huang: BQP is contained in PP"
  topic := "quantum complexity"
  sources := [
    { paper := AdlemanDeMarraisHuang1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.BQP_subset_PP
  ]
  scope := "BQP: bounded-error (2/3 versus 1/3) polynomial-time uniform families of circuits \
    over the fixed gate set {Hadamard, NOT, CNOT, Toffoli}, generated from n in unary, \
    accepting by measuring qubit 0 from the zero-padded input; PP is native multi-tape strict \
    majority over certificates. Equivalence to textbook BQP over arbitrary elementary gates \
    (universality, Solovay–Kitaev) is not formalized."

register_result "barrington" where
  title := "Barrington: five states capture NC¹"
  topic := "circuit complexity"
  sources := [
    { paper := Barrington1989, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.NC_one_eq_polyLength_perm_five
  ]
  scope := "Class equality for languages over Bool: nonuniform polynomial-size De Morgan \
    circuits of depth O(log n + 1), every gate counted, versus polynomial-length permutation \
    programs over S₅ with length-dependent acceptance sets. No uniform generator or compiler \
    runtime is asserted."

register_result "constant-depth" where
  title := "Håstad: parity resists shallow circuits"
  topic := "circuit complexity"
  sources := [
    { paper := Hastad1986, theorem := unverified, locator := unverified },
    { paper := Jukna2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Unbounded.two_pow_le_size_of_computes_parity_of_depthWith_le
  ]
  scope := "A circuit of NOT and unbounded fan-in AND/OR gates of AND/OR depth at most d \
    (negations free in depth) computing parity of n bits has at least 2^s gates whenever \
    s ≥ 2 and 17s(16s + 1)^(d - 2) ≤ n (truncated subtraction); size counts every gate, \
    including NOT and constants. Explicit finite bound with the sharp exponent 1/(d - 1); \
    nonuniform."

register_result "constant-depth-mod-p" where
  title := "Razborov–Smolensky: parity resists shallow circuits with MOD p gates"
  topic := "circuit complexity"
  sources := [
    { paper := Razborov1987, theorem := unverified, locator := unverified },
    { paper := Smolensky1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Smolensky.two_mul_two_pow_le_size_of_computes_parity
  ]
  scope := "For an odd prime p, a circuit of NOT, unbounded fan-in AND/OR and MOD_p gates (true \
    when the number of true inputs is nonzero mod p) of depth d computing parity of n bits \
    satisfies 2·2^ℓ ≤ 5·size whenever ℓ ≥ 1 and 100(((p - 1)ℓ)^d + 1)² ≤ n + 1. Depth and \
    size count every gate, including NOT and constants; nonuniform."

register_result "braverman" where
  title := "Braverman: polylogarithmic independence fools AC⁰"
  topic := "circuit complexity"
  sources := [
    { paper := Braverman2010, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Braverman.fools_of_isKWiseIndependent
  ]
  scope := "A circuit of NOT and unbounded fan-in AND/OR gates of depth at most d, with at most \
    2^q gates, each of fan-in below 2^q (q ≥ 1), is fooled with error 2^(-q) in expectation by \
    every k-wise independent distribution (vanishing biases on nonempty sets of at most k \
    coordinates) once k ≥ (64q)^((2d + 3)(d + 7) + 1). Our own constants and exponent, weaker \
    than Braverman's; size and depth count NOT gates and constants; nonuniform and \
    information-theoretic."

register_result "formula-bounds" where
  title := "Formula lower bounds: Khrapchenko's quadratic bound for parity"
  topic := "circuit complexity"
  sources := [
    { paper := Khrapchenko1971, theorem := unverified, locator := unverified },
    { paper := Jukna2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.sq_le_leafSize_of_computes_parity
  ]
  scope := "Every De Morgan formula computing parity of n bits has at least n² input leaves, \
    counted with multiplicity. Formula size only; no general-circuit lower bound."

register_result "formula-bounds-andreev" where
  title := "Formula lower bounds: Andreev's function"
  topic := "circuit complexity"
  sources := [
    { paper := Andreev1987, theorem := unverified, locator := unverified },
    { paper := Jukna2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.pow_two_mul_pow_three_le_formulaSize_andreev_sq
  ]
  scope := "Some B exists such that for all b ≥ B and m ≥ ⌊log₂ b⌋ + 2, the minimum De Morgan \
    formula leaf size L of Andreev's function on 2^b + b·m bits (explicit block indexing) \
    satisfies 2^(2b)·m³ ≤ 144·b²·(⌊log₂ b⌋ + 2)³·L². Finite quantitative bound; no \
    general-circuit lower bound."

register_result "constant-depth-arithmetic" where
  title := "Limaye–Srinivasan–Tavenas over any field (after Forbes): constant-depth algebraic \
    circuits for IMM need superpolynomial size"
  topic := "algebraic complexity"
  sources := [
    { paper := LimayeSrinivasanTavenas2021, theorem := unverified, locator := unverified },
    { paper := Forbes2024, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.SPCircuit.eventually_pow_lt_size_of_imm,
    Cslib.Circuits.Arithmetic.SPCircuit.two_rpow_le_of_imm
  ]
  scope := "Any field, formal polynomials, unbounded fan-in sum and product gates, product gates \
    reading distinct wires, size counting all gates. For constant product-depth Δ and every c, \
    for all large n, IMM of d = ⌊log₂ ⌊log₂ n⌋⌋ generic n × n matrices needs more than n^c \
    gates; the explicit form gives 2^(k(d^(1/(4^Δ - 1))/20 - 1/2)) ≤ \
    smCost(d)^Δ·(size + N + 1)^(2Δ + 1) when 10d ≤ k, 2^k ≤ n and Δ ≥ 1. Nonuniform."

register_result "cryptography" where
  title := "One-way functions yield pseudorandom generators"
  topic := "cryptography"
  sources := [
    { paper := HILL1999, theorem := unverified, locator := unverified },
    { paper := Holenstein2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.OneWay.exists_pseudorandomGenerator
  ]
  scope := "Every uniform one-way function on bit strings yields a deterministic polynomial-time \
    generator stretching every input by one bit, secure against uniform strict probabilistic \
    polynomial-time distinguishers with negligible advantage. Asymptotic security; no \
    optimized seed length; not a concrete implementation audit."

register_result "cryptography-prf" where
  title := "One-way functions yield adaptively secure pseudorandom functions"
  topic := "cryptography"
  sources := [
    { paper := GGM1986, theorem := unverified, locator := unverified },
    { paper := Holenstein2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.OneWay.exists_pseudorandomFunction
  ]
  scope := "Every uniform one-way function yields a length-preserving keyed family with a \
    deterministic polynomial-time evaluator, indistinguishable from a random function by \
    uniform adaptive oracle PPT adversaries with full stateful oracle semantics (negligible \
    advantage); via the one-way-to-PRG theorem and the GGM construction. Asymptotic security."

register_result "resolution" where
  title := "Haken: pigeonhole formulas require long resolution proofs"
  topic := "proof complexity"
  sources := [
    { paper := Haken1985, theorem := unverified, locator := unverified },
    { paper := BeamePitassi1996, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole
  ]
  scope := "Every line-based resolution refutation of the non-onto pigeonhole formula \
    PHP^(n+1)_n has at least 2^⌊n/24⌋ lines, by the Beame–Pitassi bottleneck argument. Proof \
    size is not solver runtime."

register_result "communication" where
  title := "Communication: disjointness resists randomness"
  topic := "communication complexity"
  sources := [
    { paper := KalyanasundaramSchnitger1992, theorem := unverified, locator := unverified },
    { paper := Razborov1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Communication.PublicCoin.le_mul_ecomplexityFun_disjointness_add
  ]
  scope := "n ≤ 2^16·R + 2^12 in ℕ∞, where R is the public-coin complexity of disjointness on \
    n-bit strings with error 1/3: the least, over distributions on binary protocol trees with \
    error at most 1/3 on every input pair, of the largest tree depth in the support (depth \
    counts unreachable branches). Stated for this infimum rather than per protocol."

register_result "communication-inner-product" where
  title := "Communication: inner product resists randomness"
  topic := "communication complexity"
  sources := [
    { paper := ChorGoldreich1988, theorem := unverified, locator := unverified },
    { paper := KushilevitzNisan1997, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Communication.PublicCoin.le_two_mul_ecomplexityFun_dotProduct_add_three
  ]
  scope := "n ≤ 2·R + 3 in ℕ∞, where R is the public-coin complexity with error 1/3 of the \
    inner product modulo two of n-bit strings (least worst-case tree depth over distributions \
    on protocol trees with per-input error at most 1/3), via the discrepancy method. Stated \
    for this infimum rather than per protocol."

register_result "sipser-lautemann" where
  title := "Sipser–Gács–Lautemann: BPP lies in the second polynomial level"
  topic := "randomized complexity"
  sources := [
    { paper := Sipser1983, theorem := unverified, locator := unverified },
    { paper := Lautemann1983, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.BPP_subset_SigmaP_two_inter_PiP_two
  ]
  scope := "BPP ⊆ Σ₂ ∩ Π₂ for arbitrary injective encodings: BPP uses a total native \
    polynomial-time test on fair random strings, correct with probability at least 2/3 on every \
    input; Σ₂ and Π₂ use total native polynomial-time tests with explicit polynomial \
    quantifier blocks. No derandomization assumption."

register_result "chor-goldreich" where
  title := "Chor–Goldreich: the inner product extracts from two weak sources"
  topic := "randomized complexity"
  sources := [
    { paper := ChorGoldreich1988, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Probability.isTwoSourceExtractor_dotProduct,
    Cslib.Probability.sum_mul_abs_bias_dotProduct_le,
    Cslib.Probability.exists_minEntropy_bind_dotProduct_eq_pure
  ]
  scope := "Bit strings indexed by a finite type of size n and arbitrary independent sources \
    with real min-entropy bounds k₁ and k₂: the inner product modulo two is within statistical \
    distance 2^((n - k₁ - k₂)/2)/2 of a uniform bit; the strong form bounds the average bias \
    over the second source by 2^((n - k₁ - k₂)/2); orthogonal uniform sources show the bound \
    fails at k₁ + k₂ = n. Information-theoretic; no running time asserted."

register_result "schoening" where
  title := "Schöning: 3-SAT in time (4/3)^n on the randomized word RAM"
  topic := "SAT algorithms"
  sources := [
    { paper := Schoening1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.WordRAM.Schoening.ampProgram_spec,
    Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_eq,
    Cslib.Algorithms.WordRAM.Schoening.ampProgram_failure_le_exp,
    Cslib.Algorithms.WordRAM.Schoening.ampTime_le
  ]
  scope := "One fixed program of the library's unit-cost randomized word RAM over the standard \
    basis (truncated subtraction, x / 0 = 0, x % 0 = x; unit-cost rand), for every clause width \
    k ≥ 3 and words of O(log(n + k + L + c)) bits on input k :: c :: encode φ of length L: up \
    to R = ⌈(3n + 1)(2(k - 1)/k)^n (k/(k - 1))^(k - 3)⌉·c trials, every path halting within \
    900(n + k + L + 1)³(2 - 2/k)^n(c + 1) steps, no false positives, failure probability \
    exactly (1 - p)^R and at most e^(-c) on satisfiable k-CNFs. k = 3 gives (4/3)^n; not PPSZ."

register_result "subexponential-sat" where
  title := "OpenAI: the Exponential Time Hypothesis is false"
  topic := "fine-grained complexity"
  sources := [
    { paper := OpenAI2026ETH, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.CountingNativeEndpoint.decidableInSubexpTime_KSAT,
    Cslib.Complexity.CountingNativeEndpoint.satExponent_eq_zero,
    Cslib.Complexity.CountingNativeEndpoint.not_ETH,
    Cslib.Complexity.CountingNativeEndpoint.not_SETH
  ]
  scope := "For every fixed clause width k, k-SAT under the explicit binary encoding encCNF is \
    decidable by native machines in time 2^(δn)·poly(L) for every δ > 0, where n counts the \
    occurring variables and L is the encoded length; every fixed-width SAT exponent is zero; \
    the library's ETH and SETH are false. Interpolation-scale bound only, not the manuscript's \
    sharper headline runtime."

register_result "subexponential-sat-count" where
  title := "OpenAI: exact subexponential model counting for bounded-width CNF"
  topic := "SAT algorithms"
  sources := [
    { paper := OpenAI2026ETH, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.CountingNativeEndpoint.exists_modelCounter
  ]
  scope := "For each width k, one deterministic native machine computes the exact model count \
    of every CNF over ℕ whose clauses have at most k literals, in time \
    O(⌈2^(A·s(n))⌉·(L + 1)^e) and space O((L + 1)^b) for constants A, e, b, where n is the \
    number of variables, L the length of encCNF φ and s(n) = n(log log(n + 16))²/√log(n + 16) \
    the interpolation scale. Not the manuscript's sharper headline runtime."

register_result "partial-mcsp" where
  title := "Ilango: Partial MCSP is hard under the Exponential Time Hypothesis"
  topic := "meta-complexity"
  sources := [
    { paper := Ilango2020FOCS, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_tableSize,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_encBinary,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate,
    Cslib.Complexity.ETH.not_decidableInSubexpTime_PartialMCSP_binaryGate_encBinary
  ]
  scope := "Under the library's ETH, PartialMCSP on m-variable partial truth tables is not \
    decidable by deterministic multi-tape machines in time 2^o(m log m) = N^o(log log N), \
    N = 2^m, with explicit unary or binary size-threshold encodings and De Morgan all-gate or \
    binary-gate cost. Conditional: the library also refutes ETH (subexponential-sat), so the \
    premise is false; the implications remain valid."

register_result "magnification" where
  title := "McKay–Murray–Williams: barely superlinear circuit lower bounds for MCSP separate P \
    from NP"
  topic := "meta-complexity"
  sources := [
    { paper := McKayMurrayWilliams2019, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MCSP.not_NP_subset_PPoly_of_yesSet_pow_hard,
    Cslib.MCSP.P_ne_NP_of_yesSet_pow_hard,
    Cslib.MCSP.exists_complexity_yesSet_le_of_NP_subset_PPoly,
    Cslib.MCSP.exists_complexity_yesSet_pow_le_of_NP_subset_PPoly
  ]
  scope := "If NP ⊆ P/poly (bit-string languages, native multi-tape NP), decision MCSP[s] on \
    2^n-bit truth tables in standard binary order has De Morgan circuits of size \
    2^n·c·(n + s(n) + 1)^c, counting all operation gates. Hence if for some k and every c > 0 \
    some 2^n-bit slice of MCSP[n^k] needs more than 2^n·c·(n + 1)^c gates, then NP ⊄ P/poly \
    and P ≠ NP. Size-only lower-bound hypothesis."

register_result "gap-mcsp-magnification" where
  title := "Oliveira–Pich–Santhanam: N^(1+ε) lower bounds for Gap-MCSP imply NP ⊄ P/poly"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraPichSanthanam2019, theorem := "Theorem 1.4 (ECCC TR18-158 Theorem 4)",
      locator := unverified }
  ]
  theorems := [
    Cslib.MCSP.not_NP_subset_PPoly_of_gapMCSP_hard,
    Cslib.MCSP.P_ne_NP_of_gapMCSP_hard,
    Cslib.MCSP.exists_gapMCSP_separator_of_NP_subset_PPoly
  ]
  scope := "If for some ε > 0 and every small enough β > 0 (eventually as β → 0⁺), for \
    infinitely many n no Boolean function on 2^n-bit truth tables that accepts every \
    yes-instance and rejects every no-instance of Gap-MCSP[⌊2^(βn)/(10n)⌋₊, ⌊2^(βn)⌋₊] has \
    De Morgan complexity at most N^(1+ε) (N = 2^n, all operation gates counted), then \
    NP ⊄ P/poly and P ≠ NP. The source's constant c = 10. Proof route: the \
    McKay–Murray–Williams circuits for MCSP[s] under NP ⊆ P/poly separate Gap-MCSP[s₁, s₂] \
    whenever s₁ ≤ s₂; OPS's own proof through the efficient anti-checker (Lemma 4.1) is not \
    formalized."

register_result "matrix-multiplication" where
  title := "Matrix multiplication: the exponent is at most 9/4"
  topic := "algebraic complexity"
  sources := [
    { paper := Pass2026, theorem := unverified, locator := unverified },
    { paper := OpenAI2026MatrixMultiplication, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.MatrixMultiplication.admissibleExponent_nine_quarters,
    Cslib.Circuits.Arithmetic.MatrixMultiplication.omega_le_nine_quarters
  ]
  scope := "Over every field of characteristic zero, every τ > 9/4 is an admissible exponent: \
    for every ε > 0, exact n × n matrix multiplication has nonuniform arithmetic circuits of \
    at most c·n^(τ + ε) gates, addition, multiplication and constant gates each charged one, \
    inputs and outputs free; hence ω ≤ 9/4. No uniform generation, explicit constants or \
    integer bit complexity."

/-! ## Further collected results -/

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

register_result "ladner-density" where
  title := "Ladner's density theorem for polynomial-time many-one reducibility"
  topic := "structural complexity"
  sources := [
    { paper := Ladner1975a, theorem := unverified, locator := unverified },
    { paper := Schoening1982, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.exists_isDecidable_notMem_P_lt,
    Cslib.Complexity.exists_mem_NP_notMem_P_lt,
    Cslib.Complexity.NPComplete.exists_NP_not_P_not_npComplete_lt,
    Cslib.Complexity.exists_isDecidable_between_of_notMem_P,
    Cslib.Complexity.exists_mem_NP_between_of_notMem_P
  ]
  scope := "Problems on binary words (encBits); total deterministic multi-tape polynomial-time \
    many-one reductions. Between any two problems A <ₘᵖ B on bit words with B decidable \
    (respectively A, B in NP) and B ∉ P, there is a decidable problem C (respectively in NP) \
    strictly between them; if P ≠ NP, every NP-complete language on bit words has an \
    NP-intermediate language strictly below it. Many-one (≤ₘᵖ) order and non-reductions only; \
    Ladner's polynomial-time Turing (≤ᵀᵖ) non-reduction and ≤ᵀᵖ-density forms are not included. \
    The hypothesis B ∉ P is required (∅ <ₘᵖ {[true]} has no intermediate)."

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

register_result "williams-square-root-space" where
  title := "Williams's square-root-space simulation of deterministic time"
  topic := "space complexity"
  sources := [
    { paper := Williams2025, theorem := "Theorem 1.1",
      locator := "arXiv:2502.17779v1, Section 3" }
  ]
  theorems := [
    Cslib.Complexity.DTIME_subset_DSPACE_sqrt
  ]
  scope := "For every time bound t(n) >= n and arbitrary injective input encoding, \
    DTIME(t) is contained in DSPACE(Nat.sqrt(t * (Nat.log2(t) + 1))). Finite binary \
    multitape machines, read-only input and visited-work-cell space; classes absorb \
    affine constants. No time-constructibility or monotonicity hypothesis."

register_result "blum-mansour-swap-regret" where
  title := "Blum–Mansour reduction from swap regret to external regret"
  topic := "online learning"
  sources := [
    { paper := BlumMansour2007, theorem := "Theorem 5 and Corollary 7", locator := "p. 1313" },
    { paper := Roughgarden2013CS364A, theorem := "Theorem 2.1",
      locator := "Lecture 18, Section 2, pp. 3–5" }
  ]
  theorems := [
    Cslib.MachineLearning.OnlineLearning.Experts.swap_regret_le_sum_regret,
    Cslib.MachineLearning.OnlineLearning.Experts.blumMansour_swap_regret_le,
    Cslib.MachineLearning.OnlineLearning.Experts.blumMansour_swap_regret_le_sqrt
  ]
  scope := "Experts setting with a finite set of n actions and arbitrary real loss sequences. \
    The reduction assumes the learner plays a stationary vector of the copies' distributions \
    and that copy j has regret at most R j on the losses scaled by the learner's probability of \
    j; it then bounds the swap regret against every swapping function by the sum of the R j. \
    With Hedge copies and losses in [-1, 1], swap regret is at most η T + n ln n / η, and \
    2 √(T n ln n) with the tuned rate when n ≥ 2 and T ≥ n ln n. Stationary vectors are \
    chosen classically; no running time is charged."

register_result "gmw-zero-knowledge" where
  title := "Goldreich–Micali–Wigderson auxiliary-input zero-knowledge proofs for NP"
  topic := "cryptography"
  sources := [
    { paper := GoldreichMicaliWigderson1991, theorem := unverified,
      locator := unverified },
    { paper := Goldreich2001, theorem := unverified,
      locator := "Sections 4.3.3 and 4.4" }
  ]
  theorems := [
    Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_mem_NP,
    Cslib.Crypto.NonuniformOneWay.exists_zkProof_of_npRelation
  ]
  scope := "From any nonuniformly one-way function, every language L in NP and every \
    NPRelation R admits a sequentially amplified ZKProof system (adapted masked-3SAT \
    protocol) with soundness (1/3)^(n+1), NegligibleSoundness, and auxiliary-input zero \
    knowledge in family-indexed, unbounded-auxiliary-input, and Goldreich instance-indexed \
    forms; the relation version preserves R's native witnesses via a Levin reduction."

register_result "nash-existence" where
  title := "Nash's theorem: every finite game has a mixed Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := "Theorem 1", locator := "p. 288" },
    { paper := Roughgarden2013CS364A, theorem := unverified,
      locator := "Lecture 13, Section 3.3, p. 5" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.exists_isMixedNash
  ]
  scope := "Finite cost-minimization games: finitely many players, each with a finite nonempty \
    set of pure strategies and real-valued costs. A mixed Nash equilibrium is a profile of \
    probability vectors under which no player lowers its expected cost under the product \
    distribution by a pure deviation. Proved by Brouwer's theorem on products of simplices, \
    itself derived from the hypergrid Sperner lemma. Nonconstructive: no algorithm or \
    complexity bound."

register_result "correlated-equilibrium-hierarchy" where
  title := "Pure Nash, mixed Nash, correlated and coarse correlated equilibria are nested"
  topic := "game theory"
  sources := [
    { paper := Roughgarden2013CS364A, theorem := unverified,
      locator := "Lecture 13, Section 3 and Figure 2; Lecture 18, Section 1" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.isCorrelatedEquilibrium_iff,
    Cslib.GameTheory.CostGame.IsPureNash.isCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.IsMixedNash.isCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.IsCorrelatedEquilibrium.isCoarseCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.exists_isCorrelatedEquilibrium
  ]
  scope := "Finite cost-minimization games and finitely supported distributions on profiles. \
    Correlated equilibria are defined by switching functions and shown equivalent to the \
    conditional form. Strictness of the inclusions is checked on examples in the test suite \
    (traffic light, Rock-Paper-Scissors), not stated as library theorems. Swap regret and \
    convergence of learning dynamics are not covered."

register_result "nash-existence-bimatrix" where
  title := "Every bimatrix game has a Nash equilibrium"
  topic := "game theory"
  sources := [
    { paper := Nash1951, theorem := "Theorem 1", locator := "p. 288" }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixGame.exists_isNash
  ]
  scope := "Real payoff matrices over finite nonempty strategy sets, with no nondegeneracy \
    assumption; derived from the n-player theorem. Nonconstructive."

register_result "facility-location-random-dictatorship" where
  title := "Random dictatorship is strategyproof and (2 - 2 / n)-approximate for social cost"
  topic := "game theory"
  sources := [
    { paper := AlonFeldmanProcacciaTennenholtz2010, theorem := "Theorem 3.1",
      locator := "Section 3.2 and first remark, arXiv:0907.2049v1 pp. 6–7" }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.randomDictatorship_isStrategyProof,
    Cslib.GameTheory.FacilityLocation.randomDictatorship_hasApproxRatio,
    Cslib.GameTheory.FacilityLocation.randomDictatorship_hasApproxRatio_two
  ]
  scope := "Any nonempty finite agent index set ι and Borel-measurable pseudometric space G \
    ([PseudoMetricSpace G] [OpensMeasurableSpace G]); slightly generalizes AFPT Theorem 3.1 \
    and its first remark from graph/metric spaces to pseudometrics. Weak group strategyproofness \
    fails on a 3-leaf star metric (Star4 in CslibFrontierTests.FacilityLocation, per §3.2 third \
    remark), and strong group strategyproofness fails on ℝ for n = 3."

register_result "facility-location-median" where
  title := "Fixed order-statistic and median mechanisms on ℝ are group strategyproof and optimal"
  topic := "game theory"
  sources := [
    { paper := ProcacciaTennenholtz2013, theorem := unverified,
      locator := "Section 3.1, pp. 18:7–18:8 (unnumbered prose)" },
    { paper := Moulin1980, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.orderStatisticMechanism_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.medianMechanism_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.lowerMedian_isOptimal,
    Cslib.GameTheory.FacilityLocation.medianMechanism_hasApproxRatio_one
  ]
  scope := "Any nonempty finite agent set ι locating a single facility on ℝ with sum-of-distances \
    social cost; orderStatisticMechanism k clamps k at |ι| - 1 when k ≥ |ι|. PT §3.1 states \
    weak group strategyproofness (attributed to Moulin 1980, uninspected here) and optimality \
    for the lower median x_((n-1)/2); the library proves the stronger IsGroupStrategyProof \
    property."

/-!
## Descriptive complexity and finite model theory

Capture theorems, undecidability in the finite, 0-1 laws, logic on words, and the game and
locality methods for nondefinability. Source theorem numbers and locators are copied from the
defining modules' documentation. Refinements and remarks that those modules present as their own
are not registered.
-/

register_result "immerman-vardi" where
  title := "Immerman–Vardi: FO(LFP) captures polynomial time on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1986, theorem := "Theorem 1", locator := "Section 3" }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.lfpDefinable_iff_encodedLanguage_mem_P,
    Cslib.Logic.FO.Ordered.LFPDefinable.of_encodedLanguage_mem_P
  ]
  scope := "Queries over a finite relational vocabulary on canonically ordered structures Fin n \
    with n ≥ 2. Order, BIT, 0, 1 and max are canonical numeric symbols computed from n, not \
    input tables. A query is defined by one checked FO(LFP) sentence iff its language is in \
    native P under encStructure (unary cardinality, then framed truth tables); malformed \
    table shapes and universes below two are rejected."

register_result "gradel-so-horn-captures-p" where
  title := "Grädel: SO∃-Horn captures polynomial time on ordered structures with successor"
  topic := "descriptive complexity"
  sources := [
    { paper := Gradel2007, theorem := "Theorems 3.2.17–3.2.18 and Exercise 3.2.20",
      locator := "Section 3.2.3, pp. 147–148" },
    { paper := Gradel1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.hornDefinable_iff_encodedLanguage_mem_P,
    Cslib.Logic.FO.Ordered.HornDefinable.encodedLanguage_mem_P,
    Cslib.Logic.FO.Ordered.HornDefinable.of_encodedLanguage_mem_P
  ]
  scope := "Queries over a finite relational vocabulary on canonically ordered structures Fin n \
    with n ≥ 2. HornDefinable asks for one SO∃-Horn sentence with quantifier-free guards over \
    language (succLanguage L), supplying primitive non-wrapping successor alongside the \
    canonical numeric symbols (order, BIT, 0, 1 and max); hornDefinable_iff_exists_sentence \
    identifies this fragment with arbitrary first-order guards over language L. A query is \
    HornDefinable iff its language is in native P under encStructure; malformed table shapes \
    and universes below two are rejected."

register_result "fo-tc-nl" where
  title := "FO(TC) is contained in NL on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 3.1", locator := unverified },
    { paper := Immerman1988, theorem := "Corollary 3", locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.TCDefinable.encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.PosTCDefinable.encodedLanguage_mem_NL
  ]
  scope := "A query defined by one FO(TC) sentence over a finite relational vocabulary with the \
    canonical numeric symbols, on Fin n with n ≥ 2, is in native NL under encStructure; \
    malformed tables and cardinalities below two are rejected. Closure is reflexive \
    transitive closure on tuples of fixed width. Closures under negation are compiled \
    directly by inductive counting rather than by appeal to NL = coNL. The converse, \
    NL ⊆ FO(positive TC), is in the entry immerman-nl-capture."

register_result "immerman-nl-capture" where
  title := "Immerman: FO(TC) and FO(positive TC) capture NL on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 3.1", locator := unverified },
    { paper := Immerman1988, theorem := "Corollary 3", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.tcDefinable_iff_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.posTCDefinable_iff_encodedLanguage_mem_NL
  ]
  scope := "Canonically ordered finite structures over a finite relational vocabulary, with \
    universes Fin n, n ≥ 2, and numeric symbols order, BIT, zero, one and maximum computed \
    from the size. One FO(TC) sentence defines the query iff its source-only encoded language \
    (encStructure) is in native NL; positive closures suffice. Malformed table shapes and \
    universes below two are rejected."

register_result "immerman-reach-nl-complete" where
  title := "Immerman: REACH is NL-complete under ordered first-order reductions"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 3.16 and Exercise 3.20",
      locator := "Chapter 3, pp. 64–66" }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.reduces_Reach_iff_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.reach_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.stReach_encodedLanguage_mem_NL,
    Cslib.Logic.FO.Ordered.reach_logSpaceComplete_NL
  ]
  scope := "Canonically ordered finite relational structures on Fin n (2 ≤ n) with built-in \
    ≤, BIT, 0, 1 and max, encoded at encStructure; native multi-tape NL with all-branches \
    halting. Reach is 0-to-max directed reachability over Language.graph (arbitrary binary \
    edge relation, self-loops permitted). Every ordered query in native NL reduces to Reach \
    by one positive-dimensional FullTupleInterpretation (hence Ordered.Reduces), and conversely \
    via positive FO(TC) pullback. Endpoint normalization covers arbitrary marked (s, t) \
    including s = t, and Reach is logspace interreducible with STCON (encSTCON). First-order \
    and quantifier-free projection refinements (≤_fop, ≤_qfp) are not formalized here."

register_result "fo-dtc-l" where
  title := "FO(DTC) is contained in L on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 4.2", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.DTCDefinable.encodedLanguage_mem_L
  ]
  scope := "A query defined by one FO(DTC) sentence over a finite relational vocabulary with the \
    canonical numeric symbols, on Fin n with n ≥ 2, is in native L under encStructure; \
    malformed tables and cardinalities below two are rejected. Deterministic closure is \
    reflexive transitive closure of the deterministic reduct on tuples of fixed width, \
    nested and at any polarity. The converse, L ⊆ FO(DTC), is in the entry \
    immerman-l-capture."

register_result "immerman-l-capture" where
  title := "Immerman: FO(DTC) captures L on ordered structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1987, theorem := "Theorem 4.2", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.dtcDefinable_iff_encodedLanguage_mem_L
  ]
  scope := "Canonically ordered finite structures over a finite relational vocabulary, with \
    universes Fin n, n ≥ 2, and numeric symbols order, BIT, zero, one and maximum computed \
    from the size. One FO(DTC) sentence defines the query iff its source-only encoded \
    language (encStructure) is in native L. Deterministic closure is reflexive transitive \
    closure of the deterministic reduct on tuples of fixed width. Malformed table shapes and \
    universes below two are rejected."

register_result "ordered-projection-reducibility" where
  title := "Immerman–Landau: ordered FO and QF projections compose and refine FO reductions"
  topic := "descriptive complexity"
  sources := [
    { paper := ImmermanLandau1995, theorem := "Proposition 3.7", locator := "Section 3" },
    { paper := Immerman1999, theorem := "Exercise 2.15(1)", locator := "Chapter 2, p. 36" }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.ProjectionReduces.refl,
    Cslib.Logic.FO.Ordered.ProjectionReduces.trans,
    Cslib.Logic.FO.Ordered.ProjectionReduces.reduces,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.refl,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.trans,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.projectionReduces,
    Cslib.Logic.FO.Ordered.QFProjectionReduces.reduces
  ]
  scope := "Queries on canonically ordered relational structures Fin n with n ≥ 2. Projections \
    are positive-dimensional full-tuple interpretations whose output relations are decision \
    trees of numeric guards with constants or single signed input literals at the leaves; \
    first-order projections allow guards over order, BIT, 0, 1 and max, while quantifier-free \
    projections require quantifier-free guards over order, non-wrapping successor, 0 and max \
    without BIT. Both IsProjectionMap and IsQFProjectionMap contain the identity and are \
    closed under composition (with BIT-free quantifier-free guard pullback via \
    QFNumeric.onFullTuple); projection-completeness endpoints are not yet formalized here, and \
    the logspace encoding lift at encStructure is proved separately in \
    Classes.LogSpace.FirstOrder.Ordered.Projection."

register_result "ordered-sized-graph-qfp" where
  title := "Ordered IndependentSet, Clique, and VertexCover are pairwise QF-projection equivalent"
  topic := "descriptive complexity"
  sources := [
    { paper := Karp1972, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.independentSet_qfProjectionReduces_Clique,
    Cslib.Logic.FO.Ordered.clique_qfProjectionReduces_IndependentSet,
    Cslib.Logic.FO.Ordered.independentSet_qfProjectionReduces_VertexCover,
    Cslib.Logic.FO.Ordered.vertexCover_qfProjectionReduces_IndependentSet,
    Cslib.Logic.FO.Ordered.clique_qfProjectionReduces_VertexCover,
    Cslib.Logic.FO.Ordered.vertexCover_qfProjectionReduces_Clique
  ]
  scope := "Queries on canonically ordered FO.sizedGraph structures on Fin n (2 ≤ n), where \
    target set cardinality is the cardinality of the unary relation size. Dimension-1 BIT-free \
    quantifier-free projections complement off-diagonal edges (guarding the diagonal by numeric \
    equality x = y) and complement the unary size relation; transitivity yields all six \
    pairwise QFProjectionReduces reductions."

register_result "ordered-sat-to-threesat-qfp" where
  title := "Ordered SAT reduces to ThreeSAT via a BIT-free quantifier-free projection"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_ThreeSAT,
    Cslib.Logic.FO.Ordered.isQFProjection_satToThreeSATInterpretation,
    Cslib.Logic.FO.Ordered.mem_ThreeSAT_satToThreeSATInterpretation
  ]
  scope := "Queries on canonically ordered FO.cnf structures on Fin n (2 ≤ n), where ThreeSAT \
    requires at most three literals per clause. A dimension-5 BIT-free quantifier-free \
    projection over order, non-wrapping successor, 0 and max chains positive and negative \
    literal scans with relay variables and pads unused clause tuples with two-literal \
    tautologies; each output bit reads at most one input literal. NP-hardness of Ordered.SAT \
    itself is not yet formalized."

register_result "ordered-sat-to-independent-set-qfp" where
  title := "Ordered SAT reduces to IndependentSet, Clique, and VertexCover via QF projections"
  topic := "descriptive complexity"
  sources := [
    { paper := Karp1972, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_IndependentSet,
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_Clique,
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_VertexCover,
    Cslib.Logic.FO.Ordered.isQFProjection_satToIndependentSetInterpretation,
    Cslib.Logic.FO.Ordered.mem_IndependentSet_satToIndependentSetInterpretation
  ]
  scope := "A dimension-4 BIT-free quantifier-free projection maps any canonically ordered \
    FO.cnf structure on Fin n (2 ≤ n) to an FO.sizedGraph structure partitioned into n clause \
    cliques plus one top clique with a distinguished anchor vertex and target size n + 1; \
    anchor-to-clause edges test single negated input literals and inter-clause edges enforce \
    variable consistency. Composing with the dimension-1 sizedGraph projections yields \
    QFProjectionReduces to Clique and VertexCover. NP-hardness of Ordered.SAT is not yet \
    formalized."

register_result "ordered-sat-to-three-coloring-qfp" where
  title := "Ordered SAT reduces to simple and general 3-colorability via a QF projection"
  topic := "descriptive complexity"
  sources := [
    { paper := GareyJohnson1979, theorem := unverified, locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_SimpleThreeColorable,
    Cslib.Logic.FO.Ordered.sat_qfProjectionReduces_ThreeColorable,
    Cslib.Logic.FO.Ordered.isQFProjection_satToColoringInterpretation,
    Cslib.Logic.FO.Ordered.simpleGraph_satToColoring,
    Cslib.Logic.FO.Ordered.mem_SimpleThreeColorable_satToColoringInterpretation,
    Cslib.Logic.FO.Ordered.mem_ThreeColorable_satToColoringInterpretation
  ]
  scope := "A dimension-6 BIT-free quantifier-free projection over order, non-wrapping \
    successor, 0 and max maps any canonically ordered FO.cnf structure on Fin n (2 ≤ n) to a \
    simple loopless undirected Language.graph structure (modeling Theory.simpleGraph on all \
    inputs) using a palette triangle, literal switches, single-literal activation edges, and \
    successor-linked 3-vertex OR-gate chains. Simultaneously reduces Ordered.SAT to \
    Ordered.SimpleThreeColorable and Ordered.ThreeColorable. NP-hardness of Ordered.SAT is not \
    yet formalized."

register_result "ordered-np-queries-fagin-and-logspace" where
  title := "Ordered NP benchmark queries lie in ESO and native NP with logspace gadget reductions"
  topic := "descriptive complexity"
  sources := [
    { paper := Fagin1974, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.ESODefinable.of_definable,
    Cslib.Logic.FO.Ordered.sat_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.threeSAT_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.threeColorable_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.simpleThreeColorable_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.independentSet_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.clique_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.vertexCover_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_ThreeSAT,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_SimpleThreeColorable,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_ThreeColorable,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_IndependentSet,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_Clique,
    Cslib.Logic.FO.Ordered.sat_logSpaceReducible_VertexCover
  ]
  scope := "Pushing unordered existential second-order sentences forward along LHom.sumInl \
    places Ordered.SAT, Ordered.ThreeSAT, Ordered.ThreeColorable, Ordered.SimpleThreeColorable, \
    Ordered.IndependentSet, Ordered.Clique, and Ordered.VertexCover in Ordered.ESODefinable and \
    in native NP under encStructure via the ordered Fagin verifier; lifting their BIT-free \
    quantifier-free projections yields deterministic LogSpaceReducible reductions at \
    encStructure. NP-completeness awaits the ordered Fagin converse / SAT hardness endpoint."

register_result "trakhtenbrot" where
  title := "Trakhtenbrot: finite satisfiability is undecidable"
  topic := "descriptive complexity"
  sources := [
    { paper := Trakhtenbrot1950, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.RawFormula.not_computablePred_finSat,
    Cslib.Logic.FO.RawFormula.not_rePred_finValid,
    Cslib.Logic.FO.RawFormula.not_rePred_not_finSat,
    Cslib.Logic.FO.RawFormula.exists_finValid_not_of_rePred,
    Cslib.Logic.FO.RawFormula.exists_finValid_unprovable
  ]
  scope := "Library-local raw relational formulas (RawFormula, with equality and relation \
    symbols named by natural numbers), not Mathlib L.Sentence; the reduction uses unboundedly \
    many symbols of arity at most three. FinSat asks for some, FinValid for every, finite \
    nonempty structure and assignment. Decidability is Mathlib's ComputablePred/REPred; the \
    reduction is from halting of Mathlib's Code.evaln, not from Turing machine runs. \
    Corollaries: every r.e. set of finitely valid formulas misses one, so no sound proof \
    system with a decidable proof relation proves every finitely valid formula. The \
    sharpening to a fixed vocabulary containing a relation symbol of arity at least two and \
    the transfer to Mathlib sentences are separate entries."

register_result "trakhtenbrot-binary" where
  title := "Trakhtenbrot's theorem for a vocabulary with a relation symbol of arity at least two"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.RawFormula.not_exists_computable_finSat_of_mem,
    Cslib.Logic.FO.RawFormula.not_exists_rePred_finValid_of_mem,
    Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_not_of_rePred,
    Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_unprovable
  ]
  scope := "For every vocabulary σ ⊆ ℕ × ℕ of (symbol, arity) pairs containing a symbol of \
    arity at least two, no computable procedure is correct for finite satisfiability on the \
    raw sentences over σ, and the finitely valid sentences over σ are not r.e.; hence every \
    r.e. set of finitely valid sentences misses one over σ, and no sound proof system with a \
    decidable proof relation proves them all. Libkin's Theorem 9.2 and Corollary 9.3 state \
    the binary case; higher arities pad binary atoms by repeating the second argument. Raw \
    library-local syntax with finite nonempty models; the form for Mathlib's L.Sentence is \
    the entry trakhtenbrot-sentence."

register_result "trakhtenbrot-sentence" where
  title := "Trakhtenbrot's theorem for Mathlib sentences"
  topic := "descriptive complexity"
  sources := [
    { paper := Trakhtenbrot1950, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    FirstOrder.Language.Sentence.rePred_finSat,
    FirstOrder.Language.Sentence.not_computablePred_finSat,
    FirstOrder.Language.Sentence.not_rePred_finValid,
    FirstOrder.Language.Sentence.exists_finValid_unprovable
  ]
  scope := "Mathlib L.Sentence over a relational language with finitely many relation \
    symbols; the negative results take a relation symbol of arity at least two (Libkin's \
    Theorem 9.2 and Corollary 9.3 state the binary case; higher arities pad binary atoms by \
    repeating the second argument). Sentences are coded by primcodableRaw, a scoped \
    instance, independent of the symbol encoding up to primitive recursive equivalence. \
    FinSat and FinValid quantify over finite nonempty structures. Function symbols and \
    infinite vocabularies are not covered; the decidable monadic converse and dichotomy are \
    in trakhtenbrot-dichotomy."

register_result "trakhtenbrot-dichotomy" where
  title := "Trakhtenbrot–Löwenheim: the decidability dichotomy for finite satisfiability"
  topic := "descriptive complexity"
  sources := [
    { paper := Trakhtenbrot1950, theorem := unverified, locator := unverified },
    { paper := Lowenheim1915, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 9.2 and Corollary 9.3", locator := unverified }
  ]
  theorems := [
    FirstOrder.Language.Sentence.computablePred_finSat_iff,
    FirstOrder.Language.Sentence.computablePred_finValid_iff,
    FirstOrder.Language.Sentence.rePred_finValid_iff,
    FirstOrder.Language.Sentence.rePred_not_finSat_iff,
    FirstOrder.Language.Sentence.computablePred_finSat_of_monadic,
    FirstOrder.Language.Sentence.computablePred_finValid_of_monadic
  ]
  scope := "Mathlib L.Sentence over a relational language with finitely many relation \
    symbols, coded by primcodableRaw. Finite satisfiability and finite validity (over \
    finite nonempty structures) are decidable—and finite validity and finite \
    unsatisfiability are r.e.—if and only if every relation symbol has arity at most one \
    (allowing both unary and nullary symbols). On the monadic side, finite satisfiability \
    and finite validity are primitive recursive by checking RawFormula.SatOnFin below the \
    explicit bound max q 1 * 2 ^ k proved in monadic-small-model (Löwenheim is cited for \
    decidability of the monadic class only). Function symbols and infinite vocabularies \
    are not covered."

register_result "zero-one-law-graphs" where
  title := "Glebskiĭ–Kogan–Liogon'kiĭ–Talanov and Fagin: the 0-1 law for random graphs"
  topic := "descriptive complexity"
  sources := [
    { paper := GlebskiiKoganLiogonkiiTalanov1969, theorem := unverified,
      locator := unverified },
    { paper := Fagin1976, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Chapter 12" }
  ]
  theorems := [
    Cslib.Logic.FO.graph.zero_one_law,
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_one_iff,
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_zero_iff,
    Cslib.Logic.FO.graph.not_exists_sentence_of_not_tendsto,
    Cslib.Logic.FO.graph.not_exists_sentence_even_card,
    Cslib.Logic.FO.graph.not_definable_even_card,
    Cslib.Logic.FO.graph.not_exists_sentence_evenEdges
  ]
  scope := "First-order sentences of Mathlib's language of graphs under the uniform labelled \
    random graph G(n, 1/2) on Fin n. The limit probability is 1 exactly for the \
    consequences of the theory of the random graph and 0 exactly when the negation is one. \
    Consequences: even vertex count and even edge count are not first-order definable. \
    Constant edge probabilities 0 < p < 1 are covered by the entry zero-one-law-binomial; \
    edge probabilities depending on n and unlabelled random graphs are not covered."

register_result "zero-one-law-rado" where
  title := "The Rado graph and the almost-sure theory of G(n, 1/2)"
  topic := "descriptive complexity"
  sources := [
    { paper := Fagin1976, theorem := unverified, locator := unverified },
    { paper := Rado1964, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Section 12.3" }
  ]
  theorems := [
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_one_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_randomGraphProb_zero_iff_radoGraph,
    Cslib.Logic.FO.graph.nonempty_iso_radoGraph,
    Cslib.Logic.FO.graph.nonempty_embedding_radoGraph,
    Cslib.Logic.FO.graph.nonempty_compl_iso_radoGraph
  ]
  scope := "A sentence of the language of graphs holds almost surely in G(n, 1/2) iff it holds \
    in the Rado graph SimpleGraph.radoGraph on ℕ, and almost never otherwise. Structure \
    theory for countable simple graphs: uniqueness among graphs with every extension \
    property, universality for induced embeddings, and self-complementarity."

register_result "zero-one-law-binomial" where
  title := "The 0-1 law for G(n, p) with constant edge probability"
  topic := "descriptive complexity"
  sources := [
    { paper := AlonSpencer2016, theorem := unverified, locator := unverified },
    { paper := Fagin1976, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.graph.binomialRandom_zero_one_law,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_zero_iff,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_zero_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_one_iff_tendsto_randomGraphProb,
    Cslib.Logic.FO.graph.not_exists_sentence_of_not_tendsto_binomialRandom
  ]
  scope := "First-order sentences of Mathlib's language of graphs under Mathlib's binomial \
    random graph SimpleGraph.binomialRandom (Fin n) p, labelled, for a fixed real \
    0 < p < 1. The limit probability is 1 exactly for the consequences of the theory of the \
    random graph, equivalently for the sentences true in the Rado graph, so the almost-sure \
    sentences are those of G(n, 1/2) for every such p. At p = 0 and p = 1 the graph is \
    empty or complete and this characterization fails. Edge probabilities depending on n, \
    other vocabularies and unlabelled random graphs are not covered."

register_result "zero-one-law-relational" where
  title := "The 0-1 law for finite relational vocabularies"
  topic := "descriptive complexity"
  sources := [
    { paper := GlebskiiKoganLiogonkiiTalanov1969, theorem := unverified,
      locator := unverified },
    { paper := Fagin1976, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Chapter 12" }
  ]
  theorems := [
    Cslib.Logic.FO.Relational.zero_one_law,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_one_iff,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_zero_iff,
    Cslib.Logic.FO.Relational.not_exists_sentence_even_card,
    Cslib.Logic.FO.Relational.not_definable_even_card,
    Cslib.Logic.FO.Relational.bernoulliStructure_zero_one_law,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_one_iff,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_zero_iff,
    Cslib.Logic.FO.Relational.tendsto_sentenceProb_bernoulliStructure_one_iff_uniformStructure,
    Cslib.Logic.FO.Relational.not_exists_sentence_of_not_tendsto_bernoulliStructure
  ]
  scope := "Relational languages with finitely many relation symbols, none nullary, under the \
    uniform measure on L-structures on {0, …, n - 1}. The limit is 1 exactly for the \
    consequences of the extension theory and 0 exactly when the negation is one. The law \
    fails with a nullary symbol. For Language.graph the measure is uniform on directed \
    graphs with loops, so this is not the G(n, 1/2) law. The sources cover this uniform law, \
    in which every atomic fact has probability 1/2 (Fagin1976). The bernoulliStructure \
    theorems extend it to a constant probability 0 < p R < 1 for each relation symbol R, with \
    the same almost-sure sentences for every such p. That extension is an adaptation of \
    Fagin's proof made here; no primary source for it was found, and none of the listed \
    sources is claimed for it. With p R equal to 0 or 1 the characterization by the \
    extension theory fails, although the 0-1 law still holds by replacing the symbol with \
    ⊥ or ⊤ (it is a.s. empty or full); that reduction is not formalized. Unlabelled \
    structures and probabilities depending on n are not covered."

register_result "buchi-elgot-trakhtenbrot" where
  title := "Büchi–Elgot–Trakhtenbrot: MSO-definable languages are the regular languages"
  topic := "descriptive complexity"
  sources := [
    { paper := Buchi1960, theorem := unverified, locator := unverified },
    { paper := Elgot1961, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := "Theorem 7.21", locator := unverified },
    { paper := Thomas1997, theorem := unverified, locator := "Section 3" }
  ]
  theorems := [
    Cslib.Logic.WordMSO.definable_iff_isRegular,
    Cslib.Logic.WordMSO.definable_of_isRegular
  ]
  scope := "Languages of finite words over a finite alphabet; MSO over word structures with \
    positions, <, letter predicates and set variables, including the empty word. Regularity \
    is Mathlib's Language.IsRegular. The direction MSO ⇒ regular, proved in the ToRegular \
    module, holds over every alphabet."

register_result "fo-mso-separation" where
  title := "FO[<] is strictly weaker than MSO on finite words"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Corollary 7.27", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.WordMSO.not_foDefinable_even,
    Cslib.Logic.WordMSO.exists_definable_not_foDefinable,
    Cslib.Logic.WordMSO.exists_isRegular_not_foDefinable,
    Cslib.Logic.WordMSO.not_exists_sentence_language_eq_even
  ]
  scope := "Even length is MSO-definable and regular but not definable in FO[<] with letter \
    predicates (no BIT), over any nonempty alphabet; over one letter this is the \
    first-order half of Libkin's Corollary 7.27 for (aa)*. Over the empty alphabet every \
    language is first-order definable."

register_result "star-free-fo" where
  title := "Star-free languages are first-order definable; even length is not star-free"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 7.26 and Corollary 7.27",
      locator := unverified },
    { paper := McNaughtonPapert1971, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Language.IsStarFree.foDefinable,
    Cslib.Logic.WordMSO.not_isStarFree_even,
    Cslib.Logic.WordMSO.exists_isRegular_not_isStarFree
  ]
  scope := "The direction star-free ⇒ FO[<] of McNaughton–Papert, over any alphabet, possibly \
    infinite. With the FO[<] separation it gives that even length (over one letter, (aa)*) \
    is regular but not star-free, over any nonempty alphabet. The remark that FO ⇒ \
    star-free fails over an infinite alphabet is not registered."

register_result "mcnaughton-papert" where
  title := "McNaughton–Papert: first-order definable equals star-free on finite words"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 7.26",
      locator := "second half of the proof, pp. 128–129" },
    { paper := McNaughtonPapert1971, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.WordMSO.foDefinable_iff_isStarFree,
    Cslib.Logic.WordMSO.FODefinable.isStarFree
  ]
  scope := "Languages of finite words over a finite alphabet, FO[<] with letter predicates and \
    no BIT. The direction FO ⇒ star-free needs the finite alphabet; the proof adapts \
    Libkin's induction on quantifier rank."

register_result "ehrenfeucht-fraisse" where
  title := "The Ehrenfeucht–Fraïssé theorem"
  topic := "descriptive complexity"
  sources := [
    { paper := Ehrenfeucht1961, theorem := unverified, locator := unverified },
    { paper := Fraisse1954, theorem := unverified, locator := unverified },
    { paper := Libkin2004, theorem := unverified, locator := "Chapter 3" },
    { paper := EbbinghausFlum1999, theorem := unverified, locator := "Chapter 2" }
  ]
  theorems := [
    Cslib.Logic.FO.duplicatorWins_iff_forall_realize_iff,
    Cslib.Logic.FO.duplicatorWins_iff_forall_formula,
    Cslib.Logic.FO.duplicatorWins_iff_forall_sentence,
    Cslib.Logic.FO.duplicatorWins_of_forall_realize_iff,
    Cslib.Logic.FO.exists_finite_quantifierRank_le_realize_iff,
    Cslib.Logic.FO.elementarilyEquivalent_iff_forall_duplicatorWins
  ]
  scope := "Mathlib first-order languages with finitely many relation symbols; structures may \
    be finite or infinite. Duplicator wins the n-round game from tuples a, b iff they \
    satisfy the same formulas of quantifier rank at most n. The equivalences need \
    L.IsRelational; the Hintikka direction needs only finitely many relation symbols. Also: \
    finitely many rank-n formulas up to equivalence, and elementary equivalence as winning \
    every finite game."

register_result "pebble-games-fo-k" where
  title := "The pebble-game characterization of finite-variable logic FO^k"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := "Theorem 6.10", locator := "Section 6.1, p. 123" },
    { paper := Libkin2004, theorem := "Theorem 11.5, Proposition 11.8 and Corollary 11.9",
      locator := "Section 11.2, pp. 216–218" }
  ]
  theorems := [
    Cslib.Logic.FO.pebbleWins_iff_forall_realize_iff,
    Cslib.Logic.FO.pebbleWinsForever_iff_forall_realize_iff
  ]
  scope := "Mathlib first-order languages with finitely many relation symbols; k-variable \
    formulas reuse variables and have equality and relational atoms. Duplicator wins the \
    n-round k-pebble game from a position (S, a, b) iff a and b satisfy the same FO^k formulas \
    of quantifier rank at most n with free variables in S, for arbitrary structures; the \
    infinite game corresponds to all FO^k formulas on finite structures. Positions are total \
    assignments, so for k > 0 the statements are vacuous on empty structures. Libkin states \
    the results for the infinitary logic L^k_∞ω on finite structures; the remark before \
    Proposition 11.8 reduces rank n to FO^k."

register_result "bijective-pebble-games-c-k" where
  title := "The bijective pebble-game characterization of finite-variable counting logic C^k"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := "Theorem 4.5",
      locator := "Section 4.1; the round-indexed form is in the proof of Theorem 5.2" },
    { paper := Hella1996, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWins_iff_forall_realize_iff,
    Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_realize_iff
  ]
  scope := "Mathlib first-order languages with finitely many relation symbols, finite \
    structures; k-variable counting formulas reuse variables and have equality and relational \
    atoms and the counting quantifiers 'at least m'. Duplicator wins the n-round bijective \
    k-pebble game (Spoiler picks the pebble, then Duplicator the bijection) from a position \
    (S, a, b) iff a and b satisfy the same C^k formulas of quantifier rank at most n with free \
    variables in S; the infinite game corresponds to all C^k formulas. The easy direction holds \
    for arbitrary structures; the hard direction fails for infinite ones (N and R in the empty \
    language). Positions are total assignments, so for k > 0 the statements are vacuous on \
    empty structures. Cai, Furer and Immerman state the characterization on graphs, for the \
    equivalent game in which the players exchange sets of equal size."

register_result "immerman-lander" where
  title := "The Immerman–Lander theorem: color refinement characterizes two-variable counting \
    logic C²"
  topic := "descriptive complexity"
  sources := [
    { paper := ImmermanLander1990, theorem := unverified, locator := unverified },
    { paper := CaiFurerImmerman1992, theorem := "Theorem 5.2 (k = 1 case)",
      locator := "Section 5" },
    { paper := Immerman1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWins_graph_empty_iff,
    Cslib.Logic.FO.bijPebbleWins_graph_singleton_iff,
    Cslib.Logic.FO.bijPebbleWins_graph_univ_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_singleton_le_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_singleton_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_singleton_iff_card_add_card,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_le_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_card_add_card
  ]
  scope := "Finite LocallyFinite simple graphs over FirstOrder.Language.graph with the trivial \
    initial coloring fun _ => (). Round-by-round correspondence between Hella's bijective \
    2-pebble game (with 0, 1 or 2 placed pebbles) and color refinement: sentences of quantifier \
    rank at most n + 1 correspond to round-n color histograms (for nonempty vertex types, since \
    CountingFormula.Realize takes a total assignment Fin 2 → V), and one-variable formulas of \
    rank at most n + 1 correspond to round-(n + 1) vertex colors paired with round-n histograms. \
    Full C²-equivalence reduces to round |V| + |W|. The k-dimensional generalization to C^(k+1) \
    is in weisfeiler-leman-counting; colored graphs with arbitrary initial colorings are not \
    formalized."

register_result "weisfeiler-leman-counting" where
  title := "Cai–Fürer–Immerman: k-dimensional Weisfeiler–Leman characterizes (k + 1)-variable \
    counting logic C^(k+1)"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := "Theorem 5.2", locator := "Section 5" }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWins_graph_range_castSucc_iff,
    Cslib.Logic.FO.bijPebbleWinsForever_graph_range_castSucc_iff,
    Cslib.Logic.FO.bijPebbleWins_graph_empty_of_wlHistogram_eq,
    Cslib.Logic.FO.wlHistogram_eq_of_bijPebbleWins_graph_empty,
    Cslib.Logic.FO.bijPebbleWinsForever_graph_empty_iff_wlHistogram_eq,
    Cslib.Logic.FO.forall_realize_countingFormula_castSucc_le_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_castSucc_iff,
    Cslib.Logic.FO.forall_realize_countingFormula_castSucc_iff_card_pow_add,
    Cslib.Logic.FO.realize_countingFormula_iff_of_wlHistogram_eq,
    Cslib.Logic.FO.wlHistogram_eq_of_forall_realize_countingFormula_empty_le,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_wlHistogram_eq,
    Cslib.Logic.FO.forall_realize_countingFormula_empty_iff_wlHistogram_card_pow_add,
    Cslib.Logic.FO.forall_wlColoring_one_eq_iff,
    Cslib.Logic.FO.forall_wlHistogram_one_eq_iff
  ]
  scope := "Uncolored finite simple graphs over FirstOrder.Language.graph with no LocallyFinite \
    or DecidableRel assumption, for every dimension k : ℕ. Folklore k-WL colors k-tuples from \
    their ordered atomic isomorphism type and refines by the multiset of (k + 1)-tuple step \
    profiles. Two k-tuples get the same round-n color iff they agree on C^(k+1) formulas of \
    quantifier rank at most n in the first k variables, and across all ranks iff they agree in \
    round |V|^k + |W|^k. For nonempty graphs, C^(k+1) sentence equivalence equals k-WL histogram \
    equality in all rounds and in round |V|^k + |W|^k, with a +k quantifier-rank shift for \
    individual rounds. The Cai–Fürer–Immerman lower-bound graphs separating C^(k+1) and k-WL \
    from isomorphism are in cai-furer-immerman-graphs; colored graphs are not formalized."

register_result "cai-furer-immerman-graphs" where
  title := "Cai–Fürer–Immerman lower-bound graphs separating C^(k+1) and k-WL from graph \
    isomorphism"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := unverified, locator := "Section 6" }
  ]
  theorems := [
    Cslib.Logic.FO.bijPebbleWinsForever_cfiEven_cfiOdd,
    Cslib.Logic.FO.bijPebbleWins_cfiEven_cfiOdd,
    Cslib.Logic.FO.pebbleWinsForever_cfiEven_cfiOdd,
    Cslib.Logic.FO.realize_countingFormula_cfiEven_iff_cfiOdd,
    Cslib.Logic.FO.realize_formula_cfiEven_iff_cfiOdd,
    Cslib.Logic.FO.wlHistogram_cfiGraph_eq,
    Cslib.Logic.FO.wlHistogram_cfiEven_eq_cfiOdd_of_le,
    Cslib.Logic.FO.wlHistogram_cfiEven_eq_cfiOdd,
    Cslib.Logic.FO.colorHistogram_cfiEven_eq_cfiOdd,
    Cslib.Logic.FO.bijPebbleWinsForever_cfiGraph_empty,
    Cslib.Logic.FO.realize_countingFormula_cfiGraph_iff,
    Cslib.Logic.FO.exists_nonisomorphic_wlHistogram_eq
  ]
  scope := "Uncolored finite simple graphs over FirstOrder.Language.graph. For every k : ℕ, \
    cfiEven k and cfiOdd k are built over the complete base graph K_(2k+4) with parity gadgets \
    over ZMod 2 and triangle-apex uncoloring on each edge pair; their isomorphism \
    classification and non-isomorphism are in cai-furer-immerman-isomorphism. Duplicator wins \
    the infinite (k + 1)-pebble bijective game on cfiEven k and cfiOdd k, so they agree on all \
    C^(k+1) and FO^(k+1) sentences and have identical d-WL histograms in every round for all \
    d ≤ k. Using K_(2k+4) avoids degree-3 expanders at the cost of graphs of size exponential \
    in k rather than O(k); the linear-size expander lower bound is not formalized."

register_result "even-linear-orders" where
  title := "EVEN is not first-order definable on finite linear orders"
  topic := "descriptive complexity"
  sources := [
    { paper := Kolaitis2007, theorem := unverified, locator := "Chapter 2" },
    { paper := Libkin2004, theorem := "Theorem 3.6 and Corollary 3.12",
      locator := "Chapter 3" }
  ]
  theorems := [
    Cslib.Logic.FO.FiniteLinearOrder.duplicatorWins_iff_card,
    Cslib.Logic.FO.FiniteLinearOrder.realize_iff_of_two_pow_le_card,
    Cslib.Logic.FO.FiniteLinearOrder.exists_sentence_of_card_ne,
    Cslib.Logic.FO.FiniteLinearOrder.not_exists_sentence_realize_iff_even
  ]
  scope := "Finite linear orders in Mathlib's language of orders (pure FO(≤); with BIT, EVEN \
    is definable). Duplicator wins the n-round game iff the orders have equal size or both \
    have at least 2^n - 1 elements, the sharp form in Kolaitis's survey; Libkin states the \
    sufficient condition with threshold 2^n. EVEN is not definable even above any size \
    threshold."

register_result "monadic-small-model" where
  title := "Löwenheim: the small model property for monadic sentences"
  topic := "descriptive complexity"
  sources := [
    { paper := Lowenheim1915, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Monadic.duplicatorWins_of_encard,
    Cslib.Logic.FO.Monadic.realize_iff_of_encard,
    Cslib.Logic.FO.Monadic.exists_substructure_realize,
    Cslib.Logic.FO.Monadic.exists_fin_realize
  ]
  scope := "Mathlib relational languages whose relation symbols have arity at most one, with \
    finitely many unary symbols; nullary symbols are allowed. A sentence of quantifier rank q \
    with a nonempty model has one on Fin (n + 1) with n + 1 ≤ max q 1 * 2 ^ k for k unary \
    symbols, through a substructure of the given model. The explicit bound and its proof by \
    Ehrenfeucht–Fraïssé games are proved here; Löwenheim is cited for the small model \
    property only. The resulting decision procedure and dichotomy for finite satisfiability \
    are in trakhtenbrot-dichotomy."

register_result "connectivity-not-fo" where
  title := "Connectivity is not first-order definable"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Corollary 3.19", locator := unverified },
    { paper := EbbinghausFlum1999, theorem := unverified, locator := "Chapter 2" }
  ]
  theorems := [
    Cslib.Logic.FO.Connectivity.not_exists_sentence_connected,
    Cslib.Logic.FO.Connectivity.not_exists_sentence_connected_of_le_card
  ]
  scope := "Finite simple graphs as structures of Mathlib's language of graphs, with no \
    built-in order or arithmetic, also when only graphs with at least t vertices are \
    considered. Proved by Ehrenfeucht–Fraïssé games through a reduction from EVEN on finite \
    linear orders."

register_result "bipartite-acyclic-not-fo" where
  title := "Bipartiteness and acyclicity are not first-order definable"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Exercises 3.4 and 3.5(3)", locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isBipartite,
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isBipartite_of_le_card,
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic,
    Cslib.Logic.FO.GraphProperties.not_exists_sentence_isAcyclic_of_le_card
  ]
  scope := "Mathlib's SimpleGraph.IsBipartite and SimpleGraph.IsAcyclic on finite simple graphs \
    in the pure language of graphs, also above any size threshold. Proved by adapting \
    Libkin's reduction from EVEN on finite linear orders (Corollary 3.19)."

register_result "hanf-gaifman-locality" where
  title := "Hanf and Gaifman locality of first-order logic"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Lemma 4.9, Theorem 4.12 and Corollary 4.13",
      locator := "Sections 4.2–4.3" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins,
    Cslib.Logic.FO.Locality.HanfEquiv.realize_iff,
    Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso,
    Cslib.Logic.FO.Locality.hanfEquiv_of_nbhdIso,
    Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins,
    Cslib.Logic.FO.Locality.NbhdIso.realize_iff,
    Cslib.Logic.FO.Locality.NbhdIso.formula_realize_iff
  ]
  scope := "Finite structures. Hanf: equivalence at radius (3^n - 1)/2 gives Duplicator the \
    n-round game, so formulas of quantifier rank at most n agree; this form assumes M \
    nonempty. Gaifman: tuples with isomorphic radius-(3^(n+1) - 1)/2 neighborhoods agree on \
    such formulas. Game statements hold for every language, formula statements need a \
    relational one. Gaifman's normal form is not formalized."

register_result "locality-graph-properties" where
  title := "Being a tree is not first-order definable; locality bounds for graph properties"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Exercise 4.6",
      locator := "Section 4.1, Figure 4.2 (p. 48); Theorem 4.12 and the remark after \
        Corollary 4.13 (p. 52); Exercise 4.6 (p. 63)" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.not_exists_sentence_isTree,
    Cslib.Logic.FO.Locality.not_exists_sentence_isTree_of_le_card,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_connected,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_isTree,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_isAcyclic
  ]
  scope := "Finite simple graphs in the pure language of graphs, by Hanf locality. A sentence \
    of quantifier rank q holding exactly in the connected graphs on V forces \
    |V| ≤ 2·3^q + 1; for trees or acyclic graphs, |V| ≤ 2·3^q. The constants come from \
    Hanf's radius and are not claimed sharp. The module's sharper bounds for q ≥ 1 are \
    not registered."

register_result "transitive-closure-not-fo" where
  title := "Transitive closure and reachability are not first-order definable"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := unverified,
      locator := "Section 4.1, Figure 4.1 (p. 46); after Definition 4.7 (p. 49); \
        Section 4.3 (p. 54)" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.not_exists_formula_reflTransGen,
    Cslib.Logic.FO.Locality.not_exists_formula_transGen,
    Cslib.Logic.FO.Locality.not_exists_formula_reachable,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_reflTransGen,
    Cslib.Logic.FO.Locality.card_le_of_realize_iff_transGen,
    Cslib.Logic.FO.Locality.two_pow_le_of_gaifman_radius
  ]
  scope := "Finite structures of the pure language of graphs, by Gaifman locality. No formula \
    in two free variables defines the reflexive–transitive or transitive closure of the \
    edge relation, or reachability in finite simple graphs; on the successor relation of \
    Fin N, rank q forces N ≤ 2·3^(q+1). Any Gaifman radius for rank n is at least \
    2^(n-1); the exact rank 2^n - 1 is not formalized. Constants are not claimed sharp."

register_result "fo-tc-strict" where
  title := "FO(TC) is strictly more expressive than FO on finite structures"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := unverified,
      locator := "Definition 10.20 (p. 199); Section 4.1" }
  ]
  theorems := [
    Cslib.Logic.FO.TC.exists_formula_reflTransGen,
    Cslib.Logic.FO.TC.exists_formula_not_fo_equivalent
  ]
  scope := "Unordered finite structures of Mathlib's language of graphs, read as directed \
    graphs. One well-formed FO(TC) formula defines the reflexive–transitive closure of the \
    edge relation (the library's closure operator is reflexive), and no first-order \
    formula is equivalent to it on all finite structures."

register_result "color-refinement" where
  title := "Color refinement: stabilization, coarsest equitable partition and soundness"
  topic := "descriptive complexity"
  sources := [
    { paper := GroheKerstingMladenovSelman2014, theorem := unverified,
      locator := "Section 1 (Introduction), paragraph \"Colour Refinement on Matrices\"" }
  ]
  theorems := [
    SimpleGraph.ker_refinementColoring_eq,
    SimpleGraph.isEquitable_stableColoring,
    SimpleGraph.isGreatest_ker_stableColoring,
    SimpleGraph.not_exists_iso_of_colorHistogram_ne,
    SimpleGraph.isEmpty_iso_of_colorHistogram_ne,
    SimpleGraph.forall_refinementColoring_eq_iff,
    SimpleGraph.forall_colorHistogram_eq_iff,
    SimpleGraph.IsRegularOfDegree.colorHistogram_eq
  ]
  scope := "Finite LocallyFinite simple graphs with an arbitrary initial coloring χ₀ with k₀ \
    classes. The partition is stable from round |V| - k₀ and is the coarsest equitable \
    partition refining χ₀; the source states |V| + |W| rounds for a bipartite matrix from \
    the trivial partition. Differing histograms rule out color-preserving isomorphism; the \
    test is incomplete (equal-order d-regular graphs). The correspondence with \
    two-variable counting logic C² on uncolored simple graphs is in immerman-lander, and \
    folklore k-dimensional Weisfeiler–Leman is in weisfeiler-leman. Fractional isomorphism and a \
    certified algorithm are not formalized."

register_result "weisfeiler-leman" where
  title := "k-dimensional Weisfeiler–Leman: partition stabilization, soundness and two-graph \
    stabilization"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := unverified, locator := "Section 5" }
  ]
  theorems := [
    SimpleGraph.ker_wlColoring_eq,
    SimpleGraph.ker_stableWLColoring,
    SimpleGraph.Iso.wlColoring_comp,
    SimpleGraph.Iso.wlHistogram_eq,
    SimpleGraph.isEmpty_iso_of_wlHistogram_ne,
    SimpleGraph.forall_wlColoring_eq_iff,
    SimpleGraph.forall_wlHistogram_eq_iff
  ]
  scope := "Uncolored finite simple graphs ([Fintype V], with no LocallyFinite or DecidableRel \
    assumption), for every dimension k : ℕ. Folklore k-WL colors Fin k → V by ordered atomic \
    isomorphism type at round 0 and by the multiset over all v : V of the atomic type of \
    Fin.snoc u v paired with the k single-coordinate replacement colors. The partition \
    stabilizes from round |V|^k - k₀ on, is isomorphism-invariant, and two-graph tuple or \
    histogram agreement in all rounds reduces to round |V|^k + |W|^k. The logical correspondence \
    with C^(k+1) is in weisfeiler-leman-counting, and the Cai–Fürer–Immerman lower-bound graphs \
    are in cai-furer-immerman-graphs and cai-furer-immerman-isomorphism; initial tuple \
    colorings and certified complexity bounds are not formalized."

register_result "cai-furer-immerman-isomorphism" where
  title := "Cai–Fürer–Immerman graphs over K_m: twist-parity isomorphism classification"
  topic := "descriptive complexity"
  sources := [
    { paper := CaiFurerImmerman1992, theorem := unverified, locator := "Section 6" }
  ]
  theorems := [
    SimpleGraph.isEmpty_iso_cfiGraph_of_sum_ne,
    SimpleGraph.not_nonempty_iso_cfiGraph_of_sum_ne,
    SimpleGraph.nonempty_iso_cfiGraph_iff_sum_eq,
    SimpleGraph.isEmpty_iso_cfiEven_cfiOdd,
    SimpleGraph.not_nonempty_iso_cfiEven_cfiOdd
  ]
  scope := "Uncolored finite simple Cai–Fürer–Immerman graphs cfiGraph m f over the complete \
    base graph K_m with twist f : Fin m → ZMod 2. Each edge pair is joined to an apex vertex so \
    that triangle membership separates edge and apex vertices from parity-gadget vertices \
    without vertex colors. Twisting f along an edge of K_m yields an isomorphic graph, and for \
    3 ≤ m two graphs cfiGraph m f and cfiGraph m g are isomorphic iff ∑ v, f v = ∑ v, g v; in \
    particular cfiEven k and cfiOdd k over K_(2k+4) are non-isomorphic. Indistinguishability \
    in C^(k+1) and k-WL is in cai-furer-immerman-graphs; expander base graphs of size O(k) are \
    not formalized."

register_result "translational-time-hierarchy" where
  title := "Deterministic time hierarchy below every power of the logarithm, by translation"
  topic := "time complexity"
  sources := [
    { paper := FortnowSanthanam2006,
      theorem := "Lemma 5 (the translation method only, not these statements)",
      locator := "Section 3.3" }
  ]
  theorems := [
    Cslib.Complexity.DTIME_pow_ssubset_DTIME_mul_iterSqrtLog_pow,
    Cslib.Complexity.DTIME_pow_ssubset_DTIME_of_pow_mul_log_rpow_le,
    Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_two_pow_add_log_div,
    Cslib.Complexity.DTIME_two_pow_ssubset_DTIME_of_two_pow_mul_rpow_le
  ]
  scope := "DTIME(n^a) is strictly inside DTIME(g) whenever g(n) >= n^a (ln n)^eps eventually, \
    for every integer a >= 1 and real eps > 0, and DTIME(2^n) is strictly inside DTIME(g) \
    whenever g(n) >= 2^n n^eps eventually, on bit strings with native multitape DTIME. \
    Derived by translation (padding) from the library's polylogarithmic-gap diagonal theorem; \
    the source lemma is the translation method, not this statement. Only the bounds n^a and \
    2^n are covered, not arbitrary time-constructible t, and this is not W. J. Paul's \
    fixed-tape hierarchy."

register_result "liu-pass" where
  title := "Liu–Pass: one-way functions exist iff time-bounded Kolmogorov complexity is mildly \
    hard on average"
  topic := "meta-complexity"
  sources := [
    { paper := LiuPass2020, theorem := "Theorem 3.1",
      locator := "Section 3, p. 9 of arXiv:2009.11514v1" }
  ]
  theorems := [
    Cslib.Crypto.exists_oneWay_iff_exists_mildlyHardOnAverage_timeBoundedNat,
    Cslib.Crypto.exists_oneWay_iff_exists_mildlyHardOnAverageENat_timeBounded,
    Cslib.Crypto.exists_oneWay_iff_exists_forall_mildlyHardOnAverage_timeBoundedNat,
    Cslib.Crypto.exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_clog_timeBoundedNat,
    Cslib.Crypto.exists_oneWay_iff_forall_exists_mildlyHardOnAverageToApprox_timeBoundedNat
  ]
  scope := "Uniform one-way functions on bit strings and mild average-case hardness against \
    uniform strict PPT heuristics, for the library's multi-tape K^t. Item (b) takes a \
    polynomial clock p(n) >= n + 1 where the source writes t(n) > 0. Item (c) and the \
    threshold consequence are proved only in the polynomial-threshold form (some p, every \
    t >= p), with approximation windows d floor(log n) and d ceil(log n); the source's \
    near-linear range t(n) >= (1 + eps) n is not formalized."

register_result "kabanets-cai" where
  title := "Kabanets–Cai: if MCSP is in BPP, there are no one-way functions"
  topic := "meta-complexity"
  sources := [
    { paper := KabanetsCai2000, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.not_oneWay_of_MCSP_mem_BPP,
    Cslib.Crypto.not_oneWay_of_MCSP_mem_P,
    Cslib.Crypto.not_pseudorandomFunction_of_MCSP_mem_BPP
  ]
  scope := "Conditional. MCSP is the total truth-table language with De Morgan circuits \
    counting all gates, encoded as the table followed by the threshold in binary, and the \
    hypothesis is a bounded-error polynomial-time decider at all thresholds. Every keyed \
    family computable in polynomial time is then distinguished from a random function by a \
    uniform strict oracle PPT adversary with advantage at least 1/4, so no uniform one-way \
    function on bit strings exists."

register_result "formula-magnification" where
  title := "Oliveira–Santhanam: approximate-MCSP formula lower bounds above N polylog N give \
    NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 1(i) / Theorem 17(i) and Lemma 16",
      locator := "ECCC TR18-139, Section 1.2, p. 5; Section 3.1, pp. 14–15" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_poly_hard,
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_hard
  ]
  scope := "Conditional. De Morgan formulas measured by leaf size; approximate (1, 1 - 1/k)-MCSP \
    with s₁ <= s₂, integer k >= 1 and a non-strict agreement bound in the no-set. The \
    hypothesis is that for every c some 2^n-bit slice has no separating formula of leaf size \
    (2^n + 1) c (n + 1)^c (polynomially bounded s₂ and k), or the query-length analogue for \
    general parameters. The conclusion is that NP for the succinct MCSP encoding is not \
    contained in polynomial-size formulas."

register_result "formula-magnification-stretched" where
  title := "Oliveira–Santhanam: N^(1+ε) approximate-MCSP formula lower bounds give NP formula \
    lower bounds of size 2^(m^δ)"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 17(ii)",
      locator := "ECCC TR18-139, Section 3.1, p. 15" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_NP_not_isBigO_formulaSize_of_approxMCSP_poly_hard,
    Cslib.Circuits.Boolean.exists_pos_not_isBigO_formulaSize_of_approxMCSP_hard
  ]
  scope := "Conditional. Polynomially bounded s₂ and k; the hypothesis is approximate-MCSP \
    formula leaf size above N^(1 + eps), N = 2^n, at arbitrarily large n. The conclusion gives \
    some delta > 0 such that a binary NP language (and every language agreeing with succinct \
    MCSP) has formula size not O(2^(m^delta))."

register_result "formula-magnification-subexp" where
  title := "Oliveira–Santhanam: approximate-MCSP formula lower bounds with subexponential \
    parameters give NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 17(iii)",
      locator := "ECCC TR18-139, Section 3.1, p. 15" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_subexp_hard,
    Cslib.Circuits.Boolean.not_NP_subset_FormulaPolyOn_of_approxMCSP_rpow_hard
  ]
  scope := "Conditional. Subexponentially bounded s₂ and k; the hypothesis is approximate-MCSP \
    formula leaf size above 2^(n + n/d) for a fixed d > 0, or above N^(1 + eps), at \
    arbitrarily large n. The conclusion is that NP for the succinct MCSP encoding is not \
    contained in polynomial-size formulas."

register_result "formula-magnification-average-case" where
  title := "Oliveira–Santhanam: one-sided zero-error average-case formula lower bounds for MCSP \
    give NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 27",
      locator := "ECCC TR18-139, Section 3.3, p. 21" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard,
    Cslib.Circuits.Boolean.not_mem_FormulaPoly_of_zero_error_average_case_subexp_hard
  ]
  scope := "Conditional, for De Morgan formulas only. Subexponentially bounded s; average-case \
    solvers are one-sided formulas accepting every yes-instance of MCSP[s] and at most \
    2^(2^n - n) truth tables, with the lower bound 2^(n/d) for fixed d > 0 at arbitrarily \
    large n. The conclusion is a binary NP language without polynomial-size formulas, weaker \
    than the source's 2^Omega(n)."

register_result "formula-magnification-ternary" where
  title := "Oliveira–Santhanam: sublinear zero-error average-case formula lower bounds for \
    MCSP[2^√n] imply NP ⊄ Formula[poly]"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2018, theorem := "Theorem 5",
      locator := "ECCC TR18-139, Section 1.2, p. 8; Appendix A, Definition 43, p. 34" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_average_case_hard,
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_sqrtThreshold_half_average_case_hard,
    Cslib.Circuits.Boolean.exists_NP_not_mem_FormulaPoly_of_zero_error_average_case_sublinear_hard
  ]
  scope := "If no nonuniform family of ternary De Morgan formula devices (an unknown mask and an \
    answer formula) with o(2^n) total leaves solves MCSP[⌊2^√n⌋] on 2^n-bit truth tables with \
    zero error, answering ? on at most a 1/n fraction of truth tables for every large n \
    (Definition 43), then some binary NP language has no polynomial-size De Morgan formulas; \
    the general form takes any subexponential threshold. Circuit size counts every De Morgan \
    gate. Conditional: no formula lower bound for MCSP is proved."

register_result "formula-magnification-locality" where
  title := "Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam: the Oliveira–Santhanam formula \
    magnification reduction is local"
  topic := "meta-complexity"
  sources := [
    { paper := ChenHiraharaOliveiraPichRajgopalSanthanam2020,
      theorem := "Proposition 63, [OS18] MCSP bullet",
      locator := "ECCC TR19-168, Appendix A.2, p. 52; Section 2.5, Definition 11, p. 13" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_oracleFormula_separating_approxMCSP,
    Cslib.Circuits.Boolean.localFormulaClass_approxMCSP,
    Cslib.Circuits.Boolean.localFormulaClass_approxMCSP_real_poly
  ]
  scope := "MCSP[(s, 0), (s, δ)] on N = 2^n-bit truth tables is computed by De Morgan formulas \
    with at most N oracle gates, each of fan-in at most 98·(⌈1/δ⌉·(s + 1))^3, adaptivity 1 and \
    N times that many input leaves, under one fixed oracle (encoded SuccinctMCSP) for all \
    lengths, when n ≤ s(n) and 0 < δ(n). Formulas only: no bullet of Proposition 63 is proved \
    for the [q, ℓ, a]-Circuit classes (LocalCircuitClass), and the other bullets and the \
    locality barrier (Theorem 59) are not formalized."

register_result "murray-williams" where
  title := "Murray–Williams: if MCSP is NP-hard, then EXP ≠ NP ∩ P/poly and EXP ≠ ZPP"
  topic := "meta-complexity"
  sources := [
    { paper := MurrayWilliams2017, theorem := "Theorems 1.6 and 4.1",
      locator := "Section 1, p. 5; Section 4.1, p. 13" }
  ]
  theorems := [
    Cslib.Complexity.EXP_eq_NEXP_of_MCSP_npHard_of_EXP_subset_PPoly,
    Cslib.Complexity.not_EXP_subset_NP_inter_PPolyOn_of_MCSP_npHard,
    Cslib.Complexity.EXP_ne_NP_inter_PPolyOn_of_MCSP_npHard,
    Cslib.Complexity.EXP_ne_ZPP_of_MCSP_npHard
  ]
  scope := "Conditional. The hypothesis is NP-hardness of the total truth-table MCSP (binary \
    threshold, all gates counted) under polynomial-time many-one reductions; Theorem 4.1 \
    assumes only reductions from sparse NP languages, so the formalization is its full-NP-hard \
    specialization. Classes are over bit strings with native multi-tape machines; \
    EXP ≠ NP ∩ P/poly uses the library's nondeterministic time hierarchy."

register_result "anti-checker" where
  title := "Small anti-checkers for functions without small circuits"
  topic := "meta-complexity"
  sources := [
    { paper := LiptonYoung1994, theorem := unverified, locator := unverified },
    { paper := OliveiraPichSanthanam2019, theorem := "Lemma 4.7 (ordered-tuple variant)",
      locator := "Section 4" }
  ]
  theorems := [
    Cslib.MCSP.exists_isAntiChecker,
    Cslib.MCSP.exists_lt_complexityOn,
    Cslib.MCSP.exists_ofFunction_notMem
  ]
  scope := "Unconditional, nonuniform existence. For m > 0, if no m members of a family of \
    fewer than 2^b functions on at most 2^m inputs have f as strict majority, some set of at \
    most 16 b inputs refutes every member. For circuits with n <= m: if f needs more than m s \
    gates plus those of strict majority on m bits, f needs more than s gates on some set of at \
    most 16 b inputs. Ordered tuples give the share 1/16 \
    where the source gets 1/(2m). The efficient anti-checker lemma under NP ⊆ P/poly \
    (Oliveira–Pich–Santhanam Lemma 4.1) is not formalized."

register_result "natural-proofs" where
  title := "Razborov–Rudich: subexponentially secure generators rule out natural proofs \
    against P/poly"
  topic := "meta-complexity"
  sources := [
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 4" },
    { paper := GGM1986, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_isUseful_PPoly_of_isNatural_of_generator
  ]
  scope := "Conditional. If a family of length-doubling generators with polynomial circuit \
    complexity is subexponentially secure against circuits (for long seeds of length k, \
    tests with at most 2^m gates, m^d <= k, have advantage at most 2^-m), then no \
    P/poly-natural property is useful against P/poly. The generator tests are nonuniform \
    circuits reading the 2k-bit outputs; the barrier's derived tests read whole truth tables \
    of the GGM keyed family. The generator family is a hypothesis, not a constructed object."

register_result "chaitin-incompleteness" where
  title := "Chaitin's incompleteness theorem for plain Kolmogorov complexity"
  topic := "Kolmogorov complexity"
  sources := [
    { paper := Chaitin1974, theorem := unverified, locator := unverified },
    { paper := LiVitanyi2019, theorem := unverified, locator := "Chapter 2" }
  ]
  theorems := [
    Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_complexity_universal_add,
    Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_forall_le_of_rePred_of_read,
    Cslib.Kolmogorov.DescriptionMethod.MinorizesPartrec.exists_notMem_of_rePred
  ]
  scope := "Plain complexity under any description method of a Primcodable type that is at most \
    an additive constant worse than every partial recursive decoder. Formal systems are r.e. \
    predicates on Primcodable sentences with a computable reading of n <= C(x), and soundness \
    is a hypothesis. The quantitative bound is C(encode e) + c for a code e semi-deciding the \
    collection. Prefix-free complexity, Chaitin's Omega and logic-level theories are not \
    formalized."

register_result "symmetry-of-information" where
  title := "Kolmogorov–Levin symmetry of information for plain complexity"
  topic := "Kolmogorov complexity"
  sources := [
    { paper := ShenUspenskyVereshchagin2017, theorem := unverified,
      locator := "Sections 2.2 and 2.3" }
  ]
  theorems := [
    Cslib.Kolmogorov.DescriptionMethod.exists_complexity_universal_add_condUniversal_le,
    Cslib.Kolmogorov.DescriptionMethod.exists_abs_complexity_universal_pair_sub_le,
    Cslib.Kolmogorov.exists_abs_algorithmicInformation_sub_le,
    Cslib.Kolmogorov.exists_abs_algorithmicInformation_sub_algorithmicInformation_le
  ]
  scope := "Plain complexity of the Partrec universal method on natural numbers, pairs coded by \
    Nat.pair, and log the binary length Nat.size. With k = C(x, y): C(x) + C(y | x) <= \
    k + 2 log k + 4 log log k + O(1), |C(x, y) - C(x) - C(y | x)| <= 6 log k + O(1), and \
    |I(x : y) - I(y : x)| <= 12 log k + O(1). Exact prefix-complexity symmetry and \
    time-bounded symmetry are not formalized."

register_result "minkt-np" where
  title := "MINKT, the time-bounded Kolmogorov complexity problem, is in NP"
  topic := "meta-complexity"
  sources := [
    { paper := Ko1991, theorem := unverified, locator := unverified },
    { paper := Hirahara2018, theorem := unverified, locator := "Definition 9" },
    { paper := LiuPass2020, theorem := unverified, locator := "Section 2.2" }
  ]
  theorems := [
    Cslib.Kolmogorov.MINKT.mem_NP,
    Cslib.Kolmogorov.MINKTAt.mem_NP,
    Cslib.Kolmogorov.MINKTAt.mem_NP_polynomial₂
  ]
  scope := "Instances are a string with time and size thresholds in unary, and K^t is measured \
    with the library's multi-tape universal machine and step clock. Fixed thresholds t and s \
    computable in polynomial time in unary give an NP bit-string language. Membership only; \
    NP-hardness of MINKT is not formalized. Hirahara's Definition 9 (after Ko) defines the \
    problem, and the fixed-threshold MINKTAt follows Liu and Pass, Section 2.2."

register_result "mktp-exp" where
  title := "MKtP, the minimum Levin Kt complexity problem, is in E and EXP"
  topic := "meta-complexity"
  sources := [
    { paper := LiuPass2021Crypto, theorem := unverified, locator := "Section 2.2" }
  ]
  theorems := [
    Cslib.Kolmogorov.MKtP.mem_E,
    Cslib.Kolmogorov.MKtP.mem_EXP,
    Cslib.Kolmogorov.MKtPAt.mem_EXP
  ]
  scope := "Levin's Kt for the library's multi-tape universal machine. The threshold is \
    encoded in unary, where Liu and Pass use a binary threshold of about log n bits; for \
    thresholds O(|x|) the two encodings are polynomially related. MKtPAt s, with s \
    computable in polynomial time in unary, is in EXP over bit strings. Membership only."

register_result "tfnp-eopl-eq-sopl-inter-ppad" where
  title := "EOPL = SOPL ∩ PPAD"
  topic := "structural complexity"
  sources := [
    { paper := GoosEtAl2022, theorem := "Lemma 4",
      locator := "Section 5, pp. 9–10 of arXiv:2202.07761v2" }
  ]
  theorems := [
    Cslib.Complexity.EOPL_eq_SOPL_inter_PPAD,
    Cslib.Complexity.SOPL_inter_PPAD_subset_EOPL,
    Cslib.Complexity.mem_EOPL_of_sinkOfPotentialLine_endOfLine
  ]
  scope := "Uniform total-search classes over any injective encoding enc : α ↪ List Bool, \
    defined by native deterministic multi-tape polynomial-time predecessor, successor and \
    binary potential families with unary vertex width and polynomial-time search reductions. \
    Potential-line graphs prune active edges along which the potential does not strictly \
    increase. Combines an end-of-line family directly with a sink-of-potential-line family \
    rather than routing through bijective pigeonhole."

register_result "tfnp-sopl-eopl-collapse" where
  title := "Further collapses in TFNP: SOPL = PLS ∩ PPADS and EOPL = PLS ∩ PPAD"
  topic := "structural complexity"
  sources := [
    { paper := GoosEtAl2022, theorem := "Theorem 1 and Theorem 2",
      locator := "Section 1, p. 1; Lemmas 2–3, Sections 3–4, pp. 6–8 of arXiv:2202.07761v2" }
  ]
  theorems := [
    Cslib.Complexity.SOPL_eq_PLS_inter_PPADS,
    Cslib.Complexity.EOPL_eq_PLS_inter_PPAD,
    Cslib.Complexity.PLS_inter_PPADS_subset_SOPL,
    Cslib.Complexity.PLS_inter_PPAD_subset_EOPL,
    Cslib.Complexity.mem_SOPL_of_localOpt_sinkOfLine
  ]
  scope := "Uniform total-search classes over any injective encoding enc : α ↪ List Bool, \
    defined by native deterministic multi-tape polynomial-time local-search, sink-of-line, \
    end-of-line and potential-line families with unary vertex width and polynomial-time search \
    reductions. Proves PLS ∩ PPADS ⊆ SOPL via the path-pigeonhole gadget and reversible PLS \
    transitions on width n₁(a) + 2(n₁(a) + n₂(a)), then deduces SOPL = PLS ∩ PPADS and \
    EOPL = PLS ∩ PPAD via EOPL = SOPL ∩ PPAD and PPAD ⊆ PPADS. UEOPL and query separations \
    are not formalized."

register_result "goemans-williamson-max2sat" where
  title := "Goemans–Williamson α-approximation rounding for MAX-2SAT (α > 0.87856)"
  topic := "algorithms"
  sources := [
    { paper := GoemansWilliamson1995, theorem := "Theorem 7.2.1.1",
      locator := "Section 7.2.1" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_signedSdpValue_le_integral,
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_satSdpValue_le_integral,
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_satValue_le_integral
  ]
  scope := "Exact stdGaussian random-hyperplane rounding of unit-vector SDP relaxations (P') \
    and weighted MAX-2SAT over arbitrary finite clause/variable types with nonnegative weights, \
    using Real.goemansWilliamsonConstant (0.87856 < α). No SDP solver, Gaussian sampler, \
    derandomization, or Section 7.2.2 MAX-SAT LP/SDP hybrid is formalized."

register_result "goemans-williamson-max2sat-cnf" where
  title := "Goemans–Williamson rounding bridge for Cslib MaxTwoSAT CNFs"
  topic := "algorithms"
  sources := [
    { paper := GoemansWilliamson1995, theorem := "Section 7.2.1",
      locator := "Section 7.2.1" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_countP_le_integral,
    Cslib.Algorithms.Lean.MaxTwoSAT.goemansWilliamsonConstant_mul_target_le_integral_of_mem
  ]
  scope := "Specialization of Goemans–Williamson MAX-2SAT random-hyperplane rounding to list \
    CNFs counted by Cslib.Logic.PL.CNF.countP and membership in Cslib.Complexity.MaxTwoSAT \
    under exact stdGaussian expectation; no polynomial-time SDP solver is included."

open Cslib.Algorithms.Lean.MaxDicut in
register_result "goemans-williamson-maxdicut" where
  title := "Goemans–Williamson β-approximation rounding for MAX-DICUT (β > 0.79607)"
  topic := "algorithms"
  sources := [
    { paper := GoemansWilliamson1995, theorem := "Lemma 7.3.1, Lemma 7.3.2",
      locator := "Section 7.3, pp. 1138–1139" }
  ]
  theorems := [
    goemansWilliamsonDicutConstant_mul_dicutSdpValue_le_integral,
    goemansWilliamsonDicutConstant_mul_dicutValue_le_integral,
    goemansWilliamsonConstant_mul_sub_le_integral_of_isBalancedDigraph
  ]
  scope := "Exact stdGaussian random-hyperplane rounding for triple SDP relaxations (P'') and \
    weighted directed multigraphs with nonnegative weights, achieving \
    Real.goemansWilliamsonDicutConstant (0.79607 < β < 0.79608), plus the balanced-digraph \
    reduction recovering α > 0.87856 on p. 1138. No SDP solver, finite-precision sampler, or \
    derandomization is formalized."

register_result "nayak-wu-counting" where
  title := "Nayak–Wu: quantum query lower bound for approximate counting"
  topic := "quantum complexity"
  sources := [
    { paper := NayakWu1999, theorem := "Theorem 1.11",
      locator := "Section 1 (arXiv:quant-ph/9804066v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_exactCount_le,
    Cslib.Quantum.one_sub_mul_approxCount_le,
    Cslib.Quantum.approxCount_lower_bound
  ]
  scope := "T-query bit-query quantum algorithm outputting a real estimate y with |y - t| < Δ \
    on inputs of Hamming weight t (failure probability at most ε, 2ε <= 1). When 1/2 <= Δ and \
    4Δ <= n, gives (1 - 2 sqrt(ε(1-ε))) (sqrt(n/Δ) + sqrt(t(n-t))/Δ) <= 16T and <= 288T at \
    ε = 1/3; when 0 < Δ <= 1/2 and 1 <= n, gives <= 4T. Derived from the adversary weight-layer \
    bound rather than polynomials. Relative counting and approximate mean are not formalized."

register_result "nayak-wu-kth-smallest" where
  title := "Nayak–Wu: quantum query lower bound for approximate k-th smallest selection"
  topic := "quantum complexity"
  sources := [
    { paper := NayakWu1999, theorem := "Theorem 1.5",
      locator := "Sections 1 and 2 (arXiv:quant-ph/9804066v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_kthSmallest_le,
    Cslib.Quantum.kthSmallest_lower_bound,
    Cslib.Quantum.kthSmallest_involution_lower_bound,
    Cslib.Quantum.kthSmallest_index_lower_bound
  ]
  scope := "T-query value-query quantum algorithm over a finite index type and linearly ordered \
    alphabet returning an element within rank distance < Δ of k (or any relaxed value) with \
    failure probability at most ε <= 1/2, for 1 <= k <= n, 1 <= Δ, 4Δ <= n. Proves explicit \
    constants 32T (576T at ε = 1/3), 16T (288T) for involutive-difference oracle steps, and \
    the same bound on T + 1 for index-returning algorithms. Comparison-tree oracles are not \
    formalized."

register_result "nayak-wu-median" where
  title := "Nayak–Wu: quantum query lower bound for approximate median"
  topic := "quantum complexity"
  sources := [
    { paper := NayakWu1999, theorem := "Corollary 1.6",
      locator := "Section 1 (arXiv:quant-ph/9804066v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_median_le,
    Cslib.Quantum.median_lower_bound,
    Cslib.Quantum.median_inv_delta_lower_bound,
    Cslib.Quantum.median_involution_lower_bound,
    Cslib.Quantum.median_index_lower_bound
  ]
  scope := "T-query value-query quantum algorithm over a finite index type (1 <= n) and \
    linearly ordered alphabet outputting a δ-approximate median (0 < δ < 1) with failure \
    probability at most ε <= 1/2. Gives (1 - 2 sqrt(ε(1-ε))) min(1/δ, n) <= 24T, 432T at \
    ε = 1/3 (hence 1/δ <= 432T when 1 <= δ n), 12T (216T) for involutive-difference oracle \
    steps, and the same bound on T + 1 for index-returning algorithms. Derived via adversary \
    weight-layer bounds rather than polynomials; comparison-tree oracles are not formalized."
