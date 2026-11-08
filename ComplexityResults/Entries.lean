/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import ComplexityResults.Registry
import Complexity.Algorithms.WordRAM.Schoening.Amplify
import Complexity.Computability.Circuit.Arithmetic.CircuitLowerBound
import Complexity.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters
import Complexity.Computability.Circuit.Boolean.BarringtonClass
import Complexity.Computability.Circuit.Boolean.Braverman.Fooling
import Complexity.Computability.Circuit.Boolean.Formula.Andreev
import Complexity.Computability.Circuit.Boolean.Hastad.Sharp
import Complexity.Computability.Circuit.Boolean.Khrapchenko
import Complexity.Computability.Circuit.Boolean.Smolensky
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.Andreev
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevApproxMajority
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevAverage
import Complexity.Computability.Circuit.Boolean.WeightedThreshold.AndreevLowerBound
import Complexity.Computability.Communication.Discrepancy
import Complexity.Computability.Communication.Disjointness
import Complexity.Computability.Complexity.Classes.Alternation.Savitch
import Complexity.Computability.Complexity.Classes.Alternation.SpaceGame
import Complexity.Computability.Complexity.Classes.BQP.Counting
import Complexity.Computability.Complexity.Classes.IP.Shamir
import Complexity.Computability.Complexity.Classes.LogSpace.Complement
import Complexity.Computability.Complexity.Classes.LogSpace.FirstOrder
import Complexity.Computability.Complexity.Classes.LogSpace.PolyTime
import Complexity.Computability.Complexity.Classes.LogSpace.USTCON
import Complexity.Computability.Complexity.Classes.PH.SipserLautemann
import Complexity.Computability.Complexity.Classes.SharpP.Lowness
import Complexity.Computability.Complexity.Classes.Space.Nondeterministic
import Complexity.Computability.Complexity.Classes.Space.Savitch
import Complexity.Computability.Complexity.Classes.TimeSpace.Williams
import Complexity.Computability.Complexity.Classes.Toda
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Fagin.Converse
import Complexity.Computability.Complexity.FineGrained.CountingNativeEndpoint
import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount
import Complexity.Computability.Complexity.FineGrained.OrthogonalVectors
import Complexity.Computability.Complexity.FineGrained.PPZ
import Complexity.Computability.Complexity.FineGrained.Schoening
import Complexity.Computability.Complexity.FineGrained.Sparsification
import Complexity.Computability.Complexity.Problems.Primes
import Complexity.Computability.MCSP.Magnification
import Complexity.Computability.MCSP.PartialETH
import Complexity.Computability.PCP.Completeness
import Complexity.Crypto.Computational.Nonuniform.ZeroKnowledge
import Complexity.Crypto.Computational.OneWayToPRF
import Complexity.Crypto.Computational.OneWayToPRG
import Complexity.Logics.Propositional.Resolution.Pigeonhole
import Complexity.Probability.Extractor.TwoSource

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
    polynomial space bound and whose branches all halt. Not the parameterized quadratic-space \
    simulation."

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
