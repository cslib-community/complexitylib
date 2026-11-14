/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Foundations.Algebra.Group.HomomorphismTesting
import CslibFrontier.Probability.MarkovChain.RandomWalk
import CslibFrontier.Probability.MarkovChain.RotationMap
import CslibFrontier.Foundations.Combinatorics.Expander.Visits
import CslibFrontier.Foundations.Combinatorics.Expander.HittingProduct
import CslibFrontier.Foundations.Combinatorics.Expander.VisitCount
import CslibFrontier.Computability.Complexity.Classes.Padding.Tally
import CslibFrontier.Computability.Complexity.Problems.Permanent.Valiant
import CslibFrontier.Computability.Complexity.Problems.ThreeSAT.Collapse
import CslibFrontier.Computability.Complexity.Classes.Sparse.Envelope
import CslibFrontier.Computability.Complexity.Classes.Advice.OneBit
import CslibFrontier.Computability.Complexity.Classes.Advice.LengthComparison
import CslibFrontier.Computability.Circuit.Boolean.Advice.Hierarchy
import CslibFrontier.Algorithms.Lean.Arborescence.PolyTime
import CslibFrontier.Algorithms.Lean.DFS.SCC
import CslibFrontier.Algorithms.Lean.MaxDicut.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamson
import CslibFrontier.Algorithms.Lean.MaxTwoSAT.GoemansWilliamsonMaxTwoSAT
import CslibFrontier.Algorithms.Lean.TwoSAT
import CslibFrontier.Algorithms.Lean.TrimmedYates
import CslibFrontier.Algorithms.LinearAlgebra.BareissElimination
import CslibFrontier.Algorithms.Lean.TreeDecomposition.CSP
import CslibFrontier.Algorithms.WordRAM.Schoening.Amplify
import CslibFrontier.Computability.QueryComplexity.MajorityThree
import CslibFrontier.Computability.QueryComplexity.YaoExpected
import CslibFrontier.Computability.Complexity.Problems.SharpCycle
import CslibFrontier.Computability.Complexity.Problems.StronglyConnected.Completeness

import CslibFrontier.Computability.QueryComplexity.AdjacentPair
import CslibFrontier.Computability.Circuit.Arithmetic.BitBlast
import CslibFrontier.Computability.Circuit.Arithmetic.CircuitLowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.UpperBound
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.AnyOrder
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConstantDepth
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ConcentratingShiftSet
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.LowerBound
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.NoncommABP
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.ROABP
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SetMultilinear
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.Sparse
import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.SparseOrbit
import CslibFrontier.Computability.Circuit.Arithmetic.MatrixMultiplication.NineQuarters
import CslibFrontier.Computability.Circuit.Boolean.ArithmeticRing
import CslibFrontier.Computability.Circuit.Boolean.Arithmetic
import CslibFrontier.Computability.Circuit.Boolean.BitBlastCompiler
import CslibFrontier.Computability.Circuit.Boolean.FiniteSimulation
import CslibFrontier.Computability.Circuit.Boolean.BarringtonClass
import CslibFrontier.Computability.Circuit.Boolean.ParityNC1
import CslibFrontier.Computability.Circuit.Boolean.Braverman.Fooling
import CslibFrontier.Computability.Circuit.Boolean.Formula.Andreev
import CslibFrontier.Computability.Circuit.Boolean.Hastad.Sharp
import CslibFrontier.Computability.Circuit.Boolean.FormalComplexityMeasure
import CslibFrontier.Computability.Circuit.Boolean.Khrapchenko
import CslibFrontier.Computability.Circuit.Boolean.NaturalProof.Generator
import CslibFrontier.Computability.Circuit.Boolean.NonuniformSeparation
import CslibFrontier.Computability.Circuit.Boolean.Razborov.MiddleSlice.P
import CslibFrontier.Computability.Circuit.Boolean.Razborov.Useful
import CslibFrontier.Computability.Circuit.Boolean.Smolensky
import CslibFrontier.Foundations.BooleanAnalysis.OrDegree
import CslibFrontier.Computability.Circuit.NNF.Negation.Separation
import CslibFrontier.Computability.Communication.Discrepancy
import CslibFrontier.Computability.Communication.Discrepancy.Spectral
import CslibFrontier.Computability.Communication.DistinctRows
import CslibFrontier.Computability.Communication.Disjointness
import CslibFrontier.Computability.Communication.FoolingSet
import CslibFrontier.Computability.Communication.Rank
import CslibFrontier.Computability.Communication.Nondeterministic.UniqueDisjointness
import CslibFrontier.Computability.Complexity.Classes.Alternation.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch
import CslibFrontier.Computability.Complexity.Classes.Alternation.SpaceGame
import CslibFrontier.Computability.Complexity.Classes.BQP.Counting
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.NondeterministicSpace
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
import CslibFrontier.Computability.Complexity.Classes.Space.Separation
import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Translational
import CslibFrontier.Computability.Complexity.Classes.IP.Deterministic
import CslibFrontier.Computability.Complexity.Classes.IP.PerfectSoundness
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
import CslibFrontier.Computability.Complexity.Classes.PH.Yap
import CslibFrontier.Computability.Complexity.Classes.SharpP.Lowness
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.DeterministicTime
import CslibFrontier.Computability.Complexity.Classes.Space.Nondeterministic.Savitch
import CslibFrontier.Computability.Complexity.Classes.Space.Savitch
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineCollapse
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.PotentialLineNormalization
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SOPLCollapse
import CslibFrontier.Computability.Complexity.Classes.TFNP.Subclasses.SpernerHardness
import CslibFrontier.Computability.Complexity.Classes.Time.Sublinear
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.Williams
import CslibFrontier.Computability.Complexity.Classes.Toda
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Fagin.Converse
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Completeness
import CslibFrontier.Computability.Complexity.Fagin.Ordered.Problems
import CslibFrontier.Computability.Complexity.FineGrained.CliqueGrouping
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeEndpoint
import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeModelCount
import CslibFrontier.Computability.Complexity.FineGrained.OrthogonalVectors
import CslibFrontier.Computability.Complexity.FineGrained.PPZ
import CslibFrontier.Computability.Complexity.FineGrained.Schoening
import CslibFrontier.Computability.Complexity.FineGrained.SchoeningMachine
import CslibFrontier.Computability.Complexity.FineGrained.Sparsification
import CslibFrontier.Computability.Complexity.Gradel
import CslibFrontier.Computability.Complexity.ImmermanVardi
import CslibFrontier.Computability.Complexity.Parameterized.WHierarchy.XP
import CslibFrontier.Computability.Complexity.Problems.BoundedTermination
import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.AnyEndpoints
import CslibFrontier.Computability.Complexity.Problems.HornSAT
import CslibFrontier.Computability.Complexity.Problems.QUADEQ
import CslibFrontier.Computability.Complexity.Problems.Permanent.ThreeSAT
import CslibFrontier.Computability.Complexity.Problems.Primes
import CslibFrontier.Computability.Complexity.Problems.TMSAT
import CslibFrontier.Computability.Complexity.Problems.TwoSAT.PolyTime
import CslibFrontier.Computability.Complexity.Problems.Permanent.ZeroOne
import CslibFrontier.Computability.Kolmogorov.Incompleteness
import CslibFrontier.Computability.Kolmogorov.MINKT
import CslibFrontier.Computability.Kolmogorov.MINKTStar.Hardness
import CslibFrontier.Computability.Kolmogorov.MKtP
import CslibFrontier.Computability.Kolmogorov.SymmetryOfInformation
import CslibFrontier.Computability.MCSP.AntiChecker
import CslibFrontier.Computability.MCSP.AntiChecker.Efficient
import CslibFrontier.Computability.MCSP.FormulaMagnification
import CslibFrontier.Computability.MCSP.FormulaMagnification.AverageCase
import CslibFrontier.Computability.MCSP.FormulaMagnification.Locality
import CslibFrontier.Computability.MCSP.FormulaMagnification.StretchedExponential
import CslibFrontier.Computability.MCSP.FormulaMagnification.Subexponential
import CslibFrontier.Computability.MCSP.FormulaMagnification.SublinearAverageCase
import CslibFrontier.Computability.MCSP.HardnessConsequences
import CslibFrontier.Computability.MCSP.Magnification
import CslibFrontier.Computability.MCSP.Magnification.AntiChecker
import CslibFrontier.Computability.MCSP.Magnification.GapMCSP
import CslibFrontier.Computability.MCSP.Magnification.MergeTree.Locality
import CslibFrontier.Computability.MCSP.MultiNPHard
import CslibFrontier.Computability.MCSP.PartialETH
import CslibFrontier.Computability.MCSP.PartialHardness.Reduction
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.StepCounter
import CslibFrontier.Computability.PCP.Approximation.UniqueGames.Complexity
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Computability.PolyTime.LinearAlgebra.RationalElimination
import CslibFrontier.Computability.QueryComplexity.RelevantCoordinates
import CslibFrontier.Computability.QueryComplexity.Connectivity
import CslibFrontier.Computability.QueryComplexity.Quantum.NayakWuConsequences
import CslibFrontier.Computability.QueryComplexity.Quantum.PermutationInversion
import CslibFrontier.Computability.QueryComplexity.Quantum.SpectralAdversary
import CslibFrontier.Computability.QueryComplexity.Quantum.WeightedAdversary
import CslibFrontier.Crypto.Computational.Encryption.CTRMode
import CslibFrontier.Crypto.Computational.Encryption.OFBMode
import CslibFrontier.Crypto.Computational.GoldreichLevin.HardCore
import CslibFrontier.Crypto.Computational.InaccessibleEntropy.OneWay
import CslibFrontier.Crypto.Computational.InaccessibleEntropy.TargetCollision
import CslibFrontier.Crypto.Computational.MLDSA.KeyOnly
import CslibFrontier.Crypto.Computational.NaorYung
import CslibFrontier.Crypto.Computational.Nonuniform.ZeroKnowledge
import CslibFrontier.Crypto.Computational.OneWay.LiuPass
import CslibFrontier.Crypto.Computational.OneWay.MCSP
import CslibFrontier.Crypto.Computational.OneWayToPRF
import CslibFrontier.Crypto.Computational.OneWayToPRG
import CslibFrontier.Crypto.Computational.SIS.Ajtai
import CslibFrontier.Crypto.Primitives.PRP.Finite
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.Bot
import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NotBot
import CslibFrontier.Crypto.Protocols.PIR.Block
import CslibFrontier.Crypto.Protocols.PIR.Collusion
import CslibFrontier.Crypto.Protocols.PIR.GeneralCover
import CslibFrontier.Crypto.Protocols.PIR.Indexed
import CslibFrontier.Crypto.Protocols.PIR.Interactive
import CslibFrontier.Crypto.Protocols.PIR.MultiInteractive
import CslibFrontier.Crypto.Protocols.PIR.Shamir
import CslibFrontier.Crypto.Protocols.PIR.SmoothConverse
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Correlation
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Cut
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.StableSet
import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.TSP
import CslibFrontier.DataStructure.NearNeighbor.Angular
import CslibFrontier.DataStructure.NearNeighbor.PStable
import CslibFrontier.DataStructure.Paging.Marking
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.RootBound
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Sturm
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.TotalIsolation
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CFI
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ColorRefinement
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.WeisfeilerLeman
import CslibFrontier.Foundations.Computability.KleenePost
import CslibFrontier.Foundations.Computability.KleenePostJump
import CslibFrontier.Foundations.Data.BranchingVector
import CslibFrontier.GameTheory.Bimatrix.Existence
import CslibFrontier.GameTheory.Bimatrix.PPAD
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Cycle
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Dictatorship
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Interval
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Median
import CslibFrontier.GameTheory.Mechanism.FacilityLocation.Tree
import CslibFrontier.GameTheory.Strategic.Correlated
import CslibFrontier.GameTheory.Strategic.Nash
import CslibFrontier.GameTheory.Strategic.SwapRegretDynamics
import CslibFrontier.Logics.Propositional.CNF.TruthTable
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Connectivity
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.FiniteLinearOrder
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.GraphProperties
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Hintikka
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Monadic
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CFI
import CslibFrontier.Logics.FirstOrder.FiniteVariable.ColorRefinement
import CslibFrontier.Logics.FirstOrder.FiniteVariable.CountingHintikka
import CslibFrontier.Logics.FirstOrder.FiniteVariable.Hintikka
import CslibFrontier.Logics.FirstOrder.FiniteVariable.Infinitary
import CslibFrontier.Logics.FirstOrder.FiniteVariable.WeisfeilerLeman
import CslibFrontier.Logics.FirstOrder.Locality.GraphProperties
import CslibFrontier.Logics.FirstOrder.Locality.Hanf
import CslibFrontier.Logics.FirstOrder.Locality.Reachability
import CslibFrontier.Logics.FirstOrder.Locality.Sharp
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
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Infinitary
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Rado
import CslibFrontier.Logics.FirstOrder.ZeroOneLaw.Relational
import CslibFrontier.Logics.Propositional.CNF.Branching
import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole
import CslibFrontier.Logics.SecondOrder.Ordered.Grounding
import CslibFrontier.Logics.SecondOrder.WordMSO.McNaughtonPapert
import CslibFrontier.Logics.SecondOrder.WordMSO.OfRegular
import CslibFrontier.Logics.SecondOrder.WordMSO.Separation
import CslibFrontier.Logics.SecondOrder.WordMSO.StarFree
import CslibFrontier.MachineLearning.Boosting.AdaBoost
import CslibFrontier.MachineLearning.LossMinimization.RLM
import CslibFrontier.MachineLearning.LossMinimization.Squared
import CslibFrontier.MachineLearning.OnlineLearning.SwapRegret
import CslibFrontier.MachineLearning.PACBayes.Basic
import CslibFrontier.MachineLearning.PACBayes.KL
import CslibFrontier.MachineLearning.PACLearning.AgnosticVCSharp
import CslibFrontier.MachineLearning.PACLearning.FundamentalTheorem
import CslibFrontier.MachineLearning.PACLearning.MDL
import CslibFrontier.MachineLearning.PACLearning.Nonuniform
import CslibFrontier.MachineLearning.UniformLearning.CIKK.AC0Mod
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Amplification
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Complexity
import CslibFrontier.MachineLearning.UniformLearning.CIKK.Learner
import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.GGM
import CslibFrontier.MachineLearning.UniformLearning.CryptoHardness.NaturalProperty
import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson
import CslibFrontier.MachineLearning.UniformLearning.NisanWigderson.BestOf
import CslibFrontier.Computability.Probabilistic.CoinOfDigits
import CslibFrontier.Probability.BilinearFingerprint
import CslibFrontier.Probability.Extractor.LeftoverHash
import CslibFrontier.Probability.Extractor.TwoSource
import CslibFrontier.Probability.LocalitySensitiveHash.PStable
import CslibFrontier.Probability.LocalitySensitiveHash.SimHash

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

register_result "connectivity-evasiveness" where
  title := "Graph connectivity requires every possible edge query"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 11.4 (2007 public draft)",
      locator := "2007 public draft, PDF 228 / printed p. 212" }
  ]
  theorems := [Cslib.BitString.Graph.complexity_connectivity]
  scope := "For every m, the total connectivity function on labelled undirected simple graphs \
    on Fin m has deterministic decision-tree complexity m.choose 2. Each input coordinate \
    represents one unordered pair of distinct vertices; repeated queries are allowed. Mathlib \
    regards the empty graph as disconnected and the one-vertex graph as connected, and both \
    functions have complexity zero. No graph promise, arbitrary edge-permutation symmetry, \
    randomized bound or machine-runtime bound is asserted."

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

register_result "tmsat-np-complete" where
  title := "TMSAT is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 2.9",
      locator := "Web draft 2007-01-08, printed p. 44; PDF p. 60" }
  ]
  theorems := [Cslib.Complexity.TMSAT.npComplete]
  scope := "Instances (α, x, 1^n, 1^t) as the structure TMSATInstance under encTMSATInstance, \
    with the native machine description, raw input bits and unary n and t. Acceptance is a \
    halted run with output [true] of the universal interpreter for t steps on frame x ++ u, \
    for a witness u of exactly n bits. Hardness for every NP problem and instance encoding."

register_result "truth-table-cnf-size" where
  title := "Every Boolean function has a CNF with at most ℓ·2^ℓ AND/OR symbols"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Claim 2.14",
      locator := "Web draft 2007-01-08, printed p. 46; PDF p. 62" }
  ]
  theorems := [Cslib.Logic.PL.CNF.exists_eval_eq_connectiveCount_le]
  scope := "Functions (Fin ℓ → Bool) → Bool and list CNFs over Fin ℓ. The size measure \
    connectiveCount counts binary connectives: k - 1 ORs per clause of k literals and m - 1 \
    ANDs between m clauses. The source's size ℓ·2^ℓ is read as an upper bound."

register_result "dir-ham-path-any-np-complete" where
  title := "Directed Hamiltonian path without given endpoints is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 2.18",
      locator := "Web draft 2007-01-08, printed p. 52; PDF p. 68" }
  ]
  theorems := [Cslib.Complexity.DirHamPathAny_npComplete]
  scope := "Finite listed graphs under encGraph with some Hamiltonian path; graphs without \
    declared vertices are not members. Hardness reduces the designated-endpoint DirHamPath \
    (Sipser's diamond construction) by adding a fresh source and sink, not the draft's \
    direct 3SAT reduction."

register_result "quadeq-np-complete" where
  title := "QUADEQ is NP-complete"
  topic := "NP-completeness"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 2, Exercise 18",
      locator := "Web draft 2007-01-08, printed p. 64; PDF p. 80" }
  ]
  theorems := [Cslib.Complexity.QUADEQ_npComplete]
  scope := "Systems of quadratic equations over 𝔽₂ as lists of QuadEquation records under \
    QUADEQ.encoding: each equation lists the monomials u_i u_j with a_ij = 1, repeated \
    monomials cancelling in pairs, with binary natural-number variable labels and no bound on \
    their values. Membership by a polynomial-time verifier with first-occurrence certificates; \
    hardness by a polynomial-time reduction from SAT (the exercise's hint), composed with \
    Cook–Levin."

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
    O(s n) work cells. The nondeterministic space hierarchy is the entry nspace-hierarchy."

register_result "nspace-hierarchy" where
  title := "The nondeterministic space hierarchy"
  topic := "space complexity"
  sources := [
    { paper := Immerman1988, theorem := "Corollary 4", locator := unverified },
    { paper := Sipser2013, theorem := unverified, locator := unverified },
    { paper := Szelepcsenyi1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.NSPACE_ssubset_NSPACE,
    Cslib.Complexity.NL_ssubset_NSPACE_log2_sq
  ]
  scope := "NSPACE f ⊂ NSPACE g on binary words for space-constructible g with ⌊log₂ n⌋ ≤ g n \
    when every c·f(n)+c is eventually below g(n), the same hypotheses as the deterministic \
    hierarchy. NSPACE is decision by one finite-state native nondeterministic multi-tape machine \
    within c₁·s(n) + c₂ work cells along every computation prefix, every branch halting. The \
    diagonal is in NSPACE g by Immerman–Szelepcsényi complementation of a budgeted universal \
    recognizer that reads its input in place."

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

register_result "strongly-connected-nl-complete" where
  title := "Strongly connected digraphs are NL-complete"
  topic := "space complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 4, Exercise 4",
      locator := "Web draft 2007-01-08, printed p. 89; PDF p. 105" }
  ]
  theorems := [Cslib.Complexity.StronglyConnected.logSpaceComplete]
  scope := "Digraphs on Fin n with loops allowed, encoded by encDigraph: a unary header 1^n 0 \
    and the row-major adjacency matrix (the encSTCON layout without s and t); the empty digraph \
    is strongly connected. Native visited-cell NL: membership by one nondeterministic counter \
    program that guesses a path for every ordered pair, every branch halting; hardness by a \
    native logspace many-one reduction from STCON adding arcs v → s and t → v. Completeness for \
    the draft's ever-non-blank space class needs the measure bridge of draft Theorem 4.16."

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

register_result "dip-eq-np" where
  title := "Deterministic interactive proofs decide exactly NP"
  topic := "interactive proofs"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 8.3",
      locator := "web draft 2007-01-08, Section 8.1 (printed p. 148, PDF p. 164)" }
  ]
  theorems := [Cslib.Complexity.dIP_eq_NP]
  scope := "dIP is the coin-free case of the IP model: a deterministic word-query verifier run \
    against every randomized stateful prover, strict oracle PPT (one machine, one polynomial \
    clock), completeness 1 and soundness 0; arbitrary injective encodings."

register_result "perfect-soundness-ip-subset-np" where
  title := "Interactive proofs with perfect soundness are in NP"
  topic := "interactive proofs"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Proposition 9.2",
      locator := "April 2007 draft r5.pdf, PDF p. 9; printed p. 391" }
  ]
  theorems := [Cslib.Complexity.IsInteractiveProof.mem_NP,
    Cslib.Complexity.mem_NP_of_exists_pos_acceptProb]
  scope := "Perfect soundness gives NP for every strict oracle-PPT IP verifier with any \
    positive completeness; the source's perfect-completeness assumption is dropped. The \
    certificate is a transcript of at most t messages and replies of at most t bits with the \
    t coins, t the clock; arbitrary injective encodings."

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

register_result "sharp-cycle-fp-p-eq-np" where
  title := "If #CYCLE is in FP then P = NP"
  topic := "counting classes"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 9.4",
      locator := "Web draft 2007-01-08, §9.1, printed p. 173; PDF p. 189" }
  ]
  theorems := [
    Cslib.Complexity.P_eq_NP_of_computableInPolyTime_SharpCycle,
    Cslib.Complexity.SharpCycle.mem_DirHamCycle_iff
  ]
  scope := "#CYCLE counts the simple directed cycles (Cycle values: nonempty, no repeated \
    vertex, declared vertices, arcs of the edge list; a self-loop is a cycle of length one) of \
    a graph under encGraph. FP is native polynomial-time computability with binary output \
    encNat. The gadget reduction uses n*n+n+1 layers and threshold 2^(m*n) instead of the \
    draft's n log n + 1 and n^(n^2). P = NP holds for every injective encoding."

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

register_result "middle-slice-lower-bound-mod-two" where
  title := "Razborov's rank method: a middle slice is not in AC⁰[2]"
  topic := "circuit complexity"
  sources := [
    { paper := Razborov1987, theorem := unverified, locator := unverified },
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 3.2, p. 27" },
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := unverified,
      locator := "p. 10:20" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Razborov.middleSlice_notMem_AC0Mod_two
  ]
  scope := "No family of circuits of NOT, unbounded fan-in AND/OR and MOD_2 gates of constant \
    depth and polynomial size decides the language of bit strings of length n with exactly \
    ⌈n/2⌉ - ⌊√(n + 1)/10⌋ zeros (nonuniform). Proved through a variant of Razborov's GF(2) \
    rank property (one square matrix, threshold C(n, a)/2). Razborov and Rudich (Section 3.2) \
    state the property only abstractly; the explicit p = 2 form is the sketch of Carmosino et \
    al. (p. 10:20). Razborov's original paper was not checked for its hard function. \
    Membership in P and the separation are middle-slice-mod-two."

register_result "middle-slice-mod-two" where
  title := "Razborov's rank method: a middle slice is in P but not in AC⁰[2]"
  topic := "circuit complexity"
  sources := [
    { paper := Razborov1987, theorem := unverified, locator := unverified },
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 3.2, p. 27" },
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := unverified,
      locator := "p. 10:20" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Razborov.middleSlice_mem_P,
    Cslib.Circuits.Boolean.Razborov.exists_mem_P_notMem_AC0Mod_two
  ]
  scope := "The language of bit strings of length n with exactly ⌈n/2⌉ - ⌊√(n + 1)/10⌋ zeros is \
    decided in polynomial time by a multi-tape Turing machine and is not in AC⁰[2]: no family of \
    circuits of NOT, unbounded fan-in AND/OR and MOD_2 gates of constant depth and polynomial \
    size decides it (nonuniform). Proved through a variant of Razborov's GF(2) rank property \
    (one square matrix, threshold C(n, a)/2); the sources give the abstract property and a \
    sketch, and Razborov's original paper was not checked for its hard function. The lower bound \
    itself is the separate entry middle-slice-lower-bound-mod-two."

register_result "rank-property-natural-ac0-2" where
  title := "Razborov's rank property is a P/poly-natural property useful against AC⁰[2]"
  topic := "circuit complexity"
  sources := [
    { paper := RazborovRudich1997, theorem := unverified, locator := "Section 3.2, p. 27" },
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := "Theorem 5.3",
      locator := "p. 10:19; p = 2 property p. 10:20" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.Razborov.isNatural_PPoly_and_isUseful_AC0Mod_two_rankProperty,
    Cslib.Circuits.Boolean.Razborov.isUseful_AC0Mod_two_rankProperty,
    Cslib.Circuits.Boolean.Razborov.notMem_rankProperty_rankLength_of_computes,
    Cslib.Circuits.Boolean.Razborov.rankLength_add_one_le
  ]
  scope := "Along the level ⌈n/2⌉ - ⌊√(n + 1)/10⌋, the GF(2) rank property (a variant: one square \
    matrix, threshold C(n, a)/2) is large, its truth tables are decided by De Morgan circuits of \
    173·8^n gates (P/poly; size only, depth not certified, not the sources' NC²), and it is useful \
    against AC⁰[2] (NOT, unbounded fan-in AND/OR and MOD_2 gates; nonuniform). Explicitly, at \
    the input length m = rankLength d x, which satisfies m + 1 ≤ 401·2^(2d(2d+7))·x^(2d) for \
    x ≥ 1, no circuit of depth at most d with at most 2^x gates computes a function with the \
    property. p = 2 only; the constants are this library's. \
    The learning consequence for p = 2 is the separate entry cikk-learning-ac0-2."

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

register_result "majority-three-zero-error-expected-cost" where
  title := "Three-bit majority has exact zero-error expected query complexity 8/3"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Examples 11.14 and 11.18",
      locator := "Web draft 2007-01-08, printed pp. 215–216; PDF pp. 231–232" }
  ]
  theorems := [
    Cslib.QueryComplexity.zeroErrorComplexity_majority_three,
    Cslib.QueryComplexity.MajorityThree.algorithm_expectedCost,
    Cslib.QueryComplexity.MajorityThree.hardDistribution_lower,
    Cslib.QueryComplexity.MajorityThree.weights_hardDistribution
  ]
  scope := "Total majority on three Boolean coordinates. Existing finite-support zero-error \
    randomized-tree model; cost counts executed queries, including repeats. The uniform \
    six-order short-circuit algorithm has expected cost 2 on constants and 8/3 otherwise. \
    The uniform law on six nonconstant inputs forces cost at least 8/3 on all correct \
    adaptive deterministic trees, including arbitrary repeats. Local computation is free."

register_result "yao-zero-error-expected-cost" where
  title := "Expected-cost Yao minimax with optimal algorithm and hardest input law"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 11.17; Definitions 11.13, 11.15–11.16",
      locator := "Web draft 2007-01-08, printed pp. 215–216; PDF pp. 231–232" }
  ]
  theorems := [
    Cslib.QueryComplexity.zeroErrorComplexity_eq_iSup_distributionalExpectedComplexity,
    Cslib.QueryComplexity.exists_optimal_expectedCost,
    Cslib.QueryComplexity.exists_computes_distributionalCost_eq,
    Cslib.QueryComplexity.exists_distributionalExpectedComplexity_eq_zeroErrorComplexity
  ]
  scope := "Finite Boolean coordinate space, arbitrary output type, total everywhere-correct \
    deterministic trees and finitely supported randomized trees. Expected executed queries, \
    including repeated queries; free local computation. Numerical equality with the maximum \
    optimized distributional expected cost, both sides attained. No finite-output assumption, \
    no bounded-error depth substitution, no expected Turing-machine runtime claim."

register_result "adjacent-pair-sensitivity-separation" where
  title := "Adjacent-pair block functions: sensitivity Θ(√n), block sensitivity Θ(n)"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 11, Exercise 2",
      locator := "Web draft 2007-01-08, printed p. 218; PDF p. 234" }
  ]
  theorems := [Cslib.BitString.adjacentPairSqrt_measures]
  scope := "Every length n ≥ 4, with Nat.sqrt n balanced contiguous blocks of sizes \
    n / k + [i < n % k]; a block accepts exactly two adjacent true bits, overlapping choices \
    included. Native CSLib sensitivity, block sensitivity, certificate complexity and \
    decision-tree complexity: √n ≤ s ≤ 3√n (floor square root), n ≤ 3 bs and \
    bs ≤ C ≤ D ≤ n. No exact values (such as D = n) are claimed."

register_result "adjacent-pair-block-bounds" where
  title := "Adjacent-pair block functions with arbitrary block sizes: sensitivity and block \
    sensitivity bounds"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 11, Exercise 2 (general block layout)",
      locator := "Web draft 2007-01-08, printed p. 218; PDF p. 234" }
  ]
  theorems := [
    Cslib.BitString.sensitivity_adjacentPairBlocks_le,
    Cslib.BitString.sum_half_le_blockSensitivity_adjacentPairBlocks
  ]
  scope := "Unequal consecutive blocks covering n coordinates, each accepting exactly two \
    adjacent true bits: sensitivity is at most max(3k, M) for k blocks of at most M bits, and \
    the sum over blocks of half their sizes (rounded down) is at most the block sensitivity."

register_result "boolean-two-element-arithmetic-simulation" where
  title := "Boolean and two-element arithmetic circuits have linearly related sizes"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (two-element case)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.exists_arithmetic_simulation,
    Cslib.Circuits.Boolean.exists_boolean_simulation
  ]
  scope := "Bool's Boolean ring, with XOR addition and AND multiplication. All outputs and \
    all inputs are preserved; arithmetic simulates De Morgan circuits with size factor 3, \
    and De Morgan circuits simulate arithmetic with factor 4. Constants count as gates; \
    input/output wires are free. Nonuniform existence, not compiler runtime or formal \
    polynomial equality. This does not complete the arbitrary fixed finite-field exercise."

register_result "von-neumann-fair-bit-extraction" where
  title := "Von Neumann extraction: an exact fair bit from a biased coin"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 7.15",
      locator := "Web draft 2007-01-08, §7.4, printed p. 124; PDF p. 140" }
  ]
  theorems := [Cslib.Probability.DDGTree.vonNeumann_generatesWith_coin,
    Cslib.Probability.DDGTree.expectedFlipsWith_coin_vonNeumann,
    Cslib.Probability.DDGTree.exists_generatesWith_coin_iff]
  scope := "Unbounded coin-reading trees (DDG trees) run on independent flips of a coin of \
    bias 0 < rho < 1: exact fair output and exactly 1/(rho(1-rho)) expected flips. Some tree \
    outputs a fair bit iff 0 < rho < 1. Cost counts coin flips; no Turing-machine runtime."

register_result "biased-coin-from-fair-digits" where
  title := "A coin of any bias from fair coins with expected two flips"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 7.14",
      locator := "Web draft 2007-01-08, §7.4, printed p. 124; PDF p. 140" }
  ]
  theorems := [Cslib.Probability.DDGTree.coinOfDigits_spec_of_computableInPolyTime]
  scope := "Digit-comparison DDG tree for any binary expansion of rho in [0,1] (rho = 1 via \
    0.111...): exact coin of bias rho, exactly 2 expected fair bits. With digits polynomial-time \
    from the unary index, the expected sum of the digit machine's time bounds (plus one per \
    flip) is the finite series sum_n (t n + 1) 2^-n. The comparison loop is not compiled to a \
    Turing machine."

register_result "or-exact-degree" where
  title := "Polynomials computing OR on the cube have full degree"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 13, Exercise 6",
      locator := "Web draft 2007-01-08, printed p. 252; PDF p. 268" }
  ]
  theorems := [Cslib.BitString.card_le_totalDegree_of_eval_eq_or,
    Cslib.BitString.le_totalDegree_of_eval_eq_or_zmod,
    Cslib.BitString.totalDegree_orPoly]
  scope := "Every polynomial over a nontrivial commutative ring, multilinear or not, that \
    agrees with OR at the 0/1 points has total degree at least the number of variables; \
    1 - prod (1 - X_i) attains it. The GF(q) corollary is stated over ZMod q with q prime. \
    Exact representation only; no approximate-degree statement."

register_result "parity-nc-one" where
  title := "Parity is in NC¹"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 13, Exercise 7 (PARITY)",
      locator := "Web draft 2007-01-08, printed p. 253; PDF p. 269" }
  ]
  theorems := [Cslib.Circuits.Boolean.parity_mem_NC_one]
  scope := "Nonuniform NC¹: polynomial-size fan-in-two De Morgan circuit families of depth \
    O(log n), negations free. Proved by an explicit balanced XOR formula of depth \
    2 ceil(log2 n), not by the Karchmer–Wigderson game the exercise suggests."

register_result "formal-complexity-measure-leaf-bound" where
  title := "Formal complexity measures lower-bound constant-free formula leaf size"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 22.1",
      locator := "Web draft 2007-01-08, §22.1, printed p. 438; PDF p. 454" }
  ]
  theorems := [Cslib.Circuits.Boolean.FormalComplexityMeasure.le_leafSize]
  scope := "Natural-valued measures subadditive under AND/OR and at most one on each literal. \
    Constant-free De Morgan formulas, with arbitrary negations; input-leaf size. \
    No complement invariance. Constants are excluded because their library leaf cost is zero."

register_result "formal-complexity-measure-quarter-density" where
  title := "A large formal complexity measure is large on a quarter of truth tables"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 22.2",
      locator := "Web draft 2007-01-08, §22.1, printed p. 438; PDF p. 454" }
  ]
  theorems := [Cslib.Circuits.Boolean.FormalComplexityMeasure.card_le_four_mul_card]
  scope := "For any fixed arity including zero, if one function has measure at least c, \
    at least one quarter of all truth tables have measure at least c/4. \
    Natural-number cardinalities with denominators cleared; no computational claim. \
    Theorem 22.3's stronger near-total-density endpoint is not included."

register_result "integer-permanent-to-zero-one-permanent" where
  title := "The integer permanent reduces to the 0/1 permanent"
  topic := "counting complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Proposition 6.22",
      locator := "February 2007 draft r3.pdf, PDF p. 24; printed p. 226" }
  ]
  theorems := [
    Cslib.Complexity.intPermanent_eq_recoverPermanent_intTableToZeroOne,
    Cslib.Complexity.metricReducible_intPermanent_zeroOnePermanent,
    Cslib.Complexity.computableInPolyTime_intTableToZeroOne,
    Cslib.Complexity.computableInPolyTime_recoverPermanent,
    Cslib.Complexity.parsimoniousReducible_natPermanent_zeroOnePermanent
  ]
  scope := "Dense integer tables (encIntTable, binary sign-magnitude entries) read as n x n \
    matrices with missing entries 0, mapped by a native polynomial-time machine to dense 0/1 \
    tables (encBoolTable); the integer permanent is recovered in polynomial time from the input \
    and the 0/1 permanent. Entries are reduced modulo 2 n! S^n + 1 with S the sum of absolute \
    entries (Goldreich uses the maximum), then each residue is replaced by a binary chain of \
    relay vertices; the 0/1 dimension is n + 2 L n^2. One-query (metric) reduction, a special \
    case of the source's Cook reduction."

register_result "bpp-proper-subset-ppoly" where
  title := "BPP is strictly contained in P/poly on ordinary bit languages"
  topic := "circuit complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Theorem 6.3",
      locator := "February 2007 draft r3.pdf, PDF p. 9; printed p. 211" }
  ]
  theorems := [
    Cslib.Circuits.Boolean.not_countable_PPoly,
    Cslib.Circuits.Boolean.exists_mem_PPoly_not_isDecidable,
    Cslib.Circuits.Boolean.BPP_ssubset_PPoly
  ]
  scope := "Ordinary bit languages with identity encoding encBits: nonuniform polynomial-size \
    De Morgan circuits strictly contain native seeded-verifier BPP. The witness has no native \
    machine decider and is obtained nonconstructively using P-selective sets/countability. \
    No efficient separator or uniform circuit-family construction. Strictness is not asserted \
    for arbitrary encoded finite instance domains, where the two classes coincide."

register_result "one-bit-advice-undecidable" where
  title := "One bit of advice decides a length-dependent undecidable bit language"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Theorem 3.7 (one-bit undecidability endpoint)",
      locator := "January 2007 draft r2.pdf, PDF p. 6; printed p. 122" }
  ]
  theorems := [
    Cslib.Complexity.length_preimage_mem_PWithAdvice_one,
    Cslib.Complexity.exists_mem_PWithAdvice_one_not_isDecidable
  ]
  scope := "Native polynomial-time decider on framed advice/input pairs, with exactly one \
    arbitrary advice bit per input length. Some accepted bit language has no native machine \
    decider and has the same membership for all words of equal length. Advice need not be \
    computable; no efficient construction of the undecidable advice family is claimed. \
    Arbitrary advice hierarchies and strict P/1 versus P/poly remain separate."

register_result "sat-decidable-envelope-sparse-difference" where
  title := "SAT reductions into a decidable envelope with sparse difference imply SAT in P"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 3.12",
      locator := "January 2007 draft r2.pdf, PDF pp. 19–20; printed pp. 135–136" }
  ]
  theorems := [Cslib.Complexity.SAT_mem_P_of_sparse_diff]
  scope := "Native polynomial-time many-one SAT reduction to S under an explicit target \
    encoding; S is contained in a set G in P, and G minus S is sparse in prefix-census form. \
    Concludes SAT in P. G need not be sparse and S need not be decidable. Reuses Fortune \
    through a guarded UNSAT reduction; does not implement the source DFS proof."

register_result "boolean-ring-arithmetic-simulation" where
  title := "Boolean circuits simulated over any ring with size factor five"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (Boolean-to-arithmetic direction)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Boolean.exists_ring_simulation]
  scope := "Any De Morgan circuit has an arithmetic circuit over any ring with at most \
    five times its gate count, preserving all outputs on zero/one-represented Boolean inputs. \
    Arithmetic uses constant/addition/multiplication gates; constants count and wires are free. \
    The zero/one representation is injective for nontrivial rings. No arbitrary ring-input \
    agreement, reverse simulation, formal polynomial identity or compiler-runtime claim."

register_result "arithmetic-bit-synthesis-injective-encoding" where
  title := "Arithmetic bit-synthesis with injective fixed-width encodings"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (synthesis-direction milestone)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Synthesis.bitBlast_arithmetic]
  scope := "Arithmetic circuits on a semiring with supplied w-bit encoding and total decoder \
    satisfying a left-inverse law. Given already-available encoded input functions, all output \
    bits cost at most size * bitBlastCost w additional De Morgan gates. The encoding need not \
    be surjective, admitting odd fields. No free-input compiler, reverse simulation, encoding \
    construction or runtime claim; the full finite-field exercise remains open."

register_result "encoded-circuit-boolean-simulation" where
  title := "Boolean circuits for left-invertibly encoded bounded-arity computations"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (forward circuit milestone)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Circuit.exists_encoded_boolean]
  scope := "Any interpreted circuit of arity at most two, with a supplied w-bit encoding and \
    decoder left inverse, has a Boolean circuit on N*w free inputs with M*w outputs, costing \
    at most size * bitBlastCost w gates. Correctness holds on valid encoded inputs, packed \
    wire-major by blocksEquiv.symm. Constants count as gates and wiring is free. No encoding \
    construction, reverse general-field simulation or compiler-runtime claim."

register_result "exact-advice-strict-hierarchy" where
  title := "Strict exact-advice hierarchy"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2,
      theorem := "Theorem 3.7; Exercise 3.3 / Theorem 4.1 with positive gap and capacity",
      locator := "January 2007 r2.pdf, PDF pp. 6, 16, 22; printed pp. 122, 132, 138" },
    { paper := GoldreichAdviceHierarchyAddendum,
      theorem := "Revised Theorem 4.1, positive one-bit difference",
      locator := "Online addendum, theorem and exact/no-exception technical note" }
  ]
  theorems := [
    Cslib.Complexity.PWithAdvice_ssubset_of_lt,
    Cslib.Complexity.PWithAdvice_pred_ssubset,
    Cslib.Complexity.PWithAdvice_const_ssubset_succ
  ]
  scope := "Strict pointwise growth and eventual upper truth-table capacity give strict \
    containment of exact-advice classes, with arbitrary noncomputable bounds/advice and a \
    native complete-pair polynomial clock. Includes positive predecessor, every constant \
    advice hierarchy. Does not prove the displayed hierarchy without positivity, or a \
    separation allowing finitely many errors."

register_result "constant-advice-strict-subset-ppoly" where
  title := "Every constant advice class is strictly smaller than P/poly"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2,
      theorem := "Theorem 3.7, strictness in the following paragraph",
      locator := "January 2007 r2.pdf, PDF p. 6; printed p. 122" }
  ]
  theorems := [Cslib.Circuits.Boolean.PWithAdvice_const_ssubset_PPoly]
  scope := "Every constant exact-advice class, including P/1, is strictly contained in \
    P/poly on bit languages. Uses the native full-pair polynomial-time advice class and \
    its existing polynomial-advice/circuit bridge; no uniform advice is claimed."

register_result "finite-carrier-boolean-simulation" where
  title := "Constant-factor Boolean simulation over every finite nonempty carrier"
  topic := "circuit complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 14, Exercise 1 (arithmetic-to-Boolean direction)",
      locator := "Web draft 2007-01-08, printed p. 265; PDF p. 281" }
  ]
  theorems := [Cslib.Circuits.Circuit.exists_finite_boolean]
  scope := "Any arity-at-most-two interpreted circuit over finite nonempty F is simulated \
    on valid encoded inputs by a Boolean circuit with all outputs and at most \
    size * bitBlastCost (Nat.clog 2 (Fintype.card F)) gates. The fixed encoding \
    fintypeEncoding uses a finite enumeration and least-significant-bit-first indexBits. \
    Constants count; wiring is free. No supplied encoding hypothesis, reverse simulation, \
    formal polynomial identity or uniform runtime claim; the enumeration is noncomputable."

register_result "exact-advice-length-comparison-qualification" where
  title := "Unbounded nonnegative gaps do not imply exact-advice containment"
  topic := "complexity theory"
  sources := [
    { paper := Goldreich2007DraftR2,
      theorem := "Exercise 3.3 / Theorem 4.1 (model qualification)",
      locator := "January 2007 r2.pdf, PDF pp. 16, 22; printed pp. 132, 138" },
    { paper := GoldreichAdviceHierarchyAddendum,
      theorem := "Theorem 4.1 revised (fixed-gap contrast, not refuted)",
      locator := "Online addendum, theorem and proof after the December 2014 discussion" }
  ]
  theorems := [
    Cslib.Complexity.PWithAdvice_subset_of_lt,
    Cslib.Complexity.PWithAdvice_subset_succ,
    Cslib.Complexity.exists_nonmonotone_advice_bounds
  ]
  scope := "Original counterexample for arbitrary exact-length advice: polynomial lower/gap \
    bounds, both draft capacity bounds and an unbounded nonnegative gap do not force class \
    containment. No computability of bounds/advice is claimed. Strict pointwise growth does \
    preserve inclusion by delimiter padding. This qualifies a reading of the displayed draft \
    hypotheses; it neither refutes nor completes positive-gap or official fixed-gap hierarchy \
    theorems."

register_result "sensitivity-relevant-coordinates" where
  title := "All-relevant Boolean functions have logarithmic maximum sensitivity"
  topic := "query complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 11, Exercise 1",
      locator := "Web draft 2007-01-08, printed p. 218; PDF p. 234" }
  ]
  theorems := [
    Cslib.BitString.card_relevant_le_sensitivity_mul_four_pow,
    Cslib.BitString.clog_le_three_mul_sensitivity_of_depends_on_all
  ]
  scope := "Total Boolean functions on n bits, using native maximum sensitivity. The number \
    of coordinates sensitive at some input is at most s(f)*4^s(f). If every coordinate is \
    relevant, Nat.clog 2 n ≤ 3*s(f), an explicit uniform logarithmic lower bound, including \
    the n=0 convention. Irrelevant coordinates are excluded from the cardinality theorem."

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

register_result "goldreich-levin-hard-core" where
  title := "Goldreich–Levin: every one-way function has a hard-core predicate, and one-way \
    permutations yield pseudorandom generators"
  topic := "cryptography"
  sources := [
    { paper := GoldreichLevin1989, theorem := unverified, locator := unverified },
    { paper := Goldreich2007Draft, theorem := "Theorem 7.7",
      locator := "March 2007 draft r4.pdf, PDF p. 12; printed p. 276" }
  ]
  theorems := [
    Cslib.Crypto.GoldreichLevin.padded_hardCore,
    Cslib.Crypto.OneWayPermutation.pseudorandomGenerator
  ]
  scope := "For every uniform one-way function f on bit strings, the inner product of the two \
    seed halves is hard-core for the padded function (x, r, s) ↦ (f x, r, s), with at most one \
    spare bit s so that every seed length is covered, against uniform strict PPT predictors \
    with negligible bias. This is not a hard-core predicate for f itself. For a length-preserving \
    one-way permutation, appending that bit gives a deterministic polynomial-time generator with \
    one-bit stretch, secure against uniform strict PPT distinguishers. Asymptotic security; the \
    source's explicit runtime and advantage trade-off is not stated."

register_result "naor-yung-uowhf" where
  title := "Naor–Yung: one-way permutations yield universal one-way hash functions"
  topic := "cryptography"
  sources := [
    { paper := NaorYung1989, theorem := unverified, locator := "Section 3" },
    { paper := Goldreich2004, theorem := unverified, locator := "Section 6.4.3.2" }
  ]
  theorems := [
    Cslib.Crypto.OneWayPermutation.targetCollisionResistant_naorYungHash,
    Cslib.Crypto.OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily
  ]
  scope := "Every uniform one-way permutation f on bit strings gives a keyed hash family on all \
    bit strings, with polynomial-time keys, digests and evaluation, that is target \
    collision-resistant: a uniform strict PPT adversary that commits to a target before seeing \
    the key finds a distinct colliding input with negligible probability. Each compression step \
    uses a pivot-deletion quotient instead of the source's universal hash; a binary tree extends \
    the domain. Asymptotic security; no compact key-length bound."

register_result "inaccessible-entropy-from-owf" where
  title := "Inaccessible average max-entropy from any one-way function"
  topic := "cryptography"
  sources := [
    { paper := HHRVW2020, theorem := "Theorem 4.5", locator := "Section 4.2, p. 21" }
  ]
  theorems := [
    Cslib.Crypto.OneWay.rompelBase_logGap,
    Cslib.Crypto.OneWay.exists_rompelBase_logGap,
    Cslib.Crypto.OneWay.exists_inaccessibleEntropyFamily_logGap
  ]
  scope := "Every uniform one-way function on bit strings yields a single uniform polynomial-time \
    fixed-width function family whose accessible average max-entropy against uniform strict PPT \
    adversaries is eventually at most H(Z | F₀(Z)) - d log₂ n / n for every constant d > 0, \
    witnessed at each d > 0 by an adversary-independent accessible preimage set family with \
    polynomial light-image threshold and packaged as an InaccessibleEntropyFamily with \
    Θ(n / log n) gap denominator."

register_result "rompel-uowhf" where
  title := "Rompel: one-way functions yield universal one-way hash functions"
  topic := "cryptography"
  sources := [
    { paper := Rompel1990, theorem := unverified, locator := unverified },
    { paper := HHRVW2020, theorem := "Theorem 5.1", locator := "Section 5.1, p. 26" }
  ]
  theorems := [
    Cslib.Crypto.ShrinkingCollisionGrid.targetCollisionResistant_rompelHash,
    Cslib.Crypto.AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash,
    Cslib.Crypto.OneWay.exists_targetCollisionResistant_keyedHashFamily
  ]
  scope := "Every uniform polynomial-time function family with inaccessible average max-entropy \
    against adversary-dependent accessible sets (Definition 3.9, \
    AdversaryInaccessibleEntropyFamily), and hence every uniform one-way function on bit strings, \
    gives a target collision-resistant keyed hash family on all bit strings against uniform \
    strict PPT adversaries that commit to a target before seeing the key. `rompelHash` is secure \
    for every shrinking collision grid. Each one-bit step takes a fresh subkey, so keys are \
    polynomial but not as compact as the source's O(|y| log t) bound. Asymptotic security."

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

register_result "communication-tiling-fooling" where
  title := "Fooling sets bound arbitrary monochromatic tilings"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 12.8",
      locator := "Web draft 2007-01-08; printed p. 224 / PDF p. 240" }
  ]
  theorems := [Cslib.Communication.IsFoolingSet.card_le_partition,
    Cslib.Communication.IsFoolingSet.card_le_tilingNumber]
  scope := "A finite fooling set for one label injects into pieces with that label in every \
    arbitrary finite labelled rectangle partition. Its cardinality bounds the minimum \
    tilingNumber in extended naturals; no protocol-tree realization is assumed."

register_result "communication-tiling-rank" where
  title := "Zero/one matrix rank bounds arbitrary monochromatic tilings"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 12.10",
      locator := "Web draft 2007-01-08; printed p. 224 / PDF p. 240" }
  ]
  theorems := [Cslib.Communication.RectanglePartition.rank_communicationMatrix_le,
    Cslib.Communication.rank_communicationMatrix_le_tilingNumber]
  scope := "The zero/one communication matrix over a commutative semiring with the strong \
    rank condition has rank at most the true-labelled pieces of every arbitrary tiling, \
    hence at most the minimum tiling number. Finite columns; fields are included. \
    This is not a sign-matrix rank bound or a protocol-realization theorem."

register_result "communication-rank-distinct-rows" where
  title := "Zero/one rank bounds deterministic communication from above"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 12, Exercises 4 (corrected) and 6",
      locator := "Web draft 2007-01-08; printed p. 232 / PDF p. 248" }
  ]
  theorems := [Cslib.Communication.card_image_le_two_pow_rank,
    Cslib.Communication.ecomplexityFun_le_rank_add_one,
    Cslib.Communication.le_rank_of_injective,
    Cslib.Communication.clog_le_ecomplexityFun_of_injective]
  scope := "A zero/one matrix of rank r over a field has at most 2^r distinct rows. Hence \
    C(f) <= rank_K M(f) + 1 for finite inputs and every field K; the printed Exercise 4 lacks \
    its relation symbol, and this is its evident repair. Pairwise distinct rows on n-bit \
    inputs give rank >= n and C(f) >= ceil(log2 n), with no n >= 1 hypothesis. C(f) is \
    the depth of leaf-labelled protocol trees in which both players know the output."

register_result "communication-tiling-discrepancy" where
  title := "Discrepancy bounds the minimum arbitrary monochromatic tiling size"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 12.11",
      locator := "Web draft 2007-01-08; printed p. 225 / PDF p. 241" }
  ]
  theorems := [Cslib.Communication.one_le_tilingNumber_mul_discrepancy,
    Cslib.Communication.one_div_discrepancy_le_tilingNumber]
  scope := "Any PMF on finite rectangular input sets: one is at most minimum tiling size \
    times discrepancy, and reciprocal discrepancy is at most that finite minimum. \
    Uniform equal bit cubes recover the draft normalization. A PMF excludes empty input \
    products; the tiling model separately permits empty products and charged empty pieces."

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

register_result "communication-spectral-discrepancy" where
  title := "Uniform discrepancy bounded by the Euclidean operator norm"
  topic := "communication complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 12.13 (corrected operator-norm version)",
      locator := "Web draft 2007-01-08; printed p. 225 / PDF p. 241" }
  ]
  theorems := [Cslib.Communication.discrepancy_uniformOfFintype_le_l2_opNorm,
    Cslib.Communication.discrepancy_uniformOfFintype_mul_sqrt_card_le_l2_opNorm,
    Cslib.Communication.discrepancy_bitString_le_l2_opNorm]
  scope := "Finite nonempty rectangular input sets and uniform PMF: discrepancy is at most \
    the real sign matrix's Euclidean operator norm divided by sqrt(|X|*|Y|), or by 2^n \
    on equal n-bit cubes. Decidable equality on columns. The sign convention differs by \
    an overall minus sign from the draft. This corrects its false unrestricted eigenvalue \
    bound; no general spectral-radius or numerical norm-computation claim is made."

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

register_result "seedless-extraction-impossibility" where
  title := "Deterministic seedless extraction fails even with only one bit of entropy loss"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 16, exercise 7",
      locator := "January 8, 2007 draft, printed page 319 (PDF page 335)" }
  ]
  theorems := [
    Cslib.Probability.exists_minEntropy_map_first_eq_pure,
    Cslib.Probability.not_isExtractor_bitString
  ]
  scope := "For positive n and m, every deterministic map from n bits to m bits has a finite \
    source of real min-entropy at least n - 1 whose first output bit is constant and whose \
    output distance from uniform is at least 1/2. No efficiency hypothesis. Exercise 12 and \
    the broader extractor objectives are not covered."

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

register_result "partial-mcsp-rp-hard" where
  title := "Hirahara: Partial MCSP is NP-hard under randomized reductions"
  topic := "meta-complexity"
  sources := [
    { paper := Hirahara2022, theorem := "Theorem I.2",
      locator := "p. 971, \"In particular\"" }
  ]
  theorems := [
    Cslib.PartialMCSP.rpHard,
    Cslib.PartialMCSP.rpHard_encBinary,
    Cslib.PartialMCSP.rpReducible_GapCMMSA_PartialMCSP,
    Cslib.PartialMCSP.NP_subset_BPP_of_mem_BPP,
    Cslib.PartialMCSP.NP_subset_coRP_of_mem_coRP
  ]
  scope := "Every NP language reduces to PartialMCSP (the partial truth table, then the size \
    threshold in unary, or in binary for rpHard_encBinary) by a polynomial-time randomized \
    many-one reduction with one-sided error: yes maps to yes always, no to no with probability \
    at least 2/3. Library route: from the library's GapCMMSA Δ g 1 (NP-hard via label cover) by \
    the library's own seeded construction and analysis; the source fixes the statement, not the \
    proof. The inapproximability and average-case forms of Theorem I.2 are not formalized. \
    The BPP and coRP inclusions are conditional on PartialMCSP being in BPP or coRP; they follow \
    from the reduction and are not stated separately in the source."

register_result "multi-mcsp-np-hard" where
  title := "Ilango–Loff–Oliveira: Multi-output MCSP is NP-hard under randomized reductions"
  topic := "meta-complexity"
  sources := [
    { paper := IlangoLoffOliveira2020, theorem := "Theorem 4",
      locator := "p. 22:5; reduction in Section 4.2, pp. 22:20–22:21" }
  ]
  theorems := [
    Cslib.MultiMCSP.rpHard,
    Cslib.MultiMCSP.rpHard_pos,
    Cslib.MultiMCSP.rpReducible_gapSetCover,
    Cslib.MultiMCSP.NP_subset_BPP_of_mem_BPP,
    Cslib.MultiMCSP.NP_subset_coRP_of_mem_coRP
  ]
  scope := "Every NP language reduces to Multi-output MCSP (n, m and s in unary, then the m \
    tables) by a polynomial-time randomized many-one reduction with one-sided error: yes maps \
    to yes always, no to no with probability at least 2/3; the reduction lands in Definition \
    1's positive instances. Over any De Morgan basis: Boolean.DeMorgan.interpretation is \
    Definition 1's constant-free AND/OR/NOT basis, Boolean.interpretation the library variant \
    with constants. Library route: from the library's GapSetCover 3 rather than Trevisan's \
    bounded Set Cover; soundness by a union bound over small circuits in place of Lemma 16; \
    windows as OR chains rather than canonical DNFs; the positions of the ground list in \
    place of its distinct elements. The BPP and coRP inclusions are conditional on Multi-MCSP \
    being in BPP or coRP; they follow from the reduction and are not stated separately in the \
    source."

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
    whenever s₁ ≤ s₂; OPS's own proof through the efficient anti-checker (Lemma 4.1, registered \
    as efficient-anti-checker) is not formalized."

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

register_result "depth-five-imm" where
  title := "OpenAI: homogeneous depth-five circuits for iterated matrix multiplication"
  topic := "algebraic complexity"
  sources := [
    { paper := OpenAI2026DepthFive,
      theorem := "Corollary 6.1 (characteristic zero); Theorem 1.1 is its complex case",
      locator := "§6, p. 19; §1.1, p. 2" }
  ]
  theorems := [
    Cslib.Circuits.DepthFive.exists_forall_rpow_le_size,
    Cslib.Circuits.DepthFive.rpow_le_size
  ]
  scope := "Over every field of characteristic zero and for every n ≥ exp 29200, every \
    syntactically homogeneous ΣΠΣΠΣ circuit computing IMM_{n,n} as a formal polynomial has at \
    least n^(√n/400) lower product, middle sum and upper product gates; bottom linear forms \
    are unrestricted and gates are shared. The count is of the normalized model \
    Cslib.Circuits.DepthFive.Circuit, which is at most the source's gate count; no formal \
    conversion from a layered circuit is proved. The source's threshold is unspecified; here \
    it is exp 29200, not optimized. Lower bound only; the matching construction is the \
    entry depth-five-imm-upper. Not proved in positive characteristic."

register_result "depth-five-imm-upper" where
  title := "OpenAI: a homogeneous depth-five circuit for iterated matrix multiplication"
  topic := "algebraic complexity"
  sources := [
    { paper := OpenAI2026DepthFive, theorem := "the block construction of §6",
      locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.DepthFive.exists_circuit_size_le_rpow,
    Cslib.Circuits.DepthFive.exists_circuit_imm_of_le_mul
  ]
  scope := "Over every commutative semiring and for every n ≥ 2, some syntactically \
    homogeneous ΣΠΣΠΣ circuit computes IMM_{n,n} as a formal polynomial with at most \
    n^(√n + 4) lower product, middle sum and upper product gates; for n ≤ r·t the exact count \
    is r·n^(t+1) + r·n² + n^(r+1). Normalized model Cslib.Circuits.DepthFive.Circuit: leaves \
    and bottom sums are not counted, and there are n^(r+1) upper products where the source \
    has n^(r-1). With depth-five-imm the size is n^Θ(√n) over characteristic zero."

register_result "hitting-set-derivative-closed" where
  title := "Polynomial hitting sets for small partial-derivative spaces"
  topic := "algebraic complexity"
  sources := [
    { paper := BhardwajEtAl2026, theorem := "Theorems 1.1 and 4.1 (revision 1)",
      locator := "§1, §4" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_logHittingSet,
    Cslib.Circuits.Arithmetic.aeval_logCurve_ne_zero,
    Cslib.Circuits.Arithmetic.isHittingSet_sum_pow
  ]
  scope := "Over a field of characteristic zero, a nonzero n-variate polynomial lying in a \
    space of dimension at most r closed under all partial derivatives does not vanish on the \
    curve ln(1 + (i+1)t) truncated below degree n·r² + r; the points of the curve at \
    t = 0, …, d(n·r² + r) are a hitting set for such polynomials of degree at most d, and \
    sums of s d-th powers of linear forms have a hitting set of d(n·(s(d+1))² + s(d+1)) + 1 \
    points. Existence and size of an explicit set only: no bit complexity, no black-box \
    algorithm model, nothing in positive characteristic, and not the source's extension to \
    noncommutative ABPs."

register_result "support-concentrating-shifts" where
  title := "Support-concentrating shifts for multilinear polynomials of small split rank"
  topic := "algebraic complexity"
  sources := [
    { paper := ForbesSaptharishiShpilka2014,
      theorem := "Theorem 4.1 with Lemma 4.4, for individual degree one",
      locator := "§4, pp. 21–23 (arXiv v1)" },
    { paper := Shpilka2026, theorem := "Theorem 2.3 and Corollary 2.4, for δ = 1",
      locator := "§2, p. 5" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.exists_mem_concentratingShifts_perfectHashFamily,
    Cslib.Circuits.Arithmetic.card_concentratingShifts_perfectHashFamily_le,
    Cslib.Circuits.Arithmetic.exists_mem_concentratingShifts
  ]
  scope := "Over a field of characteristic zero, an explicit set of at most \
    (n²·2^(25(⌊lg w⌋+1)) + 1)(n·2^(⌊lg w⌋+1) + 1) points such that every nonzero multilinear \
    polynomial in n variables that is a sum of w products across every split of ⌊lg w⌋ + 1 \
    variables from the rest has, after shifting by one of the points, a monomial with at most \
    ⌊lg w⌋ variables. Individual degree one only, by a direct argument and not the sources' \
    rank condensers; the support bound ⌊lg w⌋ is smaller than the sources' ⌊lg w²⌋. The set is \
    built from a perfect hash family of the library and not from the Klivans–Spielman \
    generator. Split rank is a decomposition into products, not a coefficient-matrix rank or \
    a branching program. No hitting set for read-once branching programs is claimed here."

register_result "hitting-set-multilinear-any-order-roabp" where
  title := "Polynomial-size hitting sets for multilinear any-order ROABPs"
  topic := "algebraic complexity"
  sources := [
    { paper := Shpilka2026, theorem := "Theorem 1.1, in characteristic zero; Lemmas 3.1–3.4",
      locator := "§1.1 p. 3, §3 pp. 6–9" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_anyOrderHittingSet_roabp,
    Cslib.Circuits.Arithmetic.isHittingSet_anyOrderHittingSet,
    Cslib.Circuits.Arithmetic.card_anyOrderHittingSet_le,
    Cslib.Circuits.Arithmetic.IsAnyOrderROABP.splitRankLE
  ]
  scope := "Over a field of characteristic zero, an explicit set of points in Fⁿ, of size \
    bounded by an explicit polynomial in n and w, that contains a non-root of every nonzero \
    multilinear n-variate polynomial computed by width-w read-once oblivious branching \
    programs in every variable order; more generally of every multilinear polynomial that is \
    a sum of w products across every split of the variables. Characteristic zero only: the \
    source's positive-characteristic case rests on an unpublished hitting set. The perfect \
    hash family and the shifts are the library's own constructions, so the size bound \
    differs from the source's. Existence and size of an explicit set only: no bit \
    complexity and no black-box algorithm model. The converse of Nisan's characterisation \
    is not proved."

register_result "hitting-set-set-multilinear-depth-three" where
  title := "Hitting sets for set-multilinear depth-3 circuits with small variable sets"
  topic := "algebraic complexity"
  sources := [
    { paper := Shpilka2026, theorem := "Theorem 1.2, in characteristic zero; Lemma 3.4",
      locator := "§1.1 p. 3, §3 pp. 8–9" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_setMultilinearHittingSet_sum_prod,
    Cslib.Circuits.Arithmetic.isHittingSet_setMultilinearHittingSet,
    Cslib.Circuits.Arithmetic.card_setMultilinearHittingSet_le
  ]
  scope := "Over a field of characteristic zero, for variables in n blocks of d, an explicit \
    set of points of size at most an explicit polynomial in n, d and s times \
    (d + 1)^(⌊lg s⌋ + 1), that contains a non-root of every nonzero sum of s products of n \
    linear forms, the j-th in the variables of block j; more generally of every polynomial \
    whose monomials have at most one variable of each block, to the first power, and that is \
    a sum of s products across every union of blocks. Characteristic zero only: the source's \
    positive-characteristic case rests on an unpublished hitting set. Blocks are Fin n × Fin d, \
    not a general partition. The support-concentrating shifts for individual degree d have \
    the statement the source cites from Forbes–Saptharishi–Shpilka, with a proof that is not \
    from a source; the perfect hash family is the library's, so the size bound differs from \
    the source's. Existence and size of an explicit set only: no bit complexity and no \
    black-box algorithm model."

register_result "hitting-set-constant-depth" where
  title := "Subexponential hitting sets for constant-depth formulas from the LST lower bound"
  topic := "algebraic complexity"
  sources := [
    { paper := LimayeSrinivasanTavenas2021, theorem := "Corollary 6, via Lemma 18",
      locator := "printed p. 5 and §6 p. 13, ECCC TR21-081 rev. 1" },
    { paper := ChouKumarSolomon2019, theorem := "Theorem 2.3",
      locator := "printed p. 3 (arXiv:1803.05933v1)" },
    { paper := BhattacharjeeEtAl2025, theorem := "Theorems 4.1 and 6.1",
      locator := "printed pp. 19–20 and 28 (arXiv:2506.23214v1)" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_rpow,
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_circuit_rpow,
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet,
    Cslib.Circuits.Arithmetic.eventually_card_constantDepthHittingSet_le,
    Cslib.Circuits.Arithmetic.eventually_isHittingSet_constantDepthHittingSet_circuit
  ]
  scope := "Over a field of characteristic zero, for every product-depth Δ, exponent c and \
    real ε > 0, for all large n: an explicit set of at most 2^(n^ε) points of Kⁿ containing a \
    non-root of every nonzero polynomial computed by an unbounded fan-in formula of \
    product-depth at most Δ with at most n^c nodes, and, at a larger exponent, by a simple \
    circuit of product-depth at most Δ with at most n^c gates. A finite form of LST \
    Corollary 6, which is an identity test with running time (s^(Δ+1) n)^O(n^μ) for depth \
    o(log log log n): here constant product-depth, existence and size of an explicit set with \
    non-explicit large-n thresholds, no running time or uniformity, characteristic zero only."

register_result "hitting-set-noncommutative-abp" where
  title := "Quasipolynomial hitting sets of matrices for non-commutative ABPs"
  topic := "algebraic complexity"
  sources := [
    { paper := ForbesShpilka2013,
      theorem := "Construction 4.1, Lemmas 4.2, 4.3, 4.5 and Theorem 4.6, for homogeneous \
        layered programs; not Corollary 4.7",
      locator := "§1.1 pp. 2–3, §4 pp. 22–24 (arXiv:1209.2408v2)" },
    { paper := AgrawalGurjarKorwarSaxena2015,
      theorem := "Theorem 1, in the adapted form of hitting-set-roabp-unknown-order",
      locator := "§1 and §3 of arXiv:1406.7535" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.exists_mem_noncommABPHittingSet_lift_ne_zero,
    Cslib.Circuits.Arithmetic.card_noncommABPHittingSet_le
  ]
  scope := "Over a field of characteristic zero, an explicit set of n-tuples of \
    (d + 1) × (d + 1) matrices such that every nonzero polynomial computed by a homogeneous \
    layered non-commutative branching program of degree d in n variables with all layers of \
    width at most W is nonzero at one of the tuples. The set is the image of the hitting set \
    for read-once oblivious programs in d variables, width W and layer degree n - 1, so its \
    size is (ndW)^O(log d). The reduction to read-once oblivious programs is that of \
    Forbes–Shpilka; the hitting set for those is the library's adaptation of \
    Agrawal–Gurjar–Korwar–Saxena (a different weight family, levels combined one at a \
    time), not Forbes–Shpilka's generator, so the size is neither paper's bound. Homogeneous \
    layered programs only. No white-box algorithm and no bit complexity."

register_result "hitting-set-roabp-unknown-order" where
  title := "Quasipolynomial hitting sets for ROABPs in an unknown order"
  topic := "algebraic complexity"
  sources := [
    { paper := AgrawalGurjarKorwarSaxena2015,
      theorem := "Theorem 1, for univariate layers, in characteristic zero; Lemmas 6 and 8",
      locator := "§1 and §3 of arXiv:1406.7535" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_roabpHittingSet,
    Cslib.Circuits.Arithmetic.card_roabpHittingSet_le,
    Cslib.Circuits.Arithmetic.roabpPrime_le
  ]
  scope := "Over a field of characteristic zero, an explicit set of points of Fⁿ that contains \
    a non-root of every nonzero n-variate polynomial computed by a width-w read-once \
    oblivious branching program in some order of the variables with layer entries of degree \
    at most δ; the set does not depend on the order. Its size is at most \
    (⌈lg n⌉ + 1) p^⌈lg n⌉ (nδ(nδp + 1 + p)^⌈lg n⌉ + 1) for a prime p ≤ 2(2n²w⁸ + δ + 1), \
    which is (nδw)^O(log n). Univariate layers only, not the source's sparse-factor layers. \
    The weights are aⁱ⁺¹ mod p for one prime p instead of the source's (δ + 1)ⁱ mod q over \
    many primes, and the levels are combined one at a time, so the bound is not the \
    source's. Characteristic zero only. Existence and size of an explicit set: no bit \
    complexity and no black-box algorithm model."

register_result "hitting-set-sparse" where
  title := "Ben-Or–Tiwari: a hitting set for sparse polynomials"
  topic := "algebraic complexity"
  sources := [
    { paper := BenOrTiwari1988, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_primePowers,
    Cslib.Circuits.Arithmetic.isHittingSet_powerHittingSet
  ]
  scope := "Over a domain of characteristic zero, the s points (p₁ʲ, …, pₙʲ), j < s, of powers \
    of the first n primes hit every nonzero n-variate polynomial with at most s monomials, \
    whatever its degree; more generally for any point whose monomials are pairwise distinct. \
    Zero test only: no interpolation algorithm, no bit complexity, nothing in positive \
    characteristic."

register_result "hitting-set-sparse-affine-orbit" where
  title := "Polynomial-size hitting sets for affine orbits of sparse polynomials"
  topic := "algebraic complexity"
  sources := [
    { paper := BhargavaSengupta2026,
      theorem := "Theorem 1.2 items 1 and 2, in characteristic zero; Lemmas 1.6, 3.1 and 3.2",
      locator := "§1.1 p. 3, §3 pp. 8–9, §4 pp. 9–10" }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.isHittingSet_sparseOrbitHittingSet,
    Cslib.Circuits.Arithmetic.card_sparseOrbitHittingSet_le
  ]
  scope := "Over a field of characteristic zero, an explicit set of at most \
    (n² + 1)(2d(ns² + s) + 1) points of Fⁿ that contains a non-root of every nonzero \
    polynomial p(Ax + b) of degree at most d, with A an invertible matrix and p a polynomial \
    with at most s monomials. The key lemma: if all coordinates of u are nonzero, the partial \
    derivatives of the lowest nonzero homogeneous component of p(x + u) span a space of \
    dimension at most the number of monomials of p. Ordinary partial derivatives instead of \
    the source's Hasse derivatives, so characteristic zero throughout, although the source's \
    lemma holds in every characteristic. The curve is the library's ln(1 + (i + 1)t) \
    truncated below degree ns² + s, not the source's -ln(1 - it) truncated at that degree. \
    Not the degree-free hitting set over the reals, the lower bound, the applications to \
    other orbit classes, or the operation count. Existence and size of an explicit set only: \
    no bit complexity and no black-box algorithm model."

register_result "hitting-set-lower-bound" where
  title := "Heintz–Schnorr: hitting sets give lower bounds"
  topic := "algebraic complexity"
  sources := [
    { paper := HeintzSchnorr1980, theorem := unverified, locator := unverified },
    { paper := Agrawal2005, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Circuits.Arithmetic.IsHittingSet.exists_notMem,
    Cslib.Circuits.Arithmetic.exists_ne_zero_forall_eval_eq_zero
  ]
  scope := "Over a field, if H is a hitting set for a class and T is a finite set of \
    monomials with more elements than H, some nonzero polynomial with monomials in T is not \
    in the class. Existence by a dimension count; the polynomial is not exhibited and its \
    complexity is not bounded."

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

register_result "goldreich-sharp-three-sat-to-integer-permanent" where
  title := "#3SAT reduces to the permanent of small-integer matrices"
  topic := "counting classes"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Proposition 6.21",
      locator := "February 2007 draft r3.pdf, PDF pp. 24–27; printed pp. 226–229" }
  ]
  theorems := [
    Cslib.Complexity.goldreich_prop_6_21,
    Cslib.Complexity.metricReducible_sharpThreeSAT_intPermanent
  ]
  scope := "c = 12 and I = {-1, 0, 1, 2, 3}: a native polynomial-time map from encCNF to the \
    dense integer-table encoding with perm(M_φ) = 12^m · #3SAT(φ) for every CNF φ with m \
    clauses, using Goldreich's Figure 6.3 gadget. Counts are over the variables occurring in \
    φ; formulas with an empty or over-long clause map to the 1×1 zero matrix. Not the 0/1 \
    permanent endpoint (Proposition 6.22) nor Theorem 6.20."

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

register_result "adaboost-training-error" where
  title := "AdaBoost training-error bound"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 10.2", locator := "pp. 135–137" },
    { paper := MohriRostamizadehTalwalkar2018, theorem := "Theorem 7.2", locator := "p. 149" }
  ]
  theorems := [
    Cslib.MachineLearning.Boosting.empiricalMiscount_adaBoost_le_prod,
    Cslib.MachineLearning.Boosting.empiricalMiscount_adaBoost_le_exp_sum,
    Cslib.MachineLearning.Boosting.empiricalMiscount_adaBoost_le_exp,
    Cslib.MachineLearning.Boosting.IsWeakLearner.empiricalMiscount_adaBoost_eq_zero
  ]
  scope := "AdaBoost on a finite labelled sample with a deterministic weak learner mapping \
    weights on the sample to a Boolean hypothesis. If every round has weighted error < 1, the \
    training error after T rounds is at most the product of 2 √(ε_t (1 - ε_t)), hence at most \
    exp(-2 Σ_t (1/2 - ε_t)²); if every \
    ε_t ≤ 1/2 - γ with γ ≥ 0, it is at most exp(-2 γ² T), and a weak learner of edge γ gives \
    a consistent output once log m < 2 γ² T. A round with ε_t = 0 stops AdaBoost with its \
    consistent hypothesis; vote ties predict false. Generalization is not covered."

register_result "fundamental-theorem-statistical-learning" where
  title := "The fundamental theorem of statistical learning on countable domains"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 6.7",
      locator := "Section 6.4, p. 72" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.tfae_hasFiniteVCDim,
    Cslib.MachineLearning.PACLearning.isPACLearnable_univ_iff_hasFiniteVCDim,
    Cslib.MachineLearning.PACLearning.isPACLearnable_realizableDistributions_iff_hasFiniteVCDim
  ]
  scope := "Binary classes with the 0-1 loss on a countable domain with measurable singletons. \
    Uniform convergence and learnability by every ERM use one sample-size threshold for all \
    ERMs, where the source lets it depend on the ERM rule; the equivalence is unaffected. \
    Agnostic learnability implies finite VC dimension on every domain with measurable \
    singletons (IsPACLearnable.hasFiniteVCDim_of_univ). The quantitative bounds of Theorem 6.8 \
    and the upper bounds on uncountable domains are not proved."

register_result "rlm-stability" where
  title := "Stability and oracle inequality of Tikhonov-regularized loss minimization"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Corollaries 13.6, 13.8 and 13.9",
      locator := "Sections 13.3.1 and 13.4" }
  ]
  theorems := [
    Cslib.MachineLearning.IsRLM.isReplaceOneStable_tikhonov,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_tikhonov,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_add_sqrt
  ]
  scope := "Regularizer r‖w‖² on a convex subset K of a real inner product space, losses convex \
    and ρ-Lipschitz on K, m i.i.d. examples from an arbitrary probability measure. The rule \
    minimizes over K and the comparator ranges over K. The replace-one stability rate proved is \
    ρ² / (r m), half the source's; the oracle inequalities are stated with the source's \
    constants. Integrability of the losses of the rule's output is a hypothesis."

register_result "rlm-smooth-stability" where
  title := "Stability and oracle inequality of Tikhonov-regularized loss minimization for smooth \
    losses"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Corollaries 13.7, 13.10 and 13.11",
      locator := "Sections 13.3.2 and 13.4" }
  ]
  theorems := [
    Cslib.MachineLearning.IsRLM.replaceOneGap_le_tikhonov_of_lipschitzWith_fderiv,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_tikhonov_of_lipschitzWith_fderiv,
    Cslib.MachineLearning.IsRLM.integral_trueRisk_le_add_of_lipschitzWith_fderiv
  ]
  scope := "Regularizer r‖w‖² on a convex subset K of a real inner product space, losses convex \
    on K, nonnegative, and differentiable on the whole space with β-Lipschitz derivative, m \
    i.i.d. examples from an arbitrary probability measure. Corollaries 13.7 and 13.10 are proved \
    with the factor 5β / (r m) in place of the source's 48β / (r m); Corollary 13.11 keeps the \
    source's parameters, for which the factor 48 does not suffice. Integrability of the losses \
    of the rule's output is a hypothesis."

register_result "ridge-regression-learnability" where
  title := "Learnability by ridge regression"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 13.1", locator := "Section 13.1.1" }
  ]
  theorems := [
    Cslib.MachineLearning.IsRLM.integral_trueRisk_squaredLoss_le_add
  ]
  scope := "The squared loss (⟪w, x⟫ - y)² / 2 in a real inner product space, features of norm \
    at most 1 and labels in [-1, 1], the rule minimizing over the whole space, and comparators \
    of norm at most B, with the source's parameters m ≥ 150 B² / ε² and r = ε / (3 B²). \
    Integrability of the losses of the rule's output is a hypothesis."

register_result "srm-nonuniform-learnability" where
  title := "Countable unions of uniformly convergent classes are nonuniformly learnable by SRM"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorems 7.3 and 7.5",
      locator := "Theorem 7.3 in Section 7.1.1, p. 85; Theorem 7.5 in Section 7.2, pp. 87–88" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.isNonuniformLearnable_iUnion,
    Cslib.MachineLearning.PACLearning.isNonuniformLearnable_of_countable
  ]
  scope := "Domain and labels are arbitrary measurable spaces. Uniform convergence is an \
    explicit rate ε i m δ for m > 0 and δ > 0 with ε i m δ → 0; the learner for accuracy ε and \
    confidence δ is an SRM rule over pairs (i, h) and may depend on (ε, δ), following the \
    upstream IsPACLearnable conventions. Countable classes need measurable misclassification \
    sets. Theorem 7.5's explicit sample complexity is not stated, only learnability. The \
    converse characterization (Theorem 7.2) is not proved."

register_result "mdl-bound" where
  title := "Minimum description length bound for prefix-free descriptions"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 7.7",
      locator := "Section 7.3, p. 90" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.IsPrefixFreeDescription.mdl_bound,
    Cslib.MachineLearning.PACLearning.IsPrefixFreeDescription.measure_pi_exists_le_abs_sub_le
  ]
  scope := "Binary descriptions d : (α → β) → List Bool, prefix-free on the class, and \
    hypotheses with measurable misclassification sets, for m > 0 and δ > 0. With probability \
    at least 1 - δ every h satisfies L_D(h) ≤ L_S(h) + √((|d h| log 2 + log (2/δ)) / (2m)), \
    which is sharper than the source's |h| + ln (2/δ). Kraft's inequality is Mathlib's."

register_result "pac-bayes-mcallester" where
  title := "McAllester's PAC-Bayes bound and its Occam corollary"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 31.1 and Exercise 31.2",
      locator := "Section 31.1 and 31.3, pp. 416–418" },
    { paper := McAllester1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.PACBayes.measure_pi_exists_integral_risk_gt,
    Cslib.MachineLearning.PACBayes.measure_pi_exists_integral_risk_gt_log_div,
    Cslib.MachineLearning.PACBayes.measure_pi_exists_risk_gt
  ]
  scope := "Countable hypothesis index with measurable singletons, a prior fixed before the \
    sample, measurable losses in [0, 1], m ≥ 2 i.i.d. examples and δ > 0. With probability at \
    least 1 - δ every posterior Q with KL(Q ‖ P) < ∞, possibly depending on the sample, has \
    E_Q L_D ≤ E_Q L_S + √((KL(Q ‖ P) + log (m / δ)) / (2 (m - 1))); the proved form has \
    log (√m / δ). Point masses give the Occam bound with log (1 / P {i}). Measurable \
    hypothesis spaces, the kl form and Catoni's bound are not covered."

register_result "pac-bayes-kl" where
  title := "The PAC-Bayes-kl bound of Seeger and Maurer and its Occam form"
  topic := "statistical learning"
  sources := [
    { paper := Seeger2002, theorem := "Theorem 1 and Appendix A",
      locator := "Section 1.3, p. 239, and pp. 264–265" },
    { paper := Maurer2004, theorem := "Lemma 3", locator := "Section 2, p. 4" }
  ]
  theorems := [
    Cslib.MachineLearning.PACBayes.measure_pi_exists_binaryKL_integral_risk_gt,
    Cslib.MachineLearning.PACBayes.measure_pi_exists_binaryKL_risk_gt
  ]
  scope := "Countable hypothesis index with measurable singletons, a prior fixed before the \
    sample, measurable losses in [0, 1], m ≥ 1 i.i.d. examples and δ > 0. With probability at \
    least 1 - δ every posterior Q with KL(Q ‖ P) < ∞, possibly depending on the sample, has \
    kl(E_Q L_S ‖ E_Q L_D) ≤ (KL(Q ‖ P) + log ((m + 1) / δ)) / m, the binary relative entropy \
    in nats; Seeger states it for the 0-1 loss and Maurer's Lemma 3 extends it to [0, 1]. \
    Point masses give the Occam form with log (1 / P {i}). Maurer's log (2√m / δ) for m ≥ 8, \
    the square-root form through binary Pinsker, measurable hypothesis spaces and Catoni's \
    bound are not covered."

register_result "agnostic-vc-sharp-rate" where
  title := "Sharp agnostic sample complexity of classes of finite VC dimension"
  topic := "statistical learning"
  sources := [
    { paper := ShalevShwartzBenDavid2014, theorem := "Theorem 6.8",
      locator := "Section 6.4, pp. 72–73" }
  ]
  theorems := [
    Cslib.MachineLearning.PACLearning.measure_pi_not_isRepresentative_le_of_chainingSampleSize_le,
    Cslib.MachineLearning.PACLearning.isPACLearnerFor_univ_of_chainingSampleSize_le,
    Cslib.MachineLearning.PACLearning.sampleComplexity_univ_le_chainingSampleSize
  ]
  scope := "Upper bounds of items 1 and 2 only, on countable domains with measurable \
    singletons: uniform convergence and agnostic PAC learning by ERM from \
    (16384 d + 32 log (4/δ)) / ε² and (65536 d + 128 log (4/δ)) / ε² examples, where d bounds \
    the shattered sets. The constants are explicit and unoptimized. The lower bounds and the \
    realizable item 3 are not part of this entry, and uncountable domains need a measurability \
    hypothesis on the class."

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

register_result "gkst-pir-to-smooth-code" where
  title := "Smooth codes from private information retrieval schemes"
  topic := "cryptography"
  sources := [
    { paper := GoldreichKarloffSchulmanTrevisan2006, theorem := "Lemma 7.1",
      locator := "Section 7.1, pp. 19–20 of ECCC TR01-080" },
    { paper := KerenidisDeWolf2004, theorem := "Lemma 3",
      locator := "Appendix B, p. 16 of arXiv:quant-ph/0208062v2" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.card_smoothPos_le,
    Cslib.Crypto.Protocols.PIR.card_smoothPos_le_six_mul,
    Cslib.Crypto.Protocols.PIR.smoothCode_zero,
    Cslib.Crypto.Protocols.PIR.smoothCode_add,
    Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder,
    Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder_two,
    Cslib.Crypto.Protocols.PIR.decodeLaw_smoothDecoder_of_isPrivate,
    Cslib.Crypto.Protocols.PIR.isSmoothDecoder_smoothDecoder_of_isPrivate,
    Cslib.Crypto.Protocols.PIR.smoothDecoder_eq_of_predetermined,
    Cslib.Crypto.Protocols.PIR.card_mul_sq_le_card_answer_sub_one_of_statPrivate,
    Cslib.Crypto.Protocols.PIR.card_mul_sq_le_card_answer_sub_one_of_isPrivate
  ]
  scope := "One-round k-server PIR schemes P over finite server and query sets S, Q (with \
    arbitrary retained-state type R and answer type A). Replicating each (s, q) entry \
    max 1 ⌈p₀(s, q) · |S| · |Q|⌉₊ times produces smoothCode P i₀ of length at most \
    (|S| + 1) · |S| · |Q| (≤ 6 |Q| for |S| = 2) together with a non-adaptive decoder \
    smoothDecoder P i₀ that is (|S|, |S| + 1, ε - |S| · δ / 2)-smooth under pairwise δ-statistical \
    privacy (CloseTo) and recovery probability ≥ 1/2 + ε, specializing to (2, 3, ε - δ) for two \
    servers and preserving the exact output law under perfect privacy (δ = 0). Includes additive \
    linearity preservation (smoothCodeAddHom), predetermined answer-coordinate invariance \
    (smoothDecoder_eq_of_predetermined), and the noisy / statistically-private single-server \
    answer-size bound |ι| · (ε - δ / 2)² ≤ |A| - 1 via OneQuery.lean. Expected reads coincide with \
    query probability because distinct slots query distinct servers; neither machine runtime nor \
    fair-coin simulation of rational unifFin draws is certified."

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

register_result "swap-regret-approx-ce" where
  title := "Approximate Correlated Equilibrium via Swap Regret"
  topic := "game theory"
  sources := [
    { paper := BlumMansour2007, theorem := "Theorem 3 and Corollary 7",
      locator := "pp. 1311, 1313" },
    { paper := Roughgarden2013CS364A, theorem := unverified,
      locator := "Lecture 18, Section 1" }
  ]
  theorems := [
    Cslib.GameTheory.CostGame.timeAverage_productDist_isApproxCorrelatedEquilibrium,
    Cslib.GameTheory.CostGame.blumMansourDynamics_eq_blumMansourProb,
    Cslib.GameTheory.CostGame.blumMansour_isApproxCorrelatedEquilibrium
  ]
  scope := "Finite cost-minimization games under full-information expected-cost play over a \
    fixed known finite horizon T > 0. Shows that swap regret at most R i yields an (R i / T)-\
    approximate correlated equilibrium, explicitly constructs the coupled multi-player \
    Blum–Mansour trajectory blumMansourDynamics G T (with Hedge learning rate \
    √(m_i ln m_i / T)), and proves slack 2 √(m_i ln m_i / T) when costs lie in [-1, 1], \
    m_i ≥ 2, and T ≥ m_i ln m_i. Does not cover anytime dynamics, sampled play, last-iterate \
    convergence, or native running time."

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

register_result "two-player-nash-ppad" where
  title := "Two-player rational Nash equilibrium is in PPAD"
  topic := "game theory"
  sources := [
    { paper := Papadimitriou1994PPAD, theorem := unverified, locator := unverified },
    { paper := Shapley1974, theorem := unverified, locator := unverified },
    { paper := LemkeHowson1964, theorem := unverified, locator := unverified },
    { paper := vonStengel2007, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_PPAD,
    Cslib.GameTheory.BimatrixCode.BimatrixNash_mem_TFNP,
    Cslib.GameTheory.BimatrixCode.BimatrixNash_isTotalSearch,
    Cslib.GameTheory.BimatrixCode.BimatrixNash_searchReducible_EndOfLine,
    Cslib.GameTheory.BimatrixCode.BimatrixNash.isNash
  ]
  scope := "Two-player games presented as pairs of rational payoff lists under encBimatrix. \
    For well-formed nonempty m × n games, BimatrixNash asks for a canonical rational mixed Nash \
    equilibrium encoded by encWitness within explicit bit-length bound 120·L³ + 400·L + 100 \
    (malformed inputs admit only []). Proved in PPAD by lexicographic perturbation, \
    Shapley-oriented Lemke–Howson pivoting, and Cramer rounding; does not prove PPAD-hardness \
    or an efficient Lemke–Howson solver."

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

register_result "facility-location-moulin-interval" where
  title := "Moulin characterization of strategyproof location rules on closed real intervals"
  topic := "game theory"
  sources := [
    { paper := Moulin1980, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.MoulinScheme.eval_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_moulinScheme,
    Cslib.GameTheory.FacilityLocation.moulinScheme_of_isometry
  ]
  scope := "Finite nonempty agent set ι and compact interval Set.Icc a b (with a < b) or \
    isometric domain. Every MoulinScheme yields a deterministic onto strongly group strategyproof \
    mechanism, and every deterministic onto strategyproof mechanism coincides with \
    MoulinScheme.eval. Moulin 1980 primary paper uninspected here."

register_result "facility-location-schummer-vohra-trees" where
  title := "Schummer–Vohra characterization of strategyproof location rules on trees"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2002, theorem := "Theorem 1",
      locator := "Section 3, p. 15 of the January 2001 author preprint" }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.TreeEMVS.eval_isGroupStrategyProof,
    Cslib.GameTheory.FacilityLocation.isStrategyProof_and_surjective_iff_exists_treeEMVS,
    Cslib.GameTheory.FacilityLocation.isGroupStrategyProof_of_isStrategyProof_of_surjective_tree
  ]
  scope := "Any finite nonempty agent set ι and finite connected positive-weighted tree metric \
    graph (W.graph.IsTree, MetricGraph W) with Borel measurable space. Deterministic onto \
    strategyproof rules coincide with extended median voter schemes TreeEMVS and are strongly \
    group strategyproof; majority-of-3 on star3 in CslibFrontierTests.SchummerVohra shows \
    non-dictatorial rules exist. TreeEMVS represents the source's extended median voter schemes \
    by branch-winning coalitions instead of consistent path schemes. Strong group \
    strategyproofness is proved here and is not part of the source's Theorem 1."

register_result "facility-location-schummer-vohra-cycles" where
  title := "Schummer–Vohra cycle dictatorship on graphs with cycles"
  topic := "game theory"
  sources := [
    { paper := SchummerVohra2002, theorem := "Theorem 2",
      locator := "Section 4, p. 21 of the January 2001 author preprint" }
  ]
  theorems := [
    Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_isShortestCycle,
    Cslib.GameTheory.FacilityLocation.exists_cycleDictator_of_not_isAcyclic,
    Cslib.GameTheory.FacilityLocation.exists_dictatorship_of_cycleGraph
  ]
  scope := "Any finite nonempty agent set ι and finite connected positive-weighted MetricGraph W \
    with Borel measurable space. Every deterministic onto strategyproof rule acts as a dictator \
    on profiles supported on any shortest cycle (assuming ¬ W.graph.IsAcyclic) and is globally \
    dictatorial on graphs isomorphic to cycleGraph (n + 3). Triangle + Tail in \
    CslibFrontierTests.SchummerVohra shows cycle dictatorship need not extend globally. Bounded \
    milestone of Issue #4327 (arbitrary cycles and full cyclic-network characterization remain \
    open). The source's Theorem 2 covers every cycle; only shortest cycles are formalized."

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
    QFNumeric.onFullTuple); the logspace encoding lift at encStructure is proved in \
    Classes.LogSpace.FirstOrder.Ordered.Projection, and NP-completeness endpoints are in \
    immerman-sat-np-complete and ordered-np-complete-problems."

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
    tautologies; each output bit reads at most one input literal. Unconditional NP-completeness \
    is in ordered-np-complete-problems."

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
    QFProjectionReduces to Clique and VertexCover; unconditional NP-completeness is in \
    ordered-np-complete-problems."

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
    Ordered.SimpleThreeColorable and Ordered.ThreeColorable; unconditional NP-completeness is \
    in ordered-np-complete-problems."

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
    encStructure. Full ≤_qfp, ≤_fop, ≤_fo and encStructure NP-completeness is in \
    immerman-sat-np-complete and ordered-np-complete-problems."

register_result "ordered-eso-qfp-grounding" where
  title := "Ordered relational ESO sentences ground to SAT via BIT-free QF projections"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_of_orderSentence,
    Cslib.Logic.ESO.Sentence.isQFProjection_groundQFInterpretation,
    Cslib.Logic.ESO.Sentence.satisfiable_tupleStructure_groundQFInterpretation_iff,
    Cslib.Logic.ESO.Sentence.mem_SAT_groundQFInterpretation
  ]
  scope := "For any relational language L and existential second-order sentence Φ over \
    L.sum ESO.orderLanguage, groundQFInterpretation compiles Φ uniformly into a positive-dimension \
    FullTupleInterpretation L FO.cnf certified by IsQFProjection (BIT-free, over qfNumericLanguage \
    with ≤, non-wrapping succ, 0, and max). Ground tags are encoded via binary {0, max} prefixes \
    (MatchBinaryTag), inactive tuples carry self-tautologies, and strict order guards compile to \
    numeric order comparisons on Fin M.size (2 ≤ M.size), yielding QFProjectionReduces K \
    Ordered.SAT without machine or complexity imports."

register_result "immerman-sat-np-complete" where
  title := "Immerman: ordered SAT is NP-complete under BIT-free quantifier-free projections"
  topic := "descriptive complexity"
  sources := [
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified },
    { paper := Fagin1974, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.projectionReduces_SAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.reduces_SAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SAT_of_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.esoDefinable_iff_qfProjectionReduces_SAT,
    Cslib.Logic.FO.Ordered.sat_npComplete,
    Cslib.Logic.FO.Ordered.cnf_polyTimeReducible_orderedSAT,
    Cslib.Logic.FO.Ordered.orderedSAT_polyTimeReducible_cnf
  ]
  scope := "Queries on canonically ordered finite relational structures Fin n (2 ≤ n) over a \
    finite relational vocabulary v, with source-only encodings at encStructure. Combining the \
    ordered Fagin tableau sentence on a polynomial power structure with BIT-free quantifier-free \
    projection grounding (ordered-eso-qfp-grounding) characterizes native NP membership at \
    encStructure and ESODefinable uniformly by QFProjectionReduces (≤_qfp), ProjectionReduces \
    (≤_fop), or Ordered.Reduces (≤_fo) to Ordered.SAT. At the machine level, cnfToOrdered gives an \
    explicit polynomial-time reduction from Complexity.SAT (encCNF) to Ordered.SAT (encStructure), \
    establishing NPComplete encStructure and bidirectional PolyTimeReducible equivalence."

register_result "ordered-np-complete-problems" where
  title := "Ordered ThreeSAT, 3-coloring, IndependentSet, Clique, and VertexCover are NP-complete"
  topic := "descriptive complexity"
  sources := [
    { paper := Karp1972, theorem := unverified, locator := unverified },
    { paper := GareyJohnson1979, theorem := unverified, locator := unverified },
    { paper := Immerman1999, theorem := unverified, locator := unverified },
    { paper := ImmermanLandau1995, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.Ordered.qfProjectionReduces_ThreeSAT_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_SimpleThreeColorable_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_ThreeColorable_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_IndependentSet_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_Clique_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.qfProjectionReduces_VertexCover_iff_encodedLanguage_mem_NP,
    Cslib.Logic.FO.Ordered.threeSAT_npComplete,
    Cslib.Logic.FO.Ordered.simpleThreeColorable_npComplete,
    Cslib.Logic.FO.Ordered.threeColorable_npComplete,
    Cslib.Logic.FO.Ordered.independentSet_npComplete,
    Cslib.Logic.FO.Ordered.clique_npComplete,
    Cslib.Logic.FO.Ordered.vertexCover_npComplete,
    Cslib.Logic.FO.Ordered.threeSAT_polyTimeReducible_orderedThreeSAT,
    Cslib.Logic.FO.Ordered.orderedThreeSAT_polyTimeReducible_threeSAT,
    Cslib.Logic.FO.Ordered.threeColoring_polyTimeReducible_orderedSimpleThreeColorable,
    Cslib.Logic.FO.Ordered.orderedSimpleThreeColorable_polyTimeReducible_threeColoring,
    Cslib.Logic.FO.Ordered.threeColoring_polyTimeReducible_orderedThreeColorable,
    Cslib.Logic.FO.Ordered.orderedThreeColorable_polyTimeReducible_threeColoring,
    Cslib.Logic.FO.Ordered.independentSet_polyTimeReducible_orderedIndependentSet,
    Cslib.Logic.FO.Ordered.orderedIndependentSet_polyTimeReducible_independentSet,
    Cslib.Logic.FO.Ordered.clique_polyTimeReducible_orderedClique,
    Cslib.Logic.FO.Ordered.orderedClique_polyTimeReducible_clique,
    Cslib.Logic.FO.Ordered.vertexCover_polyTimeReducible_orderedVertexCover,
    Cslib.Logic.FO.Ordered.orderedVertexCover_polyTimeReducible_vertexCover
  ]
  scope := "Composing ≤_qfp-hardness of Ordered.SAT with the BIT-free quantifier-free gadget \
    projections and downward NP closure under Ordered.Reduces characterizes native NP membership \
    at encStructure by QFProjectionReduces, ProjectionReduces, and Ordered.Reduces to each of \
    Ordered.ThreeSAT, Ordered.SimpleThreeColorable, Ordered.ThreeColorable, \
    Ordered.IndependentSet, Ordered.Clique, and Ordered.VertexCover. Lifting to encStructure and \
    combining with Cook–Levin / Karp hardness proves NPComplete encStructure for all six \
    queries and explicit bidirectional PolyTimeReducible bridges to Complexity.ThreeSAT, \
    Complexity.ThreeColoring, Complexity.IndependentSet, Complexity.Clique, and \
    Complexity.VertexCover."

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

register_result "kolaitis-vardi-zero-one-law" where
  title := "Kolaitis–Vardi: the 0-1 law for finite-variable infinitary logic L^k_∞ω"
  topic := "descriptive complexity"
  sources := [
    { paper := KolaitisVardi1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.infinitary_zero_one_law_of_finset,
    Cslib.Logic.FO.graph.isPebbleBackAndForth_of_satisfies_extensionAxiom_lt,
    Cslib.Logic.FO.graph.binomialRandom_infinitary_zero_one_law,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_one_iff_radoGraph,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_zero_iff_radoGraph,
    Cslib.Logic.FO.graph.randomGraph_infinitary_zero_one_law,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_infinitary_one_iff_tendsto_randomGraphProb,
    Cslib.Logic.FO.graph.not_exists_infinitaryFormula_of_not_tendsto_binomialRandom,
    Cslib.Logic.FO.graph.tendsto_binomialRandom_real_connected,
    Cslib.Logic.FO.Relational.isPebbleBackAndForth_of_hasExtension_lt,
    Cslib.Logic.FO.Relational.uniformStructure_infinitary_zero_one_law,
    Cslib.Logic.FO.Relational.bernoulliStructure_infinitary_zero_one_law,
    Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_one_iff_model,
    Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_zero_iff_model,
    Cslib.Logic.FO.Relational.tendsto_infinitaryProb_bernoulliStructure_one_iff_uniformStructure,
    Cslib.Logic.FO.Relational.not_exists_infinitaryFormula_even_card
  ]
  scope := "Closed formulas of the k-variable infinitary logic L^k_∞ω (at any disjunction index \
    universe w and any quantifier depth) over Mathlib's language of graphs under G(Fin n, p) \
    (0 < p < 1) and G(n, 1/2), and over finite relational vocabularies with no nullary symbols \
    under uniformStructure n and bernoulliStructure p n (0 < p R < 1). Because moving one of k \
    pebbles leaves at most k - 1 fixed pebbles, the finitely many extension axioms of arity \
    strictly below k make PartialIsoOn a k-pebble back-and-forth invariant. In G(Fin n, p), the \
    limit is 1 iff the sentence holds in SimpleGraph.radoGraph (independent of p), yielding \
    almost-sure connectivity as a corollary of L^3_∞ω definability. KolaitisVardi1992 is cited \
    for the uniform L^k_∞ω 0-1 law; the constant-probability G(Fin n, p) and per-symbol \
    bernoulliStructure extensions combine their pebble-game argument with the repository's \
    constant-probability extension bounds. Fixed-point 0-1 laws (not needed separately once \
    FO(LFP) embeds into L^ω_∞ω, which is not yet formalized), probabilities depending on n, and \
    unlabelled structures are not covered."

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

register_result "infinitary-fo-pebble-games" where
  title := "Pebble-game characterizations and expressiveness of L^k_∞ω and C^k_∞ω"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Theorem 11.5 and Proposition 11.8",
      locator := "Section 11.2, pp. 216–218" },
    { paper := KolaitisVardi1992, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.FO.pebbleWins_iff_forall_infinitaryFormula_rankLE,
    Cslib.Logic.FO.pebbleWinsForever_iff_forall_infinitaryFormula,
    Cslib.Logic.FO.exists_isPebbleBackAndForth_iff_forall_infinitaryFormula,
    Cslib.Logic.FO.bijPebbleWins_iff_forall_infinitaryCountingFormula_rankLE,
    Cslib.Logic.FO.bijPebbleWinsForever_iff_forall_infinitaryCountingFormula,
    Cslib.Logic.FO.forall_realize_infinitaryFormula_iff_forall_realize,
    Cslib.Logic.FO.forall_realize_infinitaryCountingFormula_iff_forall_realize,
    Cslib.Logic.FO.FiniteVariable.realize_reachableInfinitary,
    Cslib.Logic.FO.FiniteVariable.realize_connectedInfinitary_iff_connected,
    Cslib.Logic.FO.FiniteVariable.realize_evenCardInfinitary,
    Cslib.Logic.FO.not_exists_infinitaryFormula_even_card
  ]
  scope := "k-variable infinitary logics L^k_∞ω (InfinitaryFormula) and C^k_∞ω \
    (InfinitaryCountingFormula) with arbitrary indexed disjunctions in Type w. For arbitrary \
    languages and arbitrary (possibly infinite) structures M : Type w₁, N : Type w₂, Duplicator \
    wins the n-round or infinite k-pebble game iff the positions satisfy the same L^k_∞ω \
    formulas of quantifier rank at most n (respectively all L^k_∞ω formulas) at index universe \
    max w₁ w₂; for finite structures, the bijective k-pebble game similarly characterizes \
    C^k_∞ω, and L^k_∞ω / C^k_∞ω equivalence over finite relational vocabularies collapses to \
    finitary FO^k / C^k equivalence. Expressiveness separations: graph reachability on all \
    simple graphs and connectivity on all nonempty simple graphs (Preconnected unconditionally) \
    are definable in L^3_∞ω, while EVEN is definable in C^1_∞ω on finite structures and not \
    definable in L^k_∞ω for any k."

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
    Fin N, rank q forces N ≤ 2·3^(q+1). Any Gaifman radius on finite simple graphs for \
    rank n is at least 2^(n-1) (exact-locality-ranks gives the exact bound 2^n - 1 over \
    directed graphs with self-loops). Constants are not claimed sharp."

register_result "exact-locality-ranks" where
  title := "Exact Hanf (2^(n-1) - 1) and Gaifman (2^n - 1) locality ranks of first-order logic"
  topic := "descriptive complexity"
  sources := [
    { paper := Libkin2004, theorem := "Exercises 4.10 and 4.11",
      locator := "Chapter 4 (pp. 63–64)" }
  ]
  theorems := [
    Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_equiv_two_pow,
    Cslib.Logic.FO.Locality.NbhdIso.duplicatorWins_of_two_pow,
    Cslib.Logic.FO.Locality.NbhdIso.realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.NbhdIso.formula_realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.HanfEquiv.duplicatorWins_of_two_pow,
    Cslib.Logic.FO.Locality.HanfEquiv.realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.HanfEquiv.formula_realize_iff_of_two_pow,
    Cslib.Logic.FO.Locality.realize_sentence_iff_of_nbhdIso_two_pow,
    Cslib.Logic.FO.Locality.exists_nbhdIso_realize_loopReach,
    Cslib.Logic.FO.Locality.two_pow_sub_one_le_of_gaifman_radius,
    Cslib.Logic.FO.Locality.exists_hanfEquiv_sentence_not_realize_iff,
    Cslib.Logic.FO.Locality.exists_hanfEquiv_formula_not_realize_iff,
    Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_sentence_radius,
    Cslib.Logic.FO.Locality.two_pow_pred_sub_one_le_of_hanf_radius
  ]
  scope := "Finite structures. Gaifman locality holds at radius 2^n - 1 and Hanf locality (for \
    nonempty M) holds at radius 2^(n-1) - 1, giving Duplicator the n-round game in any \
    language and formula/sentence agreement in relational languages. Matching lower bounds \
    over Mathlib's language of graphs (interpreted via relStructure as directed graphs with \
    self-loops) show that both radii are pointwise minimal across all quantifier ranks."

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

register_result "native-sublinear-time-collapse" where
  title := "Sublinear native algorithms have constant runtime"
  topic := "time complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 4.3",
      locator := "January 2007 draft r2.pdf, PDF p. 35; printed p. 151" }
  ]
  theorems := [
    Turing.MultiTapeTM.exists_uniform_time_of_fast_length,
    Turing.MultiTapeTM.exists_uniform_time_of_isLittleO,
    Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_const_time_of_isLittleO
  ]
  scope := "A fixed native sequential-input machine with a uniform sublinear clock on every \
    input word has a global constant clock. One fast width suffices under a uniform total \
    clock on all words. Raw-bit computability preserves outputs and independent workspace. \
    No separate input length, random access or arbitrary encoding extension is asserted."

register_result "sublinear-dtime-equals-constant" where
  title := "Sublinear deterministic time classes equal constant time"
  topic := "time complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 4.3 (decision-class consequence)",
      locator := "January 2007 draft r2.pdf, PDF p. 35; printed p. 151" }
  ]
  theorems := [Cslib.Complexity.DTIME_eq_const_of_isLittleO]
  scope := "DTIME encBits p equals DTIME encBits 1 for p=o(n), including affine clock constants. \
    The input is every raw bit word; prefixes of arbitrary encoded instances need not be \
    valid, so no such encoding-general class identity is claimed."

register_result "goldreich-exact-step-counter" where
  title := "Exact native step counter from binary input"
  topic := "time complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercise 4.5",
      locator := "January 2007 r2.pdf; PDF page 36 / printed page 152" },
    { paper := Goldreich2006DraftR1, theorem := "Numbers convention",
      locator := "December 2006 r1.pdf; PDF page 45 / printed page 20" }
  ]
  theorems := [Turing.MultiTapeTM.exists_stepCounter]
  scope := "One fixed finite deterministic native multitape machine on encNat n, \
    least-significant-first binary, visits one designated signal state exactly n times. \
    It starts outside the signal state and leaves each visit on the next transition. \
    Total runtime, including binary-to-unary preparation, is bounded by c*(n+1) for a \
    uniform constant c; zero input issues no signals. No logarithmic workspace or \
    per-prefix signal-latency bound is claimed."

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
    lengths, when n ≤ s(n) and 0 < δ(n). Formulas only: for the [q, ℓ, a]-Circuit classes \
    (LocalCircuitClass) the Gap-MCSP [OPS19] bullet is registered as gap-mcsp-oracle-circuits \
    and the MCSP [MMW19] bullet as mmw-merge-tree-locality; the other bullets of Proposition 63 \
    and the locality barrier (Theorem 59) are not formalized."

register_result "mmw-merge-tree-locality" where
  title := "Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam: the McKay–Murray–Williams merge tree \
    puts MCSP[s] in [O(N/s), O(s⁴), O(n/log s)]-Circuit[O(N/s)] for n ≤ s ≤ N"
  topic := "meta-complexity"
  sources := [
    { paper := ChenHiraharaOliveiraPichRajgopalSanthanam2020,
      theorem := "Proposition 63, [MMW19] MCSP bullet",
      locator := "ECCC TR19-168, Appendix A.2, p. 52; Section 2.5, Definition 11, p. 13" }
  ]
  theorems := [
    Cslib.MCSP.localCircuitClass_MCSP
  ]
  scope := "Unconditional. Whenever n ≤ s(n) and 2 ≤ s(n) for every n, MCSP[s] (no gap) is in \
    LocalCircuitClass (Definition 11) at input length m, with n = log₂ m: at most 128m/s(n) + 1 \
    oracle gates, each of fan-in at most 12·s(n)^4, at most n/⌊log₂ s(n)⌋ + 1 oracle gates on any \
    path, and at most 129m/s(n) + 3 gates (all gates counted). The circuits are the explicit \
    merge tree MergeTree.mmwCircuit, with ⌊log₂ s⌋ bits per level, under one fixed oracle, \
    MergeTree.oracle, for all lengths; no bound on the oracle's complexity is claimed. The bounds \
    read as the source's O(N/s) and O(n/log s) when also s(n) ≤ 2^n. Deviations: the source \
    assumes only a constructive s(n) ≤ 2^n/poly(n); n ≤ s(n) and 2 ≤ s(n) exclude s(n) < n, the \
    exact bounds need no upper bound on s, and constructivity is not formalized (the class is \
    nonuniform)."

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
    (Oliveira–Pich–Santhanam Lemma 4.1) is registered as efficient-anti-checker."

register_result "efficient-anti-checker" where
  title := "Oliveira–Pich–Santhanam: under NP ⊆ P/poly, anti-checkers are generated by circuits of \
    size 2^(n + O(βn))"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraPichSanthanam2019, theorem := "Lemma 4.1 (ECCC TR18-158 Lemma 17)",
      locator := "ECCC TR18-158, Section 4.1, p. 16" }
  ]
  theorems := [
    Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_of_NP_subset_PPoly,
    Cslib.MCSP.AntiChecker.exists_antiChecker_circuit_le_of_NP_subset_PPoly
  ]
  scope := "Conditional on NP ⊆ P/poly (NP encBits ⊆ PPolyOn encBits). There is k such that for \
    every β > 0 and all large n, a De Morgan circuit with at most 2^(n + kβn) gates (all gates \
    counted) maps the truth table of f : {0,1}^n → {0,1} to ⌊2^(10βn)⌋₊ blocks of n bits, and if \
    ⌊2^(βn)⌋₊ < complexity f, every circuit with at most ⌊2^(βn)/(10n)⌋₊ gates errs on some \
    block. Every β > 0, where the source says sufficiently small β. The explicit form bounds the \
    size by 2^n·c·(n + s + 1)^c for every n > 0, s and enough blocks, assuming f needs more gates \
    than n circuits with s gates and their strict majority. Proof route: a deterministic greedy \
    against a hash-threshold oracle with tensor-power amplification, compiled to an oracle \
    circuit whose oracle gates are replaced by P/poly circuits; not the source's approximate \
    counting and listing."

register_result "gap-mcsp-oracle-circuits" where
  title := "Chen–Hirahara–Oliveira–Pich–Rajgopal–Santhanam: Gap-MCSP has oracle circuits with \
    N·poly(s) gates, fan-in poly(s) and adaptivity poly(s)"
  topic := "meta-complexity"
  sources := [
    { paper := ChenHiraharaOliveiraPichRajgopalSanthanam2020,
      theorem := "Proposition 63, [OPS19] Gap-MCSP bullet",
      locator := "ECCC TR19-168, Appendix A.2, p. 52; Section 2.5, Definition 11, p. 13" }
  ]
  theorems := [
    Cslib.MCSP.exists_oracleCircuit_gapMCSP,
    Cslib.MCSP.localCircuitClass_gapMCSP
  ]
  scope := "Unconditional. Whenever n·s₁ + 2 + 2n(n + 2) ≤ s₂ at length n, one oracle circuit on \
    N = 2^n inputs with the fixed oracle antiCheckerOracle accepts the yes-instances of \
    Gap-MCSP[s₁, s₂] and rejects its no-instances. It has at most 5000·N·s₂^5 gates, at most \
    610·N·s₂^4 + 1 oracle gates, fan-in at most 5000·s₂^5 and at most 610·s₂^4 + 1 oracle gates \
    on any path. localCircuitClass_gapMCSP states this in the class LocalCircuitClass \
    (Definition 11) at input length m with n = log₂ m, the gap condition holding at every n; its \
    size bound has a + 1 for input length 0, which has no instances. The gap condition replaces \
    the source's constructive s(n) ≤ 2^n/poly(n)."

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

register_result "learning-hardness-from-generators" where
  title := "Subexponentially secure generators rule out learners with small circuits for \
    polynomial-size circuits"
  topic := "meta-complexity"
  sources := [
    { paper := Valiant1984, theorem := unverified, locator := unverified },
    { paper := GGM1986, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.eventually_le_of_isSubexponentiallySecure,
    Cslib.MachineLearning.UniformLearning.exists_eventually_not_learns_of_isSubexponentiallySecure
  ]
  scope := "Conditional on a subexponentially secure family of length-doubling generators of \
    polynomial circuit complexity, as in natural-proofs. For a polynomial s, every c and large n, \
    a learner whose tests are circuits of at most 2^(cn) gates on truth tables (HasCircuitTests) \
    for the functions of circuit size s n has (1 - delta)(1 - eps) <= 1/2 + q/2^(n+1) + 2^(-cn). \
    Learners with q <= 2^(n-1) adaptive membership queries and De Morgan circuits of S <= 2^(cn) \
    gates in all on each seed (HasAdaptiveCircuit, covering non-adaptive HasCircuit learners) \
    have such tests, so none reaches (1 - delta)(1 - eps) > 3/4. Running time is not modelled. \
    The distinguisher fixes the learner's seed and comparison point by averaging; it is a \
    nonuniform circuit test."

register_result "learning-natural-property" where
  title := "Oliveira–Santhanam: learners for SIZE s yield P/poly-natural properties useful against \
    SIZE s"
  topic := "meta-complexity"
  sources := [
    { paper := OliveiraSanthanam2017, theorem := "Theorem 8, (1) ⇒ (5)", locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.isNatural_PPoly_and_isUseful_SIZE,
    Cslib.MachineLearning.UniformLearning.isNatural_PPoly_lowAgreement,
    Cslib.MachineLearning.UniformLearning.isUseful_lowAgreement
  ]
  scope := "Membership-query learners (adaptive allowed) with uniform seeds from a set of size \
    2^(c(n+1)), circuit tests of at most 2^(c(n+1)) gates on truth tables (HasCircuitTests), and \
    accuracy \
    (1 - delta)(1 - eps) at least 2^(-cn) above 1/2 + q/2^(n+1). The property is the set of \
    functions on which the seed-averaged agreement is below (1 - delta)(1 - eps); it is decided \
    by an exact threshold over all seeds and points, so constructivity is P/poly by circuit size, \
    not the source's BPP-natural form, and arbitrary seed distributions are not covered. The \
    random-function bound is the fair-coin argument, not the source's small-hypothesis lemma. \
    The accuracy gap restricts it to strong or confidence-amplified learners; the source's \
    non-trivial (1/2 - 1/n^k, 1/n) learners of item (1) are not covered as stated."

register_result "nw-reconstruction-learner" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: the Nisan–Wigderson reconstruction as a \
    membership-query weak learner, one run"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := "Theorem 2.11",
      locator := "Section 2.4" },
    { paper := NisanWigderson1994, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.nwLearner_learns_of_dens,
    Cslib.MachineLearning.UniformLearning.nwLearner_learns,
    Cslib.MachineLearning.UniformLearning.div_two_mul_le_dens_uniformError_nwLearner_le,
    Cslib.MachineLearning.UniformLearning.nwLearner_queriesAtMost,
    Cslib.MachineLearning.UniformLearning.complexity_eval_nwLearner_le
  ]
  scope := "One run of the reconstruction, in a library form. For an (l, n, a)-design with m > 0 \
    blocks and a deterministic test accepting at least a delta fraction of m-bit strings but \
    no output of the generator of any f in the class, the learner built from the negated test \
    learns the class under the uniform distribution with membership queries, error \
    1/2 - delta/(2m) and success probability delta/(2m) over a uniform trial. This is the \
    delta-dense natural-property case; nwLearner_learns covers a distinguisher of any \
    advantage eps, where the source takes advantage above 1/5, and advantage eps/(2m) \
    replaces 1/L (the source's L is the output length m). It makes at most \
    m 2^a queries, and every hypothesis has De Morgan circuit size at most that of the test \
    plus m (2^a (2a + 3) + 1) + 1. The running time of the learner is not certified. Repeating \
    runs and selecting the best hypothesis, which the full Theorem 2.11 needs, is the entry \
    nw-reconstruction-best-of."

register_result "nw-reconstruction-best-of" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning from a distinguisher for the \
    Nisan–Wigderson generator"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016, theorem := "Theorem 2.11",
      locator := "p. 10:9" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns,
    Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_learns_of_dens,
    Cslib.MachineLearning.UniformLearning.bestOf_nwLearner_queriesAtMost,
    Cslib.MachineLearning.UniformLearning.complexity_eval_bestOf_nwLearner_le
  ]
  scope := "Theorem 2.11 in a library form. For an (l, n, a)-design with m > 0 blocks and a \
    deterministic test that accepts outputs of the generator of each f in the class with \
    probability at least eps > 0 more than uniform m-bit strings, best-of-k selection on t \
    uniform sample points over the reconstruction learner built from the test learns the class \
    under the uniform distribution with membership queries, error 1/2 - eps/(4m) and confidence \
    1 - eta, when eps/(2m) <= 1, log(2/eta) <= (eps/(2m)) k and 8 log(4k/eta) <= t (eps/(2m))^2. \
    Any advantage eps > 0 replaces the source's advantage above 1/5, error 1/2 - eps/(4m) \
    replaces 1/2 - 1/L (the source's L is the output length m), and explicit k and t replace \
    poly(L). bestOf_nwLearner_learns_of_dens is the natural-property special case: a test \
    accepting at least a delta > 0 fraction of m-bit strings but no generator output, used \
    through its negation, which has advantage at least delta. It makes at most k m 2^a + t \
    queries, and every hypothesis has the De Morgan circuit bound of one run. The running time \
    of the learner is not certified."

register_result "cikk-amp-reconstruction" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning f from a learner for its \
    amplification (f^k)^GL"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 4.3, with Claim 4.4 in its proof",
      locator := "pp. 10:15–10:16; Claim 4.4 stated on p. 10:15" },
    { paper := ImpagliazzoJaiswalKabanetsWigderson2010, theorem := unverified,
      locator := unverified }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.learns_ampLearner,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_ampLearner,
    Cslib.MachineLearning.UniformLearning.eval_ampLearner
  ]
  scope := "The reconstruction for p = 2 in a library form, with the GF(2) amplification \
    Amp(f) = (f^k)^GL. If a membership-query learner learns {Amp(f) | f in C} under the uniform \
    distribution with error 1/2 - gamma and success probability p, then the black-box reduction \
    that answers each of its queries with k queries to f, decodes its hypothesis with \
    Goldreich-Levin and then with the direct-product decoder learns C with error eps and \
    success probability p delta0^2/8, where delta0 = gamma/2^(K+3), when \
    k <= 2 (gamma/2)^2 (2^K - 1), 2s <= k, s >= (64/eps) log(512/(eps delta0^2)) and \
    m >= (16/delta0) log(8/eps). Claim 4.4, the Goldreich-Levin step, is \
    dens_filter_glAmpCandidate_agree in HardnessAmplification/GLAmpDecode.lean, used in the \
    proof. Deviations: (a) the Goldreich-Levin list has 2^K = O(k/gamma^2) \
    entries, where the source's Goldreich-Rubinfeld-Sudan decoder has O(1/gamma^2); (b) each \
    seed gives a deterministic decoder, and a delta0 fraction of the seeds has agreement at \
    least delta0, by reverse Markov; (c) the success probability and the direct-product \
    constants are ours, and p delta0^2/8 >= p gamma^6/(10368 k^2) for the least admissible K; \
    (d) the four parameter conditions are hypotheses, where the source fixes \
    k = ceil(3c (1/eps) ln(1/gamma)) + 1. The size s of the direct-product set is an explicit \
    argument, and the seed distribution needs k > 0 and s <= k. The circuit size of the \
    hypotheses is not bounded here (see cikk-learner-hypothesis-size), and the running time of \
    the learner is not certified."

register_result "cikk-learning-from-dense-test" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning f from a dense test that rejects \
    the generator of its amplification, p = 2"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 5.1, with the composition from the proof of Theorem 3.2",
      locator := "p. 10:19; proof of Theorem 3.2 on p. 10:11" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.learns_cikkLearner,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_two_pow
  ]
  scope := "The learner of Theorem 5.1 for p = 2 in a per-function black-box form. Let a test on \
    2^l-bit strings accept at least 2^(2^l) 2^(l+1-g) strings and no output of the \
    Nisan-Wigderson generator of Amp(f) = (f^k)^GL, k = cikkK e g, on the binary polynomial \
    design, for every f in C. Then cikkLearner, best-of selection over the amplification \
    reconstruction (cikk-amp-reconstruction) of the Nisan-Wigderson learner of the negated test \
    (nw-reconstruction-learner), learns C under the uniform distribution with membership \
    queries, error 2^-e and confidence 1 - 2^-h, with at most \
    (h+1) 2^(2l + 10g + 6e + 59) queries. Labelled deviations: (1) a single outer best-of \
    selection replaces the source's per-stage confidence boosts (proof of Theorem 3.2), with \
    the same result up to constants; (2) any density at least 2^(l+1-g) replaces largeness \
    1/5, and the Nisan-Wigderson advantage is delta/(2L) instead of 1/L; (3) error, \
    confidence and k are powers of two with this library's constants, where the source has \
    k = ceil(3c (1/eps) ln(1/gamma)) + 1, and the deviations of cikk-amp-reconstruction carry \
    over; (4) the number of queries is certified, the hypothesis size is bounded in \
    cikk-learner-hypothesis-size, and the running time is not certified; (5) p = 2 only; \
    (6) the test is an arbitrary Boolean function, not a natural property, so the \
    property-to-learner form of Theorem 5.1 is not included; Corollary 5.4 for p = 2 is \
    cikk-learning-ac0-2."

register_result "cikk-learner-hypothesis-size" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: the hypotheses of the learner from a \
    dense test are small circuits relative to the test, p = 2"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 5.1, the size of the hypothesis circuit", locator := "p. 10:19" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le,
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_le_two_pow,
    Cslib.MachineLearning.UniformLearning.complexity_eval_ampLearner_le
  ]
  scope := "On every target and seed, the hypothesis of the learner of \
    cikk-learning-from-dense-test has De Morgan circuit size at most \
    T (F+1) ((2^K - 1)(c + N + 3) + 8 + 2 (2^K - 1)(2^K + 1)) + 3T + 1, where c is the circuit \
    size of the test, N = 2^l (2^(l-1) (2(l-1) + 3) + 1), and T, F, K are the numbers of \
    trials, fixed positions and masks; in closed form, at most 2^(11g + 9e + 3l + 80) (c + 1). \
    The bound composes the Nisan-Wigderson hypothesis bound (nw-reconstruction-learner), the \
    Goldreich-Levin candidate bound and the direct-product decoder bound \
    (complexity_dpDecode_le); complexity_eval_ampLearner_le is the step for one run of the \
    amplification reconstruction (cikk-amp-reconstruction). The bound is affine in c with \
    T (F+1)(2^K - 1) copies of the test. Labelled deviations: (1) with unit-cost test gates \
    it is the size that the source's oracle circuit would have, but that oracle circuit is not \
    built; (2) the constants, including the closed form's, are this library's and not tight; \
    (3) size only: depth and the running time of the learner are not certified."

register_result "cikk-learning-ac0-2" where
  title := "Carmosino–Impagliazzo–Kabanets–Kolokolova: learning AC⁰[2] with the rank property, \
    with quasi-polynomially many membership queries and quasi-polynomial-size hypotheses"
  topic := "meta-complexity"
  sources := [
    { paper := CarmosinoImpagliazzoKabanetsKolokolova2016,
      theorem := "Theorem 5.1 and Corollary 5.4, p = 2",
      locator := "p. 10:19 (Theorem 5.1 and its proof); p. 10:20 (Corollary 5.4)" }
  ]
  theorems := [
    Cslib.MachineLearning.UniformLearning.learns_cikkLearner_rankTest,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_rankTest,
    Cslib.MachineLearning.UniformLearning.queriesAtMost_cikkLearner_rankTest_le,
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_rankTest_le_two_pow,
    Cslib.MachineLearning.UniformLearning.complexity_eval_cikkLearner_rankTest_le
  ]
  scope := "Corollary 5.4 for p = 2 with queries and hypothesis size counted, for a fixed depth d \
    and size s. With g = cikkAC0Gap d e n s and l = cikkAC0Len d e n s g, the CIKK learner \
    (cikk-learning-from-dense-test) whose test accepts the truth tables of the rank property \
    (rank-property-natural-ac0-2) at input length l learns every function on n bits computed \
    by a circuit of NOT, unbounded fan-in AND/OR and MOD_2 gates of depth at most d and size at \
    most s, under the uniform distribution with membership queries, with error 2^-e and \
    confidence 1 - 2^-h. It makes at most (h+1) 2^(12g + 6e + 59) queries, and \
    g <= 2^(2D(5D+25)) B^(2D) with D = d + 7 and B = floor(log2(M^2 (s + 6(n+1)^2 + 3))) + 1, \
    M = 2^(e+10)(3e+42), so for fixed d the number of queries is quasi-polynomial in n, s and \
    2^e. On every target and seed the hypothesis has a De Morgan circuit with at most \
    2^(17g + 9e + 76) gates, also quasi-polynomial for fixed d: the rank test's truth-table \
    circuit (173 * 8^l gates) fed into cikk-learner-hypothesis-size, with l + 2 <= g. Labels: \
    (1) the rank property is this library's variant (one square matrix, threshold C(n, a)/2, \
    level sliceLevel) with density 1/2 where Theorem 5.1 assumes largeness 1/5, and its \
    constructivity is used only as truth-table circuit size, not the source's NC^2; (2) p = 2 \
    only, where Corollary 5.4 states every prime; (3) queries and De Morgan hypothesis size are \
    certified, but the source's running-time bound is not; hypothesis depth is not certified, \
    so the hypotheses are not shown to lie in AC^0[2] (Corollary 5.4's hypotheses are general \
    circuits too); (4) the target class is nonuniform, fixed by d and s; (5) g and \
    l are explicit closed forms from the fixed point l + 2 <= g, replacing the source's choice \
    of L with log L > u^-1(poly); the generator circuits add depth 7, and all constants are \
    this library's; (6) the deviations of cikk-learning-from-dense-test carry over. The \
    abstract form of Theorem 5.1, from any natural property useful against a class, is not \
    included."

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

register_result "minktstar-rp-hard" where
  title := "Hirahara: MINKT* is NP-hard under randomized reductions"
  topic := "meta-complexity"
  sources := [
    { paper := Hirahara2022, theorem := "Theorem I.2",
      locator := "p. 971, \"In particular\"" }
  ]
  theorems := [
    Cslib.Kolmogorov.MINKTStar.rpHard,
    Cslib.Kolmogorov.MINKTStar.rpReducible_GapCMMSA_MINKTStar,
    Cslib.Kolmogorov.MINKTStar.NP_subset_BPP_of_mem_BPP,
    Cslib.Kolmogorov.MINKTStar.NP_subset_coRP_of_mem_coRP
  ]
  scope := "Every NP language reduces to MINKT* (a partial string over {0, 1, *}, then the step \
    budget and the size threshold in unary) by a polynomial-time randomized many-one reduction \
    with one-sided error: yes maps to yes always, no to no with probability at least 2/3. K^t \
    counts the steps of the described machine under the library's multi-tape universal machine, \
    where the source's footnote 6 uses a KT-style measure. Library route: from the library's \
    GapCMMSA Δ g 1 (NP-hard via label cover) by the seeded construction of the partial MCSP \
    reduction, with a polynomial-time generator for the yes side and a count of truth tables of \
    small time-bounded complexity for the no side; the source fixes the statement, not the \
    proof. The (log N)^ε inapproximability and distributional forms of Theorem I.2 are not \
    formalized. The BPP and coRP inclusions are conditional on MINKT* being in BPP or coRP; they \
    follow from the reduction and are not stated separately in the source."

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

register_result "tfnp-eopl-sopl-promised-normalization" where
  title := "Promised-source normalization for EOPL and SOPL (Fearnley et al. Definition 9)"
  topic := "structural complexity"
  sources := [
    { paper := FearnleyGordonMehtaSavani2020, theorem := "Definition 9",
      locator := "Section 2 (arXiv:1811.03841v1)" }
  ]
  theorems := [
    Cslib.Complexity.promisedPotentialLine_normalized,
    Cslib.Complexity.exists_normalizedPotentialBound,
    Cslib.Complexity.endOfPotentialLinePromisedRel_normalized_iff,
    Cslib.Complexity.sinkOfPotentialLinePromisedRel_normalized_iff,
    Cslib.Complexity.endOfPotentialLineRel_searchReducible_promised_normalized,
    Cslib.Complexity.promised_normalized_searchReducible_endOfPotentialLineRel,
    Cslib.Complexity.endOfPotentialLineViolationRel_searchReducible_promised_normalized,
    Cslib.Complexity.mem_EOPL_iff_promised_bounded,
    Cslib.Complexity.mem_SOPL_iff_promised_bounded
  ]
  scope := "Uniform polynomial-time (n + 1)-bit normalization for EOPL and SOPL families over \
    any injective encoding enc : α ↪ List Bool, enforcing P(0^(n+1)) = 0^(n+1) ≠ S(0^(n+1)) and \
    V(0^(n+1)) = 0 with V'(1 u) = V u + 1, unary potential bit-bound 2^(m + 1), pure (R1)/(R2) \
    solution relations without a failed-promise fallback, and failed-promise back-maps via \
    potentialLineBack. Presented on uniform families rather than canonical circuit codes; UEOPL \
    and CLS are not formalized."

register_result "edmonds-optimum-branchings" where
  title := "Edmonds: optimum branchings and minimum-cost spanning arborescences are in P"
  topic := "algorithms"
  sources := [
    { paper := Edmonds1967Branchings, theorem := "Theorem 1",
      locator := "Section 3 (Section 2 reduction, Section 4 algorithm and proof)" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_edmondsList,
    Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_edmondsOutList,
    Cslib.Algorithms.Lean.Arborescence.computableInPolyTime_optimumBranchingList,
    Cslib.Algorithms.Lean.Arborescence.minArborescenceDec_mem_P,
    Cslib.Algorithms.Lean.Arborescence.minOutArborescenceDec_mem_P,
    Cslib.Algorithms.Lean.Arborescence.maxBranchingDec_mem_P
  ]
  scope := "Adjacency matrices in Boolean row-major tables and integer arc weights and \
    thresholds in binary (encIntBin); roots are binary naturals (encNat). Subtraction-free \
    contraction keeps intermediate table entries within (n + 1) ^ i · M₀, yielding native \
    multi-tape P deciders for bounded-cost spanning in- and out-arborescences and \
    bounded-weight branchings. Related O(n³) TimeM bounds and weight-shift reductions live \
    in the sibling Arborescence.Table and Arborescence.Branching modules; Edmonds' Theorem 2 \
    (the branching polytope) and sparse O(m log n) / O(m + n log n) implementations are not \
    formalized."
register_result "simhash" where
  title := "Charikar's SimHash collision law"
  topic := "algorithms"
  sources := [
    { paper := Charikar2002, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Probability.measureCollisionProb_simHash,
    Cslib.Probability.measureCollisionProb_simHash_of_norm_eq_one,
    Cslib.Probability.isLocalitySensitive_simHash_inner
  ]
  scope := "Random-hyperplane sign hash `simHash r u = decide (0 <= <u, r>)` with seed `r` \
    drawn from the standard Gaussian measure `stdGaussian E` on a finite-dimensional real \
    inner product space `E` (and i.i.d. `gaussianReal 0 1` coordinates on `EuclideanSpace`). \
    Proves exact collision probability `1 - angle u v / pi` on nonzero vectors, cosine-similarity \
    sensitivity on unit vectors, and Charikar's triangle inequality for measurable collision laws."

register_result "angular-near-neighbor" where
  title := "Approximate near neighbours in angular distance via SimHash"
  topic := "algorithms"
  sources := [
    { paper := Charikar2002, theorem := unverified, locator := unverified },
    { paper := IndykMotwani1998, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.DataStructure.NearNeighbor.rho_simHash_le,
    Cslib.DataStructure.NearNeighbor.measureReal_query_simHash_eq_none_le
  ]
  scope := "Static `(c, theta)`-approximate near-neighbour query bound over `Measure.pi` tables of \
    `k = numHashes` AND-composed SimHash bits (`L = numTables`, stopping rule `T = 3 * L`). \
    Proves exponent `rho <= 1 / c` and failure probability at most `exp (-1) + 1 / 3` whenever \
    `0 < theta`, `1 < c`, and `c * theta < pi`. Probabilistic query failure only; word-RAM hash \
    buckets, seed storage, dynamic updates, and query runtime are not formalized."

register_result "p-stable-lsh" where
  title := "p-stable LSH collision probabilities for p = 1 and p = 2"
  topic := "algorithms"
  sources := [
    { paper := DatarImmorlicaIndykMirrokni2004, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Probability.measureCollisionProb_p2StableHash,
    Cslib.Probability.p2StableProb_eq_integral,
    Cslib.Probability.measureCollisionProb_p1StableHash,
    Cslib.Probability.p1StableProb_eq
  ]
  scope := "Shifted interval quantization `floor ((proj a x + b) / r)` with `b` drawn from \
    `uniformInterval r`. Proves the general Fubini integral, Cauchy `1`-stability for i.i.d. \
    `cauchyMeasure 0 1` projections, exact Euclidean (`p = 2`, Gaussian) and `l_1` (`p = 1`, \
    Cauchy) collision formulas including Datar et al.'s integral representation and closed \
    forms, strict positivity, and strict monotonicity. General `p` in `(0, 2) \\ {1, 2}` is \
    not formalized."

register_result "p-stable-near-neighbor" where
  title := "Approximate near neighbours in l_2 and l_1 via p-stable LSH"
  topic := "algorithms"
  sources := [
    { paper := DatarImmorlicaIndykMirrokni2004, theorem := unverified, locator := unverified },
    { paper := HarPeledIndykMotwani2012, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.DataStructure.NearNeighbor.rho_p2Stable_lt_one,
    Cslib.DataStructure.NearNeighbor.measureReal_query_p2Stable_eq_none_le,
    Cslib.DataStructure.NearNeighbor.rho_p1Stable_lt_one,
    Cslib.DataStructure.NearNeighbor.measureReal_query_p1Stable_eq_none_le
  ]
  scope := "Static `(c, d)`-approximate near-neighbour guarantees over `Measure.pi` AND tables \
    for Euclidean distance (`p = 2`, `stdGaussian E`) and `l_1` distance (`p = 1`, product \
    `cauchyMeasure 0 1`), proving sublinear `rho < 1` and query failure at most `exp (-1) + 1 / 3` \
    when `0 < w`, `0 < d`, and `1 < c`. Probabilistic query failure only; word-RAM hash buckets, \
    seed storage, dynamic updates, and query runtime are not formalized."

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

register_result "quantum-value-adversary" where
  title := "Ambainis: relational quantum adversary bound for non-Boolean input alphabets"
  topic := "quantum complexity"
  sources := [
    { paper := Ambainis2002, theorem := "Theorem 6",
      locator := "Section 6.1 (arXiv:quant-ph/0002066v1)" }
  ]
  theorems := [
    Cslib.Quantum.norm_inner_valueOracle_valueOracle_ge,
    Cslib.Quantum.one_sub_mul_sum_le_of_sq_le_value,
    Cslib.Quantum.one_sub_mul_sqrt_le_two_mul_mul_sqrt_value,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_le_two_mul_mul_sqrt_value_measureOut
  ]
  scope := "T-query quantum value-query algorithms over an arbitrary finite index type ι, \
    arbitrary input alphabet α, finite value register V, finite workspace W, and arbitrary \
    unitary oracle family step : α → (ℂ^V ≃ₗᵢ[ℂ] ℂ^V), with multi-outcome classical readout \
    out : ι × V × W → β (both measureProb and PMF measureOut forms). Proves exact factor 2 \
    without two-value diagonalization overhead: (1 - δ) √(m m') <= 2T √L and \
    (1 - 2√(ε(1-ε))) √(m m') <= 2T √L."

register_result "quantum-permutation-inversion" where
  title := "Ambainis: Ω(√N) quantum query lower bound for inverting a permutation"
  topic := "quantum complexity"
  sources := [
    { paper := Ambainis2002, theorem := "Theorem 7",
      locator := "Section 6.2 (arXiv:quant-ph/0002066v1)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_sqrt_min_le_of_permInversion_partition,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_div_two_le_of_permInversion_measureOut,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_sub_one_le_of_permInversion,
    Cslib.Quantum.one_sub_two_mul_sqrt_mul_sqrt_card_le_of_permInversion,
    Cslib.Quantum.permInversion_div_two_lower_bound,
    Cslib.Quantum.permInversion_lower_bound,
    Cslib.Quantum.permInversion_measureOut_lower_bound
  ]
  scope := "T-query quantum value-query algorithms over a finite index type ι, finite value \
    register V, finite workspace W, and arbitrary unitary oracle family step : ι → (ℂ^V ≃ₗᵢ[ℂ] \
    ℂ^V), outputting π.symm target via a classical readout out with failure probability at most \
    ε <= 1/2 on every permutation π : Equiv.Perm ι. Proves (1 - 2√(ε(1-ε))) √⌊|ι|/2⌋ <= 2T, \
    (1 - 2√(ε(1-ε))) √(|ι| - 1) <= 2√2 T, and (for 2 <= |ι|) (1 - 2√(ε(1-ε))) √|ι| <= 2√3 T, \
    giving |ι| / 2 <= 1296 T² and |ι| <= 3888 T² at ε = 1/3."

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

register_result "unique-games-perfect-completeness" where
  title := "Satisfiable unique games are in P"
  topic := "interactive proofs"
  sources := [
    { paper := Khot2010, theorem := unverified,
      locator := "Section 2.4, after Definition 2.4 (author copy, p. 6)" }
  ]
  theorems := [
    Cslib.Complexity.gapUniqueGames_one_mem_PromiseP,
    Cslib.Complexity.gapUniqueGames_one_mem_PromiseP_of_pos,
    Cslib.Complexity.gapUniqueGames_zero_mem_PromiseP,
    Cslib.Complexity.isUniqueGame_mem_P,
    Cslib.Complexity.satisfiable_uniqueGame_mem_P
  ]
  scope := "Native multi-tape PromiseP and P membership for each fixed finite alphabet Fin L \
    under Graph.encoding (encPi (encFinEnum (Fin L))), the encoding of UniqueGamesConjecture. \
    For 0 < L, label propagation over List.finRange L is certified by reading the final \
    table directly without constructing ℕ → Fin L closures at runtime. For L = 0, Fin 0 is \
    empty so every unique game vacuously has unsatVal = 0 and GapUniqueGames (Fin 0) 1 s \
    has no no-instances, while no graph is satisfiable. This fixes L rather than taking it \
    as part of the input."

register_result "bareiss-rational-elimination" where
  title := "Exact rational Bareiss–Jordan Gaussian elimination and entry bounds"
  topic := "algorithms"
  sources := [
    { paper := Schrijver1986,
      theorem := "Theorem 3.2; Theorem 3.3; Corollary 3.3a; Equations (28)–(30)",
      locator := "Section 3.2, pp. 29–30; Section 3.3, pp. 32–35" }
  ]
  theorems := [
    Cslib.LinearAlgebra.rationalElim_spec,
    Cslib.LinearAlgebra.ratRref_isReducedRowEchelon,
    Cslib.LinearAlgebra.ratRank_eq,
    Cslib.LinearAlgebra.ratSolve_spec,
    Cslib.LinearAlgebra.rationalElim_entry_bounds,
    Cslib.LinearAlgebra.ratSolve_entry_bounds
  ]
  scope := "Executable row-denominator-cleared fraction-free Bareiss–Jordan elimination over ℚ \
    built on Sylvester–Bareiss minor elimination over ℤ (RREF, exact rank, linearly independent \
    spanning row and kernel bases, canonical linear system solving, and Hadamard/factorial entry \
    and denominator bit-length bounds via stageEntryBound). Local adaptation: clears row \
    denominators upfront and tracks fraction-free minor-scaled Jordan updates with a \
    factorial/Hadamard bound rather than Schrijver's normalized rational elimination \
    (Section 3.3, pp. 32–35). Bounded milestone of Issue #3672 (circulant spectra and fibre-sum \
    bounds remain open there)."

register_result "bareiss-rational-elimination-polytime" where
  title := "Polynomial-time multi-tape Turing certificates for rational Gaussian elimination"
  topic := "algorithms"
  sources := [
    { paper := Schrijver1986,
      theorem := "Theorem 3.3; Corollary 3.3a (ii), (iv), (v)",
      locator := "Section 3.3, pp. 32–35" }
  ]
  theorems := [
    Cslib.LinearAlgebra.rationalElim_computableInPolyTime,
    Cslib.LinearAlgebra.ratRref_computableInPolyTime,
    Cslib.LinearAlgebra.ratRank_computableInPolyTime,
    Cslib.LinearAlgebra.ratRowBasis_computableInPolyTime,
    Cslib.LinearAlgebra.ratKernelBasis_computableInPolyTime,
    Cslib.LinearAlgebra.ratSolve_computableInPolyTime
  ]
  scope := "Native Turing.MultiTapeTM.ComputableInPolyTime certificates for rationalElim, \
    ratRref, ratRank, ratRowBasis, ratKernelBasis, and ratSolve. Local adaptations: uses \
    row-denominator-cleared fraction-free Bareiss–Jordan integer updates and structured \
    enc_structure codecs with explicit unary matrix dimensions and framed signed-binary/rational \
    entries to certify native multi-tape time and workspace bounds unconditionally (including on \
    ragged or oversized-header inputs), whereas Schrijver Section 3.3 analyzes normalized \
    rational elimination in binary input encoding size. Bounded milestone of Issue #3672 \
    (circulant spectra and fibre-sum bounds remain open there)."

register_result "kosaraju-scc" where
  title := "Kosaraju's linear-time strongly connected components and condensation order"
  topic := "algorithms"
  sources := [
    { paper := CLRS2009, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.Lean.DFS.isSCCCondensation_sccs,
    Cslib.Algorithms.Lean.DFS.time_sccsM_of_nodup,
    Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_eq_iff,
    Cslib.Algorithms.Lean.DFS.IsSCCCondensation.indexComponents_le_of_edge
  ]
  scope := "Two-pass Kosaraju SCC decomposition on adjacency lists adj : V → List V in TimeM, \
    returning duplicate-free mutual-reachability components in forward condensation topological \
    order at exact cost 3 * (|vs| + ∑ v, |adj v|) for duplicate-free vertex lists covering V, \
    plus O(|V|) component-index lookup. Visited-set membership, insertion, and function-update \
    array steps are counted as unit-cost operations."

register_result "selected-entries-subset-convolution-timem" where
  title := "Selected entries of ranked subset convolution by the trimmed fast zeta transform"
  topic := "algorithms"
  sources := [
    { paper := ChanItakuraMaYu2026, theorem := "Theorem 2.2",
      locator := "Section 2.1, p. 5" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.TrimmedYates.ret_solveM,
    Cslib.Algorithms.Lean.TrimmedYates.time_solveM
  ]
  scope := "TimeM unit-cost model (one tick per table cell; enumeration and dictionary \
    construction uncharged), not Word-RAM time. Inputs are look-up functions, so the paper's n \
    term for storing the input sets is absent; the bound 3 (d + 1) (sum_{j <= s} (d choose j) + \
    |queries| sum_{s <= j <= 2t} (2t choose j)) is exact. Weights in a commutative ring."

register_result "twosat-linear-timem" where
  title := "Aspvall–Plass–Tarjan linear-time 2-SAT solver and witness construction in TimeM"
  topic := "algorithms"
  sources := [
    { paper := AspvallPlassTarjan1979, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Algorithms.Lean.TwoSAT.solve_eq_some,
    Cslib.Algorithms.Lean.TwoSAT.isSome_solve_iff,
    Cslib.Algorithms.Lean.TwoSAT.time_solveFinM_le,
    Cslib.Algorithms.Lean.TwoSAT.isSome_solveNat_iff
  ]
  scope := "Linear-time 2-SAT decision and satisfying-assignment construction via Kosaraju SCCs \
    of the implication graph in TimeM (at most 12 * n + 8 * |φ| + 1 steps on CNF (Fin n)), \
    together with variable compaction connecting solveNat to Cslib.Complexity.TwoSAT."

register_result "twosat-polytime" where
  title := "Native multi-tape polynomial-time 2-SAT decision and witness construction"
  topic := "computational complexity"
  sources := [
    { paper := AspvallPlassTarjan1979, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.TwoSAT.mem_P,
    Cslib.Complexity.TwoSAT.eval_assignment_of_mem,
    Cslib.Complexity.TwoSAT.computableInPolyTime_solve,
    Cslib.Complexity.TwoSAT.computableInPolyTime_assignment
  ]
  scope := "Multi-tape Turing-machine polynomial-time decision and satisfying-assignment \
    construction for Cslib.Complexity.TwoSAT under binary CNF encoding encCNF, using \
    occurrence-bounded implication-graph reachability without dense variable-index arrays."

register_result "hornsat-least-model" where
  title := "Least-model characterization and non-uniqueness for HornSAT"
  topic := "computational complexity"
  sources := [
    { paper := Papadimitriou94, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.HornSAT.assignment_le_of_eval,
    Cslib.Complexity.HornSAT.isLeast_assignment,
    Cslib.Complexity.HornSAT.exists_multiple_models
  ]
  scope := "Forward-chaining HornSAT.assignment computes the pointwise-least satisfying model \
    of every satisfiable Horn formula, together with an explicit Horn formula admitting \
    distinct satisfying assignments on its occurring variables."
register_result "sperner-2d-ppad-completeness" where
  title := "PPAD-completeness of circuit two-dimensional Sperner (Sperner2D)"
  topic := "structural complexity"
  sources := [
    { paper := ChenDeng2006, theorem := unverified,
      locator := unverified },
    { paper := ChenDengTeng2009, theorem := unverified,
      locator := "Section 4.1, Definitions 4.2, 4.4 and 4.5 (with d = 2)" }
  ]
  theorems := [
    Cslib.Complexity.EndOfLine_searchReducible_Sperner2D,
    Cslib.Complexity.Sperner2D_searchHard,
    Cslib.Complexity.Sperner2D_searchComplete
  ]
  scope := "Explicit polynomial-time search reduction EndOfLine ≤ Sperner2D compiling each \
    n-bit EndOfLine instance uniformly into a circuit on a 2^(n + 5) × 2^(n + 5) grid of 16 × 16 \
    routing, crossover and end-tile gadgets, combined with Sperner2D_mem_PPAD under encSperner2D. \
    Sperner2D fixes the boundary colouring rather than taking a circuit-enforced boundary promise \
    as in discrete Brouwer; two-dimensional discrete Brouwer, three-dimensional Sperner \
    completeness and d-dimensional circuit Sperner are not formalized."

register_result "branching-vector-recurrence" where
  title := "Search-tree branching-vector recurrences and separated node-work bounds"
  topic := "exact exponential algorithms"
  sources := [
    { paper := FominKratsch2010, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.BranchingVector.BranchingRecurrence.le_mul_pow,
    Cslib.BranchingVector.BranchingTree.leafCount_le_pow,
    Cslib.BranchingVector.BranchingTree.workCost_le_mul_pow,
    Cslib.BranchingVector.charSum_fibonacci,
    Cslib.BranchingVector.charSum_prefixSteps_le_one
  ]
  scope := "Positive integer decrease vectors steps = [a₁, …, a_b] with characteristic sum \
    charSum steps r = ∑ r ^ (-aᵢ) <= 1 (1 <= r): T n <= C * r ^ n for recurrences with \
    T n <= max C (sum of T (n - d) over d in steps with d <= n) at every n and C >= 0; \
    leaf count <= r ^ measure s, node count <= (measure s + 1) * r ^ measure s, and separated \
    per-node overhead workCost <= W * (measure s + 1) * r ^ measure s on multi-way search trees \
    (1 <= r), plus closed-form Fibonacci ((1 + sqrt 5) / 2) and prefix [1, …, k] (2 - (1 / 2) ^ k) \
    factors."

register_result "cnf-prefix-branching" where
  title := "Disjoint clause-prefix SAT branching and model-count conservation"
  topic := "SAT algorithms"
  sources := [
    { paper := FominKratsch2010, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Logic.PL.CNF.not_partitionsModels_clauseCoverBranches_two,
    Cslib.Logic.PL.CNF.modelCountOn_eq_sum_clausePrefixTree_leaves,
    Cslib.Logic.PL.CNF.satisfiable_iff_exists_clausePrefixTree_leaf,
    Cslib.Logic.PL.CNF.leafCount_clausePrefixTree_le,
    Cslib.Logic.PL.CNF.leafCount_clausePrefixTree_two_le
  ]
  scope := "Separates covering (CoversModels) and model-partitioning (PartitionsModels) CNF \
    branching rules, refutes model partitioning for naive two-literal clause covers, and proves \
    that disjoint clause-prefix branching on width-<= k CNFs conserves exact modelCountOn across \
    leaves with at most (2 - (1 / 2) ^ k) ^ n leaves (k >= 1) and ((1 + sqrt 5) / 2) ^ n leaves \
    at k = 2. Combinatorial search-tree specification; no native machine runtime asserted here."

register_result "schoening-multitape" where
  title := "Schöning: randomized k-SAT in time (2(k - 1)/k)^n on fair-coin multitape machines"
  topic := "SAT algorithms"
  sources := [
    { paper := Schoening1999, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.Schoening.half_mul_succeedProb_trial_le_fairTrial,
    Cslib.Complexity.Schoening.exists_multiTapePTM_KSAT,
    Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_KSAT,
    Cslib.Complexity.Schoening.exists_decidesWithBoundedErrorInTime_ThreeSAT
  ]
  scope := "For every fixed clause width k >= 3 and amplification parameter c : Nat, one \
    finite-control fair-coin MultiTapePTM on encCNF (CNF Nat) using w = 2n + k + 3 bits per \
    sampleModNat step and a binary encNat countdown over 2 * schoeningTrials k φ.numVars c trials \
    halts on every branch within C * (((2(k - 1))/k) ^ φ.numVars * (|encCNF φ| + 1) ^ E) steps \
    and C * (|encCNF φ| + 1) ^ E work-tape cells (toNTM.RunsInSpace), outputs PMF.pure [false] \
    outside KSAT k, and accepts every φ in KSAT k with probability >= 1 - exp(-c) (>= 2/3 at \
    c = 2, giving (4/3)^n on ThreeSAT)."

section
open Cslib.Communication

register_result "unique-disjointness-cover-lower-bound" where
  title := "Kaibel–Weltge: (3/2)^n rectangle-cover lower bound for unique disjointness"
  topic := "communication complexity"
  sources := [
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Sections 2–3 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    Nondeterministic.three_pow_le_two_pow_mul_coverNumber_uniqueDisjointnessRel,
    Nondeterministic.three_div_two_pow_le_of_coverNumber_uniqueDisjointnessRel_le,
    Nondeterministic.clog_ceil_div_le_ecomplexity_uniqueDisjointnessRel
  ]
  scope := "Exponential (3/2)^|alpha| lower bound on the 1-rectangle covering number and \
    ceil(log2 ceil((3/2)^|alpha|)) bound on N^1 communication complexity of uniqueDisjointnessRel \
    over subsets of a finite type alpha, via card_le_two_pow_of_isValidDisjointSet."

end

register_result "correlation-polytope-extension-complexity" where
  title := "Kaibel–Weltge: (3/2)^n extension-complexity lower bound for the correlation polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" },
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Lemma 6 and Theorem 7",
      locator := "Section 3.2 (arXiv:1111.0837v4)" }
  ]
  theorems := [
    three_pow_le_two_pow_mul_extensionComplexity_corrPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_corrPolytope
  ]
  scope := "Over any linearly ordered field K and nonempty finite index type alpha, \
    extensionComplexity (corrPolytope K alpha) satisfies 3^|alpha| <= 2^|alpha| * xc and \
    (3/2 : F)^|alpha| <= r for every extended formulation with r inequalities, via the valid \
    inequalities 2 diag(a) - a a^T and the unique-disjointness cover bound."

register_result "cut-polytope-extension-complexity" where
  title := "FMPTW: exponential extension-complexity lower bound for the cut polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := DeSimone1990, theorem := unverified, locator := unverified },
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Theorems 5 and 7",
      locator := "Section 3.2 (arXiv:1111.0837v4)" },
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    extensionComplexity_cutPolytope_option_eq,
    three_pow_le_two_pow_mul_extensionComplexity_cutPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_cutPolytope
  ]
  scope := "Linear isomorphism between cutPolytope K (Option alpha) and corrPolytope K alpha, \
    yielding (3/2 : F)^(|V| - 1) <= r for every extended formulation of cutPolytope K V with \
    r inequalities over any finite vertex type V with |V| >= 2."

register_result "stable-set-polytope-extension-complexity" where
  title := "FMPTW: 2^{Omega(sqrt n)} extension-complexity lower bound for the stable-set polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Lemma 8 and Theorem 10",
      locator := "Section 3.3 (arXiv:1111.0837v4)" },
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    extensionComplexity_corrPolytope_le_corrGadgetGraph,
    three_pow_le_two_pow_mul_extensionComplexity_stabPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_stabPolytope
  ]
  scope := "For every m >= 2, the explicit m-vertex graph stabHardGraph m (built from the \
    2 p^2-vertex gadget graph corrGadgetGraph p with p = Nat.sqrt (m / 2) and isolated padding) \
    satisfies (3/2 : F)^Nat.sqrt (m / 2) <= r for any extended formulation of \
    stabPolytope K (stabHardGraph m) with r inequalities."

register_result "tsp-polytope-extension-complexity" where
  title := "FMPTW: 2^{Omega(sqrt n)} extension-complexity lower bound for the TSP polytope"
  topic := "combinatorial optimization"
  sources := [
    { paper := FioriniMassarPokuttaTiwaryDeWolf2015, theorem := "Lemma 11 and Theorem 12",
      locator := "Section 3.4 (arXiv:1111.0837v4)" },
    { paper := KaibelWeltge2015, theorem := "Theorem 1",
      locator := "Section 2 (arXiv:1307.3543v6)" }
  ]
  theorems := [
    extensionComplexity_corrPolytope_le_tspPolytope_splitV,
    extensionComplexity_corrPolytope_le_tspHardGraph_face,
    three_pow_le_two_pow_mul_extensionComplexity_tspPolytope,
    HasExtendedFormulation.three_div_two_pow_le_of_tspPolytope
  ]
  scope := "Via the 3-SAT correlation digraph corrDigraphAdj (at most 23 p^2 vertices) and the \
    padded directed-to-undirected 3-split, corrPolytope K (Fin p) projects linearly from a face \
    of tspPolytope K V whenever |V| >= 69 with p = Nat.sqrt (|V| / 69), giving (3/2 : F)^p <= r \
    for every extended formulation of tspPolytope K V with r inequalities."
register_result "sturm-real-root-counting" where
  title := "Sturm's theorem for separable real polynomials"
  topic := "algebraic complexity"
  sources := [
    { paper := BasuPollackRoy2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Polynomial.sturmSeq_map,
    Polynomial.sturmVariations_sub_eq_card_roots_Ioc,
    Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_squarefree,
    Polynomial.sturmVariations_sub_eq_card_roots_Ioo,
    Polynomial.sturmVariations_sub_eq_card_roots_Icc
  ]
  scope := "Exact real-root counting on (a, b], (a, b), and [a, b] via Sturm sign variations of \
    sturmSeq p (derivative p) for separable (equivalently squarefree) p : ℝ[X], together with \
    field-homomorphism invariance of sturmSeq. Proved over ℝ via local constancy of \
    sturmVariations p x + #{r <= x} rather than general real closed fields."

register_result "mahler-mignotte-root-separation" where
  title := "Hadamard's determinant inequality and Mahler–Mignotte root-separation bounds"
  topic := "algebraic complexity"
  sources := [
    { paper := Mahler1964, theorem := unverified, locator := "pp. 257–262" },
    { paper := Mignotte1982, theorem := unverified, locator := "pp. 259–263" },
    { paper := BasuPollackRoy2006, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Matrix.hadamard_det_sq_le,
    Polynomial.mignotte_sep_mahler_complex,
    Polynomial.mignotte_sep_sqNorm_complex,
    Polynomial.mignotte_sep_sqNorm_real,
    Polynomial.mignotte_sep_sqNorm_rat
  ]
  scope := "Hadamard's determinant inequality over ℂ and Mahler–Mignotte root-separation lower \
    bounds 3 <= |α - β| ^ 2 * (d ^ (d + 2) * coeffSqNorm p ^ (d - 1)) for distinct roots of \
    separable integer and cleared-denominator rational polynomials of degree d >= 2, combining \
    Mahler's discriminant/Mahler-measure inequality with |discr p| >= 1 and Landau's l^2 bound."

register_result "certified-real-root-isolation" where
  title := "Certified Sturm-bisection real-root isolation with Mignotte depth and TimeM bounds"
  topic := "algorithms"
  sources := [
    { paper := BasuPollackRoy2006, theorem := unverified, locator := unverified },
    { paper := Mahler1964, theorem := unverified, locator := "pp. 257–262" },
    { paper := Mignotte1982, theorem := unverified, locator := "pp. 259–263" }
  ]
  theorems := [
    Cslib.RealRoot.isolateRootsTotal_isIsolatingFor,
    Cslib.RealRoot.isolateRootsTotal_pairwise_disjoint,
    Cslib.RealRoot.isolateRootsTotal_bijective_of_squarefree,
    Cslib.RealRoot.isolateRootsTotal_endpoint_bounds_of_bitBound,
    Cslib.RealRoot.isolateRootsTotalM_time_le_of_bitBound,
    Cslib.RealRoot.isolateRootsTotal_spec_of_eq,
    Cslib.RealRoot.isolatePolyRootsTotal_bijective,
    Cslib.RealRoot.isolatePolyRootsTotalM_time_le_of_bitBound
  ]
  scope := "End-to-end TimeM ℕ-charged Sturm-bisection real-root isolator over ℚ[X]: \
    isolateRootsTotalM / isolateRootsTotal on List ℚ is executable (decide +kernel / #eval), \
    charging all preprocessing (trim, Euclidean Sturm sequence, Cauchy bound, denominator \
    clearing, l^2 norm, and Nat.clog), bisection, left-root refinement, and Mignotte-fueled \
    boundary separation into strictly disjoint closed intervals (J₁.upper < J₂.lower), whereas \
    isolatePolyRootsTotalM / isolatePolyRootsTotal on Polynomial ℚ is noncomputable (inheriting \
    Polynomial's noncomputable Finsupp representation) and measures the TimeM ℕ cost of \
    isolateRootsTotalM on p.coeffsBelow (p.natDegree + 1) without charging coefficient extraction \
    from Polynomial ℚ. Certifies strict monotone bijection onto {x : ℝ // aeval x p = 0} for \
    every squarefree p : ℚ[X], dyadic endpoint numerator/denominator bit bounds, and O(n^5 (B+2)) \
    TimeM ℕ operation count under HasCoeffBitBound B cs. TimeM ℕ counts unit-cost algebraic/RAM \
    scalar operations on ℚ/ℤ/ℕ rather than bit-level Turing complexity along Euclidean Sturm \
    remainders."
register_result "yap-collapse" where
  title := "Yap's theorem: coNP in NP/poly collapses the polynomial hierarchy to Σ₃"
  topic := "structural complexity"
  sources := [
    { paper := Yap1983, theorem := unverified, locator := unverified },
    { paper := BodlaenderJansenKratsch2014, theorem := "Theorem 2",
      locator := "p. 6 (arXiv v1)" }
  ]
  theorems := [
    Cslib.Complexity.SigmaP_two_subset_NPPoly_of_coNP_subset_NPPoly,
    Cslib.Complexity.PiP_three_eq_SigmaP_three_of_coNP_subset_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_of_coNP_subset_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_of_UNSAT_mem_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_of_coNP_encBits_subset_NPPoly,
    Cslib.Complexity.PH_eq_SigmaP_three_inter_PiP_three_of_coNP_subset_NPPoly
  ]
  scope := "Conditional collapse for arbitrary injective instance encodings. NPPoly uses a \
    polynomially bounded bit-string advice function of the encoded input length read by a \
    native polynomial-time NP verifier; PH uses polynomial-time alternating verifiers with \
    exact polynomial block lengths. Under coNP ⊆ NP/poly (equivalently NP ⊆ coNP/poly, \
    coNP encBits ⊆ NPPoly encBits, or UNSAT ∈ NPPoly encCNF via Cook–Levin and the CNF \
    decoder), Σ₂ ⊆ NP/poly, Π₃ = Σ₃, and PH = Σ₃ = Σ₃ ∩ Π₃. General level-k advice collapses \
    from Σ_k ⊆ Π_k/poly are not part of this entry."
register_result "randomized-marking-paging" where
  title := "2 H_k-competitiveness of the randomized marking paging algorithm"
  topic := "algorithms"
  sources := [
    { paper := FiatKarpLubyMcGeochSleatorYoung1991,
      theorem := "Theorem 1",
      locator := "Section 3" }
  ]
  theorems := [
    Cslib.DataStructure.Paging.expectedCost_markingStrategy_eq,
    Cslib.DataStructure.Paging.trackerExpectedCost_le_harmonic_mul_cleanCount,
    Cslib.DataStructure.Paging.cleanCount_le_two_mul_scheduleCost,
    Cslib.DataStructure.Paging.markingStrategy_expectedCost_le,
    Cslib.DataStructure.Paging.markingStrategy_isCompetitive,
    Cslib.DataStructure.Paging.markingStrategy_expectedCost_toReal_le
  ]
  scope := "Proves that the randomized marking algorithm (markingStrategy k hk) in the \
    behavioural online strategy model (Online.BehavioralStrategy) is 2 H_k-competitive with \
    additive constant 0 against an oblivious adversary from any admissible initial cache \
    |s₀| ≤ k over any [DecidableEq α] page type. Local adaptations relative to \
    arXiv:cs/0205038v1 Section 3: allows arbitrary page types α, initializes from any |s₀| ≤ k \
    via non-evicting warmup while |cache| < k, and bounds clean requests by 2 * OPT directly \
    against arbitrary (not necessarily lazy) valid offline schedules."


register_result "quantum-weighted-adversaries" where
  title := "Weighted quantum adversary lower bounds (Alb₂ and Alb₃)"
  topic := "quantum complexity"
  sources := [
    { paper := Ambainis2006, theorem := "Lemma 1",
      locator := "Section 4.1 (arXiv:quant-ph/0305028v4)" },
    { paper := Zhang2005, theorem := "Theorem 3 and Theorem 5",
      locator := "Section 1 and Section 2 (arXiv:quant-ph/0311060v2)" }
  ]
  theorems := [
    Cslib.Quantum.WeightScheme.one_sub_mul_sum_le,
    Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sum_le,
    Cslib.Quantum.WeightScheme.one_sub_mul_sqrt_le_of_load_le,
    Cslib.Quantum.WeightScheme.one_sub_two_mul_sqrt_mul_sqrt_le_of_load_le,
    Cslib.Quantum.WeightScheme.ofUnweighted_loadFst_le,
    Cslib.Quantum.WeightScheme.ofUnweighted_loadSnd_le
  ]
  scope := "T-query bit-query phase-oracle quantum algorithms over finite workspace, for general \
    promise relations (x, y) with P x ∧ P y ∧ f x ≠ f y and arbitrary finite output alphabets α \
    (using pairwise disjoint measurement regions S_out : α → Finset _). Covers nonnegative \
    WeightScheme (Ambainis's weighted adversary and Zhang's strong Alb₃ method), its reduction \
    from strong to weak load bounds, and the WeightScheme.ofUnweighted embedding used in \
    AmbainisAdversary.lean to derive the unweighted adversary bound (Alb₂). Spectral matrices \
    and negative weights are in SpectralAdversary.lean."

register_result "quantum-general-adversaries" where
  title := "Spectral and negative-weight quantum adversary lower bounds (ADV and ADV±)"
  topic := "quantum complexity"
  sources := [
    { paper := BarnumSaksSzegedy2003, theorem := unverified, locator := unverified },
    { paper := HoyerLeeSpalek2007, theorem := "Theorem 1 and Theorem 2",
      locator := "Section 1.1 (arXiv:quant-ph/0611054v2)" }
  ]
  theorems := [
    Cslib.Quantum.one_sub_mul_opNorm_le_spectral,
    Cslib.Quantum.one_sub_mul_spectralAdversary_le,
    Cslib.Quantum.one_sub_mul_opNorm_le_general_boolean,
    Cslib.Quantum.one_sub_mul_generalAdversary_le_boolean,
    Cslib.Quantum.one_sub_mul_opNorm_le_general,
    Cslib.Quantum.one_sub_mul_generalAdversary_le,
    Cslib.Quantum.spectralSensitivity_le_spectralAdversary,
    Cslib.Quantum.WeightScheme.le_spectralAdversary,
    Cslib.Quantum.spectralAdversary_le_generalAdversary,
    Cslib.Quantum.spectralAdversary_le_div_of_hammingDist_ge
  ]
  scope := "T-query bit-query phase-oracle quantum algorithms over finite workspace, for general \
    promise relations (x, y) with P x ∧ P y ∧ f x ≠ f y and arbitrary finite output alphabets α \
    (using pairwise disjoint measurement regions S_out : α → Finset _). Covers Barnum–Saks–Szegedy \
    spectral adversary ADV (norm quotient over nonnegative symmetric Γ, cited via HLS07 §1.1 since \
    CCC'03 was not directly inspected), Høyer–Lee–Špalek negative-weight adversary ADV± \
    (strengthened to (1 - 2√(ε(1-ε)) - ε) ADV± ≤ 2T and exact Boolean 1 - 2√(ε(1-ε))), the \
    hierarchy λ(f) ≤ ADV(f) ≤ ADV±(f) and Alb₃ ≤ ADV(f), and the Hamming-distance barrier \
    ADV(f) ≤ N / k. Non-Boolean input alphabets (value queries / permutation inversion) and \
    general composition theorems are not formalized here."
register_result "fujisaki-okamoto-notbot-ind-cca" where
  title := "ROM IND-CCA security of the implicit-rejection Fujisaki–Okamoto transform FO-notbot"
  topic := "cryptography"
  sources := [
    { paper := HofheinzHoevelmannsKiltz2017, theorem := unverified,
      locator := "§3.1 and §3.2.2 (IACR ePrint 2017/604, full version of 2 November 2021)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaRomAdvantage_le
  ]
  scope := "Domain-separated FO-notbot = U-notbot ∘ T over an explicit-coin PKE: for uniform \
    messages, a δ-correct and γ-spread PKE, and a deterministic oracle adversary making at most \
    qG queries to G and qH queries to H (decapsulation queries unbounded), the ROM IND-CCA \
    advantage is at most 2·Adv^{IND-CPA}(romCpaReduction) + (2qH + 2(qG + qH))/|M| + \
    2(qG + qH + 1)δ + 2(qG + qH)2^{-γ} for some distinct fixed challenge messages. The proof \
    composes the T and U-notbot hops directly instead of through OW-PCA; roIndCcaGame draws both \
    real (H) and ideal challenge keys from the arbitrary sampler S.sampleKey (uniform sampleKey \
    recovers HHK17 §2.2 Def. 2.4 / Fig. 4); information-theoretic games with no running-time \
    accounting for the reduction; FO^⊥ is registered separately as fujisaki-okamoto-bot-ind-cca."

register_result "fujisaki-okamoto-bot-ind-cca" where
  title := "ROM IND-CCA security of the explicit-rejection Fujisaki–Okamoto transform FO^⊥"
  topic := "cryptography"
  sources := [
    { paper := HofheinzHoevelmannsKiltz2017, theorem := unverified,
      locator := "§3.1 and §3.2.1 (IACR ePrint 2017/604, full version of 2 November 2021)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.FujisakiOkamoto.Scheme.indCcaBotAdvantage_le
  ]
  scope := "Explicit-rejection FO^⊥ = U^⊥ ∘ T over an explicit-coin PKE: for uniform messages, \
    a δ-correct and γ-spread PKE, and a deterministic oracle adversary making at most qG queries \
    to G, qH queries to H, and qD queries to decapsulation (ROFullQueryBounds A qG qH qD), the \
    ROM IND-CCA advantage is at most 2·Adv^{IND-CPA}(romBotCpaReduction) + 2(qG + qH)/|M| + \
    2(qG + qH + 1)δ + 2(qG + qH + qD)2^{-γ} for some distinct fixed challenge messages. \
    Necessity of the qD·2^{-γ} ciphertext-validity spreadness term is proved in \
    FujisakiOkamoto.SpreadNecessity (advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv). \
    Composes the T and U^⊥ hops directly instead of through standalone OW-PCVA; \
    roIndCcaBotGame and eagerIndCcaBotGame draw both real (H) replies and the independent ideal \
    challenge key from the arbitrary sampler S.sampleKey (uniform sampleKey recovers the \
    standard uniform-ideal-key experiment of HHK17 §2.2 Def. 2.4 / Fig. 4); information-\
    theoretic games with no running-time accounting for the reduction."

register_result "cgks-pir-coalition-lower-bound" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: coalition t-privacy and full-coalition \
    communication lower bound"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998, theorem := unverified,
      locator := "Sections 2.2, 2.4 and 5.1 (pp. 4–6 and 14 of the April 21, 1998 journal \
        version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_one_iff,
    Cslib.Crypto.Protocols.PIR.Scheme.isTPrivate_iff_tuple,
    Cslib.Crypto.Protocols.PIR.Scheme.exists_injective_answers_of_card_le,
    Cslib.Crypto.Protocols.PIR.Scheme.card_le_communication_of_card_le,
    Cslib.Crypto.Protocols.PIR.HasTPrivateScheme.card_le_of_le
  ]
  scope := "One-round information-theoretic PIR over arbitrary payload types β (defaulting to \
    Bool) with perfect correctness and perfect t-privacy against coalitions of at most t servers \
    (equivalent at t = 1 to single-server IsPrivate and for every t to t-tuple query \
    independence; machine runtime in CGKS §2.4, p. 6 is not modeled). Generalizing CGKS §5.1 \
    (p. 14) from k = 1 to full coalitions |S| ≤ t, some joint query vector makes the combined \
    server answers determine the database, and any perfectly correct t-private Boolean scheme \
    with |S| ≤ t communicates at least |ι| bits."

register_result "cgks-pir-shamir" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: explicit finite-field polynomial Shamir \
    t-private PIR schemes"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998, theorem := unverified,
      locator := "Sections 1.1, 2.2, 2.4 and 3.4 (pp. 1–2, 4–6 and 11 of the April 21, 1998 \
        journal version)" },
    { paper := Shamir1979, theorem := unverified, locator := "whole paper" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.isCorrect_shamir,
    Cslib.Crypto.Protocols.PIR.isTPrivate_shamir,
    Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamir,
    Cslib.Crypto.Protocols.PIR.isCorrect_shamirCube,
    Cslib.Crypto.Protocols.PIR.isTPrivate_shamirCube,
    Cslib.Crypto.Protocols.PIR.not_isTPrivate_succ_shamirCube,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_mul_self,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_of_le_pow,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_rows_of_le_pow,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_of_le_pow,
    Cslib.Crypto.Protocols.PIR.hasTPrivateScheme_prime_rows_of_le_pow
  ]
  scope := "Because CGKS §1.1 (pp. 1–2) omits the polynomial construction details, PIR.Shamir \
    gives an explicit finite-field adaptation over Shamir.Params F S (|F| > |S|, instantiated \
    over ZMod p for primes p > k): linear Shamir PIR with matrix balancing gives \
    |S| * 2 m * ⌈log₂ |F|⌉ bits for n ≤ m², unbalanced degree-d hypercube PIR gives \
    |S| * ((d * ℓ + 1) * ⌈log₂ |F|⌉) bits for d * t < |S| and n ≤ ℓ^d, and applying §3.4's \
    rows balancing step (p. 11) gives |S| * ((d + 1) * ℓ * ⌈log₂ |F|⌉) bits for n ≤ ℓ^(d + 1). \
    At d = c - 1 (c ≥ 2, t ≥ 1), this is a weaker finite-field communication variant of CGKS \
    §1.1's headline claim: it matches the exact server count k = c * t and fixed-t database \
    exponent n^(1/c), but retains the field bit-width factor ⌈log₂ |F|⌉ (with |F| > c * t) \
    rather than proving §1.1's varying-t(n) O(t(n) * n^(1/c)) bound. Machine runtime (CGKS \
    §2.4, p. 6) and fair-coin realization of finite-uniform ProbComp sampling are not certified. \
    Any t + 1 colluding servers break privacy whenever |ι| ≥ 2 (for shamir) and whenever D is \
    nonempty (d ≥ 1) and |ι| ≥ 2 (for shamirCube; at empty D, D → ι is a singleton so privacy \
    holds trivially)."

register_result "cgks-pir-block-retrieval" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: private block retrieval transformations and \
    constant-overhead schemes"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := "Propositions 4–5 and Corollaries 6–8",
      locator := "Section 4 (pp. 11–13 of the April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.Scheme.card_mul_le_communication_of_card_le,
    Cslib.Crypto.Protocols.PIR.Scheme.card_mul_le_communication,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_one_iff,
    Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.toBlock,
    Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.toBlock,
    Cslib.Crypto.Protocols.PIR.communication_toBlock_le,
    Cslib.Crypto.Protocols.PIR.communication_toBlock_of_card_answer,
    Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.mapAnswerHom,
    Cslib.Crypto.Protocols.PIR.Scheme.IsCorrect.sumChunks,
    Cslib.Crypto.Protocols.PIR.Scheme.IsTPrivate.sumChunks,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_of_xorReconstruct,
    Cslib.Crypto.Protocols.PIR.hasTPrivateBlockScheme_of_xorReconstruct,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_two_of_le,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_four_of_le_sq,
    Cslib.Crypto.Protocols.PIR.hasBlockScheme_four_of_le_half_sq
  ]
  scope := "One-round private retrieval of ℓ-bit blocks (Scheme ι S R Q A (κ → Bool)) from n \
    blocks with fixed-length binary encoding communication |S| * (⌈log₂ |Q|⌉ + ⌈log₂ |A|⌉) \
    (machine runtime in CGKS §2.4 is not modeled). Single-server (and full-coalition |S| ≤ t) \
    block retrieval requires at least n * ℓ bits (attained at k = 1 by PIR.download). \
    Proposition 4 (Scheme.toBlock) lifts any scheme by repeating answers across block \
    coordinates; Proposition 5 (Scheme.sumChunks) and its AddCommGroup homomorphism reduction \
    (Scheme.mapAnswerHom) compress m parallel XOR-reconstructed instances on Option ι into 1-bit \
    server answers, preserving t-privacy without finiteness assumptions on R or Q. Composing \
    them gives Corollary 6; specializing Proposition 4 to twoServer and cube (Fin 2) gives 4 * ℓ \
    bits with 2 servers for n ≤ ℓ (Corollary 7) and 8 * ℓ bits with 4 servers when n ≤ m² and \
    2 * m ≤ ℓ, in particular n ≤ (ℓ / 2)^2 (Corollary 8, replacing the paper's unrounded \
    n ≤ ℓ² / 4 with the integer subcube condition 2 * m ≤ ℓ, matching n ≤ ℓ² / 4 when ℓ is \
    even)."

register_result "cgks-pir-indexed-schemes" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: PIR with per-server query and answer widths"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := "Definition 1",
      locator := "Sections 2.1, 2.2, 3.3 (Footnote 1), and 5.1 (pp. 4–5, 9, 14 of the \
        April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.indexedCommunication_const,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.isTPrivate_one_iff,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.isTPrivate_iff_tuple,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.exists_injective_answers_of_card_le,
    Cslib.Crypto.Protocols.PIR.IndexedScheme.card_le_indexedCommunication_of_card_le,
    Cslib.Crypto.Protocols.PIR.HasTPrivateIndexedScheme.card_le_of_le,
    Cslib.Crypto.Protocols.PIR.hasIndexedScheme_one_iff
  ]
  scope := "One-round PIR schemes with server-indexed query and answer alphabets Q, A : S → Type \
    and per-server fixed-length binary encoding cost ∑ s, (⌈log₂ |Q s|⌉ + ⌈log₂ |A s|⌉) \
    (execution-dependent variable-length codes within a single server and §2.4 machine runtime \
    are not modeled). Embedding into uniform PIR.Scheme over Σ s, Q s and Σ s, A s \
    (IndexedScheme.toSigmaScheme) transfers coalition-privacy equivalences and the full-coalition \
    (|S| ≤ t) and single-server n-bit lower bounds without re-proving them."

register_result "cgks-pir-general-covering" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: unbalanced covering-code PIR (Theorem 1) and \
    radius-r covering schemes"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := "Theorem 1",
      locator := "Section 3.3, Footnote 1, Figure 1 (d = 5, k = 7), and p. 10 remark \
        (pp. 9–10 of the April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.isCorrect_indexedScheme,
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.isPrivate_indexedScheme,
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.indexedCommunication_indexedScheme_eq,
    Cslib.Crypto.Protocols.PIR.ExactRadiusOneCover.hasIndexedScheme,
    Cslib.Crypto.Protocols.PIR.hasIndexedScheme_of_hammingDist,
    Cslib.Crypto.Protocols.PIR.hasIndexedScheme_seven_of_le_pow_five,
    Cslib.Crypto.Protocols.PIR.isCorrect_radiusCoverScheme,
    Cslib.Crypto.Protocols.PIR.isPrivate_radiusCoverScheme,
    Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_le,
    Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_two,
    Cslib.Crypto.Protocols.PIR.hasScheme_of_hammingDist_two_sq,
    Cslib.Crypto.Protocols.PIR.hasScheme_two_radius_two_of_le_pow_five
  ]
  scope := "Removes the balancedness hypothesis k * (m + 1) = 2^d from CGKS §3.3 Theorem 1 via \
    PIR.IndexedScheme: any injective radius-1 covering code c : S → D → Bool on nonempty D \
    (0 < |D|, made explicit because d - 1 truncates at d = 0 in ℕ and duplicate codewords would \
    violate |S| ≤ 2^d) gives k + (2^d + (d - 1) * k) * ℓ bits for n ≤ ℓ^d, instantiated on the \
    unbalanced optimal 7-word cover of {0, 1}^5 (60 * ℓ + 7 bits, matching Figure 1's 60 n^(1/5) \
    asymptotic term plus k). For general radius-r covers, radiusCoverScheme achieves \
    k * (d * ℓ + ∑_{j ≤ r} C(d, j) * ℓ^j) bits in uniform PIR.Scheme, specializing at r = 2 to \
    k * (2 d ℓ + C(d, 2) ℓ² + 1) (CGKS p. 10's displayed leading expression k d ℓ + k C(d, 2) ℓ² \
    plus the k * (d ℓ + 1) distance-0/1 answer bits; the literal k d ℓ + k C(d, 2) ℓ² bound \
    without lower-order answer terms is not proved) and the coarser polynomial upper bound \
    k * d * ℓ + k * d² * ℓ² (when 2 ≤ d and 1 ≤ ℓ). Server and user runtime (Remark on p. 10) is \
    not modeled."

register_result "cgks-pir-interactive-lower-bound" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: interactive single-server PIR and block lower bounds"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := unverified,
      locator := "Sections 4 and 5.1 (pp. 11–14 of the April 21, 1998 journal version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.injective_leaf,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_pow_card_le_ncard_transcripts,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_pow_card_le_leafCount,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_le_depth,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.card_mul_le_depth,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.exists_iff,
    Cslib.Crypto.Protocols.PIR.InteractiveScheme.exists_block_iff
  ]
  scope := "Arbitrary-round deterministic protocol trees (Communication.Protocol) with \
    independent ProbComp userCoins i and serverCoins over general payload β (defaulting to Bool). \
    Replaces CGKS §5.1's deterministic-output step with Protocol.leaf_eq_iff (rectangle \
    property), forcing |β|^|ι| leaves, |ι| bits on Boolean databases, and |ι| * |κ| bits on \
    (κ → Bool) block databases (attained by download and blockDownload)."

register_result "cgks-pir-multi-interactive-lower-bound" where
  title := "Chor–Goldreich–Kushilevitz–Sudan: multi-server interactive PIR and full-coalition \
    lower bounds"
  topic := "cryptography"
  sources := [
    { paper := ChorGoldreichKushilevitzSudan1998,
      theorem := unverified,
      locator := "Sections 2.1, 2.2, 4, and 5.1 (pp. 4–5, 11–14 of the April 21, 1998 journal \
        version)" }
  ]
  theorems := [
    Cslib.Crypto.Protocols.PIR.MultiRoundTree.depth_compile,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.isTPrivate_one_iff,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.isPrivate_toInteractiveScheme_of_card_le,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.card_le_depth_of_card_le,
    Cslib.Crypto.Protocols.PIR.MultiInteractiveScheme.card_mul_le_depth_of_card_le
  ]
  scope := "Channel-isolated adaptive multi-round k-server PIR (MultiInteractiveScheme), where \
    each step exchanges 1 bit between the user and a chosen server s and serverBit s depends only \
    on x, d s, and the directional ChannelMsg history previously exchanged on s's channel (and \
    IsPrivate / IsTPrivate compare communication sub-traces rather than full server views). \
    Compiling to two-party InteractiveScheme preserves worst-case tree depth and transfers the \
    |ι|-bit and |ι| * |κ|-bit lower bounds whenever all servers may collude (|S| ≤ t). \
    Multi-round lower bounds below full collusion (t < |S|) are not proved."

register_result "prp-prf-switching" where
  title := "PRP/PRF switching lemma: a pseudorandom permutation is a pseudorandom function"
  topic := "cryptography"
  sources := [
    { paper := BonehShoup2023, theorem := "Theorem 4.4 and Corollary 4.5",
      locator := "Section 4.4.3" }
  ]
  theorems := [
    Cslib.Crypto.PRP.advantage_idealExperiment_prfIdealExperiment_le,
    Cslib.Crypto.PRP.prfAdvantage_le_advantage_add
  ]
  scope := "Finite block set D and key set Key, block ciphers E : Key → Equiv.Perm D, and \
    adaptive oracle adversaries with private coins (PRF.Adversary D D) making at most Q queries \
    (IsQueryBounded Q). A uniform permutation and a uniform function of D are distinguished \
    with advantage at most Q.choose 2 / |D|, so the PRF advantage of E is at most its PRP \
    advantage plus Q.choose 2 / |D|. Concrete information-theoretic bounds; no running time is \
    charged and no asymptotic form is stated."

register_result "ajtai-collision-sis" where
  title := "Finding collisions in Ajtai's hash function is no easier than SIS"
  topic := "cryptography"
  sources := [
    { paper := Ajtai1996, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.IsAjtaiCollision.isSolution_sub,
    Cslib.Crypto.isSolution_sub_of_abs_le,
    Cslib.Crypto.ajtaiAdvantage_le_sisAdvantage
  ]
  scope := "Ajtai's hash x ↦ A x mod q on integer vectors, for every nonzero modulus q (the two \
    collision lemmas need no assumption on q), dimensions n × m and bound β, with no primality \
    or compression assumption. Distinct inputs in [0, β]^m (or [-β, β]^m) with equal hashes \
    differ by a nonzero solution with ∞-norm at most β (or 2β), and the collision-finding \
    success probability of any finder against a uniform A ∈ ℤ_q^{n×m} is at most the SIS \
    success probability of collisionToSIS, which subtracts the two inputs. Ajtai's \
    worst-case-to-average-case reduction for lattice problems is not formalized; no running \
    time is charged."

register_result "mldsa-key-only-forgery" where
  title := "ML-DSA key-only unforgeability from Module-LWE and self-target MSIS"
  topic := "cryptography"
  sources := [
    { paper := DucasEtAl2018, theorem := unverified, locator := unverified },
    { paper := NISTFIPS204, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Crypto.MLDSA.isSelfTargetSolution_of_verify,
    Cslib.Crypto.MLDSA.succProbability_koaGame_le_selfTargetGame,
    Cslib.Crypto.MLDSA.succProbability_koaGame_le
  ]
  scope := "Key-only attacks (no signing queries) on ML-DSA verification with valid parameters \
    and a fixed hash H. A verifying forgery yields a self-target MSIS solution for \
    [I_k | A | -t] with hash H(HighBits(·), ·) and bound max γ₁ γ₂. For honest keys with \
    secret coefficients drawn independently from an arbitrary law, the forger's success \
    probability is at most the advantage of forgeryDistinguisher between honest and uniform \
    keys plus the success probability of selfTargetReduction against a uniform [A | t]. \
    Hardness of self-target MSIS is the assumption, not reduced to Module-SIS; the honest-key \
    term is not routed through the uniform-secret DecisionModuleLWE. Chosen-message security \
    (signing-oracle simulation in the random-oracle model) and asymptotic packaging are not \
    formalized; no running time is charged."

register_result "ctr-mode-cpa" where
  title := "CTR mode is CPA-secure for a pseudorandom function"
  topic := "cryptography"
  sources := [
    { paper := KatzLindell2020, theorem := "Theorem 3.33", locator := "Section 3.6.3, p. 93" }
  ]
  theorems := [
    Cslib.Crypto.advantage_ctrCpaGame_le,
    Cslib.Crypto.advantage_ctrCpaGame_ctrModCounter_le
  ]
  scope := "Left-or-right multiple-encryption CPA (Definition 3.22) for CTR mode on n-bit blocks, \
    with a finite key set and a keyed function F : Key → BitString n → BitString n, against \
    block-mode oracle adversaries asking at most K blocks in total and at most ℓ per query. For \
    any counter schedule that is distinct within a query and injective in the IV at each \
    offset, and in particular for the modular counter iv + i mod 2^n when ℓ ≤ 2^n, the \
    advantage is at most the PRF advantages of the two explicit reductions plus 2 K² / 2^n. \
    Concrete bound; no running time is charged and no asymptotic form is stated."

register_result "ofb-mode-cpa" where
  title := "OFB mode is CPA-secure for a pseudorandom function"
  topic := "cryptography"
  sources := [
    { paper := KatzLindell2020, theorem := "unnumbered statement that OFB mode is CPA-secure",
      locator := "Section 3.6.3, p. 92" }
  ]
  theorems := [
    Cslib.Crypto.advantage_ofbCpaGame_le
  ]
  scope := "Left-or-right multiple-encryption CPA (Definition 3.22) for OFB mode on n-bit blocks, \
    with a finite key set and a keyed function F : Key → BitString n → BitString n, against \
    block-mode oracle adversaries asking at most K blocks in total and at most ℓ per query: the \
    advantage is at most the PRF advantages of the two explicit reductions plus \
    2 K (K + ℓ) / 2^n. The source states OFB security without a numbered theorem or proof; the \
    proof follows its Theorem 3.33 template. Concrete bound; no running time is charged."

register_result "clique-eth-lower-bound" where
  title := "No f(k) n^o(k) or FPT algorithm for Clique under ETH"
  topic := "fine-grained complexity"
  sources := [
    { paper := CyganEtAl2015, theorem := "Theorem 14.21", locator := "p.485" }
  ]
  theorems := [
    Cslib.Complexity.ETH.not_clique_subexpVertex,
    Cslib.Complexity.ETH.not_clique_subexpEnc,
    Cslib.Complexity.ETH.clique_not_mem_FPT,
    Cslib.Complexity.DecidableInSubexpTime.threeSAT_of_clique_subexpVertex
  ]
  scope := "Clause-grouping reduction SAT.groupClique on Clique encCliqueInstance and \
    ThreeSAT (encCNF). Under ETH (relative to the library's native DecidableInTimeO model), no \
    decider for Clique runs in time f(k) · (|V| + 1)^o(k) · poly(|enc|) or f(k) · (|enc| + 1)^o(k) \
    with arbitrary f and real exponent g(k) satisfying g(k) ≤ ε k for large k; in particular \
    Clique ∉ FPT. Unconditional subexponential-time transfers to ThreeSAT hold without ETH. \
    This adapts the source's 3-Coloring vertex grouping to 3-CNF clauses and arbitrary f."

register_result "csp-bounded-treewidth" where
  title := "Exact counting and decision for finite-domain CSPs over bounded treewidth"
  topic := "parameterized algorithms"
  sources := [
    { paper := CyganEtAl2015, theorem := "Lemma 7.4 (nice trees)", locator := "p.161" }
  ]
  theorems := [
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountRootedM,
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspDecideRootedM,
    Cslib.Algorithms.Lean.TreeDecomposition.time_cspCountRootedM_le,
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountActiveRootedM,
    Cslib.Algorithms.Lean.TreeDecomposition.ret_cspCountNiceM_equiv
  ]
  scope := "Finite constraint domains Fin q (and arbitrary Fintype/Inhabited D via Equiv D \
    (Fin q)) over a supplied RootedTreeDecomposition of the primal or active primal graph. \
    Normalizes via toNiceTreePruned to at most (3 w + 5)(|V| + 1) nice nodes (size, not runtime \
    bound) and charges unit-cost TimeM inner-loop ticks bounded by (3 w + 5)(|V| + 1) · q^(w + 1) \
    · dpNodeCost w F (excluding recursive list-manipulation overhead like bagList, sem \
    evaluations, and unbounded integer arithmetic). The generic CSP-counting DP extension is an \
    adaptation/original implementation. Computing the tree decomposition is external."

register_result "kleene-post-incomparable" where
  title := "Kleene–Post theorem: existence of Turing-incomparable degrees"
  topic := "computability"
  sources := [
    { paper := KleenePost1954, theorem := unverified, locator := unverified },
    { paper := Soare1987, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Nat.RecursiveIn.kleene_post,
    TuringDegree.exists_incomparable,
    Nat.RecursiveIn.KleenePost.not_limA_le_limB,
    Nat.RecursiveIn.KleenePost.not_limB_le_limA
  ]
  scope := "Finite-extension construction of two sets A = {n | limA n = true} and \
    B = {n | limB n = true} whose characteristic functions A.indicator 1 and B.indicator 1 \
    are Turing incomparable (¬A ≤ᵀ B and ¬B ≤ᵀ A) under Mathlib's TuringReducible over \
    Nat.RecursiveIn.Code. The upper bound A, B ≤ᵀ ∅′ is proved in KleenePostJump; \
    incomparable computably enumerable degrees (Friedberg–Muchnik) remain open (#3379)."

register_result "kleene-post-below-jump" where
  title := "Kleene–Post theorem: incomparable sets constructed by finite extension lie below ∅′"
  topic := "computability"
  sources := [
    { paper := KleenePost1954, theorem := unverified, locator := unverified },
    { paper := Soare1987, theorem := unverified, locator := unverified },
    { paper := Simpson2005, theorem := "Theorem 2.6.4",
      locator := "§2.6, pp. 30–31 (November 1, 2005 draft)" }
  ]
  theorems := [
    kleene_post_below_jump,
    Nat.RecursiveIn.KleenePost.halts_reducibleTo_halting,
    Nat.RecursiveIn.KleenePost.rec_stageNat
  ]
  scope := "Proves that the Kleene–Post limit sequences limA and limB from KleenePost are \
    Turing reducible to the characteristic function halting.indicator 1 of the diagonal \
    ordinary-code halting set halting = {c | (Nat.Partrec.Code.eval (ofNat Code c) c).Dom}, \
    via primitive-recursive stage-bounded oracle evaluation (RecursiveInEvalnPrimrec) and \
    many-one reduction of the one-step extension question Halts to halting. Constructs total \
    Δ⁰₂ sets below ∅′; no c.e. property is proved. Friedberg–Muchnik, Sacks splitting/density \
    and Spector's minimal degree remain open (#3379)."

register_result "w-hierarchy-subset-xp" where
  title := "WeightedCircuitSAT, W[P] and every level W[t] of the W-hierarchy lie in XP"
  topic := "parameterized complexity"
  sources := [
    { paper := CyganEtAl2015, theorem := "weighted-circuit enumeration; Definition 13.16 (W[t])",
      locator := "Section 13.3, pp. 436–437 (authors' May 30, 2016 PDF)" }
  ]
  theorems := [
    Cslib.Complexity.WeightedCircuitSAT_mem_XP,
    Cslib.Complexity.WP_subset_XP,
    Cslib.Complexity.W_subset_XP,
    Cslib.Complexity.WCS_mem_XP,
    Cslib.Complexity.W_subset_WP,
    Cslib.Complexity.WP_eq_FPT_iff,
    Cslib.Complexity.IndependentSet_mem_XP,
    Cslib.Complexity.Clique_mem_XP
  ]
  scope := "Instances of WeightedCircuitSAT encode a one-output unbounded fan-in Boolean circuit \
    with unary input count, framed before the binary target weight k. Exhaustive search \
    over min(n, k)-tuples of input wires gives independent native multi-tape time and workspace \
    bounds C * 2^(D*k) * (L+1)^(D*k+D), hence XP membership. Library fpt-reduction closure gives \
    FPT ⊆ W[t] ⊆ WP ⊆ XP for every t and XP membership for WCS t d, Clique and IndependentSet. \
    WP denotes this library's reduction closure with arbitrary, potentially ineffective time \
    and parameter bounds; equivalence with the effective literature W[P] is not claimed. Circuits \
    are straight-line programs, with the basis conventions documented in WHierarchy.lean."

register_result "dnnf-size-multipartition-cover" where
  title := "DNNF size bounds the multi-partition rectangle cover number"
  topic := "circuit complexity"
  sources := [
    { paper := BovaCapelliMengelSlivovsky2016, theorem := unverified, locator := unverified },
    { paper := ArenasBroadrickLiewVanDenBroeck2026, theorem := "Theorem 3.1",
      locator := "§3.2, p. 9" }
  ]
  theorems := [
    Cslib.Circuits.NNF.exists_isCover,
    Cslib.Circuits.NNF.coverNumberFun_le_size,
    Cslib.Circuits.NNF.coverNumberFun_false_le_size
  ]
  scope := "NNF DAGs with literal and constant leaves and fan-in-two gates on finitely many \
    nodes, size = number of nodes; for at least two variables, a DNNF with s nodes computing f \
    gives a cover of f⁻¹(1) by s rectangles, each for its own partition with both sides of at \
    least n/3 variables."

register_result "ddnnf-negation-separation" where
  title := "d-DNNF is not polynomially closed under negation, given cubic edge expanders"
  topic := "circuit complexity"
  sources := [
    { paper := ArenasBroadrickLiewVanDenBroeck2026, theorem := "Theorem 1.1",
      locator := "§1, p. 3; proof in §5 (Proposition 5.1, Theorem 5.3)" }
  ]
  theorems := [
    Cslib.CubicEdgeColoring.ddnnf_negation_separation,
    Cslib.Circuits.NNF.exponential_separation_of_expanders
  ]
  scope := "For every cubic graph with a proper 3-edge-colouring on n ≥ 2 vertices that is a \
    balanced-cut γ-edge expander, f_G has a d-DNNF with at most 150n + 50 nodes and every DNNF \
    for ¬f_G has at least (48/47)^(γn/126) nodes. Theorem 1.1 itself (a 2^(cn) lower bound \
    with c > 0) is derived from a family of such expanders with γ > 0 on unboundedly many \
    vertex counts, which is Proposition 5.2 of the paper \
    and is a hypothesis, not proved (#4668)."

register_result "three-sat-complement-ph-collapse" where
  title := "3SAT reducing to its complement collapses PH to NP"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 5, Exercise 3",
      locator := "2007 public draft, printed p. 100 / PDF p. 116" }
  ]
  theorems := [Cslib.Complexity.PH_eq_NP_of_ThreeSAT_reducible_compl]
  scope := "Native polynomial-time many-one reduction with encCNF. ThreeSAT has clause width \
    at most three; its complement is inside all CNF Nat, including wider formulas. \
    The conclusion PH enc = NP enc holds for every explicit encoding enc."

register_result "bounded-termination-exponential-completeness" where
  title := "Any-output bounded termination is in E but outside P and is EXP-complete"
  topic := "computational complexity"
  sources := [
    { paper := Goldreich2007DraftR2, theorem := "Exercises 4.6–4.7",
      locator := "PDF p. 36, printed p. 152; bounded universal function: \
        PDF p. 28, printed p. 144" }
  ]
  theorems := [
    Cslib.Complexity.BoundedTermination.mem_E,
    Cslib.Complexity.BoundedTermination.notMem_P,
    Cslib.Complexity.BoundedTermination.polyTimeComplete_EXP,
    Cslib.Complexity.BoundedTermination.mk_desc_mem_iff,
    Cslib.Complexity.BoundedTermination.mem_reencode_iff
  ]
  scope := "Plain bit-word language with total description/input decoders and an MSB-first binary \
    clock; any halted output is allowed. E membership and EXP Karp-completeness hold on all \
    words; canonical native finite-machine triples have exact step-bound semantics. The chosen \
    representation is explicit: no arbitrary-encoding E invariance or sharp simulator bound \
    is claimed. Existing accepting-output-[true] BoundedHalting remains distinct."

register_result "valiant-zero-one-permanent-sharp-p-complete" where
  title := "Valiant: the 0/1 permanent and bipartite perfect-matching counting are #P-complete"
  topic := "counting complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Theorem 9.8",
      locator := "2007-01-08 draft, printed p. 175; PDF p. 191" },
    { paper := Goldreich2007Draft, theorem := "Theorem 6.20",
      locator := "February 2007 draft r3.pdf, PDF p. 23; printed p. 225" }
  ]
  theorems := [
    Cslib.Complexity.zeroOnePermanent_sharpPMetricComplete,
    Cslib.Complexity.zeroOnePermanent_computableInPolyTimeWithOracle,
    Cslib.Complexity.bipartitePerfectMatchingCount_sharpPMetricComplete,
    Cslib.Complexity.bipartitePerfectMatchingCount_computableInPolyTimeWithOracle,
    Cslib.Complexity.intPermanent_sharpPMetricHard
  ]
  scope := "Dense Boolean tables (encBoolTable) read as n x n 0/1 matrices, and the bipartite \
    graphs on Fin n + Fin n they describe (Mathlib perfect matchings). Membership in #P by a \
    native permutation-matrix verifier; hardness under one-query metric reductions composed \
    from #3SAT, Goldreich's Propositions 6.21 and 6.22. The books' Cook-reduction form (Arora \
    and Barak Definition 9.5, FP with a bit oracle) is derived as a native polynomial-time \
    oracle program reading the permanent's bits. Arora and Barak's XOR-gadget proof and its \
    constant 4^(3m) are not formalized; the proof uses Goldreich's gadget."

register_result "bilinear-finite-field-fingerprint" where
  title := "Two-vector matrix identity fingerprint"
  topic := "randomized verification"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.22",
      locator := "r5.pdf; PDF page 70 / printed page 452; rendered guideline exponent checked" }
  ]
  theorems := [Cslib.Probability.toOuterMeasure_bilinear_ne_zero_ge,
    Cslib.Probability.toOuterMeasure_bilinear_zmod_ne_zero_ge,
    Cslib.Probability.toOuterMeasure_bilinear_vecMulVec]
  scope := "Arbitrary finite field and finite rectangular matrix with M ≠ 0. Independent \
    uniform product sampling detects a nonzero bilinear fingerprint with probability at \
    least (1 - 1/|F|)^2. Nonzero outer products attain equality, including characteristic \
    two. No runtime bound or general rank formula."

register_result "random-walk-edge-hitting-time" where
  title := "The random walk crosses an edge of a connected graph in expected time at most 2|E|"
  topic := "randomized complexity"
  sources := [
    { paper := Goldreich2007Draft, theorem := "Exercise 6.19 (completing Proposition 6.13)",
      locator := "February 2007 draft r3.pdf, PDF p. 56; printed p. 258" }
  ]
  theorems := [
    Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_of_adj,
    Cslib.Probability.MarkovChain.hittingTime_randomWalk_add_degree_le,
    Cslib.Probability.MarkovChain.degree_mul_returnTime_randomWalk,
    Cslib.Probability.MarkovChain.hittingTime_randomWalk_le_dist_mul
  ]
  scope := "Finite simple graphs (Mathlib SimpleGraph) with the simple random walk as a \
    MarkovChain; connectedness assumed. Expected hitting and return times are exact \
    extended-real tail sums of the probabilities of avoiding the target, not finite-horizon \
    approximations. Proves E_u[tau_v] + deg v <= 2|E| for every edge {u,v}, Kac's formula \
    deg v * E_v[tau+_v] = 2|E|, and E_u[tau_v] <= 2|E| dist(u,v). Proposition 6.13's cover-time \
    bound and the log-space USTCON algorithm are not included."

register_result "regular-random-walk-hitting-times" where
  title := "Random walks on regular multigraphs: unique stationary law, return and hitting times"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 7, Exercise 9(b)(i), (c), (d)",
      locator := "2007-01-08 draft, printed p. 133; PDF p. 149" }
  ]
  theorems := [
    Cslib.RotationMap.isStationary_randomWalk_iff,
    Cslib.RotationMap.returnTime_randomWalk_eq_card,
    Cslib.RotationMap.returnTime_randomWalk_le_ten_mul_sq,
    Cslib.RotationMap.hittingTime_randomWalk_le_hundred_mul,
    Cslib.RotationMap.ten_mul_card_filter_walkAt_ne_le
  ]
  scope := "d-regular multigraphs presented by rotation maps (loops and parallel edges allowed), \
    random walk along a uniform edge label as a MarkovChain. Exact extended-real expectations. \
    (b)(i): on a connected graph the uniform PMF is the unique stationary law. (c): the expected \
    return time to u equals the size of u's component, hence n when connected and at most 10 n^2. \
    (d): with d <= n, E_{u,v} <= 100 k n^2 along a path of length k, and at most a tenth of the \
    label sequences of length 1000 n^3 avoid t. Part (b)(ii) (visit-count concentration) and \
    part (e) are not included."

register_result "regular-random-walk-visit-concentration" where
  title := "Visit counts of random walks on connected regular multigraphs concentrate around t/n"
  topic := "randomized complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 7, Exercise 9(b)(ii)",
      locator := "2007-01-08 draft, printed p. 133; PDF p. 149" }
  ]
  theorems := [
    Cslib.RotationMap.exists_visits_mem_Icc,
    Cslib.RotationMap.eventually_visits_mem_Icc,
    Cslib.RotationMap.exists_abs_sum_walk_pow_le
  ]
  scope := "Connected d-regular multigraphs presented by rotation maps; probability is the \
    fraction of the d^t label sequences. For every u, v and eps > 0, for all large t, the \
    number of visits to v at times 1..t lies in [(1-eps)t/n, (1+eps)t/n] with probability at \
    least 1 - eps. No aperiodicity is assumed; no explicit rate in t is given."

register_result "goldreich-expander-varying-density-hitting" where
  title := "Expander-walk varying-density product and constant-set bound"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.43, equation (8.24)",
      locator := "March 2007 draft, printed p. 381 / PDF p. 117" }
  ]
  theorems := [
    Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_product,
    Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_product_of_spectralExpansion_le,
    Cslib.RotationMap.dens_filter_forall_walkAt_mem_le_rpow_of_spectralExpansion_le
  ]
  scope := "Finite nonempty rotation map with nonempty incident slots; uniform initial vertex \
    and independent uniform slot choices. Length counts t+1 vertices. Individual densities \
    retained, with explicit transport to lambda/d and the constant-set real half-length power. \
    No machine uniformity, runtime or Exercise 8.44 concentration claim."

register_result "finite-abelian-homomorphism-testing" where
  title := "Finite abelian homomorphism testing and plurality correction"
  topic := "property testing"
  sources := [
    { paper := Goldreich2007DraftR5, theorem := "Exercise 9.21(1)–(3)",
      locator := "r5.pdf; PDF 69–70 / printed 451–452; rendered notation checked" }
  ]
  theorems := [Cslib.HomomorphismTesting.concentration,
    Cslib.HomomorphismTesting.plurality_add, Cslib.HomomorphismTesting.closeness,
    Cslib.HomomorphismTesting.distance_attained, Cslib.HomomorphismTesting.min_le_rejection]
  scope := "Arbitrary finite additive commutative groups, including trivial groups. Uniform \
    independent rejection epsilon and attained minimum normalized homomorphism \
    disagreement delta. Every plurality has mass at least 1-2epsilon; below 1/6 it is \
    a homomorphism with disagreement at most 2epsilon. Unconditionally epsilon >= \
    min(1/6,delta/2). No efficiency or encoding claim."

register_result "linear-space-ne-np" where
  title := "Book: linear space is not NP"
  topic := "space complexity"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 3, Exercise 2",
      locator := "2007 public draft, printed p. 73 / PDF p. 89" },
    { paper := Book1974, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.DSPACE_ne_NP,
    Cslib.Complexity.DSPACE_pow_ne_of_polyTimeReducible_mem
  ]
  scope := "DSPACE encBits (fun n => n) ≠ NP encBits on bit words. DSPACE counts visited work \
    cells of one native multi-tape machine; the draft's Definition 4.1 counts ever-non-blank \
    cells. More generally DSPACE (n ^ k), k ≥ 1, differs from every class closed under \
    polynomial-time many-one reductions, by polynomial space padding and the space hierarchy."

register_result "arora-barak-draft-leftover-hash" where
  title := "Draft leftover hash lemma with entropy k/delta"
  topic := "pseudorandomness"
  sources := [
    { paper := AroraBarak07, theorem := "Lemma 16.42; Chapter 16, Exercise 12",
      locator := "January 8, 2007 draft; printed 308 / PDF 324; exercise printed 319 / PDF 335" }
  ]
  theorems := [Cslib.Probability.IsUniversalHash.isStrongExtractor_of_entropy_div,
    Cslib.Probability.IsUniversalHash.isExtractor_append_of_entropy_div]
  scope := "All n,k,t and positive delta. Uniform independent seed, distinct-input collision \
    bound (1+delta)/2^k, source min-entropy at least k/delta, statistical distance at most \
    sqrt(2 delta). Concatenated output is digest followed by seed. Includes zero digest \
    and large delta; no efficiency or short-seed assertion."

register_result "goldreich-expander-visit-count" where
  title := "Expander-walk selected-time hitting and visit-count tails"
  topic := "pseudorandomness"
  sources := [
    { paper := Goldreich2007DraftR4, theorem := "Exercise 8.44",
      locator := "March 2007 draft, printed p. 381 / PDF p. 117" }
  ]
  theorems := [
    Cslib.RotationMap.dens_filter_selected_walkAt_mem_le,
    Cslib.RotationMap.expect_choose_visitCount_le,
    Cslib.RotationMap.dens_filter_visitCount_ge_le,
    Cslib.RotationMap.dens_filter_visitCount_gt_le,
    Cslib.RotationMap.dens_filter_visitCount_gt_lt,
    Cslib.RotationMap.dens_filter_visitCount_half_lt
  ]
  scope := "Finite nonempty rotation map and ports; uniform initial vertex and independent \
    ports. Length L=t+1 counts vertices, including time zero. Arbitrary selected \
    times, factorial moments, integer tails and strict half-visits for every positive \
    L. The source strict integer bound requires 1<=m<=L and rho+eta^2>0; alpha*L needs \
    an integer convention. No sampler/runtime claim."

register_result "tally-np-exp-nexp" where
  title := "Easy tally NP collapses EXP and NEXP"
  topic := "complexity classes"
  sources := [
    { paper := AroraBarak07, theorem := "Chapter 2, Exercise 23",
      locator := "2007 public draft, printed p. 64 / PDF p. 80" },
    { paper := HartmanisImmermanSewelson1985, theorem := unverified, locator := unverified }
  ]
  theorems := [
    Cslib.Complexity.EXP_eq_NEXP_of_tally,
    Cslib.Complexity.E_eq_NE_of_tally,
    Cslib.Complexity.expPaddedNPEasy_of_tally
  ]
  scope := "(∀ L ∈ TALLY, L ∈ NP encBits → L ∈ P encBits) → EXP enc = NEXP enc and E enc = NE enc \
    for every encoding enc; TALLY is the set of bit-languages of all-true words. Only this \
    direction of Hartmanis–Immerman–Sewelson is proved."
