# Metacomplexity and general lower-bound methods

Metacomplexity treats a function's representation or truth table as input and asks about the cost of computing that function. Complexitylib separates total tables, partial tables, sample constraints and promise gaps. Its general lower-bound interfaces then connect concrete circuits to covers, approximation schemes and cryptographic distinguishers. [complexitylib][complexitylib]

## MCSP variants and encodings

| Variant | Instance and acceptance |
|---|---|
| [Instance](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Basic.lean#L97) | Arity n, table of exactly `2^n` bits, threshold s; some De Morgan circuit of at most s gates computes the table. |
| [Instance](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Partial.lean#L91) | Table entries are optional booleans; a circuit must agree at every defined position. |
| [Instance](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Succinct.lean#L64) | Finite set of input/output samples; one circuit must satisfy all sample constraints. |
| [GapMCSP](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Basic.lean#L270) | Promise separates complexity at most a lower threshold from complexity above an upper threshold. |

“Succinct” here means a sample-set specification, not an arbitrary circuit encoding of a longer truth table. Partial MCSP supplies both the default all-operation count and a binary AND/OR-only cost measure. The library also distinguishes unary and binary threshold encodings. A theorem stated in function arity n may become a qualitatively different bound when expressed in truth-table length `N=2^n`.

The [partial-MCSP abstract](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/PartialMCSPAbstract.lean) states NP membership and ETH-conditional hardness at the `2^o(n log n)` scale, equivalently `N^o(log log N)`. It preserves the different cost/threshold conventions. At this snapshot the library also contains a separate [native fixed-width SAT counting endpoint](../machines-and-classes/native-counting.md) deriving the negation of ETH. Consequently the historical ETH-conditional implication remains a valid formal theorem, but its premise is false within the combined development. That chapter gives the native encodings, quantitative contract, manuscript mapping and review limits; this interaction affects how the conditional result may be applied and is not a proof inconsistency.

## Hardness magnification

The [magnification abstract](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/MagnificationAbstract.lean) gives decision, no-oracle and size-only specializations. Under `NP subset P/poly`, there is a constant c such that every threshold function s and every arity n admit a decision circuit for the corresponding MCSP slice of size at most `2^n c (n+s(n)+1)^c`; a polynomial threshold yields `2^n c(n+1)^c` after changing c. Contrapositive lower bounds therefore imply `NP` is not contained in P/poly and, through the native containment bridge, `P != NP`.

The [implementation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/MCSP/Magnification.lean) explicitly maps this version to the cited McKay–Murray–Williams lemma/theorem and explains its stronger lower-bound premise and restricted scope. It uses fixed-threshold witness certificates, binary subcube merging and a polynomial-hierarchy collapse. It should not be cited as every search, oracle or fine quantitative formulation of magnification in the literature.

## Hardness versus randomness

[IsAverageCaseHard](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/HardnessAmplification.lean#L58) says that every Boolean function of De Morgan circuit complexity at most s agrees with a target function on at most a `1/2 + 1/s` fraction of uniformly distributed inputs. Both the gate bound and agreement bound are non-strict. This is a nonuniform circuit predicate, distinct from hardness against uniform probabilistic heuristics. XOR amplification and the Nisan–Wigderson generator use it as an intermediate interface.

The [average-case endpoint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/BPP/Derandomization.lean#L302) assumes a binary language in native E and a positive natural c such that its n-bit slice satisfies this predicate at size `2^(n/c)` at all sufficiently large lengths, with natural-number division. It proves `P enc = BPP enc` for every supplied instance encoding. The native deterministic decider computes a Nisan–Wigderson generator and enumerates its short seeds. The result credits Nisan and Wigderson. [nisanwigderson94][nisanwigderson94]

The [worst-case endpoint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Complexity/Classes/BPP/WorstCaseHardness.lean#L80) assumes instead a native E language and a real `gamma > 0` whose slices require at least `2^(gamma*n)` De Morgan gates at **all sufficiently large lengths**. It derives the same native class equality through Reed–Muller/Hadamard encoding and local list decoding. The endpoint is credited to Impagliazzo and Wigderson, while the source identifies the Sudan–Trevisan–Vadhan proof route. These declarations assume their circuit lower bounds; an infinitely-often hardness hypothesis and simulation variant are not formalized here. [impagliazzowigderson97][impagliazzowigderson97] [sudantrevisanvadhan01][sudantrevisanvadhan01]

The [machine endpoint account](../machines-and-classes/endpoints-and-hierarchies.md#hardness-versus-randomness) states the uniform class side and the literature-check scope. Here the inspected evidence is the circuit-hardness definition, the final theorem statements and their direct native bridge, not an independent reconstruction of the hardness amplification or generator proof.

## Natural proofs and cryptographic assumptions

[NaturalProof.IsLarge](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/NaturalProof.lean#L147) separates largeness, constructivity and usefulness. A property is a family of sets of Boolean functions. Constructivity concerns deciding from a full truth table; polynomial in that input length is exponential in the function's arity. Usefulness excludes every easy language's slices eventually. Largeness is a quantitative density condition.

The Razborov–Rudich barrier is stated through concrete circuit distinguishers: a property excluding a small-circuit keyed family distinguishes its truth tables from uniform random function tables with advantage equal to the property's density. An exponentially secure keyed family prevents a P/poly-natural useful property. A [generator-to-barrier bridge](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Boolean/NaturalProof/Generator.lean) uses the GGM construction and its circuit-size analysis. Security is an explicit hypothesis and belongs to the cryptographic model in the [programs section](../programs-crypto-and-probability/index.md), not an unconditional result.

## Lower-bound interfaces beyond one theorem

[Atom](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Fusion/Basic.lean#L60) represents a gate together with argument values as an atom and a finite collection of invariant failures as a cover. The central inequality `coverComplexity_le_ecomplexityFrom` lets a combinatorial cover lower bound imply a weighted source-relative circuit lower bound. This factors semantic lower-bound arguments away from a particular syntax traversal.

[SemifilterWitness](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Fusion/Semifilter.lean#L127) specializes the argument to monotone truth-valued maps on subsets that preserve the empty and full set. These maps need not preserve intersections, so they are not filters in the usual algebraic sense. Pair covers connect their witness failures to AND complexity, including the conondeterministic model in which both input polarities and OR gates are free.

[Scheme](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Computability/Circuit/Approximation.lean#L55) compares exact and approximate interpretations of the same circuit program. A correctness relation can be one-sided; each gate has a finite exception set with bounded cardinality. The approximate value is correct outside the union of gate exceptions, giving a failure bound by total charged cost. A shared gate is charged once even if its output has many uses. This reusable statement supports the monotone approximation method rather than reproving the same union argument for every lower bound.

These are mathematical proof interfaces, not automatically encoded certificates or proof-search procedures. Other reusable measures in the query and formula layers—sensitivity, certificate complexity, degree, Khrapchenko edge counts—play a similar role while using different objects and costs.

## Two-boundary CNF counting

Import [`TwoBoundary`](../../Complexity/Logics/Propositional/CNF/TwoBoundary.lean)
and open `Cslib.Logic.PL.TwoBoundary`. Supply an existing `CNF V`, an internal
path length `r`, and `P : Fin (r + 1) → DNF V`.
Each `P j` uses the existing `DNF` syntax with conjunctions of literals as terms;
`DNF.eval x (P j)` evaluates it under assignment `x`. `query B r P false`
and `query B r P true` are ordinary CNFs on `V ⊕ Fin r`; the two endpoint bits
are substituted constants, not declared variables. Empty term lists are false,
whereas an empty term is true. Every variable of the finite type is declared,
including those that do not occur in any generated clause.

`counting_identity` subtracts the satisfying-assignment cardinalities of those
queries to recover the solution count of `B` and all the predicates.
`query_width`, `query_length` and `declared_variables` give width at most
$\max(b,d+2)$, at most $m_B+2\sum_j |T_j|$ clauses, and exactly
$n+h-1$ variables with $h=r+1$. With no predicates, use `B` itself.
The [checked client](../../ComplexityTests/PaperEndpoints/TwoBoundary.lean)
includes one-edge paths, empty terms, failed predicates, unused variables and
a general three-variable count identity. This is an algebraic reduction;
no external subexponential SAT theorem or native runtime bound is assumed.

## Original-row selection

Import [`RowSelection`](../../Complexity/Foundations/LinearAlgebra/RowSelection.lean)
and open `Cslib.LinearSystem`. Supply coefficient rows `A`, right-hand side `b`,
and an actual rational solution `x₀` to `exists_original_rows`. It returns a finite
subset of original row indices, independent coefficient rows, the same rational
solution set, and selected cardinality equal to the row-space dimension.
`exists_original_rows_of_two_solutions` takes two distinct rational solutions and
proves that the selected cardinality is strictly below the number of columns.
`solution_eq_of_span_eq_top` handles uniqueness when the rows span the column space.
The [checked client](../../ComplexityTests/PaperEndpoints/RowSelection.lean) uses five
repeated exact-one equations, an unused column, two distinct solutions, and an
inconsistent system that cannot supply the required witness.

This is the algebraic row-selection step of STOC submission 1575, Lemma 3.1
(PDF pp. 10–11). It is not an elimination implementation or a polynomial bit-time
certificate. For the construction from selected signed rows to actual counting
queries, use the next section. Polynomial-bit-time elimination, local
VC-dimension-one table representation and advertised runtime remain open. In particular, the
[native counting endpoint](../machines-and-classes/native-counting.md) currently
has a weaker exponent with an additional $\log\log$ factor; it cannot establish
the sharper quantitative bound by direct substitution.

## Signed exact-one counting queries

Import [`ExactOneCounting`](../../Complexity/Logics/Propositional/CNF/ExactOneCounting.lean)
and open `Cslib.Logic.PL.ExactOne`. Use a finite ordered declared variable type
(such as `Fin r`), scopes `S : I → Finset V` and polarities `p : I → V → Bool`.
A variable occurs once per scope; `Holds (S i) (p i) x` says precisely one of its
signed literals is true. `signedClause` uses the existing clause syntax, and
`holds_iff_evalOne` identifies this presentation with `Clause.evalOne`. The older
occurrence-sensitive API also permits repeated variables; this scope presentation
enforces the manuscript's distinct-variable convention.

For retained rows indexed by `Fin (k + 1)`, `query S p false` and `query S p true`
construct ordinary CNFs over `V ⊕ Fin k`. `compilation_iff` verifies the actual
coverage/exclusion construction, and `counting_identity` subtracts their model
counts. `sideQuery B S p` adds arbitrary binary side clauses on the same columns,
deduplicating them before compilation. `side_counting_identity` counts the
intersection with those side constraints. `sideQuery_width` proves width three;
`sideQuery_length` gives at most $13r^2$ clauses when $k+1<r$. Deduplication covers
empty, unary and binary clauses, including repeated literals and contradictory
empty clauses; the bound is independent of the original side-clause count.

To derive the retained rows and queries from an original nonempty signed system,
apply `exists_queries_of_two_rational_solutions` with two distinct rational solutions of
its derived equations and the binary side CNF. The witnesses need not be Boolean or satisfy the side
CNF. `equation_iff` derives the rational coefficients and right-hand sides from
literal truth. The theorem selects original rows by rational rank and returns
actual queries, with $h=k+1$ equal to that rank, $h<r$, exactly $r+h-1$ declared
variables, and at most $2r-2$ declared variables. Each answer is bounded by
$2^{2r-2}$, hence fits in at most $2r-1$ bits. No query or reduced subsystem
is assumed. This is an existence theorem; extracting its classical row choice
is not a certified elimination algorithm.

For direct cases, `count_eq_zero_of_empty_scope` and
`count_eq_zero_of_inconsistent` prove rejection. Given an actual rational
solution and full column span, `fullRankCount_correct` proves that
`fullRankCount B z` returns the count by testing whether every entry of `z` is
zero or one and checking the side CNF on `candidateBits z`. `coverScopes` and
`coverScopes_iff` transpose indexed Exact Cover without identifying equal
candidate sets or dropping empty candidate-set variables.

The [complete client](../../ComplexityTests/PaperEndpoints/ExactOne.lean) starts
from repeated original signed rows, an unused bit and explicit different
solutions. It checks the rank-derived bounds and the individual counts $8$ and
$4$, whose difference is the source count $4$. Invalid extensions cancel;
neither individual query is intended to count only source solutions. The client
also checks side clauses, non-Boolean rational candidates, empty scopes, zero
variables and equal/empty indexed cover candidates. From the repository root,
run `scripts/build.sh ComplexityTests.PaperEndpoints.ExactOne` to elaborate it.

This proves the actual rank-derived query existence/correctness portion of
STOC submission 1575, Theorems 1.2/5.2 and Corollary 5.3, and the Exact Cover
transposition of Corollary 5.4. It does not complete those algorithmic statements:
polynomial-bit-time rank preprocessing, the VC-dimension-one relation-table
representation, bounded-demand/graph extensions and the sharper counting
runtime remain unproved. No curated headline abstract is added for this partial
coverage.

## Known Limitations

The conditional statements, truth-table scales and source-specific quantitative scope were inspected, but the complete magnification and cryptographic reduction proofs were not independently reconstructed in this worker pass. Distinguish a valid conditional theorem, a conventional open assumption, and a premise that this same library proves false elsewhere.

[complexitylib]: ../sources.md#complexitylib
[impagliazzowigderson97]: ../sources.md#impagliazzowigderson97
[nisanwigderson94]: ../sources.md#nisanwigderson94
[sudantrevisanvadhan01]: ../sources.md#sudantrevisanvadhan01
