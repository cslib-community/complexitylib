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
queries, use the next sections, including the table representation below.
The executable assembly below supplements this existence API. Its encoded
polynomial-bit-time certification and the advertised runtime remain open. In particular, the
[native counting endpoint](../machines-and-classes/native-counting.md) currently
has a weaker exponent with an additional $\log\log$ factor; it cannot establish
the sharper quantitative bound by direct substitution.

## Executing elimination and query assembly

Import [`ExactOneElimination`](../../Complexity/Logics/Propositional/CNF/ExactOneElimination.lean)
and open `Cslib.Logic.PL.ExactOne`. Supply the original finite signed scopes and
polarities, with ordered row and declared-variable types (for example `Fin m` and
`Fin r`), and the side CNF to `preprocess B S p`. The result is a `CountPlan`:
a direct natural-number answer or two ordinary CNFs on `V ⊕ Fin k`.
`CountPlan.execute` accepts a counter indexed by the number of added bits. Both
queries are constructed without using either answer. `preprocess_correct` supplies
mathematical counting semantics; `preprocess_budget` requires binary side clauses
and proves width three, at most $13r^2$ clauses and at most $2r-2$ declared variables
for every emitted query. Every direct answer uses zero queries.

The implementation first handles $r\leq 1$ by at most two assignment tests.
Larger instances use `originalElimination`, which scans original row indices in
column order, transforms the coefficient matrix and right-hand side together,
and back-substitutes a rational point. Inconsistency returns zero. A pivot in
every column leaves one rational candidate, which is checked against the original
signed rows and side clauses; a non-Boolean candidate cannot pass this check.
Otherwise the retained original indices feed the existing two-boundary compiler.
With no retained rows, the two queries are the deduplicated binary side CNF and
an unsatisfiable CNF on the same declared bits.

For general rational systems, import
[`Elimination`](../../Complexity/Foundations/LinearAlgebra/Elimination.lean) and use
`Cslib.LinearSystem.eliminateCached rows columns A b`. The explicit lists determine
pivot order. `eliminateCached_eq` connects its materialized computation to the
verified `eliminate` kernel. `eliminate_point`, `eliminate_consistent_iff` and
`eliminate_selected_iff` require that all nonzero input columns occur in `columns`;
`eliminate_unique` determines those coordinates when every listed column gets a
pivot. Selected indices always come from `rows` and number at most `columns.length`.
Intermediate matrices, right-hand sides and back-substituted points use
[`Function.tabulate`](../../Complexity/Foundations/Data/Function/Tabulate.lean)
to share their computed entries. Lookup is a finite linear scan.

The [executed client](../../ComplexityTests/PaperEndpoints/ExactOneElimination.lean)
checks all 256 ordered pairs of two-bit signed rows against independent direct
counts, rational row permutations, inconsistency, unused bits, and a 40-variable
instance with 80 repeated rows. From the checkout root, validate it with
`LEAN_NUM_THREADS=2 scripts/build.sh ComplexityTests.PaperEndpoints.ExactOneElimination`.
If a different imported version is used, check the module search path and the
checkout's toolchain and dependency manifest before investigating a proof failure.

These are functional execution and syntax-budget theorems. They do **not** certify
polynomial bit time or polynomial peak space: coefficient-growth bounds and a
costed encoded implementation remain open. No arithmetic-operation contract is
assumed in place of that proof. The sharper fixed-width counting runtime and the
bounded-demand/graph applications remain separate open objectives.

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
polynomial-bit-time rank preprocessing, bounded-demand/graph extensions and
the sharper counting runtime remain unproved. No curated headline abstract is added for this partial
coverage.

## Tables of VC dimension at most one

From the repository root, import
[`VCOneTables`](../../Complexity/Logics/Propositional/CNF/VCOneTables.lean)
and open `Cslib.Logic.PL.VCOne`. A table is a `Finset (Fin w → Bool)`;
repeated listed tuples are identified by `List.toFinset`. `DimensionOne R` is
Mathlib's finite set-family VC dimension bound on `family R`, the positive
supports of the actual tuples. To prove the promise, use
`dimensionOne_of_missing`: supply one missing Boolean pattern for each pair of
distinct coordinates. This excludes the full two-bit cube.

`binary R` constructs the unary/binary side clauses, and `binary_eval` identifies
its models with `closure R`, the tuples whose projections onto at most two
coordinates occur in the table. `dimensionOne_closure` preserves the VC bound;
`card_le` specializes Mathlib's Sauer–Shelah theorem to obtain at most $w+1$
closure tuples. For executable enumeration, use `listedClosure R`.
`listedClosure_eq` identifies it with this semantic closure. It starts with one
zero-padded empty prefix (or none for an empty table), extends one coordinate by
both bit values, and retains only prefixes whose unary/binary projections occur
in the input rows. Unprocessed coordinates stay zero. `mem_prefixes` proves the
exact invariant; `prefixes_card` bounds every retained frontier by $w+1$ under
the VC promise. `prefixCandidates_le` bounds attempted extensions by
$2\ell(w+1)$ for a list of $\ell$ distinct coordinates, hence $2w(w+1)$ for the
complete traversal. Each extension checks at most $w^2$ coordinate pairs by
scanning the explicit table; comparisons for deduplication inspect the $w$
declared bits. The recursive result is shared between the two bit extensions.
No cube enumeration or feasibility oracle is used. This original variant of the
manuscript's 2-SAT prefix method tests pair compatibility rather than
extendibility. The VC bound controls its frontier, and the final rows are
exactly the closure.
The side formula has at most $1+2w+4w^2$ clauses, each of width
at most two. The empty clause handles an empty table.

For each unwanted closure tuple `y`, `greedyScope R y` visits the declared
coordinates and deletes a coordinate when the remaining projection still has
no agreeing table row. Its tests scan the given table; it does not search
subsets of coordinates. `greedy_separator` proves that its scope has at least
three coordinates and that each allowed row disagrees with `y` at exactly one
of them. `separatorScope` supplies this computed scope for a tuple indexed by
`closure R \ R`. `representation_iff` proves exact membership using the binary
CNF and these signed exact-one equations. `representation_bounds` derives at
most $w+1-|R|$ equations from the table, without assuming a representation.
There are no auxiliary bits in this step, so no extra satisfying extensions.
Singletons retain their constant coordinates. On zero coordinates, the nonempty
table contains the unique empty tuple and imposes no restriction; the empty
table rejects every assignment.

For several tables, give `w : I → ℕ`, embeddings
`scope : (i : I) → Fin (w i) ↪ V`, and the actual tables `R i`.
Injectivity excludes repeated coordinates within a scope; scopes of different
tables can overlap arbitrarily, in any order. `tables_iff` aligns all local
separator literals in the shared global columns and proves pointwise equivalence
to the original table conjunction. Its `EquationIndex` enumeration uses
`listedDifferenceFintype`, an explicit map from the listed unwanted tuples;
it does not enumerate the semantic closure's finite cube. `tablePolarity` uses
finite scope lookup, with `tablePolarity_eq` proving equality to the semantic
extension, including the false default outside the scope. For $r=|V| \ge 2$,
`tables_queries` then derives
two ordinary 3-CNFs with at most $2r-2$ declared variables and $13r^2$ clauses
each, whose exact count difference is the original global count. It includes
empty equation families, inconsistent systems and unique-candidate direct
branches. No rational witnesses or desired representation are required from
the caller. `tables_queries_of_two_rational_solutions` exposes the rank-derived
nonunique branch separately. `directCount_correct` and `directCount_small`
cover direct enumeration when at most one global bit is declared.

The [complete checked client](../../ComplexityTests/PaperEndpoints/VCOne.lean)
starts from a three-row table whose closure adds exactly one unwanted tuple.
It checks the greedy separator and a global instance with opposite signs on
overlapping scopes and one unused bit, giving four source assignments. It
also checks empty and zero-width tables, duplicate rows, constant coordinates,
and a failed VC promise. Guarded runtime checks execute the 32-coordinate,
two-row listing (two outputs and 126 attempted extensions), zero-width cases,
global equation enumeration, derived scopes, and opposite signs on overlapping
columns. These runtime checks supplement the kernel-checked general proofs;
they do not prove correctness by executing a solver. Run
`scripts/build.sh ComplexityTests.PaperEndpoints.VCOne` from the repository root.
If a scope cannot be embedded injectively or the missing-pattern proof fails,
check distinctness of its coordinates and its actual four pair patterns before
applying the theorem.

These results establish the mathematical representation and global query-budget
claims of [ChenJiangZhu2027], Theorems 1.3/6.3 (PDF pp. 18–21). They do not yet
certify a polynomial-bit-time reduction: the executable row selection and direct
branches below have no coefficient-growth/encoded-bit-cost proof for exact
elimination. The semantic `closure` remains a finite-cube
specification; the compiler's equation enumeration uses `listedClosure` instead.
The greedy separator is supplied explicitly, but no machine-level running-time certificate
is asserted. The sharper counting runtime and bounded-demand/graph applications
remain open. The broad issue is not complete and no curated abstract is added.

## Executing plans from overlapping VC-one tables

Import [`VCOneElimination`](../../Complexity/Logics/Propositional/CNF/VCOneElimination.lean)
and use `Cslib.Logic.PL.VCOne.tablePlan w scope R` with tables indexed by `Fin m`.
`equationList` enumerates missing closure tuples using the proved prefix listing,
retaining each table's index. `listedScopes` and `listedPolarity` number and align
these equations in the global columns, materializing scopes and signs before
elimination. The compiler then runs the same elimination
and direct/query branches as `preprocess`. No disjointness of scopes is needed.
`tablePlan_correct` assumes each input table has VC dimension at most one;
`tablePlan_budget` gives the emitted query bounds, with the number of globally
declared variables as parameter.

Binary restrictions execute through `scanBinary`. The proved compiler equality
`binary_eq_scanBinary` preserves the exact original `binary` syntax while replacing
a generic finite universal test over all Boolean tuples by a scan of the actual
table. This distinction matters even when a table contains only two rows on many
coordinates. The [global executed client](../../ComplexityTests/PaperEndpoints/VCOneElimination.lean)
counts overlapping positive/negative scopes with an unused bit, handles both
zero-width table cases, and constructs the plan for a 32-coordinate two-row table.
From the checkout root, run
`LEAN_NUM_THREADS=2 scripts/build.sh ComplexityTests.PaperEndpoints.VCOneElimination`.
The functional bridge does not discharge the coefficient-growth/encoded-runtime
obligation described above or prove the whole-paper algorithmic endpoint.

### Binary square-system recovery

Import `Complexity.Computability.PolyTime.Int.Cramer` for an independently certified
square-system component. `Cslib.LinearSystem.cramerCertificate A b` takes an integer
row table `A` and RHS list `b`, returning a common denominator and numerator list.
The dimension is `A.length`; missing entries read as zero and extra columns/RHS
entries are ignored. The denominator is the determinant of that normalized square.
Each numerator is computed with the existing division-free Bird program, avoiding
rational intermediate coefficients. Negative denominators are allowed.

`cramerCertificate_correct` proves the scaled integer equations and
`cramerCertificate_unique` proves uniqueness when the denominator is nonzero.
`cramerBoolean A b` tests that denominator and checks every numerator is either zero
or the denominator. `cramerBoolean_correct` identifies this test with Boolean
feasibility for nonsingular squares. A singular input is rejected even if it has
Boolean solutions; use the existing general functional preprocessing for such inputs.

`cramerCertificate_polytime` and `cramerBoolean_polytime` certify uniform multitape
Turing-machine polynomial time under `encPair (encList (encList encIntBin))
(encList encIntBin)`, with the dimension varying with the input. These certificates
include binary arithmetic. For entries and RHS magnitudes below $2^\beta$,
`cramerCertificate_bits_le` bounds each emitted integer's sign-magnitude code length
by $\beta+n(1+n+\beta)+2$, where $n=A.length$.
`cramerColumnRows_stage_bits_le` controls the actual numerator determinant stages;
the reused determinant API also controls partial sums/products and table encodings.

The [complete checked client](../../ComplexityTests/PaperEndpoints/CramerBinary.lean)
executes negative-denominator, non-Boolean, singular, dimension-zero, ragged and
128-bit examples and compares all 1,296 signed two-variable/RHS inputs with direct
Boolean testing whenever nonsingular. From the checkout root, run
`LEAN_NUM_THREADS=2 scripts/build.sh ComplexityTests.PaperEndpoints.CramerBinary`.
The rectangular API below reuses this square solver. Neither binary component
replaces `originalElimination` or certifies the global `tablePlan` pipeline yet.

### Binary rectangular row selection and consistency

Import `Complexity.Computability.PolyTime.Int.Rectangular` for the general integer
row-table component. Supply the declared column count `n`, a list of integer rows
`A`, and a RHS list `b`. Width is explicit, so empty matrices and unused columns
retain their intended dimension. Missing entries/RHS values read as zero; columns
after `n` and RHS entries after `A.length` are ignored.

`gramRowBasis n A` scans original row indices once. It retains a row precisely when
the enlarged row Gram determinant is nonzero, using the existing binary Bird
program. There is one determinant test per input row, with no enumeration of row
subsets or minors. The output is in reverse acceptance order. Theorems
`gramRowBasis_independent`, `gramRowBasis_span`, `gramRowBasis_length` and
`gramRowBasis_rank` establish independence, exact row-span preservation, at most
`n` selected rows, and equality of the computed length with rational row-space
dimension. `gramRowBasis_selected_iff` preserves solutions on consistent systems.

`rectangularCertificate n A b` solves the selected row Gram system with
`cramerCertificate`, then multiplies by the transpose of the selected original
matrix. It emits a nonzero denominator and exactly `n` integer numerators. Their
quotients define `rectangularPoint`. `rectangularConsistent` checks every original
scaled equation. `rectangularConsistent_correct` proves exact rational consistency
for arbitrary rectangular inputs, including dependent and contradictory rows;
`rectangularPoint_correct` proves that acceptance returns an actual solution.
`rectangular_unique` proves uniqueness at full computed column rank.
`rectangularBoolean_correct` then identifies the candidate's Booleanity test with
Boolean feasibility at that full rank. At deficient rank this test is insufficient:
for `x+y=1` the recovered point is `(1/2,1/2)`, although Boolean solutions exist.

`gramRowBasis_polytime`, `rectangularCertificate_polytime` and
`rectangularConsistent_polytime` give uniform multitape polynomial binary time,
with unary declared width and framed binary integer lists. These certificates
include basis selection, every determinant, transpose multiplication and the scan
of all original equations. For original entry/RHS magnitudes below $2^\beta$, set
$g=n+2\beta$ and $B=g+n(1+n+g)+2$. The denominator has at most $B$ sign-magnitude
bits and each final numerator at most $n+\beta+B+1$ bits.
`rowGram_partial_sum_natAbs_lt`, `rowGram_stage_bits_le` and
`transposeNumerators_partial_sum_natAbs_lt` control the actual Gram sums, Bird
stages and recovery sums; the determinant API additionally bounds stage products.

The [complete checked client](../../ComplexityTests/PaperEndpoints/RectangularBinary.lean)
executes tall, wide, dependent, contradictory, empty, zero-width, ragged and
128-bit cases, a 40-column/80-row dependent input, and all 1,296 signed two-variable
systems/RHS combinations against the existing rational elimination kernel.
From the checkout root, run
`LEAN_NUM_THREADS=2 scripts/build.sh ComplexityTests.PaperEndpoints.RectangularBinary`.

### Counting plans using the binary selector

Import `Complexity.Logics.Propositional.CNF.ExactOneBinary` for
`binaryPreprocess S p B`, on `n` declared bits and `m` signed equations indexed
by `Fin n` and `Fin m`. `integerRows` materializes coefficients in
$\{-1,0,1\}$ and `integerRhs` moves negative-literal constants to the right
side. Their entry theorems identify these integers with the existing rational
signed equations; this input needs no denominator-clearing compiler.
`binaryConsistent_iff` detects inconsistency, `binaryIndices_selected` proves
pointwise equivalence of the computed original equations on acceptance, and
full computed rank justifies checking the unique candidate. Deficient rank
emits the existing two-query construction. `binaryPreprocess_correct` and
`binaryPreprocess_budget` prove exact counting and the global syntax budgets.

For actual tables, import
`Complexity.Logics.Propositional.CNF.VCOneElimination` and use
`binaryTablePlan w scope R` with declared variables `Fin r`.
`binaryTablePlan_correct` requires each table to have dimension at most one;
`binaryTablePlan_budget` applies without this semantic premise. Overlapping
scopes share columns, and unused declared variables retain their multiplicity.
The rational `preprocess` and `tablePlan` interfaces remain available.

From the checkout root, check the [complete binary client](../../ComplexityTests/PaperEndpoints/ExactOneBinary.lean)
and [overlapping-table client](../../ComplexityTests/PaperEndpoints/VCOneElimination.lean)
with `scripts/build.sh ComplexityTests.PaperEndpoints.ExactOneBinary ComplexityTests.PaperEndpoints.VCOneElimination`.
The former executes all 256 ordered pairs of two-bit signed equations against
an independent source count, plus direct, no-equation and 40-bit cases.

This is a functional composition with a binary-certified elimination backend.
A uniform encoded binary runtime theorem for the whole composition is still
missing: closure/separator listing, equation materialization, candidate checking,
control and query construction all need resource composition. In particular,
interpreting the certificate by rational division in `checkCandidate` has not
received a binary runtime proof. Full-pipeline peak space, the sharper counting
runtime, bounded-demand and graph endpoints remain open. The rational kernel's
own coefficient-growth theorem is not implied by the binary backend.

## Known Limitations

The conditional statements, truth-table scales and source-specific quantitative scope were inspected, but the complete magnification and cryptographic reduction proofs were not independently reconstructed in this worker pass. Distinguish a valid conditional theorem, a conventional open assumption, and a premise that this same library proves false elsewhere.

[complexitylib]: ../sources.md#complexitylib
[impagliazzowigderson97]: ../sources.md#impagliazzowigderson97
[nisanwigderson94]: ../sources.md#nisanwigderson94
[sudantrevisanvadhan01]: ../sources.md#sudantrevisanvadhan01
