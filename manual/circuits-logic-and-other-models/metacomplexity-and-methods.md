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
transposition of Corollary 5.4. The binary rank/dispatch and sharp signed-clause counter are
completed in the later executable sections (`ExactOneCountingResources`); they support Theorems
1.2/5.1–5.2 and Corollary 5.3 on the recorded distinct-variable signed-clause encoding. For
Corollary 5.4, the actual original indexed candidate-list transposition and complete native resource
composition remain open; equal/empty candidates must retain separate original bits. No curated
headline abstract is added by this inventory assessment.

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

This interface is a functional composition with a binary-certified elimination backend.
The `BinaryFrontend.compile` continuation below now supplies the complete actual binary
constructor and sharp counting resource endpoint for the explicit promised table encoding.
The rational kernel's own coefficient-growth theorem is not implied by the binary backend.
The weighted-row endpoint later in this chapter is also certified; the independent-domination
frontends below cover independent domination, kernels, perfect matching cuts and efficient edge
domination; other graph endpoints remain open.

The listing resource bound is promise-restricted. Without `DimensionOne`, take
one width-$w$ table containing the all-zero tuple, all-one tuple and all $w$
unit vectors. For distinct coordinates these rows realize all four patterns;
for a repeated coordinate both values occur. Consequently every tuple passes
the pair tests and `listedClosure` contains $2^w$ tuples, although the input has
at most $w+2$ rows. The unconditional query syntax budget does not bound this
intermediate computation. The new capped list implementation below bounds all intermediate frontiers even outside the
promise. Its equality with the semantic closure still requires `DimensionOne`; it does not use
the uncapped function as a polynomial-time subroutine.

The same import provides `tablePayload w scope R`, which retains the global
declaration count, local widths, lexicographically listed Boolean rows and
injective scope column numbers. `encTablePayload` frames this data: declarations
and widths use unary encoding (including unused coordinates), rows are literal
bits and column numbers are binary. `equationPayload` materializes the actual
signed equations as lists of global column/polarity pairs; its membership theorem
connects every row to `equationList`. `planPayload` erases bounded column types,
numbering auxiliaries after the original columns, and retains the declared count.
`encPlanPayload` tags a binary direct answer or two framed CNFs;
`binaryTableBits` applies it to the actual `binaryTablePlan`, without advice.
The complete overlapping-table client above checks these constructors and framing
edge cases. `frontier_coordinates_le` and `prefix_comparison_coordinates_le`
bound stored coordinates and full-frontier comparison volume under `DimensionOne`.
`payloadRows` and `payloadRhs` now materialize the actual signed equation payload
in uniform polynomial binary time; `payloadConsistent_polytime` composes them
with the rectangular solver on unary declared width and framed binary literals.
`payloadConsistent_equationPayload` identifies this executed stage with the
original signed equations, retaining separate rows and shared signed columns.
The complete client checks conflicting signs, empty equations, unused columns
and the no-equation case. This certifies the equation-to-consistency stage.

Import `Complexity.Computability.PolyTime.CNF.VCOneFrontend` for the resource-certified
preprocessing path, in namespaces `VCOne.BinaryClosure`, `VCOne.BinarySeparator` and
`VCOne.BinaryFrontend` under `Cslib.Logic.PL`. `BinaryClosure.enumerate` takes a unary local
width and explicit bit rows. It extends full-width prefixes in reverse coordinate order, scans
all unary/binary projections, deduplicates and caps every frontier at $w+1$. The polynomial
machine proof charges each scan, comparison, copy, delimiter and loop step and bounds every
intermediate state; it does not infer runtime from final output size. `enumerate_rows` proves
that the cap removes nothing on VC-one tables. `missing_rows` extracts exactly the unwanted
closure tuples, and `missing_length` proves the sharp deficit $w+1-|R|$.

`BinarySeparator.equations` computes those missing tuples and greedily deletes coordinates by
scanning the original table before writing each signed equation. `equation_rows_perm` and
`equation_separator` connect the actual lists to the reviewed signed exact-one separator;
`equations_polytime` charges the complete computation. `BinaryFrontend.side` constructs the
actual quadratic syntax universe and keeps exactly the unary/binary restrictions valid on the
listed rows. `side_rows`, `side_width`, `side_length` and `representation` give Theorem 1.3's
pointwise representation and quantitative budgets for these actual writers, including empty
relations and width zero.

`BinaryFrontend.payload` consumes the existing `encTablePayload`: unary global declaration
and local widths, explicit bit rows and binary scope columns. It writes separate signed equations
in the original shared columns, and deduplicates the side CNF globally. `payload_tables` proves
pointwise correspondence on `tablePayload w scope R`, with arbitrary table counts/arities and
arbitrary overlap, assuming only locally VC-one relations and injective individual scopes.
`payload_count` transfers the exact count on all declared original bits, including unused bits.
`payload_side_length` bounds the actual side output by $1+2r+4r^2$, independent of table count.
The semantic encoding here uses the existing canonical explicit relation rows (`Finset` images
sorted as lists) and declared injective scopes; no correctness/admission theorem for other table
file formats or malformed tuple/scope lengths is claimed. All raw payloads nevertheless have
polynomial computation resources, even outside the VC-one promise.

`payload_polytime`, `basis_polytime` and `consistent_polytime` compose all local construction and
overlap-writing costs through actual signed integer materialization and the binary backend.
The computed `basis` consists of original equation indices and has length at most the declared
width. `consistent` checks the affine equations only: an empty allowed table may yield a false
side clause and no equations, so linear consistency does not assert table satisfiability.
The actual all-cases table dispatcher and its complete counting resource composition are now
available as follows. Generic Theorem 1.1 resource transfer, graph applications and ALL-main remain
open where not separately covered.

From the repository root run
`scripts/build.sh ComplexityTests.PaperEndpoints.VCOneResources`.
The [complete client](../../ComplexityTests/PaperEndpoints/VCOneResources.lean) executes missing
point/separator extraction, width-zero empty/tautological relations, a 32-coordinate two-row
closure, a capped non-VC-one relation, shared columns with opposite signs, a contradictory
shared-scope system and original assignment count 4 with an unused bit.

### Complete original-table dispatch and sharp counting resources

From the checkout root, import
`Complexity.Computability.Complexity.FineGrained.VCOneCountingResources` and open
`Cslib.Logic.PL.VCOne`. Pass the original `tablePayload w scope R` to
`BinaryFrontend.compile`. Its tagged result is a binary direct answer or two explicit CNFs with
a unary declaration. It computes the side/equation payload, consistency and an original-row basis.
Small declarations, false side clauses, no constraints, inconsistent equations and full rank take
direct branches. Full rank checks the computed integer candidate against the side formula and all
original rows. Rank zero retains the side formula; positive deficient rank writes both path queries
from computed original rows. It never requests a basis or enumerates the declared assignment cube.

`BinaryFrontend.compile_polytime` certifies all construction stages with binary arithmetic,
including the direct $2^r$ answer and actual query writes. `compile_count` identifies the count
of the actual result with `Satisfies w scope R` on all declared bits. `compile_withinBudget`
bounds declarations by $2r-2$, width by three and clause lists by
`WeightedRow.countingBudget r 1` (a uniform quadratic independent of table count).
`payload_presentation` transports local row permutations and signs through each scope embedding;
its proof witnesses are never inputs to the executable compiler.

`BinaryFrontend.exists_count_sharp_certificate` supplies one actual counting algorithm and its
`NativeCertificate`: global polynomial peak workspace and
$L^{O(1)}2^{O(\eta(r))}$ time on the canonical promised table inputs, where $L$ is the complete
`encTablePayload` bit length. It composes the actual constructor, sequential general-density
width-three counting and binary subtraction; direct tags bypass the counter.
`exists_count_realEta_certificate` states the real exponent
$\eta(r)=r\log\log r/\sqrt{\log r}$ for $r\ge16$. The rounded theorem includes all smaller cases.
Constants are uniform over table count, arity and overlap. The native word-certificate convention
and unary global/local declarations are material; no succinct binary-declaration or alternative
raw-table parser/admission theorem is asserted. Polynomial space holds for all raw payloads;
correctness and sharp time use locally VC-one tables with injective individual scopes.

Run `scripts/build.sh ComplexityTests.PaperEndpoints.VCOneDispatch` from the repository root.
The [complete checked client](../../ComplexityTests/PaperEndpoints/VCOneDispatch.lean) checks
zero/one declarations, empty and zero-width tables, the binary 256-bit free answer, inconsistent
and fractional/full-rank candidates, rank-zero side constraints, deficient-rank queries and
original overlapping tables with unused bits. Its exhaustive small counter is a test oracle only;
the resource theorem instantiates the proved native sharp counter.

### Generic explicit DNF conditions without a VC-one promise

Import `Complexity.Computability.Complexity.FineGrained.TwoBoundaryFrontend` and open
`Cslib.Logic.PL.TwoBoundary.BinaryFrontend`. The original input contains a unary declaration,
a side CNF and an explicit list of DNFs. Literal indices are binary and lists are framed.
Use `declared`, `side` and `conditions` to inspect the input, and `compile` to write the plan.
It emits one ordinary query when there are no conditions and the two endpoint-substituted queries
otherwise. Repeated, contradictory and empty terms are preserved. No relation table or assignment
cube is materialized. In particular, arbitrary DNFs need not define VC-one relations: the DNF
containing one empty term admits the entire cube. The source's generic Theorem 1.1 therefore uses
the path writer directly, rather than a conversion to the separate table theorem.

For finite-variable formulas, `ofFinite B P` erases only the original bounded labels.
`compile_count` proves the original declared-assignment count, including unused bits and arbitrary
inter-condition overlap. `compile_budget` gives exactly $n+h-1$ variables when $h>0$, at most
$m_B+2\sum_j|P_j|$ clauses, width at most $\max(b,d+2)$ and declared output indices; the $h=0$
branch retains the original side query. `compile_polytime` certifies the actual binary constructor,
including list traversal, endpoint substitution and every literal/encoding write. There is no
normalization or VC-one promise conversion to trust: the explicit original terms themselves
satisfy the proved correspondence.

`exists_count_sharp_certificate b d` instantiates the actual general-density counter at fixed
width $\max(b,d+2)$, sequentially executes the emitted queries and charges binary reconstruction.
It supplies one original-input algorithm with global polynomial peak workspace and promised time
$L^{O_{b,d}(1)}2^{O_{b,d}(\eta(n+h))}$, where $h$ is the actual number of conditions and $L$ is the
complete framed input length. `exists_count_realEta_certificate` states the real single-log-log
eta bound for $n+h\ge16$; rounded bounds include all smaller cases. This does not silently assume
that the number of conditions is linear in $n$. These are the existing native word/resource
certificates, with a unary declaration; untrusted-byte parsing/admission and succinct declarations
are not added by these statements.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.TwoBoundaryFrontend`.
The [complete checked client](../../ComplexityTests/PaperEndpoints/TwoBoundaryFrontend.lean)
checks arbitrary two-literal terms, overlapping/repeated/contradictory terms, empty conditions and
terms, side clauses, unused bits, zero variables, one-versus-two calls and a 256-variable writer.
It also proves the full-cube counterexample to a generic VC-one conversion.

### Original-graph independent domination without a cardinality test

Import `Complexity.Computability.Complexity.FineGrained.IndependentDomination` and open
`Cslib.Logic.PL.IndependentDomination`. `ofGraph G` is the canonical explicit square Boolean
adjacency matrix of a simple undirected graph on `Fin n`, with unary vertex declaration and
framed literal Boolean cells. `build` writes edge exclusions and one closed-neighborhood DNF
condition per vertex. `build_polytime` charges matrix lookups, loops and all writes, without
vertex-subset enumeration. The literal labels of the resulting DNF input are binary.

`finite_semantics` and `plan_count` identify the original independent dominating selections.
Each Boolean vector specifies exactly its selected original vertices; there are no extra markings.
`plan_budget` gives $2n-1$ declared variables, width three and at most $3n^2$ clauses per emitted
query. The empty graph uses the one-query zero-variable branch and has one selection. The actual
`exists_count_sharp_certificate` composes construction and native counting with global polynomial
space and $L^{O(1)}2^{O(\eta(n))}$ time, proving the fixed-linear $2n$ rescaling.
`exists_count_realEta_certificate` gives real eta for $n\ge16$, with rounded bounds at every size.

This covers the no-size-test fixed independent-domination rule in Corollary 7.2 and the local
predicate of Appendix D.4, Proposition D.3. The continuation below supplies variable input
cardinality bounds. Size distributions, general finite/cofinite rules, labeled partition matrices
and the remaining graph applications are separate. Graph correctness uses the canonical simple undirected input; arbitrary raw matrix
shapes have total polynomial construction/global space without an additional graph-admission claim.
Run `scripts/build.sh ComplexityTests.PaperEndpoints.IndependentDomination` from the root.
The [complete checked client](../../ComplexityTests/PaperEndpoints/IndependentDomination.lean)
checks empty/isolated/edge/path/triangle/star graphs, original counts and exact query budgets.
Its small exhaustive oracle is a test instrument, not the production counting algorithm.

### Independent domination with signed binary input cardinality bounds

Import `Complexity.Computability.Complexity.FineGrained.IndependentDominationInterval` and open
`Cslib.Logic.PL.IndependentDominationInterval.Signed`. `ofGraph G lo hi` retains the canonical
simple undirected adjacency matrix and adds two signed binary input bounds. The accepted original
selections satisfy $\mathrm{lo}\le |S|\le\mathrm{hi}$. Set both bounds equal for an exact-size
count, or use lower bound zero for Appendix D.4, Proposition D.3's input upper-bound problem.
Negative upper bounds and reversed intervals reject; negative lower bounds impose no restriction.
The empty-graph branch checks whether the interval contains zero and writes its answer directly.

`CardinalityInterval.generate` caps each binary threshold at one more than the original unary
vertex declaration before calling the existing linear population-count circuit generator.
`FunctionalCNF.write` traverses its explicit gates and writes full truth-table clauses and output
units. The functional extension proof gives exactly one accepted gate trace per original selection
inside the interval, and none outside. In particular the tested weight counts original vertices,
not true gate variables. The two thresholds share their input wires and introduce
$a\le952(v+1)$ auxiliary variables and at most $2+2856(v+1)$ clauses of width three.
There is no search over gate assignments or loop of length equal to a binary cutoff.

The natural-bound `build` appends this formula to the edge exclusions and keeps the original
closed-neighborhood DNFs. `representation` proves exact original-selection count correspondence.
For $v\ge1$, `query_budget` gives two actual queries with $N=2v+a-1$, width three and at most
$3v^2+2+2856(v+1)$ clauses each. Signed normalization is executable and polynomial in the full
encoded length. `Signed.exists_count_sharp_certificate` composes normalization, the empty branch,
gate/query writing, sequential counting and reconstruction into one actual native certificate:
global polynomial workspace and $L^{O(1)}2^{O(\eta(v))}$ time. The real-eta version applies for
$v\ge16$; the rounded certificate includes every smaller graph. Constants are uniform over both
input bounds. The fixed-linear rescaling charges $2v+a$, retaining the single loglog factor.

From the checkout root run
`scripts/build.sh ComplexityTests.PaperEndpoints.IndependentDominationInterval`.
The [complete graph client](../../ComplexityTests/PaperEndpoints/IndependentDominationInterval.lean)
computes edge/path/triangle/isolated/empty cases, overlapping neighborhoods, impossible intervals,
negative bounds, huge binary cutoffs, actual query metadata and direct empty dispatch.
The [cardinality client](../../ComplexityTests/PaperEndpoints/CardinalityInterval.lean) checks
unique-trace evaluation and constant-size generation at out-of-range 512/1024-bit thresholds.
Small test oracles enumerate original selections only; production uses the proved sharp counter.

These are native word/resource certificates on explicit framed encodings, with unary declarations,
binary references and signed binary bounds. They do not add a fresh bit-transition machine
simulation or arbitrary untrusted-byte graph admission. General finite/cofinite degree-rule and
labeled partition constructors, the width-three private-mark refinement and four graph predicates'
full witness/optimum composition remain open. The continuations cover kernels, matching
applications, Maximum Induced Matching and Upper Domination optimization/witness recovery, and
the full induced-matching distribution.
ALL-main remains open.

### Outgoing-absorbing kernels in directed graphs

Import `Complexity.Computability.Complexity.FineGrained.DigraphKernel` and open
`Cslib.Logic.PL.DigraphKernel`. `ofDigraph G` writes the canonical directed adjacency matrix on
`Fin v`. It retains arc orientation, unary vertex declaration and framed Boolean cells. The input
encoding and actual arc-exclusion/neighborhood traversal are shared with `IndependentDomination`;
this reuse does not convert the input to an undirected graph. `plan` performs actual binary query
writing and `plan_polytime` charges all matrix lookups, loops and literal writes.

`Digraph.IsKernel G S` means that no arc joins two selected vertices and every outside vertex has
an **outgoing** arc into the selected set. Reversing every arc gives the opposite convention.
`finite_semantics` proves the formula correspondence and `plan_count` counts original vertex sets,
with no marking or selection-code multiplicity. A directed odd cycle can have no kernel; a single
arc has its head as the unique kernel. `query_count` gives two ordinary queries for $v\ge1$;
`plan_budget` gives $N=2v-1$, width three and at most $3v^2$ clauses per query. At zero vertices,
the one ordinary query has zero variables and no clauses, and counts the empty kernel once.

`exists_count_sharp_certificate` composes construction, sequential counting and reconstruction
with global polynomial workspace and $L^{O(1)}2^{O(\eta(v))}$ native time. Its count is the
cardinality of actual kernel vertex sets. `exists_decide_sharp_certificate` additionally charges
binary positivity postprocessing: the count certificate's global space/output bound proves that
reading its result is polynomial in the original input length. The real-eta versions use
$\eta(v)=v\log\log v/\sqrt{\log v}$ for $v\ge16$, and the rounded versions retain all smaller
and empty inputs. No assumed graph reduction, count, runtime or extra-loglog suppression is used.

This is Proposition D.5 (PDF p. 37) and the kernel decision specialization of Corollary 7.4
(p. 26). The source is loopless and directed. The proved formulas also count the same explicitly
defined kernel predicate on canonical directed matrices with loops; there is no symmetry or
looplessness hypothesis hidden in the interface. Raw encoded construction/global space are total,
without asserting arbitrary-byte graph admission. Certificates use the existing native word/resource
model, not a fresh bit-transition simulation; declarations remain unary.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.DigraphKernel`.
The [complete checked client](../../ComplexityTests/PaperEndpoints/DigraphKernel.lean) computes
empty, isolated, single-arc, reversed-arc, oriented-star, directed odd/even cycle, transitive and
dense symmetric cases. It checks actual original selections, the stronger loop case, nonvacuous
kernel/nonkernel instances and query metadata at 64 vertices without selection enumeration.
Tiny exhaustive query oracles are tests only; production certificates use the proved sharp counter.

The general Corollary 7.2 degree rules and Theorem 7.3 labeled partitions remain open. Of the six
Corollary 7.4 predicates, independent-domination counting with size bounds and kernel counting/
decision are covered here. The continuations below cover Perfect Matching Cut and Dominating
Induced Matching, signed-threshold Maximum Induced Matching and Upper Dominating Set.
Maximum Induced Matching's optimum/witness extraction and Corollary 7.5's complete distribution
appear below. The other predicates' full witness/optimum composition and Proposition 7.6's
the width-three path-marker refinement remains open; the exact width-four counter appears below. These graph milestones do not complete
ALL-main.

### Perfect matching cuts with labeled sides

Import `Complexity.Computability.Complexity.FineGrained.PerfectMatchingCut` and open
`Cslib.Logic.PL.PerfectMatchingCut`. Reuse `IndependentDomination.ofGraph G`, `Input` and
`encInput` for the canonical explicit simple-undirected adjacency matrix on `Fin v`: the vertex
declaration is unary and Boolean cells are framed. The new `upper`, `conditions` and `build`
actually traverse that matrix. Distinct neighbor pairs write both width-three upper clauses;
each vertex has a positive and a negative singleton-term neighborhood condition. `build_polytime`
charges the triple loops, matrix lookups, binary indices and every literal write. It enumerates
neighbor pairs, without enumerating partitions or matchings.

`SimpleGraph.crossingSubgraph G side` contains **all** original edges whose Boolean side labels
differ, on all original vertices. `SimpleGraph.IsPerfectMatchingCut G side` requires this spanning
subgraph to be a Mathlib perfect matching and requires both labeled sides to be nonempty. This is
the source's Perfect Matching Cut problem, not an arbitrary perfect matching that contains some
cut. On a nonempty graph, `finite_semantics` proves that the actual constraints hold precisely for
this predicate: the upper clauses allow at most one opposite neighbor, and the two signed
conditions require at least one. Each Boolean assignment specifies exactly one labeled partition;
swapping labels counts separately. No claim about unordered-cut counts is implicit.

For $v\ge1$, `query_count` and `query_budget` prove exactly two ordinary queries with
$N=3v-1$, width three and at most $10v^3$ clauses each. The upper part has at most $2v^3$ clauses;
there are exactly $2v$ coverage conditions and at most $2v(v+1)$ terms in total. Ordered neighbor
pairs may duplicate clauses, without changing the count or source polynomial bound.
`run` rejects the empty graph before constructing any constraints or invoking its continuation:
the vacuous per-vertex condition at zero vertices is not a partition into two nonempty sides.
`plan_count` concerns nonempty inputs; complete counting certificates include this empty branch.

`exists_count_sharp_certificate` instantiates the proved general-density DNF counter and composes
actual dispatch/construction, sequential query calls, subtraction and reconstruction. The output is
the exact labeled-cut count, with global polynomial workspace and
$L^{O(1)}2^{O(\eta(v))}$ native time. `exists_decide_sharp_certificate` additionally charges
binary positivity inspection using the count's proved output/space bound. The real-eta versions
use $\eta(v)=v\log\log v/\sqrt{\log v}$ for $v\ge16$, with rounded versions at every size.
The proved fixed-linear rescaling is from $3v$, retaining one loglog. These are Proposition D.2
(PDF p. 34) and its Corollary 7.4 decision specialization (p. 26), in the existing native
word/resource model. Raw construction/global space are total; graph correctness and sharp time
use canonical matrices. Arbitrary-byte graph admission, succinct declarations, unordered quotients,
a fresh bit-transition simulation and complete witness extraction are separate.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.PerfectMatchingCut`.
The [complete checked client](../../ComplexityTests/PaperEndpoints/PerfectMatchingCut.lean) executes
empty, isolated, edge, path, disjoint-edge, cycle and dense cases, with original labeled selections
and actual written queries. A complete four-vertex graph and a six-cycle have perfect matchings but
no perfect matching cut. Concrete two-vertex examples check both a proper cut and a rejected
one-sided assignment. The direct empty branch bypasses a fake continuation, and 32-vertex query
metadata is computed without partition enumeration. Tiny exhaustive oracles are tests only;
production certificates instantiate the proved sharp counter.

Corollary 7.2's general sigma-rho rules and Theorem 7.3's fixed labeled degree matrices/per-class
bounds remain open. Of the six Corollary 7.4 predicates, independent-domination counting with size
bounds, kernel counting/decision and labeled perfect-matching-cut counting/decision are covered.
The continuations below cover dominating induced matching and signed-threshold Maximum Induced
Matching, its complete optimum/witness recovery, Corollary 7.5's full distribution and Upper
Dominating Set decision. Other predicates' full witness/optimum recovery and Proposition 7.6's
width-three path-marker refinement remains open; exact width-four counting appears below. This concrete bipartition endpoint does not
complete the general partition theorem or ALL-main.

### Dominating induced matchings with exact edge-domination counts

Import `Complexity.Computability.Complexity.FineGrained.DominatingInducedMatching` and open
`Cslib.Logic.PL.DominatingInducedMatching`. Reuse `IndependentDomination.Input`, `encInput` and
`ofGraph G` for the canonical explicit simple-undirected Boolean matrix, with unary vertex
declaration and framed cells. `upper` writes a negative triple for each vertex and distinct
neighbor pair; `conditions` permits an unselected vertex or requires a selected neighbor.
`cover` reuses the original edge-exclusion traversal with flipped literal polarities, requiring
at least one selected endpoint of every edge. `build_polytime` certifies actual traversal,
binary-index writing and all constructed clauses/terms, without enumerating matchings or supports.

The source problem is **efficient edge domination**: a matching edge dominates itself and each
edge sharing either endpoint, and every original edge is dominated exactly once.
`SimpleGraph.Subgraph.IsDominatingInducedMatching` states this directly for a conventional Mathlib
matching and unordered `Sym2` edges. Its proved characterization derives inducedness and edge-cover
support from exact edge domination, and proves the converse. The count bijection
`SimpleGraph.card_dominatingMatching_supports_eq` identifies each valid Boolean support with one
actual matching subgraph. No orientation, label or private certificate is counted. The finite
cardinalities are correctness statements, not enumerations used by the production algorithm.

`regular_semantics` proves that selected vertices induce a Mathlib matching; `finite_semantics`
adds edge cover. `plan_count` connects the **actual written queries** to the number of matching
objects satisfying exact edge domination. For $v\ge1$, `query_count` gives two ordinary queries;
`query_budget` gives $N=2v-1$, width three and at most $v^3+3v^2+2v$ clauses each.
`query_cubic_budget` bounds this by $6v^3$. There are exactly $v$ conditions, with at most
$v(v+1)$ terms in total, and no extra matching-edge variables. The empty graph uses the single
zero-variable empty query and counts the empty matching once. Edgeless graphs likewise have only
the empty matching; isolates must be unselected and add no free-bit multiplicity.

`exists_count_sharp_certificate` composes actual construction, the proved unrestricted-density
counter, sequential query calls/subtraction and reconstruction with global polynomial workspace
and $L^{O(1)}2^{O(\eta(v))}$ native time. Its count is of actual matching subgraphs, including
empty inputs. The decision certificate additionally charges binary positivity using the count's
proved output/space bound. The real-eta versions use
$\eta(v)=v\log\log v/\sqrt{\log v}$ for $v\ge16$; the rounded versions cover all smaller
sizes. Fixed-linear rescaling from $2v$ retains a single loglog. This is Corollary D.4
(PDF p. 36) and its Corollary 7.4 specialization (p. 26). Certificates use the existing native
word/resource model, not a fresh bit-transition simulation. Raw construction/global space are
total; graph correctness/sharp time use canonical simple matrices. Arbitrary-byte admission,
succinct declarations and matching witness extraction are separate.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.DominatingInducedMatching`.
The [complete checked client](../../ComplexityTests/PaperEndpoints/DominatingInducedMatching.lean)
executes empty, isolated, edge, path, disjoint-edge, triangle, star, cycle and dense cases, with
original support selections and actual query metadata. A single edge has one matching, not two
orientations. On a four-vertex path only the middle edge works; two outer edges double-dominate
the middle edge. Actual matching/nonmatching examples check the original predicate. Construction
at 32 vertices writes queries without support enumeration. Exhaustive tiny query oracles are tests
only; production uses the instantiated proved sharp counter.

Corollary 7.2's general sigma-rho rules and Theorem 7.3's fixed degree-matrix frontend remain open.
For Corollary 7.4, independent-domination counting with size bounds is covered, as are count/
decision for kernels, perfect matching cuts and dominating induced matchings.
The continuations below supply signed-threshold Maximum Induced Matching and Upper Dominating
Set decision and their full optimum/witness composition. The other four recovery specializations
remain open.
Corollary 7.5's unrestricted matching bijection, total counts and full size distribution are covered below.
Proposition 7.6's width-three path-marker refinement remains open; its exact width-four and initial set–marking
construction is supplied below. ALL-main remains open.

### Maximum induced matching with a varying binary threshold

Import `Complexity.Computability.Complexity.FineGrained.InducedMatchingInterval` and open
`Cslib.Logic.PL.InducedMatchingInterval.Maximum`. `Input` is the existing canonical simple-graph
matrix frame paired with a signed binary edge threshold. `ofGraph G k` retains the unary vertex
declaration, including isolated vertices. `prepare` computes the natural endpoint interval
`((2*k).toNat, v)` and passes it to the actual degree-one/functional-cardinality construction.
The binary multiplier and sign normalization are certified computations; the cardinality generator
caps oversized thresholds before unary construction. No supplied matching, rank, circuit or
runtime is accepted. This is Proposition D.1 (PDF pp. 33–34), with Corollary 7.4's sharp resources.

`SimpleGraph.Subgraph.IsMatching.card_verts_eq_twice_edges` proves exactly two endpoints per
unordered matching edge. `SimpleGraph.card_inducedMatching_supports_eq` gives a size-preserving
bijection between degree-one Boolean supports and conventional induced matching subgraphs.
Unlike efficient edge domination, the actual `InducedMatchingInterval.build` omits edge-cover
clauses. Isolated vertices cannot be selected. The empty matching is included, and each actual
matching is counted once, without orientations or auxiliary gate multiplicity.
`count_correspondence` connects the computed endpoint interval to at least `k` unordered edges.

`InducedMatchingInterval.query_count` and `query_budget` certify two ordinary width-three queries
for $v\ge1$, on $N=2v+a-1$ variables, where the actual cardinality circuit has
$a\le952(v+1)$ gates. Each query has at most
$v^3+3v^2+2v+2+2856(v+1)$ clauses, and every written literal is in range. `query_cubic_budget` bounds this by $6000v^3$.
`Maximum.exists_count_sharp_certificate` composes preparation, actual construction, sequential
counting and reconstruction with global polynomial workspace and
$L^{O(1)}2^{O(\eta(v))}$ native time. `Maximum.exists_decide_sharp_certificate` additionally
charges binary positivity. Their real-eta versions use
$\eta(v)=v\log\log v/\sqrt{\log v}$ for $v\ge16$; rounded certificates include all smaller
and empty cases. Thresholds are varying signed binary inputs. Nonpositive thresholds count all
induced matchings; impossible thresholds count zero, without exponential threshold decoding.
The resource model remains the existing native word/resource model, with binary encodings,
not a new bit-transition simulation or arbitrary-byte graph admission theorem.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.InducedMatchingInterval`.
The [complete checked client](../../ComplexityTests/PaperEndpoints/InducedMatchingInterval.lean)
executes empty, isolated, single-edge, path, disjoint-edge, triangle, cycle and dense cases.
Two disjoint edges admit a size-two matching; the two outer edges of a four-vertex path do not.
The client checks actual query writing, exact endpoint-size coefficients, and negative/oversized
512-bit thresholds. It computes unique circuit traces for tiny original selections; production
uses the certified sharp counter, never an exhaustive auxiliary cube traversal.

This closes the signed-threshold counting/decision specialization; the continuation below supplies
its optimum value and witness. Threshold zero gives Corollary 7.5's unrestricted total count, using
the functional size circuit rather than that corollary's sharper no-size-test query budget. Witness/optimum extraction for the other graph predicates and
general Corollary 7.2 sigma-rho rules, Theorem 7.3 labeled degree matrices and Proposition 7.6
width-three upper-domination path-marker refinement remains open; its initial decision construction appears
below. These remaining source endpoints keep ALL-main open.

### Returning the optimum value and an actual maximum induced matching

Import `Complexity.Computability.Complexity.FineGrained.InducedMatchingWitness` and open
`Cslib.Logic.PL.InducedMatchingInterval.Maximum`. The original input is just
`IndependentDomination.Input`, encoded by `IndependentDomination.encInput`; the user supplies
neither an optimum value nor a matching. The complete native endpoint is
`Witness.exists_optimalWitness_realEta_certificate` (and its rounded sharp counterpart).
Its `Output` contains a binary edge count and an original-vertex bit word. Read these through
`Witness.value` and `Witness.vertices`, and use `Witness.decode G` to obtain the conventional
Mathlib subgraph. The theorem proves that the word has the original declared length, the decoded
subgraph is both matching and induced, its unordered edge count equals the returned value, and
**every** induced matching has at most that many edges. This is the optimum and witness clause
of Corollary 7.4 / Appendix D.5 (PDF pp. 26, 37), not merely another threshold decision.

`Optimum.run` scans edge thresholds $0,\ldots,v$, keeping the greatest feasible value.
`Optimum.run_optimal` proves attainment and global optimality using the proved two-endpoints-per-
edge bound. This uses $v+1$ tests instead of the paper's logarithmic binary search; it preserves
the stated sharp asymptotic bound. `Witness.run` then inspects the $v$ original vertices. It
writes a restricted graph, isolating a vertex exactly when that restriction still admits the
computed optimum threshold. `Witness.restrict_ofGraph` proves that every written query is the
canonical matrix of the intended simple graph with the same vertex declaration. Because matching
supports cannot contain isolated marks, restriction is equivalent to fixing that original bit
false. The feasibility/forced-bit invariant proves that the **returned** final support is itself
a matching; it does not leave decoding to an existentially chosen extension.

`Witness.solve` composes the actual value and witness passes. The native certificates charge
all threshold calls, repeated restricted-matrix writing, retained original input, every-prefix
live state, and binary value/selection output. They give global polynomial workspace and
$L^{O(1)}2^{O(\eta(v))}$ time on canonical simple graphs, with the same single-loglog
$\eta(v)=v\log\log v/\sqrt{\log v}$ for $v\ge16$. Rounded certificates include all smaller
and empty cases. An empty graph returns zero and the empty word; an edgeless graph returns zero
with every declared vertex unselected. No vertices or artificial positive weights are added.
Raw malformed frames still have a total algorithm and polynomial workspace; graph correctness
and sharp time use the existing canonical promise, not an added validation/admission theorem.
The encoding remains nonsuccinct with a unary declaration, in the existing native resource model.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.InducedMatchingOptimum`.
The [complete computed client](../../ComplexityTests/PaperEndpoints/InducedMatchingOptimum.lean)
checks actual returned values and words for empty/edgeless graphs, an edge, paths, disjoint edges,
a triangle, a dense graph and declared isolates. On a five-vertex path it returns the two outer
edges' four endpoints and clears the middle vertex. The tiny threshold oracle evaluates the
approved real construction on original selections/unique traces; production instantiates the
proved sharp native decider. It is not exhaustive matching search.

The other four graph predicates' full witness/optimum composition remains open, together with
general sigma-rho rules, labeled degree matrices and the width-three Upper Dominating Set
path-marker refinement. The continuation below completes Corollary 7.5's full distribution and sharper no-size-test construction. The other source
clauses keep the paperwide/ALL-main objective open.

### Total induced matching counts and the complete size distribution

Import `Complexity.Computability.Complexity.FineGrained.InducedMatchingDistribution` and open
`Cslib.Logic.PL.InducedMatching`. Reuse the original canonical simple undirected matrix frame,
`IndependentDomination.Input`, `IndependentDomination.encInput` and
`IndependentDomination.ofGraph G`, with its unary declaration and framed Boolean cells. This completes Corollary 7.5 / Appendix D.1 (PDF pp. 26, 34) in that encoding.

For a total count without a size test, `build` writes only the selected-degree-one upper clauses
and selected-neighbor predicates. It adds neither functional size gates nor domination clauses.
`plan_count` proves exact counts of conventional induced matching subgraphs, with no orientations
or isolated marks. For $v\ge1$, `query_count`, `query_budget` and `query_cubic_budget` give two
ordinary width-three queries on exactly $2v-1$ variables and at most $6v^3$ clauses each, with all
literal indices in range. `exists_count_realEta_certificate` supplies the actual total counter,
charging construction, sequential counting and reconstruction with sharp time/global polynomial
workspace. The empty no-size plan has one empty zero-variable query and counts the empty matching.

For the whole size distribution, `Distribution.run` visits exactly the edge indices
$0,\ldots,\lfloor v/2\rfloor$. `Distribution.caseInput` computes both endpoint bounds as twice the edge index
and invokes the approved actual functional equality construction. `Distribution.coefficient_count` proves that
this counts exactly the matchings with that many **unordered edges**. The original graph, current
index and reverse-ordered binary coefficients persist; final `Distribution.output` reverses the actual list.
`Distribution.run_eq_map` proves order and length, including trailing zero coefficients.
Coefficients are at most $2^v$ (`Distribution.coefficient_le_two_pow`), so each takes at most $v+1$ binary bits. The complete
framed output takes at most $(\lfloor v/2\rfloor+1)(2(v+1)+1)$ bits.

`Distribution.exists_distribution_realEta_certificate` states exact output-list correctness,
that binary output bound, actual native time $L^{O(1)}2^{O(\eta(v))}$ and global polynomial
workspace together, where $\eta(v)=v\log\log v/\sqrt{\log v}$ for $v\ge16$.
The rounded certificate includes all smaller/empty graphs. The proof charges every exact-size
call, current-index encoding, retained input, stored coefficient word/framing, accumulation,
reversal and output write. Every reached prefix has a polynomial live-state bound. Previously
stored coefficients are excluded from the next coefficient request; the backend's proved output/
space bound controls intermediate integer bit lengths uniformly in original input and index.
The output-size bound is separate from this actual runtime proof. The native resource model is
unchanged, and graph correctness/sharp time still use the canonical promise. Global polynomial
workspace holds even for malformed raw frames; a new arbitrary-byte validator or succinct
vertex declaration is not asserted. The empty graph's complete list is `[1]`, not an empty list.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.InducedMatchingDistribution`.
The [complete computed client](../../ComplexityTests/PaperEndpoints/InducedMatchingDistribution.lean)
checks total-query execution and full lists on empty/edgeless/edge/path/disjoint-edge/triangle/
dense/isolate/cycle instances. It retains infeasible-size zeros and checks total counts against
coefficient sums. A 32-vertex query construction has 63 variables per query without any size gates;
that construction test enumerates neither selections nor matchings. Tiny query/trace oracles are
tests only; production certificates instantiate the approved unrestricted-density native counter.

General sigma-rho rules, labeled degree matrices, the width-three Upper Dominating Set refinement
and four other graph predicates' full witness/optimum composition remain open. Corollary 7.5 is
covered under the stated encoding; that milestone does not close the paperwide/ALL-main objective or alternative admission/
succinct-encoding transfers.

### Upper domination through private-neighbor markings

Import `Complexity.Computability.Complexity.FineGrained.UpperDomination`.
This implements the width-three construction of STOC1575 Proposition 7.6, PDF p.27 and
Appendix D.3 pp.34–35. The original input is an explicitly framed graph with unary declared
vertex count and a varying signed binary threshold. For a canonical simple graph $G$ on $v$
vertices, `exists_decide_realEta_certificate` decides whether an inclusion-minimal dominating
set has at least $k$ vertices. Minimal means inclusion-minimal, not minimum cardinality.
The foundation `SimpleGraph.minimal_dominatingSet_iff` characterizes these sets by a private
closed neighbor for every selected vertex.

The actual constructor adds $v$ marking bits after the $v+a$ functional cardinality wires.
Domination, at most one selected closed neighbor per marked vertex, and a marked closed neighbor
for each selected vertex are written explicitly. The signed threshold is capped before unary
cardinality construction; no rank, reduction, desired runtime or witness is input advice.
`FunctionalCNF.count_extensions_appended` preserves these free marking bits while eliminating
the unique gate trace. For positive $v$, the constructor yields two width-three CNF queries on
exactly $4v+a-1$ variables, with at most $6000v^3$ clauses and $a\le952(v+1)$.

`exists_count_sharp_certificate` counts **set–marking pairs**. An edge has two minimal dominating
sets but six valid pairs, so this is deliberately not an exact unmarked-set count. Positivity
is exactly the original Upper Dominating Set decision predicate. The complete native count and
decision machines charge binary threshold processing, query writing, sequential sharp counting,
reconstruction and the positivity test. They have time $C(L+1)^e2^{A\eta(v)}$, where
$\eta(v)=v\log_2\log_2 v/\sqrt{\log_2 v}$ for $v\ge16$, and polynomial peak workspace.
The rounded certificate includes every smaller size. Global workspace is proved on all raw
frames; correctness and sharp graph time use the canonical simple-graph promise. This retains
the existing native word-cost model and is not a new simulation by binary Turing transitions.
Unused declared vertices are retained. The empty graph accepts exactly $k\le0$.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.UpperDomination`.
The [computed client](../../ComplexityTests/PaperEndpoints/UpperDomination.lean) covers empty and
edgeless graphs, paths, cycles, complete graphs, adjacent selected vertices, pair multiplicity,
512-bit positive/negative thresholds, actual query metadata and the real-eta decision certificate.
Its tiny assignment enumeration is a test oracle; the production machine uses the sharp counter.

This completes Proposition 7.6's initial width-three decision construction and Corollary 7.4's
Upper Dominating Set decision specialization for the stated encoding. The unique-mark width-four
original-set counter on $5v+a-1$ query variables appears below. The width-three path-marker
refinement on at most $6v+a-1$ variables remains open. Upper-domination optimum-value and actual witness extraction are supplied below.
All six Corollary 7.4 decision predicates are now covered in their recorded explicit models;
Maximum Induced Matching and Upper Domination have full optimum/witness composition, as
described below; the other four recovery specializations remain open. General Corollary 7.2
finite/cofinite degree rules, Theorem 7.3 labeled degree partitions, alternative admission/succinct
encodings and the paper-wide independent audit remain outstanding. These limits keep ALL-main open.

### Compute the upper-domination optimum value

Import `Complexity.Computability.Complexity.FineGrained.UpperDominationOptimum`.
Corollary 7.4 and Appendix D.5, PDF pp.26,37, explicitly claim optimum-threshold and witness
recovery. `UpperDomination.Optimum.run` computes the value using the existing original-graph
threshold iterator, instantiated with the actual Upper Dominating Set decider. It makes $v+1$
tests from zero through $v$, retaining only the graph, next threshold and best feasible value.
This polynomial scan replaces the source's binary search and preserves the same asymptotic bound.
It enumerates neither vertex sets nor private-neighbor markings.

`run_optimal` proves that the computed value is attained by an inclusion-minimal dominating set
and is at least every such set's cardinality. Every finite graph has a minimal dominating set,
including the empty graph; thus the initial zero threshold is valid without input advice.
The output is the maximum cardinality of an inclusion-minimal set, not the minimum dominating-set
size and not the number of markings. `exists_optimum_realEta_certificate` instantiates the proved
native decider, charging threshold writes, every loop update, binary output and intermediate live
state. It gives time $C(L+1)^e2^{A\eta(v)}$ for $v\ge16$ and global polynomial peak workspace;
the rounded certificate covers every smaller size. Every-prefix graph-state encodings have length
at most $5(L+1)$, and the loop uses maximum round workspace rather than multiplying space by
its time. The same canonical graph/unary-declaration/native word-cost conventions apply as above.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.UpperDominationOptimum`.
The [computed client](../../ComplexityTests/PaperEndpoints/UpperDominationOptimum.lean) covers empty
graphs, declared isolates, edges, paths, stars, cycles and complete graphs. A three-vertex path
returns two, although a singleton dominates it; an edge returns one despite six valid marking
pairs. It checks acceptance at the returned threshold and rejection at the next threshold.

The value theorem asserts existential attainment. The following endpoint separately returns the
attaining original set; it does not replace witness output by that existential statement.

### Return an actual maximum minimal dominating set

Import `Complexity.Computability.Complexity.FineGrained.UpperDominationWitness`.
`UpperDomination.Witness.solve` computes the approved optimum value, recovers a satisfying word
of the actual selection/gate/mark formula by unit-clause self-reduction, then returns exactly the
original $v$ selection bits with the binary value. `selected` decodes those bits to an ordinary
vertex set. `exists_optimalWitness_realEta_certificate` proves that this returned set is itself
inclusion-minimal dominating, its cardinality equals the output value, and every inclusion-minimal
dominating set has at most that cardinality. Empty graphs return `(0, [])`; original isolates stay
selected. No attaining set, optimum, rank or desired runtime is supplied as input advice.

The reusable `TwoBoundary.BinaryFrontend.Witness.run` retains an original explicit CNF/DNF
input and a fixed Boolean prefix. It tries the next bit false by appending actual unit clauses;
if that trial has no satisfying extension it fixes the bit true. Its invariant preserves a real
extension, and its final complete declared word satisfies the original formula. The actual
sharp counter is instantiated in `exists_recovery_sharp_certificate`, with explicit unit-writing,
branching, every-prefix state lengths, sequential counter calls and output charges. Trial prefixes
are capped at the declared length, including the terminal state charged by the resource calculus.
This does not assume an unimplemented oracle. For this graph construction all $2v+a$ wires are
fixed, including gates and private marks, then discarded except for the original prefix. Since
$a\le952(v+1)$, this still makes $O(v)$ feasibility calls. Appendix D.5 permits leaving markings
unfixed; fixing them as well preserves its bound and avoids a separate conditional count bridge.

`model_sound` checks the actual recovered formula word pointwise: functional gate acceptance
yields the cardinality bound, and the original private-neighbor constraints yield inclusion
minimality. The full algorithm charges normalization/writing, the optimum scan, recovery,
intermediate encodings, binary value and prefix trimming/output. Time is
$C(L+1)^e2^{A\eta(v)}$ for $v\ge16$, with rounded bounds for all smaller sizes and global polynomial
peak workspace. It retains the explicit canonical simple-graph promise, unary declaration and
native charged-word model. No new malformed-input admission, succinct declaration or binary
Turing-transition realization is claimed. The recovery theorem requires feasibility; the complete
optimizer proves that feasibility at its computed optimum, including the empty graph.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.UpperDominationWitness`.
The [complete computed client](../../ComplexityTests/PaperEndpoints/UpperDominationWitness.lean)
checks actual returned words on empty/isolated/edge/path/star/triangle/cycle graphs. It independently
checks domination, private neighbors, bit count and output value on representative outputs.
A four-cycle returns an adjacent selected pair, illustrating that independence is not required.
A generic CNF/DNF client also retains a declared unused variable. Tiny trace enumeration is a test
oracle; production uses the proved sharp counter and never enumerates a vertex-set or gate cube.

This completes Upper Domination's Corollary 7.4 optimum/witness clause for the recorded encoding.
The other four non-MIM/Upper graph predicates still need their recovery specializations. General
Corollary 7.2 finite/cofinite degree rules, Theorem 7.3 labeled degree partitions, Proposition 7.6's
width-three path-marker refinement, alternative encodings/admission and the independent paperwide
audit remain open. The initial pair counter is still not an exact unmarked-set counter. ALL-main
is not completed by this witness endpoint.

### Count original minimal dominating sets with unique marks

Import `Complexity.Computability.Complexity.FineGrained.UpperDominationUnique`.
This implements Proposition 7.6 / Appendix D.3, PDF pp.27,35, augmented exact counting. The input
is the same explicit canonical simple-graph frame and varying signed binary lower size threshold.
`UpperDomination.Unique.complete` writes one extra DNF predicate per original vertex: the mark is
true, or two distinct selected closed neighbors exist. Pair terms reuse original selection wires;
ordered pair enumeration may repeat terms but introduces neither variables nor counted choices.
`Unique.build` retains the reviewed gate/mark wires and side clauses, adding these actual predicates.

`SimpleGraph.completePrivateMarking_iff` proves the augmented predicate equivalent to ordinary
inclusion-minimal domination together with the canonical marking of **all** private closed
neighbors. `card_completePrivateMarking` is an explicit forgetful bijection. The actual functional
gate/mark representation and `Unique.exists_count_realEta_certificate` therefore count original
sets exactly once, not set–marking pairs. For an edge this gives two rather than six; for a
triangle it gives three rather than twenty-one. Negative thresholds count all minimal sets;
thresholds above the declaration give zero. Empty graphs contribute one exactly when $k\le0$.

For positive $v$, `Unique.query_count`, `query_budget` and `query_cubic_budget` prove exactly two
ordinary width-four queries on $5v+a-1$ variables, with valid indices and at most $6000v^3$ clauses
each. The actual generated cardinality circuit satisfies $a\le952(v+1)$. Binary polynomial
construction includes every pair/term/literal write. The complete counter charges writing,
sequential unrestricted-density width-four counting, reconstruction and binary output, with
$C(L+1)^e2^{A\eta(v)}$ time for $v\ge16$ and global polynomial peak workspace. Rounded bounds
cover all smaller sizes; fixed-linear rescaling uses the actual $5v+a$ dimension, without dropping
an extra loglog factor. The existing unary declaration, canonical graph promise and native
charged-word model apply. This adds no malformed-byte admission or succinct/binary-transition
simulation claim and does not change the reviewed width-three decision/witness algorithms.

From the checkout root run `scripts/build.sh ComplexityTests.PaperEndpoints.UpperDominationUnique`.
The [complete computed client](../../ComplexityTests/PaperEndpoints/UpperDominationUnique.lean)
checks empty graphs, isolates, edges, paths, cycles, cliques, an edge with an isolate, 512-bit
thresholds, the marking/count distinction and actual width/dimension/size metadata. Positive and
negative conventional marking instances ensure completeness is not vacuous. Tiny trace-based
selection/mark enumeration is test-only; production uses the certified sharp counter.

This closes the augmented width-four exact-set clause. The source's optional shared path-marker
width-three construction on at most $6v+a-1$ variables is still open; ordinary clause splitting
would add too many variables. General degree rules/partitions, four other recovery specializations,
the indexed Exact Cover encoded-transposition composition and the remaining explicit inventory
stay open. The semantic `coverScopes_iff` alone is not that encoded frontend/resource theorem.
This does not complete ALL-main or the independent paperwide audit.

## Known Limitations

The conditional statements, truth-table scales and source-specific quantitative scope were inspected, but the complete magnification and cryptographic reduction proofs were not independently reconstructed in this worker pass. Distinguish a valid conditional theorem, a conventional open assumption, and a premise that this same library proves false elsewhere.

[complexitylib]: ../sources.md#complexitylib
[impagliazzowigderson97]: ../sources.md#impagliazzowigderson97
[nisanwigderson94]: ../sources.md#nisanwigderson94
[sudantrevisanvadhan01]: ../sources.md#sudantrevisanvadhan01

### Weighted signed row semantics

Import `Complexity.Logics.Propositional.CNF.WeightedRow` and open
`Cslib.Logic.PL.WeightedRow`. `Row V d` represents distinct variables with fixed
polarities, positive natural weights, demand at most `d`, and weights capped at
`demand + 1`. `Row.value` sums the weights of true row literals. For equations
(24)–(25) of Theorem 7.1 (submission 1575, PDF pp. 23–24), `Row.upper` constructs
negated-literal clauses for small overweight subsets and `Row.attainment`
constructs exact-weight terms. `upper_eval`, `attainment_eval` and `row_eval`
provide their assignment semantics. Zero demand includes the empty true term;
an unattainable demand produces an empty false DNF.

`upper_width`, `attainment_width`, `upper_length` and `attainment_length` give
per-row width and binomial size bounds. `query`, `counting_identity` and
`query_width` reuse the existing two-boundary construction for a nonempty indexed
family of rows, obtaining exact counts and width at most `d + 2`.
[The complete checked client](../../ComplexityTests/WeightedRow.lean) exercises
weights 2 and 1, both polarities, overweight rejection, zero demand, unattainable
demand and the counting wrapper. It can be checked from the repository root with
`scripts/build.sh ComplexityTests.WeightedRow` after the usual setup.

This is row-local progress, not the full Theorem 7.1 reduction. Subset listing
uses noncomputable `Finset.toList`; no executable enumeration or runtime theorem
is supplied. The wrapper concatenates upper bounds without global deduplication.
The subsequent modules below supply normalization, capped affine row selection
and global signed clause counting. All direct branches and full
construction/counting time and space remain open.
Graph endpoints are unaffected.

Import `Complexity.Logics.Propositional.CNF.WeightedNormalization` for original
occurrence-indexed rows. `Occurrences r m` accepts repeated variables, both signs,
positive natural weights and an integer target. `normalize` aggregates each sign,
extracts the common constant, rejects targets outside the residual interval,
complements when that gives a smaller demand, drops constant-true rows, and caps
remaining weights at demand plus one. Its only bound argument is that the computed
normalized demand is at most `d`; it does not assume normalization correctness.
`normalize_iff` and `normalize_count` prove exact assignment and count preservation.
`toRow_iff` and `formula_iff` connect valid rows to the reviewed weighted formulas.
The original declared variable type is retained throughout, including unused bits.

[The complete normalization client](../../ComplexityTests/WeightedNormalization.lean)
checks repeated positive occurrences, both polarities, complementation, capping,
negative and overlarge targets, zero demand and deletion of a constant row. From
the repository root, run `scripts/build.sh ComplexityTests.WeightedNormalization`.
This normalization has no encoded runtime certificate. Subsequent rank selection
must use its **capped** affine system; the original coefficient matrix can have a
different rank. The all-cases mathematical plan is available below; composed runtime/space remain unproved.

Import `Complexity.Logics.Propositional.CNF.WeightedGlobal` to deduplicate the
upper clauses across every retained row. `upperKeys` identifies clauses by finite
sets of signed literals, so literal order and source row do not affect identity.
`globalBase_upper_eval` proves all upper bounds; `global_counting_identity` and
`globalQuery_width` use the existing TwoBoundary queries and width `d + 2`.
`globalQuery_polynomial` gives an explicit polynomial bound: the base contributes
`(d + 2) * (2 * n + 1)^(d + 1)`, and the attainment terms contribute at most
`2 * (h + 1) * (d + 1) * (n + 1)^d`, where `n` counts declared variables and
`h + 1` counts rows. Thus at most `n` rows gives degree `d + 1`, without an
extra row factor on the upper clauses. This is a noncomputable finite listing;
the affine module below supplies capped-rank row selection separately, while
encoded construction time remains open.
[The complete global client](../../ComplexityTests/WeightedGlobal.lean) checks
cross-row duplicates, accepted/rejected assignments, count recovery and the
normalization connection. From the repository root run
`scripts/build.sh ComplexityTests.WeightedGlobal`.


Import `Complexity.Logics.Propositional.CNF.WeightedAffine` for the actual capped
integer affine conversion. `Row.coefficients` lists signed weights in declared
variable order, with zero outside support; `Row.rhs` subtracts the negative-literal
constant. `Row.affine_iff` preserves each Boolean assignment. `cappedRows` deletes
true rows, while `cappedRows_iff` requires that no rejected row was present.
`cappedMatrix` and `cappedRhs` materialize these rows for the existing rectangular
solver. `selectedCappedRow_iff` pulls its computed indices back to actual capped
rows under the computed rational consistency test. No basis is supplied by the caller.
The [complete affine client](../../ComplexityTests/WeightedAffine.lean) checks mixed
weights and signs, an unused variable, rejection, and the empty zero equation.
From the repository root run `scripts/build.sh ComplexityTests.WeightedAffine`.
This bridge does not assemble all direct branches or certify the full reduction's
runtime, space or graph endpoints.


Import `Complexity.Logics.Propositional.CNF.WeightedCounting` for the all-cases
mathematical assembler. `originalCountingPlan R hd` takes actual occurrence rows
and bounds on their computed normalized demands, normalizes them, and returns a
`CountingPlan` with exact count recovery on every declared variable. No rank,
basis or consistency advice is required. `countingPlan` also accepts an already
normalized list. It enumerates dimension at most one directly, returns zero on
rejection or inconsistency, returns `2^n` for empty or consistent rank-zero
systems, and tests the unique rational candidate for Booleanity at full rank.
Only positive deficient rank produces two ordinary CNFs, using actual selected
capped rows. Each query has at most `2*n-2` variables, width `d+2`, and at most
`countingBudget n d` clauses, a degree `d+1` polynomial for fixed `d`.
This is a noncomputable mathematical plan, with no composed encoded runtime or
space guarantee. Theorem 7.1 and the graph endpoints remain incomplete.
The [counting client](../../ComplexityTests/WeightedCounting.lean) exercises the
original-input entry point and the direct and query interfaces. From the
repository root run `scripts/build.sh ComplexityTests.WeightedCounting`.

For executable bounded subset enumeration on `Fin n`, import
`Complexity.Logics.Propositional.CNF.WeightedExecutable`. `boundedLists` visits
only the requested lengths using `List.sublistsLen`; its exact binomial count and
`boundedLists_polynomial` bound include empty inputs. `upperList` and
`attainmentList` write signed clauses and terms from the canonical support order.
`executableQuery` deduplicates upper clauses globally and invokes the existing
boundary writer. `executableQuery_eval` proves pointwise agreement with
`globalQuery`, and `executable_counting_identity` transfers exact full-variable
count recovery. Width is at most `d+2`; the row candidate budgets are polynomial
for fixed `d`. Run `scripts/build.sh ComplexityTests.WeightedExecutable` from the
repository root to check concrete mixed-sign, overweight, duplicate-row and
boundary-query examples. These row/query writers are used by the executable
all-cases assembler below.
Candidate and output bounds alone are not runtime certificates.


Import `Complexity.Logics.Propositional.CNF.WeightedExecution` to execute the
complete original-input dispatcher. `executableOriginalCountingPlan R hd` takes
finite occurrence rows and a bound on their computed normalized demands. It
computes aggregation, constant extraction, interval rejection, complementation,
capping, the integer affine system, Gram row selection, consistency and rational
candidate Booleanity. Only declared dimension at most one enumerates assignments.
Other direct branches return zero, one or `2^n` from the computed tests; positive
deficient rank writes the two queries on selected actual capped rows.

The returned `CountingPlan` certifies exact counting on every declared variable,
at most `2*n-2` query variables, width `d+2` and `countingBudget n d` clauses.
`executableBase_keys_injective` proves that canonical signed lists deduplicate
as signed finite sets, recovering the sharp global polynomial clause budget.
`executableOriginalCountingPlan_count` proves agreement with the reviewed
mathematical plan's count; query ordering may differ. No rank, basis, consistency,
output or runtime conclusion is supplied by the caller. The API also handles
`d=0`, beyond the source's stated `d>=1` scope.

From the repository root run `scripts/build.sh ComplexityTests.WeightedExecution`.
The [complete client](../../ComplexityTests/WeightedExecution.lean) checks actual
returned constructors and direct answers, full-rank Boolean and fractional
candidates, inconsistency, duplicate partial-rank rows, repeated opposite
polarities, empty input and rank zero. A test-only exhaustive oracle checks
small emitted queries; it is not used by the dispatcher.

This stage proves correctness and output budgets. The later `WeightedRaggedResources`
continuation composes its binary cost with actual counting and supplies a parsed ragged-input
adapter. Table construction and graph endpoints remain separate.


Import `Complexity.Computability.PolyTime.CNF.WeightedNormalization` for the
certified binary normalizer/backend stage in namespace
`Cslib.Logic.PL.WeightedRow.BinaryNormalization`. `Input` stores an explicit list
of `(variable, sign, integer weight)` occurrences and a signed integer target.
`encInput` frames unary variable indices and binary integer weights/targets;
the outer input uses unary declared width and a framed list of rows.
`ofOccurrences` serializes the reviewed positive-weight finite input directly.
The total raw program also runs on malformed lists; semantic correspondence is
proved for serialized `Occurrences`, not for an unvalidated parser.

`materialize n rows` computes normalization/capping and writes the retained
affine matrix and RHS. `analyze n rows` additionally emits the separate rejection
flag, computed original-row basis indices, consistency and full-rank candidate
Booleanity. The last flag is false at deficient rank and does not decide
feasibility there. Rejection must be respected even if the matrix after deleting
invalid rows is consistent. `materialize_ofOccurrences` and
`analyze_ofOccurrences` prove exact correspondence with the actual normalized
tables and solver tests used by the executable dispatcher.

`materialize_polytime` and `analyze_polytime` compose plain multitape binary
polynomial-time certificates, including actual list writing, binary sums,
comparisons, Gram/Bird selection and rectangular recovery. These certificates
also supply polynomial space for this stage through the library's independent
time/space predicate. They are uniform in width, row count and binary weight
magnitudes; normalization alone needs no fixed-demand assumption.
`aggregate_prefix_bits` bounds uncapped partial sums by actual input length.
The post-cap entry/RHS bounds, `original_gram_stage_bits` and
`original_certificate_bits` derive the backend widths from demand and declared
width without supplied coefficient-growth advice.
`materialize_output_polyBounded` derives storage from the proved runtime, not
runtime from output size.

From the repository root run `scripts/build.sh ComplexityTests.WeightedBinaryNormalization`.
The [complete client](../../ComplexityTests/WeightedBinaryNormalization.lean) checks
repeated opposite signs, a `2^80` coefficient, deleted true rows, rejection,
inconsistency, unused variables and Boolean/fractional full-rank recovery.
The complete tagged continuation below now composes this stage with direct
answers and query writing. Advertised counting runtime, full table frontend
and graph endpoints remain open; Theorem 7.1 and ALL-main remain incomplete.


Import `Complexity.Computability.PolyTime.CNF.WeightedQuery` for the certified
selected-query branch, in namespace `Cslib.Logic.PL.WeightedRow.BinaryQuery`.
`RowData` stores canonical signed variable/weight entries and a binary demand;
`encRow`, `encLiteral` and `encCNF` frame unary variable indices, polarity bits
and binary integer data. `boundedAt` chooses the actual bounded enumeration
from a fixed cap and binary demand. Its fallback on an out-of-cap parameter is
length zero; correctness is asserted on the original normalized-demand domain.

`upper_polytime`, `attainment_polytime`, `base_polytime` and `query_polytime`
charge bounded candidate traversal, binary weight tests, signed literal writing,
encoded clause equality scans, global deduplication and boundary CNF writing.
The generic `sublistsLen_polytime` and `dedup_polytime` certificates use suffix
scans proved equal to the existing lists, including their order. The induction
is on the fixed selected length; no full powerset or input-sized exponent is
used. The existing combinatorial candidate bound is retained separately from
this instruction-cost argument.

`selectedQuery d n rows beta` computes the actual retained normalized rows and
Gram-selected original indices before writing the query.
`selectedQuery_polytime` composes the approved binary normalizer/backend with
the new writer: a plain finite-state binary multitape machine has polynomial
time and stage space in the complete encoded input length for every fixed `d`.
No normalized rows, basis, candidate budget or desired runtime is advice.
`originalQueryStage_polytime` certifies one composed machine returning all
backend diagnostics and both CNFs together, charging their simultaneous
workspace and writes.
`selectedRows_ofOccurrences` and `selectedQuery_ofOccurrences` connect the result
to the actual reviewed selected capped rows. `query_ofRows` proves exact query
list equality after injectively flattening original/path indices; sharp clause
and width bounds transfer. All declared variables are still counted, including
unused ones. The query branch applies only where the dispatcher has computed
positive deficient rank and consistency; unconditional execution of this stage
is not a replacement for the direct branches.

`candidate_prefix_bits` bounds candidate-weight partial sums by the actual
framed row input. Written indices fit the declared original/path interval; all
index arithmetic is certified unary arithmetic. The approved backend supplies
its integer-growth bounds. `selectedQuery_output_polyBounded` derives storage
from the actual machine-time certificate. This is polynomial stage workspace
through the independent time/space predicate, not a numerical peak-space
polynomial or a complete counting-algorithm space theorem.

From the repository root run `scripts/build.sh ComplexityTests.WeightedBinaryQuery`.
The [complete client](../../ComplexityTests/WeightedBinaryQuery.lean) checks exact
sublist/dedup order, duplicate and unattainable rows, all boundary cases, actual
query counts on declared bits, computed original-row selection, repeated opposite
occurrences and a `2^80` coefficient. Test-only exhaustive counting is absent
from the implementation. The complete tagged continuation below resolves the
remaining construction branches. The native continuation below supplies sharper counting time
on dependent occurrence families; the parsed ragged adapter follows below. Table/graph endpoints
remain open.


Import `Complexity.Computability.PolyTime.CNF.WeightedPlan` for the complete
binary construction, in namespace `Cslib.Logic.PL.WeightedRow.BinaryPlan`.
`compile d n rows` consumes original occurrence records and returns `Output`:
a tagged binary natural answer, or a declared variable count and the false/true
ordinary CNFs. `encOutput` includes the tag, unary declaration and literal indices,
binary direct answer and framed formula lists. The fixed demand cap `d` is not
part of the varying input.

`compile_polytime` certifies one plain binary multitape machine for this actual
output, with polynomial time and independent polynomial space in the complete
encoded input length. It composes computed normalization/backend diagnostics,
branch tests, selected query writing and output serialization. It receives no
basis, rank, answer or resource bound as advice. At width zero it scans the
single assignment; at width one it scans the two constant assignments. Larger
widths use computed rejection, empty-matrix, consistency, full-rank Booleanity
and rank-zero tests before the positive deficient-rank query branch. The direct
`2^n` answer uses certified binary exponentiation with unary exponent; it does
not enumerate assignments. `compile_direct_bits` bounds direct answer bits by
`n+1` on serialized original inputs.

`compile_original` proves exact equality with serialization of the reviewed
executable original-input all-cases plan. `compile_count` proves exact recovery
of the original equation count, interpreting the query output as the difference
of its two model counts. Those counts range over every declared variable,
including unused variables. `compile_withinBudget` transfers the variable bound
`2n-2`, sharp clause budget, width `d+2` and literal-index bounds to the actual
output. `compile_output_polyBounded` derives encoded output storage from the
machine certificate. Correctness uses `R : Fin t → Occurrences n m`: positive
weights and a common occurrence count `m` across all rows, with bounded normalized
demands. Arbitrary variable-length raw rows are not covered by this semantic
bridge. Total execution on raw lists does not certify their parser or semantics.

From the repository root run `scripts/build.sh ComplexityTests.WeightedBinaryPlan`.
The [complete client](../../ComplexityTests/WeightedBinaryPlan.lean) checks zero/one
variables, no rows, rejection, inconsistency, Boolean/fractional full rank,
positive deficient rank, duplicate constraints, large binary coefficients and a
binary `2^80` direct answer. Exhaustive counting appears only in tiny test oracles.

This completes binary time/space certification of tagged plan construction,
including simultaneous intermediate workspace and actual output writes. Construction stops
before counting. The native continuation below now supplies polynomial space and sharper time
on dependent occurrence families, with the parsed ragged adapter below. Table/graph endpoints
and ALL-main remain incomplete.


Import `Complexity.Computability.Complexity.FineGrained.WeightedCountingPlan`
for whole-algorithm polynomial-space counting in the same `BinaryPlan` namespace.
`counterInput beta p` reads the actual tagged output and selects its declaration
and formula; its certificate includes conversion from the writer's unary indices
to the native CNF counter's binary indices. `execute counter p` reads the tag,
returns a direct answer without counting, or evaluates both declared queries and
subtracts their answers in binary. `queryCount_eq_modelCountOn` connects the
finite declared-assignment semantics to the native counter, including unused bits.
`counterInput_valid` derives the width/index guard from the plan's actual budget.

`exists_count_polySpace d` obtains a native fixed-width counter from the proved
library endpoint, then composes the actual original-input compiler, query calls
and reconstruction. Its conclusion is an existential exact counter in plain
`ComputableInPolySpace`, not a caller-supplied counting oracle. Workspace charges
include retained queries, both answers, binary reconstruction and output. The
same hypotheses govern exact counting: positive weights, a common occurrence
count `m` and bounded normalized demands. They do not serve as rank, basis, output
or resource advice. All direct
and query branches are covered by the previously proved original-plan equality.

From the repository root run `scripts/build.sh ComplexityTests.WeightedCountingPlan`.
The [complete client](../../ComplexityTests/WeightedCountingPlan.lean) checks tag
selection, large direct answers, unused declared bits, both boundary counts,
contradictory rows and a nonzero instance of the existential native machine.
The tiny exhaustive counter in this client is test-only.

Import `Complexity.Computability.Complexity.FineGrained.WeightedCountingResources`
for the actual sharper execution certificate. `exists_count_sharp_certificate d` constructs
one native implementation of the tagged compiler, direct-tag readback, sequential false/true
CNF calls and binary subtraction. It has global polynomial workspace on typed raw records.
On `R : Fin t → Occurrences n m` with every computed demand at most fixed $d$, it returns the
original assignment count and has time
$$
C(L+1)^e2^{A\,\texttt{Nat.logLogSqrtLogScale}(n)}.
$$
The constants and machine precede all inputs. Weights, targets, answers and subtraction are binary;
$L$ includes the original unary declaration/indices and all binary occurrence data. Both retained
answers, intermediate query encodings and output writing are charged. Actual direct tags make no
counting calls, covering small dimensions and computed rejection/rank-zero/full-rank answers.

`exists_count_real_sharp_certificate d` gives the same original count and global polynomial space,
with exponent $6A\eta(n)$ when $n\ge16$. The proof uses the actual compiler's `2n-2` variable
budget and proved fixed-linear scale comparison for both queries. A fixed additive exponent
handles all smaller query dimensions; no extra loglog factor or faster-oracle assumption is used.
The older `exists_count_polySpace` API now selects this sharper general-density counter too.

From the repository root run `scripts/build.sh ComplexityTests.WeightedCountingResources`.
The [complete client](../../ComplexityTests/WeightedCountingResources.lean) couples one actual
machine with repeated-occurrence partial-rank queries, fractional full-rank rejection, a $2^{80}$
coefficient, unused variables, an 81-bit direct answer, and real resource bounds for declared
empty systems at arbitrary size. These APIs now allow each row its own occurrence length.
The actual parsed arbitrary-row frontend follows.

Import `Complexity.Computability.Complexity.FineGrained.WeightedRaggedResources`, namespace
`Cslib.Logic.PL.WeightedRow.BinaryRagged`. `Input` is the declared size paired with a list of
rows; each row is a list of `(index, polarity, weight)` occurrences and a signed target.
`encInput` uses a unary declaration and framed ragged lists, binary indices, and signed binary
weights/targets. The unary declaration accounts for unused declared variables in the input size;
it must not be replaced by a succinct binary declaration without revisiting the resource claim.
`parse_eq_some_iff` accepts exactly canonical encodings, including canonical signed integers.

`admit d` computes declaration/strict-positive-weight checks and normalized minimized demands.
Signed targets and empty rows are retained. Contradictory intervals have truncated demand zero
and are rejected by the existing compiler. `recode` caps binary indices at the declaration before
unary conversion, has a polynomial machine certificate even on invalid inputs, and is the
identity on admitted inputs. `admitted_refinement` converts each checked list into its own exact
finite occurrence type; no padding, zero-weight literals, fresh variables or supplied backend
data occur. `compile_admitted_budget` transfers the actual two-query/width/variable/clause budget.

`exists_countWords_sharp_certificate d` constructs one framed-word counting algorithm and native
certificate. It proves global polynomial workspace, time $C(L+1)^e2^{A\eta_{\mathrm{rounded}}(n)}$,
exact original assignment counts on admitted encodings, and zero on malformed/rejected inputs.
`exists_countWords_real_sharp_certificate d` gives $C(L+1)^e2^{A\eta(n)}$ for $n\ge16$;
constants depend only on fixed $d$. Parsing/canonicality, admission, integer growth, normalization,
query writing, both counting calls and binary reconstruction/output are charged by composed
machine certificates, rather than inferred from output length. All declared assignments are
counted, including unused variables; small sizes use the rounded theorem's actual direct paths.
This supplies Theorem 7.1's weighted-row frontend and counting resources for this explicit encoding.

From the repository root run `scripts/build.sh ComplexityTests.WeightedRagged`.
The [complete client](../../ComplexityTests/WeightedRagged.lean) couples one actual machine with
rows of lengths 0, 1 and 3, repeated mixed polarities, an 81-bit coefficient, an unused variable,
empty contradictions, zero-variable systems, invalid large indices/nonpositive coefficients and
malformed words. Table closure/equation/separator/overlap resources, graph endpoints and ALL-main
remain open.


Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryBounds`
for a resource link in the sharper counter, in namespace
`Cslib.Circuits.Frontier.IncidenceNetwork`. This is the construction of Lemma D.2
of [the counter manuscript](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf),
PDF pp. 54–56, rather than a tighter estimate for the old interpolation schedule.

`descInc_rowVertex` and `descInc_le` bound the exponent of the actual streaming
row-entry machine by incidences in one quarter-root test group, including dead
arrays and padding. `exists_groupInc_le` proves this number is eventually at most
`ceilNineTenths (sizeParam n)`, where `sizeParam n` is
`n * Nat.clog 2 (Nat.clog 2 n)`. The scopes and per-variable incidence counts must
be bounded by a fixed power of `Nat.clog 2 n`, and the number of tests by a fixed
multiple of `n`.

`exists_entry_admissible` combines these bounds with the existing graph shape,
actual entry certificate and encoded descriptor sizes. It charges entry time,
workspace and output without expanding tensor tables. `exists_contraction_bound`
then instantiates `CountingSimulation.truncEntryContractionAlgorithm incCertificate`
at precision and truncation order `n+1`: its actual time is bounded by
`A * (L+1)^A * 2^(A*s / Nat.sqrt (Nat.log 2 s))` and space by `A*(L+1)^A`, for
`s = sizeParam n` and the actual encoded network input length `L`.
Constants and an exceptional-size threshold are chosen before the instance.
`exists_sparseBranch_contraction_bound` accepts the existing `IsSparseBranch`
contract and computes the source degree cap `k*(sys.length+2*n)` itself. It does
not take an entry-time bound, contraction oracle or chosen answer as advice.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceEntryBounds`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceEntryBounds.lean)
checks row/column/dead/padding incidence counts and actual admissible padded
networks at all sufficiently large sizes.

This establishes one constructed network's native contraction resources at the
smaller size `n*ceil(log₂ ceil(log₂ n))`. It does not sum degree arrays or
high-incidence branches, prove their full count reconstruction, or assemble the
parity queries and general-density counter. Those steps and final weighted-plan
time composition remain open. Weighted correctness still requires the typed
rows to share a common occurrence count `m`; arbitrary variable-length raw rows,
tables and graphs remain material gaps. No Theorem 7.1 or ALL-main completion follows.


Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceEntryCorrectness`
for the semantics of the actual entry-extraction program, in the same
`IncidenceNetwork` namespace. `val_factorCoeffs` proves that the binary residue
list represents the integer parity factor in the truncated ring, including its
negative coefficients and zero precision or truncation order. `rowPolynomial`
is a mathematical specification: the product of the parity factors evaluated
on the indicator of a finite set of test-variable incidences. It is not the
program's output or an input to its native certificate.

`val_rowTerm` proves the actual modular product equals that source product.
`val_rowSum` proves that the signed word stream computes its subset Möbius
coefficient; this is the multilinear coefficient formula of Lemma D.2, PDF p. 56.
The insertion law `BitString.subsetMobius_insert` justifies the signs, and the
word/subset correspondence requires distinct selected incidences.
`IncidenceSelections` discharges that requirement for the actual constructed
rows: block selection only removes entries, scopes are deduplicated, and
variable-group blocks are disjoint. `val_rowVertex` therefore needs no supplied
selection or entry-correctness premise. Invalid wire indices give zero.
`val_colEntry` proves the corresponding power of two counts unselected bits in
the variable group. These results cover repeated raw variables and tests; they
do not assert a complete raw-system counting frontend.

The implementation remains the existing certified entry stream. It enumerates
subsets of the selected incidences in one group, not assignments to all original
variables. The preceding entry-resource theorem already charges that stream's
actual time and polynomial workspace. The new specification introduces no
counting oracle or runtime assumption.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceEntryCorrectness`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceEntryCorrectness.lean)
checks signed coefficients, zero parameters, exact selections, repeated variables
and rows, invalid indices, free-variable columns and a constructed row whose
coefficient is $-6V$ modulo $16$.

The extra factor in the old counter comes from its replacement group schedule
`floor(sqrt(lambda)/nu^2)`, with `lambda=ceil(log₂ n)` and
`nu=ceil(log₂ lambda)`; its division and interpolation charges retain `nu^2`.
The sharper route uses truncated incidence-network contraction at size `n*nu`.
This entry-correctness milestone does not change the old end-to-end algorithm.
The actual degree-array traversal and native contraction sum are now connected
as described below. Exact reconstruction of the sparse-system count, high-incidence
branches and parity-query composition still need to be connected before the source
eta-time bound can be claimed. The common occurrence
count restriction on weighted rows, variable-length raw rows, tables and graphs
remain material limitations.


### Stream the computed degree arrays and their native contractions

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySum`
and open `Cslib.Circuits.Frontier.IncidenceNetwork`. `ArrayInput` contains the
unary declared variable count `n` and the actual equation list, with binary
monomial indices. `degreeCap k` computes $K=k(a+2n)$ from its equation count $a$;
`Nat.ceilQuarter` computes $J=\lceil n^{1/4}\rceil$. The checked square-root
identity `Nat.ceilQuarter_eq_sqrt` supplies a polynomial-time implementation of
the search-defined root, including zero.

`arrayCount K J` is the binary number $(K+1)^{J^2}$, rather than an allocated
list of arrays. `arrayAt K J i` writes one length-$J^2$ radix array. The decoder
has unique coverage of all arrays with entries at most $K$, including radix one
and zero width; `selected_degrees_coverage` derives those coordinate bounds from
the total selected degree. `arrayCount_polytime` and `arrayAt_polytime` charge the
actual binary arithmetic, digit traversal and unary coordinate writes.
`degreeCount_le` bounds the computed number of visited indices by
$2^{4\sqrt n(\operatorname{clog}_2(k(c+2)+1)+\operatorname{clog}_2 n)}$
when $a\le cn$ and $n\ge1$.

`network_polytime` charges actual incidence discovery/deduplication, binomial
index widths, ports, descriptors and padding, without expanding tensor tables.
`buildArray_polytime` discharges all its parameter computations from the
original input and binary index, including precision and truncation $n+1$.
`sumArrays k` specifies the native loop's modular contraction sum;
`sumArrays_eq` identifies it with the sum over exactly those computed indices.
Although this mathematical specification is noncomputable, its
`exists_sumArrays_certificate` gives a proved native binary machine constructing,
contracting and accumulating one network at a time. Its time is bounded by

$$
(\mathrm{degreeCount}+1)A(L+1)^A
  2^{A s/\lfloor\sqrt{\lfloor\log_2 s\rfloor}\rfloor},
\qquad s=n\operatorname{clog}_2(\operatorname{clog}_2 n),
$$

and its peak workspace by $A(L+1)^A$ in the original encoded input length $L$.
For fixed $k\ge1,c$, the certificate derives admissibility for every sufficiently
large `IsSparseBranch k c n sys`; no network, rank, answer, entry budget or
contraction oracle is supplied. The array-count multiplier remains explicit.
This is a source-algorithm stage from OpenAI2026ETH, Appendix D.3, Lemma D.2,
PDF pp. 55–57, toward 1575 Lemma 3.2/Proposition 4.2, rather than a new bound for the
old interpolation counter.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceArrays`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceArrays.lean)
checks radix-one/empty arrays, unique selected-degree coverage, quarter-root
boundaries, a fully computed network and a nonvacuous family of native certificates.

The outstanding semantic step is equality of this modular contraction sum with
the sparse-system solution count. The extra-array zero and local-rank coverage
obligations are now proved below.
Then high-incidence branching, greedy parity queries, sharper sparsification and
weighted reconstruction/time rescaling must be assembled. The old end-to-end
counter still has its squared-log-log overhead. Common-occurrence positive
serialized rows remain a frontend restriction; arbitrary variable-length rows,
table and graph endpoints, full Theorem 7.1 and ALL-main remain open.


### Reconstruct the source-supported incidence sum and its count target

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceArraySupport`
and `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceCountReconstruction`,
and open `Cslib.Circuits.Frontier.IncidenceNetwork`.

`unrankCombination_coverage` proves that the existing false-first decoder covers
fixed-weight words uniquely, without enumerating the whole Boolean cube.
`selectBlock_coverage` transfers this to the actual incidence sublists.
`array_and_ranks_coverage` derives the unique decoded degree array and every
unique valid local rank from a selected incidence monomial. The system supplies
the actual incidence lists; their distinctness follows from `nodup_pairInc`,
even with repeated raw variables or tests. The total selected degree supplies
the array coordinate bounds. No rank or basis is input advice.

`FeasibleArray` is the mathematical source condition: the actual global degree
check passes and each degree is at most the capacity of its computed group pair.
`polyContraction_eq_zero_of_not_feasible` proves that every extra array in the
full radix box has zero contraction over natural coefficient polynomials,
before modular reduction. Cap overflow writes the isolated dead row. Capacity
overflow makes the actual row entry zero at every word. This includes a block
with no bits: `length_blockIndices` ensures it is checked rather than skipped by
`zip`. `sumArrays_eq_feasible` therefore identifies the existing native output
with the modular sum over exactly the feasible decoded arrays. This filter is a
mathematical identity of the existing output, not an extra loop or an assumed
counter contract; the approved actual construction/streaming time and workspace
certificates above remain unchanged.

`systemIncidencePolynomial k (n,sys)` uses the actual listed equations, their
finite monomials/scopes and the computed cap $k(a+2n)$. It is the existing source
incidence expansion, used as a specification rather than evaluated by monomial
enumeration. `rootCount_eq_incidenceResidue` derives the exact solution count by
summing its coefficients below $V^{n+1}$ and taking the least nonnegative residue
modulo $2^{n+1}$. Its hypotheses are canonical equations, declared variable
indices and listed monomial lengths at most $k$. The finite degree bound is
proved from those lengths, and the existing declared-variable count bridge and
coefficient cutoff discharge recovery. No supplied polynomial coefficients,
answer or native output equality is a premise. This covers zero declared
variables, no equations, contradiction, and variables outside every scope.

These are the local uniqueness, zero-contribution and original-input recovery
stages of OpenAI2026ETH, Appendix D.3, Lemma D.2, equations (D.1)–(D.2), PDF
pp.55–56. From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceReconstruction`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceReconstruction.lean)
checks decoder ranks, deduplicated incidences, unique subset/array coverage,
valid and invalid zero-width blocks, dead/capacity-zero padded contractions,
actual native output support and exact count recovery including free variables
and constant contradiction. A duplicate-monomial negative case checks that the
normalization hypothesis is material.

The remaining global correspondence must identify the supported native
contraction sum with `systemIncidencePolynomial` in the truncated ring. The
shared-wire, padding and factorization stages are now proved below. The sum
still needs to be reindexed globally into the original per-test incidence
families, with invalid binary ranks removed and listed-test coefficients
identified with the finite normalized equations. High-incidence branches, parity
queries, sharper sparsification and actual eta-time absorption/rescaling remain.
These are the limits of this intermediate stage. The later native general counter and parsed
ragged weighted continuation resolve the counting-resource and weighted frontend gaps; table,
graph and ALL-main endpoints remain open.


### Identify physical wire assignments, padding and coefficient products

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceWireRanks`,
`Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidencePadding`,
`Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceGroupCoefficients`
and `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceColumnWeights`.
The namespace is `Cslib.Circuits.Frontier.IncidenceNetwork`.

`blockIndices_rowPorts` and `blockIndices_colPorts` characterize the actual fold
that reads each endpoint's ports. `row_col_index_eq` proves both endpoints read
the same physical block, even though their block order differs. Width-zero
blocks are included. `wireRankEquiv` identifies the actual main-wire assignment
space with the tuples of ranks below $2^{w_b}$; its coordinate map is the actual
prefix sum plus in-block offset, rather than a cardinality-only bijection.
`wireRankEquiv_apply` identifies its rank with `wireIndex`. Thus
`existsUnique_wireAssignment` constructs the unique main-wire assignment for
any fitting local subset ranks, and `sum_wireAssignments_eq_sum_ranks` reindexes
the full assignment sum exactly. No assignment or decoding identity is advice.

`polyContraction_network_padding` proves that the actual added padding leaves
the natural polynomial contraction unchanged, before truncation or reduction.
Each added row `[1,0]` forces its edge false and the column `[1,1]` contributes
one. The prefix/suffix bijection and `sum_padding_false` count each original
assignment exactly once. Dead arrays and no padding are covered.
`sumArrays_eq_unpadded` transports this to the existing native loop's actual
scalar output, while keeping the same charged construction/contraction machine.
Its previously proved time and polynomial original-input space bounds are
unchanged; the mathematical reindexing is not a new exhaustive evaluator.

The generic `subsetMobius_color_product` factors coefficients across disjoint
coordinate colors. `val_rowVertex_prod` applies it to the actual group stream:
the row entry is the product of the separate test coefficients in the truncated
modular ring, with selected-test scope bounds derived from its constructed
blocks. Invalid ranks still give zero. On the variable side,
`mem_allColumnSelected_iff_rows` proves both endpoints select the same incidences
on their shared wires. `val_colVertices_prod` then identifies the product of the
actual column entries with $2^u$, where $u$ is the number of declared variables
missing from all actual row selections. Residue classes count each variable
once, including variables outside every scope. The variable-side theorem assumes
$J>0$; the wire and padding theorems also handle no blocks.

These are the concrete shared-wire, assignment-coverage, padding and group-weight
steps of OpenAI2026ETH, Appendix D.3, Lemma D.2, PDF pp.55–56. From the repository
root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceGlobal`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceGlobal.lean)
checks distinct row/column port orders, actual readback, unique fitting-rank
assignments, zero widths and no blocks, forced padding multiplicity, live/dead
padded readback, a negative test-coefficient product modulo 16, and variables
outside every scope contributing their powers of two.

The native finite-sum support/readback stage is now proved below. Its grouped
incidence polynomial still needs identification with the polynomial on original
finite normalized equations. The new identity is not yet original-assignment
count correctness. High-incidence branch and parity-query composition, sharper
sparsification, explicit exponent absorption and weighted eta-time rescaling
remain at this intermediate stage. The later native general counter and parsed ragged weighted
continuation resolve these counting/frontend gaps. The older interpolation counter is unchanged;
table/graph endpoints and ALL-main remain open.


### Read the actual native stream as a fitting-rank incidence sum

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceRankSum`
and open `Cslib.Circuits.Frontier.IncidenceNetwork`.
`polyContraction_eq_rankPolynomial` is an exact finite-sum identity for each
actual padded network. It reindexes all main-wire assignments by full-width
binary ranks, proves every unused rank makes its actual group row zero, removes
those terms, and bijects the remainder with `CombinationRanks`. These tuples
contain one `Fin (choose capacity degree)` per computed pair. The proof also
covers dead arrays, zero capacities, zero widths and no wire blocks. Padding
preservation is included. It assumes no contraction value or output relation.

`rankIncidencePolynomial` is the resulting integer polynomial specification:
for each fitting tuple, multiply the actual test-group Möbius coefficients by
the constant $2^u$ for declared variables absent from all actual row selections;
retain the actual global degree-cap check. The polynomial's coefficients can
be negative. `truncNatHom_polyContraction_eq_rankIncidencePolynomial` proves its
image in the truncated modular ring equals the actual natural contraction.
This composes the real wire assignment, row coefficients and variable weights;
none of these correspondences are supplied as premises.

`sumArrays_eq_rankIncidenceResidue` then proves the complete existing native
stream's scalar output is exactly the least nonnegative residue of the sum of
those polynomials' coefficients below $V^{n+1}$, modulo $2^{n+1}$. It assumes
$n\ge1$ for positive quarter-root groups. The natural finite-rank identity also
handles no groups; the zero-variable counting dispatch remains separate. The
coefficient congruences and canonical residue are derived, rather than assumed.
These finite sums specify the existing fast native contraction; no exhaustive
rank/powerset evaluator is substituted. Its actual binary time and original-input
polynomial peak-space certificates remain unchanged. The complete client
combines the output identity with that certificate on a genuine sparse family.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceRankSum`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceRankSum.lean)
checks a genuine unused two-bit encoding (three fitting singleton subsets), zero
from impossible capacity and cap overflow, the unique empty-assignment term,
padded truncated reconstruction and exact native grouped readback/resource
composition.

This completes the native-to-grouped fitting-rank identity. The next section removes
these array/rank indices from the global sum. Original-equation coordinate and
coefficient identification, complete sharper counting and the broader frontend/graph
objectives remain separate. The source locator is OpenAI2026ETH, Appendix D.3,
Lemma D.2, PDF pp.55–56, especially the unique-index/zero-unused-bit and
contraction-sum paragraphs; no full 1575 Lemma 3.2 or Theorem 7.1 is claimed.


### Remove the global array and rank indices

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceSelectionSum`.
`sum_rankIncidencePolynomial_eq_selectionPolynomial` replaces the complete array/rank sum
by `selectionPolynomial`: choose a sublist of each actual `pairInc` block, keep exactly
families whose total length is at most the cap, and multiply the corresponding group
coefficients and declared free-variable weight. This is an exact identity over integer
polynomials. The proof recovers the unique array from the sublist lengths and the unique
fitting ranks from sublist coverage, so it preserves multiplicity even for repeated
input equations. Dead arrays contribute zero. `mem_selectionFamilies` exposes the
componentwise sublist condition without unfolding the mathematical enumeration.

`sumArrays_eq_selectionResidue` connects this family sum directly to the actual native
scalar output for $n\ge1$. These finite sets specify the output; the native machine
continues to decode binary indices, write networks and stream contractions. Its existing
binary time includes the actual degree-array traversal, and its peak workspace remains
polynomial in the original encoding. No output-size bound is substituted for runtime and
no extra log-log factor is discarded.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceSelectionSum`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceSelectionSum.lean)
checks separate positions for repeated equations, a cap that admits a singleton and one
that rejects it, native readback for a nonconstant equation, no equations and a constant
contradiction, and composition with the existing binary time/space certificate.

The next section proves the original-equation coordinate and coefficient bridge for
this family sum. The source is OpenAI2026ETH, Lemma D.2, PDF pp.55–56; the complete
STOC1575 Lemma 3.2 and Theorem 7.1 still need the separate resource compositions below.

### Count original assignments with the native incidence stream

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceOriginalCounter`
and open `Cslib.Circuits.Frontier.IncidenceNetwork`.
`selectionPolynomial_eq_incidenceSum` transports the capped family sum to the original
finite equations. Its identity is exact over integer polynomials at every cap. Local
positions in a residue-class group biject with original row indices, so repeated equations
remain distinct. Canonical listed integer monomial counts equal finite equation lifts;
selected incidence degree, per-test coefficient products and every declared free-variable
weight are preserved. No polynomial identity or desired output is supplied as a premise.

`trunc_selectionPolynomial_eq_systemIncidencePolynomial` specializes this to the actual
quarter-root grouping, computed cap and truncated coefficient ring. `sumArrays_eq_rootCount`
then proves the native output equals `HeavyBranchFold.rootCount` when $n\ge1$, every equation
is canonical, all listed variable indices are below $n$, and every listed monomial has length
at most $k$. The degree hypothesis supplies the cap needed for source residue recovery;
the coordinate transport itself does not need it. The theorem counts all declared variables,
including those absent from every equation.

For zero variables, use `countOriginal k (n, sys)`. Its `zeroCount` branch evaluates the
system on the unique empty assignment, with proved polynomial binary time and actual output
writing. `countOriginal_eq_rootCount` covers every $n$ under the same semantic hypotheses.
Positive sizes use the existing streamed contractions. There is no positive-size exhaustive
fallback: the existing exhaustive-counter module supplies only its polynomial input-evaluation
lemma to the zero-variable branch.

`exists_countOriginal_certificate` certifies one actual native machine for this dispatch.
For fixed $k,c$ and all sufficiently large admissible sparse branches, its time is bounded by
$$P(L)+(\operatorname{degreeCount}+1)A(L+1)^A
  2^{\lfloor As/\lfloor\sqrt{\lfloor\log_2 s\rfloor}\rfloor\rfloor},
  \qquad s=n\lceil\log_2\lceil\log_2 n\rceil\rceil,$$
and its peak space by $P(L)+A(L+1)^A$, with $P$ polynomial and $L$ the full original encoding
length. The zero-variable branch has polynomial time and space even for arbitrary raw equation
lists. The actual branch test, direct output, binary network writing and streamed summation
are charged by the composed certificate. The degree-array multiplier remains explicit.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceOriginalCount`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceOriginalCount.lean)
derives numeric original counts for a three-variable parity equation, declared free variables,
repeated equations in different groups, interleaved local positions, a nonlinear equation with a
constant term, empty and contradictory systems, and the zero-variable dispatch. It also checks
the exact truncated-ring bridge, negative semantic hypotheses and a genuine sparse family with
both the original answer and actual native resource certificate.

This finishes original-count correctness of the incidence branch solver. The next section
composes its sharper resource bound and high-incidence branching. The source is OpenAI2026ETH
Appendix D.3, Lemma D.2, PDF pp.55–56, particularly the per-test coefficient, free-variable
weight and contraction-sum paragraphs.

### Run the sharper normalized sparse-system counter

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceSparseCounter`
and open `Cslib.Circuits.Frontier.IncidenceNetwork`. `countSparse k (n, sys)` computes the
source high-incidence variables, streams their assignments, and uses the certified incidence
solver on reduced systems. The direct contradiction and tautology branches retain their
binary outputs. `countSparse_eq_rootCount` counts original assignments at every size under
canonicality, declaration and listed degree at most $k$.

`validSystem` computes those semantic checks in polynomial binary time. `countChecked` uses
the incidence solver when valid and returns zero otherwise. Its global output bound follows
from proved original-count correctness. This supplies the streaming accumulator bound;
no counter or desired runtime contract is assumed. Only validation routines are reused from
the older interpolation-counter module; its counting algorithm is not called.

`exists_countSparse_real_sharp_certificate` certifies one actual native machine. For fixed
$k,c$ and all sufficiently large $n$, assume at most $cn$ equations and at most
$\lceil\log_2 n\rceil^c$ monomials per equation, as well as the semantic hypotheses above.
No input bound on scopes or occurrences is needed. With $L$ the full unary-size/binary-index
encoding length, its native certificate time bound is
$$D(L+1)^D 2^{6D\eta(n)},\qquad
  \eta(n)=\frac{n\log_2\log_2 n}{\sqrt{\log_2 n}},$$
and its peak space at most $D(L+1)^D$. The constant and threshold depend only on $k,c$. Native certificate time and charged space
include encoded output and hold up to fixed machine constants.
The certificate charges validation, branch construction, every reduced-system call, network
writing, contraction, binary reconstruction and summation. Its rounded counterpart is
`exists_countSparse_sharp_certificate`.

The numerical modules `LogLogSqrtLog` and `LogLogSqrtLogReal` make the rounding explicit.
The complete array exponent $\sqrt n(C+\lceil\log_2 n\rceil)$ is eventually bounded by
`Nat.logLogSqrtLogScale n`; the padded contraction size is reduced to the same scale.
For $n\ge16$, this rounded scale is at most $6\eta(n)$. For a fixed linear enlargement
$N\le Cn$ and $n\ge\max(16,C)$, it is at most $120C\eta(n)$. These proved numerical
comparisons support the weighted plan's variable bound; they are not a supplied CNF runtime.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceSparseCounter`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceSparseCounter.lean)
checks a genuinely heavy variable with both a reduced incidence-solver call and a contradictory
branch, the original answer, invalid-input rejection, zero-variable cases, a numerical rounding
instance, linear rescaling and a nonempty all-size sparse family with the real resource certificate.

### Count polylogarithmic-density parity leaves with the native machine

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceParityCounter`.
`countParity k β N₀ (n, ψ)` runs the actual initial-row search and greedy parity reduction,
using `uniformSparseCount k (paritySparsity β) N₀` for every candidate system. It counts over
all declared variables, including unused bits. `countParity_eq_modelCountOn` proves the
original CNF count when the width is at most $k$, variables are below $n$, and either
$m\le\lceil\log_2 n\rceil^\beta n$ or $n<\texttt{parityCutoff}\ k\ \beta$.
`countParity_le` bounds the binary output on every input, including rejected ones.

`compiledSystem_isSparse` covers every candidate, including discarded candidates: above the
fixed cutoff there are at most $6n$ equations, each canonical, declared, degree at most $k$,
and listing at most $\lceil\log_2 n\rceil^{\max(6,2\beta+4)}$ monomials. This discharges
correctness for the actual callback rather than assuming a polynomial-system oracle.

`exists_uniformSparseCount_certificate` supplies a global sharper-time/polynomial-space
certificate for that callback. The algorithm uses direct counting only below a fixed threshold,
validates the sparse domain otherwise, and rejects outside it. The threshold is an algorithm
constant; no input rank, desired answer or runtime is supplied. Its time includes validation,
output writing and all original native stages, even on invalid inputs.

`exists_countParity_certificate` composes an actual greedy-search machine with global polynomial
workspace. Its explicit `sparseCNFTimeBound` charges the initial search and
$(3n+1)(\texttt{candidateTupleCount}\ m\ P+1)$ actual candidate evaluations, where
$P=\texttt{greedyRowListLength}\ B\ m$. Each call has the proved single-loglog callback
bound with a polynomial encoded-system length.

The companion `IncidenceParityResources` now finishes this leaf resource composition.
`exists_countParity_sharp_certificate` gives one actual machine with global bounds, at **every**
size and for every typed input:
$$A(L+1)^A2^{A\,\texttt{Nat.logLogSqrtLogScale}(n)},\qquad A(L+1)^A\text{ space}.$$
Here $L$ is the complete unary-declared-size/binary-index CNF encoding length. The time includes
initial-row search, every candidate, compilation, native evaluation and binary output writing.
These are charged native-certificate bounds, realized up to fixed machine constants.
The correctness domain remains the density restriction above; rejected dense inputs do not acquire
a counting claim from an all-input resource bound. `exists_countParity_real_sharp_certificate`
replaces the rounded exponent with $6A\eta(n)$ for $n\ge16$.

`LogLogSqrtLogPolylog` bounds every fixed polynomial in $\lceil\log_2 n\rceil$ by the rounded
scale plus a fixed additive constant. The constant covers the finite exceptional prefix, including
zero. This absorbs both initial search and the full candidate multiplier; the older module's
integer query-count estimate is reused, while its squared-loglog asymptotic is not used.

### Compose disjoint counting at the sharper schedule

`SharpCountingSchedule.sharpSearchDivisor` computes $\lceil\sqrt{\lceil\log_2 n\rceil}\rceil$,
using one when the logarithm is zero. Its exact square bounds identify the source schedule
$\sigma=1/\lceil\sqrt\lambda\rceil$, without the old $\nu^2$ denominator. The computed
first-success threshold satisfies the actual disjoint counting-tree budget.
`sharp_parameters_polylog` bounds numerical depth and leaf occurrences by fixed polynomials
in $\lambda$, not just their binary lengths. `sharp_rounds_polytime` computes the actual binary
traversal clock in polynomial time/space; `sharp_rounds_le` bounds its value by
$4\,2^{\texttt{Nat.logLogSqrtLogScale}(n)}$ for supported formulas and $n\ge4$, independently
of clause density. Computing this clock does not mean executing its steps takes polynomial time.

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralCounter`.
`exists_countGeneralParity_eq_modelCountOn` derives fixed density and small-size parameters
from the width and proves the original declared-variable count for **arbitrary clause density**.
`countGeneralParity` uses direct counting below the fixed cutoff and the existing executable
disjoint search otherwise. Each actual parity leaf count is normalized to its occurring support;
the outer search restores the unused original variables exactly once. Empty formulas, empty
clauses and zero variables are included. No leaf-counter or sparsifier-correctness contract is
assumed. The companion whole-machine resource certificate below now covers this same function.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceSharpParity`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceSharpParity.lean)
checks ceiling rounding, actual traversal clocks, polynomial absorption including zero, sharp
native parity resources with original-count semantics, dense repeated clauses, unused declared
bits, zero-variable direct branches and a nonempty family above the general counter's cutoff.

### Use the whole general-density machine certificate

Import `Complexity.Computability.Circuit.Frontier.TensorNetwork.IncidenceGeneralResources`.
`exists_countGeneralParity_sharp_certificate k` fixes one actual `countGeneralParity` machine
and all parameters before its input, for fixed $k\ge2$. It counts every valid original declared
CNF, rejects invalid width/support inputs, and has global native time
$D(L+1)^D2^{D\,\texttt{Nat.logLogSqrtLogScale}(n)}$ and space $D(L+1)^D$.
The uniform disjoint traversal theorem is instantiated with the actual normalized parity leaves.
Iteration-prefix bounds transfer every intermediate formula encoding. The declared-count bit
length is bounded by the actual counter's charged workspace before binary normalization.
Accumulation, final unused-variable restoration, selected validity guards and bounded direct
counting are included; workspace has no factor of the traversal clock or counting time.

`exists_countGeneralParity_source_certificate` matches Lemma 3.2's unrestricted-density resource
claim: for every fixed $k\ge2$, all $n\ge20$ and every valid $m$-clause CNF, one machine has bit
time $C(n+m+1)^e2^{A\eta(n)}$ and space $C(n+m+1)^e$, up to fixed realization constants.
Here $\eta(n)=n\log_2\log_2 n/\sqrt{\log_2 n}$. The reusable encoding lemma
`Cslib.Complexity.SAT.length_declaredInput_le` bounds
$L+1\le(20k+4)(n+m+1)^2$ using actual binary literal indices below the declared size.
There is no assumption on $m/n$, and unused declared bits remain counted. The real-scale
comparison applies already at $n\ge16$; every smaller size is covered by the rounded certificate.

From the repository root run
`scripts/build.sh ComplexityTests.Computability.Circuit.Frontier.TensorNetworkIncidenceGeneralResources`.
The [complete client](../../ComplexityTests/Computability/Circuit/Frontier/TensorNetworkIncidenceGeneralResources.lean)
checks a family with $n^2$ repeated clauses and $n-1$ unused variables, original count $2^{n-1}$,
and the actual source time/space witness. It also covers zero-variable contradiction/tautology
and an unbounded invalid-support family rejected in polynomial charged time at declared size zero.

The sharper source counter and parsed ragged weighted execution are now certified as described
above. The table preprocessing/dispatch endpoints are also covered above. General graph
degree-rule/partition endpoints and the remaining graph clauses keep ALL-main open. The source
composition is OpenAI2026ETH Appendix D.3, PDF p.57, imported by STOC1575 Lemma 3.2 p.11.
