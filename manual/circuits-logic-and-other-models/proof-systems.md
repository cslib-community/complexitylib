# Propositional models and resolution proof complexity

Complexitylib represents propositional syntax as concrete finite data and distinguishes satisfiability, derivability and resource-bounded proof objects. This supports reductions, model counting and lower bounds without identifying a proof's length with the time needed to find it. [complexitylib][complexitylib]

## CNF, CSP and quantified formulas

[CNF](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CNF.lean#L67) is a list of clauses, each a list of signed variables. Ordering and repeated occurrences are retained. Several useful sizes coexist: clause count, literal-occurrence count, distinct-variable support, maximum clause width and serialized bit length. In a fixed-width SAT theorem the stated width convention must be checked; in resolution, width is explicitly the number of distinct literals.

The [ClauseSet](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/ClauseSet/Basic.lean#L55) representation instead uses finite sets of finite sets of literals, so order and repetitions disappear. Its occurrence measure counts clauses mentioning a variable. List/set conversions preserve satisfying assignments but need separate size/occurrence lemmas. This is the representation used by the sparsification development.

Support-based CNF model counting counts assignments to variables that occur. Declared-universe counting instead fixes a larger variable set and can include free choices for unused variables. The library supplies relabeling and exact gadget-counting bridges, so a reduction claiming preservation of counts must specify which convention it preserves. This distinction is particularly relevant to dense relabeling and the [native fixed-width counting endpoint](../machines-and-classes/native-counting.md).

[Constraint](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/CSP.lean#L69) has a relation alphabet and constraints consisting of a relation label plus a variable list. Semantics evaluates the label on the corresponding list of domain values. Arity is not enforced by the relation's type; a fixed-arity interpretation is an additional condition. Boolean/CNF translations and partition-function clients instantiate this generic semantic interface.

[QBF](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/QBF.lean#L76) uses named-variable Boolean quantifiers. Evaluating an existential or universal binder updates the assignment with both possible values and ORs or ANDs the results. Arithmetization and native/interactive-proof completeness clients live in their corresponding sections. This formula syntax does not by itself assert a resource bound for evaluation.

## Majority preservation and Boolean constraint languages

A polymorphism combines satisfying tuples coordinatewise and preserves the relation. Import
[`Complexity.Logics.Polymorphism`](../../Complexity/Logics/Polymorphism.lean) for
`Cslib.Logic.IsPolymorphism`. Its preservation rules cover conjunction, substitution (including
repeated variables), existential projection, projections and composition. The operation's index
type may be empty: a nullary constant preserves a relation exactly when its constant tuple belongs
to that relation. This differs from vacuous preservation of an empty relation by an operation
with positive arity.

Import [`Complexity.Logics.Propositional.CNF.Majority`](../../Complexity/Logics/Propositional/CNF/Majority.lean)
for `Cslib.Logic.PL.isPolymorphism_majority_iff_exists_twoCNF`. For any finite coordinate type
`V`, a relation `R : Set (V → Bool)` is preserved by `Cslib.majority 3` exactly when some
`CNF V` defines it using clauses of width at most two. The definition has no auxiliary variables
and agrees on every assignment. Empty relations and nullary relations are included: an empty
clause defines falsity and the empty CNF defines truth. The proof uses the existing coordinatewise
median `Cslib.BitString.median`.

The [checked examples](../../ComplexityTests/MajorityCNF.lean) give a signed 2CNF definition of
equality, an existential projection, a ternary-disjunction counterexample and the nullary edge
cases. This is the bijunctive structural equivalence used in Schaefer's Boolean dichotomy.
The structural theorem alone makes no complexity claim. The full Boolean theorem is tracked in
[#2822](https://github.com/cslib-community/complexitylib/issues/2822); symmetric and larger-domain
dichotomies are outside that task.

For native complexity statements, import
[`Problems.CSP.Basic`](../../Complexity/Computability/Complexity/Problems/CSP/Basic.lean).
`Cslib.Complexity.CSPSAT arity sem` uses the existing CSP lists, requires every scope length to
equal its symbol's declared arity, and asks for one Boolean assignment satisfying all constraints.
The alphabet, arities and semantics are fixed independently of the input. For a finite alphabet,
`CSPSAT.mem_NP` proves native NP membership under `encCSP encRel encNat`, with framed lists/pairs
and binary variable labels. Repeated scope variables, empty relations and nullary relations are
allowed; malformed arities are rejected. The
[checked syntax and model examples](../../ComplexityTests/BooleanCSP.lean) include sparse large
labels, inconsistent unary pins, repeated variables and nullary truth/falsity.

[`Problems.CSP.Constant`](../../Complexity/Computability/Complexity/Problems/CSP/Constant.lean)
and [`Problems.CSP.Majority`](../../Complexity/Computability/Complexity/Problems/CSP/Majority.lean)
prove native P membership from a common unary constant (`CSPSAT.mem_P_of_constant`) or a common
majority operation (`CSPSAT.mem_P_of_majority`). The constant decider first rejects constraints
using empty relations. In the majority case, fixed local 2CNF templates are instantiated by a
certified polynomial-time compiler and sent to native 2SAT. Local positions use unary indices
for list lookup; original variable labels retain their binary encoding. These bounds are for
each fixed language, with no uniform bound on preprocessing a supplied language or its truth
tables. The shared six-case criterion is `Cslib.Logic.PL.CSP.HasSchaeferPolymorphism`; this layer
establishes its two constant cases and majority case, with the remaining cases tracked in #2822.

Import `Complexity.Logics.Polymorphism.BooleanClone` for the full positive-arity Boolean clone
classification (`Cslib.Logic.BooleanClone.classification`). A clone contains every projection
and is closed under superposition. Either every operation is essentially unary, or it contains
AND, OR, ternary majority or ternary parity. The arbitrary-arity step uses a finite-partition
argument; only the binary and ternary cases use truth-table enumeration. Constants in the shared
Schaefer criterion are unary. For a language lacking all six operations,
`CSP.projection_or_negation_of_not_hasSchaeferPolymorphism` identifies every positive-arity
polymorphism as a projection or negated projection. Consequently every self-dual relation is
preserved. [Checked examples](../../ComplexityTests/BooleanClone.lean) include a NAE relation
with none of the six operations and with negation as a polymorphism. The hardness application
below uses this algebraic classification.

For fixed-language reductions, import `Complexity.Logics.Propositional.CSP.PrimitivePositive`
and `Complexity.Computability.PolyTime.CSP.Gadget`. A `CSP.PPGadget` is a well-formed conjunction
with free ports and existential auxiliary ports. `CSP.exists_ppGadget_of_polymorphisms` proves
the canonical finite construction when the target relation is nonempty, separates its coordinate
columns, and is preserved by every positive-arity common polymorphism. This restricted
equality-free form does not assert general equality elimination. The native
`CSP.computableInPolyTime_replaceGadgetsGuarded` compiler uses fixed gadget lookup, fresh odd
auxiliary names and even original names, retaining binary variable labels. It checks exact source
arities and substitutes an explicit rejecting instance on malformed inputs.
[Checked examples](../../ComplexityTests/CSPGadget.lean) exercise freshness, repeated ports,
existential witnesses, empty/nullary instances and malformed rejection.

The hard branch is available from `Complexity.Computability.Complexity.Problems.CSP.Hardness`:
`CSPSAT.npComplete_of_not_hasSchaeferPolymorphism` proves native NP-completeness whenever the
fixed finite language has none of the six operations. It assumes no solver, clone classification
or pp-definability theorem: all are proved in its imports. `SelfDualThreeSAT.npComplete` supplies
the hard source by adjoining a shared reference bit to signed three-literal clauses. XOR with
that bit normalizes any model to an ordinary clause model. The eight lifted relations are
self-dual, nonempty and separate all coordinate columns, discharging the restricted gadget
construction's hypotheses. The reduction checks exact arity and retains binary labels, including
sparse labels. [Checked hardness examples](../../ComplexityTests/SchaeferHardness.lean) give
a concrete NAE language and cover contradictory clauses, repeated variables and malformed scopes.
The tractable branches must still be assembled to complete #2822.

Import `Complexity.Logics.Propositional.CNF.Horn` and
`Complexity.Computability.Complexity.Problems.HornSAT` for AND/Horn and OR/dual-Horn
correspondence (`isPolymorphism_and_iff_exists_hornCNF`,
`isPolymorphism_or_iff_exists_dualHornCNF`) and native `HornSAT.mem_P`/`DualHornSAT.mem_P`.
These solvers support all clause widths under binary `encCNF`. Horn syntax counts positive
occurrences: repeated negative literals and opposite-polarity tautologies are supported, while
two copies of a positive literal violate the syntax condition. Forward chaining computes the
least-model candidate in `numVars + 1` passes, storing filtered occurrences rather than a table
indexed by the largest label. [Checked Horn examples](../../ComplexityTests/HornSAT.lean)
include sparse labels, empty clauses and the repeated-positive convention.

`Complexity.Logics.Propositional.CSP.Affine` proves
`isPolymorphism_parity_iff_exists_affineSystem`: ternary parity preservation is equivalent to
definition by affine parity equations without auxiliaries, including empty/nullary relations.
`Complexity.Computability.Complexity.Problems.XORSAT` gives actual dense Gaussian elimination,
a certified sparse binary-label compiler and `XORSAT.satisfiable_mem_P` for ordinary systems.
An equation is a variable list paired with a Boolean right-hand side; repeated variables cancel
in the Boolean ring. The dense algorithm preserves row count and weakly decreases its complete
framed state encoding at each column. [Checked XOR examples](../../ComplexityTests/XORSAT.lean)
cover cancellation, inconsistency, dependent equations and malformed dense widths.
The fixed-language CSP applications of these solvers remain to be connected in #2822.

## Three resolution representations

| Representation | What it supplies | Cost |
|---|---|---|
| [CNF.Derives](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution.lean#L100) | Inductive proposition generated by input clauses and pivot resolution | No explicit size. |
| [CNF.IsProof](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Proof.lean#L107) | A finite ordered list whose lines are justified by inputs or earlier lines | Number of lines; maximum distinct-literal width. |
| [CNF.Derivation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/TreeLike.lean#L85) | Type-valued tree with input leaves and binary resolution nodes | Tree-node count, width and depth. |

The resolvent removes opposite pivot literals and concatenates the remaining lists. There is no primitive weakening rule; list-level subtleties are handled by lemmas. Soundness and refutation completeness relate the derivability proposition to unsatisfiability. Explicit proof representations then support quantitative theorems.

A tree-like derivation yields a decision tree that finds a clause falsified by the input assignment. Conversely, a suitable clause-search decision tree yields a resolution refutation with at most `2 leaves - 1` nodes. Sharing in a line proof need not survive this tree conversion, which explains why tree-like and general resolution complexity must remain separate.

## Major lower bounds and interpolation

[The pigeonhole development](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Pigeonhole.lean) formalizes Haken's exponential lower bound for `PHP^(n+1)_n`, using a simplified Beame–Pitassi-style argument. Its explicit finite endpoint gives at least `2^floor(n/24)` proof lines. Source documentation explains the critical-assignment measure and greedy restriction sequence. The result also lower-bounds tree-like resolution through the line/tree bridge.

[The Ben-Sasson–Wigderson tradeoff](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/SizeWidth.lean) says that a CNF of initial width k on N variables with an s-line refutation has a refutation of width at most `k + 2 sqrt(2 N log s) + 2`. The contrapositive form yields an exponential line lower bound from a width lower bound. These constants and the logarithm/real square-root convention are explicit in the theorem.

[The Tseitin-expander result](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/TseitinExpander.lean) combines a graph-expansion width lower bound with that tradeoff. It gives a family of linear-variable, constant-width unsatisfiable CNFs requiring exponentially many proof lines. The expansion witnesses are obtained nonconstructively from counting, and the source explicitly says so: existence of a hard family is proved, while an efficient explicit expander/formula generator is not supplied by that endpoint.

Interpolation modules extract circuits separating the two sides of a refuted conjunction. Monotone extraction supports clique/coloring lower-bound applications, and a separate polynomial-time file addresses encoded extraction. The distinction between semantic existence of an interpolant and a native efficient extraction algorithm follows the same design pattern as circuits and finite-model logic. See [interpolation](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation.lean), [monotone extraction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/MonotoneExtraction.lean) and [native extraction](https://github.com/cslib-community/complexitylib/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Logics/Propositional/Resolution/Interpolation/PolyTime.lean).

## Known Limitations

This section inventories resolution and its syntax clients. It does not reclassify PCPs or interactive proofs as resolution proof systems; their verifier and protocol models have separate owners. The endpoint statements and model conventions are source-inspected, while every proof body and every original lower-bound paper has not been independently checked in this worker pass.

[complexitylib]: ../sources.md#complexitylib
