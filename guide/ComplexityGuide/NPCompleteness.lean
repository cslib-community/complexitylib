/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.CircuitSAT
import Complexity.Computability.Complexity.Problems.ChromaticNumber
import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.CliqueCover
import Complexity.Computability.Complexity.Problems.Coloring
import Complexity.Computability.Complexity.Problems.DominatingSet
import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Complexity.Problems.FeedbackArcSet
import Complexity.Computability.Complexity.Problems.FeedbackVertexSet
import Complexity.Computability.Complexity.Problems.NAEThreeSAT
import Complexity.Computability.Complexity.Problems.Hamiltonian.Directed
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Complexity.Problems.IntegerProgramming
import Complexity.Computability.Complexity.Problems.JobSequencing
import Complexity.Computability.Complexity.Problems.Knapsack
import Complexity.Computability.Complexity.Problems.MaxCut
import Complexity.Computability.Complexity.Problems.MaxTwoSAT
import Complexity.Computability.Complexity.Problems.Partition
import Complexity.Computability.Complexity.Problems.PlanarPositiveOneInThreeSAT
import Complexity.Computability.Complexity.Problems.PlanarThreeSATThree
import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Complexity.Problems.TSP
import Complexity.Computability.Complexity.Problems.TwoSAT.Completeness
import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.Problems.ThreeSATThree
import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Computability.Complexity.Problems.CSP.Constant
import Complexity.Computability.Complexity.Problems.CSP.Majority
import Complexity.Computability.Complexity.Problems.CSP.Hardness
import Complexity.Computability.Complexity.Problems.CSP.Schaefer
import Complexity.Computability.Complexity.Problems.HornSAT
import Complexity.Computability.Complexity.Problems.XORSAT
import Complexity.Computability.PolyTime.CSP.Gadget
import Complexity.Logics.Polymorphism.BooleanClone
import Complexity.Logics.BooleanClone.Post
import Complexity.Logics.Propositional.CNF.Majority
import Complexity.Computability.Complexity.Problems.CSP.Incidence
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler
import Complexity.Computability.PolyTime.CSP.Table
import Complexity.Computability.PolyTime.CSP.Edge.Augmenting
import Complexity.Logics.Propositional.CSP.Edge.Augmenting
import Complexity.Logics.Propositional.CSP.Edge.DAGPaths
import Complexity.Logics.Propositional.CSP.Edge.Walk.Operations
import Complexity.Logics.Propositional.CSP.Table.DeltaMatroid
import Complexity.Logics.Propositional.CSP.Planar.Crossover
import Complexity.Logics.Propositional.CSP.Planar.Normalization
import Complexity.Logics.Propositional.CSP.Planar.OneInThree.Gadget
import Complexity.Algorithms.Lean.EdgeCSP.Forest.Blossom
import Complexity.Algorithms.Lean.EdgeCSP.Forest.Optimality
import Complexity.Computability.PolyTime.CSP.Edge.Forest.Spec
import Complexity.Foundations.Data.BitString.CyclicDifference
import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations
import Complexity.Tactic.PolyTime

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

#doc (Manual) "NP-Completeness" =>
%%%
tag := "np-completeness"
%%%

This chapter states and proves NP-completeness results the way the library does: problems with
explicit encodings, polynomial time on multi-tape Turing machines, verifiers, polynomial-time
reductions and the Cook–Levin theorem. It ends by proving that `Clique` is NP-complete, step by
step, which is the outline every new NP-completeness proof follows.

Each problem lives in its own module under `Complexity.Computability.Complexity.Problems`, so a
development imports the problems it uses. The first examples need only these:

```
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.CSP.Incidence
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler
import Complexity.Computability.PolyTime.CSP.Table
import Complexity.Computability.PolyTime.CSP.Edge.Augmenting
import Complexity.Logics.Propositional.CSP.Edge.Augmenting
import Complexity.Logics.Propositional.CSP.Edge.DAGPaths
import Complexity.Logics.Propositional.CSP.Edge.Walk.Operations
import Complexity.Logics.Propositional.CSP.Table.DeltaMatroid
import Complexity.Logics.Propositional.CSP.Planar.Crossover
import Complexity.Logics.Propositional.CSP.Planar.Normalization
import Complexity.Logics.Propositional.CSP.Planar.OneInThree.Gadget
import Complexity.Algorithms.Lean.EdgeCSP.Forest.Blossom
import Complexity.Algorithms.Lean.EdgeCSP.Forest.Optimality
import Complexity.Computability.PolyTime.CSP.Edge.Forest.Spec
import Complexity.Foundations.Data.BitString.CyclicDifference
import Complexity.Foundations.Data.BitString.DeltaMatroid.Operations
import Complexity.Tactic.PolyTime

open Cslib.Complexity Turing.MultiTapeTM
```

```lean -show
open Cslib.Complexity Turing.MultiTapeTM
```

# Problems and Encodings
%%%
tag := "problems-and-encodings"
%%%

A decision problem is a set of instances, `A : Set α`. Complexity is measured on words, so a problem
comes with an encoding of its instances as bit strings, `enc : α ↪ List Bool`. The encoding is
part of every statement: whether a problem is in {name}`P` can depend on it, as it does for
numbers written in unary rather than binary.

Encodings are built from a few combinators: {name}`encBool` and {name}`encNat` (binary) for
atoms, {name}`encPair` and {name}`encList` for pairs and lists, and {name}`encBits` for bit
strings, which encode themselves. Encodings are ordinary functions, so you can look at them:

```lean (name := encNatFive)
#eval encNat 5
```
```leanOutput encNatFive
[true, false, true]
```

```lean (name := encPairEx)
#eval encPair encNat encBool (5, true)
```
```leanOutput encPairEx
[true, true, true, false, true, true, false, true]
```

Problems fix their encodings next to their definitions. Satisfiability of CNF formulas over
variables numbered by natural numbers is {name}`SAT`, encoded by {name}`encCNF`:

```lean
example : SAT = {φ : Cslib.Logic.PL.CNF ℕ | φ.Satisfiable} := rfl

example : encCNF = encList (encList (encPair encNat encBool)) := rfl
```

A graph is a list of vertices and a list of edges ({name}`Graph`), encoded by {name}`encGraph`.
{name}`Clique` asks whether a graph has a clique of a given size, so its instances are pairs,
encoded by `encPair encGraph encNat`.

# Polynomial Time
%%%
tag := "polynomial-time"
%%%

{name}`ComputableInPolyTime` `f encIn encOut` says that some multi-tape Turing machine with a
binary alphabet and finitely many states computes `f`, reading `encIn a` and writing
`encOut (f a)`, within time and space bounded by polynomials in the length of `encIn a`. This is
the notion that definitions and theorems use.

You rarely build machines. Closure rules for the usual operations are registered with
`fun_prop`, so a function written with certified operations gets its certificate automatically:

```lean
example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2 + 1)
    (encPair encNat encNat) encNat := by
  fun_prop

example : ComputableInPolyTime (fun l : List ℕ => l.map (· + 1))
    (encList encNat) (encList encNat) := by
  fun_prop
```

Loops whose body depends on the rest of the input, such as a filter that compares each element
with another part of the input, need the `polytime` tactic, which chooses loop rules and composes
certificates. Membership tests and their negations are certified too:

```lean
example : ComputableInPolyTime (fun p : List ℕ × ℕ => p.1.filter (· ≤ p.2))
    (encPair (encList encNat) encNat) (encList encNat) := by
  polytime

example : ComputableInPolyTime
    (fun p : List ℕ × List ℕ => p.1.filter fun x => x ∉ p.2)
    (encPair (encList encNat) (encList encNat)) (encList encNat) := by
  polytime
```

Both tactics prove only the cost. That `f` computes what you intend is a separate proof.

# P, Verifiers and NP
%%%
tag := "p-and-np"
%%%

A problem is in {name}`P` when a Boolean function deciding it is computable in polynomial time
({name}`mem_P`):

```lean
example : {l : List ℕ | 0 ∈ l} ∈ P (encList encNat) :=
  ⟨fun l => decide (0 ∈ l), by polytime, fun l => by simp⟩
```

{name}`NP` is defined by verifiers. A verifier `V : α × List Bool → Bool` reads an instance
together with a certificate. {name}`IsVerifier` `enc p V A` says that `a ∈ A` exactly when some
certificate of length `p.eval (enc a).length` makes `V` accept, so certificates are polynomially
long in the encoded instance. A problem is in {name}`NP` when it has a verifier that is
computable in polynomial time on the encoded pair ({name}`mem_NP`):

```lean
example {α : Type} (enc : α ↪ List Bool) (A : Set α) :
    A ∈ NP enc ↔ ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
        IsVerifier enc p V A :=
  mem_NP
```

Certificates have exactly the prescribed length. When the natural certificate is shorter, pad it
with `false` and use {name}`IsVerifier.of_padding`. Every problem in {name}`P` is in {name}`NP`,
with a verifier that ignores its certificate ({name}`P_subset_NP`), and {name}`coNP` consists of
the complements of problems in {name}`NP`.

# Reductions
%%%
tag := "reductions"
%%%

{name}`PolyTimeReducible` `encA encB A B` holds when a function `f`, computable in polynomial time
from `encA` to `encB`, satisfies `a ∈ A ↔ f a ∈ B`. A reduction is built as a triple: the map, its
cost and its correctness.

```lean
example : PolyTimeReducible (encPair encNat encNat) encNat
    {p : ℕ × ℕ | p.1 ≤ p.2} {0} :=
  ⟨fun p => p.1 - p.2, by fun_prop,
    fun p => by simp [Nat.sub_eq_zero_iff_le]⟩
```

Reductions compose ({name}`PolyTimeReducible.trans`), and {name}`P` is closed under them
({name}`PolyTimeReducible.mem_P`). The library's
[checked NP-completeness examples](https://github.com/cslib-community/complexitylib/blob/main/ComplexityTests/NPCompleteness.lean)
state deciders, verifiers and reductions in the same plain form.

# NP-Hardness and NP-Completeness
%%%
tag := "np-hardness"
%%%

{name}`NPHard` `encB B` says that every problem in {name}`NP`, over any type of instances and with
any encoding of them, reduces to `B`; {name}`NPComplete` adds that `B` is itself in {name}`NP`.
Hardness transfers along reductions ({name}`NPHard.trans`), which is how almost every hardness
proof goes. An NP-complete problem is in {name}`P` exactly when {name}`P` and {name}`NP` coincide
({name}`NPComplete.mem_P_iff`), so two NP-complete problems are both in {name}`P` or both outside
it ({name}`NPComplete.mem_P_iff_mem_P`):

```lean
example : Clique ∈ P (encPair encGraph encNat) ↔ SAT ∈ P encCNF :=
  Clique_npComplete.mem_P_iff_mem_P CookLevin.SAT_npComplete
```

# The Cook–Levin Theorem
%%%
tag := "cook-levin"
%%%

The first NP-complete problem is satisfiability ({name}`CookLevin.SAT_npComplete`):

```lean (name := cookLevin)
#check (CookLevin.SAT_npComplete : NPComplete encCNF SAT)
```
```leanOutput cookLevin
CookLevin.SAT_npComplete : NPComplete encCNF SAT
```

Its hardness half ({name}`CookLevin.SAT_npHard`) encodes the computation of any polynomial-time
verifier as a formula. Unsatisfiability, its complement, is coNP-complete
({name}`CookLevin.UNSAT_coNPComplete`). The
[Cook–Levin abstract](https://github.com/cslib-community/complexitylib/blob/main/abstracts/ComplexityAbstracts/CookLevinAbstract.lean)
restates the theorem together with every definition it depends on.

# The Catalogue
%%%
tag := "catalogue"
%%%

Every other NP-completeness proof in the library starts from Cook–Levin and follows reductions.
Here is the tree, with the reduction for each edge and the completeness theorem for each problem:

* SAT reduces to 3SAT ({name}`polyTimeReducible_SAT_ThreeSAT`, {name}`ThreeSAT_npComplete`), and
  3SAT to exact 3SAT ({name}`polyTimeReducible_ThreeSAT_ExactThreeSAT`,
  {name}`ExactThreeSAT_npComplete`) and to subset sum ({name}`polyTimeReducible_ThreeSAT_SubsetSum`,
  {name}`SubsetSum_npComplete`).
* 3SAT reduces to maximum 2-satisfiability ({name}`polyTimeReducible_ThreeSAT_MaxTwoSAT`,
  {name}`MaxTwoSAT_npComplete`): given clauses of at most two literals and a binary target `K`,
  can some assignment satisfy `K` of them? Each clause of three literals becomes the ten-clause
  gadget of Garey, Johnson and Stockmeyer ({name}`MaxTwoSAT.gadget`) with a fresh variable, whose
  satisfied clauses depend only on four truth values ({name}`MaxTwoSAT.countP_gadget`). An
  assignment satisfies at most seven of them ({name}`MaxTwoSAT.gadgetScore_le`), seven when the
  source clause holds and the fresh variable is the majority of its literals
  ({name}`MaxTwoSAT.gadgetScore_majority`), and at most six when it fails
  ({name}`MaxTwoSAT.gadgetScore_false_le`). Short clauses
  are first padded by repetition through {name}`toExactThreeSAT`. Plain 2-satisfiability, by
  contrast, is in `NL` ({name}`TwoSAT.mem_NL`).
* 3SAT reduces to {name}`ThreeSATThree` via {name}`toThreeSATThree`
  ({name}`ThreeSATThree_npComplete`). Its clauses have at most three literals, including binary
  clauses, and every variable has at most three literal occurrences. Repetitions within a clause
  count separately. {name}`Cslib.Logic.PL.CNF.toThreeOccurrence` gives each occurrence a fresh
  copy and connects copies by binary implication cycles. For `m` clauses and `ℓ` literal
  occurrences it produces exactly `m + ℓ` clauses, `3ℓ` literal occurrences, and `ℓ` distinct
  variables. The implication cycles force each copy's value, so the reduction also preserves
  the exact number of satisfying assignments ({name}`modelCount_toThreeSATThree`). No planarity
  condition is imposed.
* Ordinary SAT with exactly three distinct variables per clause is NP-complete
  ({name}`EUThreeSAT_npComplete`). This strengthens the repeated-literal convention of
  {name}`ExactThreeSAT`. There is no occurrence bound: exact-three distinct-variable formulas
  with at most three occurrences per variable are always satisfiable by Hall's matching argument
  ({name}`Cslib.Logic.PL.CNF.satisfiable_of_exactThreeDistinct_of_count_le_three`). Accordingly,
  {name}`EUThreeSATThree.mem_P` decides this language by checking its syntax alone.
* Not-all-equal SAT requires both a true and a false literal in every clause
  ({name}`Cslib.Logic.PL.CNF.evalNAE`). NAE3SAT, with width at most three, is NP-complete
  ({name}`NAEThreeSAT_npComplete`). NAE EU3SAT, with exactly three distinct variables per clause,
  is NP-complete ({name}`NAEEUThreeSAT_npComplete`). NAE3SAT-3, with width at most three and at
  most three occurrences per variable, is NP-complete ({name}`NAEThreeSATThree_npComplete`).
  The last reduction reuses
  {name}`toThreeSATThree` and permits binary clauses. It does not establish hardness with
  both exact-three clauses and occurrence bound three.
* Orthogonal planar 3SAT-3 is NP-hard, both when a drawing must exist
  ({name}`PlanarThreeSATThree_npHard`) and when it is supplied
  ({name}`DrawnPlanarThreeSATThree_npHard`). Clauses have width at most three, binary clauses
  are allowed, and each variable has at most three literal occurrences. Routes are simple
  integer orthogonal paths whose full real supports meet only at common graph endpoints.
  The native polynomial-time compiler {name}`toDrawnPlanarThreeSAT` starts from ordinary 3SAT.
  Its paired implications and local templates have unique extensions, preserving the exact
  model count ({name}`modelCount_toPlanarThreeSAT`); only occurring variables are counted.
  For original size `S = clauses + literal occurrences + 1`, its grid sides are at most
  `13440*S`; formula size, route count, segment count and Manhattan wire length are quadratic
  in `S` ({name}`toDrawnPlanarThreeSAT_fits`, {name}`toDrawnPlanarThreeSAT_costs`).
* Positive 1-in-3SAT and positive 1-in-E3SAT are NP-complete, with or without the restriction
  that each variable occurs at most three times ({name}`PositiveOneInThreeSAT_npComplete`,
  {name}`PositiveOneInExactThreeSAT_npComplete`, {name}`PositiveOneInThreeSATThree_npComplete`,
  {name}`PositiveOneInExactThreeSATThree_npComplete`). Positive means no negated literals;
  exactly one literal occurrence must be true in each clause. E3 requires exactly three
  distinct variables per clause. The same compiler {name}`toPositiveOneInExactThreeSATThree`
  produces this strongest syntax and, on valid 3SAT inputs, preserves counts on occurring
  variables ({name}`oneModelCount_toPositiveOneInExactThreeSATThree`). For `m` source clauses
  and `ℓ` literal occurrences, it produces at most `169*(m + ℓ)` clauses and `507*(m + ℓ)`
  occurrences ({name}`size_toPositiveOneInExactThreeSATThree`).
* Planar positive 1-in-E3SAT-3 is NP-hard both with an existential drawing
  ({name}`PlanarPositiveOneInExactThreeSATThree_npHard`) and with its actual drawing supplied
  ({name}`DrawnPlanarPositiveOneInExactThreeSATThree_npHard`). The width-at-most-three planar
  variant is also NP-hard ({name}`PlanarPositiveOneInThreeSATThree_npHard`). These endpoints
  assert NP-hardness; the NP membership proofs above concern the nonplanar languages.
  The local positive replacement scales supplied grid sides from `W,H` to at most
  `1080000*(W + 1),1080000*(H + 1)` ({name}`SAT.ExactOne.positiveDrawing_fits`), with
  constant-factor formula and drawing costs ({name}`SAT.ExactOne.positiveDrawing_costs`).
  Composed with ordinary 3SAT planarization, grid sides remain linear and formula size,
  vertices, routes, segments and Manhattan wire length remain quadratic in
  `S = clauses + literal occurrences + 1`
  ({name}`toDrawnPlanarPositiveOneInExactThreeSATThree_fits`,
  {name}`toDrawnPlanarPositiveOneInExactThreeSATThree_costs`).
  The full compiler {name}`toDrawnPlanarPositiveOneInExactThreeSATThree` computes the actual
  formula, binary coordinates and route lists in native polynomial time
  ({name}`computableInPolyTime_toDrawnPlanarPositiveOneInExactThreeSATThree`). On valid 3SAT
  inputs it preserves the exact model count
  ({name}`oneModelCount_toPlanarPositiveOneInExactThreeSATThree`).
  The positive gadgets follow
  [Hunt et al., Theorem 3.8](https://arxiv.org/pdf/cs/9809017v1), Figures 3.4–3.5;
  their satisfying extensions are unique.
* Subset sum reduces to partition ({name}`polyTimeReducible_SubsetSum_Partition`,
  {name}`Partition_npComplete`), knapsack ({name}`polyTimeReducible_SubsetSum_Knapsack`,
  {name}`Knapsack_npComplete`), zero-one integer programming
  ({name}`polyTimeReducible_SubsetSum_ZeroOneIP`, {name}`ZeroOneIP_npComplete`) and sequencing
  with deadlines and penalties ({name}`polyTimeReducible_SubsetSum_JobSequencing`,
  {name}`JobSequencing_npComplete`). Partition reduces to weighted maximum cut through Karp's
  complete graph weighted by products ({name}`polyTimeReducible_Partition_MaxCut`,
  {name}`MaxCut_npComplete`).
* SAT reduces to independent set ({name}`polyTimeReducible_SAT_IndependentSet`,
  {name}`IndependentSet_npComplete`), which reduces to clique
  ({name}`polyTimeReducible_IndependentSet_Clique`, {name}`Clique_npComplete`) and vertex cover
  ({name}`polyTimeReducible_IndependentSet_VertexCover`, {name}`VertexCover_npComplete`).
* Vertex cover reduces to directed feedback vertex set by replacing every edge with two opposite
  arcs ({name}`polyTimeReducible_VertexCover_FeedbackVertexSet`,
  {name}`FeedbackVertexSet_npComplete`), which reduces to feedback arc set by splitting every
  vertex into an arc ({name}`polyTimeReducible_FeedbackVertexSet_FeedbackArcSet`,
  {name}`FeedbackArcSet_npComplete`).
* Vertex cover reduces to dominating set through a hub adjacent to a copy of every vertex, a
  pendant on the hub, and a vertex for every edge adjacent to the copies of its endpoints
  ({name}`polyTimeReducible_VertexCover_DominatingSet`, {name}`DominatingSet_npComplete`).
* SAT reduces to three-colorability ({name}`polyTimeReducible_SAT_ThreeColoring`,
  {name}`ThreeColoring_npComplete`) and to `k`-colorability for every `k ≥ 3`
  ({name}`polyTimeReducible_SAT_KColoring`, {name}`KColoring_npComplete`). Fixed colorability
  reduces to chromatic number, with the number of colors in the input
  ({name}`polyTimeReducible_KColoring_ChromaticNumber`, {name}`ChromaticNumber_npComplete`), which
  reduces to clique cover by complementing the graph
  ({name}`polyTimeReducible_ChromaticNumber_CliqueCover`, {name}`CliqueCover_npComplete`).
* SAT reduces to directed Hamiltonian paths and cycles ({name}`polyTimeReducible_SAT_DirHamPath`,
  {name}`DirHamPath_npComplete`, {name}`polyTimeReducible_SAT_DirHamCycle`,
  {name}`DirHamCycle_npComplete`), these reduce to their undirected versions
  ({name}`polyTimeReducible_DirHamPath_HamPath`, {name}`HamPath_npComplete`,
  {name}`polyTimeReducible_DirHamCycle_HamCycle`, {name}`HamCycle_npComplete`), and Hamiltonian
  cycles reduce to the traveling salesperson problem ({name}`polyTimeReducible_HamCycle_TSP`,
  {name}`TSP_npComplete`).
* SAT reduces to circuit satisfiability ({name}`SAT.polyTimeReducible_CircuitSAT`,
  {name}`CircuitSAT_npComplete`).

Chaining reductions with {name}`NPHard.trans` gives the hardness of any problem in the tree
directly from Cook–Levin:

```lean
example : NPHard (encPair encGraph encNat) Clique :=
  (CookLevin.SAT_npHard.trans polyTimeReducible_SAT_IndependentSet).trans
    polyTimeReducible_IndependentSet_Clique
```

The module documentation of `Complexity.Computability.Complexity.Reduction` indexes the same
results by problem, with the module to import for each.

# Boolean Constraint Languages

Schaefer's full Boolean dichotomy is proved for fixed finite constraint languages
over `Bool`, with arbitrary fixed relation arities and explicit binary instance
encoding. The six common-polymorphism cases are native P; otherwise the problem
is native NP-complete. Its structural ingredients include majority preservation
being equivalent to definability by clauses of width at most
two, with no auxiliary variables
({name}`Cslib.Logic.PL.isPolymorphism_majority_iff_exists_twoCNF`).

```lean
open Cslib.Logic Cslib.Logic.PL in
example {V : Type} [Finite V] (R : Set (V → Bool))
    (h : IsPolymorphism (Cslib.majority 3) R) :
    ∃ φ : CNF V, (∀ c ∈ φ, c.length ≤ 2) ∧
      ∀ a, a ∈ R ↔ φ.eval a = true :=
  (isPolymorphism_majority_iff_exists_twoCNF R).mp h
```

Here preservation applies the operation coordinatewise to satisfying tuples.
{name}`Cslib.Logic.IsPolymorphism.project` preserves it under existential
projection, and {name}`Cslib.Logic.IsPolymorphism.substitute` covers repeated
variables. Empty and nullary relations are allowed. This characterization alone
does not supply a polynomial-time certificate for constructing the formula.

For native complexity, {name}`CSPSAT` fixes a relation alphabet, arities and list
semantics, and rejects input scopes with incorrect lengths. Variable labels are
arbitrary natural numbers encoded in binary by {name}`encCSP` with {name}`encNat`.
Every fixed finite Boolean language is in NP ({name}`CSPSAT.mem_NP`). Common unary
constants and majority give native P via {name}`CSPSAT.mem_P_of_constant` and
{name}`CSPSAT.mem_P_of_majority`. Empty relations are handled explicitly.

```lean
open Cslib.Logic.PL in
example {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : CSP.HasPolymorphism arity sem (Cslib.majority 3)) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) :=
  CSPSAT.mem_P_of_majority encRel arity sem h
```

The language is fixed: template lookup is finite preprocessing. The reduction
instantiates its local clauses in native polynomial time and uses the existing
native 2SAT theorem; no solver hypothesis is needed.

The positive-arity Boolean clone classification is proved in
{module}`Complexity.Logics.BooleanClone.Classification`:
{name}`Cslib.Logic.BooleanClone.classification` covers every positive arity.
For a language lacking the six common operations,
{name}`Cslib.Logic.PL.CSP.projection_or_negation_of_not_hasSchaeferPolymorphism`
identifies every polymorphism as a projection or negated projection. This supplies
the algebraic ingredient used by the native hardness application below.

Post's functional-completeness criterion shares this same classification:
{name}`Cslib.Logic.BooleanClone.functionallyComplete_iff` characterizes generating
families by witnesses outside the five closed classes. Its completeness notion
quantifies over positive input arities, with unary constant functions. In particular,
NAND is complete in that sense; the stronger circuit notion also requires zero-input
functions. No circuit-size bound is asserted by this criterion.

For reductions between fixed Boolean languages,
{name}`Cslib.Logic.PL.CSP.exists_ppGadget_of_polymorphisms` constructs equality-free
primitive-positive gadgets for nonempty target relations with separating columns.
{name}`Cslib.Complexity.CSP.computableInPolyTime_replaceGadgetsGuarded` certifies
fixed-gadget replacement with binary labels, fresh auxiliaries and exact-arity
rejection. The hardness application must discharge nonemptiness, separation and
polymorphism invariance; general equality elimination is outside this gadget API.
The shared guard certificate is
{name}`Cslib.Complexity.CSP.computableInPolyTime_validArity` in
{module}`Complexity.Computability.PolyTime.CSP.Boolean`.

The hard branch is native and unconditional:
{name}`CSPSAT.npComplete_of_not_hasSchaeferPolymorphism` proves NP-completeness
for any fixed finite language lacking all six common operations. The proof imports
the proved clone classification, constructs gadgets for the eight self-dual
reference lifts of signed ternary clauses, and compiles them in native polynomial
time. Their nonemptiness and separating columns are proved internally. Empty and
nullary language relations remain allowed.

```lean
open Cslib.Logic.PL in
example {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    NPComplete (encCSP encRel encNat) (CSPSAT arity sem) :=
  CSPSAT.npComplete_of_not_hasSchaeferPolymorphism encRel arity sem h
```

{name}`CSPSAT.exists_linear_size_reduction_from_threeSAT` gives the actual
hardness reduction together with correctness, native polynomial-time computation
and `output.numVars + output.length ≤ C * input.length`. Thus the number of
distinct output variables plus constraints is at most a fixed constant times the
number of input clauses, and hence at most `C * (input.numVars + input.length)`.
The constant depends only on the fixed language. The bound holds on all raw CNFs,
including malformed and empty inputs; it concerns combinatorial counts rather
than encoded bit length or running time.

```lean
open Cslib.Logic.PL Turing.MultiTapeTM in
example {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬ CSP.HasSchaeferPolymorphism arity sem) :
    ∃ (f : CNF ℕ → CSP Rel ℕ) (C : ℕ),
      ComputableInPolyTime f encCNF (encCSP encRel encNat) ∧
      (∀ φ, φ ∈ ThreeSAT ↔ f φ ∈ CSPSAT arity sem) ∧
      (∀ φ, (f φ).numVars + (f φ).length ≤ C * (φ.numVars + φ.length)) := by
  obtain ⟨f, C, hp, hm, hs⟩ :=
    CSPSAT.exists_linear_size_reduction_from_threeSAT encRel arity sem h
  refine ⟨f, C, hp, hm, fun φ => (hs φ).trans ?_⟩
  apply Nat.mul_le_mul_left
  omega
```

The remaining tractable normal forms have proved native solvers:
{name}`Cslib.Logic.PL.isPolymorphism_and_iff_exists_hornCNF` and
{name}`Cslib.Logic.PL.isPolymorphism_or_iff_exists_dualHornCNF` characterize
AND/OR preservation. {name}`HornSAT.mem_P` and {name}`DualHornSAT.mem_P` decide
all-width formulas under {name}`encCNF`. Horn syntax counts positive occurrences,
so repeating a positive literal twice is rejected as non-Horn syntax.

{name}`Cslib.Logic.PL.isPolymorphism_parity_iff_exists_affineSystem`
characterizes ternary parity preservation by affine equations.
{name}`XORSAT.satisfiable_mem_P` certifies ordinary sparse XOR-SAT with binary
variable names; repeated variables cancel modulo two. The dense Gaussian
elimination algorithm and sparse compiler both have native certificates.
Their fixed-language compilers give {name}`CSPSAT.mem_P_of_and`,
{name}`CSPSAT.mem_P_of_or` and {name}`CSPSAT.mem_P_of_parity`, including repeated
scope variables, sparse binary labels and empty/nullary relations. Malformed
scopes are rejected before instantiation.

{name}`CSPSAT.schaefer_dichotomy` assembles all six cases and the hard branch.
Its unconditional corollary uses no assumption separating P and NP:

```lean
open Cslib.Logic.PL in
example {Rel : Type} [Finite Rel] (encRel : Rel ↪ List Bool)
    (arity : Rel → ℕ) (sem : Rel → List Bool → Bool) :
    CSPSAT arity sem ∈ P (encCSP encRel encNat) ∨
      NPComplete (encCSP encRel encNat) (CSPSAT arity sem) :=
  CSPSAT.mem_P_or_npComplete encRel arity sem
```

# Proving a Problem NP-Complete
%%%
tag := "clique-walkthrough"
%%%

A proof that a problem is NP-complete has five parts: a verifier, its cost, a reduction from a
known NP-complete problem, the reduction's cost, and the combination. Here they are for
{name}`Clique`, following `Complexity/Computability/Complexity/Problems/Clique.lean`.

## The Problem
%%%
tag := "walkthrough-problem"
%%%

An instance is a graph and a target size. The graph has a clique of that size when some set of
its declared vertices is pairwise adjacent and has exactly that many elements:

```lean
example : Clique = {x | ∃ S : Finset {v // v ∈ x.1.1},
    x.1.induced.IsNClique x.2 S} :=
  rfl
```

## The Verifier
%%%
tag := "walkthrough-verifier"
%%%

The certificate is a mask over the vertex list. The verifier keeps the masked vertices, checks
that there are as many as the target, and checks that each two of them are adjacent. Graph
problems that ask for a set of vertices with a pairwise property share this verifier,
{name}`Graph.verifySubset`, and its correctness lemma {name}`Graph.isVerifier_verifySubset`,
which leaves only the pairwise test to check:

```lean
example : IsVerifier (encPair encGraph encNat) Polynomial.X
    Clique.verifier Clique := by
  have h := Graph.isVerifier_verifySubset (rel := Graph.adjBool)
    (P := fun G u v => G.toSimpleGraph.Adj u v)
    (fun G u v _ => by rw [Graph.adjBool_eq_true_iff])
  intro x
  simp only [Clique, Set.mem_ofPred_eq, SimpleGraph.isNClique_iff,
    SimpleGraph.IsClique, Clique.verifier]
  exact h x
```

The certificate length is `Polynomial.X`, one bit per bit of the encoded instance, which is at
least one bit per vertex. The verifier is executable, so you can test it on a triangle:

```lean (name := triangle)
#eval Clique.verifier
  ((([0, 1, 2], [(0, 1), (1, 2), (0, 2)]), 3), [true, true, true])
```
```leanOutput triangle
true
```

## The Verifier's Cost
%%%
tag := "walkthrough-verifier-cost"
%%%

The verifier is written with certified operations, so its cost is automatic, and the two parts
give membership in {name}`NP`:

```lean
example : ComputableInPolyTime Clique.verifier
    (encPair (encPair encGraph encNat) encBits) encBool := by
  fun_prop

example : Clique ∈ NP (encPair encGraph encNat) :=
  ⟨Polynomial.X, Clique.verifier, by fun_prop, Clique.isVerifier⟩
```

## The Reduction
%%%
tag := "walkthrough-reduction"
%%%

A set of vertices is independent in a graph exactly when it is a clique in the complement graph
on the same vertices ({name}`Graph.compl`), so complementing reduces {name}`IndependentSet` to
{name}`Clique`. The correctness half is {name}`Graph.compl_mem_Clique_iff`. The complement keeps
every pair of distinct declared vertices that no edge joins:

```lean
example (G : Graph) : G.compl = (G.1, G.1.flatMap fun u =>
    (G.1.filter fun v => decide (u ≠ v ∧ (u, v) ∉ G.2 ∧ (v, u) ∉ G.2)).map
      fun v => (u, v)) :=
  rfl
```

## The Reduction's Cost
%%%
tag := "walkthrough-reduction-cost"
%%%

Unfolding the complement exposes list operations and membership tests, which `polytime`
certifies:

```lean
example : ComputableInPolyTime Graph.compl encGraph encGraph := by
  unfold Graph.compl
  polytime
```

## Putting It Together
%%%
tag := "walkthrough-combine"
%%%

The reduction is the triple of map, cost and correctness. Hardness transfers from
{name}`IndependentSet`, and membership with hardness is completeness:

```lean
example : PolyTimeReducible (encPair encGraph encNat)
    (encPair encGraph encNat) IndependentSet Clique :=
  ⟨fun x => (x.1.compl, x.2), by fun_prop,
    fun ⟨G, m⟩ => (Graph.compl_mem_Clique_iff G m).symm⟩

example : NPComplete (encPair encGraph encNat) Clique :=
  ⟨Clique.mem_NP,
    IndependentSet_npHard.trans polyTimeReducible_IndependentSet_Clique⟩
```

A new problem follows the same outline. Define it with its encoding, give a verifier and prove
{name}`IsVerifier`, certify the verifier, give a reduction map from a problem in the catalogue and
prove it correct, certify the map, and combine. Put it in its own module under
`Complexity/Computability/Complexity/Problems/`, next to the problems it reduces from.


# Planar Boolean CSP Prerequisites

Ordered cyclic differences are defined by
{name}`Cslib.BitString.cyclicDifference`. They determine a tuple up to simultaneous
complementation and have exactly the even-parity tuples as their image.
{name}`Cslib.BitString.cyclicIntegral` supplies a prefix-parity inverse:

```lean
open Cslib Cslib.BitString in
example {n : ℕ} (d : Fin n → Bool)
    (hd : parityOn Finset.univ d = false) :
    cyclicDifference (cyclicIntegral d) = d :=
  cyclicDifference_cyclicIntegral d hd
```

{name}`Cslib.BitString.IsDeltaMatroid` requires nonemptiness and one-sided
symmetric exchange. {name}`Cslib.BitString.IsEvenDeltaMatroid` adds common parity,
which may be odd. It forces exchange to flip two distinct coordinates:

```lean
open Cslib.BitString in
example {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Set (ι → Bool)} (hR : IsEvenDeltaMatroid R)
    {x y : ι → Bool} (hx : x ∈ R) (hy : y ∈ R)
    {i : ι} (hi : x i ≠ y i) :
    ∃ j, j ≠ i ∧ x j ≠ y j ∧ flipOn {i, j} x ∈ R :=
  hR.exchange hx hy hi
```

Twists, coordinate transport and feasible two-bit connectivity are also proved.
The difference tests show that ternary NAE has an even delta-matroid difference
relation. These are mathematical prerequisites; a planar embedding algorithm,
general edge-CSP solver and full planar dichotomy remain to be formalized.


# Indexed CSP and Table Operations

{name}`Cslib.Logic.PL.CSP.Occurrence` preserves constraint and scope positions,
including repeated variables and identical constraints. Given a supplied value
`outside : D`, consistent valid local labels reconstruct precisely a global CSP
model. Reconstruction uses `outside` at nonoccurring variables; this hypothesis
matters when the domain may be empty. The native incidence graph retains one
edge per argument; it never expands sparse binary names to a range.

```lean
open Cslib.Logic.PL in
example {Rel V D : Type} (sem : Rel → List D → Bool)
    (F : CSP Rel V) (outside : D) :
    F.Satisfiable sem ↔ ∃ l : F.OccurrenceLabeling D,
      CSP.ValidLabeling sem l ∧ CSP.ConsistentLabeling l :=
  CSP.satisfiable_iff_exists_labeling sem outside
```

{name}`Cslib.Logic.PL.CSP.Table` is an explicit relation alphabet for the same CSP
lists. Its semantics rejects malformed row widths. Local contraction projects
outside coordinates and appends a connector bit for zero or one internal
change. The local native certificate does not yet prove blossom correctness.
Exactly-one generation takes a scope list whose length funds its quadratic
output:

```lean
open Cslib.Logic.PL.CSP Cslib.Complexity.CSP in
example (scope : List ℕ) (hs : scope ≠ []) :
    ∃ row, (Table.exactlyOne scope).sem row = true :=
  (Table.exists_sem_exactlyOne scope).mpr
    (List.length_pos_iff.mpr hs)
```

```lean
open Cslib.Complexity Cslib.Logic.PL.CSP
  Cslib.Complexity.CSP Turing.MultiTapeTM in
example : ComputableInPolyTime (Table.exactlyOne (V := ℕ))
    (encList encNat) encTable :=
  computableInPolyTime_tableExactlyOne
```

{name}`Cslib.Complexity.Graph.RotationSystem` retains indexed ends of loops and
parallel edges, all face orbits including fixed points, and cyclic vertex orders.
{name}`Cslib.Complexity.CSP.RespectsArgumentOrder` requires the constraint-side
rotation to follow the scope's cyclic order. This rotation structure imposes no
genus-zero condition and supplies no planarity recognizer or solver.


# Finite Ordered Rotation Certificates

{name}`Cslib.Complexity.Graph.RotationCertificate` stores one binary successor
index per indexed dart. Its checker validates a supplied permutation and vertex
rotation, then checks {name}`Cslib.Complexity.Graph.RotationSystem.NumericalGenusZero`:
`V + F = E + 2` in each edge component. Faces include fixed-point orbits.
Isolated vertices use `V = 1, E = 0, F = 1` without inventing darts.

The CSP checker also preserves the actual cyclic scope order. A ternary mirror
can pass numerical genus zero while failing this order condition:

```lean
open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP in
example : verifyRotationCertificate
    ([((), [0, 1, 2])] : CSP Unit ℕ) ⟨[0, 3, 2, 5, 4, 1]⟩ = true :=
  by decide
```

```lean
open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP in
example : verifyRotationCertificate
    ([((), [0, 1, 2])] : CSP Unit ℕ) ⟨[0, 5, 2, 1, 4, 3]⟩ = false :=
  by decide
```

{name}`Cslib.Complexity.CSP.exists_bounded_rotationCertificate_iff` proves that
ordered numerical genus-zero rotations exist exactly when a bounded certificate
is accepted. The explicit graph bound is `10 * (N + 1)^2` bits for the complete
`encGraph` bit length `N`; its composition with the incidence construction is
polynomial in the original CSP bit length. The full supplied-certificate checker
has native polynomial time, including on malformed tables:

```lean
open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP
  Turing.MultiTapeTM in
example : ComputableInPolyTime
    (fun p : CSP Unit ℕ × Graph.RotationCertificate =>
      verifyRotationCertificate p.1 p.2)
    (encCSPRotationCertificate encUnit encNat) encBool :=
  computableInPolyTime_verifyRotationCertificate encUnit encNat
```

Original variable labels remain binary. Iteration uses actual list lengths,
never a maximum label or supplied successor index. Nullary port order is
vacuous; semantic rejection and exact relation arity remain separate guards.
These supplied-certificate theorems leave bare-instance construction, geometric
correspondence, an edge solver and the dichotomy open. The finite duality and
Boolean difference interface is proved below.


# Indexed Duality and Boolean Difference Lifting

Import `Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting`
for the complete graph entry point. The actual dual keeps listed edge positions,
including loops and parallel occurrences, and gives every source face its least
actual dart index as a vertex name. Its vertex permutation is the source face
successor. Complete face/incident-vertex and component bijections establish:

```lean
open Cslib.Complexity in
example {G : Graph} (r : Graph.RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1) :
    r.dualRotation.NumericalGenusZero ↔ r.NumericalGenusZero :=
  r.numericalGenusZero_dual_iff hG
```

The endpoint guard is essential. Isolated source vertices have no darts and
are omitted by dualization; their conventional Euler equation is trivial.
Empty and disconnected graphs, duplicate declarations and sparse names are
covered. Face parity counts dart occurrences with boundary multiplicity.
For an indexed Boolean edge assignment, all face parities vanish exactly when
it is the endpoint XOR of vertex spins:

```lean
open Cslib.Complexity in
example {G : Graph} (r : Graph.RotationSystem G)
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.1)
    (hgenus : r.NumericalGenusZero) (x : Fin G.2.length → Bool) :
    r.FaceEven x ↔ ∃ spin : ℕ → Bool, G.edgeGradient spin = x :=
  r.faceEven_iff_exists_vertexSpins hG hgenus x
```

The proof discharges the characteristic-two incidence-rank and connectivity
facts internally. The gradient-to-parity direction telescopes without either
premise:

```lean
open Cslib.Complexity in
example {G : Graph} (r : Graph.RotationSystem G) (spin : ℕ → Bool) :
    r.FaceEven (G.edgeGradient spin) :=
  r.faceEven_edgeGradient spin
```

`ComplexityTests/RotationDual.lean` contains concrete bridge, loop, digon,
torus and disconnected sparse-name cases. These are finite combinatorial
results. Geometric realization, bare recognition, native compilation, the
whole cyclic-difference CSP reduction and recursive solver remain open.


# Ordered Incidence-to-Polygon Rotations

Import `Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Euler`.
The actual `polygonGraph` puts one edge between successive variables of each
cyclic scope, retaining occurrence positions and dense variable names. Unary
scopes become loops; repeated names and identical constraints stay distinct.
Given an incidence rotation respecting the original argument order, every
polygon face is an indexed constraint face or an original incidence face:

```lean
open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP in
noncomputable example {Rel V : Type} [DecidableEq V] (F : CSP Rel V)
    (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) :
    (polygonRotation r).Face ≃ Fin F.length ⊕ r.Face :=
  polygonFaceEquiv r hOrder hPos
```

Singleton face orbits are included. With positive actual scopes, components
correspond and the exact per-component counts preserve numerical genus zero:

```lean
open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.CSP in
example {Rel V : Type} [DecidableEq V] (F : CSP Rel V)
    (r : Graph.RotationSystem (incidenceGraph F))
    (hOrder : RespectsArgumentOrder r)
    (hPos : ∀ i : Fin F.length, 0 < F[i.val].2.length) :
    (polygonRotation r).NumericalGenusZero ↔ r.NumericalGenusZero :=
  numericalGenusZero_polygon_iff r hOrder hPos
```

The graph has exactly one edge per occurrence and at most that many variable
vertices. The bridge covers empty/disconnected bodies and sparse names;
positivity is about actual scopes and assumes no relation semantics or arity
contract. Nullary constraints require separate handling.
`ComplexityTests/CSPPrimalRotation.lean` checks loops, repeated positions,
identical constraints, malformed arity, the positivity guard and a toroidal
rotation. The finite graph is explicit; abstract rotation inverses and face
bijections are proof data. Native compilation, geometric realization and bare
recognition remain open, along with the complete planar CSP reduction/solver.


# Delta-Matroid Closure for Local Contraction

{name}`Cslib.BitString.IsDeltaMatroid.comp` and
{name}`Cslib.BitString.IsEvenDeltaMatroid.comp` prove relational composition
along finite shared coordinates. They require a nonempty output: nonempty input
relations can disagree on the shared values. The proofs use the one-sided
exchange axiom and permit empty external coordinate types.

For the actual guarded table operation,
{name}`Cslib.Logic.PL.CSP.Table.isEvenDeltaMatroid_contract` supplies the
mathematical invariant used by blossom contraction. A feasible reference and
distinct in-range internal positions are enough; the reference witnesses output
nonemptiness internally:

```lean
open Cslib.BitString Cslib.Logic.PL.CSP in
example {table : Table} {reference : List Bool} {positions : List ℕ}
    (hR : IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem table))
    (hc : Table.canContract table reference positions = true) :
    IsEvenDeltaMatroid (booleanRelation Table.arity Table.sem
      (Table.contract table reference positions)) :=
  Table.isEvenDeltaMatroid_contract hR hc
```

The new connector's exactly-one relation is even for every nonempty scope,
with odd common parity. Empty scopes are excluded. These local mathematical
closures do not prove whole-blossom lifting, the edge solver, or its native cost.


# Prefix-Valid Edge-CSP Augmentation

{name}`Cslib.Logic.PL.CSP.defects` counts distinct inconsistent variables.
{name}`Cslib.Logic.PL.CSP.Walk.IsFWalk` requires distinct endpoints, consistent
internal variables, and validity after every variable-ended prefix. An
augmenting walk removes exactly two defects:

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP in
example {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    {f : OccurrenceLabeling F Bool} {w : Walk F}
    (hw : w.IsAugmenting sem f) :
    (defects (w.flip f)).card + 2 = (defects f).card :=
  hw.card_defects_flip_add_two h
```

For even delta-matroid constraints,
{name}`Cslib.Logic.PL.CSP.EdgeInstance.augmentingWalk` is a total deterministic
two-phase routine. Its correctness requires an improving valid comparison
labeling as input; it does not search for that labeling. The combined exchange
count is bounded by half the initial occurrence Hamming distance.

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP in
example {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (h : EdgeInstance F) {sem : Rel → List Bool → Bool}
    (hM : EdgeInstance.EvenConstraints sem F)
    {f : OccurrenceLabeling F Bool} :
    IsOptimalLabeling sem f ↔ ValidLabeling sem f ∧
      ¬ ∃ w : Walk F, w.IsAugmenting sem f :=
  h.isOptimalLabeling_iff_no_augmentingWalk hM
```

The test module also rejects final-only validity. A complete solver still needs
DAG/forest/blossom search and certification of the complete solver.


For explicit tables, {name}`Cslib.Complexity.CSP.EdgeAugmenting.run` takes the CSP,
two finite occurrence buffers and the excluded start. Its ordinary native certificate
covers the full framed input, including malformed buffers and sparse binary names:

```lean
open Cslib.Complexity.CSP.EdgeAugmenting Turing.MultiTapeTM in
example : ComputableInPolyTime (fun input => (run input).isSome)
    encInput encBool := by fun_prop
```

{name}`Cslib.Complexity.CSP.EdgeAugmenting.run_eq` identifies its output with the
mathematical routine when buffer widths match.
{name}`Cslib.Complexity.CSP.EdgeAugmenting.run_spec` supplies an actual augmenting
walk and the combined exchange bound given a valid improving comparison.
A `none` output does not establish unsatisfiability. The fresh forest search below
uses only the base labeling and stops at its first blossom or augmentation.
The complete behavioral clients are in `ComplexityTests/EdgeCSPAugmentingNative.lean`.


# Timestamped DAG Search Prerequisites

{name}`Cslib.Logic.PL.CSP.DAG.IsFDAG` combines base validity with all six KKR
invariants. Copies use original constraint positions and timestamps; arcs use
actual argument occurrences. Supported isolated nodes are retained. Finite ranks
can be made injective without changing any required comparison.

The earliest-copy deletion and rerooting theorems preserve the invariants after
a feasible pair flip, with the source's leaf and degree hypotheses explicit.
Rerooting keeps unselected children. The paired-copy theorem gives the directed
path argument; original constraints may recur at distinct timestamps. Prefix
validity is a conclusion, not part of the path certificate:

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.DAG in
example {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    {sem : Rel → List Bool → Bool} {f : OccurrenceLabeling F Bool}
    {T : DAG F} {w : Walk F} {time : Occurrence F → ℕ}
    (hp : DirectedPath T w time) (hT : T.IsFDAG sem f)
    (hM : EdgeInstance.EvenConstraints sem F) (n : ℕ) :
    ValidLabeling sem ((w.take n).flip f) := hp.valid_take hT hM n
```

{name}`Cslib.Logic.PL.CSP.DAG.DirectedPath.isFWalk` also requires distinct
endpoints and original internal consistency. Lemma 43 is formalized by
{name}`Cslib.Logic.PL.CSP.DAG.IsFDAG.flip_walk_of_no_prefix_extension`, using
actual prefix extensions against every used incidence. Its direct-exchange proof
handles timestamp zero without adding a smaller timestamp.

For assembly, trail reversal preserves the underlying trail:

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP in
example {Rel V : Type} {F : CSP Rel V} {w : Walk F}
    (hw : w.IsWalk) : w.reverse.IsWalk := hw.reverse
```

Arbitrary f-walk reversal need not preserve prefix validity, even for even
delta-matroid relations. Operation tests give a counterexample. These results
feed the fresh forest search below. Whole-blossom contraction/lifting, native
recursive solving and the full planar dichotomy remain open.


# Fresh Forest Search

{name}`Cslib.Logic.PL.CSP.Forest.search` starts from the actual defective variables,
without an improving comparison. Its positional log keeps copied constraints and
zero-based timestamps. It stops at exhaustion, an augmentation or a blossom.
{name}`Cslib.Logic.PL.CSP.Forest.search_terminal_isFDAG` proves both terminal DAG
invariants from the edge-instance condition and base validity, without evenness.

The three outcome theorems add even delta-matroid constraints, permitting odd
local common parity. Exhaustion certifies genuine optimality:

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest in
example {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {es : Log F}
    (hr : search sem f = .exhausted es) : IsOptimalLabeling sem f :=
  search_exhausted_isOptimalLabeling sem f hF hf hM hr
```

An actual returned augmentation is prefix-valid, its flip is valid, and it removes
exactly two defects:

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest in
example {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {m : Meeting F}
    (hr : search sem f = .augment m) :
    m.walk.IsAugmenting sem f ∧ ValidLabeling sem (m.walk.flip f) ∧
      (defects (m.walk.flip f)).card + 2 = (defects f).card :=
  search_augment_correct sem f hF hf hM hr
```

A blossom result certifies the data actually computed by the extractor. Preparation
preserves validity and defect count. Its cycle has distinct copied steps, and
the actual timestamps are distinct:

```lean
open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Forest in
example {Rel V : Type} [DecidableEq V] {F : CSP Rel V}
    (sem : Rel → List Bool → Bool) (f : OccurrenceLabeling F Bool)
    (hF : EdgeInstance F) (hf : ValidLabeling sem f)
    (hM : EdgeInstance.EvenConstraints sem F) {m : Meeting F}
    (hr : search sem f = .blossom m) :
    ∃ b, m.blossomData = some b ∧ b.cycle.IsBlossom sem (b.prepare.flip f) ∧
      b.times.Nodup ∧ ValidLabeling sem (b.prepare.flip f) ∧
      (defects (b.prepare.flip f)).card = (defects f).card := by
  obtain ⟨b, hb, hbl, hv, hd⟩ := search_blossom_correct sem f hF hf hM hr
  have ht := search_trace sem f hF
  rw [hr] at ht
  exact ⟨b, hb, hbl, ht.blossom_times_nodup hb, hv, hd⟩
```

No supplied forest/event invariant or finite universe of variable names is needed.
Both variable and constraint least-common-ancestor cases are proved.
{name}`Cslib.Logic.PL.CSP.Walk.DistinctCopies` forbids sharing a copied node
between cycle steps; original constraints may recur at different timestamps.
The graph union alone admits an invalid-prefix counterexample, checked in
`ComplexityTests/EdgeCSPBlossomCopies.lean`. The cycle certificate also retains
the pivot, feasibility and no shortcuts;
its validity does not follow from reversing an arbitrary f-walk. Exhaustion uses
an alternative exchange-counting proof of KKR Lemma 45. The preparation proof uses
chronological prefix transfer and Lemma 37 rerooting.

Complete actual-run clients are in `ComplexityTests/EdgeCSPForestEvents.lean`,
`ComplexityTests/EdgeCSPForestTerminal.lean` and
`ComplexityTests/EdgeCSPForestOptimality.lean`. They include nonempty preparation,
repeated original constraints, timestamp zero, odd parity and sparse labels.
These mathematical endpoints compose with the native compiler below. Whole-blossom
contraction/lifting, recursive solving and the full planar dichotomy remain separate.


# Native Fresh Forest Search

Import `Complexity.Computability.PolyTime.CSP.Edge.Forest.Spec` for the complete
fresh-search entry point. Its input is an explicit-table CSP with binary original
names and one finite occurrence-bit buffer. Table arities and output indices are
binary, while internal constraint/scope positions are unary. All clocks are
funded by actual lists, including on malformed input:

```lean
open Cslib.Complexity.CSP.EdgeForest Turing.MultiTapeTM in
example : ComputableInPolyTime run encInput (encOption encResultCode) := by
  fun_prop
```

Correct buffer width alone gives exact agreement and decoding, without semantic
or forest-invariant hypotheses:

```lean
open Cslib.Logic.PL.CSP Cslib.Complexity.CSP Cslib.Complexity.CSP.EdgeForest in
example (input : Input)
    (hw : input.labels.length = (incidenceList input.body).length) :
    (run input).bind (decode input.body) =
      some (Forest.search Table.sem
        (EdgeAugmenting.labeling input.body input.labels)) :=
  decode_run input hw
```

{name}`Cslib.Complexity.CSP.EdgeForest.run_eq_none_iff` proves that `none` means
width mismatch. A correctly sized buffer never exhausts the clock. Logs, roots,
partial current copies and timestamps are retained; decoding external codes
rejects invalid indices. This establishes no semantic correctness for an event
on invalid input. With the model hypotheses, the composed specification applies
to the actual decoded result:

```lean
open Cslib.Logic.PL.CSP Cslib.Complexity.CSP Cslib.Complexity.CSP.EdgeForest in
example (input : Input)
    (hw : input.labels.length = (incidenceList input.body).length)
    (hF : EdgeInstance input.body)
    (hf : ValidLabeling Table.sem
      (EdgeAugmenting.labeling input.body input.labels))
    (hM : EdgeInstance.EvenConstraints Table.sem input.body)
    {m : Forest.Meeting input.body}
    (hr : (run input).bind (decode input.body) = some (.augment m)) :
    m.walk.IsAugmenting Table.sem
      (EdgeAugmenting.labeling input.body input.labels) := by
  have hs := run_spec input hw hF hf hM
  rw [hr] at hs
  exact hs.1
```

The same specification supplies optimality for exhaustion and valid
count-preserving preparation for a blossom. This is a native fresh-search routine,
without an improving comparison input. The existing augmentation API is preserved
through the shared buffer module. `ComplexityTests/EdgeCSPForestNative.lean` checks
actual executions, including an end-to-end valid augmentation to zero defects.
Whole-blossom contraction/lifting, recursive solving, geometric recognition and
the full planar dichotomy remain open.


# Finite Crossover Gadget Semantics

{name}`Cslib.BitString.cross` equates opposite cyclic ports.
{name}`Cslib.BitString.nearCross` additionally accepts `0001` and `1110`.
{name}`Cslib.BitString.IsStandardizedInconsistent` has exactly eight shapes.
The literal Dvořák–Kupec Figure 1(a) gadget targets CROSS or NEAR-CROSS according
to which optional complementary pairs occur:

```lean
open Cslib.BitString Cslib.Logic.PL.CSP.Crossover in
example : figureOneARelation (standardizedRelation true false false) =
    nearCross := figureOneARelation_standardized true false false
```

{name}`Cslib.Logic.PL.CSP.Crossover.figureOneAStandardized` exposes the selected
target as an ordinary primitive-positive gadget. Figure 1(b) then defines CROSS
from NEAR-CROSS using one existential auxiliary:

```lean
open Cslib.BitString Cslib.Logic.PL.CSP.Crossover in
example : ∃ b, figureOneB.body.eval nearSem
    (Sum.elim ![false, true, false, true] b) = true :=
  (figureOneB.correct _).mp (by decide)
```

Both bodies retain the source diagram's numbered port order and use guarded
scope widths. These results concern finite semantics; geometric realization,
planar substitution, hardness and a new native runtime certificate remain open.


# Ordered Cyclic-Obstruction Normalization

{name}`Cslib.Logic.PL.CSP.Normalization.exists_construction` treats arbitrary arity.
Its input relation is nonempty and self-complementary, with a cyclic-difference
relation failing the even delta-matroid axiom. It proves arity at least four and
produces an ordered recipe and an actual gadget over the original relation and
disequality. The finite constraint, scope-occurrence and auxiliary bounds compose:

```lean
open Cslib.BitString Cslib.Logic.PL.CSP in
example {n : ℕ} (R : Set (Fin n → Bool)) (hne : R.Nonempty)
    (hsc : IsSelfComplementary R)
    (hbad : ¬IsEvenDeltaMatroid (cyclicDifferenceRelation R)) :
    ∃ Q : Set (Fin 4 → Bool), IsStandardizedInconsistent Q ∧
      ∃ g : PPGadget (Normalization.arity n) (Normalization.sem R) Q,
        g.body.length ≤ 1 + 2 * n ∧ g.body.vars.length ≤ 5 * n ∧
          g.numAux ≤ 3 * n - 4 := by
  obtain ⟨_, ⟨c⟩⟩ := Normalization.exists_construction R hne hsc hbad
  exact ⟨c.target, c.standardized, c.gadget, c.body_bounds.1, c.body_bounds.2,
    c.numAux_bound⟩
```

The program uses cyclic rotations, adjacent zero-conditioned identifications and
the specific cap identifying old ports 1 and 3 while hiding old port 2. It keeps
the resulting free-port order. The initial body contains one original literal and
one or two disequality spokes per original port; later steps relabel scopes.
The bounds count constraints, scope occurrences and allocated auxiliaries, including
unused labels. They assert neither native runtime nor binary encoded size.

This is an original combinatorial reconstruction of the omitted argument behind
Dvořák–Kupec Lemma 6, not its full planar-expressibility conclusion. Geometric
realization and the full planar theorem remain open. Complete nonvacuous clients
are in `ComplexityTests/PlanarNormalization.lean`.


# Original-Language Nonselfdual Gadgets

{name}`Cslib.Logic.PL.CSP.NonSelfDual.exists_oneHotGadget` constructs an actual
one-in-three gadget over the original language. It requires absence of all six
common Schaefer polymorphisms and of unary complement. Pins and disequality are
derived internally, and the language relations may have arbitrary arity:

```lean
open Cslib.BitString Cslib.Logic.PL.CSP in
example {Rel : Type} (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬HasSchaeferPolymorphism arity sem)
    (hn : ¬HasPolymorphism arity sem (fun a : Fin 1 → Bool => !(a 0))) :
    Nonempty (PPGadget arity sem (oneHotRelation (Fin 3))) :=
  NonSelfDual.exists_oneHotGadget h hn
```

Disequality needs only the first hypothesis, including when unary complement
preserves the language:

```lean
open Cslib.Logic.PL.CSP in
example {Rel : Type} (arity : Rel → ℕ) (sem : Rel → List Bool → Bool)
    (h : ¬HasSchaeferPolymorphism arity sem) :
    Nonempty (PPGadget arity sem RelationMinor.disequality) :=
  RelationMinor.exists_disequalityGadget h
```

{name}`Cslib.Logic.PL.CSP.RelationMinor.Construction.gadget` interprets each finite
ordered construction tree on actual original-language bodies. The final triangle
appends a ternary body and three NAND bodies on `(0,1)`, `(1,2)`, `(2,0)`; each use
receives fresh auxiliaries. Projection retains survivor order, and cyclic rotation
retains orientation. The arbitrary-arity parity and majority minor arguments are
original reconstructions of the proof omitted from Dvořák–Kupec Lemma 4, printed
pp. 438–439. The constants descent follows Lemma 3, pp. 437–438.

This proves finite primitive-positive semantics. Witness selection is fixed-language
data, without a uniform preprocessing bound. Geometric realization, ordered planar
substitution, native hardness transfer and the full dichotomy remain open. Complete
clients, including a one-symbol language without primitive pins or disequality,
are in `ComplexityTests/PlanarConstructionGadget.lean`.
