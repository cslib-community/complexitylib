/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import VersoManual
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.CircuitSAT
import Complexity.Computability.Complexity.Problems.Clique
import Complexity.Computability.Complexity.Problems.Coloring
import Complexity.Computability.Complexity.Problems.ExactThreeSAT
import Complexity.Computability.Complexity.Problems.Hamiltonian.Directed
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Complexity.Problems.IntegerProgramming
import Complexity.Computability.Complexity.Problems.Knapsack
import Complexity.Computability.Complexity.Problems.Partition
import Complexity.Computability.Complexity.Problems.PlanarPositiveOneInThreeSAT
import Complexity.Computability.Complexity.Problems.PlanarThreeSATThree
import Complexity.Computability.Complexity.Problems.SubsetSum
import Complexity.Computability.Complexity.Problems.TSP
import Complexity.Computability.Complexity.Problems.ThreeSAT
import Complexity.Computability.Complexity.Problems.ThreeSATThree
import Complexity.Computability.Complexity.Problems.VertexCover
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
* 3SAT reduces to {name}`ThreeSATThree` via {name}`toThreeSATThree`
  ({name}`ThreeSATThree_npComplete`). Its clauses have at most three literals, including binary
  clauses, and every variable has at most three literal occurrences. Repetitions within a clause
  count separately. {name}`Cslib.Logic.PL.CNF.toThreeOccurrence` gives each occurrence a fresh
  copy and connects copies by binary implication cycles. For `m` clauses and `ℓ` literal
  occurrences it produces exactly `m + ℓ` clauses, `3ℓ` literal occurrences, and `ℓ` distinct
  variables. The implication cycles force each copy's value, so the reduction also preserves
  the exact number of satisfying assignments ({name}`modelCount_toThreeSATThree`). No planarity
  condition is imposed.
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
  {name}`Knapsack_npComplete`) and zero-one integer programming
  ({name}`polyTimeReducible_SubsetSum_ZeroOneIP`, {name}`ZeroOneIP_npComplete`).
* SAT reduces to independent set ({name}`polyTimeReducible_SAT_IndependentSet`,
  {name}`IndependentSet_npComplete`), which reduces to clique
  ({name}`polyTimeReducible_IndependentSet_Clique`, {name}`Clique_npComplete`) and vertex cover
  ({name}`polyTimeReducible_IndependentSet_VertexCover`, {name}`VertexCover_npComplete`).
* SAT reduces to three-colorability ({name}`polyTimeReducible_SAT_ThreeColoring`,
  {name}`ThreeColoring_npComplete`) and to `k`-colorability for every `k ≥ 3`
  ({name}`polyTimeReducible_SAT_KColoring`, {name}`KColoring_npComplete`).
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
