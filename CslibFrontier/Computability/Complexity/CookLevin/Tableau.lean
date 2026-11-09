/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Feature
public import CslibFrontier.Logics.Propositional.CNF.ExactlyOne

/-!
# The Cook–Levin tableau

Given a deterministic multi-tape machine `tm` over the binary alphabet, a fixed input prefix `u`,
a certificate length `L` and a number of steps `T`, `tableau tm u L T` is a formula in
conjunctive normal form that is satisfiable exactly when some certificate `w` of length `L`
makes `tm`, started on `u ++ w`, halt within `T` steps with output `[true]`
(`Cslib.Complexity.CookLevin.tableau_satisfiable_iff`, in
`CslibFrontier/Computability/Complexity/CookLevin/Correctness.lean`). It has
exactly one satisfying assignment (of its variables) for each such certificate
(`Cslib.Complexity.CookLevin.modelCount_tableau`, in
`CslibFrontier/Computability/Complexity/CookLevin/Parsimonious.lean`).

The formula describes the first `T + 1` configurations of the run directly, in the model of
`Turing.MultiTapeTM`: a read-only input tape, `k` two-way infinite work tapes, and a write-only
output tape. Its variables say which features (`Turing.MultiTapeTM.Feature`) hold at which time:
the state, the input head, the work heads and work cells in the window `|z| ≤ T` (a head moves at
most one cell per step), the view of the output, the symbols read and the situation of a step.
The only other variables are the certificate bits.

The clauses fix the initial configuration, ask that exactly one basic feature of each group hold
at each time (`Turing.MultiTapeTM.Feature.groups`), force the symbols read and the situation that
actually hold to be true, and impose the step equation: each term of
`Turing.MultiTapeTM.Feature.stepTerms` at time `t` implies its feature at time `t + 1`. For
satisfiability, forcing the symbols read and the situations in one direction suffices, because
situations occur only positively in the terms
(`Turing.MultiTapeTM.Feature.mem_basic_of_mem_stepTerms`). The uniqueness clauses force the
converse: each head reads at most one symbol, and a true situation has its state and symbols read
true. Every variable of the tableau is then determined by the certificate bits, which makes the
reduction parsimonious (`Cslib.Complexity.CookLevin.modelCount_tableau`, in
`CslibFrontier/Computability/Complexity/CookLevin/Parsimonious.lean`). No conversion to a
single-tape
or oblivious machine is needed: the
action of a step depends on the situation only, and every tape applies its part of the action
locally.

The definitions are noncomputable: the transition function of `Turing.MultiTapeTM` is chosen from
its transition relation, and the states and situations are enumerated through `Finset.toList` in
an arbitrary order. Both depend on the machine only, so a machine producing the tableau can store
them in a table; the enumerations that depend on the input (`Turing.windowList`, `List.range`) are
explicit lists. Only the set of satisfying assignments matters for correctness.

## Main definitions

* `Cslib.Complexity.CookLevin.Var`.
* `Cslib.Complexity.CookLevin.tableau`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Section 2.3.
* [C. H. Papadimitriou, *Computational Complexity*][Papadimitriou94], Theorem 8.2.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin

open Turing Turing.MultiTapeTM Cslib.Logic.PL

/-- The variables of the tableau for a machine with `k` work tapes and states in `State`. -/
inductive Var (k : ℕ) (State : Type) where
  /-- The feature `φ` holds at time `t`. -/
  | holds (t : ℕ) (φ : Feature k State)
  /-- The `j`-th bit of the certificate. -/
  | cert (j : ℕ)
  deriving DecidableEq

variable {k : ℕ} {State : Type}

theorem Var.holds_right_injective (t : ℕ) :
    Function.Injective (Var.holds (k := k) (State := State) t) :=
  fun _ _ h => (Var.holds.inj h).2

/-! ### Clauses -/

section Clauses

variable (tm : MultiTapeTM k Bool State) (u : List Bool) (L T : ℕ)

/-- The initial configuration: state `q₀`, input head on the first input cell, every work head
on cell `0`, blank work tapes, empty output. -/
def initClauses : CNF (Var k State) :=
  [[(.holds 0 (.state (some tm.q₀)), true)], [(.holds 0 (.inPos 1), true)],
    [(.holds 0 (.out .empty), true)]] ++
    (List.finRange k).flatMap fun i =>
      [(.holds 0 (.head i 0), true)] ::
        (windowList T).map fun z => [(.holds 0 (.cell i z none), true)]

/-- Exactly one basic feature of each group holds at time `t`. -/
noncomputable def oneHotClauses [Fintype State] [DecidableEq State] (t : ℕ) : CNF (Var k State) :=
  (Feature.groups (u.length + L) T).flatMap fun g => CNF.exactlyOne (g.map (.holds t))

/-- The input head at position `j` reads the input symbol there: a fixed symbol of `u` or a blank
end marker, or a certificate bit. -/
def inputClauses (t j : ℕ) : CNF (Var k State) :=
  if j = 0 ∨ u.length + L < j then
    [Clause.imp [.holds t (.inPos j)] (.holds t (.inRead none))]
  else if j ≤ u.length then
    [Clause.imp [.holds t (.inPos j)] (.holds t (.inRead u[j - 1]?))]
  else
    [Clause.impLits [(.holds t (.inPos j), true), (.cert (j - 1 - u.length), true)]
        (.holds t (.inRead (some true))),
      Clause.impLits [(.holds t (.inPos j), true), (.cert (j - 1 - u.length), false)]
        (.holds t (.inRead (some false)))]

/-- The symbols under the heads at time `t`: the symbol a head reads, from its position and the
cell there, is true. -/
def readClauses (t : ℕ) : CNF (Var k State) :=
  ((List.finRange k).flatMap fun i => (windowList T).flatMap fun z =>
      Feature.symbols.map fun s =>
        Clause.imp [.holds t (.head i z), .holds t (.cell i z s)] (.holds t (.read i s))) ++
    (List.range (u.length + L + 2)).flatMap (inputClauses u L t)

/-- The situation at time `t`: a situation whose state and symbols read are true is true. -/
noncomputable def sitClauses [Fintype State] (t : ℕ) : CNF (Var k State) :=
  Feature.situations.map fun y =>
    Clause.imp (.holds t (.state (some y.1)) :: .holds t (.inRead y.2.1) ::
      (List.finRange k).map fun i => .holds t (.read i (y.2.2 i))) (.holds t (.sit y))

/-- The symbols read and the situation at time `t` are unique: each work head and the input head
read at most one symbol, and a true situation has its state and symbols read true. With the read
and situation clauses, the symbols read and the situation that are true are then exactly those
that hold. -/
noncomputable def uniqueClauses [Fintype State] [DecidableEq State] (t : ℕ) :
    CNF (Var k State) :=
  (List.finRange k).flatMap (fun i =>
      CNF.atMostOne (Feature.symbols.map fun s => .holds t (.read i s))) ++
    CNF.atMostOne (Feature.symbols.map fun s => .holds t (.inRead s)) ++
    Feature.situations.flatMap fun y =>
      Clause.imp [.holds t (.sit y)] (.holds t (.state (some y.1))) ::
        Clause.imp [.holds t (.sit y)] (.holds t (.inRead y.2.1)) ::
          (List.finRange k).map fun i =>
            Clause.imp [.holds t (.sit y)] (.holds t (.read i (y.2.2 i)))

/-- The step equation from time `t` to time `t + 1`: each term of the step equation of a basic
feature, at time `t`, implies the feature at time `t + 1`. -/
noncomputable def stepClauses [Fintype State] [DecidableEq State] (t : ℕ) : CNF (Var k State) :=
  (Feature.basic (u.length + L) T).flatMap fun φ =>
    (Feature.stepTerms tm (u.length + L) T φ).map fun c =>
      Clause.impLits (c.map fun l => (.holds t l.1, l.2)) (.holds (t + 1) φ)

/-- The run has halted by time `T` with output `[true]`. -/
def acceptClauses : CNF (Var k State) :=
  [[(.holds T (.state none), true)], [(.holds T (.out (.one true)), true)]]

/-- The Cook–Levin tableau of `tm` on inputs `u ++ w` with `|w| = L`, unrolled for `T` steps. -/
noncomputable def tableau [Fintype State] [DecidableEq State] : CNF (Var k State) :=
  initClauses tm T ++ (List.range (T + 1)).flatMap (oneHotClauses u L T) ++
    (List.range T).flatMap (fun t =>
      readClauses u L T t ++ sitClauses t ++ uniqueClauses t ++ stepClauses tm u L T t) ++
    acceptClauses T

end Clauses

end Cslib.Complexity.CookLevin
