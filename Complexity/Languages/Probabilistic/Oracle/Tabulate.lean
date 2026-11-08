/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle.QueryCount

/-!
# Tabulating an oracle on a list of points

`ProbOracleComp.tabulate q ps` queries the oracle at `q p` for each point `p` of the list `ps`, in
order, and returns the table of answers, with `0` at points outside the list. Against a fixed
function the table is that function on the list (`interpret_tabulate`), and the program makes
exactly one query per list entry (`isQueryBounded_tabulate`). A reduction that needs an oracle's
values on a known finite set of points, for example every PRF input used by a construction, reads
them all up front this way and then runs without further queries.

## Main definitions

* `Cslib.ProbOracleComp.tabulate`: query a list of points and return the table of answers.

## Main results

* `Cslib.ProbOracleComp.interpret_tabulate`: against a fixed function, the returned table.
* `Cslib.ProbOracleComp.isQueryBounded_tabulate`: one query per list entry.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {P Query R : Type} [DecidableEq P] [Zero R]

/-- Query the oracle at `q p` for each `p` in `ps`, in order, and return the table `p ↦ answer`,
which is `0` off the list. -/
def tabulate (q : P → Query) : List P → ProbOracleComp (fun _ : Query => R) (P → R)
  | [] => pure 0
  | p :: ps => do
    let a ← query (q p)
    let table ← tabulate q ps
    return Function.update table p a

/-- Against a fixed function `f`, tabulation returns `f ∘ q` on the list and `0` off it, in every
lawful monad supplying the private coins. -/
theorem interpret_tabulate {m : Type → Type*} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (f : Query → R) (q : P → Query) (ps : List P) :
    OracleComp.interpret (OracleComp.sumHandler random fun x => pure (f x)) (tabulate q ps) =
      pure (fun p => if p ∈ ps then f (q p) else 0) := by
  induction ps with
  | nil => simp only [tabulate, OracleComp.interpret_pure, List.not_mem_nil, ite_false]; rfl
  | cons p ps ih =>
    simp only [tabulate, OracleComp.interpret_bind, interpret_query, ih, pure_bind,
      OracleComp.interpret_pure]
    congr 1
    funext p'
    by_cases h : p' = p
    · subst h
      simp
    · simp [h]

/-- Tabulation makes one external query per list entry. -/
theorem isQueryBounded_tabulate (q : P → Query) (ps : List P) :
    (tabulate (R := R) q ps).IsQueryBounded ps.length := by
  induction ps with
  | nil => exact IsCostBounded.pure _ 0
  | cons p ps ih =>
    have h := (IsQueryBounded.query (spec := fun _ : Query => R) (q p)).bind fun a =>
      ih.bind fun table => IsCostBounded.pure (Function.update table p a) 0
    simpa only [tabulate, List.length_cons, Nat.add_zero, Nat.add_comm] using h

end Cslib.ProbOracleComp
