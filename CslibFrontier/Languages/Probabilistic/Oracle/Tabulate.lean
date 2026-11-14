/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

/-!
# Tabulating an oracle on a list of points

`ProbOracleComp.tabulate q ps` queries the oracle at `q p` for each point `p` of the list `ps`, in
order, and returns the table of answers, with `0` at points outside the list. Against a fixed
function the table is that function on the list (`interpret_tabulate`), and the program makes at
most `ps.length` queries, one per list entry (`isQueryBounded_tabulate`). More generally, its
cost under any per-query weight is at most the sum of the entry costs (`isCostBounded_tabulate`),
and when `ps` has no duplicates and a projection `f ∘ q` is injective, at most one query lands on
each fibre of `f` (`isCostBounded_tabulate_eq`). A reduction that needs
an oracle's values on a known finite set of points, for example every PRF input used by a
construction, reads them all up front this way and then runs without further queries.

## Main definitions

* `Cslib.ProbOracleComp.tabulate`: query a list of points and return the table of answers.

## Main results

* `Cslib.ProbOracleComp.interpret_tabulate`: against a fixed function, the returned table.
* `Cslib.ProbOracleComp.isCostBounded_tabulate`: cost bound under an arbitrary query weight.
* `Cslib.ProbOracleComp.isCostBounded_tabulate_eq`,
  `Cslib.ProbOracleComp.isCostBounded_tabulate_le_one`: at most one query per fibre when `f ∘ q` is
  injective on a duplicate-free list.
* `Cslib.ProbOracleComp.isQueryBounded_tabulate`: at most one query per list entry.
-/

public section

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
    congr 1 with p' : 1
    by_cases h : p' = p
    · subst h
      simp
    · simp [h]

/-- Tabulation costs at most the sum of the query costs of the list entries. -/
theorem isCostBounded_tabulate (cost : Query → ℕ) (q : P → Query) (ps : List P) :
    IsCostBounded (Sum.elim (fun _ => 0) cost) (tabulate (R := R) q ps)
      (ps.map (cost ∘ q)).sum := by
  induction ps with
  | nil => exact IsCostBounded.pure _ 0
  | cons p ps ih =>
    have h := (isCostBounded_query (spec := fun _ : Query => R) cost (q p)).bind fun a =>
      ih.bind fun table => IsCostBounded.pure (Function.update table p a) 0
    simpa only [tabulate, List.map_cons, List.sum_cons, Function.comp_apply, Nat.add_zero] using h

/-- When `ps` has no duplicates and `f ∘ q` is injective, at most one tabulated query has image
`t` under `f`. -/
theorem isCostBounded_tabulate_eq {T : Type} [DecidableEq T] (f : Query → T) (q : P → Query)
    {ps : List P} (hps : ps.Nodup) (hq : Function.Injective (f ∘ q)) (t : T) :
    IsCostBounded (Sum.elim (fun _ => 0) fun x => if f x = t then 1 else 0)
      (tabulate (R := R) q ps) (if ∃ p ∈ ps, f (q p) = t then 1 else 0) := by
  induction ps with
  | nil => exact IsCostBounded.pure _ _
  | cons p ps ih =>
    rw [List.nodup_cons] at hps
    refine ((isCostBounded_query (spec := fun _ : Query => R)
      (fun x => if f x = t then 1 else 0) (q p)).bind fun a =>
      (ih hps.2).bind fun table =>
        IsCostBounded.pure (Function.update table p a) 0).mono ?_
    by_cases h1 : f (q p) = t
    · have h2 : ¬ ∃ p' ∈ ps, f (q p') = t := by
        rintro ⟨p', hp', hp't⟩
        exact hps.1 (hq (hp't.trans h1.symm) ▸ hp')
      simp [h1, h2]
    · by_cases h2 : ∃ p' ∈ ps, f (q p') = t <;> simp [h1, h2]

/-- Uniform `1`-bound form of `isCostBounded_tabulate_eq`: when `ps` has no duplicates and
`f ∘ q` is injective, at most one tabulated query has image `t` under `f` for every `t`. -/
theorem isCostBounded_tabulate_le_one {T : Type} [DecidableEq T] (f : Query → T) (q : P → Query)
    {ps : List P} (hps : ps.Nodup) (hq : Function.Injective (f ∘ q)) (t : T) :
    IsCostBounded (Sum.elim (fun _ => 0) fun x => if f x = t then 1 else 0)
      (tabulate (R := R) q ps) 1 :=
  (isCostBounded_tabulate_eq f q hps hq t).mono (by split_ifs <;> omega)

/-- Tabulation makes at most `ps.length` external queries, one per list entry. -/
theorem isQueryBounded_tabulate (q : P → Query) (ps : List P) :
    (tabulate (R := R) q ps).IsQueryBounded ps.length := by
  simpa [IsQueryBounded, Function.comp_def] using
    isCostBounded_tabulate (R := R) (fun _ => 1) q ps

end Cslib.ProbOracleComp
