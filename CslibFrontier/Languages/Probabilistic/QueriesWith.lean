/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Languages.Probabilistic.Semantics

/-!
# The requests of a deterministic run

Answering every call `q` of an oracle program by `answer q` runs it deterministically:
`OracleComp.interpret (m := Id) answer program`. `OracleComp.queriesWith answer program` lists the
requests made along that run, in order. Only their answers matter
(`OracleComp.interpret_id_congr`): this locality underlies oracle constructions and adversary
arguments, which fix the answers to the requests a program makes and leave every other answer
free.

A program with a query budget of `n` makes at most `n` requests along every run
(`OracleComp.IsQueryBounded.length_queriesWith_le`), and the result of a run whose answers are all
possible is a possible result (`OracleComp.interpret_id_mem_supportWith`).

## Main definitions

* `Cslib.OracleComp.queriesWith`: the requests a deterministic run makes.

## Main results

* `Cslib.OracleComp.interpret_id_congr`: answers to requests that are not made do not matter.
* `Cslib.OracleComp.IsQueryBounded.length_queriesWith_le`: a run makes at most the budgeted number
  of requests.
* `Cslib.OracleComp.interpret_id_mem_supportWith`: a run along possible answers has a possible
  result.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

variable {ι α β : Type} {spec : OracleSpec.{0, 0} ι}

/-- The requests made by `program`, in order, when every call `q` is answered by `answer q`. -/
def queriesWith (answer : (q : ι) → spec q) : OracleComp spec α → List ι
  | .pure _ => []
  | .liftBind q next => q :: queriesWith answer (next (answer q))

@[simp] theorem queriesWith_pure (answer : (q : ι) → spec q) (a : α) :
    queriesWith answer (pure a : OracleComp spec α) = [] := rfl

@[simp] theorem queriesWith_query (answer : (q : ι) → spec q) (q : ι) :
    queriesWith answer (query q) = [q] := rfl

@[simp] theorem queriesWith_query_bind (answer : (q : ι) → spec q) (q : ι)
    (next : spec q → OracleComp spec α) :
    queriesWith answer (query q >>= next) = q :: queriesWith answer (next (answer q)) := rfl

/-- Answering the first call and continuing. -/
@[simp] theorem interpret_id_query_bind (answer : (q : ι) → spec q) (q : ι)
    (next : spec q → OracleComp spec α) :
    interpret (m := Id) answer (query q >>= next) = interpret (m := Id) answer (next (answer q)) :=
  rfl

/-- A sequence makes the requests of its first part, then those of the continuation selected by
the first result. -/
theorem queriesWith_bind (answer : (q : ι) → spec q) (program : OracleComp spec α)
    (next : α → OracleComp spec β) :
    queriesWith answer (program >>= next) = queriesWith answer program ++
      queriesWith answer (next (interpret (m := Id) answer program)) := by
  induction program using PFunctor.FreeM.induction with
  | pure a => rfl
  | lift_bind q cont ih =>
    exact congrArg (q :: ·) (ih (answer q))

/-- Postprocessing the result makes no request. -/
@[simp] theorem queriesWith_map (answer : (q : ι) → spec q) (f : α → β)
    (program : OracleComp spec α) :
    queriesWith answer (f <$> program) = queriesWith answer program := by
  rw [← bind_pure_comp, queriesWith_bind, queriesWith_pure, List.append_nil]

/-- **Locality.** Answer functions that agree on the requests made under one of them give the
same result and the same requests. -/
theorem interpret_id_congr (answer answer' : (q : ι) → spec q) (program : OracleComp spec α)
    (h : ∀ q ∈ queriesWith answer program, answer' q = answer q) :
    interpret (m := Id) answer' program = interpret (m := Id) answer program ∧
      queriesWith answer' program = queriesWith answer program := by
  induction program using PFunctor.FreeM.induction with
  | pure a => exact ⟨rfl, rfl⟩
  | lift_bind q cont ih =>
    have hq : answer' q = answer q := h q (List.mem_cons_self ..)
    have hrest := ih (answer q) fun q' hq' => h q' (List.mem_cons_of_mem _ hq')
    change interpret (m := Id) answer' (cont (answer' q)) =
        interpret (m := Id) answer (cont (answer q)) ∧
      q :: queriesWith answer' (cont (answer' q)) = q :: queriesWith answer (cont (answer q))
    rw [hq]
    exact ⟨hrest.1, congrArg (q :: ·) hrest.2⟩

/-- A program with a query budget of `n` makes at most `n` requests along every run. -/
theorem IsQueryBounded.length_queriesWith_le (answer : (q : ι) → spec q)
    {program : OracleComp spec α} {n : ℕ} (h : program.IsQueryBounded n) :
    (queriesWith answer program).length ≤ n := by
  induction h with
  | pure a n => exact Nat.zero_le _
  | liftBind q cont n _ ih =>
    rw [queriesWith_query_bind, List.length_cons]
    exact Nat.add_le_add_right (ih _) 1

/-- A run whose every answer is possible has a possible result. -/
theorem interpret_id_mem_supportWith {possible : (q : ι) → Set (spec q)}
    {answer : (q : ι) → spec q} (h : ∀ q, answer q ∈ possible q) (program : OracleComp spec α) :
    interpret (m := Id) answer program ∈ supportWith possible program := by
  induction program using PFunctor.FreeM.induction with
  | pure a => exact Set.mem_singleton _
  | lift_bind q cont ih =>
    exact Set.mem_biUnion (h q) (ih (answer q))

end OracleComp

end Cslib
