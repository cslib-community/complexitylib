/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Oracle.Transcript
public import Complexity.Languages.Probabilistic.QueryCount

import Complexity.Languages.Probabilistic.Oracle.Simulation

/-!
# Query budgets of randomized programs

A program with private coins, `ProbOracleComp spec α`, makes two kinds of calls: private samples
(`Sum.inl`) and external queries (`Sum.inr`). Its query budgets are the budgets
`OracleComp.IsCostBounded` of a cost that is `0` on every sample:

* `ProbOracleComp.IsQueryBounded program n`: at most `n` external queries on every path, whatever
  the samples and the replies;
* `ProbOracleComp.QueriesSatisfy p program`: every external query satisfies `p`, for example a
  bound on its length.

All rules of `OracleComp.IsCostBounded` apply. A program over the external interface alone, with
its calls made external queries, keeps its budget (`isCostBounded_interpret_query`).

**Meaning.** Against every stateful oracle, the external queries recorded on a supported run
respect the budget (`transcript_cost_le`). Conversely, when every reply type is nonempty, a program
whose recorded queries respect the budget against every stateful oracle satisfies it
(`isCostBounded_iff_transcript_cost_le`): an oracle that answers its first call with a chosen
reply realizes each path. This is how a certificate stated through executions, such as an oracle
machine's, yields a structural budget. Without nonempty reply types the converse fails: if some
reply type is empty, no oracle exists, and the condition on executions holds vacuously.

## Main definitions

* `Cslib.ProbOracleComp.IsQueryBounded`: at most `n` external queries on every path.
* `Cslib.ProbOracleComp.QueriesSatisfy`: every external query on every path satisfies `p`.

## Main results

* `Cslib.ProbOracleComp.isCostBounded_sample`: private samples cost nothing.
* `Cslib.ProbOracleComp.isCostBounded_interpret_query`: budgets of programs without private coins.
* `Cslib.ProbOracleComp.isCostBounded_iff_transcript_cost_le`: the structural budget is the budget
  of every logged execution.
-/

@[expose] public section

namespace Cslib.ProbOracleComp

open OracleComp

variable {Query α β : Type} {spec : Query → Type}

/-- The program makes at most `n` external queries on every path, whatever its private samples and
the replies. Private samples are free. -/
abbrev IsQueryBounded (program : ProbOracleComp spec α) (n : ℕ) : Prop :=
  IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) program n

/-- Every external query of the program, on every path, satisfies `p`. Private samples are
unconstrained. -/
abbrev QueriesSatisfy (p : Query → Prop) (program : ProbOracleComp spec α) : Prop :=
  OracleComp.QueriesSatisfy (Sum.elim (fun _ => True) p) program

/-- A closed sampler makes no external query. -/
theorem isCostBounded_sample (cost : Query → ℕ) (program : ProbComp α) :
    IsCostBounded (Sum.elim (fun _ => 0) cost) (sample (spec := spec) program) 0 := by
  induction program using OracleComp.induction with
  | pure a => exact .pure a 0
  | query_bind n cont ih =>
    have hquery : sample (spec := spec) (OracleComp.query n) = OracleComp.query (Sum.inl n) :=
      OracleComp.interpret_query _ _
    rw [sample_bind, hquery]
    simpa using (IsCostBounded.query (Sum.inl n)).bind fun a => ih a

/-- A single external query costs its cost. -/
theorem isCostBounded_query (cost : Query → ℕ) (q : Query) :
    IsCostBounded (Sum.elim (fun _ => 0) cost) (query (spec := spec) q) (cost q) :=
  IsCostBounded.query (Sum.inr q)

/-- A program over the external interface alone keeps its budget when its calls become external
queries of a program with private coins. -/
theorem isCostBounded_interpret_query {cost : Query → ℕ} {program : OracleComp spec α} {n : ℕ}
    (h : IsCostBounded cost program n) :
    IsCostBounded (Sum.elim (fun _ => 0) cost)
      (OracleComp.interpret (fun q => query (spec := spec) q) program) n :=
  h.interpret fun q => isCostBounded_query cost q

/-- A closed sampler makes no external query. -/
theorem IsQueryBounded.sample (program : ProbComp α) :
    (sample (spec := spec) program).IsQueryBounded 0 :=
  isCostBounded_sample _ program

/-- A single external query is one query. -/
theorem IsQueryBounded.query (q : Query) : (query (spec := spec) q).IsQueryBounded 1 :=
  isCostBounded_query _ q

/-- A program without private coins makes as many external queries as it makes calls. -/
theorem _root_.Cslib.OracleComp.IsQueryBounded.probOracleComp {program : OracleComp spec α}
    {n : ℕ} (h : program.IsQueryBounded n) :
    IsQueryBounded (OracleComp.interpret (fun q => query (spec := spec) q) program) n :=
  isCostBounded_interpret_query h

/-- A closed sampler makes no external query. -/
theorem QueriesSatisfy.sample {p : Query → Prop} (program : ProbComp α) :
    (sample (spec := spec) program).QueriesSatisfy p := by
  classical
  refine (isCostBounded_sample (fun q => if p q then 0 else 1) program).of_le fun q => ?_
  cases q <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all

/-- A single external query satisfies `p` when its request does. -/
theorem QueriesSatisfy.query {p : Query → Prop} {q : Query} (hq : p q) :
    (query (spec := spec) q).QueriesSatisfy p :=
  OracleComp.QueriesSatisfy.query (q := Sum.inr q) hq

/-- A weaker predicate on external queries is still satisfied. -/
theorem QueriesSatisfy.mono {p p' : Query → Prop} {program : ProbOracleComp spec α}
    (h : program.QueriesSatisfy p) (hp : ∀ q, p q → p' q) : program.QueriesSatisfy p' :=
  OracleComp.QueriesSatisfy.mono h fun q hq => by
    cases q with
    | inl _ => trivial
    | inr q => exact hp q hq

/-- Every program satisfies a predicate that holds for every external query. -/
theorem QueriesSatisfy.of_forall {p : Query → Prop} (hp : ∀ q, p q)
    (program : ProbOracleComp spec α) : program.QueriesSatisfy p :=
  OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> simp [hp]) program

/-! ### Logged executions -/

/-- Against every stateful oracle, the external queries recorded on a supported run cost at most
the budget. Private samples are not recorded. -/
theorem transcript_cost_le {cost : Query → ℕ} {program : ProbOracleComp spec α} {n : ℕ}
    (h : IsCostBounded (Sum.elim (fun _ => 0) cost) program n) {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) {s s' : State} {result : α}
    {transcript : Transcript spec}
    (hmem : (result, s', transcript) ∈ ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        program).run (s, [])).support) :
    (transcript.map fun entry => cost entry.1).sum ≤ n := by
  induction h generalizing s s' result transcript with
  | pure a n =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hmem
    cases hmem
    simp
  | liftBind q cont n _ ih =>
    simp only [interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨a, middle, seen⟩, hfirst, hrest⟩ := hmem
    cases q with
    | inl k =>
      simp only [sumHandler, StateT.run_lift, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hfirst
      obtain ⟨_, -, heq⟩ := hfirst
      cases heq
      simpa using ih a hrest
    | inr q =>
      simp only [sumHandler, StateT.run, withTranscript, PMF.mem_support_map_iff] at hfirst
      obtain ⟨⟨answer, next⟩, -, heq⟩ := hfirst
      cases heq
      rw [run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
      obtain ⟨⟨result', final, fresh⟩, hfresh, heq⟩ := hrest
      cases heq
      have := ih answer hfresh
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Sum.elim_inr]
      omega

/-- If, against every stateful oracle, the external queries recorded on every supported run cost
at most `n`, and every reply type is nonempty, then the program's external queries cost at most
`n` on every path. -/
theorem isCostBounded_of_transcript_cost_le [hne : ∀ q, Nonempty (spec q)] {cost : Query → ℕ}
    {program : ProbOracleComp spec α} {n : ℕ}
    (h : ∀ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State)
      (result : α) (transcript : Transcript spec),
      (result, s', transcript) ∈ ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
          program).run (s, [])).support →
      (transcript.map fun entry => cost entry.1).sum ≤ n) :
    IsCostBounded (Sum.elim (fun _ => 0) cost) program n := by
  classical
  induction program generalizing n with
  | pure a => exact .pure a n
  | liftBind q cont ih =>
    have hrun (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s : State) :
        ((OracleComp.interpret
          (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
            (PFunctor.FreeM.liftBind q cont)).run (s, [])) =
          ((sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle) q).run
            (s, [])).bind fun first => (OracleComp.interpret
              (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
                (cont first.1)).run first.2 := rfl
    cases q with
    | inl k =>
      refine IsCostBounded.liftBind_iff.mpr ⟨Nat.zero_le n, fun a => ?_⟩
      rw [Sum.elim_inl, Nat.sub_zero]
      refine ih a fun State oracle s s' result transcript hmem => h State oracle s s' result
        transcript ?_
      rw [hrun, PMF.mem_support_bind_iff]
      refine ⟨(a, s, []), ?_, hmem⟩
      simp [sumHandler, ProbComp.unifOracle]
    | inr q =>
      -- Every supported run of a continuation, with the first call answered as chosen, is part
      -- of a supported run of the whole program.
      have key (a : spec q) (State : Type) (oracle : (q : Query) → StateT State PMF (spec q))
          (s s' : State) (result : α) (transcript : Transcript spec)
          (hmem : (result, s', transcript) ∈ ((OracleComp.interpret
            (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
              (cont a)).run (s, [])).support) :
          (transcript.map fun entry => cost entry.1).sum + cost q ≤ n := by
        let first (q' : Query) : spec q' :=
          if hq : q' = q then hq ▸ a else Classical.choice (hne q')
        let oracle' (q' : Query) : StateT (Option State) PMF (spec q') := fun
          | none => PMF.pure (first q', some s)
          | some state => (oracle q' state).map fun (b, state') => (b, some state')
        have hlift := run_interpret_map_state (withTranscript oracle) (withTranscript oracle')
          (fun state => (some state.1, state.2)) (fun q' state => by
            simp [withTranscript, oracle', PMF.map_comp, Function.comp_def]) (cont a) (s, [])
        have hwhole := h (Option State) oracle' none (some s') result
          (transcript ++ [⟨q, a⟩]) (by
            rw [hrun, PMF.mem_support_bind_iff]
            refine ⟨(a, some s, [⟨q, a⟩]), ?_, ?_⟩
            · change (a, some s, [⟨q, a⟩]) ∈ ((withTranscript oracle' q) (none, [])).support
              simp only [withTranscript, PMF.mem_support_map_iff]
              exact ⟨(a, some s), by simp [oracle', first], rfl⟩
            · rw [run_interpret_withTranscript_append, PMF.mem_support_map_iff]
              refine ⟨(result, some s', transcript), ?_, rfl⟩
              rw [← hlift, PMF.mem_support_map_iff]
              exact ⟨(result, s', transcript), hmem, rfl⟩)
        simpa [List.map_append, List.sum_append] using hwhole
      let default (q' : Query) : StateT Unit PMF (spec q') := fun _ =>
        PMF.pure (Classical.choice (hne q'), ())
      obtain ⟨⟨result, s', transcript⟩, hmem⟩ := PMF.support_nonempty ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript default))
          (cont (Classical.choice (hne q)))).run ((), []))
      have hle : cost q ≤ n := by
        have := key _ Unit _ () s' result transcript hmem
        omega
      refine IsCostBounded.liftBind_iff.mpr ⟨hle, fun a => ?_⟩
      refine ih a fun State oracle s s' result transcript hmem => ?_
      have := key a State oracle s s' result transcript hmem
      simp only [Sum.elim_inr]
      omega

/-- When every reply type is nonempty, a program's external queries cost at most `n` on every
path exactly when, against every stateful oracle, those recorded on every supported run do. -/
theorem isCostBounded_iff_transcript_cost_le [∀ q, Nonempty (spec q)] {cost : Query → ℕ}
    {program : ProbOracleComp spec α} {n : ℕ} :
    IsCostBounded (Sum.elim (fun _ => 0) cost) program n ↔
      ∀ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State)
        (result : α) (transcript : Transcript spec),
        (result, s', transcript) ∈ ((OracleComp.interpret
          (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
            program).run (s, [])).support →
        (transcript.map fun entry => cost entry.1).sum ≤ n :=
  ⟨fun h _ oracle _ _ _ _ hmem => transcript_cost_le h oracle hmem,
    isCostBounded_of_transcript_cost_le⟩

/-- Against every stateful oracle, a supported run records at most `n` external queries. -/
theorem IsQueryBounded.length_transcript_le {program : ProbOracleComp spec α} {n : ℕ}
    (h : program.IsQueryBounded n) {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) {s s' : State} {result : α}
    {transcript : Transcript spec}
    (hmem : (result, s', transcript) ∈ ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        program).run (s, [])).support) :
    transcript.length ≤ n := by
  simpa using transcript_cost_le h oracle hmem

/-- Against every stateful oracle, every external query recorded on a supported run satisfies
`p`. -/
theorem QueriesSatisfy.forall_mem_transcript {p : Query → Prop}
    {program : ProbOracleComp spec α} (h : program.QueriesSatisfy p) {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) {s s' : State} {result : α}
    {transcript : Transcript spec}
    (hmem : (result, s', transcript) ∈ ((OracleComp.interpret
      (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
        program).run (s, [])).support) :
    ∀ entry ∈ transcript, p entry.1 := by
  classical
  have hsum := transcript_cost_le (cost := fun q => if p q then 0 else 1)
    (h.of_le fun q => by
      cases q <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all) oracle hmem
  intro entry hentry
  by_contra hp
  have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := fun entry : (q : Query) × spec q =>
    if p entry.1 then 0 else 1) hentry)
  simp only [hp, ite_false] at hle
  omega

/-- When every reply type is nonempty and, against every stateful oracle, every supported run
records at most `n` external queries, the program makes at most `n` external queries. -/
theorem isQueryBounded_of_length_transcript_le [∀ q, Nonempty (spec q)]
    {program : ProbOracleComp spec α} {n : ℕ}
    (h : ∀ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State)
      (result : α) (transcript : Transcript spec),
      (result, s', transcript) ∈ ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
          program).run (s, [])).support →
      transcript.length ≤ n) :
    program.IsQueryBounded n :=
  isCostBounded_of_transcript_cost_le fun State oracle s s' result transcript hmem => by
    simpa using h State oracle s s' result transcript hmem

/-- When every reply type is nonempty and, against every stateful oracle, every external query
recorded on a supported run satisfies `p`, every external query of the program satisfies `p`. -/
theorem queriesSatisfy_of_forall_mem_transcript [∀ q, Nonempty (spec q)] {p : Query → Prop}
    {program : ProbOracleComp spec α}
    (h : ∀ (State : Type) (oracle : (q : Query) → StateT State PMF (spec q)) (s s' : State)
      (result : α) (transcript : Transcript spec),
      (result, s', transcript) ∈ ((OracleComp.interpret
        (sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (withTranscript oracle))
          program).run (s, [])).support →
      ∀ entry ∈ transcript, p entry.1) :
    program.QueriesSatisfy p := by
  classical
  have hcost := isCostBounded_of_transcript_cost_le (cost := fun q => if p q then 0 else 1)
    (program := program) (n := 0) fun State oracle s s' result transcript hmem => by
      have hall := h State oracle s s' result transcript hmem
      refine Nat.le_zero.mpr (List.sum_eq_zero fun x hx => ?_)
      obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hx
      simp [hall entry hentry]
  exact hcost.of_le fun q => by
    cases q <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all

end Cslib.ProbOracleComp
