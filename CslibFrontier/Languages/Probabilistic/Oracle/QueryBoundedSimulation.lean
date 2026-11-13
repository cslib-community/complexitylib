/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF.Coupling

/-!
# Simulating query-bounded programs

A program with private coins runs against a real stateful oracle or against an ideal oracle that
depends on a hidden sample. The two are linked by a law `exp s` of the hidden sample given the
real oracle state and by a representation `rep s` of that state. When each external query keeps
the link, the whole program keeps it, retaining its result and the final oracle state.

The local link need only hold on states satisfying an invariant indexed by the remaining query
budget. Each query may use one unit of the budget, as when the invariant reserves room in a
bounded cache for every query still to come. Private samples use none.

## Main results

* `Cslib.ProbOracleComp.IsQueryBounded.run_interpret_bind_comm_of_invariant`: a link kept by every
  external query on the remaining budget is kept by a query-bounded program.
* `Cslib.ProbOracleComp.IsQueryBounded.run_interpret_invariant`: a budget-indexed invariant kept by
  every external query holds after a query-bounded program.
-/

public section

namespace Cslib.ProbOracleComp

variable {Query α : Type} {spec : Query → Type}

/-- A query-bounded program keeps the link `(exp s).map (·, a, rep s)` between the real run and
an ideal run on a hidden sample, when every external query keeps it on states satisfying the
invariant `inv (rem + 1)` and leads to states satisfying `inv rem`. Private samples are fresh in
both runs. -/
theorem IsQueryBounded.run_interpret_bind_comm_of_invariant {σ₁ σ₂ γ : Type}
    (h₁ : (q : Query) → StateT σ₁ PMF (spec q))
    (h₂ : γ → (q : Query) → StateT σ₂ PMF (spec q))
    (exp : σ₁ → PMF γ) (rep : σ₁ → σ₂) (inv : ℕ → σ₁ → Prop)
    (hweaken : ∀ r s, inv (r + 1) s → inv r s)
    (hstep : ∀ rem q s, inv (rem + 1) s →
      ((h₁ q s).bind fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) =
        ((exp s).bind fun k => (h₂ k q (rep s)).map fun y => (k, y.1, y.2)) ∧
      ∀ ans s', (ans, s') ∈ (h₁ q s).support → inv rem s')
    {program : ProbOracleComp spec α} {rem : ℕ} (hq : program.IsQueryBounded rem)
    {s : σ₁} (hinv : inv rem s) :
    (((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) h₁)
      program).run s).bind fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) =
      ((exp s).bind fun k =>
        ((OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (h₂ k))
          program).run (rep s)).map fun y => (k, y.1, y.2)) ∧
    ∀ res s', (res, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) h₁)
      program).run s).support → inv 0 s' := by
  have hzero : ∀ r s, inv r s → inv 0 s := by
    intro r
    induction r with
    | zero => exact fun _ h => h
    | succ r ih => exact fun s h => ih s (hweaken r s h)
  induction hq generalizing s with
  | pure a rem =>
    refine ⟨?_, fun res s' hm => ?_⟩
    · simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
        PMF.pure_bind, PMF.map, Function.comp_def]
    · simp only [OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure] at hm
      obtain ⟨_, rfl⟩ := Prod.mk.inj ((PMF.mem_support_pure_iff _ _).mp hm)
      exact hzero rem _ hinv
  | liftBind q cont rem _ ih =>
    have hcall :
        ((OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) h₁ q s).bind
          fun x => (exp x.2).map fun k => (k, x.1, rep x.2)) =
          ((exp s).bind fun k =>
            (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (h₂ k) q
              (rep s)).map fun y => (k, y.1, y.2)) ∧
        ∀ ans s', (ans, s') ∈
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) h₁ q s).support →
            inv rem s' := by
      cases q with
      | inl n =>
        simp only [Sum.elim_inl, Nat.add_zero] at hinv
        refine ⟨?_, fun ans s' hm => ?_⟩
        · change ((ProbComp.unifOracle n).map (·, s)).bind _ =
            (exp s).bind fun k => ((ProbComp.unifOracle n).map (·, rep s)).map _
          simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
          exact PMF.bind_comm _ _ _
        · change (ans, s') ∈ ((ProbComp.unifOracle n).map (·, s)).support at hm
          obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
          obtain ⟨-, rfl⟩ := Prod.mk.inj heq
          exact hinv
      | inr q =>
        simp only [Sum.elim_inr] at hinv
        exact hstep rem q s hinv
    simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
      Probability.PMF.monad_bind_eq_bind]
    refine (fun h => ⟨h.1, fun res s' hm => h.2 (res, s') hm⟩)
      (Probability.PMF.bind_bind_comm_of_invariant _ (fun x => exp x.2) (fun x => (x.1, rep x.2))
        (fun k => OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (h₂ k) q
          (rep s))
        (fun x => inv rem x.2) (exp s) _ (fun x => exp x.2) (fun x => (x.1, rep x.2))
        (fun k y => (OracleComp.interpret
          (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (h₂ k))
          (cont y.1)).run y.2)
        (fun x => inv 0 x.2) ⟨hcall.1, fun x hx => hcall.2 x.1 x.2 hx⟩
        fun x _ hx => ⟨(ih x.1 hx).1, fun b hb => (ih x.1 hx).2 b.1 b.2 hb⟩)

/-- A budget-indexed invariant holds after a query-bounded program when every external query from
a state satisfying `inv (rem + 1)` leads to states satisfying `inv rem`. Private samples leave the
state unchanged. -/
theorem IsQueryBounded.run_interpret_invariant {σ : Type}
    (h : (q : Query) → StateT σ PMF (spec q)) (inv : ℕ → σ → Prop)
    (hweaken : ∀ r s, inv (r + 1) s → inv r s)
    (hstep : ∀ rem q s, inv (rem + 1) s → ∀ ans s', (ans, s') ∈ (h q s).support → inv rem s')
    {program : ProbOracleComp spec α} {rem : ℕ} (hq : program.IsQueryBounded rem)
    {s : σ} (hinv : inv rem s) :
    ∀ res s', (res, s') ∈ ((OracleComp.interpret
      (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) h)
      program).run s).support → inv 0 s' :=
  (hq.run_interpret_bind_comm_of_invariant h (fun _ => h) (fun _ => PMF.pure ()) id inv hweaken
    (fun rem q s hs => ⟨by simp only [PMF.pure_bind, PMF.pure_map]; rfl, hstep rem q s hs⟩)
    hinv).2

end Cslib.ProbOracleComp
