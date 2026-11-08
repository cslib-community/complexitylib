/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.Transcript
import Mathlib.Tactic.Positivity

/-!
# Query budgets

`OracleComp.IsCostBounded cost program n` says that on every path through the tree of calls of
`program`, whatever the answers, the calls cost at most `n` in total, where a call `q` costs
`cost q`. This is the library's notion of a query budget; the others are instances of it.

* With unit costs it is `OracleComp.IsQueryBounded program n`: at most `n` calls on every path,
  that is, a query tree of depth at most `n`.
* A cost that is `1` on calls of one kind and `0` on the others counts those calls only, such as
  the signing calls of a forger, or the external queries of a program with private coins
  (`ProbOracleComp.IsQueryBounded`).
* A zero budget for the calls outside a predicate `p` says that every call satisfies `p`
  (`OracleComp.QueriesSatisfy`), for example that every request has bounded length.

Budgets are proved and used by induction on the program. They are preserved by sequencing
(`IsCostBounded.bind`), add over costs (`IsCostBounded.add`), and compose with handlers whose calls
are budgeted in turn (`IsCostBounded.run_interpret`). Against every stateful oracle, the calls that
`OracleComp.withTranscript` records respect the budget (`IsCostBounded.transcript_cost_le`).
A budget says nothing about running time.

## Main definitions

* `Cslib.OracleComp.IsCostBounded`: calls costing at most `n` on every path.
* `Cslib.OracleComp.IsQueryBounded`: at most `n` calls on every path.
* `Cslib.OracleComp.QueriesSatisfy`: every call on every path satisfies a predicate.

## Main results

* `Cslib.OracleComp.IsCostBounded.bind`: budgets add under sequencing.
* `Cslib.OracleComp.IsCostBounded.add`: budgets for two costs give a budget for their sum.
* `Cslib.OracleComp.IsCostBounded.run_interpret`: the budget of a program run through a stateful
  handler.
* `Cslib.OracleComp.IsCostBounded.transcript_cost_le`: logged calls respect the budget.
-/

@[expose] public section

namespace Cslib.OracleComp

universe u v

variable {ι : Type u} {spec : OracleSpec.{u, v} ι} {α β : Type v}

/-- The calls of the program cost at most `n` in total on every path, whatever the answers, where
a call `q` costs `cost q`. -/
inductive IsCostBounded (cost : ι → ℕ) : OracleComp spec α → ℕ → Prop
  /-- Returning a value makes no call. -/
  | pure (a : α) (n : ℕ) : IsCostBounded cost (pure a) n
  /-- A call followed by continuations whose calls each cost at most `n`. -/
  | liftBind (q : ι) (cont : spec q → OracleComp spec α) (n : ℕ)
      (hcont : ∀ a, IsCostBounded cost (cont a) n) :
      IsCostBounded cost (OracleComp.query q >>= cont) (n + cost q)

/-- The program makes at most `n` oracle calls on every path, whatever the answers. -/
abbrev IsQueryBounded (program : OracleComp spec α) (n : ℕ) : Prop :=
  IsCostBounded (fun _ => 1) program n

namespace IsCostBounded

variable {cost : ι → ℕ}

/-- A larger budget is still a budget. -/
theorem mono {program : OracleComp spec α} {n m : ℕ} (h : IsCostBounded cost program n)
    (hnm : n ≤ m) : IsCostBounded cost program m := by
  induction h generalizing m with
  | pure a n => exact .pure a m
  | liftBind q cont n _ ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + cost q := ⟨m - cost q, by omega⟩
    exact .liftBind q cont m fun a => ih a (by omega)

/-- A budget for a call's continuations, from a budget for the call. -/
theorem liftBind_iff {q : ι} {cont : spec q → OracleComp spec α} {n : ℕ} :
    IsCostBounded cost (PFunctor.FreeM.liftBind q cont) n ↔
      cost q ≤ n ∧ ∀ a, IsCostBounded cost (cont a) (n - cost q) := by
  constructor
  · rintro (_ | ⟨_, _, n, hcont⟩)
    exact ⟨by omega, fun a => by rw [Nat.add_sub_cancel]; exact hcont a⟩
  · rintro ⟨hle, hcont⟩
    rw [show n = n - cost q + cost q by omega]
    exact .liftBind q cont _ hcont

/-- One call costs its cost. -/
theorem query (q : ι) : IsCostBounded cost (OracleComp.query (spec := spec) q) (cost q) := by
  have h := IsCostBounded.liftBind (spec := spec) (cost := cost) q
    (fun a : spec q => PFunctor.FreeM.pure a) 0 fun a => .pure a 0
  rw [Nat.zero_add] at h
  exact h

/-- Budgets add under sequencing. -/
theorem bind {program : OracleComp spec α} {next : α → OracleComp spec β} {n m : ℕ}
    (h : IsCostBounded cost program n) (hnext : ∀ a, IsCostBounded cost (next a) m) :
    IsCostBounded cost (program >>= next) (n + m) := by
  induction h with
  | pure a n => exact (hnext a).mono (by omega)
  | liftBind q cont n _ ih =>
    rw [show n + cost q + m = n + m + cost q by omega]
    exact .liftBind q _ (n + m) ih

/-- Calls that cost nothing fit in a zero budget. -/
theorem of_forall_cost_eq_zero (hcost : ∀ q, cost q = 0) (program : OracleComp spec α) :
    IsCostBounded cost program 0 := by
  induction program with
  | pure a => exact .pure a 0
  | liftBind q cont ih =>
    exact liftBind_iff.mpr ⟨(hcost q).le, fun a => by simpa [hcost q] using ih a⟩

/-- A budget for a cost is one for every smaller cost. -/
theorem of_le {cost' : ι → ℕ} {program : OracleComp spec α} {n : ℕ}
    (h : IsCostBounded cost program n) (hcost : ∀ q, cost' q ≤ cost q) :
    IsCostBounded cost' program n := by
  induction h with
  | pure a n => exact .pure a n
  | liftBind q cont n _ ih => exact (IsCostBounded.liftBind q cont n ih).mono (by simp [hcost q])

/-- Budgets for two costs give a budget for their sum. -/
theorem add {cost' : ι → ℕ} {program : OracleComp spec α} {n n' : ℕ}
    (h : IsCostBounded cost program n) (h' : IsCostBounded cost' program n') :
    IsCostBounded (fun q => cost q + cost' q) program (n + n') := by
  induction h generalizing n' with
  | pure a n => exact .pure a _
  | liftBind q cont n _ ih =>
    obtain ⟨hle, hcont⟩ := liftBind_iff.mp h'
    rw [show n + cost q + n' = n + (n' - cost' q) + (cost q + cost' q) by omega]
    exact .liftBind q cont _ fun a => ih a (hcont a)

/-- A program whose calls are replaced by programs over another interface, each call `q` costing
at most `cost q` there, costs at most `n` there when its own calls cost at most `n`. -/
theorem interpret {κ : Type u} {target : OracleSpec.{u, v} κ} {cost' : κ → ℕ}
    {handler : (q : ι) → OracleComp target (spec q)}
    (hhandler : ∀ q, IsCostBounded cost' (handler q) (cost q)) {program : OracleComp spec α}
    {n : ℕ} (h : IsCostBounded cost program n) :
    IsCostBounded cost' (OracleComp.interpret handler program) n := by
  induction h with
  | pure a n => exact .pure a n
  | liftBind q cont n _ ih =>
    rw [interpret_bind, interpret_query, Nat.add_comm]
    exact (hhandler q).bind ih

/-- A program run through a stateful handler, each of whose calls `q` costs at most `cost q` on
the target interface, costs at most `n` there when its own calls cost at most `n`. -/
theorem run_interpret {κ : Type u} {target : OracleSpec.{u, v} κ} {cost' : κ → ℕ} {σ : Type v}
    {handler : (q : ι) → StateT σ (OracleComp target) (spec q)}
    (hhandler : ∀ q s, IsCostBounded cost' ((handler q).run s) (cost q))
    {program : OracleComp spec α} {n : ℕ} (h : IsCostBounded cost program n) (s : σ) :
    IsCostBounded cost' ((OracleComp.interpret handler program).run s) n := by
  induction h generalizing s with
  | pure a n => exact .pure (a, s) _
  | liftBind q cont n _ ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind]
    rw [Nat.add_comm]
    exact (hhandler q s).bind fun result => ih result.1 result.2

end IsCostBounded

/-- Postprocessing the result makes no call. -/
@[simp] theorem isCostBounded_map_iff {cost : ι → ℕ} (f : α → β) (program : OracleComp spec α)
    (n : ℕ) : IsCostBounded cost (f <$> program) n ↔ IsCostBounded cost program n := by
  constructor
  · intro h
    induction program generalizing n with
    | pure a => exact .pure a n
    | liftBind q cont ih =>
      obtain ⟨hle, hcont⟩ := IsCostBounded.liftBind_iff.mp h
      exact IsCostBounded.liftBind_iff.mpr ⟨hle, fun a => ih a _ (hcont a)⟩
  · intro h
    rw [← bind_pure_comp]
    simpa using h.bind fun a => IsCostBounded.pure (f a) 0

/-! ### Every call satisfies a predicate -/

open Classical in
/-- Every call of `program`, on every path and whatever the answers, satisfies `p`: the calls
outside `p` have a zero budget. -/
def QueriesSatisfy (p : ι → Prop) (program : OracleComp spec α) : Prop :=
  IsCostBounded (fun q => if p q then 0 else 1) program 0

namespace QueriesSatisfy

variable {p p' : ι → Prop}

/-- A call followed by its continuations satisfies `p` exactly when the call and every
continuation do. -/
theorem liftBind_iff {q : ι} {cont : spec q → OracleComp spec α} :
    QueriesSatisfy p (PFunctor.FreeM.liftBind q cont) ↔
      p q ∧ ∀ a, QueriesSatisfy p (cont a) := by
  classical
  unfold QueriesSatisfy
  rw [IsCostBounded.liftBind_iff]
  by_cases hq : p q <;> simp [hq]

/-- Returning a value makes no call. -/
theorem pure (a : α) : QueriesSatisfy p (Pure.pure a : OracleComp spec α) :=
  IsCostBounded.pure a 0

/-- A single call satisfies `p` when its query does. -/
theorem query {q : ι} (hq : p q) : QueriesSatisfy p (OracleComp.query (spec := spec) q) := by
  classical
  have h := IsCostBounded.query (spec := spec) (cost := fun q => if p q then 0 else 1) q
  simpa [QueriesSatisfy, hq] using h

/-- Sequencing preserves the predicate. -/
theorem bind {program : OracleComp spec α} {next : α → OracleComp spec β}
    (h : QueriesSatisfy p program) (hnext : ∀ a, QueriesSatisfy p (next a)) :
    QueriesSatisfy p (program >>= next) := by
  simpa [QueriesSatisfy] using IsCostBounded.bind h hnext

/-- Every program satisfies a predicate that holds for every call. -/
theorem of_forall (hp : ∀ q, p q) (program : OracleComp spec α) : QueriesSatisfy p program :=
  IsCostBounded.of_forall_cost_eq_zero (fun q => by simp [hp q]) program

/-- A weaker predicate is still satisfied. -/
theorem mono {program : OracleComp spec α} (h : QueriesSatisfy p program)
    (hp : ∀ q, p q → p' q) : QueriesSatisfy p' program := by
  classical
  refine IsCostBounded.of_le h fun q => ?_
  by_cases hq : p q
  · simp [hq, hp q hq]
  · by_cases hq' : p' q <;> simp [hq, hq']

end QueriesSatisfy

/-- Postprocessing the result makes no call. -/
@[simp] theorem queriesSatisfy_map_iff {p : ι → Prop} (f : α → β) (program : OracleComp spec α) :
    QueriesSatisfy p (f <$> program) ↔ QueriesSatisfy p program :=
  isCostBounded_map_iff f program 0

/-! ### Logged calls respect the budget -/

section Transcript

variable {Query : Type u} {Response : Query → Type u} {State γ : Type u}

/-- If each oracle call `q` increases a state measure `size : State → ℕ` by at most `cost q` on
every supported transition, then any `cost`-bounded execution increases `size` by at most `n`. -/
theorem IsCostBounded.measure_le {cost : Query → ℕ} {program : OracleComp Response γ}
    {n : ℕ} (h : IsCostBounded cost program n)
    (oracle : (q : Query) → StateT State PMF (Response q)) (size : State → ℕ)
    (hstep : ∀ q s res s', (res, s') ∈ (oracle q s).support → size s' ≤ size s + cost q)
    {s s' : State} {result : γ}
    (hmem : (result, s') ∈ ((OracleComp.interpret oracle program).run s).support) :
    size s' ≤ size s + n := by
  induction h generalizing s with
  | pure a n =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, rfl⟩
    omega
  | liftBind q cont n _ ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨ans, s₁⟩, hans, hcont⟩ := hmem
    have h₁ := hstep q s ans s₁ hans
    have h₂ : size s' ≤ size s₁ + n := ih ans hcont
    omega

/-- Against every stateful oracle, the calls recorded on a supported run cost at most the
budget. -/
theorem IsCostBounded.transcript_cost_le {cost : Query → ℕ} {program : OracleComp Response γ}
    {n : ℕ} (h : IsCostBounded cost program n)
    (oracle : (q : Query) → StateT State PMF (Response q)) {s s' : State} {result : γ}
    {transcript : Transcript Response}
    (hmem : (result, s', transcript) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    (transcript.map fun entry => cost entry.1).sum ≤ n := by
  induction h generalizing s s' result transcript with
  | pure a n =>
    simp only [run_interpret_pure, Probability.PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff] at hmem
    cases hmem
    simp
  | liftBind q cont n _ ih =>
    simp only [interpret_bind, interpret_query, StateT.run_bind,
      Probability.PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hmem
    obtain ⟨⟨a, middle, seen⟩, hfirst, hrest⟩ := hmem
    simp only [StateT.run, withTranscript, PMF.mem_support_map_iff] at hfirst
    obtain ⟨⟨answer, next⟩, -, heq⟩ := hfirst
    cases heq
    rw [run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
    obtain ⟨⟨result', final, fresh⟩, hfresh, heq⟩ := hrest
    cases heq
    have := ih answer hfresh
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega

/-- Against every stateful oracle, a supported run records at most `n` calls. -/
theorem IsQueryBounded.length_transcript_le {program : OracleComp Response γ} {n : ℕ}
    (h : program.IsQueryBounded n) (oracle : (q : Query) → StateT State PMF (Response q))
    {s s' : State} {result : γ} {transcript : Transcript Response}
    (hmem : (result, s', transcript) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    transcript.length ≤ n := by
  simpa using h.transcript_cost_le oracle hmem

/-- Against every stateful oracle, every call recorded on a supported run satisfies `p`. -/
theorem QueriesSatisfy.forall_mem_transcript {p : Query → Prop}
    {program : OracleComp Response γ} (h : QueriesSatisfy p program)
    (oracle : (q : Query) → StateT State PMF (Response q)) {s s' : State} {result : γ}
    {transcript : Transcript Response}
    (hmem : (result, s', transcript) ∈
      ((OracleComp.interpret (withTranscript oracle) program).run (s, [])).support) :
    ∀ entry ∈ transcript, p entry.1 := by
  classical
  have hsum := IsCostBounded.transcript_cost_le h oracle hmem
  intro entry hentry
  by_contra hp
  have hle := List.le_sum_of_mem (List.mem_map_of_mem (f := fun entry : (q : Query) × Response q =>
    if p entry.1 then 0 else 1) hentry)
  simp only [hp, ite_false] at hle
  omega

end Transcript

end Cslib.OracleComp

namespace Cslib.Probability.PMF

/-- If each outcome in the support of `p : _root_.PMF α` satisfies `pred x m = true` for at most `Q`
indices `m : M`, then the sum over `m : M` of `Pr_{x ← p}[pred x m = true]` is at most `Q`. -/
theorem sum_toReal_indicator_le {α M : Type*} [Fintype M] (p : _root_.PMF α)
    (pred : α → M → Bool) (Q : ℕ)
    (hcard : ∀ x ∈ p.support, (Finset.univ.filter fun m => pred x m = true).card ≤ Q) :
    (∑ m : M, ((p.map fun x => pred x m) true).toReal) ≤ (Q : ℝ) := by
  have hterm (m : M) :
      ((p.map fun x => pred x m) true).toReal =
        ∑' x : α, (p x).toReal * if pred x m = true then 1 else 0 := by
    simp only [_root_.PMF.map, Function.comp_def, bind_apply_toReal_tsum]
    refine tsum_congr fun x => ?_
    cases pred x m <;> simp
  simp_rw [hterm]
  have hsumm (m : M) :
      Summable (fun x : α => (p x).toReal * if pred x m = true then (1 : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun x => ?_) (fun x => ?_) (summable_toReal p)
    · positivity
    · by_cases hx : pred x m = true <;> simp [hx, ENNReal.toReal_nonneg]
  rw [← Summable.tsum_finsetSum (fun m _ => hsumm m)]
  calc ∑' x : α, ∑ m : M, ((p x).toReal * if pred x m = true then (1 : ℝ) else 0)
      ≤ ∑' x : α, (p x).toReal * (Q : ℝ) := by
        refine Summable.tsum_le_tsum (fun x => ?_)
          (summable_sum fun m _ => hsumm m) ((summable_toReal p).mul_right (Q : ℝ))
        rw [← Finset.mul_sum]
        by_cases hx : x ∈ p.support
        · refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
          rw [Finset.sum_boole]
          exact_mod_cast hcard x hx
        · rw [(_root_.PMF.apply_eq_zero_iff _ _).mpr hx, ENNReal.toReal_zero, zero_mul, zero_mul]
    _ = (Q : ℝ) := by
        rw [tsum_mul_right, tsum_toReal, one_mul]

end Cslib.Probability.PMF
