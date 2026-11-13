/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Tactic.SuppCases

/-!
# Cache invariants of the lazy random oracle

A run of an oracle program under the lazy random oracle `RandomOracle.answer dist` only extends
its cache, keeps every cached answer in the support of `dist`, and returns what the program
computes against any total oracle extending the final cache
(`OracleComp.mem_support_runWith_answer_invariant`). Completing the final cache to a total oracle
with `OracleComp.cacheOracle` turns facts about deterministic evaluation (`OracleComp.evalPure`)
into facts about the lazy random-oracle run: a program that returns `a` against every oracle drawn
from the pointwise support of `dist` returns `PMF.pure a` under `RandomOracle.answer dist`
(`OracleComp.map_fst_runWith_answer_eq_pure`).

## Main definitions

* `Cslib.OracleComp.cacheOracle`: a total oracle extending a cache, answering uncached queries
  with an element of the support of `dist`.

## Main results

* `Cslib.OracleComp.mem_support_runWith_answer_invariant`: the cache invariant of supported runs.
* `Cslib.OracleComp.map_fst_runWith_answer_eq_pure`: oracle programs that are constant on the
  support of `dist` are deterministic under the lazy random oracle.
-/

@[expose] public section

namespace Cslib

namespace OracleComp

universe u

variable {ι : Type u} {spec : OracleSpec.{u, u} ι} {α : Type u}

/-- Single-step invariant of `RandomOracle.answer`: a supported transition binds `q` to the
returned answer, preserves existing cache bindings, and keeps all cached answers in the support
of `dist`. -/
private theorem mem_support_answer_invariant [DecidableEq ι] (dist : (q : ι) → PMF (spec q)) (q : ι)
    {cache cache₁ : RandomOracle.Cache spec} {ans : spec q}
    (hsupp : ∀ q' v', cache q' = some v' → v' ∈ (dist q').support)
    (hmem : (ans, cache₁) ∈ (RandomOracle.answer dist q cache).support) :
    cache₁ q = some ans ∧
      (∀ q' v', cache q' = some v' → cache₁ q' = some v') ∧
      (∀ q' v', cache₁ q' = some v' → v' ∈ (dist q').support) := by
  cases hq : cache q with
  | some v₀ =>
    supp_cases hmem [RandomOracle.answer_of_some dist cache q v₀ hq] with ⟨rfl, rfl⟩
    exact ⟨hq, fun _ _ h => h, hsupp⟩
  | none =>
    supp_cases hmem [RandomOracle.answer_of_none dist cache q hq] with ⟨v, hv, rfl, rfl⟩
    refine ⟨Function.update_self q (some v) cache, fun q' v' hq' => ?_, fun q' v' hq' => ?_⟩
    · have hne : q' ≠ q := by
        rintro rfl
        rw [hq] at hq'
        cases hq'
      rw [Function.update_of_ne hne, hq']
    · by_cases hne : q' = q
      · subst hne
        rw [Function.update_self] at hq'
        cases hq'
        exact hv
      · rw [Function.update_of_ne hne] at hq'
        exact hsupp q' v' hq'

/-- Multi-step invariant of `runWith (RandomOracle.answer dist)`: any outcome `(res, cache')` in
the support of a run from `cache` produces a final cache `cache'` extending `cache` whose entries
lie in `(dist q).support`, and `res = evalPure h prog` for every total function `h` extending
`cache'`. -/
theorem mem_support_runWith_answer_invariant [DecidableEq ι] (dist : (q : ι) → PMF (spec q))
    (prog : OracleComp spec α) {cache cache' : RandomOracle.Cache spec} {res : α}
    (hsupp : ∀ q' v', cache q' = some v' → v' ∈ (dist q').support)
    (hmem : (res, cache') ∈ (runWith (RandomOracle.answer dist) prog cache).support) :
    (∀ q' v', cache q' = some v' → cache' q' = some v') ∧
      (∀ q' v', cache' q' = some v' → v' ∈ (dist q').support) ∧
      (∀ h : (q : ι) → spec q,
        (∀ q' v', cache' q' = some v' → h q' = v') → res = evalPure h prog) := by
  induction prog using OracleComp.induction generalizing cache with
  | pure a =>
    supp_cases hmem [runWith_pure] with ⟨rfl, rfl⟩
    exact ⟨fun _ _ h => h, hsupp, fun _ _ => rfl⟩
  | query_bind q cont ih =>
    supp_cases hmem [runWith_bind, runWith_query] with ⟨⟨ans, cache₁⟩, hans, hcont⟩
    obtain ⟨hq_ans, hsub₁, hsupp₁⟩ := mem_support_answer_invariant dist q hsupp hans
    obtain ⟨hsub₂, hsupp', heval⟩ := ih ans hsupp₁ hcont
    refine ⟨fun q' v' h => hsub₂ q' v' (hsub₁ q' v' h), hsupp', fun h hh => ?_⟩
    have hq_eq : h q = ans := hh q ans (hsub₂ q ans hq_ans)
    simp only [evalPure_bind, evalPure_query, hq_eq]
    exact heval h hh

/-- Extend a partial cache `cache` to a total deterministic oracle by returning `v` when
`cache q = some v` and otherwise choosing an element in `(dist q).support`. -/
noncomputable def cacheOracle (dist : (q : ι) → PMF (spec q))
    (cache : RandomOracle.Cache spec) (q : ι) : spec q :=
  (cache q).getD (Classical.choose (dist q).support_nonempty)

theorem cacheOracle_eq_of_eq_some (dist : (q : ι) → PMF (spec q))
    (cache : RandomOracle.Cache spec) {q : ι} {v : spec q} (h : cache q = some v) :
    cacheOracle dist cache q = v := by
  simp [cacheOracle, h]

theorem cacheOracle_mem_support (dist : (q : ι) → PMF (spec q))
    {cache : RandomOracle.Cache spec}
    (hsupp : ∀ q' v', cache q' = some v' → v' ∈ (dist q').support) (q : ι) :
    cacheOracle dist cache q ∈ (dist q).support := by
  unfold cacheOracle
  cases h : cache q with
  | none => exact Classical.choose_spec (dist q).support_nonempty
  | some v => exact hsupp q v h

/-- If an oracle program evaluates to `a` under every deterministic oracle drawn from the
point-wise support of `dist`, then running it under the lazy random oracle
`RandomOracle.answer dist` from the empty cache yields `PMF.pure a`. -/
theorem map_fst_runWith_answer_eq_pure [DecidableEq ι] (dist : (q : ι) → PMF (spec q))
    (prog : OracleComp spec α) (a : α)
    (hprog : ∀ h : (q : ι) → spec q, (∀ q, h q ∈ (dist q).support) → evalPure h prog = a) :
    (runWith (RandomOracle.answer dist) prog (fun _ => none)).map Prod.fst = PMF.pure a := by
  refine (Probability.PMF.map_congr_on_support _ Prod.fst (Function.const _ a) ?_).trans
    (PMF.map_const _ a)
  rintro ⟨res, cache'⟩ hmem
  obtain ⟨-, hsupp', heval⟩ := mem_support_runWith_answer_invariant dist prog (by simp) hmem
  have heq := heval (cacheOracle dist cache')
    (fun _ _ h => cacheOracle_eq_of_eq_some dist cache' h)
  exact heq.trans (hprog (cacheOracle dist cache') (cacheOracle_mem_support dist hsupp'))

end OracleComp

end Cslib
