/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Languages.Probabilistic.RandomPermutation

/-! Direct clients of the shared reverse switching, cache-support inequalities, and bidirectional
query deduplication (`bidirDedup`). -/

set_option linter.privateModule false

open Cslib Cslib.Probability Cslib.RandomPermutation
open scoped ENNReal

example {α β γ : Type} [DecidableEq α] [Fintype α] [Nonempty α]
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (next : β → PMF γ) (c : γ) :
    ((((OracleComp.interpret forgetfulAnswer program).run []).map Prod.fst).bind next) c ≤
    ((do
      let π ← PMF.uniformOfFintype (Equiv.Perm α)
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) program).bind next) c +
      (Q.choose 2 : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ :=
  forgetfulAnswer_bind_apply_le_uniformPerm hQ next c

example {α β : Type} [DecidableEq α] [Fintype α] [Nonempty α]
    {program : OracleComp (PermOracleSpec α) β} {Q : ℕ}
    (hQ : OracleComp.IsQueryBounded program Q) (P : Cache α → Prop) :
    ((OracleComp.interpret forgetfulAnswer program).run []).toOuterMeasure {x | P x.2} ≤
      ((OracleComp.interpret forgetfulAnswer program).run []).toOuterMeasure
        {x | (x.2.Pairwise (fun a b => a.1 ≠ b.1) ∧
          x.2.Pairwise (fun a b => a.2 ≠ b.2) ∧ x.2.length ≤ Q) ∧ P x.2} +
      (Q.choose 2 : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ :=
  toOuterMeasure_forgetfulAnswer_le_pairwise_and_length_le_add hQ P

example {α β γ : Type} [DecidableEq α] [Fintype α] [Nonempty α]
    (a : β) (next : β → PMF γ) (c : γ) :
    ((((OracleComp.interpret forgetfulAnswer (pure a : OracleComp (PermOracleSpec α) β)).run
      []).map Prod.fst).bind next) c ≤
    ((do
      let π ← PMF.uniformOfFintype (Equiv.Perm α)
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) (pure a)).bind next) c +
      (Nat.choose 0 2 : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ :=
  forgetfulAnswer_bind_apply_le_uniformPerm (OracleComp.IsCostBounded.pure a 0) next c

/-! ### Adaptive bidirectional query deduplication (`bidirDedup`) on `Fin 4` -/

/-- Non-involution 4-cycle `0 ↦ 1 ↦ 2 ↦ 3 ↦ 0` on `Fin 4`, separating forward and inverse
evaluation (`cycle4 0 = 1 ≠ 3 = cycle4.symm 0`). -/
private def cycle4 : Equiv.Perm (Fin 4) where
  toFun x := x + 1
  invFun y := y - 1
  left_inv x := add_sub_cancel_right x 1
  right_inv y := sub_add_cancel y 1

example : cycle4 0 = 1 ∧ cycle4.symm 0 = 3 := ⟨rfl, rfl⟩

/-- Adaptive 5-query bidirectional program over `PermOracleSpec (Fin 4)` interleaving:
1. `.forward 0` (fresh forward query `0 ↦ y₁`),
2. `.forward 0` (repeated forward query hitting `(0, y₁)`),
3. `.inverse y₁` (adaptive inverse query hitting cached forward output `y₁`),
4. `.inverse (y₁ + 2)` (adaptive fresh inverse query since `y₁ + 2 ≠ y₁`, returning `x₄`),
5. `.forward x₄` (adaptive forward query hitting cached inverse preimage `x₄`). -/
private def adaptiveBidirProg :
    OracleComp (PermOracleSpec (Fin 4)) (Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4) := do
  let y₁ ← OracleComp.query (spec := PermOracleSpec (Fin 4)) (.forward 0)
  let y₂ ← OracleComp.query (spec := PermOracleSpec (Fin 4)) (.forward 0)
  let x₃ ← OracleComp.query (spec := PermOracleSpec (Fin 4)) (.inverse y₁)
  let x₄ ← OracleComp.query (spec := PermOracleSpec (Fin 4)) (.inverse (y₁ + 2))
  let y₅ ← OracleComp.query (spec := PermOracleSpec (Fin 4)) (.forward x₄)
  pure (y₁, y₂, x₃, x₄, y₅)

private theorem isQueryBounded_adaptiveBidirProg :
    OracleComp.IsQueryBounded adaptiveBidirProg 5 := by
  dsimp [adaptiveBidirProg]
  refine ((OracleComp.IsCostBounded.query (spec := PermOracleSpec (Fin 4)) (.forward 0)).bind
    fun y₁ =>
      (OracleComp.IsCostBounded.query (spec := PermOracleSpec (Fin 4)) (.forward 0)).bind
        fun y₂ =>
          (OracleComp.IsCostBounded.query (spec := PermOracleSpec (Fin 4)) (.inverse y₁)).bind
            fun x₃ =>
              (OracleComp.IsCostBounded.query (spec := PermOracleSpec (Fin 4))
                (.inverse (y₁ + 2))).bind fun x₄ =>
                  (OracleComp.IsCostBounded.query (spec := PermOracleSpec (Fin 4))
                    (.forward x₄)).bind fun y₅ =>
                      OracleComp.IsCostBounded.pure (y₁, y₂, x₃, x₄, y₅) 0).mono (by omega)

/-- `bidirDedup` preserves the 5-query pathwise bound. -/
example : OracleComp.IsQueryBounded (bidirDedup adaptiveBidirProg) 5 :=
  isQueryBounded_bidirDedup isQueryBounded_adaptiveBidirProg

/-- Deterministic counting handler in `StateM ℕ` recording how many underlying oracle calls are
actually invoked. -/
private def countingEvalPerm (π : Equiv.Perm (Fin 4)) (q : PermQuery (Fin 4)) :
    StateM ℕ (Fin 4) := fun count =>
  (evalPerm π q, count + 1)

/-- Without deduplication, `adaptiveBidirProg` against `cycle4` makes all `5` underlying oracle
calls and returns `(1, 1, 0, 2, 3)`. -/
example :
    (OracleComp.interpret (countingEvalPerm cycle4) adaptiveBidirProg).run 0 =
      ((1, 1, 0, 2, 3), 5) := rfl

/-- With `bidirDedup`, the same 5-query adaptive program makes only `2` underlying oracle calls
(strictly fewer than `5`), returning the identical tuple `(1, 1, 0, 2, 3)` and final cache
`[(2, 3), (0, 1)]`. -/
example :
    (OracleComp.interpret (countingEvalPerm cycle4) (bidirDedup adaptiveBidirProg)).run 0 =
      (((1, 1, 0, 2, 3), [(2, 3), (0, 1)]), 2) := rfl

example :
    ((OracleComp.interpret (countingEvalPerm cycle4) (bidirDedup adaptiveBidirProg)).run 0).2 <
      ((OracleComp.interpret (countingEvalPerm cycle4) adaptiveBidirProg).run 0).2 := by
  decide

/-- Concrete check of `AgreesWith` and pairwise-distinct domain and range entries on the resulting
cache `[(2, 3), (0, 1)]`. -/
example :
    let cache' :=
      ((OracleComp.interpret (countingEvalPerm cycle4) (bidirDedup adaptiveBidirProg)).run 0).1.2
    AgreesWith cache' cycle4 ∧
      cache'.Pairwise (fun a b => a.1 ≠ b.1) ∧
      cache'.Pairwise (fun a b => a.2 ≠ b.2) := by
  decide

/-- Stateful `PMF` counting handler for `evalPerm π`, incrementing the underlying query counter on
each forwarded call. -/
private noncomputable def countingPMF (π : Equiv.Perm (Fin 4)) (q : PermQuery (Fin 4)) :
    StateT ℕ PMF (Fin 4) := fun count =>
  PMF.pure (evalPerm π q, count + 1)

@[simp] private theorem run_countingPMF (π : Equiv.Perm (Fin 4)) (q : PermQuery (Fin 4))
    (count : ℕ) :
    (countingPMF π q).run count = PMF.pure (evalPerm π q, count + 1) := rfl

/-- Against `countingPMF π` for every permutation `π : Equiv.Perm (Fin 4)`, raw `adaptiveBidirProg`
makes `5` underlying calls while `bidirDedup adaptiveBidirProg` makes `2` underlying calls and
produces the exact same output `(π 0, π 0, 0, π.symm (π 0 + 2), π 0 + 2)`. -/
example (π : Equiv.Perm (Fin 4)) :
    (OracleComp.interpret (countingPMF π) adaptiveBidirProg).run 0 =
      PMF.pure ((π 0, π 0, 0, π.symm (π 0 + 2), π 0 + 2), 5) ∧
    (OracleComp.interpret (countingPMF π) (bidirDedup adaptiveBidirProg)).run 0 =
      PMF.pure (((π 0, π 0, 0, π.symm (π 0 + 2), π 0 + 2),
        [(π.symm (π 0 + 2), π 0 + 2), (0, π 0)]), 2) := by
  have hne : π 0 + 2 ≠ π 0 := by
    intro h
    have h2 : (2 : Fin 4) = 0 := add_left_cancel (h.trans (add_zero (π 0)).symm)
    exact absurd h2 (by decide)
  have hinv : invLookup [(0, π 0)] (π 0 + 2) = none := by
    rw [invLookup_eq_none_iff]
    intro e he
    rw [List.mem_singleton] at he
    subst he
    exact hne.symm
  have hhit_fwd : ([(0, π 0)] : Cache (Fin 4)).lookup 0 = some (π 0) := by simp
  have hhit_inv : invLookup [(0, π 0)] (π 0) = some 0 := by simp [invLookup]
  have hhit_fwd2 :
      ([(π.symm (π 0 + 2), π 0 + 2), (0, π 0)] : Cache (Fin 4)).lookup (π.symm (π 0 + 2)) =
        some (π 0 + 2) := by simp
  constructor
  · simp [adaptiveBidirProg, StateT.run_bind, Probability.PMF.monad_bind_eq_bind, PMF.pure_map]
  · simp only [bidirDedup, adaptiveBidirProg, OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure]
    change (((OracleComp.interpret (countingPMF π) (bidirDedupStep (.forward 0) [])).run 0).bind
      fun p₁ =>
        ((OracleComp.interpret (countingPMF π) (bidirDedupStep (.forward 0) p₁.1.2)).run
          p₁.2).bind fun p₂ =>
          ((OracleComp.interpret (countingPMF π) (bidirDedupStep (.inverse p₁.1.1) p₂.1.2)).run
            p₂.2).bind fun p₃ =>
            ((OracleComp.interpret (countingPMF π)
              (bidirDedupStep (.inverse (p₁.1.1 + 2)) p₃.1.2)).run p₃.2).bind fun p₄ =>
              ((OracleComp.interpret (countingPMF π)
                (bidirDedupStep (.forward p₄.1.1) p₄.1.2)).run p₄.2).bind fun p₅ =>
                PMF.pure (((p₁.1.1, p₂.1.1, p₃.1.1, p₄.1.1, p₅.1.1), p₅.1.2), p₅.2)) = _
    rw [bidirDedupStep_forward_of_none (by rfl)]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
      StateT.run_bind, StateT.run_pure, run_countingPMF, evalPerm_forward,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
    rw [bidirDedupStep_forward_of_some hhit_fwd]
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
    rw [bidirDedupStep_inverse_of_some hhit_inv]
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
    rw [bidirDedupStep_inverse_of_none hinv]
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, OracleComp.interpret_pure,
      StateT.run_bind, StateT.run_pure, run_countingPMF, evalPerm_inverse,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]
    rw [bidirDedupStep_forward_of_some hhit_fwd2]
    simp only [OracleComp.interpret_pure, StateT.run_pure,
      Probability.PMF.monad_pure_eq_pure, PMF.pure_bind]

/-- Exact output-distribution equality for `adaptiveBidirProg` under `evalPerm π` and under a
uniformly random permutation on `Fin 4`, plus the `forgetfulAnswer` correspondence. -/
example (π : Equiv.Perm (Fin 4)) :
    (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
      (bidirDedup adaptiveBidirProg)).map Prod.fst =
    OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) adaptiveBidirProg :=
  map_fst_interpret_bidirDedup_evalPerm π adaptiveBidirProg

example :
    (do
      let π ← PMF.uniformOfFintype (Equiv.Perm (Fin 4))
      (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
        (bidirDedup adaptiveBidirProg)).map Prod.fst) =
    (do
      let π ← PMF.uniformOfFintype (Equiv.Perm (Fin 4))
      OracleComp.interpret (fun q => PMF.pure (evalPerm π q)) adaptiveBidirProg) := by
  simp only [map_fst_interpret_bidirDedup_evalPerm]

example :
    OracleComp.interpret (fun _ : PermQuery (Fin 4) => PMF.uniformOfFintype (Fin 4))
      (bidirDedup adaptiveBidirProg) =
    (OracleComp.interpret forgetfulAnswer adaptiveBidirProg).run [] :=
  interpret_bidirDedup_uniformOfFintype adaptiveBidirProg

/-- Every supported run of `bidirDedup adaptiveBidirProg` against `evalPerm π` yields a cache
agreeing with `π` whose domain and range entries are pairwise distinct, and every supported
transcript against any stateful handler has non-repeating queries and cache length at most `5`. -/
example (π : Equiv.Perm (Fin 4)) {result : Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4}
    {cache' : Cache (Fin 4)}
    (hmem : (result, cache') ∈
      (OracleComp.interpret (fun q => PMF.pure (evalPerm π q))
        (bidirDedup adaptiveBidirProg)).support) :
    AgreesWith cache' π ∧
      cache'.Pairwise (fun a b => a.1 ≠ b.1) ∧
      cache'.Pairwise (fun a b => a.2 ≠ b.2) :=
  agreesWith_and_pairwise_of_mem_support_bidirDedup π adaptiveBidirProg hmem

example (π : Equiv.Perm (Fin 4)) {result : Fin 4 × Fin 4 × Fin 4 × Fin 4 × Fin 4}
    {cache' : Cache (Fin 4)} {count' : ℕ}
    {transcript : OracleComp.Transcript (PermOracleSpec (Fin 4))}
    (hmem : ((result, cache'), (count', transcript)) ∈
      ((OracleComp.interpret (OracleComp.withTranscript (countingPMF π))
        (bidirDedup adaptiveBidirProg)).run (0, [])).support) :
    cache' = transcript.map PermQuery.toCacheEntry ∧
      (transcript.map Sigma.fst).Nodup ∧
      cache'.length ≤ 5 := by
  have hceq := cache_eq_of_mem_support_withTranscript_bidirDedup (countingPMF π)
    adaptiveBidirProg hmem
  have hnodup := nodup_transcript_of_mem_support_withTranscript_bidirDedup (countingPMF π)
    adaptiveBidirProg hmem
  have hlen := (isQueryBounded_bidirDedup isQueryBounded_adaptiveBidirProg).length_transcript_le
    (countingPMF π) hmem
  refine ⟨hceq, hnodup, ?_⟩
  rw [hceq, List.length_map]
  exact hlen
