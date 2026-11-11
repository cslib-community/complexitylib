/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.ParallelRepetition.Factorization
import Complexity.Probability.Product

/-! # The factorization in Holenstein's embedding lemma

Bounds on the two distances of Corollary 5.3, for the law of `((x_j, y_j), S)` under `W_C`, pass
through the second stage of the embedding to strategy extraction. The second stage also composes
with the first through `IsEmbeddable.trans` directly. In the one-fold repetition with
nothing conditioned, `S` carries no information, so the first stage is exact; the second stage then
bounds every strategy's probability of winning the single coordinate by the value of the game.
-/

namespace ComplexityTests.RepetitionFactorization

open Cslib.PCP Cslib.PCP.ParallelRepetition
open Cslib.Probability.CorrelatedSampling (IsEmbeddable withKernel condX condY
  isEmbeddable_diag_of_dist_le)
open scoped Cslib.Probability.PMF

variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  (G : TwoProverGame X Y A B)

-- Corollary 5.3 for the law of `((x_j, y_j), S)`, the second stage and strategy extraction
-- compose: the error of the first stage is the error of the coordinate.
example [Nonempty A] [Nonempty B] {n : ℕ} (ha : (Fin n → X) → Fin n → A)
    (hb : (Fin n → Y) → Fin n → B) (C : Finset (Fin n))
    (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support) (j : {i // i ∉ C})
    {ε₁ ε₂ : ℝ}
    (h₁ : dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
      (withKernel G.questions fun xy =>
        condX ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)) xy.1) ≤ ε₁)
    (h₂ : dist ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω))
      (withKernel G.questions fun xy =>
        condY ((condLaw G C ha hb hC).map fun ω => (ω.2 j, shared ha hb j ω)) xy.2) ≤ ε₂) :
    G.winProbOn ha hb (insert (j : Fin n) C) ≤
      G.winProbOn ha hb C * (G.value + (7 * ε₁ + 2 * ε₂)) := by
  have h := isEmbeddable_diag_of_dist_le _ _ h₁ h₂
  rw [PMF.map_comp] at h
  exact G.winProbOn_insert_le ha hb C j hC (isEmbeddable_filter_questions_of_shared j hC h)

-- The second stage starts from the first stage's output, regrouped by `IsEmbeddable.trans`.
example {n : ℕ} (ha : (Fin n → X) → Fin n → A) (hb : (Fin n → Y) → Fin n → B)
    (C : Finset (Fin n)) (hC : ∃ q ∈ G.winsOn ha hb C, q ∈ (G.pow n).questions.support)
    (j : {i // i ∉ C}) {ε : ℝ}
    (h : IsEmbeddable G.questions
      ((condLaw G C ha hb hC).map fun ω => (ω.2 j, (shared ha hb j ω, shared ha hb j ω))) ε) :
    IsEmbeddable G.questions
      (((condLaw G C ha hb hC).map fun ω =>
        ((((ω.2 j).1, shared ha hb j ω), ((ω.2 j).2, shared ha hb j ω)),
          (Prod.fst ∘ ω.2, Prod.snd ∘ ω.2))).map
        fun (((x, s), (y, t)), (u, v)) => ((x, y), ((s, u), (t, v)))) (ε + 0) :=
  h.trans (by rw [PMF.map_comp]; exact isEmbeddable_map_condLaw_tuples j hC)

-- In the one-fold repetition with nothing conditioned, the first stage is exact: `S` is trivial
-- and the pair at the only coordinate has the law of the questions of `G`. The second stage then
-- bounds the probability of winning that coordinate by the value of `G`.
example [Nonempty A] [Nonempty B] (ha : (Fin 1 → X) → Fin 1 → A)
    (hb : (Fin 1 → Y) → Fin 1 → B) : G.winProbOn ha hb {0} ≤ G.value := by
  obtain ⟨q, hq⟩ := (G.pow 1).questions.support_nonempty
  have hC : ∃ q ∈ G.winsOn ha hb ∅, q ∈ (G.pow 1).questions.support := ⟨q, by simp, hq⟩
  let j : {i // i ∉ (∅ : Finset (Fin 1))} := ⟨0, Finset.notMem_empty 0⟩
  -- `S` has no questions, halves or answers.
  let s₀ : Shared X Y A B (∅ : Finset (Fin 1)) j := ⟨fun i => absurd i.2 (Finset.notMem_empty _),
    fun i => absurd (Subtype.ext (Subsingleton.elim _ _)) i.2,
    fun i => absurd i.2 (Finset.notMem_empty _)⟩
  have hS : ∀ ω, shared ha hb j ω = s₀ := by
    intro ω
    simp only [shared, Shared.ofRevealed, s₀, Shared.mk.injEq]
    exact ⟨funext fun i => absurd i.2 (Finset.notMem_empty _),
      funext fun i => absurd (Subtype.ext (Subsingleton.elim _ _)) i.2,
      funext fun i => absurd i.2 (Finset.notMem_empty _)⟩
  -- The pair at the coordinate has the law of the questions.
  have hpair : (condLaw G ∅ ha hb hC).map (fun ω => ω.2 j) = G.questions := by
    have h := congrArg (PMF.map fun q : Fin 1 → X × Y => q j) (map_snd_condLaw hC)
    rw [PMF.map_comp, Cslib.Probability.PMF.filter_eq_self_of_support_subset _ _ _
      (fun q _ => by simp [winsOnPairs])] at h
    rw [← Cslib.Probability.PMF.pi_map_eval (fun _ : Fin 1 => G.questions) j]
    exact h
  have hstage1 : IsEmbeddable G.questions ((condLaw G ∅ ha hb hC).map fun ω =>
      (ω.2 j, (shared ha hb j ω, shared ha hb j ω))) 0 := by
    refine IsEmbeddable.of_dist_le (PMF.pure ()) (fun _ _ => s₀) (fun _ _ => s₀) (le_of_eq ?_)
    rw [dist_eq_zero, ← hpair, PMF.bind_map]
    simp only [PMF.pure_map, Function.comp_def, hS]
    exact PMF.bind_pure_comp _ _
  have h := G.winProbOn_insert_le ha hb ∅ j hC
    (isEmbeddable_filter_questions_of_shared j hC hstage1)
  simpa using h

end ComplexityTests.RepetitionFactorization
