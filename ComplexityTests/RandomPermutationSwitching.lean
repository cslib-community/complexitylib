/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Languages.Probabilistic.RandomPermutation

/-! Direct clients of the shared reverse switching and cache-support inequalities. -/

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
