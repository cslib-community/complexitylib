/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.SuccinctDictionaryAbstract

/-!
# Formal Abstract Tests: Fixed-Capacity Succinct Dynamic Dictionary (`SuccinctDictionaryAbstract`)

Non-vacuity and concrete evaluation checks for `ComplexityAbstracts.SuccinctDictionaryAbstract`.
-/

namespace ComplexityTests.Abstracts.SuccinctDictionaryTests

open scoped ENNReal
open ComplexityAbstracts.SuccinctDictionaryAbstract

/-! ## Concrete Resource Function Evaluations -/

example : optBits 16 8 4 = 23 := by decide
example : logLogFactor 4 = 1 := by decide
example : logLogFactor 16 = 2 := by decide
example : succinctWords 81 213 16 8 64 4 = 219 := by decide

/-! ## Sample Valid Operation History and Semantics -/

abbrev k2 : Fin 16 := ⟨2, by decide⟩
abbrev k6 : Fin 16 := ⟨6, by decide⟩

example :
    prepareDynDictRegs (⟨244, by decide⟩ : Fin 256) ⟨245, by decide⟩ ⟨246, by decide⟩
      (.insert k2 5) (fun _ => 0) ⟨244, by decide⟩ = 1 :=
  rfl

example :
    prepareDynDictRegs (⟨244, by decide⟩ : Fin 256) ⟨245, by decide⟩ ⟨246, by decide⟩
      (.insert k2 5) (fun _ => 0) ⟨245, by decide⟩ = 2 :=
  rfl

example :
    prepareDynDictRegs (⟨244, by decide⟩ : Fin 256) ⟨245, by decide⟩ ⟨246, by decide⟩
      (.insert k2 5) (fun _ => 0) ⟨246, by decide⟩ = 5 :=
  rfl

example :
    decodeOptionRegs (⟨252, by decide⟩ : Fin 256) ⟨253, by decide⟩ (fun _ => 0) = none :=
  rfl

example :
    decodeOptionRegs (⟨252, by decide⟩ : Fin 256) ⟨253, by decide⟩ (fun _ => 7) = some 7 :=
  rfl

/-- Six-operation dynamic dictionary history on `Fin 16` with value bound `V = 8` and capacity
`n_max = 4`: insert `k2 ↦ 5`, insert `k6 ↦ 3`, query `k2`, delete `k2`, query `k2`, and query `k6`.
-/
def sampleOps : List (DynDictOp 16) :=
  [ .insert k2 5
  , .insert k6 3
  , .query k2
  , .delete k2
  , .query k2
  , .query k6 ]

theorem validDynDictHistory_sampleOps :
    ValidDynDictHistory 8 4 (emptyDict 16) sampleOps := by
  dsimp only [ValidDynDictHistory, validDynDictOp, stepDynDict, emptyDict, sampleOps]
  refine ⟨⟨Or.inl (by decide), by decide⟩,
    ⟨Or.inl (by decide), by decide⟩,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

lemma wordBounded_zero {r : ℕ} : WordBounded 64 (fun (_ : Fin r) => 0) (fun _ => 0) :=
  ⟨fun _ => (by decide : 0 < 2 ^ 64), fun _ => (by decide : 0 < 2 ^ 64)⟩

/-! ## Headline Theorem Space and Initialization Budget Non-Vacuity -/

/-- Non-vacuity of `succinctDynamicDictionary` at `(U, V, w, n_max) = (16, 8, 64, 4)`: produces
`r ≥ 292`, `C_op`, `sp`, `initBudget ≤ 31 * 4 + 1092`, `p_init`, and `p_op` with
`sp ≤ succinctWords 81 213 16 8 64 4 = 219` and end-to-end execution on `sampleOps` at `base = 0`.
-/
theorem nonvacuous_succinctDynamicDictionary :
    ∃ (r C_op sp initBudget : ℕ) (hr : 292 ≤ r) (p_init p_op : List (Instr r))
      (Seed : Type) (μ_init μ_final : PMF (CoupledState Seed r)) (T_ops : ℝ≥0∞),
      initBudget ≤ 31 * 4 + 1092 ∧
      sp ≤ succinctWords 81 213 16 8 64 4 ∧
      ExecProgramDist 64 p_init ⟨247, by omega⟩ (fun _ => 0) (fun _ => 0)
        (μ_init.map CoupledState.toRegMem) initBudget ∧
      (∀ p ∈ μ_init.support,
        WordBounded 64 p.reg p.mem ∧
        p.reg ⟨0, by omega⟩ = 0 ∧
        p.reg ⟨240, by omega⟩ = 0 + sp ∧
        UnchangedOutside 0 sp (fun _ => 0) p.mem) ∧
      ExecDynDictOps 64 p_op
        ⟨244, by omega⟩ ⟨245, by omega⟩ ⟨246, by omega⟩
        ⟨247, by omega⟩ ⟨252, by omega⟩ ⟨253, by omega⟩
        0 sp (emptyDict 16) sampleOps
        μ_init μ_final T_ops ∧
      T_ops ≤ ((sampleOps.length * C_op : ℕ) : ℝ≥0∞) := by
  obtain ⟨r, C_op, hr, hdict⟩ := succinctDynamicDictionary
  obtain ⟨sp, initBudget, p_init, p_op, hinit_le, hsp_le, hrun⟩ :=
    hdict 16 8 64 4
  have hsp : sp ≤ succinctWords 81 213 16 8 64 4 :=
    hsp_le (by decide) (by decide) (by decide)
  have hsp_lt : 0 + sp < 2 ^ 64 := by
    have h219 : succinctWords 81 213 16 8 64 4 = 219 := by decide
    omega
  obtain ⟨Seed, μ_init, hinit, hsupp, hseq⟩ :=
    hrun 0 (by decide) (by decide) (by decide) (by decide) hsp_lt
      (fun _ => 0) (fun _ => 0) wordBounded_zero rfl (fun _ _ _ => rfl)
  obtain ⟨μ_final, T_ops, hops, hbound⟩ :=
    hseq sampleOps validDynDictHistory_sampleOps
  exact ⟨r, C_op, sp, initBudget, hr, p_init, p_op, Seed, μ_init, μ_final, T_ops,
    hinit_le, hsp, hinit, hsupp, hops, hbound⟩

end ComplexityTests.Abstracts.SuccinctDictionaryTests
