/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Promise.Randomized
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List


import Diag1155.Measure
/-! Tests for probabilistic promise classes (`PromiseBPP`, `PromiseRP`, `PromiseCoRP`) and
randomized one-sided promise reductions (`RPReducible`, `RPReducibleWithError`), including
nonvacuous coin-flip solvers, soundness strictly between `2 / 3` and `1`, and the `s ≤ 0` edge
case. -/


diag1155_install
namespace ComplexityTests.PromiseProbabilistic

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-! ### Randomized reductions on promise problems -/

example {X : PromiseProblem α} {Y : PromiseProblem β} :
    PromiseProblem.RPReducible encA encB X Y ↔
      ∃ R : α → Cslib.ProbComp β, Cslib.Probability.IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ∀ b ∈ (Cslib.ProbComp.eval (R a)).support, b ∈ Y.yes) ∧
        ∀ a ∈ X.no, 2 / 3 ≤ ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.no).toReal :=
  Iff.rfl

example {X : PromiseProblem α} {Y : PromiseProblem β} :
    PromiseProblem.RPReducible encA encB X Y ↔
      ∃ R : α → Cslib.ProbComp β, Cslib.Probability.IsPPTOn encA encB R ∧
        (∀ a ∈ X.yes, ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal = 1) ∧
        ∀ a ∈ X.no, 2 / 3 ≤ ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.no).toReal :=
  PromiseProblem.rpReducible_iff_toOuterMeasure_eq_one

example {X : PromiseProblem α} {Y : PromiseProblem β} {s : α → ℝ} :
    PromiseProblem.RPReducibleWithError encA encB s Xᶜ Yᶜ ↔
      ∃ R : α → Cslib.ProbComp β, Cslib.Probability.IsPPTOn encA encB R ∧
        (∀ a ∈ X.no, ∀ b ∈ (Cslib.ProbComp.eval (R a)).support, b ∈ Y.no) ∧
        ∀ a ∈ X.yes, s a ≤ ((Cslib.ProbComp.eval (R a)).toOuterMeasure Y.yes).toReal :=
  PromiseProblem.rpReducibleWithError_compl_iff

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (h : PromiseProblem.PolyTimeReducible encA encB X Y) :
    PromiseProblem.RPReducible encA encB X Y :=
  h.rpReducible

example {X : PromiseProblem α} : PromiseProblem.RPReducible encA encA X X :=
  PromiseProblem.RPReducible.refl encA X

example {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    {s₁ : α → ℝ} {s₂ : ℝ} (hs₂ : 0 ≤ s₂)
    (hXY : PromiseProblem.RPReducibleWithError encA encB s₁ X Y)
    (hYZ : PromiseProblem.RPReducibleWithError encB encC (fun _ => s₂) Y Z) :
    PromiseProblem.RPReducibleWithError encA encC (fun a => s₁ a * s₂) X Z :=
  hXY.trans hYZ hs₂

example {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    {s₁ : α → ℝ} {s₂ : ℝ} (hs₂ : s₂ ≤ 1)
    (hXY : PromiseProblem.RPReducibleWithError encA encB s₁ X Y)
    (hYZ : PromiseProblem.RPReducibleWithError encB encC (fun _ => s₂) Y Z) :
    PromiseProblem.RPReducibleWithError encA encC (fun a => s₁ a + s₂ - 1) X Z :=
  hXY.trans_add hYZ hs₂

example {X : PromiseProblem α} {Y : PromiseProblem β} {Z : PromiseProblem γ}
    {s : β → ℝ} {f : α → β} (hf : ComputableInPolyTime f encA encB)
    (hyes : Set.MapsTo f X.yes Y.yes) (hno : Set.MapsTo f X.no Y.no)
    (hYZ : PromiseProblem.RPReducibleWithError encB encC s Y Z) :
    PromiseProblem.RPReducibleWithError encA encC (fun a => s (f a)) X Z :=
  hYZ.of_computableInPolyTime hf hyes hno

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.RPReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA :=
  hXY.mem_PromiseCoRP hY

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.RPReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA :=
  hXY.mem_PromiseBPP hY

example {X : PromiseProblem α} {Y : PromiseProblem β}
    (hXY : PromiseProblem.RPReducible encA encB Xᶜ Yᶜ)
    (hY : Y ∈ PromiseRP encB) : X ∈ PromiseRP encA :=
  hXY.mem_PromiseRP_of_compl hY

/-! ### Nonvacuous concrete instances -/

/-- A concrete `PromiseRP` solver using a real 1-bit coin flip: on `true`,
`V (b, r) = b && r.headD false` accepts `[true]` and rejects `[false]` (acceptance probability
`1 / 2`); on `false`, it rejects both coins (acceptance probability `0`). -/
example : PromiseProblem.ofSet ({true} : Set Bool) ∈ PromiseRP encBool := by
  refine ⟨1, fun p : Bool × List Bool => p.1 && p.2.headD false, by fun_prop,
    fun a => ⟨fun ha => ?_, fun ha r => ?_⟩⟩
  · obtain rfl : a = true := ha
    generalize hk : (1 : Polynomial ℕ).eval (encBool true).length = k
    rw [Polynomial.eval_one] at hk
    subst hk
    decide
  · have hfalse : a = false := by
      cases a
      · rfl
      · exfalso; exact ha rfl
    subst hfalse
    rfl

/-- A concrete randomized `RPReducible` reduction whose soundness on the no-instance `false` is
strictly between `2 / 3` and `1`: reading 2 random bits `r`,
`f (b, r) = b || (r.headD false && r.tail.headD false)` maps `true` exclusively to `true` (all 4
seeds) and maps `false` to `false` on 3 out of 4 seeds (soundness `3 / 4 ∈ (2 / 3, 1)`). -/
example : PromiseProblem.RPReducible encBool encBool
    (PromiseProblem.ofSet ({true} : Set Bool))
    (PromiseProblem.ofSet ({true} : Set Bool)) := by
  rw [PromiseProblem.rpReducible_iff_exists_seeded]
  refine ⟨2, fun p : Bool × List Bool => p.1 || (p.2.headD false && p.2.tail.headD false),
    by fun_prop, fun a ha r => ?_, fun a ha => ?_⟩
  · obtain rfl : a = true := ha
    simp
  · have hfalse : a = false := by
      cases a
      · rfl
      · exfalso; exact ha rfl
    subst hfalse
    generalize hk : (2 : Polynomial ℕ).eval (encBool false).length = k
    rw [Polynomial.eval_ofNat] at hk
    subst hk
    simp only [PromiseProblem.no_ofSet, Set.mem_compl_iff, Set.mem_singleton_iff]
    decide

/-- Edge case `s ≤ 0`: when `s a = 0`, even the constant yes-map `fun _ => pure true` (which maps
the no-instance `false` into the no-set `{false}` with probability `0`) satisfies
`RPReducibleWithError`. -/
example : PromiseProblem.RPReducibleWithError encBool encBool (fun _ => 0)
    (PromiseProblem.ofSet ({true} : Set Bool))
    (PromiseProblem.ofSet ({true} : Set Bool)) := by
  refine ⟨fun _ => pure true, (ComputableInPolyTime.const true).isPPTOn,
    fun a _ b hb => ?_, fun _ _ => ENNReal.toReal_nonneg⟩
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hb
  exact hb

end ComplexityTests.PromiseProbabilistic
