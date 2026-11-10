/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.StreamArithmetic.QueryTree
public import CslibFrontier.Foundations.Analysis.SignedDigitStream.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform numerical stream interface and stage composition

This module formalizes the uniform numerical interface and composition theorem of
[OpenAI2026LogSpace, Section 10.6, Theorem 10.9] together with reusable finite-state streaming
query-program building blocks and the clock-zero buffered margin test recipe (**Lemma 10.8**).

A `UniformStreamRecipe Op Struct` at slack `d ≥ 1` packages:
* a domain precondition `ValidEnv` on operand streams and structural leaves,
* an exact mathematical target value `targetVal : (Op → ℝ) → (Struct → Bool) → ℝ` in `[-1, 1]`,
* a family of deterministic conditional query programs `digitProg : ℕ → QueryProg Op Struct ℤ`,
* exact stream emission proofs (`emits_signed`, `emits_exact`) showing that emitted digits form a
  valid `{-6, ..., 6}` stream summing to `targetVal` with zero numerical drift across stages, and
* unconditional per-query allowance bounds (`j ≤ t + c * d` and suspended record length
  `L ≤ a * d + b * (t - j)` on digit queries, `L ≤ a * d + b * t` on clock-zero structural leaves)
  and `O(d + t)` peak intrinsic storage bounds.

As in `QueryTree`, `UniformStreamRecipe` and `UniformBoolRecipe` certify exact mathematical stream
semantics alongside `AllowanceBound` and `maxIntrinsicBits` over caller-supplied `QueryProg`
annotations; downstream native Turing or counter-program compilation realizes structured recipe
combinators rather than arbitrary host `QueryProg` continuations.

## Main definitions

* `Cslib.StreamArithmetic.IsNormSignedStream`: signed-digit stream with value in `[-1, 1]`.
* `Cslib.StreamArithmetic.AllowanceBound`: per-query overshoot and suspended-record inequality
  `(10.18)` of [OpenAI2026LogSpace].
* `Cslib.StreamArithmetic.UniformStreamRecipe`: certified exact-stream recipe at slack `d ≥ 1`.
* `Cslib.StreamArithmetic.UniformStreamRecipe.comp`: **Theorem 10.9** stage composition with common
  clock-drop coefficient unification and exact stream substitution.
* `Cslib.StreamArithmetic.UniformBoolRecipe`: certified clock-zero Boolean/structural test recipe.
* `Cslib.StreamArithmetic.bufferedTestRecipe`: **Lemma 10.8** finite buffered margin test recipe.

## Main results

* `Cslib.StreamArithmetic.AllowanceBound.mono_coeff`, `AllowanceBound.comp_child`: coefficient
  unification and clock-difference telescoping along composed query paths.
* `Cslib.StreamArithmetic.recipeOfMod16Prog`: lifts any mod-16 scaled-approximation residue program
  to an exact `UniformStreamRecipe` via Lemma 10.1 (`decodeDiffResidue 4`).
* `Cslib.StreamArithmetic.bufferedTestRecipe_true_of_two_mul_lt`,
  `bufferedTestRecipe_false_of_le`: soundness and completeness of `bufferedTestRecipe`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 10.5--10.6, Lemma 10.8 and Theorem 10.9 (23 September 2026, revision `7ef5c0cc`,
  not peer reviewed).
-/

public section

namespace Cslib.StreamArithmetic

open Cslib.SignedDigitStream Finset

universe u u' v

/-- A signed-digit stream in `{-6, ..., 6}` whose represented real value lies in `[-1, 1]`. -/
@[expose] def IsNormSignedStream (x : ℕ → ℤ) : Prop :=
  IsSignedStream x ∧ |streamVal x| ≤ 1

section AllowanceAccounting

/-- Per-query clock-overshoot and suspended-record inequality of
[OpenAI2026LogSpace, Equation (10.18), Theorem 10.9] at slack `d`, constants `(a, b, c)`, and
enclosing output clock `t`. -/
@[expose] def AllowanceBound {Op : Type u} {Struct : Type v} (d a b c t : ℕ) :
    QueryEvent Op Struct → Prop
  | .digit _ j L =>
      j ≤ t + c * d ∧ (L : ℤ) ≤ ((a * d : ℕ) : ℤ) + (b : ℤ) * ((t : ℤ) - (j : ℤ))
  | .struct _ L =>
      (L : ℤ) ≤ ((a * d : ℕ) : ℤ) + (b : ℤ) * (t : ℤ)

theorem AllowanceBound.mono_ac {Op : Type u} {Struct : Type v} {d a₀ a b c₀ c t : ℕ}
    (ha : a₀ ≤ a) (hc : c₀ ≤ c) {ev : QueryEvent Op Struct}
    (h : AllowanceBound d a₀ b c₀ t ev) :
    AllowanceBound d a b c t ev := by
  have had : a₀ * d ≤ a * d := Nat.mul_le_mul_right d ha
  have hcd : c₀ * d ≤ c * d := Nat.mul_le_mul_right d hc
  cases ev with
  | digit op j L =>
    obtain ⟨hj, hL⟩ := h
    refine ⟨by omega, ?_⟩
    have hadZ : ((a₀ * d : ℕ) : ℤ) ≤ ((a * d : ℕ) : ℤ) := by exact_mod_cast had
    linarith
  | struct sOp L =>
    have hadZ : ((a₀ * d : ℕ) : ℤ) ≤ ((a * d : ℕ) : ℤ) := by exact_mod_cast had
    exact le_trans h (by linarith)

/-- Increasing the clock-drop coefficient from `b₀` to `b ≥ b₀` is paid for by increasing `a₀` to
`a₀ + (b - b₀) * c₀` [OpenAI2026LogSpace, Theorem 10.9 proof]. -/
theorem AllowanceBound.mono_coeff {Op : Type u} {Struct : Type v} {d a₀ b₀ b c₀ t : ℕ}
    (hb : b₀ ≤ b) {ev : QueryEvent Op Struct}
    (h : AllowanceBound d a₀ b₀ c₀ t ev) :
    AllowanceBound d (a₀ + (b - b₀) * c₀) b c₀ t ev := by
  cases ev with
  | digit op j L =>
    obtain ⟨hj, hL⟩ := h
    refine ⟨hj, ?_⟩
    have hjZ : (j : ℤ) ≤ (t : ℤ) + ((c₀ * d : ℕ) : ℤ) := by exact_mod_cast hj
    have hbZ : (0 : ℤ) ≤ (b : ℤ) - (b₀ : ℤ) := by omega
    have hmul : (0 : ℤ) ≤ ((b : ℤ) - (b₀ : ℤ)) * ((t : ℤ) + ((c₀ * d : ℕ) : ℤ) - (j : ℤ)) :=
      mul_nonneg hbZ (by linarith)
    have hcast : (((a₀ + (b - b₀) * c₀) * d : ℕ) : ℤ) =
        ((a₀ * d : ℕ) : ℤ) + ((b : ℤ) - (b₀ : ℤ)) * ((c₀ * d : ℕ) : ℤ) := by
      have hsub : ((b - b₀ : ℕ) : ℤ) = (b : ℤ) - (b₀ : ℤ) := Int.ofNat_sub hb
      push_cast [Nat.add_mul, Nat.mul_assoc, hsub]
      ring
    rw [hcast]
    linarith
  | struct sOp L =>
    have hbZ : (b₀ : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
    have hmul : (b₀ : ℤ) * (t : ℤ) ≤ (b : ℤ) * (t : ℤ) := by gcongr
    have had : a₀ * d ≤ (a₀ + (b - b₀) * c₀) * d :=
      Nat.mul_le_mul_right d (Nat.le_add_right _ _)
    have hadZ : ((a₀ * d : ℕ) : ℤ) ≤ (((a₀ + (b - b₀) * c₀) * d : ℕ) : ℤ) := by
      exact_mod_cast had
    exact le_trans h (by linarith)

theorem AllowanceBound.mono_clock {Op : Type u} {Struct : Type v} {d a b c t₁ t₂ : ℕ}
    (ht : t₁ ≤ t₂) {ev : QueryEvent Op Struct}
    (h : AllowanceBound d a b c t₁ ev) :
    AllowanceBound d a b c t₂ ev := by
  have htZ : (t₁ : ℤ) ≤ (t₂ : ℤ) := by exact_mod_cast ht
  cases ev with
  | digit op j L =>
    obtain ⟨hj, hL⟩ := h
    refine ⟨by omega, ?_⟩
    have hmul : (b : ℤ) * ((t₁ : ℤ) - (j : ℤ)) ≤ (b : ℤ) * ((t₂ : ℤ) - (j : ℤ)) := by gcongr
    linarith
  | struct sOp L =>
    have hmul : (b : ℤ) * (t₁ : ℤ) ≤ (b : ℤ) * (t₂ : ℤ) := by gcongr
    exact le_trans h (by linarith)

theorem AllowanceBound.shift_clock_up {Op : Type u} {Struct : Type v} {d a b c t k : ℕ}
    (hd : 1 ≤ d) {ev : QueryEvent Op Struct}
    (h : AllowanceBound d a b c (t + k) ev) :
    AllowanceBound d (a + b * k) b (c + k) t ev := by
  have hkd : k ≤ k * d := Nat.le_mul_of_pos_right k hd
  cases ev with
  | digit op j L =>
    obtain ⟨hj, hL⟩ := h
    refine ⟨?_, ?_⟩
    · calc j ≤ t + k + c * d := hj
        _ ≤ t + (c * d + k * d) := by omega
        _ = t + (c + k) * d := by rw [Nat.add_mul]
    · have hbk : (b : ℤ) * (k : ℤ) ≤ (((b * k) * d : ℕ) : ℤ) := by
        have hnat : b * k ≤ (b * k) * d := Nat.le_mul_of_pos_right _ hd
        exact_mod_cast hnat
      have hcast : (((a + b * k) * d : ℕ) : ℤ) =
          ((a * d : ℕ) : ℤ) + (((b * k) * d : ℕ) : ℤ) := by
        push_cast [Nat.add_mul]
        ring
      have htk : ((t + k : ℕ) : ℤ) = (t : ℤ) + (k : ℤ) := by push_cast; ring
      rw [htk] at hL
      rw [hcast]
      linarith
  | struct sOp L =>
    have hbk : (b : ℤ) * (k : ℤ) ≤ (((b * k) * d : ℕ) : ℤ) := by
      have hnat : b * k ≤ (b * k) * d := Nat.le_mul_of_pos_right _ hd
      exact_mod_cast hnat
    have hcast : (((a + b * k) * d : ℕ) : ℤ) =
        ((a * d : ℕ) : ℤ) + (((b * k) * d : ℕ) : ℤ) := by
      push_cast [Nat.add_mul]
      ring
    have htk : ((t + k : ℕ) : ℤ) = (t : ℤ) + (k : ℤ) := by push_cast; ring
    change (L : ℤ) ≤ ((a * d : ℕ) : ℤ) + (b : ℤ) * ((t + k : ℕ) : ℤ) at h
    rw [htk] at h
    change (L : ℤ) ≤ (((a + b * k) * d : ℕ) : ℤ) + (b : ℤ) * (t : ℤ)
    rw [hcast]
    linarith

theorem AllowanceBound.addBits_const {Op : Type u} {Struct : Type v} {d a b c t : ℕ}
    (hd : 1 ≤ d) (extra : ℕ) {ev : QueryEvent Op Struct}
    (h : AllowanceBound d a b c t ev) :
    AllowanceBound d (a + extra) b c t (ev.addBits extra) := by
  have hex : (extra : ℤ) ≤ ((extra * d : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_right extra hd
  cases ev with
  | digit op j L =>
    obtain ⟨hj, hL⟩ := h
    refine ⟨hj, ?_⟩
    push_cast at hex hL ⊢
    linarith
  | struct sOp L =>
    change (L : ℤ) ≤ ((a * d : ℕ) : ℤ) + (b : ℤ) * (t : ℤ) at h
    change ((extra + L : ℕ) : ℤ) ≤ (((a + extra) * d : ℕ) : ℤ) + (b : ℤ) * (t : ℤ)
    push_cast at hex h ⊢
    linarith

/-- Clock-difference telescoping along a parent-to-child digit substitution
[OpenAI2026LogSpace, Theorem 10.9]. -/
theorem AllowanceBound.comp_child {Op₂ : Type u'} {Struct : Type v} {d a₁ a₂ b c₁ c₂ t u w : ℕ}
    (hd : 1 ≤ d) (retBits : ℕ)
    (hu : u ≤ t + c₁ * d)
    (hw : (w : ℤ) ≤ ((a₁ * d : ℕ) : ℤ) + (b : ℤ) * ((t : ℤ) - (u : ℤ)))
    {evChild : QueryEvent Op₂ Struct}
    (hChild : AllowanceBound d a₂ b c₂ u evChild) :
    AllowanceBound d (a₁ + a₂ + retBits) b (c₁ + c₂) t (evChild.addBits (w + retBits)) := by
  have hret : (retBits : ℤ) ≤ ((retBits * d : ℕ) : ℤ) := by
    exact_mod_cast Nat.le_mul_of_pos_right retBits hd
  cases evChild with
  | digit op₂ j L =>
    obtain ⟨hj, hL⟩ := hChild
    refine ⟨?_, ?_⟩
    · calc j ≤ u + c₂ * d := hj
        _ ≤ t + c₁ * d + c₂ * d := Nat.add_le_add_right hu _
        _ = t + (c₁ + c₂) * d := by rw [Nat.add_mul, Nat.add_assoc]
    · push_cast at hw hL hret ⊢
      linarith
  | struct sOp L =>
    change (L : ℤ) ≤ ((a₂ * d : ℕ) : ℤ) + (b : ℤ) * (u : ℤ) at hChild
    change ((w + retBits + L : ℕ) : ℤ) ≤
      (((a₁ + a₂ + retBits) * d : ℕ) : ℤ) + (b : ℤ) * (t : ℤ)
    push_cast at hw hChild hret ⊢
    linarith

end AllowanceAccounting

section UniformRecipes

/-- Certified exact signed-digit stream recipe at slack `slack ≥ 1`
[OpenAI2026LogSpace, Theorem 10.9], packaging exact stream semantics with `AllowanceBound` and
`maxIntrinsicBits` certificates over the recipe's annotated `QueryProg` family (prior to native
machine compilation of host continuations). -/
structure UniformStreamRecipe (Op : Type u) (Struct : Type v) where
  /-- Asymptotic slack parameter `d ≥ 1`. -/
  slack : ℕ
  slack_pos : 1 ≤ slack
  /-- Precondition on operand streams and clock-zero structural leaves. -/
  ValidEnv : (Op → ℕ → ℤ) → (Struct → Bool) → Prop
  /-- Exact real value in `[-1, 1]` computed by the recipe. -/
  targetVal : (Op → ℝ) → (Struct → Bool) → ℝ
  /-- Deterministic conditional query program emitting place `t`. -/
  digitProg : ℕ → QueryProg Op Struct ℤ
  /-- Slack multiplier `a` in `AllowanceBound`. -/
  coeffA : ℕ
  /-- Clock-slope coefficient `b` in `AllowanceBound`. -/
  coeffB : ℕ
  /-- Requested-place payment coefficient `c` in `AllowanceBound`. -/
  coeffC : ℕ
  /-- Intrinsic storage multiplier `C` bounding `maxIntrinsicBits ≤ C * slack`. -/
  intrinsicCoeff : ℕ
  abs_targetVal_le_one :
    ∀ {env sEnv}, ValidEnv env sEnv → |targetVal (fun op => streamVal (env op)) sEnv| ≤ 1
  emits_signed :
    ∀ {env sEnv}, ValidEnv env sEnv → IsSignedStream (fun t => (digitProg t).eval env sEnv)
  emits_exact :
    ∀ {env sEnv}, ValidEnv env sEnv →
      streamVal (fun t => (digitProg t).eval env sEnv) =
        targetVal (fun op => streamVal (env op)) sEnv
  allowance :
    ∀ (t : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct},
      ev ∈ (digitProg t).activeQueries env sEnv →
      AllowanceBound slack coeffA coeffB coeffC t ev
  intrinsic_bound :
    ∀ (t : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool),
      (digitProg t).maxIntrinsicBits env sEnv ≤ intrinsicCoeff * (slack + t)

namespace UniformStreamRecipe

/-- Strengthen the environment precondition of a `UniformStreamRecipe`. -/
@[expose] noncomputable def weakenValid {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) (V' : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (hV : ∀ {env sEnv}, V' env sEnv → R.ValidEnv env sEnv) :
    UniformStreamRecipe Op Struct where
  slack := R.slack
  slack_pos := R.slack_pos
  ValidEnv := V'
  targetVal := R.targetVal
  digitProg := R.digitProg
  coeffA := R.coeffA
  coeffB := R.coeffB
  coeffC := R.coeffC
  intrinsicCoeff := R.intrinsicCoeff
  abs_targetVal_le_one h := R.abs_targetVal_le_one (hV h)
  emits_signed h := R.emits_signed (hV h)
  emits_exact h := R.emits_exact (hV h)
  allowance := R.allowance
  intrinsic_bound := R.intrinsic_bound

/-- Rewrite the mathematical `targetVal` of a `UniformStreamRecipe` on valid environments. -/
@[expose] noncomputable def congrTarget {Op : Type u} {Struct : Type v}
    (R : UniformStreamRecipe Op Struct) (T' : (Op → ℝ) → (Struct → Bool) → ℝ)
    (hT : ∀ {env sEnv}, R.ValidEnv env sEnv →
      R.targetVal (fun op => streamVal (env op)) sEnv =
        T' (fun op => streamVal (env op)) sEnv) :
    UniformStreamRecipe Op Struct where
  slack := R.slack
  slack_pos := R.slack_pos
  ValidEnv := R.ValidEnv
  targetVal := T'
  digitProg := R.digitProg
  coeffA := R.coeffA
  coeffB := R.coeffB
  coeffC := R.coeffC
  intrinsicCoeff := R.intrinsicCoeff
  abs_targetVal_le_one h := by rw [← hT h]; exact R.abs_targetVal_le_one h
  emits_signed := R.emits_signed
  emits_exact h := by rw [R.emits_exact h, hT h]
  allowance := R.allowance
  intrinsic_bound := R.intrinsic_bound

/-- **Theorem 10.9 (stage composition of uniform stream recipes)**
[OpenAI2026LogSpace, Theorem 10.9]: substituting a family of certified child recipes `child` for
the operand streams of `parent` produces an exact stream recipe with zero numerical drift across
stages and telescoped annotated allowance/intrinsic constants. -/
@[expose] noncomputable def comp {Op₁ : Type u} {Op₂ : Type u'} {Struct : Type v}
    (parent : UniformStreamRecipe Op₁ Struct)
    (child : Op₁ → UniformStreamRecipe Op₂ Struct)
    (cA cB cC cInt : ℕ)
    (hSlack : ∀ op, (child op).slack = parent.slack)
    (hA : ∀ op, (child op).coeffA ≤ cA)
    (hB : ∀ op, (child op).coeffB ≤ cB)
    (hC : ∀ op, (child op).coeffC ≤ cC)
    (hInt : ∀ op, (child op).intrinsicCoeff ≤ cInt) :
    UniformStreamRecipe Op₂ Struct :=
  let B := max parent.coeffB (max cB cInt)
  let a₁ := parent.coeffA + (B - parent.coeffB) * parent.coeffC
  let a₂ := cA + B * cC
  { slack := parent.slack
    slack_pos := parent.slack_pos
    ValidEnv := fun env₂ sEnv =>
      (∀ op, (child op).ValidEnv env₂ sEnv) ∧
        parent.ValidEnv (fun op u => ((child op).digitProg u).eval env₂ sEnv) sEnv
    targetVal := fun val₂ sEnv =>
      parent.targetVal (fun op => (child op).targetVal val₂ sEnv) sEnv
    digitProg := fun t =>
      (parent.digitProg t).substDigits 4 (fun op u => (child op).digitProg u)
    coeffA := a₁ + a₂ + 4
    coeffB := B
    coeffC := parent.coeffC + cC
    intrinsicCoeff := max parent.intrinsicCoeff (max (a₁ + 4 + cInt) B)
    abs_targetVal_le_one := by
      rintro env₂ sEnv ⟨hCh, hPar⟩
      have heq : (fun op => (child op).targetVal (fun op₂ => streamVal (env₂ op₂)) sEnv) =
          fun op => streamVal (fun u => ((child op).digitProg u).eval env₂ sEnv) := by
        ext op
        exact ((child op).emits_exact (hCh op)).symm
      rw [heq]
      exact parent.abs_targetVal_le_one hPar
    emits_signed := by
      rintro env₂ sEnv ⟨_, hPar⟩
      have heval : (fun t =>
          ((parent.digitProg t).substDigits 4 (fun op u => (child op).digitProg u)).eval
            env₂ sEnv) =
          fun t => (parent.digitProg t).eval
            (fun op u => ((child op).digitProg u).eval env₂ sEnv) sEnv := by
        ext t
        exact QueryProg.eval_substDigits 4 _ _ _ _
      rw [heval]
      exact parent.emits_signed hPar
    emits_exact := by
      rintro env₂ sEnv ⟨hCh, hPar⟩
      have heval : (fun t =>
          ((parent.digitProg t).substDigits 4 (fun op u => (child op).digitProg u)).eval
            env₂ sEnv) =
          fun t => (parent.digitProg t).eval
            (fun op u => ((child op).digitProg u).eval env₂ sEnv) sEnv := by
        ext t
        exact QueryProg.eval_substDigits 4 _ _ _ _
      rw [heval, parent.emits_exact hPar]
      congr 1
      ext op
      exact (child op).emits_exact (hCh op)
    allowance := by
      intro t env₂ sEnv ev hev
      have hB_par : parent.coeffB ≤ B := le_max_left _ _
      have hB_ch : cB ≤ B := (le_max_left _ _).trans (le_max_right _ _)
      rcases QueryProg.mem_activeQueries_substDigits 4 _ _ _ _ hev with
        ⟨sOp, w, hs, rfl⟩ | ⟨op, u, w, evC, hd, hevC, rfl⟩
      · have h1 := (parent.allowance t _ sEnv hs).mono_coeff hB_par
        change (w : ℤ) ≤ ((a₁ * parent.slack : ℕ) : ℤ) + (B : ℤ) * (t : ℤ) at h1
        change (w : ℤ) ≤ (((a₁ + a₂ + 4) * parent.slack : ℕ) : ℤ) + (B : ℤ) * (t : ℤ)
        have had : a₁ * parent.slack ≤ (a₁ + a₂ + 4) * parent.slack :=
          Nat.mul_le_mul_right _ (by omega)
        have hadZ : ((a₁ * parent.slack : ℕ) : ℤ) ≤ (((a₁ + a₂ + 4) * parent.slack : ℕ) : ℤ) := by
          exact_mod_cast had
        linarith
      · have hParB := (parent.allowance t _ sEnv hd).mono_coeff hB_par
        obtain ⟨hu, hw⟩ := hParB
        have hChRaw := (child op).allowance u env₂ sEnv hevC
        rw [hSlack op] at hChRaw
        have hChMono := (hChRaw.mono_ac (a := cA) (c := cC) (hA op) (hC op)).mono_coeff
          (b := B) ((hB op).trans hB_ch)
        have hChA₂ := hChMono.mono_ac (a := a₂) (c := cC)
          (Nat.add_le_add_left (Nat.mul_le_mul_right cC (Nat.sub_le B _)) cA) le_rfl
        exact AllowanceBound.comp_child parent.slack_pos 4 hu hw hChA₂
    intrinsic_bound := by
      intro t env₂ sEnv
      set K := max parent.intrinsicCoeff (max (a₁ + 4 + cInt) B)
      apply QueryProg.maxIntrinsicBits_substDigits_le 4 _ _ _ _
      · exact (parent.intrinsic_bound t _ sEnv).trans
          (Nat.mul_le_mul_right _ (le_max_left _ _))
      · intro op u w hd
        have hB_par : parent.coeffB ≤ B := le_max_left _ _
        have hB_int : cInt ≤ B := (le_max_right _ _).trans (le_max_right _ _)
        have hParB := (parent.allowance t _ sEnv hd).mono_coeff hB_par
        obtain ⟨_, hw⟩ := hParB
        have hChInt := (child op).intrinsic_bound u env₂ sEnv
        rw [hSlack op] at hChInt
        have hChLe : ((child op).digitProg u).maxIntrinsicBits env₂ sEnv ≤
            cInt * (parent.slack + u) :=
          hChInt.trans (Nat.mul_le_mul_right _ (hInt op))
        have hret : (4 : ℤ) ≤ ((4 * parent.slack : ℕ) : ℤ) := by
          exact_mod_cast Nat.le_mul_of_pos_right 4 parent.slack_pos
        have hChZ : ((((child op).digitProg u).maxIntrinsicBits env₂ sEnv : ℕ) : ℤ) ≤
            (cInt : ℤ) * ((parent.slack : ℤ) + (u : ℤ)) := by
          exact_mod_cast hChLe
        have hB_ge_cInt : (cInt : ℤ) ≤ (B : ℤ) := by exact_mod_cast hB_int
        have hu_nonneg : (0 : ℤ) ≤ ((B : ℤ) - (cInt : ℤ)) * (u : ℤ) :=
          mul_nonneg (by linarith) (Nat.cast_nonneg u)
        have hsumNat : w + 4 + ((child op).digitProg u).maxIntrinsicBits env₂ sEnv ≤
            (a₁ + 4 + cInt) * parent.slack + B * t := by
          have hsumZ : ((w + 4 + ((child op).digitProg u).maxIntrinsicBits env₂ sEnv : ℕ) : ℤ) ≤
              (((a₁ + 4 + cInt) * parent.slack + B * t : ℕ) : ℤ) := by
            dsimp only [a₁]
            push_cast at hw hret ⊢
            linarith
          exact_mod_cast hsumZ
        have hK_left : a₁ + 4 + cInt ≤ K := (le_max_left _ _).trans (le_max_right _ _)
        have hK_right : B ≤ K := (le_max_right _ _).trans (le_max_right _ _)
        calc w + 4 + ((child op).digitProg u).maxIntrinsicBits env₂ sEnv
            ≤ (a₁ + 4 + cInt) * parent.slack + B * t := hsumNat
          _ ≤ K * parent.slack + K * t := by gcongr
          _ = K * (parent.slack + t) := (Nat.mul_add K parent.slack t).symm }

/-- Clock-zero structural leaf conditional branch between two `UniformStreamRecipe`s
[OpenAI2026LogSpace, Section 10.5, Lemma 10.6]. Only the branch selected by `sEnv sOp` is
evaluated or required to satisfy `ValidEnv`. -/
@[expose] noncomputable def condStruct {Op : Type u} {Struct : Type v}
    (sOp : Struct) (onTrue onFalse : UniformStreamRecipe Op Struct)
    (hSlack : onFalse.slack = onTrue.slack) :
    UniformStreamRecipe Op Struct where
  slack := onTrue.slack
  slack_pos := onTrue.slack_pos
  ValidEnv := fun env sEnv =>
    (sEnv sOp = true → onTrue.ValidEnv env sEnv) ∧
      (sEnv sOp = false → onFalse.ValidEnv env sEnv)
  targetVal := fun val sEnv =>
    if sEnv sOp then onTrue.targetVal val sEnv else onFalse.targetVal val sEnv
  digitProg := fun t =>
    .queryStruct sOp 0 fun b => if b then onTrue.digitProg t else onFalse.digitProg t
  coeffA := max onTrue.coeffA onFalse.coeffA +
    (max onTrue.coeffB onFalse.coeffB) * max onTrue.coeffC onFalse.coeffC
  coeffB := max onTrue.coeffB onFalse.coeffB
  coeffC := max onTrue.coeffC onFalse.coeffC
  intrinsicCoeff := max onTrue.intrinsicCoeff onFalse.intrinsicCoeff
  abs_targetVal_le_one := by
    rintro env sEnv ⟨hT, hF⟩
    cases hs : sEnv sOp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact onFalse.abs_targetVal_le_one (hF hs)
    · simp only [↓reduceIte]
      exact onTrue.abs_targetVal_le_one (hT hs)
  emits_signed := by
    rintro env sEnv ⟨hT, hF⟩
    cases hs : sEnv sOp
    · simpa only [QueryProg.eval, hs, Bool.false_eq_true, ↓reduceIte] using
        onFalse.emits_signed (hF hs)
    · simpa only [QueryProg.eval, hs, ↓reduceIte] using
        onTrue.emits_signed (hT hs)
  emits_exact := by
    rintro env sEnv ⟨hT, hF⟩
    cases hs : sEnv sOp
    · simpa only [QueryProg.eval, hs, Bool.false_eq_true, ↓reduceIte] using
        onFalse.emits_exact (hF hs)
    · simpa only [QueryProg.eval, hs, ↓reduceIte] using
        onTrue.emits_exact (hT hs)
  allowance := by
    intro t env sEnv ev hev
    simp only [QueryProg.activeQueries, List.mem_cons] at hev
    set A := max onTrue.coeffA onFalse.coeffA
    set B := max onTrue.coeffB onFalse.coeffB
    set C := max onTrue.coeffC onFalse.coeffC
    rcases hev with rfl | hevRest
    · simp only [AllowanceBound, Int.ofNat_zero]
      positivity
    · cases hs : sEnv sOp
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hevRest
        have hF := onFalse.allowance t env sEnv hevRest
        rw [hSlack] at hF
        have h1 := (hF.mono_ac (a := A) (c := C) (le_max_right _ _) (le_max_right _ _)).mono_coeff
          (b := B) (le_max_right _ _)
        exact h1.mono_ac (a := A + B * C) (c := C) (Nat.add_le_add_left
          (Nat.mul_le_mul_right C (Nat.sub_le B _)) A) le_rfl
      · simp only [hs, ↓reduceIte] at hevRest
        have hT := onTrue.allowance t env sEnv hevRest
        have h1 := (hT.mono_ac (a := A) (c := C) (le_max_left _ _) (le_max_left _ _)).mono_coeff
          (b := B) (le_max_left _ _)
        exact h1.mono_ac (a := A + B * C) (c := C) (Nat.add_le_add_left
          (Nat.mul_le_mul_right C (Nat.sub_le B _)) A) le_rfl
  intrinsic_bound := by
    intro t env sEnv
    simp only [QueryProg.maxIntrinsicBits, Nat.zero_max]
    cases hs : sEnv sOp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hF := onFalse.intrinsic_bound t env sEnv
      rw [hSlack] at hF
      exact hF.trans (Nat.mul_le_mul_right _ (le_max_right _ _))
    · simp only [↓reduceIte]
      exact (onTrue.intrinsic_bound t env sEnv).trans
        (Nat.mul_le_mul_right _ (le_max_left _ _))

end UniformStreamRecipe

/-- Certified clock-zero finite Boolean test recipe [OpenAI2026LogSpace, Lemma 10.8, Theorem 10.9],
whose precision, result, and annotated query/intrinsic bounds are independent of any enclosing
numerical clock (prior to native machine compilation). -/
structure UniformBoolRecipe (Op : Type u) (Struct : Type v) where
  /-- Asymptotic slack parameter `d ≥ 1`. -/
  slack : ℕ
  slack_pos : 1 ≤ slack
  /-- Deterministic conditional query program computing the clock-zero Boolean test. -/
  prog : QueryProg Op Struct Bool
  /-- Slack multiplier `a` in `AllowanceBound` at clock zero. -/
  coeffA : ℕ
  /-- Clock-slope coefficient `b` in `AllowanceBound` (unused at clock zero). -/
  coeffB : ℕ
  /-- Requested-place payment coefficient `c` in `AllowanceBound`. -/
  coeffC : ℕ
  /-- Intrinsic storage multiplier `C` bounding `maxIntrinsicBits ≤ C * slack`. -/
  intrinsicCoeff : ℕ
  allowance :
    ∀ (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct},
      ev ∈ prog.activeQueries env sEnv →
      AllowanceBound slack coeffA coeffB coeffC 0 ev
  intrinsic_bound :
    ∀ (env : Op → ℕ → ℤ) (sEnv : Struct → Bool),
      prog.maxIntrinsicBits env sEnv ≤ intrinsicCoeff * slack

end UniformRecipes

section StreamingBuildingBlocks

/-- Lift a mod-16 approximation residue program `resProg` (`(resProg s).eval = N s % 16`) to an
exact difference-digit program via `decodeDiffResidue 4` [OpenAI2026LogSpace, Lemma 10.1]. -/
@[expose] def diffDigitProg {Op : Type u} {Struct : Type v}
    (resProg : ℕ → QueryProg Op Struct ℤ) : ℕ → QueryProg Op Struct ℤ
  | 0 => (resProg 0).map (fun rCurr => decodeDiffResidue 4 rCurr 0 0)
  | t + 1 =>
      (resProg (t + 1)).bindOverhead 4 fun rCurr =>
        (resProg t).bindOverhead 8 fun rPrev =>
          .scratchStep 8 (.ret (decodeDiffResidue 4 rCurr rPrev (t + 1)))

theorem eval_diffDigitProg {Op : Type u} {Struct : Type v}
    (resProg : ℕ → QueryProg Op Struct ℤ) (N : ℕ → ℤ) {z : ℝ}
    (hz : |z| ≤ 1) (hN : IsScaledApprox z N)
    {env : Op → ℕ → ℤ} {sEnv : Struct → Bool}
    (hRes : ∀ s, (resProg s).eval env sEnv = N s % 16) (t : ℕ) :
    (diffDigitProg resProg t).eval env sEnv = diffDigit N t := by
  have h16 : (16 : ℤ) = (2 : ℤ) ^ (4 : ℕ) := by decide
  cases t with
  | zero =>
    simp only [diffDigitProg, QueryProg.eval_map, hRes 0, h16]
    have hdec := decodeDiffResidue_eq_diffDigit (by decide : 4 ≤ 4) hz hN 0
    simpa only [decodeDiffResidue] using hdec
  | succ t =>
    simp only [diffDigitProg, QueryProg.eval_bindOverhead, QueryProg.eval, hRes (t + 1), hRes t,
      h16]
    have hdec := decodeDiffResidue_eq_diffDigit (by decide : 4 ≤ 4) hz hN (t + 1)
    simpa only [Nat.add_sub_cancel] using hdec

theorem allowance_diffDigitProg {Op : Type u} {Struct : Type v} {d a b c : ℕ} (hd : 1 ≤ d)
    (resProg : ℕ → QueryProg Op Struct ℤ)
    (hAllow : ∀ (s : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct},
      ev ∈ (resProg s).activeQueries env sEnv → AllowanceBound d a b c s ev)
    (t : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (diffDigitProg resProg t).activeQueries env sEnv) :
    AllowanceBound d (a + 8) b c t ev := by
  cases t with
  | zero =>
    simp only [diffDigitProg, QueryProg.activeQueries_map] at hev
    exact (hAllow 0 env sEnv hev).mono_ac (Nat.le_add_right a 8) le_rfl
  | succ t =>
    simp only [diffDigitProg, QueryProg.activeQueries_bindOverhead, QueryProg.activeQueries,
      List.append_nil, List.mem_append, List.mem_map] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | ⟨ev₀, hev₀, rfl⟩
    · exact ((hAllow (t + 1) env sEnv hev₀).addBits_const hd 4).mono_ac (by omega) le_rfl
    · have h0 := (hAllow t env sEnv hev₀).mono_clock (Nat.le_succ t)
      exact h0.addBits_const hd 8

theorem maxIntrinsicBits_diffDigitProg_le {Op : Type u} {Struct : Type v} {d C : ℕ} (hd : 1 ≤ d)
    (resProg : ℕ → QueryProg Op Struct ℤ)
    (hInt : ∀ (s : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool),
      (resProg s).maxIntrinsicBits env sEnv ≤ C * (d + s))
    (t : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (diffDigitProg resProg t).maxIntrinsicBits env sEnv ≤ (C + 8) * (d + t) := by
  cases t with
  | zero =>
    simp only [diffDigitProg, QueryProg.maxIntrinsicBits_map]
    exact (hInt 0 env sEnv).trans (Nat.mul_le_mul_right _ (Nat.le_add_right C 8))
  | succ t =>
    simp only [diffDigitProg]
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · have h1 := hInt (t + 1) env sEnv
      calc 4 + (resProg (t + 1)).maxIntrinsicBits env sEnv
          ≤ 4 + C * (d + (t + 1)) := Nat.add_le_add_left h1 4
        _ ≤ 8 * (d + (t + 1)) + C * (d + (t + 1)) :=
            Nat.add_le_add_right (by omega) _
        _ = (C + 8) * (d + (t + 1)) := by ring
    · refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
      · have h0 := hInt t env sEnv
        calc 8 + (resProg t).maxIntrinsicBits env sEnv
            ≤ 8 + C * (d + t) := Nat.add_le_add_left h0 8
          _ ≤ 8 * (d + (t + 1)) + C * (d + (t + 1)) := by gcongr <;> omega
          _ = (C + 8) * (d + (t + 1)) := by ring
      · simp only [QueryProg.maxIntrinsicBits, Nat.max_zero]
        have hle : 8 ≤ 8 * (d + (t + 1)) := by omega
        exact hle.trans (by rw [Nat.add_mul]; omega)

/-- Package any mod-16 scaled-approximation residue program into a certified
`UniformStreamRecipe`. -/
@[expose] noncomputable def recipeOfMod16Prog {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d)
    (ValidEnv : (Op → ℕ → ℤ) → (Struct → Bool) → Prop)
    (targetVal : (Op → ℝ) → (Struct → Bool) → ℝ)
    (N : (Op → ℕ → ℤ) → (Struct → Bool) → ℕ → ℤ)
    (resProg : ℕ → QueryProg Op Struct ℤ)
    (a b c C : ℕ)
    (hBound : ∀ {env sEnv}, ValidEnv env sEnv →
      |targetVal (fun op => streamVal (env op)) sEnv| ≤ 1)
    (hApprox : ∀ {env sEnv}, ValidEnv env sEnv →
      IsScaledApprox (targetVal (fun op => streamVal (env op)) sEnv) (N env sEnv))
    (hEval : ∀ {env sEnv}, ValidEnv env sEnv → ∀ s,
      (resProg s).eval env sEnv = N env sEnv s % 16)
    (hAllow : ∀ (s : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct},
      ev ∈ (resProg s).activeQueries env sEnv → AllowanceBound d a b c s ev)
    (hInt : ∀ (s : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool),
      (resProg s).maxIntrinsicBits env sEnv ≤ C * (d + s)) :
    UniformStreamRecipe Op Struct where
  slack := d
  slack_pos := hd
  ValidEnv := ValidEnv
  targetVal := targetVal
  digitProg := diffDigitProg resProg
  coeffA := a + 8
  coeffB := b
  coeffC := c
  intrinsicCoeff := C + 8
  abs_targetVal_le_one := hBound
  emits_signed := by
    intro env sEnv hV
    have heq : (fun t => (diffDigitProg resProg t).eval env sEnv) = diffDigit (N env sEnv) := by
      ext t
      exact eval_diffDigitProg resProg (N env sEnv) (hBound hV) (hApprox hV) (hEval hV) t
    rw [heq]
    exact diffDigit_isSignedStream (hBound hV) (hApprox hV)
  emits_exact := by
    intro env sEnv hV
    have heq : (fun t => (diffDigitProg resProg t).eval env sEnv) = diffDigit (N env sEnv) := by
      ext t
      exact eval_diffDigitProg resProg (N env sEnv) (hBound hV) (hApprox hV) (hEval hV) t
    rw [heq]
    exact streamVal_diffDigit (hBound hV) (hApprox hV)
  allowance t env sEnv _ hev := allowance_diffDigitProg hd resProg hAllow t env sEnv hev
  intrinsic_bound t env sEnv := maxIntrinsicBits_diffDigitProg_le hd resProg hInt t env sEnv

/-- Tail-recursive modular Horner scan over `rem` consecutive digits starting at `idx`, charging
`2 * W` retained bits for the `W`-bit residue accumulator and bounded window offset (`rem ≤ W`). -/
@[expose] def scanModAux {Op : Type u} {Struct : Type v} (op : Op) (W idx : ℕ) :
    ℕ → ℤ → QueryProg Op Struct ℤ
  | 0, acc => .scratchStep (2 * W) (.ret (acc % (2 : ℤ) ^ W))
  | rem + 1, acc =>
      .queryDigit op idx (2 * W) fun d =>
        scanModAux op W (idx + 1) rem ((2 * acc + d) % (2 : ℤ) ^ W)

private def windowModFold (x : ℕ → ℤ) (M : ℤ) (idx : ℕ) : ℕ → ℤ → ℤ
  | 0, acc => acc % M
  | rem + 1, acc => windowModFold x M (idx + 1) rem ((2 * acc + x idx) % M)

private theorem windowModFold_snoc (x : ℕ → ℤ) (M : ℤ) (idx rem : ℕ) (acc : ℤ) :
    windowModFold x M idx (rem + 1) acc =
      (2 * windowModFold x M idx rem acc + x (idx + rem)) % M := by
  induction rem generalizing idx acc with
  | zero =>
    simp only [windowModFold, Nat.add_zero, Int.emod_emod]
    conv_rhs => rw [Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, ← Int.add_emod]
  | succ rem ih =>
    conv_lhs => rw [windowModFold]
    rw [ih]
    have hidx : idx + 1 + rem = idx + (rem + 1) := by omega
    rw [hidx]
    rfl

private theorem eval_scanModAux {Op : Type u} {Struct : Type v} (op : Op) (W idx rem : ℕ)
    (acc : ℤ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (scanModAux op W idx rem acc).eval env sEnv =
      windowModFold (env op) ((2 : ℤ) ^ W) idx rem acc := by
  induction rem generalizing idx acc with
  | zero => rfl
  | succ rem ih =>
    simp only [scanModAux, QueryProg.eval, windowModFold]
    exact ih _ _

private theorem windowModFold_eq_sum (x : ℕ → ℤ) (M : ℤ) (lo m : ℕ) :
    windowModFold x M lo m 0 =
      (∑ j ∈ Ico lo (lo + m), x j * (2 : ℤ) ^ (lo + m - 1 - j)) % M := by
  induction m with
  | zero => simp [windowModFold]
  | succ m ih =>
    rw [windowModFold_snoc, ih]
    have htop : Ico lo (lo + (m + 1)) = insert (lo + m) (Ico lo (lo + m)) := by
      ext j
      simp only [mem_Ico, mem_insert]
      omega
    have hnot : lo + m ∉ Ico lo (lo + m) := by simp
    rw [htop, sum_insert hnot]
    have hself : lo + (m + 1) - 1 - (lo + m) = 0 := by omega
    rw [hself, pow_zero, mul_one]
    have hmul_sum : ∑ j ∈ Ico lo (lo + m), x j * (2 : ℤ) ^ (lo + (m + 1) - 1 - j) =
        2 * ∑ j ∈ Ico lo (lo + m), x j * (2 : ℤ) ^ (lo + m - 1 - j) := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hjlt : j < lo + m := (mem_Ico.mp hj).2
      have hexp : lo + (m + 1) - 1 - j = (lo + m - 1 - j) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [hmul_sum, add_comm (x (lo + m))]
    conv_rhs => rw [Int.add_emod, Int.mul_emod]
    rw [Int.add_emod, Int.mul_emod (2 : ℤ), Int.emod_emod]

/-- Windowed low-residue reader computing `intPrefix (env op) K % 2 ^ W` by scanning at most `W`
digits in `Ico (K + 1 - W) (K + 1)` with `2 * W` retained bits and `K + 2 * W + 4` intrinsic
scratch bits for place calculation [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def windowPrefixModProg {Op : Type u} {Struct : Type v} (op : Op) (W K : ℕ) :
    QueryProg Op Struct ℤ :=
  let lo := K + 1 - W
  .scratchStep (K + 2 * W + 4) (scanModAux op W lo (K + 1 - lo) 0)

theorem eval_windowPrefixModProg {Op : Type u} {Struct : Type v} (op : Op) (W K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (windowPrefixModProg op W K).eval env sEnv = intPrefix (env op) K % (2 : ℤ) ^ W := by
  unfold windowPrefixModProg
  dsimp only [QueryProg.eval]
  set lo := K + 1 - W
  have hlo : lo ≤ K + 1 := Nat.sub_le _ _
  have hadd : lo + (K + 1 - lo) = K + 1 := Nat.add_sub_of_le hlo
  rw [eval_scanModAux, windowModFold_eq_sum, hadd, Nat.add_sub_cancel,
    intPrefix_emod_eq_windowPrefix_emod]
  rfl

theorem mem_activeQueries_windowPrefixModProg {Op : Type u} {Struct : Type v} (op : Op) (W K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (windowPrefixModProg op W K).activeQueries env sEnv) :
    ∃ j ≤ K, ev = .digit op j (2 * W) := by
  unfold windowPrefixModProg at hev
  dsimp only [QueryProg.activeQueries] at hev
  have haux : ∀ idx rem acc,
      ev ∈ (scanModAux op W idx rem acc).activeQueries env sEnv →
      ∃ j < idx + rem, ev = .digit op j (2 * W) := by
    intro idx rem
    induction rem generalizing idx with
    | zero =>
      intro acc h
      nomatch h
    | succ rem ih =>
      intro acc h
      simp only [scanModAux, QueryProg.activeQueries, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨idx, by omega, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := ih (idx + 1) _ h
        exact ⟨j, by omega, rfl⟩
  obtain ⟨j, hj, rfl⟩ := haux (K + 1 - W) (K + 1 - (K + 1 - W)) 0 hev
  exact ⟨j, by omega, rfl⟩

theorem maxIntrinsicBits_windowPrefixModProg_le {Op : Type u} {Struct : Type v} (op : Op)
    (W K : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (windowPrefixModProg op W K).maxIntrinsicBits env sEnv ≤ K + 2 * W + 4 := by
  have haux : ∀ idx rem acc, (scanModAux op W idx rem acc).maxIntrinsicBits env sEnv ≤ 2 * W := by
    intro idx rem
    induction rem generalizing idx with
    | zero =>
      intro acc
      simp [scanModAux, QueryProg.maxIntrinsicBits]
    | succ rem ih =>
      intro acc
      simp only [scanModAux, QueryProg.maxIntrinsicBits]
      exact max_le le_rfl (ih (idx + 1) _)
  simp only [windowPrefixModProg, QueryProg.maxIntrinsicBits]
  exact max_le le_rfl ((haux _ _ 0).trans (by omega))

/-- Top-down 27-state prefix comparison `QueryProg` computing `cmpPrefix (env op₁) (env op₂) K`
without storing a binary loop counter across queries: unfolding from output gate `K` down to `0`
retains `6` bits per ancestor step (`L ≤ 10 + 6 * (K - j)`) and uses `O(K + 1)` intrinsic scratch
to regenerate place indices [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def cmpPrefixProg {Op : Type u} {Struct : Type v} (op₁ op₂ : Op) :
    ℕ → QueryProg Op Struct ℤ
  | 0 =>
      .scratchStep 10
        (.queryDigit op₁ 0 5 fun d₁ =>
          .queryDigit op₂ 0 9 fun d₂ =>
            .ret (cmpStep 0 (d₁ - d₂)))
  | K + 1 =>
      .scratchStep (K + 11)
        ((cmpPrefixProg op₁ op₂ K).bindOverhead 6 fun state =>
          .queryDigit op₁ (K + 1) 6 fun d₁ =>
            .queryDigit op₂ (K + 1) 10 fun d₂ =>
              .ret (cmpStep state (d₁ - d₂)))

theorem eval_cmpPrefixProg {Op : Type u} {Struct : Type v} (op₁ op₂ : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (cmpPrefixProg op₁ op₂ K).eval env sEnv = cmpPrefix (env op₁) (env op₂) K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [cmpPrefixProg, QueryProg.eval, QueryProg.eval_bindOverhead, ih, cmpPrefix]

theorem mem_activeQueries_cmpPrefixProg {Op : Type u} {Struct : Type v} (op₁ op₂ : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (cmpPrefixProg op₁ op₂ K).activeQueries env sEnv) :
    ∃ op j L, j ≤ K ∧ L ≤ 10 + 6 * (K - j) ∧ ev = .digit op j L := by
  induction K generalizing ev with
  | zero =>
    simp only [cmpPrefixProg, QueryProg.activeQueries, List.mem_cons] at hev
    rcases hev with rfl | rfl | hev
    · exact ⟨op₁, 0, 5, le_rfl, by decide, rfl⟩
    · exact ⟨op₂, 0, 9, le_rfl, by decide, rfl⟩
    · nomatch hev
  | succ K ih =>
    simp only [cmpPrefixProg, QueryProg.activeQueries, QueryProg.activeQueries_bindOverhead,
      List.mem_append, List.mem_map, List.mem_cons] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | rfl | rfl | hev
    · obtain ⟨op, j, L, hj, hL, rfl⟩ := ih hev₀
      exact ⟨op, j, 6 + L, by omega, by omega, rfl⟩
    · exact ⟨op₁, K + 1, 6, le_rfl, by omega, rfl⟩
    · exact ⟨op₂, K + 1, 10, le_rfl, by omega, rfl⟩
    · nomatch hev

theorem maxIntrinsicBits_cmpPrefixProg_le {Op : Type u} {Struct : Type v} (op₁ op₂ : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (cmpPrefixProg op₁ op₂ K).maxIntrinsicBits env sEnv ≤ 6 * K + 10 := by
  induction K with
  | zero =>
    simp [cmpPrefixProg, QueryProg.maxIntrinsicBits]
  | succ K ih =>
    simp only [cmpPrefixProg, QueryProg.maxIntrinsicBits]
    refine max_le (by omega) ?_
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · omega
    · simp only [QueryProg.maxIntrinsicBits]
      omega

/-- Top-down 27-state prefix comparator `QueryProg` comparing `env op` against a fixed digit
sequence `bound` through place `K`, retaining `6` bits per ancestor step (`L ≤ 6 + 6 * (K - j)`)
and using `O(K + 1)` intrinsic scratch [OpenAI2026LogSpace, Lemma 10.3]. -/
@[expose] def cmpWithConstProg {Op : Type u} {Struct : Type v} (op : Op) (bound : ℕ → ℤ) :
    ℕ → QueryProg Op Struct ℤ
  | 0 =>
      .scratchStep 10
        (.queryDigit op 0 5 fun d =>
          .ret (cmpStep 0 (d - bound 0)))
  | K + 1 =>
      .scratchStep (K + 11)
        ((cmpWithConstProg op bound K).bindOverhead 6 fun state =>
          .queryDigit op (K + 1) 6 fun d =>
            .ret (cmpStep state (d - bound (K + 1))))

theorem eval_cmpWithConstProg {Op : Type u} {Struct : Type v} (op : Op) (bound : ℕ → ℤ) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (cmpWithConstProg op bound K).eval env sEnv = cmpPrefix (env op) bound K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [cmpWithConstProg, QueryProg.eval, QueryProg.eval_bindOverhead, ih, cmpPrefix]

theorem mem_activeQueries_cmpWithConstProg {Op : Type u} {Struct : Type v} (op : Op)
    (bound : ℕ → ℤ) (K : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) {ev : QueryEvent Op Struct}
    (hev : ev ∈ (cmpWithConstProg op bound K).activeQueries env sEnv) :
    ∃ j L, j ≤ K ∧ L ≤ 6 + 6 * (K - j) ∧ ev = .digit op j L := by
  induction K generalizing ev with
  | zero =>
    simp only [cmpWithConstProg, QueryProg.activeQueries, List.mem_cons] at hev
    rcases hev with rfl | hev
    · exact ⟨0, 5, le_rfl, by decide, rfl⟩
    · nomatch hev
  | succ K ih =>
    simp only [cmpWithConstProg, QueryProg.activeQueries, QueryProg.activeQueries_bindOverhead,
      List.mem_append, List.mem_map, List.mem_cons] at hev
    rcases hev with ⟨ev₀, hev₀, rfl⟩ | rfl | hev
    · obtain ⟨j, L, hj, hL, rfl⟩ := ih hev₀
      exact ⟨j, 6 + L, by omega, by omega, rfl⟩
    · exact ⟨K + 1, 6, le_rfl, by omega, rfl⟩
    · nomatch hev

theorem maxIntrinsicBits_cmpWithConstProg_le {Op : Type u} {Struct : Type v} (op : Op)
    (bound : ℕ → ℤ) (K : ℕ) (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (cmpWithConstProg op bound K).maxIntrinsicBits env sEnv ≤ 6 * K + 10 := by
  induction K with
  | zero =>
    simp [cmpWithConstProg, QueryProg.maxIntrinsicBits]
  | succ K ih =>
    simp only [cmpWithConstProg, QueryProg.maxIntrinsicBits]
    refine max_le (by omega) ?_
    refine (QueryProg.maxIntrinsicBits_bindOverhead_le _ _ _ _ _).trans (max_le ?_ ?_)
    · omega
    · simp only [QueryProg.maxIntrinsicBits]
      omega

private def cmpIter (stepFn : ℤ → ℤ → ℤ) (δFn : ℕ → ℤ) (idx : ℕ) : ℕ → ℤ → ℤ
  | 0, state => state
  | rem + 1, state => cmpIter stepFn δFn (idx + 1) rem (stepFn state (δFn idx))

private theorem cmpIter_snoc (stepFn : ℤ → ℤ → ℤ) (δFn : ℕ → ℤ) (idx rem : ℕ) (state : ℤ) :
    cmpIter stepFn δFn idx (rem + 1) state =
      stepFn (cmpIter stepFn δFn idx rem state) (δFn (idx + rem)) := by
  induction rem generalizing idx state with
  | zero => simp [cmpIter]
  | succ rem ih =>
    conv_lhs => rw [cmpIter]
    rw [ih]
    have hidx : idx + 1 + rem = idx + (rem + 1) := by omega
    rw [hidx]
    rfl

/-- Tail-recursive 63-state comparator for `bufferedTest` (`2 s - 3 u` clamped to `[-31, 31]`),
charging `cntBits` bits for the bounded place counter alongside the 6-bit state and 4-bit saved
digit. -/
@[expose] def cmpBufferedAux {Op : Type u} {Struct : Type v} (opS opU : Op) (cntBits idx : ℕ) :
    ℕ → ℤ → QueryProg Op Struct ℤ
  | 0, state => .scratchStep (cntBits + 7) (.ret state)
  | rem + 1, state =>
      .queryDigit opS idx (cntBits + 6) fun dS =>
        .queryDigit opU idx (cntBits + 10) fun dU =>
          cmpBufferedAux opS opU cntBits (idx + 1) rem (cmpBufferedStep state (2 * dS - 3 * dU))

/-- Streaming 63-state buffered comparator `QueryProg` computing `cmpBuffered (env opS) (env opU) K`
across places `0, ..., K`. -/
@[expose] def cmpBufferedProg {Op : Type u} {Struct : Type v} (opS opU : Op) (K : ℕ) :
    QueryProg Op Struct ℤ :=
  cmpBufferedAux opS opU (K + 1) 0 (K + 1) 0

/-- Clock-zero `QueryProg` evaluating `bufferedTest M R (env opS) (env opU)` at cutoff
`K = M + R + 7` [OpenAI2026LogSpace, Lemma 10.8]. -/
@[expose] def bufferedTestProg {Op : Type u} {Struct : Type v} (opS opU : Op) (M R : ℕ) :
    QueryProg Op Struct Bool :=
  (cmpBufferedProg opS opU (M + R + 7)).map (fun c => decide (0 < c))

theorem eval_cmpBufferedProg {Op : Type u} {Struct : Type v} (opS opU : Op) (K : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (cmpBufferedProg opS opU K).eval env sEnv = cmpBuffered (env opS) (env opU) K := by
  have haux : ∀ cntBits idx rem state,
      (cmpBufferedAux opS opU cntBits idx rem state).eval env sEnv =
        cmpIter cmpBufferedStep (fun j => 2 * env opS j - 3 * env opU j) idx rem state := by
    intro cntBits idx rem
    induction rem generalizing idx with
    | zero => intro state; rfl
    | succ rem ih =>
      intro state
      simp only [cmpBufferedAux, QueryProg.eval, cmpIter]
      exact ih _ _
  rw [cmpBufferedProg, haux]
  induction K with
  | zero => simp [cmpIter, cmpBuffered]
  | succ K ih =>
    rw [cmpIter_snoc, Nat.zero_add, ih, cmpBuffered]

theorem eval_bufferedTestProg {Op : Type u} {Struct : Type v} (opS opU : Op) (M R : ℕ)
    (env : Op → ℕ → ℤ) (sEnv : Struct → Bool) :
    (bufferedTestProg opS opU M R).eval env sEnv = bufferedTest M R (env opS) (env opU) := by
  unfold bufferedTestProg bufferedTest
  rw [QueryProg.eval_map]
  exact congrArg (fun c => decide (0 < c)) (eval_cmpBufferedProg opS opU (M + R + 7) env sEnv)

/-- **Lemma 10.8 (certified buffered margin test recipe)** [OpenAI2026LogSpace, Lemma 10.8]:
at starting clock `0` and `M + R ≤ κ * d`, `bufferedTestProg` queries at most `M + R + 7 ≤
(κ + 7) * d` normalized places while retaining at most `(κ + 18) * d` bits (`coeffB = 0`). -/
@[expose] def bufferedTestRecipe {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (opS opU : Op) (M R κ : ℕ) (hMR : M + R ≤ κ * d) :
    UniformBoolRecipe Op Struct where
  slack := d
  slack_pos := hd
  prog := bufferedTestProg opS opU M R
  coeffA := κ + 18
  coeffB := 0
  coeffC := κ + 7
  intrinsicCoeff := κ + 18
  allowance := by
    intro env sEnv ev hev
    rw [bufferedTestProg, QueryProg.activeQueries_map, cmpBufferedProg] at hev
    have haux : ∀ cntBits idx rem state,
        ev ∈ (cmpBufferedAux opS opU cntBits idx rem state).activeQueries env sEnv →
        ∃ op j L, j < idx + rem ∧ L ≤ cntBits + 10 ∧ ev = .digit op j L := by
      intro cntBits idx rem
      induction rem generalizing idx with
      | zero => intro state h; nomatch h
      | succ rem ih =>
        intro state h
        simp only [cmpBufferedAux, QueryProg.activeQueries, List.mem_cons] at h
        rcases h with rfl | rfl | h
        · exact ⟨opS, idx, cntBits + 6, by omega, by omega, rfl⟩
        · exact ⟨opU, idx, cntBits + 10, by omega, le_rfl, rfl⟩
        · obtain ⟨op, j, L, hj, hL, rfl⟩ := ih (idx + 1) _ h
          exact ⟨op, j, L, by omega, hL, rfl⟩
    obtain ⟨op, j, L, hj, hL, rfl⟩ := haux (M + R + 8) 0 ((M + R + 7) + 1) 0 hev
    refine ⟨?_, ?_⟩
    · have h7 : 7 ≤ 7 * d := Nat.le_mul_of_pos_right 7 hd
      calc j ≤ M + R + 7 := by omega
        _ ≤ κ * d + 7 * d := by omega
        _ = 0 + (κ + 7) * d := by rw [Nat.add_mul, Nat.zero_add]
    · have h18 : 18 ≤ 18 * d := Nat.le_mul_of_pos_right 18 hd
      have hLn : L ≤ (κ + 18) * d := by
        calc L ≤ M + R + 18 := by omega
          _ ≤ κ * d + 18 * d := by omega
          _ = (κ + 18) * d := (Nat.add_mul κ 18 d).symm
      have hLZ : (L : ℤ) ≤ (((κ + 18) * d : ℕ) : ℤ) := by exact_mod_cast hLn
      simpa only [Nat.cast_zero, zero_mul, add_zero] using hLZ
  intrinsic_bound := by
    intro env sEnv
    rw [bufferedTestProg, QueryProg.maxIntrinsicBits_map, cmpBufferedProg]
    have haux : ∀ cntBits idx rem state,
        (cmpBufferedAux opS opU cntBits idx rem state).maxIntrinsicBits env sEnv ≤
          cntBits + 10 := by
      intro cntBits idx rem
      induction rem generalizing idx with
      | zero =>
        intro state
        simp only [cmpBufferedAux, QueryProg.maxIntrinsicBits, Nat.max_zero]
        omega
      | succ rem ih =>
        intro state
        simp only [cmpBufferedAux, QueryProg.maxIntrinsicBits]
        exact max_le (by omega) (max_le le_rfl (ih (idx + 1) _))
    have h18 : 18 ≤ 18 * d := Nat.le_mul_of_pos_right 18 hd
    calc (cmpBufferedAux opS opU (M + R + 7 + 1) 0 (M + R + 7 + 1) 0).maxIntrinsicBits env sEnv
        ≤ (M + R + 7 + 1) + 10 := haux _ 0 _ 0
      _ ≤ κ * d + 18 * d := by omega
      _ = (κ + 18) * d := (Nat.add_mul κ 18 d).symm

theorem bufferedTestRecipe_true_of_two_mul_lt {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (opS opU : Op) {M R κ : ℕ} (hMR : M + R ≤ κ * d)
    {env : Op → ℕ → ℤ} (sEnv : Struct → Bool)
    (hs : IsSignedStream (env opS)) (hu : IsSignedStream (env opU))
    {sVal uVal ρ : ℝ} (hsVal : sVal = (2 : ℝ) ^ M * streamVal (env opS))
    (huVal : uVal = (2 : ℝ) ^ M * streamVal (env opU))
    (hρ : 1 / (2 : ℝ) ^ R ≤ ρ) (huρ : ρ ≤ uVal) (hlt : 2 * uVal < sVal) :
    (bufferedTestRecipe d hd opS opU M R κ hMR).prog.eval env sEnv = true := by
  change (bufferedTestProg opS opU M R).eval env sEnv = true
  rw [eval_bufferedTestProg]
  exact bufferedTest_eq_true_of_two_mul_lt hs hu hsVal huVal hρ huρ hlt

theorem bufferedTestRecipe_false_of_le {Op : Type u} {Struct : Type v}
    (d : ℕ) (hd : 1 ≤ d) (opS opU : Op) {M R κ : ℕ} (hMR : M + R ≤ κ * d)
    {env : Op → ℕ → ℤ} (sEnv : Struct → Bool)
    (hs : IsSignedStream (env opS)) (hu : IsSignedStream (env opU))
    {sVal uVal ρ : ℝ} (hsVal : sVal = (2 : ℝ) ^ M * streamVal (env opS))
    (huVal : uVal = (2 : ℝ) ^ M * streamVal (env opU))
    (hρ : 1 / (2 : ℝ) ^ R ≤ ρ) (huρ : ρ ≤ uVal) (hle : sVal ≤ uVal) :
    (bufferedTestRecipe d hd opS opU M R κ hMR).prog.eval env sEnv = false := by
  change (bufferedTestProg opS opU M R).eval env sEnv = false
  rw [eval_bufferedTestProg]
  exact bufferedTest_eq_false_of_le hs hu hsVal huVal hρ huρ hle

end StreamingBuildingBlocks

end Cslib.StreamArithmetic
