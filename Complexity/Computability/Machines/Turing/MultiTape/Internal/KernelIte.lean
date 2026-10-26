/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Branch

/-! # The existing conditional machine and its run theorem

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {k₀ k₁ k₂ : ℕ} {Symbol S₀ S₁ S₂ : Type*}

/-- Run `tmc` with its output on a new last work tape, then `tm₁` if that word is non-empty and
`tm₂` otherwise, and clear the tape. All three machines are padded to `max k₀ (max k₁ k₂)` work
tapes. -/
public noncomputable def iteTM (tmc : MultiTapeTM k₀ Symbol S₀) (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (tm₂ : MultiTapeTM k₂ Symbol S₂) : MultiTapeTM (max k₀ (max k₁ k₂) + 1) Symbol
      ((S₀ ⊕ RewindWorkState) ⊕ Option (S₁ ⊕ S₂) ⊕ Unit ⊕ RewindWorkState) :=
  (tmc.extendTapes (Fin.castLEEmb (le_max_left _ _))).outputToWord.seq
    ((branch (Fin.last _)
        ((tm₁.extendTapes (Fin.castLEEmb ((le_max_left k₁ k₂).trans
          (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
        ((tm₂.extendTapes (Fin.castLEEmb ((le_max_right k₁ k₂).trans
          (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)).seq
      ((clearWork Symbol).extendTapes (tapeEmb (Fin.last _))))

namespace Ite

/-- A tidy machine, padded to `K` work tapes and placed below a last work tape that holds `w`
throughout. -/
lemma transformsTapes_padded {k K : ℕ} (hk : k ≤ K) {S : Type*} {tm : MultiTapeTM k Symbol S}
    {x w y : List Symbol} {t s : ℕ} (h : tm.ComputesTidilyInTimeAndSpace x y t s) :
    TransformsTapes ((tm.extendTapes (Fin.castLEEmb hk)).extendTapes Fin.castSuccEmb)
      (fun inp ws => inp = x ∧ ws = Function.update (fun _ => []) (Fin.last K) w)
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last K) w ∧ e = y)
      t (s + (K - k) + (K + 1 - K)) := by
  refine (TransformsTapes.extendTapes (h.extendTapes (Fin.castLEEmb hk)) Fin.castSuccEmb).imp
    (fun _ ws ⟨hin, hws⟩ => ⟨hin, ?_⟩)
    (fun _ ws ws' _ ⟨_, hws⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨?_, he⟩) le_rfl le_rfl
  · subst hws
    funext j
    simp [Fin.castSucc_ne_last]
  · funext l
    induction l using Fin.lastCases with
    | last => rw [hx _ fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj, hws]
    | cast j =>
      rw [show ws' j.castSucc = _ from congrFun hv j]
      simp [Fin.castSucc_ne_last]

end Ite

open Ite in
/-- If `tmc` computes `w` from `x` tidily, `tm₁` computes `y` from `x` tidily when `w` is non-empty
and `tm₂` does when `w` is empty, then `iteTM tmc tm₁ tm₂` computes `y` from `x` tidily, within the
bounds of `tmc` plus those of the machine that runs. -/
public theorem ComputesTidilyInTimeAndSpace.ite {tmc : MultiTapeTM k₀ Symbol S₀}
    {tm₁ : MultiTapeTM k₁ Symbol S₁} {tm₂ : MultiTapeTM k₂ Symbol S₂} {x w y : List Symbol}
    {tc sc t₁ s₁ t₂ s₂ : ℕ} (hc : tmc.ComputesTidilyInTimeAndSpace x w tc sc)
    (h₁ : w ≠ [] → tm₁.ComputesTidilyInTimeAndSpace x y t₁ s₁)
    (h₂ : w = [] → tm₂.ComputesTidilyInTimeAndSpace x y t₂ s₂) :
    (iteTM tmc tm₁ tm₂).ComputesTidilyInTimeAndSpace x y
      (tc + (if w = [] then t₂ else t₁) + 4 * w.length + 6)
      (sc + (if w = [] then s₂ else s₁) + 3 * w.length + 5 * max k₀ (max k₁ k₂) + 10) := by
  set K := max k₀ (max k₁ k₂)
  -- phase 1: the test word on the last tape
  have hp₁ := (hc.extendTapes (Fin.castLEEmb (le_max_left k₀ (max k₁ k₂)))).outputToWord
  -- phase 2: the branch, with the machine that does not run specified vacuously
  have hM₁ : TransformsTapes ((tm₁.extendTapes (Fin.castLEEmb ((le_max_left k₁ k₂).trans
        (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
      (fun inp ws => (inp = x ∧ ws = Function.update (fun _ => []) (Fin.last K) w) ∧
        ws (Fin.last K) ≠ [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last K) w ∧ e = y)
      (if w = [] then 0 else t₁) (if w = [] then 0 else s₁ + (K - k₁) + (K + 1 - K)) := by
    split_ifs with hw
    · rintro _ _ _ ⟨⟨_, rfl⟩, hne⟩
      simp [hw] at hne
    · exact (transformsTapes_padded _ (h₁ hw)).imp (fun _ _ h => h.1) (fun _ _ _ _ _ h => h)
        le_rfl le_rfl
  have hM₂ : TransformsTapes ((tm₂.extendTapes (Fin.castLEEmb ((le_max_right k₁ k₂).trans
        (le_max_right k₀ _)))).extendTapes Fin.castSuccEmb)
      (fun inp ws => (inp = x ∧ ws = Function.update (fun _ => []) (Fin.last K) w) ∧
        ws (Fin.last K) = [])
      (fun _ _ ws' e => ws' = Function.update (fun _ => []) (Fin.last K) w ∧ e = y)
      (if w = [] then t₂ else 0) (if w = [] then s₂ + (K - k₂) + (K + 1 - K) else 0) := by
    split_ifs with hw
    · exact (transformsTapes_padded _ (h₂ hw)).imp (fun _ _ h => h.1) (fun _ _ _ _ _ h => h)
        le_rfl le_rfl
    · rintro _ _ _ ⟨⟨_, rfl⟩, he⟩
      simp [hw] at he
  have hp₂ := transformsTapes_branch (Fin.last K) hM₁ hM₂
  -- phase 3: clear the last tape
  have hp₃ := transformsTapes_clearWork_only (Symbol := Symbol) (Fin.last K) w
  refine (transformsTapes_seq hp₁ (hp₂.seq_eq hp₃) fun _ _ _ _ hP hQ => ⟨hP.1, hQ.1⟩).imp
    (fun _ _ h => h) ?_ ?_ ?_
  · rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩
    exact ⟨hws, by simp⟩
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- The test word of a condition: empty exactly for `false`. -/
@[expose] public def encTest : Bool ↪ List Bool :=
  ⟨fun b => if b then [true] else [], fun a b h => by cases a <;> cases b <;> simp_all⟩

public lemma encTest_true : encTest true = [true] := rfl
public lemma encTest_false : encTest false = [] := rfl

/-- Emits `[true]` on the word `w` and nothing on every other word. Its state is the rest of `w`
still to be read, or `none` once the input differs from `w`. -/
@[expose, simps -isSimp step final]
public def eqWordT (w : List Bool) : Transducer Bool (Option {v // v ∈ w.tails}) where
  q₀ := some ⟨w, (List.mem_tails _ _).mpr (List.suffix_refl w)⟩
  step q a := match q with
    | some ⟨b :: v, h⟩ =>
      (if a = b then some ⟨v, (List.mem_tails _ _).mpr ((List.suffix_cons b v).trans
        ((List.mem_tails _ _).mp h))⟩ else none, [])
    | _ => (none, [])
  final q := if q.map Subtype.val = some [] then [true] else []
  length_step_le q a := by rcases q with _ | ⟨_ | _, _⟩ <;> simp
  length_final_le q := by split_ifs <;> simp

lemma eqWordT_run_none (w u : List Bool) : (eqWordT w).run none u = [] := by
  induction u <;> simp [eqWordT_step, eqWordT_final, *]

lemma eqWordT_run (w : List Bool) (u : List Bool) (v : {v // v ∈ w.tails}) :
    (eqWordT w).run (some v) u = if u = v.1 then [true] else [] := by
  obtain ⟨v, hv⟩ := v
  induction u generalizing v with
  | nil => cases v <;> simp [eqWordT_final]
  | cons a u ih =>
    rcases v with _ | ⟨b, v⟩
    · simp [eqWordT_step, eqWordT_run_none]
    · by_cases hab : a = b <;> simp [eqWordT_step, eqWordT_run_none, hab, ih]

public lemma eqWordT_run_q₀ (w u : List Bool) :
    (eqWordT w).run (eqWordT w).q₀ u = if u = w then [true] else [] :=
  eqWordT_run w u _

end Turing.MultiTapeTM
