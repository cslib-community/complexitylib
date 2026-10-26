/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81
-- `transformsTapes_clearWork_only` and `ComputableTidilyInTimeAndSpace.comp_linear` are from
-- crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import Mathlib.Basic.Finite.Sum
public import Cslib.Foundations.Data.Fin.Tuple
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ClearWork
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.InputFromTape
public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.OutputToTape
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelFacts

/-! # The existing composition machine and its run theorem

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- `tm₂` after `tm₁`, both with their work tapes padded to `max k₁ k₂`: run `tm₁` with its output
written to the work tape `Fin.natAdd (max k₁ k₂) 0`, run `tm₂` reading its input from that tape
(using `mark` on the last work tape to flag the left end of the input), then clear that tape. -/
public noncomputable def comp (tm₂ : MultiTapeTM k₂ Symbol S₂) (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (mark : Symbol) : MultiTapeTM (max k₁ k₂ + 2) Symbol
      ((S₁ ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ S₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      ((clearWork Symbol).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0))))

/-- Clearing the only non-blank work tape leaves all work tapes blank. -/
public theorem transformsTapes_clearWork_only {k : ℕ} (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i))
      (fun _ ws => ws = Function.update (fun _ => []) i w)
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = []) (3 * (w.length + 1)) (w.length + 1 + k) :=
  (transformsTapes_clearWork_tapeEmb i w).imp (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl

/-- If `tm₁` computes `w` from `x` tidily and `tm₂` computes `y` from `w` tidily, then
`tm₂.comp tm₁ mark` computes `y` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.comp {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x w y : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x w t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace w y t₂ s₂) (mark : Symbol) :
    (tm₂.comp tm₁ mark).ComputesTidilyInTimeAndSpace x y (t₁ + t₂ + 4 * w.length + 9)
      (s₁ + s₂ + 5 * w.length + (6 * max k₁ k₂ + 20)) := by
  set K := max k₁ k₂
  -- the work tape holding the intermediate word `w`
  set A : Fin (K + 2) := Fin.natAdd K 0
  have hA : Fin.append (fun _ : Fin K => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) A w := by
    funext l
    cases l using Fin.addCases with
    | left j => simp [A, Function.update_of_ne (Fin.castAdd_ne_natAdd j 0)]
    | right i => match i with | 0 | 1 => simp [A]
  -- phase 1: `tm₁` writes `w` to `A`
  have hQ₁ (ws' : Fin (K + 1 + 1) → List Symbol)
      (hv : (fun j => ws' (Fin.castSuccEmb j)) = Function.update (fun _ => []) (Fin.last K) w)
      (hx : ∀ l ∉ Set.range Fin.castSuccEmb, ws' l = []) :
      ws' = Function.update (fun _ => []) A w := by
    funext l
    induction l using Fin.lastCases with
    | last =>
      rw [hx _ fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj]
      simp [A, Fin.ext_iff]
    | cast j =>
      rw [show ws' j.castSucc = _ from congrFun hv j]
      simp [A, Function.update_apply, Fin.ext_iff]
  have hp₁ := ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
    Fin.castSuccEmb).imp (P' := fun inp ws => inp = x ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = [])
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ ws' _ ⟨_, hws⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨hQ₁ ws' hv fun l hl => (hx l hl).trans
      (congrFun hws l), he⟩) le_rfl le_rfl
  -- phase 2: `tm₂` reads `w` from `A` and emits `y`
  have hp₂ := (transformsTapes_inputFromWord mark
      (computesTidily_iff.mp (h₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))))).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = y)
    (fun _ _ hws => hws.trans hA.symm) (fun _ _ _ _ _ ⟨hws', he⟩ => ⟨hws'.trans hA, he⟩)
    le_rfl le_rfl
  -- phase 3: clear `A`
  have hclear : Function.update (Function.update (fun _ => []) A w) A [] = fun _ => [] := by
    rw [Function.update_idem]
    exact Function.update_eq_self A _
  have hp₃ := (transformsTapes_clearWork_tapeEmb (Symbol := Symbol) A w).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
    (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by rw [hws', hws, hclear], he⟩) le_rfl le_rfl
  refine (transformsTapes_seq hp₁ (transformsTapes_seq hp₂ hp₃ fun _ _ _ _ _ hQ => hQ.1)
    fun _ _ _ _ _ hQ => hQ.1).imp (fun _ _ h => h) ?_ (by omega) (by omega)
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩, rfl⟩
  exact ⟨hws, by simp⟩

end Turing.MultiTapeTM
