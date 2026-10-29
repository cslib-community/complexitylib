/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.NormalForm
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ConditionalMachine

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Direct charged asymptotic composition and case distinction

The same realizing machine is normalized within the internal construction proof. Composition
uses the encoded-output charge already included in `ComputableInO`; it is not a rule for the
uncharged `ComputableInBigO` predicate. The independent time and space functions are retained.
Adapted from #869 by worker-claude-tidyspike-c4b0c164.

## Main results

* `ComputableInO.comp`: add the inner and outer resource bounds.
* `ComputableInO.ite`: pay for the test and the branch actually taken.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- **Composition** within time `O(T₁ a + T₂ (g a))` and space `O(S₁ a + S₂ (g a))`, through the
machine-level composition of tidy machines. -/
theorem comp {f : β → γ} {g : α → β} {T₁ S₁ : α → ℕ} {T₂ S₂ : β → ℕ}
    (hf : ComputableInO f encMid encOut T₂ S₂) (hg : ComputableInO g encIn encMid T₁ S₁) :
    ComputableInO (f ∘ g) encIn encOut (fun a => T₁ a + T₂ (g a))
      (fun a => S₁ a + S₂ (g a)) := by
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := Internal.NormalForm.inO hg
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := Internal.NormalForm.inO hf
  refine ⟨6 * c₁ + c₂ + (6 * max k₁ k₂ + 20), ⟨_, _, inferInstance, tm₂.comp tm₁ true,
    fun a => (((h₁ a).comp (h₂ (g a)) true).mono ?_ ?_).computesInTimeAndSpace⟩, fun a => ?_⟩
  · -- the intermediate word is no longer than the time of `g`
    have hm := (h₁ a).length_output_le
    have := Nat.mul_le_mul_left c₁ (by omega : T₁ a + 1 ≤ T₁ a + T₂ (g a) + 1)
    have := Nat.mul_le_mul_left c₂ (by omega : T₂ (g a) + 1 ≤ T₁ a + T₂ (g a) + 1)
    have e : (6 * c₁ + c₂) * (T₁ a + T₂ (g a) + 1) =
        6 * (c₁ * (T₁ a + T₂ (g a) + 1)) + c₂ * (T₁ a + T₂ (g a) + 1) := by ring
    beta_reduce
    exact Internal.NormalForm.le_mul_succ (A := 6 * c₁ + c₂) (B := 6 * max k₁ k₂ + 20) (by omega)
      le_rfl
  · -- the intermediate word is within the space bound of `g`
    have hm := l₁ a
    have := Nat.mul_le_mul_left c₁ (by omega : S₁ a + 1 ≤ S₁ a + S₂ (g a) + 1)
    have := Nat.mul_le_mul_left c₂ (by omega : S₂ (g a) + 1 ≤ S₁ a + S₂ (g a) + 1)
    have e : (6 * c₁ + c₂) * (S₁ a + S₂ (g a) + 1) =
        6 * (c₁ * (S₁ a + S₂ (g a) + 1)) + c₂ * (S₁ a + S₂ (g a) + 1) := by ring
    beta_reduce
    exact Internal.NormalForm.le_mul_succ (A := 6 * c₁ + c₂) (B := 6 * max k₁ k₂ + 20) (by omega)
      le_rfl
  · have := Nat.mul_le_mul_left c₂ (by omega : S₂ (g a) + 1 ≤ S₁ a + S₂ (g a) + 1)
    exact (l₂ (g a)).trans (this.trans (Nat.mul_le_mul_right _ (by omega)))

/-- **Case distinction** within the bounds of the test plus those of the branch taken, through the
explicit-bound case-distinction combinator. -/
theorem ite {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    {Tc Tf Tg Sc Sf Sg : α → ℕ} (hc : ComputableInO c encIn encC Tc Sc)
    (hf : ComputableInO f encIn encMid Tf Sf) (hg : ComputableInO g encIn encMid Tg Sg) :
    ComputableInO (fun x => if c x then f x else g x) encIn encMid
      (fun x => Tc x + if c x then Tf x else Tg x)
      (fun x => Sc x + if c x then Sf x else Sg x) := by
  obtain ⟨c₀, ⟨k₀, Q₀, _, tm₀, h₀⟩, -⟩ := Internal.NormalForm.inO hc
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := Internal.NormalForm.inO hf
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := Internal.NormalForm.inO hg
  obtain ⟨k, K, Q, _, tm, h⟩ := Internal.conditional (encOut := encMid)
    (f := f) (g := g)
    (tc := fun a => c₀ * (Tc a + 1)) (sc := fun a => c₀ * (Sc a + 1))
    (tf := fun a => c₁ * (Tf a + 1)) (sf := fun a => c₁ * (Sf a + 1))
    (tg := fun a => c₂ * (Tg a + 1)) (sg := fun a => c₂ * (Sg a + 1))
    h₀ (fun x => h₁ x.1) (fun x => h₂ x.1)
  -- each bound is a sum of two terms, each at most a constant times their sum plus one
  have key (c' d' X Y : ℕ) (u : ℕ) (hu : u ≤ c₀ * (X + 1) + c' * (Y + 1) + d')
      (hc' : c' + d' ≤ c₁ + c₂ + k) : u ≤ (c₀ + c₁ + c₂ + k) * (X + Y + 1) := by
    have := Nat.mul_le_mul_left c₀ (by omega : X + 1 ≤ X + Y + 1)
    have := Nat.mul_le_mul_left c' (by omega : Y + 1 ≤ X + Y + 1)
    have e : (c₀ + c') * (X + Y + 1) = c₀ * (X + Y + 1) + c' * (X + Y + 1) := by ring
    exact Internal.NormalForm.le_mul_succ (A := c₀ + c') (B := d') (by omega) (by omega)
  refine ⟨c₀ + c₁ + c₂ + k, ⟨K, Q, inferInstance, tm,
    fun x => ((h x).mono ?_ ?_).computesInTimeAndSpace⟩, fun x => ?_⟩
  · beta_reduce
    split_ifs
    · exact key c₁ k _ _ _ le_rfl (by omega)
    · exact key c₂ k _ _ _ le_rfl (by omega)
  · beta_reduce
    split_ifs
    · exact key c₁ k _ _ _ le_rfl (by omega)
    · exact key c₂ k _ _ _ le_rfl (by omega)
  · beta_reduce
    split_ifs
    · exact key c₁ 0 _ _ _ (by have := l₁ x; omega) (by omega)
    · exact key c₂ 0 _ _ _ (by have := l₂ x; omega) (by omega)

end Turing.MultiTapeTM.ComputableInO
