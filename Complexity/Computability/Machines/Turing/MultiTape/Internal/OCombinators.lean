/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPairPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelAppend
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Direct charged resource combinators

Composition with a linear outer computation preserves independent time/workspace budgets:
the inner machine's clock bounds the intermediate word for time, and its explicit output charge
bounds that same word for workspace. Concatenation and framed pairing retain their output charge.
All construction proofs use only plain certificates and machine-level combinators.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

universe u
variable {α β γ δ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool} {T S : α → ℕ}

/-- The encoded value is within the certificate's existing workspace charge. -/
theorem length_le {f : α → β} (h : ComputableInO f encIn encMid T S) :
    ∃ c, ∀ a, (encMid (f a)).length ≤ c * (S a + 1) :=
  let ⟨c, _, hl⟩ := h
  ⟨c, hl⟩

/-- The encoded value is within the time bound, since the machine writes it. -/
theorem length_le_time {f : α → β} (h : ComputableInO f encIn encMid T S) :
    ∃ c, ∀ a, (encMid (f a)).length ≤ c * (T a + 1) :=
  let ⟨c, ⟨_, _, _, _, htm⟩, _⟩ := h
  ⟨c, fun a => (htm a).length_output_le⟩

/-- A common linear certificate includes the output bound through its actual clock. -/
theorem of_linear {f : α → β} (h : ComputableInLinearTimeAndSpace f encIn encMid) :
    ComputableInO f encIn encMid (fun a => (encIn a).length) (fun a => (encIn a).length) := by
  obtain ⟨c, k, State, hfinite, tm, htm⟩ := Internal.NormalForm.linear h
  exact ⟨c, ⟨k, State, hfinite, tm, fun a => (htm a).computesInTimeAndSpace⟩,
    fun a => (htm a).length_output_le⟩

private theorem linearBound (a b K X m : ℕ) (hm : m ≤ a * (X + 1)) :
    a * (X + 1) + b * (m + 1) + 5 * m + K ≤
      (6 * a + b * (a + 1) + K) * (X + 1) := by
  have hi : b * (m + 1) ≤ b * (a + 1) * (X + 1) := by
    have : m + 1 ≤ (a + 1) * (X + 1) := by nlinarith
    exact (Nat.mul_le_mul_left b this).trans_eq (by ring)
  have hk := Nat.le_mul_of_pos_right K (Nat.succ_pos X)
  simp only [Nat.succ_eq_add_one] at hk
  calc
    _ ≤ 6 * (a * (X + 1)) + b * (a + 1) * (X + 1) + K * (X + 1) := by omega
    _ = _ := by ring

/-- A linear outer computation preserves both independent bounds of the inner certificate. -/
theorem comp_linear {f : β → γ} {g : α → β}
    (hf : ComputableInO f encMid encOut (fun b => (encMid b).length)
      (fun b => (encMid b).length)) (hg : ComputableInO g encIn encMid T S) :
    ComputableInO (f ∘ g) encIn encOut T S := by
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, h₁⟩, l₁⟩ := Internal.NormalForm.inO hg
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, h₂⟩, l₂⟩ := Internal.NormalForm.inO hf
  let K := 6 * max k₁ k₂ + 20
  let C := 6 * c₁ + c₂ * (c₁ + 1) + K
  refine ⟨C, ⟨_, _, inferInstance, tm₂.comp tm₁ true, fun a =>
    (((h₁ a).comp (h₂ (g a)) true).mono ?_ ?_).computesInTimeAndSpace⟩, fun a => ?_⟩
  · have hb := linearBound c₁ c₂ K (T a) _ (h₁ a).length_output_le
    have hk : 9 ≤ K := by dsimp [K]; omega
    dsimp only [C]
    omega
  · exact linearBound c₁ c₂ K (S a) _ (l₁ a)
  · have hb := linearBound c₁ c₂ K (S a) _ (l₁ a)
    have hl := l₂ (g a)
    dsimp only [C, Function.comp_def]
    omega

private theorem sumBound (a b k x y : ℕ) :
    a * (x + 1) + b * (y + 1) + k ≤ (a + b + k) * (x + y + 1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one]
  omega

/-- Concatenate two computed encodings, retaining the sum of both charged bounds. -/
theorem append {enc₂ : δ ↪ List Bool} {f₁ : α → β} {f₂ : α → δ} {g : α → γ}
    {T₁ S₁ T₂ S₂ : α → ℕ}
    (h₁ : ComputableInO f₁ encIn encMid T₁ S₁)
    (h₂ : ComputableInO f₂ encIn enc₂ T₂ S₂)
    (hg : ∀ a, encOut (g a) = encMid (f₁ a) ++ enc₂ (f₂ a)) :
    ComputableInO g encIn encOut (fun a => T₁ a + T₂ a) (fun a => S₁ a + S₂ a) := by
  obtain ⟨c₁, ⟨k₁, Q₁, _, tm₁, hm₁⟩, hl₁⟩ := Internal.NormalForm.inO h₁
  obtain ⟨c₂, ⟨k₂, Q₂, _, tm₂, hm₂⟩, hl₂⟩ := Internal.NormalForm.inO h₂
  let K := 2 * max k₁ k₂
  refine ⟨c₁ + c₂ + K, ⟨_, _, inferInstance, appendTM tm₁ tm₂, fun a => ?_⟩, fun a => ?_⟩
  · rw [hg a]
    refine (((hm₁ a).append (hm₂ a)).mono ?_ ?_).computesInTimeAndSpace
    · have := sumBound c₁ c₂ K (T₁ a) (T₂ a)
      beta_reduce
      omega
    · exact sumBound c₁ c₂ K (S₁ a) (S₂ a)
  · rw [hg a, List.length_append]
    have hleft := hl₁ a
    have hright := hl₂ a
    have := sumBound c₁ c₂ K (S₁ a) (S₂ a)
    beta_reduce
    omega

/-- A fixed output is charged within constant workspace, even when its input is unbounded. -/
theorem constZero (b : β) :
    ComputableInO (fun _ : α => b) encIn encMid (fun a => (encIn a).length) (fun _ => 0) := by
  obtain ⟨c, hc⟩ := computableInTimeAndSpace_of_const (encIn := encIn) (encOut := encMid) b
  refine of_bounds hc (c + (encMid b).length) (fun a => ?_) (fun _ => by simp) (fun _ => ?_)
  · exact (Nat.le_add_right _ _).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos (encIn a).length))
  · simp only [zero_add, mul_one]
    omega

/-- A fixed output fits the input-length charged workspace bound. -/
theorem const (b : β) :
    ComputableInO (fun _ : α => b) encIn encMid (fun a => (encIn a).length)
      (fun a => (encIn a).length) :=
  (constZero b).mono_le (fun _ => le_rfl) (fun _ => Nat.zero_le _)

/-- Standard framed pairing, with the sum of the original time and charged workspace bounds. -/
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} {T₁ S₁ T₂ S₂ : α → ℕ}
    (hf : ComputableInO f encIn enc₁ T₁ S₁) (hg : ComputableInO g encIn enc₂ T₂ S₂) :
    ComputableInO (fun a => (f a, g a)) encIn (encPair enc₁ enc₂)
      (fun a => T₁ a + T₂ a) (fun a => S₁ a + S₂ a) := by
  have hframe : ComputableInO (fun x : β₁ => x) enc₁ (encFramed enc₁)
      (fun a => (enc₁ a).length) (fun a => (enc₁ a).length) :=
    of_linear (.of_frame fun _ => rfl)
  exact (hframe.comp_linear hf).append hg fun _ => rfl

/-- Copy an encoded value without changing its independent representation. -/
theorem of_eq {f : α → β} (h : ∀ a, encMid (f a) = encIn a) :
    ComputableInO f encIn encMid (fun a => (encIn a).length) (fun a => (encIn a).length) :=
  of_linear (.of_eq h)

/-- The first component of a standard framed pair, with linear charged bounds. -/
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInO Prod.fst (encPair enc₁ enc₂) enc₁
      (fun p => (encPair enc₁ enc₂ p).length) (fun p => (encPair enc₁ enc₂ p).length) :=
  of_linear (.fst enc₁ enc₂)

/-- The second component of a standard framed pair, with linear charged bounds. -/
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInO Prod.snd (encPair enc₁ enc₂) enc₂
      (fun p => (encPair enc₁ enc₂ p).length) (fun p => (encPair enc₁ enc₂ p).length) :=
  of_linear (.snd enc₁ enc₂)

/-- Project the first computed component without changing either independent budget. -/
theorem fst' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableInO f encIn (encPair enc₁ enc₂) T S) :
    ComputableInO (fun a => (f a).1) encIn enc₁ T S := (fst enc₁ enc₂).comp_linear h

/-- Project the second computed component without changing either independent budget. -/
theorem snd' {β₁ β₂ : Type u} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁ × β₂} (h : ComputableInO f encIn (encPair enc₁ enc₂) T S) :
    ComputableInO (fun a => (f a).2) encIn enc₂ T S := (snd enc₁ enc₂).comp_linear h

/-- Reinterpret an encoding along an equivalence, retaining the same machine and budgets. -/
theorem of_equiv {δ : Type*} {f : α → β} (h : ComputableInO f encIn encMid T S) (e : δ ≃ α) :
    ComputableInO (f ∘ e) (encOfEquiv e encIn) encMid (T ∘ e) (S ∘ e) :=
  h.of_encIn_eq e fun _ => rfl

end Turing.MultiTapeTM.ComputableInO
