/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Cryptanalysis.AddXNORClasses

/-!
# Class labels wider than the physical state

For the deterministic part of [WangLvShenZhang2027], Theorem 7 (PDF p. 22),
zero-extension adds only empty classes. It does not change the maximum smaller
class population. This statement concerns labels on already evaluated states;
zero-extension is not a homomorphism for modular addition or XNOR.

## Main results

* `classBalance_of_width_le`: extending labels beyond the word width preserves balance.
* `classBalance_min_width`: capping the requested label width loses no balance information.
-/

public section
namespace Cslib.Cryptanalysis.AddXNOR

private theorem extend_injective {m p : ℕ} (hp : m ≤ p) :
    Function.Injective (fun x : BitVec m => x.setWidth p) := by
  intro x y h
  have h' := congrArg (fun z : BitVec p => z.setWidth m) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hp, BitVec.setWidth_eq] using h'

/-- Above the physical word width, each nonempty label is a zero-extended full state.
The added labels are empty, so the deterministic maximum is unchanged. -/
theorem classBalance_of_width_le {m p l r : ℕ} (hp : m ≤ p)
    (left : Fin l → BitVec m) (right : Fin r → BitVec m) (s t : BitVec m) :
    classBalance p left right s t = classBalance m left right s t := by
  have inj := extend_injective hp
  have forward_le (g : BitVec p) :
      forwardClassCount p left s g ≤ forwardClassCount m left s (g.setWidth m) := by
    apply Finset.sum_le_sum
    intro bs _
    by_cases h : (eval (steps bs left) s).setWidth p = g
    · have he := congrArg (fun z : BitVec p => z.setWidth m) h
      simp only [BitVec.setWidth_setWidth_of_le _ hp, BitVec.setWidth_eq] at he
      simp only [BitVec.setWidth_eq, he]
      split_ifs <;> omega
    · simp [h]
  have backward_le (g : BitVec p) :
      backwardClassCount p right t g ≤ backwardClassCount m right t (g.setWidth m) := by
    apply Finset.sum_le_sum
    intro bs _
    by_cases h : (backward (steps bs right) t).setWidth p = g
    · have he := congrArg (fun z : BitVec p => z.setWidth m) h
      simp only [BitVec.setWidth_setWidth_of_le _ hp, BitVec.setWidth_eq] at he
      simp only [BitVec.setWidth_eq, he]
      split_ifs <;> omega
    · simp [h]
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro g _
    exact (min_le_min (forward_le g) (backward_le g)).trans
      (min_classCount_le_balance m left right s t (g.setWidth m))
  · apply Finset.sup_le
    intro g _
    have hf : forwardClassCount p left s (g.setWidth p) = forwardClassCount m left s g := by
      simp only [forwardClassCount, inj.eq_iff, BitVec.setWidth_eq]
    have hb : backwardClassCount p right t (g.setWidth p) = backwardClassCount m right t g := by
      simp only [backwardClassCount, inj.eq_iff, BitVec.setWidth_eq]
    rw [← hf, ← hb]
    exact min_classCount_le_balance p left right s t (g.setWidth p)

/-- Requested depths beyond the state width only add empty classes. -/
theorem classBalance_min_width {m l r : ℕ} (p : ℕ)
    (left : Fin l → BitVec m) (right : Fin r → BitVec m) (s t : BitVec m) :
    classBalance (min p m) left right s t = classBalance p left right s t := by
  rcases le_total p m with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, classBalance_of_width_le h]

end Cslib.Cryptanalysis.AddXNOR
