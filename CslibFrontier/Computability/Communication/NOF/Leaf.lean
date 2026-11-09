/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.NOF.Protocol

/-!
# Leaves of number-on-forehead protocols

The bits written while a deterministic number-on-forehead protocol runs on an input determine the
leaf it reaches, and conversely. We number the leaves from left to right (`NOF.Protocol.leaf`), as
for two-party protocols. There are at most `2 ^ depth` of them
(`NOF.Protocol.leafCount_le_two_pow_depth`), and the output is a function of the leaf
(`NOF.Protocol.run_eq_of_leaf_eq`).

The basic structural fact is the **star lemma** (`NOF.Protocol.leaf_eq_of_view_eq`). Suppose that
for every player `i` some input `y i`, which player `i` cannot tell apart from `q`, reaches the leaf
`l`. Then `q` reaches `l` too. At each node the speaker writes the same bit on `q` as on their own
witness, and all the witnesses take the same branch. Equivalently, the inputs reaching a leaf form
a cylinder intersection (`NOF.Protocol.isCylinderIntersection_leaf`, in the discrepancy module).
This is what makes Ramsey-type lower bounds work: a leaf containing the corners of a "star"
contains its center.

## Main definitions

* `Cslib.Communication.NOF.Protocol.leafCount`, `Cslib.Communication.NOF.Protocol.leaf`: the
  number of leaves and the leaf reached by an input.

## Main results

* `Cslib.Communication.NOF.Protocol.leafCount_le_two_pow_depth`: at most `2 ^ depth` leaves.
* `Cslib.Communication.NOF.Protocol.run_eq_of_leaf_eq`: inputs at the same leaf get the same output.
* `Cslib.Communication.NOF.Protocol.leaf_eq_of_view_eq`: the star lemma.

## References

* [A. K. Chandra, M. L. Furst and R. J. Lipton, *Multi-party protocols*][ChandraFurstLipton1983]
* [A. Rao and A. Yehudayoff, *Communication Complexity and Applications*][RaoYehudayoff2020]
-/

public section

namespace Cslib.Communication.NOF.Protocol

universe u v w

variable {ι : Type u} {X : ι → Type v} {Z : Type w}

/-- The number of leaves of a protocol. It is exposed because the type `Fin p.leafCount` of
`leaf` must unfold along the protocol. -/
@[expose] def leafCount : Protocol X Z → ℕ
  | output _ => 1
  | speak _ _ p₀ p₁ => p₀.leafCount + p₁.leafCount

/-- The leaf a protocol reaches on the input `x`, numbering the leaves from left to right. -/
def leaf : (p : Protocol X Z) → (∀ i, X i) → Fin p.leafCount
  | output _, _ => (0 : Fin 1)
  | speak i send p₀ p₁, x =>
    cond (send (view i x)) (Fin.natAdd p₀.leafCount (p₁.leaf x))
      (Fin.castAdd p₁.leafCount (p₀.leaf x))

@[simp] theorem leafCount_output (z : Z) : (output z : Protocol X Z).leafCount = 1 :=
  rfl

@[simp] theorem leafCount_speak (i : ι) (send : View X i → Bool) (p₀ p₁ : Protocol X Z) :
    (speak i send p₀ p₁).leafCount = p₀.leafCount + p₁.leafCount :=
  rfl

@[simp] theorem leaf_output (z : Z) (x : ∀ i, X i) :
    (output z : Protocol X Z).leaf x = ⟨0, Nat.one_pos⟩ := by
  rw [leaf]
  rfl

@[simp] theorem leaf_speak (i : ι) (send : View X i → Bool) (p₀ p₁ : Protocol X Z) (x : ∀ i, X i) :
    (speak i send p₀ p₁).leaf x =
      cond (send (view i x)) (Fin.natAdd p₀.leafCount (p₁.leaf x))
        (Fin.castAdd p₁.leafCount (p₀.leaf x)) := by
  rw [leaf]
  rfl

/-- Every protocol has a leaf. -/
theorem leafCount_pos (p : Protocol X Z) : 0 < p.leafCount := by
  induction p with
  | output z => exact Nat.one_pos
  | speak i send p₀ p₁ ih₀ _ => exact Nat.add_pos_left ih₀ _

/-- With no players nobody can speak, so a protocol is a single leaf. -/
theorem leafCount_eq_one_of_isEmpty [IsEmpty ι] (p : Protocol X Z) : p.leafCount = 1 := by
  cases p with
  | output z => rfl
  | speak i _ _ _ => exact (IsEmpty.false i).elim

/-- **At most `2 ^ depth` leaves.** -/
theorem leafCount_le_two_pow_depth (p : Protocol X Z) : p.leafCount ≤ 2 ^ p.depth := by
  induction p with
  | output z => simp
  | speak i send p₀ p₁ ih₀ ih₁ =>
    rw [leafCount_speak, depth_speak, pow_succ, mul_two]
    exact add_le_add (ih₀.trans (Nat.pow_le_pow_right two_pos (le_max_left _ _)))
      (ih₁.trans (Nat.pow_le_pow_right two_pos (le_max_right _ _)))

/-- Two inputs reach the same leaf below a node when the speaker writes the same bit on both and
they reach the same leaf of the branch taken. -/
theorem leaf_speak_eq_iff {i : ι} {send : View X i → Bool} {p₀ p₁ : Protocol X Z}
    {x y : ∀ j, X j} :
    (speak i send p₀ p₁).leaf x = (speak i send p₀ p₁).leaf y ↔
      (send (view i x) = true ∧ send (view i y) = true ∧ p₁.leaf x = p₁.leaf y) ∨
        (send (view i x) = false ∧ send (view i y) = false ∧ p₀.leaf x = p₀.leaf y) := by
  simp only [leaf_speak]
  cases send (view i x) <;> cases send (view i y) <;> simp [Fin.ext_iff] <;> omega

/-- **The output is a function of the leaf.** -/
theorem run_eq_of_leaf_eq (p : Protocol X Z) {x y : ∀ i, X i} (h : p.leaf x = p.leaf y) :
    p.run x = p.run y := by
  induction p with
  | output z => rfl
  | speak i send p₀ p₁ ih₀ ih₁ =>
    rcases leaf_speak_eq_iff.mp h with ⟨hx, hy, h₁⟩ | ⟨hx, hy, h₀⟩
    · simp only [run_speak, hx, hy, Bool.cond_true, ih₁ h₁]
    · simp only [run_speak, hx, hy, Bool.cond_false, ih₀ h₀]

/-- **The star lemma.** If, for every player `i`, an input `y i` that player `i` cannot tell apart
from `q` (`view i (y i) = view i q`) reaches the same leaf as every other `y j`, then `q` reaches
that leaf too. -/
theorem leaf_eq_of_view_eq (p : Protocol X Z) {q : ∀ i, X i} {y : ι → ∀ i, X i}
    (hview : ∀ i, view i (y i) = view i q) (hleaf : ∀ i j, p.leaf (y i) = p.leaf (y j)) (i : ι) :
    p.leaf q = p.leaf (y i) := by
  induction p generalizing i with
  | output z => rfl
  | speak k send p₀ p₁ ih₀ ih₁ =>
    -- Every witness takes the branch of player `k`'s witness, which is the branch of `q`.
    have hk : ∀ j, send (view k (y j)) = send (view k q) := fun j => by
      rcases leaf_speak_eq_iff.mp (hleaf j k) with ⟨hj, hk', _⟩ | ⟨hj, hk', _⟩ <;>
        rw [hj, ← hview k, hk']
    cases hq : send (view k q)
    · have h₀ : ∀ j j', p₀.leaf (y j) = p₀.leaf (y j') := fun j j' => by
        rcases leaf_speak_eq_iff.mp (hleaf j j') with ⟨hj, -, -⟩ | ⟨-, -, h⟩
        · rw [hk j, hq] at hj
          exact absurd hj (by decide)
        · exact h
      exact leaf_speak_eq_iff.mpr (Or.inr ⟨hq, (hk i).trans hq, ih₀ h₀ i⟩)
    · have h₁ : ∀ j j', p₁.leaf (y j) = p₁.leaf (y j') := fun j j' => by
        rcases leaf_speak_eq_iff.mp (hleaf j j') with ⟨-, -, h⟩ | ⟨hj, -, -⟩
        · exact h
        · rw [hk j, hq] at hj
          exact absurd hj (by decide)
      exact leaf_speak_eq_iff.mpr (Or.inl ⟨hq, (hk i).trans hq, ih₁ h₁ i⟩)

end Cslib.Communication.NOF.Protocol
