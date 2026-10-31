/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Probability.PairwiseIndependentHash.FrameSubstitution
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for affine substitution invariance of frame-conditioned channels

Substituting `2 y + 1` over `𝔽₃` swaps the identifiers `0` and `1` and leaves the joint retention
law unchanged. The constant substitution `α = 0` changes that law, so `α ≠ 0` is needed.
-/

namespace ComplexityTests.FrameSubstitution

open Finset Cslib.Probability

private instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The channel `y ↦ (1 + y, 2 + y ^ 2)` over `𝔽₅`, with the standard frame of length two. -/
private def chan : FrameChannel 5 2 2 :=
  (![1, 2], ⟨![![1, 0], ![0, 1]], by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h0 := congrFun hg 0
    have h1 := congrFun hg 1
    simp [Fin.sum_univ_two] at h0 h1
    fin_cases i <;> simpa⟩)

-- The substituted channel evaluates `3` as `chan` evaluates `2 · 3 + 1 = 2`, namely `(3, 1)`.
example : (chan.affineSubst 1 (α := 2) (by decide)).eval 3 = ![3, 1] := by
  rw [FrameChannel.eval_affineSubst]
  decide

/-- The event that both `0` and `1` lie in the retention box of side `2`. -/
private abbrev Both (e : ZMod 3 → Fin 1 → ZMod 3) : Prop :=
  e 0 ∈ retentionBox 3 1 2 ∧ e 1 ∈ retentionBox 3 1 2

-- Substituting `2 y + 1` exchanges `0` and `1`; the law is unchanged, for frames of length two in
-- `𝔽₃ ^ 2` as for any other.
example (E : (ZMod 3 → Fin 2 → ZMod 3) → Prop) [DecidablePred E] :
    dens {A : FrameChannel 3 2 2 | E fun y ↦ A.eval (2 * y + 1)} =
      dens {A : FrameChannel 3 2 2 | E A.eval} :=
  dens_eval_comp_affine (by decide) 1 E

-- The joint law of two independent channels is invariant too.
example (E : (Fin 2 → ZMod 3 → Fin 1 → ZMod 3) → Prop) [DecidablePred E] :
    dens {As : Fin 2 → FrameChannel 3 1 1 | E fun c y ↦ (As c).eval (2 * y + 1)} =
      dens {As : Fin 2 → FrameChannel 3 1 1 | E fun c ↦ (As c).eval} :=
  dens_pi_eval_comp_affine (by decide) 1 E

-- Two of the six channels over `𝔽₃` retain both `0` and `1`, before and after substitution.
example : #{A : FrameChannel 3 1 1 | Both A.eval} = 2 := by decide
example : #{A : FrameChannel 3 1 1 | Both fun y ↦ A.eval (2 * y + 1)} = 2 := by decide

-- With `α = 0` both identifiers become `1`, which four of the six channels retain: the
-- substitution `y ↦ 1` changes the law.
example : #{A : FrameChannel 3 1 1 | Both fun y ↦ A.eval (0 * y + 1)} = 4 := by decide

end ComplexityTests.FrameSubstitution
