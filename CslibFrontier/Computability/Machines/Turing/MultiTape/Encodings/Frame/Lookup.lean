/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic

/-!
# Lookup in a framed word followed by a suffix

These pure list laws are shared by the unary take/drop and zip-transducer machine proofs.
They depend only on the framing format, independently of either machine construction.

## Main results

* `Turing.MultiTapeTM.getElem?_frame_append`: the marker and data bit at each framed position.
* `Turing.MultiTapeTM.getElem?_frame_append_length`: the terminator after the framed pairs.
* `Turing.MultiTapeTM.getElem?_frame_append_boundary`: every bit of the suffix beyond the frame.
-/

public section

namespace Turing.MultiTapeTM

/-- The marker and data bit of `u[i]` in a frame followed by any suffix. -/
theorem getElem?_frame_append (u v : List Bool) {i : ℕ} (hi : i < u.length) :
    (frame u ++ v)[2 * i]? = some true ∧ (frame u ++ v)[2 * i + 1]? = some u[i] := by
  induction u generalizing i with
  | nil => simp at hi
  | cons b u ih =>
    rcases i with _ | i
    · simp [frame_cons]
    · obtain ⟨h₁, h₂⟩ := ih (i := i) (by simpa using hi)
      have e₁ : 2 * (i + 1) = 2 * i + 1 + 1 := by omega
      simp only [frame_cons, List.cons_append, e₁, List.getElem?_cons_succ,
        List.getElem_cons_succ]
      exact ⟨h₁, h₂⟩

private theorem frame_append_eq_flatMap (u v : List Bool) :
    frame u ++ v = (u.flatMap fun b => [true, b]) ++ false :: v := by simp [frame]

private theorem length_flatMap_pair (u : List Bool) :
    (u.flatMap fun b => [true, b]).length = 2 * u.length := by
  have := length_frame u
  simp only [frame, List.length_append, List.length_singleton] at this
  omega

/-- After the pairs of a frame comes its terminator `false`. -/
theorem getElem?_frame_append_length (u v : List Bool) :
    (frame u ++ v)[2 * u.length]? = some false := by
  have hlen := length_flatMap_pair u
  rw [frame_append_eq_flatMap, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  rfl

/-- Lookup beyond the frame reads the suffix, including out of bounds. -/
theorem getElem?_frame_append_boundary (u v : List Bool) (j : ℕ) :
    (frame u ++ v)[2 * u.length + 1 + j]? = v[j]? := by
  have hlen := length_flatMap_pair u
  rw [frame_append_eq_flatMap, List.getElem?_append_right (by omega), hlen,
    (by omega : 2 * u.length + 1 + j - 2 * u.length = j + 1)]
  rfl

end Turing.MultiTapeTM
