/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Operators

/-! Clients of the native BP·NP equality, including nonconstant and empty message blocks. -/

set_option linter.privateModule false

open Cslib.Complexity Turing.MultiTapeTM

private theorem univ_mem_AM {α : Type} (enc : α ↪ List Bool) (p q : Polynomial ℕ) :
    Set.univ ∈ AM enc := by
  refine ⟨p, q, fun _ => true, ComputableInPolyTime.const true, ?_⟩
  intro a
  constructor
  · intro _
    simp
  · simp

-- Both message lengths vary, with an encoding of instances that is not the identity.
example : Set.univ ∈ BPOp encUnary (NP (encPair encUnary encBits)) := by
  rw [BPOp_NP]
  exact univ_mem_AM encUnary Polynomial.X (Polynomial.X ^ 2 + 1)

-- Empty coin and reply blocks are allowed.
example : Set.univ ∈ BPOp encUnary (NP (encPair encUnary encBits)) := by
  rw [BPOp_NP]
  exact univ_mem_AM encUnary 0 0

-- Soundness is tested too, with nonconstant coin and certificate bounds.
example : (∅ : Set ℕ) ∈ AM encUnary := by
  refine ⟨Polynomial.X + 1, Polynomial.X ^ 2, fun _ => false,
    ComputableInPolyTime.const false, ?_⟩
  intro a
  constructor
  · simp
  · intro _
    rw [Finset.filter_true_of_mem (fun _ _ => fun _ => rfl)]
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    simp

-- A library consumer transfers membership and obtains advice without reconstructing blocks.
example {α : Type} {enc : α ↪ List Bool} {A : Set α}
    (hA : A ∈ BPOp enc (NP (encPair enc encBits))) : A ∈ NPPoly enc :=
  BPOp_NP_subset_NPPoly hA
