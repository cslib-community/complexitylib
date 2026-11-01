/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the enc_len tactic)

public import Complexity.Tactic.EncLen

/-!
# Tests for `enc_len`
-/

public section

open Turing.MultiTapeTM

variable {α β : Type} {eA : α ↪ List Bool} {eB : β ↪ List Bool}

/-- A local encoding, unfolded by name at the call. -/
@[expose] def eLocal : ℕ × Bool ↪ List Bool := encPair encUnary encBool

theorem eLocal_apply (p : ℕ × Bool) : eLocal p = encPair encUnary encBool p := rfl

/-! Nested pairs expand to their fields, with projections of literal pairs reduced. -/

example (a : α) (b : β) (n : ℕ) :
    (eA a).length ≤ (encPair eA (encPair eB encUnary) (a, b, n)).length := by
  enc_len

example (a : α) (b : β) (n : ℕ) :
    n + (eB b).length < (encPair eA (encPair eB encUnary) (a, b, n)).length := by
  enc_len

/-- Variable pairs keep their projections as atoms. -/
example (p : α × β) : (eB p.2).length ≤ (encPair eA eB p).length := by
  enc_len

/-! The standard leaf encodings. -/

example (b : Bool) (w : List Bool) (x : α) :
    (encPair encBool encBits (b, w)).length = 3 + w.length ∧
      (encOption eA (some x)).length = (eA x).length + 1 ∧
      (encOption eA (none : Option α)).length = 0 ∧
      (encSum eA eB (Sum.inl x : α ⊕ β)).length = (eA x).length + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> enc_len

/-! Local encodings are named at the call. -/

example (p : ℕ × Bool) : p.1 ≤ (eLocal p).length := by
  enc_len [eLocal_apply]

/-! Locations work as for `simp`, and hypotheses stay unexpanded otherwise. -/

example (a : α) (b : β) (T : ℕ) (h : (encPair eA eB (a, b)).length ≤ T) : (eA a).length ≤ T := by
  enc_len at h ⊢

example (a : α) (b : β) (T : ℕ) (h : (encPair eA eB (a, b)).length ≤ T) : (eB b).length ≤ T := by
  enc_len at *

/-! A product is an atom, which the expansion rewrites everywhere it is asked to. -/

example (a : α) (b : β) (k T : ℕ) (hk : k * (encPair eA eB (a, b)).length ≤ T) :
    k * (encPair eA eB (a, b)).length + (eA a).length ≤ T + (encPair eA eB (a, b)).length := by
  enc_len at hk ⊢

/-- The tactic also closes a goal that the expansion alone proves. -/
example (n : ℕ) : (encUnary n).length = n := by
  enc_len

/-! Failures. -/

/--
error: enc_len: the expansion failed: `simp` made no progress
If there is no encoded length to expand, use `omega`.
-/
#guard_msgs in
example (a b : ℕ) (h : a ≤ b) : a ≤ b + 1 := by
  enc_len

/-- enc_len: `omega` could not close the expanded goal. -/
#guard_msgs (substring := true) in
example (a : α) (b : β) : (encPair eA eB (a, b)).length ≤ (eA a).length := by
  enc_len

/-! A false bound shows the expanded form, not the original encoding. -/

/-- ⊢ 2 * (eA a).length + 1 + (eB b).length ≤ (eA a).length -/
#guard_msgs (substring := true) in
example (a : α) (b : β) : (encPair eA eB (a, b)).length ≤ (eA a).length := by
  enc_len

/-! Products stay atoms, so this needs a scaling fact. -/

/-- enc_len: `omega` could not close the expanded goal. -/
#guard_msgs (substring := true) in
example (a : α) (b : β) (k : ℕ) :
    k * (eA a).length ≤ k * (encPair eA eB (a, b)).length := by
  enc_len

/-- With the scaling fact in context, the same goal only adds. -/
example (a : α) (b : β) (k : ℕ) :
    k * (eA a).length ≤ k * (encPair eA eB (a, b)).length := by
  have h := Nat.mul_le_mul_left k (length_le_encPair_left eA eB (a, b))
  enc_len at h ⊢

/-! A bad lemma name reports the real error. -/

/-- error: Unknown identifier `noSuchLemma` -/
#guard_msgs in
example (n : ℕ) : (encUnary n).length ≤ n := by
  enc_len [noSuchLemma]
