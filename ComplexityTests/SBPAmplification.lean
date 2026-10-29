/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.SBP.Amplification
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Uniform #P powers and nonconstant SBP amplification clients -/

@[expose] public section

namespace Cslib.Complexity.Tests.UniformSBP

open Turing.MultiTapeTM

/-- A nonconstant language with a genuinely positive rejecting count. -/
def language : Set (List Bool) := {w | w.headD false = true}

private def count (w : List Bool) : ℕ := if w.headD false then 3 else 1

private theorem count_mem : count ∈ SharpP encBits :=
  mem_SharpP_of_polyTime (f := count) (.of_tidy (by unfold count; fun_prop))

private theorem language_mem : language ∈ SBP encBits := by
  refine ⟨count, count_mem, fun _ => 3, .const 3, fun w => ?_⟩
  cases w with
  | nil => norm_num [count, language]
  | cons b w => cases b <;> norm_num [count, language]

example : [true] ∈ language ∧ [false] ∉ language := by simp [language]

example : count [true] = 3 ∧ count [false] = 1 := by decide

/-- The #P count may be exponential even though its unary exponent is polynomial-time. -/
example : (fun w : List Bool => 3 ^ w.length) ∈ SharpP encBits :=
  SharpP.pow_mem_polyTime (SharpP.natCast_mem 3) (ComputableInPolyTime.encoding_length encBits)

/-- Zero rows accept the empty tuple, even for an always-rejecting zero-width verifier. -/
example : acceptCount (SharpP.powerVerifier (fun _ : Unit => 0) (fun _ => 0)
    (fun _ => false)) () 0 = 1 := by
  change acceptCount _ () (0 * 0) = 1
  rw [SharpP.acceptCount_powerVerifier]
  simp

/-- Positive repetitions of an always-rejecting zero-width verifier have count zero. -/
example (r : ℕ) : acceptCount (SharpP.powerVerifier (fun _ : Unit => r + 1) (fun _ => 0)
    (fun _ => false)) () ((r + 1) * 0) = 0 := by
  rw [SharpP.acceptCount_powerVerifier]
  simp [acceptCount]

/-- One pair of witnesses achieves a gap growing with the input length. -/
example : ∃ f ∈ SharpP encBits, ∃ k : List Bool → ℕ,
    ComputableInPolyTime k encBits encNat ∧ (∀ w, 0 < k w) ∧ ∀ w,
      (w ∈ language → k w ≤ f w) ∧ (w ∉ language → 2 ^ (w.length + 1) * f w < k w) :=
  exists_SBP_gap_pow_polyBounded language_mem (fun w => w.length + 1)
    (PolyBounded.self.add (.const 1))

/-- A zero requested exponent still has a strict nonmember inequality and positive threshold. -/
example : ∃ f ∈ SharpP encBits, ∃ k : List Bool → ℕ,
    ComputableInPolyTime k encBits encNat ∧ (∀ w, 0 < k w) ∧ ∀ w,
      (w ∈ language → k w ≤ f w) ∧ (w ∉ language → 2 ^ (0 : ℕ) * f w < k w) :=
  exists_SBP_gap_pow_polyBounded language_mem (fun _ => 0) (.const 0)

/-- A noncomputable requested rate can be handled by fixed dominating polynomial repetition. -/
example (S : Set (List Bool)) : ∃ f ∈ SharpP encBits, ∃ k : List Bool → ℕ,
    ComputableInPolyTime k encBits encNat ∧ (∀ w, 0 < k w) ∧ ∀ w,
      let r := @ite ℕ (w ∈ S) (Classical.propDecidable _) w.length 0
      (w ∈ language → k w ≤ f w) ∧ (w ∉ language → 2 ^ r * f w < k w) := by
  classical
  apply exists_SBP_gap_pow_polyBounded language_mem
  exact PolyBounded.self.mono fun w => by
    simp only [encBits_apply]
    split_ifs <;> lia

end Cslib.Complexity.Tests.UniformSBP
