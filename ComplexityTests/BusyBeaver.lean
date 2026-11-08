/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.BusyBeaver
import Mathlib.Computability.Ackermann
import Mathlib.Data.Nat.Size

/-!
# Busy beaver clients

The four codes of size at most `3` are `zero`, `succ`, `left` and `right`. On input `0` they output
`0`, `1`, `0`, `0`, each with fuel `1`, so `bbOutput 0 = 0`, `bbOutput 3 = 1` (the function is
monotone but not strictly so) and `bbSteps 3 = 1`. The code `pair succ succ` has size `16` and
outputs `Nat.pair 1 1 = 3`, so `3 ≤ bbOutput 16`. The halting characterization accepts the code
`zero`. Domination is applied to the diagonal Ackermann function, which is computable but not
primitive recursive, to `n ↦ n` (so `bbOutput` is unbounded), and to bit-length indexing.
-/

namespace ComplexityTests.BusyBeaver

open Cslib.BusyBeaver Cslib.BlumComplexity Encodable Nat.Partrec Filter

/-- The codes of size at most `3` are the four basic codes. -/
private theorem eq_of_encode_le_three {c : Code} (hc : encode c ≤ 3) :
    c = .zero ∨ c = .succ ∨ c = .left ∨ c = .right := by
  cases c <;> simp_all [Code.encodeCode_eq, Code.encodeCode]

private theorem mem_eval_succ_zero : 1 ∈ Code.succ.eval 0 :=
  Part.mem_some 1

/-- The only code of size `0` outputs `0`. -/
example : bbOutput 0 = 0 := by
  obtain ⟨c, hc, hx⟩ := exists_mem_eval_bbOutput 0
  have hc0 : c = .zero := by cases c <;> simp_all [Code.encodeCode_eq, Code.encodeCode]
  subst hc0
  exact Part.mem_some_iff.1 hx

/-- The best code of size at most `3` is `succ`, with output `1`. Together with `bbOutput 1 = 1`
below, this shows `bbOutput` is not strictly monotone. -/
theorem bbOutput_three : bbOutput 3 = 1 := by
  refine le_antisymm ?_ (le_bbOutput (c := .succ) (by decide) mem_eval_succ_zero)
  obtain ⟨c, hc, hx⟩ := exists_mem_eval_bbOutput 3
  rcases eq_of_encode_le_three hc with rfl | rfl | rfl | rfl <;>
    simp [Code.eval, pure, PFun.pure] at hx <;> omega

example : bbOutput 1 = 1 :=
  le_antisymm ((monotone_bbOutput (show 1 ≤ 3 by decide)).trans_eq bbOutput_three)
    (le_bbOutput (c := .succ) (by decide) mem_eval_succ_zero)

/-- Each basic code needs fuel exactly `1` on input `0`. -/
theorem bbSteps_three : bbSteps 3 = 1 := by
  obtain ⟨c, hc, hk⟩ := exists_mem_evalnFuel_bbSteps 3
  obtain ⟨hsome, hmin⟩ := mem_evalnFuel_iff.1 hk
  have hpos : 0 < bbSteps 3 := by
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hsome
    exact lt_of_le_of_lt (Nat.zero_le 0) (Code.evaln_bound hx)
  by_contra hne
  have h1 := hmin 1 (by omega)
  rcases eq_of_encode_le_three hc with rfl | rfl | rfl | rfl <;> simp [Code.evaln] at h1

/-- The code `pair succ succ` has size `16` and outputs `Nat.pair 1 1 = 3`. -/
example : 3 ≤ bbOutput 16 :=
  le_bbOutput (c := .pair .succ .succ) (by decide)
    (Part.mem_bind (Part.mem_map _ (Part.mem_some 1)) (Part.mem_map _ (Part.mem_some 1)))

/-- The halting characterization: `zero` halts, and fuel `bbSteps 0` detects it. -/
example : (Code.evaln (bbSteps 0) Code.zero 0).isSome :=
  (dom_eval_iff_isSome_evaln_bbSteps (c := .zero) le_rfl).1
    (Part.dom_iff_mem.2 ⟨0, Part.mem_some 0⟩)

/-- `bbOutput` eventually exceeds the diagonal Ackermann function, which is computable but not
primitive recursive. -/
example : ∀ᶠ n in atTop, ack n n < bbOutput n :=
  eventually_lt_bbOutput (computable₂_ack.comp Computable.id Computable.id)

example : ∀ᶠ n in atTop, ack n n < bbSteps n :=
  eventually_lt_bbSteps (computable₂_ack.comp Computable.id Computable.id)

/-- `bbOutput` is unbounded. -/
example : Tendsto bbOutput atTop atTop :=
  tendsto_atTop_mono' atTop (eventually_lt_bbOutput Computable.id |>.mono fun _ h => h.le)
    tendsto_id

/-- Bit-length indexing: the codes with `Nat.size (encode c) ≤ ℓ` are those with
`encode c ≤ 2 ^ ℓ - 1`, and the busy beaver function so indexed still dominates. -/
example (c : Code) (ℓ : ℕ) : Nat.size (encode c) ≤ ℓ ↔ encode c ≤ 2 ^ ℓ - 1 := by
  rw [Nat.size_le]
  have := Nat.one_le_two_pow (n := ℓ)
  omega

example : ∀ᶠ ℓ in atTop, ack ℓ ℓ < bbOutput (2 ^ ℓ - 1) :=
  eventually_lt_bbOutput_comp (computable₂_ack.comp Computable.id Computable.id)
    fun _ => Nat.le_sub_one_of_lt Nat.lt_two_pow_self

/-- The two halting-problem routes and the two domination routes agree. -/
example : ¬ Computable bbSteps := fun h => not_exists_computable_bbSteps_le ⟨_, h, fun _ => le_rfl⟩

example : ¬ Computable bbOutput := fun h =>
  not_exists_computable_bbOutput_le ⟨_, h, fun _ => le_rfl⟩

end ComplexityTests.BusyBeaver
