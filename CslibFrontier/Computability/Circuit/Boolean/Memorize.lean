/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
import Mathlib.Tactic

/-!
# Memorizing a function on few points

A De Morgan formula of `binaryCost` depth at most `⌈log₂ n⌉ + ⌈log₂ K⌉` agrees with any
`g : BitString n → Bool` on a set `T` of `K` points and is a chosen constant `b` elsewhere
(`exists_memorize`). It is the balanced disjunction of the equality tests (`Formula.eqFormula`) of
the points of `T` where `g` is not `b`, negated when `b` is true. This is the memorization step of
[ChukhinKulikovMihajlinSmal2026], proof of Lemma 6.3 (printed p. 15; PDF p. 16).

## Main results

* `Cslib.Circuits.Boolean.exists_memorize`: memorizing `g` on `T`.
-/

public section

namespace Cslib.Circuits.Boolean

open Formula

variable {n : ℕ}

/-- **Memorization.** For `g : BitString n → Bool`, a finite set `T` and a constant `b`, some
formula of `binaryCost` depth at most `⌈log₂ n⌉ + ⌈log₂ |T|⌉` equals `g` on `T` and `b` outside
`T`. -/
theorem exists_memorize (g : BitString n → Bool) (T : Finset (BitString n)) (b : Bool) :
    ∃ F : Formula signature n, (∀ x ∈ T, F.eval interpretation x = g x) ∧
      (∀ x ∉ T, F.eval interpretation x = b) ∧
      F.depthWith binaryCost ≤ Nat.clog 2 n + Nat.clog 2 T.card := by
  classical
  set l := (T.filter fun x => g x ≠ b).toList.map eqFormula
  set D := orList l
  have hD (x : BitString n) : D.eval interpretation x = decide (x ∈ T ∧ g x ≠ b) := by
    simp only [D, l, eval_orList, List.any_map, Function.comp_def, eval_eqFormula]
    rw [Bool.eq_iff_iff]
    simp [List.any_eq_true]
  have hlen : l.length ≤ T.card := by
    simp only [l, List.length_map, Finset.length_toList]
    exact Finset.card_filter_le _ _
  refine ⟨if b then D.not else D, fun x hx => ?_, fun x hx => ?_, ?_⟩
  · cases b <;> cases hg : g x <;> simp [hD, hx, hg]
  · cases b <;> simp [hD, hx]
  · have hd : D.depthWith binaryCost ≤ Nat.clog 2 n + Nat.clog 2 l.length :=
      depthWith_binaryCost_orList_le fun F hF => by
        simp only [l, List.mem_map] at hF
        obtain ⟨z, -, rfl⟩ := hF
        exact depthWith_eqFormula_le z
    have := Nat.clog_mono_right 2 hlen
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true, depthWith_not,
      binaryCost_not, add_zero] <;> omega

end Cslib.Circuits.Boolean
