/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Comp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Linarith

/-!
# Iterating a polynomial-time step until it stops

A loop whose number of rounds is not known in advance: apply a polynomial-time `step` to a
polynomial-time start value until the result has the empty encoding, then apply a polynomial-time
`fin` to the last value before the empty one. Neither the number of rounds `r a` nor a bound on the
intermediate values needs to be computable. They only need to hold along the trajectory from the
start value of each instance. The loop then runs within time `c (r a + 1) N ^ d` and space
`c N ^ d`, where `N` is one more than a bound on the encoded intermediate values and the encoded
instance.

This is the loop of algorithms that iterate until a fixed point, such as breadth-first search until
no new element is found, where the number of rounds is bounded only through the analysis. It is
built from the machine-level loop `Turing.MultiTapeTM.iterateWhile`, which needs the round count
only along the trajectory.

## Main results

* `Turing.MultiTapeTM.exists_computableInTimeAndSpace_iterateWhile`: iterating a polynomial-time
  step until the empty encoding is computable within the number of rounds times a polynomial in
  the size of the intermediate values.
-/

public section

namespace Turing.MultiTapeTM

variable {α β γ : Type} {encIn : α ↪ List Bool} {encState : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-- **Iterating a polynomial-time step until it stops.** Let `init`, `step` and `fin` be
polynomial-time, and along the trajectory from `init a` let `step` produce a value with the empty
encoding first after `r a + 1` rounds, with the values up to round `r a` encoded within `l a` bits.
Then `fin` of the value after `r a` rounds is computable within time `c (r a + 1) N ^ d` and space
`c N ^ d`, for `N = l a + |encIn a| + 1`. Neither `r` nor `l` needs to be computable. -/
theorem exists_computableInTimeAndSpace_iterateWhile {init : α → β} {step : β → β} {fin : β → γ}
    (hinit : ComputableInPolyTime init encIn encState)
    (hstep : ComputableInPolyTime step encState encState)
    (hfin : ComputableInPolyTime fin encState encOut) {r l : α → ℕ}
    (hl : ∀ a, ∀ n ≤ r a, (encState (step^[n] (init a))).length ≤ l a)
    (hne : ∀ a, ∀ n < r a, encState (step^[n + 1] (init a)) ≠ [])
    (hnil : ∀ a, encState (step^[r a + 1] (init a)) = []) :
    ∃ c d, ComputableInTimeAndSpace (fun a => fin (step^[r a] (init a))) encIn encOut
      (fun a => c * (r a + 1) * (l a + (encIn a).length + 1) ^ d)
      (fun a => c * (l a + (encIn a).length + 1) ^ d) := by
  obtain ⟨ti, si, hti, hsi, ki, Si, _, tmi, hi⟩ := hinit.tidy
  obtain ⟨ts, ss, hts, hss, ks, Ss, _, tms, hs⟩ := hstep.tidy
  obtain ⟨tf, sf, htf, hsf, hf⟩ := hfin.tidy
  obtain ⟨ci, di, hti⟩ := hti.exists_le
  obtain ⟨ci', di', hsi⟩ := hsi.exists_le
  obtain ⟨cs, ds, hts⟩ := hts.exists_le
  obtain ⟨cs', ds', hss⟩ := hss.exists_le
  obtain ⟨cf, df, htf⟩ := htf.exists_le
  obtain ⟨cf', df', hsf⟩ := hsf.exists_le
  -- the loop, along the trajectory from `init a`
  have hloop (a : α) := computesTidily_iterateWhile (tm := tms)
    (w := fun n => encState (step^[n] (init a))) (r := r a)
    (t := cs * (l a + 1) ^ ds) (s := cs' * (l a + 1) ^ ds') (l := l a)
    (fun n hn => by
      have h := (hs (step^[n] (init a))).mono
        ((hts _).trans (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left
          (Nat.add_le_add_right (hl a n hn) 1) ds)))
        ((hss _).trans (Nat.mul_le_mul_left cs' (Nat.pow_le_pow_left
          (Nat.add_le_add_right (hl a n hn) 1) ds')))
      simpa only [Function.iterate_succ_apply'] using h)
    (hl a) (hne a) (hnil a) true
  -- the start followed by the loop
  have hmain : ComputableTidilyInTimeAndSpace (fun a => step^[r a] (init a)) encIn encState _ _ :=
    ⟨_, _, inferInstance, (tms.iterateWhile true).comp tmi true,
      fun a => (hi a).comp (hloop a) true⟩
  obtain ⟨c₀, h⟩ := ComputableTidilyInTimeAndSpace.comp_linear hf hmain
  -- the bounds, with `P = (l a + |encIn a| + 1) ^ D` bounding every polynomial term
  obtain ⟨E, hE⟩ : ∃ E, E = 2 * (ks + 3) := ⟨_, rfl⟩
  set D := di + di' + ds + ds' + df + df' + 1
  have hpow (a : α) {e : ℕ} (he : e ≤ D) {x : ℕ} (hx : x + 1 ≤ l a + (encIn a).length + 1) :
      (x + 1) ^ e ≤ (l a + (encIn a).length + 1) ^ D :=
    (Nat.pow_le_pow_left hx e).trans (Nat.pow_le_pow_right (by omega) he)
  refine ⟨ci + ci' + cs + E * cs' + cf + cf' + 2 * c₀ + 6 * ki + E * (6 * ks + 54) + 10 * ks + 200,
    D, ?_⟩
  refine ComputableInTimeAndSpace.mono h.computableInTimeAndSpace (fun a => ?_) (fun a => ?_)
  all_goals
    have h₁ := (hti a).trans (Nat.mul_le_mul_left ci (hpow a (by omega) (by omega)))
    have h₂ := (hsi a).trans (Nat.mul_le_mul_left ci' (hpow a (by omega) (by omega)))
    have h₃ := Nat.mul_le_mul_left cs (hpow a (show ds ≤ D by omega) (x := l a) (by omega))
    have h₄ := Nat.mul_le_mul_left cs' (hpow a (show ds' ≤ D by omega) (x := l a) (by omega))
    have hlast := hl a (r a) le_rfl
    have h₅ := (htf (step^[r a] (init a))).trans
      (Nat.mul_le_mul_left cf (hpow a (show df ≤ D by omega) (by omega)))
    have h₆ := (hsf (step^[r a] (init a))).trans
      (Nat.mul_le_mul_left cf' (hpow a (show df' ≤ D by omega) (by omega)))
    have hlP := hpow a (show 1 ≤ D by omega) (x := l a) (by omega)
    have hfirst := hl a 0 (Nat.zero_le _)
    have hmax : max ki (ks + 1 + 2) ≤ ki + ks + 3 := by omega
    rw [pow_one] at hlP
    generalize (l a + (encIn a).length + 1) ^ D = P at h₁ h₂ h₃ h₄ h₅ h₆ hlP ⊢
  · -- time
    have hloopT : cs * (l a + 1) ^ ds + 10 * l a + 24 ≤ (cs + 34) * P := by linarith
    calc _ ≤ (r a + 1) * ((cs + 34) * P) + (ci + cf + 2 * c₀ + 50) * P := by
          have := Nat.mul_le_mul_left (r a + 1) hloopT
          simp only [Function.iterate_zero, id_eq] at hfirst ⊢
          nlinarith
      _ ≤ (r a + 1) * ((cs + 34) * P) + (r a + 1) * ((ci + cf + 2 * c₀ + 50) * P) :=
          Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)) _
      _ = (cs + 34 + (ci + cf + 2 * c₀ + 50)) * ((r a + 1) * P) := by ring
      _ ≤ _ := by rw [mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
  · -- space
    have hY : cs' * (l a + 1) ^ ds' + 10 * l a + 6 * ks + 44 ≤ (cs' + 6 * ks + 54) * P := by
      have : 6 * ks + 44 ≤ (6 * ks + 44) * P := Nat.le_mul_of_pos_right _ (by omega)
      nlinarith
    have hEY := Nat.mul_le_mul_left E hY
    rw [← hE] at ⊢
    simp only [Function.iterate_zero, id_eq] at hfirst ⊢
    have : 6 * ki + 10 * ks + 94 ≤ (6 * ki + 10 * ks + 94) * P :=
      Nat.le_mul_of_pos_right _ (by omega)
    nlinarith

end Turing.MultiTapeTM
