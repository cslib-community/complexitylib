/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.TopDown.Rectangle
import Mathlib.Tactic.Linarith

/-!
# Korten's top-down adversary

A protocol with `d` messages of at most `m` bits cannot separate a density rectangle of small
rate: by induction on the messages, each message leaves a density rectangle, at the end no
coordinate separates it, and the deficits grow as `194 ^ i k` and the rates as
`(32768 · 194 ^ d k) ^ i p` (`RoundProtocol.not_solves_bounded_density`)
[Korten, Sections 2 to 4][Korten2026]. When the starting sets are density limits of each other,
the first message needs no mirror step, which saves one round
(`RoundProtocol.not_solves_bilateral_density`).

## Main results

* `Cslib.Communication.RoundProtocol.not_solves_density`: the adversary, for general parameters.
* `Cslib.Communication.RoundProtocol.not_solves_bounded_density`: with explicit parameters.
* `Cslib.Communication.RoundProtocol.not_solves_bilateral_density`: from mutual density limits,
  with one more message.

## References

* [O. Korten, *Top-Down Lower Bounds for All Depths*][Korten2026]
-/

@[expose] public section

namespace Cslib.Communication.RoundProtocol

open Cslib.BitString

variable {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M]

omit [Fintype ι] [DecidableEq ι] [Fintype M] in
/-- If Alice's message is the constant `a` on `X' ⊆ X`, then the continuation after `a` solves the
game on `X' × Y`. -/
private theorem solves_next_of_alice {d : ℕ} {send : (ι → Bool) → M}
    {next : M → KWRoundProtocol ι M d} {X X' Y : Finset (ι → Bool)}
    (hsol : (RoundProtocol.alice send next).Solves DiffersAt X Y) (hsub : X' ⊆ X) {a : M}
    (hsend : ∀ x ∈ X', send x = a) : (next a).Solves DiffersAt X' Y := by
  intro x hx y hy
  have he := hsol x (hsub hx) y hy
  simpa only [run, hsend x hx] using he

omit [Fintype ι] [DecidableEq ι] [Fintype M] in
/-- If Bob's message is the constant `a` on `Y' ⊆ Y`, then the continuation after `a` solves the
game on `X × Y'`. -/
private theorem solves_next_of_bob {d : ℕ} {send : (ι → Bool) → M}
    {next : M → KWRoundProtocol ι M d} {X Y Y' : Finset (ι → Bool)}
    (hsol : (RoundProtocol.bob send next).Solves DiffersAt X Y) (hsub : Y' ⊆ Y) {a : M}
    (hsend : ∀ y ∈ Y', send y = a) : (next a).Solves DiffersAt X Y' := by
  intro x hx y hy
  have he := hsol x hx y (hsub hy)
  simpa only [run, hsend y hy] using he

/-- **Korten's adversary**: a protocol with `d` messages of at most `m` bits does not separate a
density rectangle of rate `p 0` and deficit `k 0` when the parameters grow fast enough,
`1 ≤ k i`, `k (i + 1) ≥ max (194 k i) (2 k i + 2 + m)` and `p (i + 1) ≥ 32768 k i p i`, and the
rates stay at most `1 / 4`. -/
theorem not_solves_density {d : ℕ} (P : KWRoundProtocol ι M d)
    {X Y : Finset (ι → Bool)} {m : ℝ} (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m)
    (k p : ℕ → ℝ)
    (hstep : ∀ i < d, 1 ≤ k i ∧ 194 * k i ≤ k (i + 1) ∧
      2 * k i + 2 + m ≤ k (i + 1) ∧ 32768 * k i * p i ≤ p (i + 1))
    (hcap : ∀ i ≤ d, p i ≤ 1 / 4) (h : DensityRectangle X Y (p 0) (k 0)) :
    ¬ P.Solves DiffersAt X Y := by
  intro hsol
  induction d generalizing X Y k p with
  | zero =>
    cases P with
    | output i => exact h.not_separated (by linarith [hcap 0 (by omega)]) i hsol
  | succ d ih =>
    cases P with
    | output i => exact h.not_separated (by linarith [hcap 0 (by omega)]) i hsol
    | alice send next =>
      have hs := hstep 0 (by omega)
      obtain ⟨a, X', hsub, hsend, hnew⟩ := h.select_left_message send hM
        hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (hcap 1 (by omega))
      exact ih (next a) (fun i => k (i + 1)) (fun i => p (i + 1))
        (fun i hi => hstep (i + 1) (by omega))
        (fun i hi => hcap (i + 1) (by omega)) hnew (solves_next_of_alice hsol hsub hsend)
    | bob send next =>
      have hs := hstep 0 (by omega)
      obtain ⟨a, Y', hsub, hsend, hnew⟩ := h.swap.select_left_message send hM
        hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 (hcap 1 (by omega))
      exact ih (next a) (fun i => k (i + 1)) (fun i => p (i + 1))
        (fun i hi => hstep (i + 1) (by omega))
        (fun i hi => hcap (i + 1) (by omega)) hnew.swap (solves_next_of_bob hsol hsub hsend)

/-- Korten's adversary with explicit parameters: a protocol with `d` messages of at most `m` bits
does not separate a density rectangle of rate `p` and deficit `k ≥ max 1 (m + 1)` when
`(32768 · 194 ^ d k) ^ d p ≤ 1 / 4`. -/
theorem not_solves_bounded_density {d : ℕ} (P : KWRoundProtocol ι M d)
    {X Y : Finset (ι → Bool)} {m k p : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hk : 1 ≤ k) (hmk : m + 1 ≤ k)
    (hbudget : (32768 * (194 : ℝ) ^ d * k) ^ d * p ≤ 1 / 4)
    (h : DensityRectangle X Y p k) : ¬ P.Solves DiffersAt X Y := by
  let C : ℝ := 32768 * (194 : ℝ) ^ d * k
  let K (i : ℕ) : ℝ := (194 : ℝ) ^ i * k
  let B (i : ℕ) : ℝ := C ^ i * p
  have hp : 0 ≤ p := by
    obtain ⟨r, hr, hrp, _⟩ := h.2.2.2.2
    exact hr.le.trans hrp
  have hC : 1 ≤ C := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    dsimp [C]
    nlinarith [mul_le_mul hk hh (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  have hK (i : ℕ) : k ≤ K i := by
    have hh : 1 ≤ (194 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    dsimp [K]
    nlinarith
  have hKsucc (i : ℕ) : K (i + 1) = 194 * K i := by dsimp [K]; rw [pow_succ]; ring
  have hBsucc (i : ℕ) : B (i + 1) = C * B i := by dsimp [B]; rw [pow_succ]; ring
  apply P.not_solves_density hM K B
  · intro i hi
    refine ⟨hk.trans (hK i), (hKsucc i).ge, ?_, ?_⟩
    · rw [hKsucc]
      linarith [hK i]
    · rw [hBsucc]
      have hiC : 32768 * K i ≤ C := by
        have ht := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 194) (Nat.le_of_lt hi))
          (show 0 ≤ k by linarith)
        dsimp [K, C]
        nlinarith
      exact mul_le_mul_of_nonneg_right hiC (mul_nonneg (pow_nonneg (by linarith) _) hp)
  · intro i hi
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hi) hp).trans hbudget
  · simpa only [K, B, pow_zero, one_mul] using h

/-- **Korten's adversary from mutual limits**: if `X` and `Y` are nonempty of deficit at most
`k ≥ 1` and their points are `(p, k)`-limits of each other for a rate `p > 0`, then a protocol with
`d + 1` messages of at most `m ≥ 0` bits does not separate them when
`(32768 · 194 ^ d (m + k)) ^ d p ≤ 1 / 4`. -/
theorem not_solves_bilateral_density {d : ℕ} (P : KWRoundProtocol ι M (d + 1))
    {X Y : Finset (ι → Bool)} {m p k : ℝ}
    (hM : (Fintype.card M : ℝ) ≤ (2 : ℝ) ^ m) (hm : 0 ≤ m) (hk : 1 ≤ k) (hp : 0 < p)
    (hX : X.Nonempty) (hY : Y.Nonempty) (hdX : uniformDeficit X ≤ k) (hdY : uniformDeficit Y ≤ k)
    (hleft : ∀ x ∈ X, IsDensityLimit Y p k x) (hright : ∀ y ∈ Y, IsDensityLimit X p k y)
    (hbudget : (32768 * (194 : ℝ) ^ d * (m + k)) ^ d * p ≤ 1 / 4) :
    ¬ P.Solves DiffersAt X Y := by
  classical
  have hC : 1 ≤ 32768 * (194 : ℝ) ^ d * (m + k) := by
    have hh : 1 ≤ (194 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [mul_nonneg (show 0 ≤ (194 : ℝ) ^ d by positivity) hm]
  have hcap : p ≤ 1 / 4 := by
    have ht := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := d) hC) hp.le
    simp only [one_mul] at ht
    exact ht.trans hbudget
  intro hsol
  cases P with
  | output i =>
    have h : DensityRectangle X Y p k := ⟨hX, hY, hdX, hdY, p, hp, le_rfl, Or.inl hleft⟩
    exact h.not_separated (by linarith) i hsol
  | alice send next =>
    obtain ⟨a, hne, hdef⟩ := exists_uniformDeficit_fiber_le X hX send hM
    let X' := X.filter (fun x => send x = a)
    have hnew : DensityRectangle X' Y p (m + k) := by
      refine ⟨hne, hY, by linarith, by linarith, p, hp, le_rfl, Or.inl ?_⟩
      intro x hx
      exact (hleft x (Finset.mem_filter.mp hx).1).mono_right
        hp.le (by linarith) (by linarith)
    exact (next a).not_solves_bounded_density hM (k := m + k) (by linarith) (by linarith) hbudget
      hnew (solves_next_of_alice hsol (Finset.filter_subset _ X)
        fun x hx => (Finset.mem_filter.mp hx).2)
  | bob send next =>
    obtain ⟨a, hne, hdef⟩ := exists_uniformDeficit_fiber_le Y hY send hM
    let Y' := Y.filter (fun y => send y = a)
    have hnew : DensityRectangle X Y' p (m + k) := by
      refine ⟨hX, hne, by linarith, by linarith, p, hp, le_rfl, Or.inr ?_⟩
      intro y hy
      exact (hright y (Finset.mem_filter.mp hy).1).mono_right
        hp.le (by linarith) (by linarith)
    exact (next a).not_solves_bounded_density hM (k := m + k) (by linarith) (by linarith) hbudget
      hnew (solves_next_of_bob hsol (Finset.filter_subset _ Y)
        fun y hy => (Finset.mem_filter.mp hy).2)

end Cslib.Communication.RoundProtocol
