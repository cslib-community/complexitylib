/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.CorrectionAtom
public import Complexity.Probability.PairwiseIndependentHash.AtomChannels
import Complexity.Foundations.Data.Finset.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional rarity of true heavy counts

A nonnegative deterministic row `d` with `a * ∑ y, d y ≤ Cmass` has few entries above
`ρ / 4`. On a finite conditioning slice, suppose every such endpoint other than one specified
endpoint is retained with frequency at most `c * a`. The specified endpoint contributes at
most one, regardless of its own retention probability. Finite Markov then bounds the event
`n ≤ 2 * #{retained y | ρ / 4 < d y}` by `(2 + 8 * c * Cmass) / (n * ρ)`.

The bound allows arbitrary dependence among the endpoint hits. Its affine specialization uses
the actual cross-rate pair count, with broad side `⌈P * α⌉` and an endpoint condition of any
smaller side. Empty conditioning slices have frequency zero; the division-free count theorem
also applies without positivity of the capacity.

This is the conditional true-heavy-count rarity assertion of [OpenAI2026LogSpace, Section 8.4],
the equation labelled `buf-rarity`. The normalized deterministic row and its mass bound are
explicit inputs. Masked mean and noise estimates, post-overflow stability, and the integrated
compression theorem remain separate.

## Main results

* `Finset.card_heavy_mul_le_mass`: derive the deterministic heavy-set bound from row mass.
* `Finset.card_filter_heavyCount_mul_le`: bound the actual exceptional seed count.
* `Finset.card_filter_heavyCount_div_card_le`: the conditional frequency bound, including
  empty conditioning slices.
* `Finset.card_filter_heavyCount_product_div_card_le`: an independent start slice preserves
  the same bound, including an empty start slice.
* `Cslib.Probability.card_affineRetains_heavyCount_div_card_le`: the actual affine sampler at
  broad and narrower endpoint conditions.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 8.4, lemma and equation labelled `buf-rarity`
  (23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

open scoped BigOperators

namespace Finset

variable {Ω V : Type*}

/-- The scaled number of deterministic entries above `ρ / 4` is controlled by the actual
nonnegative row mass. No retained-set or independence hypothesis is used. -/
theorem card_heavy_mul_le_mass (T : Finset V) {d : V → ℝ} {a ρ Cmass : ℝ}
    (ha : 0 ≤ a) (hd : ∀ y ∈ T, 0 ≤ d y) (hmass : a * ∑ y ∈ T, d y ≤ Cmass) :
    a * (#{y ∈ T | ρ / 4 < d y} : ℝ) * ρ ≤ 4 * Cmass := by
  have h := mul_le_mul_of_nonneg_left
    (card_filter_mul_le_sum T (fun y => ρ / 4 < d y) d hd
      (fun _ _ hy => hy.le)) ha
  nlinarith [h.trans hmass]

/-- **True-heavy-count rarity as a finite count.** Only off-endpoint conditional pair counts
are required. The one specified endpoint costs at most one retained entry per draw.
The capacity may be zero, and the seed slice may be empty. -/
theorem card_filter_heavyCount_mul_le (X : Ω → V → Prop) [∀ σ y, Decidable (X σ y)]
    (S : Finset Ω) (T : Finset V) (x : V) {d : V → ℝ} {a c ρ Cmass : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hd : ∀ y ∈ T, 0 ≤ d y) (hmass : a * ∑ y ∈ T, d y ≤ Cmass)
    (hpair : ∀ y ∈ T, ρ / 4 < d y → y ≠ x →
      (#{σ ∈ S | X σ y} : ℝ) ≤ c * a * #S) (n : ℕ) :
    (#{σ ∈ S | n ≤ 2 * #{y ∈ T | X σ y ∧ ρ / 4 < d y}} : ℝ) * n * ρ ≤
      #S * (2 + 8 * c * Cmass) := by
  classical
  let D : Finset V := {y ∈ T | ρ / 4 < d y}
  have hD := card_heavy_mul_le_mass T (ρ := ρ) ha hd hmass
  have hmarkov := card_filter_le_card_filter_mul_le X S D x (mul_nonneg hc ha)
    (fun y hy hyx => hpair y (mem_filter.mp hy).1 (mem_filter.mp hy).2 hyx) ((n + 1) / 2)
  have hevent : {σ ∈ S | (n + 1) / 2 ≤ #{y ∈ D | X σ y}} =
      {σ ∈ S | n ≤ 2 * #{y ∈ T | X σ y ∧ ρ / 4 < d y}} := by
    apply filter_congr
    intro σ _
    have hset : {y ∈ D | X σ y} = {y ∈ T | X σ y ∧ ρ / 4 < d y} := by
      ext y
      simp [D, and_left_comm, and_comm]
    rw [hset]
    omega
  rw [hevent] at hmarkov
  have hn : (n : ℝ) ≤ 2 * ((n + 1) / 2 : ℕ) := by
    exact_mod_cast (show n ≤ 2 * ((n + 1) / 2) by omega)
  have hfirst :
      (#{σ ∈ S | n ≤ 2 * #{y ∈ T | X σ y ∧ ρ / 4 < d y}} : ℝ) * n ≤
        2 * (#S : ℝ) * (1 + c * a * #D) := by
    nlinarith [mul_le_mul_of_nonneg_left hn
      (show (0 : ℝ) ≤ #{σ ∈ S | n ≤ 2 * #{y ∈ T | X σ y ∧ ρ / 4 < d y}} by positivity)]
  have hmassD : c * a * (#D : ℝ) * ρ ≤ 4 * c * Cmass := by
    dsimp only [D]
    nlinarith [mul_le_mul_of_nonneg_left hD hc]
  calc
    _ ≤ (2 * (#S : ℝ) * (1 + c * a * #D)) * ρ :=
      mul_le_mul_of_nonneg_right hfirst hρ.le
    _ ≤ #S * (2 + 8 * c * Cmass) := by
      have hfactor : 2 * (1 + c * a * (#D : ℝ)) * ρ ≤ 2 + 8 * c * Cmass := by
        nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hfactor (Nat.cast_nonneg #S : (0 : ℝ) ≤ #S)]

/-- The conditional true-heavy-count frequency is small. An empty conditioning slice has
frequency zero, so no nonemptiness hypothesis is needed. -/
theorem card_filter_heavyCount_div_card_le (X : Ω → V → Prop) [∀ σ y, Decidable (X σ y)]
    (S : Finset Ω) (T : Finset V) (x : V) {d : V → ℝ} {a c ρ Cmass : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hd : ∀ y ∈ T, 0 ≤ d y) (hmass : a * ∑ y ∈ T, d y ≤ Cmass)
    (hpair : ∀ y ∈ T, ρ / 4 < d y → y ≠ x →
      (#{σ ∈ S | X σ y} : ℝ) ≤ c * a * #S) {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ S | n ≤ 2 * #{y ∈ T | X σ y ∧ ρ / 4 < d y}} : ℝ) / #S ≤
      (2 + 8 * c * Cmass) / ((n : ℝ) * ρ) := by
  have hC : 0 ≤ Cmass := (mul_nonneg ha (sum_nonneg hd)).trans hmass
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp only [filter_empty, card_empty, Nat.cast_zero, zero_div]
    positivity
  have hnρ : (0 : ℝ) < n * ρ := mul_pos (by exact_mod_cast hn) hρ
  have hSpos : (0 : ℝ) < #S := by exact_mod_cast hS.card_pos
  rw [div_le_div_iff₀ hSpos hnρ]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    card_filter_heavyCount_mul_le X S T x ha hc hρ hρ1 hd hmass hpair n

/-- Conditioning independently on a start seed does not increase the heavy-count bound.
The product slice and retained count are explicit; either conditioning slice may be empty. -/
theorem card_filter_heavyCount_product_div_card_le {Γ : Type*}
    (X : Ω → V → Prop) [∀ σ y, Decidable (X σ y)]
    (R : Finset Γ) (S : Finset Ω) (T : Finset V) (x : V) {d : V → ℝ} {a c ρ Cmass : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hd : ∀ y ∈ T, 0 ≤ d y) (hmass : a * ∑ y ∈ T, d y ≤ Cmass)
    (hpair : ∀ y ∈ T, ρ / 4 < d y → y ≠ x →
      (#{σ ∈ S | X σ y} : ℝ) ≤ c * a * #S) {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ R ×ˢ S | n ≤ 2 * #{y ∈ T | X σ.2 y ∧ ρ / 4 < d y}} : ℝ) / #(R ×ˢ S) ≤
      (2 + 8 * c * Cmass) / ((n : ℝ) * ρ) := by
  classical
  refine card_filter_heavyCount_div_card_le (fun (σ : Γ × Ω) y => X σ.2 y)
    (R ×ˢ S) T x ha hc hρ hρ1 hd hmass ?_ hn
  intro y hy hdy hyx
  have hset : {σ ∈ R ×ˢ S | X σ.2 y} = R ×ˢ {σ ∈ S | X σ y} := by
    ext σ
    simp [and_assoc]
  rw [hset, card_product, card_product, Nat.cast_mul, Nat.cast_mul]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left (hpair y hy hdy hyx) (Nat.cast_nonneg #R : (0 : ℝ) ≤ #R)

end Finset

namespace Cslib.Probability

open Finset

variable {V : Type*} {P H : ℕ} [Fact P.Prime]

/-- **Conditional true-heavy-count rarity for affine channels.** The broad rate parameter is
`α ^ H`, and the actual cross-rate pair estimate supplies `c = 2 ^ H`. The conditioning side
may equal the broad side or be narrower, including zero; no conditional error independence is
assumed. -/
theorem card_affineRetains_heavyCount_div_card_le (T : Finset V) {ident : V → ZMod P}
    (hident : Function.Injective ident) {α : ℝ} (hPα : 1 ≤ P * α) (hα1 : α ≤ 1)
    {Lt : ℕ} (hLt : Lt ≤ ⌈P * α⌉₊) (x : V) {d : V → ℝ} {ρ Cmass : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hd : ∀ y ∈ T, 0 ≤ d y)
    (hmass : α ^ H * ∑ y ∈ T, d y ≤ Cmass) {n : ℕ} (hn : 0 < n) :
    (#{σ ∈ ({σ | affineRetains P H Lt σ (ident x)} :
        Finset (Matrix (Fin H) (Fin 1) (ZMod P) × (Fin H → ZMod P))) |
      n ≤ 2 * #{y ∈ T | affineRetains P H ⌈P * α⌉₊ σ (ident y) ∧ ρ / 4 < d y}} : ℝ) /
        #{σ | affineRetains P H Lt σ (ident x)} ≤
      (2 + 8 * (2 : ℝ) ^ H * Cmass) / ((n : ℝ) * ρ) := by
  have hα : 0 < α := by
    by_contra h
    have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hP (not_lt.mp h)]
  obtain ⟨hL, -, -, -, -⟩ := affineRetains_rates (H := H) hPα hα1
  refine card_filter_heavyCount_div_card_le
    (fun σ y => affineRetains P H ⌈P * α⌉₊ σ (ident y))
    {σ | affineRetains P H Lt σ (ident x)} T x (pow_nonneg hα.le H)
    (by positivity) hρ hρ1 hd hmass ?_ hn
  intro y _ _ hyx
  simpa only [filter_filter] using
    card_affineRetains_and_affineRetains_le hident hPα hα1 (hLt.trans hL) hyx

end Cslib.Probability
