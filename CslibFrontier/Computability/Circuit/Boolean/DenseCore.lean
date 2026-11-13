/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.HardSet
import Mathlib.Tactic

/-!
# Constant-density cores for every function

[ChukhinKulikovMihajlinSmal2026], Theorem 1.7 (statement printed p. 3, PDF p. 4; proof printed
p. 16, PDF p. 17). For every total `g : {0, 1}ⁿ → {0, 1}` there is a nonempty `S ⊆ {0, 1}ⁿ` such
that, for every `m ≥ 2` and every `X ⊆ Sᵐ` of relative density at least `(1 + 2^{1-m})/3`,
`CC(R_g(X)) ≥ D(g) - O(log n)`. This answers the first test case of [DinurMeir2016],
Conjecture 9.4.

`exists_core` proves it with the explicit loss `coreLoss n = 4 ⌈log₂ n⌉ + ⌈log₂(4n + 4)⌉ + 33`.
`D(g)` is `formulaDepth g`, `CC(R_g(X))` is `ecomplexity (composeKW g) X X`, and the density
condition is `(2^{m-1} + 1) |S|ᵐ ≤ 3 · 2^{m-1} |X|`. One `S` serves every `m` and every `X`.

The proof follows the source.
* `le_ecomplexity_composeKW_of_hard` is the core step. Let `S` be `t`-hard: no formula of depth
  at most `t` agrees with `g` on `2|S|/3` points of `S`. Under the uniform distribution on `S`
  (`density_uniformOfFinset`, `accuracy_uniformOfFinset`), Lemma 6.2 (`exists_accuracy_ge`) turns
  a protocol of depth `d` for `R_g(X)` into a formula of depth `d + 1` with accuracy at least
  `2/3` (`two_thirds_le_half_add`; exactly `2/3` at the threshold). Since hardness is strict,
  `d ≥ t`.
* Lemma 6.3 (`formulaDepth_le_add_of_forall_exists_agree`) bounds `D(g)` by the least `t` for
  which no set is `t`-hard, plus `O(log n)`.

The source's assumptions that `g` is nonconstant and `m ≥ 2` are not needed. The source also notes
that the `O(log n)` loss is tight up to a constant factor (Section 6.5); that tightness statement
is not formalized.

## Main definitions

* `Cslib.Circuits.Boolean.coreLoss`: the additive loss.

## Main results

* `Cslib.Circuits.Boolean.two_thirds_le_half_add`: the threshold arithmetic.
* `Cslib.Circuits.Boolean.le_ecomplexity_composeKW_of_hard`: dense subsets of a hard set are hard.
* `Cslib.Circuits.Boolean.exists_core`: Theorem 1.7.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
* [I. Dinur and O. Meir, *Toward the KRW Composition Conjecture: Cubic Formula Lower Bounds via
  Communication Complexity*][DinurMeir2016]
-/

public section

namespace Cslib.Circuits.Boolean

open Formula Cslib.Communication Cslib.Probability.PMF

variable {n : ℕ}

/-- At relative density `ρ ≥ (1 + 2^{1-m})/3`, the accuracy bound of Lemma 6.2 is at least
`2/3`: `1/2 + (2ᵐ ρ - 1)/(2 (2ᵐ - 1)) ≥ 1/2 + 1/6`, with equality at the threshold. -/
theorem two_thirds_le_half_add {m : ℕ} (hm : 1 ≤ m) {ρ : ℝ}
    (hρ : (1 + 2 / (2 : ℝ) ^ m) / 3 ≤ ρ) :
    2 / 3 ≤ 1 / 2 + (2 ^ m * ρ - 1) / (2 * (2 ^ m - 1)) := by
  have hP : (2 : ℝ) ≤ 2 ^ m := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
  have hpos : (0 : ℝ) < 2 * (2 ^ m - 1) := by linarith
  have h1 : (2 ^ m - 1) / 3 ≤ 2 ^ m * ρ - 1 := by
    have := mul_le_mul_of_nonneg_left hρ (by linarith : (0 : ℝ) ≤ 2 ^ m)
    have e : (2 : ℝ) ^ m * ((1 + 2 / 2 ^ m) / 3) = (2 ^ m + 2) / 3 := by
      field_simp
    linarith
  have h2 : 1 / 6 ≤ (2 ^ m * ρ - 1) / (2 * (2 ^ m - 1)) := by
    rw [le_div_iff₀ hpos]
    linarith
  linarith

/-- **The core step of Theorem 1.7** ([ChukhinKulikovMihajlinSmal2026], proof of Theorem 1.7,
printed p. 16; PDF p. 17). Let `S` be `t`-hard: every formula of `binaryCost` depth at most `t`
agrees with `g` on fewer than `2|S|/3` points of `S`. Let `X ⊆ Sᵐ` have relative density at least
`(1 + 2^{1-m})/3`, stated as `(2^{m-1} + 1) |S|ᵐ ≤ 3 · 2^{m-1} |X|`. Then `CC(R_g(X)) ≥ t`.

A protocol of depth `d` gives, by Lemma 6.2 (`exists_accuracy_ge`) under the uniform distribution
on `S`, a formula of depth at most `d + 1` that agrees with `g` on at least `2|S|/3` points
(`two_thirds_le_half_add`; exactly `2/3` at the threshold). Hardness is strict, so `d + 1 > t`.
The source states it for `m ≥ 2`; the argument also works for `m = 1`. -/
theorem le_ecomplexity_composeKW_of_hard (g : BitString n → Bool) {S : Finset (BitString n)}
    {t : ℕ} (hS : ∀ F : Formula signature n, F.depthWith binaryCost ≤ t →
      3 * (S.filter fun x => F.eval interpretation x = g x).card < 2 * S.card)
    {m : ℕ} (hm : 1 ≤ m) {X : Finset (Fin m → BitString n)} (hXS : ∀ Z ∈ X, ∀ i, Z i ∈ S)
    (hX : (2 ^ (m - 1) + 1) * S.card ^ m ≤ 3 * 2 ^ (m - 1) * X.card) :
    (t : ℕ∞) ≤ Protocol.ecomplexity (composeKW g) (X : Set (Fin m → BitString n))
      (X : Set (Fin m → BitString n)) := by
  have hSne : S.Nonempty := Finset.card_pos.1 (by have := hS (.const false) (by simp); omega)
  have hS0 : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  refine Protocol.le_ecomplexity_iff.2 fun p hp => ?_
  obtain ⟨h, hd, hacc⟩ := exists_accuracy_ge (g := g) (uniformOfFinset S hSne) hp hm
  rw [density_uniformOfFinset hSne hXS, accuracy_uniformOfFinset] at hacc
  -- The relative density is at least `(1 + 2^{1-m})/3`.
  have hρ : (1 + 2 / (2 : ℝ) ^ m) / 3 ≤ X.card / (S.card : ℝ) ^ m := by
    have hpow : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hX' : ((2 : ℝ) ^ (m - 1) + 1) * (S.card : ℝ) ^ m ≤ 3 * 2 ^ (m - 1) * X.card := by
      exact_mod_cast hX
    rw [hpow, le_div_iff₀ (by positivity)]
    have h2 : (0 : ℝ) < 2 ^ (m - 1) := by positivity
    rw [show (1 + 2 / (2 * (2 : ℝ) ^ (m - 1))) / 3 * (S.card : ℝ) ^ m =
      ((2 : ℝ) ^ (m - 1) + 1) * (S.card : ℝ) ^ m / (3 * 2 ^ (m - 1)) by field_simp]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have h23 := (two_thirds_le_half_add hm hρ).trans hacc
  rw [le_div_iff₀ hS0] at h23
  by_contra hlt
  push Not at hlt
  have := hS h (hd.trans (by exact_mod_cast Order.add_one_le_of_lt hlt))
  have h' : (3 * (S.filter fun x => h.eval interpretation x = g x).card : ℝ) <
      2 * S.card := by exact_mod_cast this
  linarith

/-- The additive loss of Theorem 1.7: `4 ⌈log₂ n⌉ + ⌈log₂(4n + 4)⌉ + 33`. It is the `O(log n)` of
Lemma 6.3 (`formulaDepth_le_add_of_forall_exists_agree`) plus one. -/
@[expose] def coreLoss (n : ℕ) : ℕ := 4 * Nat.clog 2 n + Nat.clog 2 (4 * n + 4) + 33

open scoped Classical in
/-- **[ChukhinKulikovMihajlinSmal2026], Theorem 1.7** (printed pp. 3, 16; PDF pp. 4, 17). For
every total `g : {0, 1}ⁿ → {0, 1}` there is one nonempty `S ⊆ {0, 1}ⁿ` such that, for every
`m ≥ 1` and every `X ⊆ Sᵐ` of relative density at least `(1 + 2^{1-m})/3`,
`CC(R_g(X)) ≥ D(g) - coreLoss n`. The density is stated as
`(2^{m-1} + 1) |S|ᵐ ≤ 3 · 2^{m-1} |X|`. The set `S` is chosen before `m` and `X`.

The proof follows the source. Call `S` `t`-hard if no formula of depth at most `t` agrees with `g`
on `2|S|/3` of its points. Let `t₀` be the least `t` for which no set is `t`-hard; it exists,
because a formula for `g` of depth `D(g)` agrees everywhere. Lemma 6.3 at `t₀` gives
`D(g) ≤ t₀ + O(log n)`. If `t₀ = 0`, any `S` works. Otherwise a `(t₀ - 1)`-hard `S` exists, and
`le_ecomplexity_composeKW_of_hard` gives `CC(R_g(X)) ≥ t₀ - 1`.

The source assumes `g` nonconstant and `m ≥ 2`; neither is needed. For constant `g`, `D(g) = 0`.
At `m = 1`, Lemma 6.2 still gives the needed `2/3` at density `2/3`. -/
theorem exists_core (g : BooleanFunction n) :
    ∃ S : Finset (BitString n), S.Nonempty ∧ ∀ m, 1 ≤ m → ∀ X : Finset (Fin m → BitString n),
      (∀ Z ∈ X, ∀ i, Z i ∈ S) → (2 ^ (m - 1) + 1) * S.card ^ m ≤ 3 * 2 ^ (m - 1) * X.card →
        (formulaDepth g : ℕ∞) ≤ Protocol.ecomplexity (composeKW g)
          (X : Set (Fin m → BitString n)) (X : Set (Fin m → BitString n)) + (coreLoss n : ℕ) := by
  let Hard : ℕ → Prop := fun t => ∃ S : Finset (BitString n), ∀ F : Formula signature n,
    F.depthWith binaryCost ≤ t →
      3 * (S.filter fun x => F.eval interpretation x = g x).card < 2 * S.card
  have hex : ∃ t, ¬ Hard t := ⟨formulaDepth g, fun ⟨S, hS⟩ => by
    obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth g
    have := hS F hd.le
    rw [Finset.filter_true_of_mem fun x _ => hF x] at this
    omega⟩
  have h63 (t : ℕ) (ht : ¬ Hard t) :
      formulaDepth g ≤ t + 4 * Nat.clog 2 n + Nat.clog 2 (4 * n + 4) + 32 :=
    formulaDepth_le_add_of_forall_exists_agree g t fun S _ => by
      simp only [Hard, not_exists, not_forall, not_lt] at ht
      obtain ⟨F, hF, h⟩ := ht S
      exact ⟨F, hF, h⟩
  have hD := h63 _ (Nat.find_spec hex)
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · refine ⟨Finset.univ, Finset.univ_nonempty, fun m _ X _ _ => ?_⟩
    calc (formulaDepth g : ℕ∞) ≤ ((coreLoss n : ℕ) : ℕ∞) := by
          exact_mod_cast (show formulaDepth g ≤ coreLoss n by unfold coreLoss; omega)
      _ ≤ _ := le_add_self
  · obtain ⟨S, hS⟩ : Hard (Nat.find hex - 1) := not_not.1 (Nat.find_min hex (by omega))
    refine ⟨S, Finset.card_pos.1 (by have := hS (.const false) (by simp); omega),
      fun m hm X hXS hX => ?_⟩
    calc (formulaDepth g : ℕ∞) ≤ ((Nat.find hex - 1 : ℕ) : ℕ∞) + (coreLoss n : ℕ) := by
          exact_mod_cast (show formulaDepth g ≤ (Nat.find hex - 1) + coreLoss n by
            unfold coreLoss; omega)
      _ ≤ _ := by gcongr; exact le_ecomplexity_composeKW_of_hard g hS hm hXS hX

end Cslib.Circuits.Boolean
