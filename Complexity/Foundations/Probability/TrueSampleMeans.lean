/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.CorrectionAtom
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# True means of sampled atom products

The direct and correction--dense sample terms of [OpenAI2026LogSpace, Lemma 7.1] use a broad
terminal conditioning slice and a possibly narrower usage slice. Their exact retention-density
ratio changes the conditioning. In a product, a second ratio cancels the sampling of the
intermediate vertex.

These results use the concrete `Matrix.denseAtom` and `Matrix.correctionAtom` definitions.
The true dense atom is a function of the terminal seed alone, while the correction atom uses
the source and intermediate seeds. Thus the required factorization follows from finite product
averages. No independence of estimated factors, estimator correctness, or machine certificate
is assumed.

The formulas are the raw direct and product terms before division by the parent first-channel
scale. Copy projections, detector and reward assembly, and the conditional-walk schedule remain
separate parts of the estimator construction.

## Main results

* `Finset.expect_mul_dens_div_of_subset`: change a finite conditioning slice by its exact
  density ratio, for a function supported on the smaller slice.
* `Matrix.expect_denseAtom_change_usage`: the importance-weighted dense-atom mean.
* `Matrix.expect_correctionAtom_unconditioned`: the correction-atom mean when the intermediate
  seed is unconditioned.
* `Matrix.expect_correctionAtom_mul_denseAtom`: the exact correction--dense product mean on
  the source/terminal conditioning slice, with the intermediate seed averaged over all draws.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 7.2, Lemma 7.1, September 23, 2026 revision `7ef5c0cc` (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Finset

/-- A function supported on `T ⊆ S` has the same mean after restricting to `T` and multiplying
its mean on `S` by the exact ratio of the two uniform densities. -/
theorem expect_mul_dens_div_of_subset {Ω : Type*} [Fintype Ω] {S T : Finset Ω}
    (hTS : T ⊆ S) (hT : T.Nonempty) (v : Ω → ℝ)
    (hv : ∀ σ ∈ S, σ ∉ T → v σ = 0) :
    𝔼 σ ∈ S, ((dens S : ℝ) / dens T) * v σ = 𝔼 σ ∈ T, v σ := by
  have hS : S.Nonempty := hT.mono hTS
  have hScard : (#S : ℝ) ≠ 0 := by exact_mod_cast hS.card_ne_zero
  have hTcard : (#T : ℝ) ≠ 0 := by exact_mod_cast hT.card_ne_zero
  have hΩcard : (Fintype.card Ω : ℝ) ≠ 0 := by
    have hpos : 0 < Fintype.card Ω := hT.card_pos.trans_le (card_le_univ T)
    exact_mod_cast hpos.ne'
  have hsum : ∑ σ ∈ S, v σ = ∑ σ ∈ T, v σ := (sum_subset hTS hv).symm
  rw [← mul_expect, expect_eq_sum_div_card, expect_eq_sum_div_card, hsum,
    dens_eq_card_div_card, dens_eq_card_div_card]
  push_cast
  field_simp

/-- Averaging a supported function over the full seed space multiplies its conditional mean
by the exact retention density. -/
theorem expect_eq_dens_mul_expect_of_eq_zero {Ω : Type*} [Fintype Ω] (S : Finset Ω)
    (v : Ω → ℝ) (hv : ∀ σ ∉ S, v σ = 0) :
    𝔼 σ, v σ = (dens S : ℝ) * 𝔼 σ ∈ S, v σ := by
  classical
  have hmask : ∀ σ, v σ = if σ ∈ S then v σ else 0 := by
    intro σ
    split_ifs with hσ
    · rfl
    · exact hv σ hσ
  calc
    𝔼 σ, v σ = 𝔼 σ, if σ ∈ S then v σ else 0 :=
      expect_congr rfl fun σ _ => hmask σ
    _ = _ := by simpa only [NNRat.smul_def] using Fintype.expect_ite_mem S v

end Finset

namespace Matrix

variable {V κ : Type*} [Fintype V] [Fintype κ]

/-- The actual dense atom, averaged on a broader terminal slice, has the correct mean after
the exact density-ratio importance correction [OpenAI2026LogSpace, Lemma 7.1]. The sufficient
gate hypotheses are those of `Matrix.expect_denseAtom`. -/
theorem expect_denseAtom_change_usage {Y Ya Yt : κ → V → Prop}
    [∀ t v, Decidable (Y t v)] [∀ t v, Decidable (Ya t v)] [∀ t v, Decidable (Yt t v)]
    {k h ρ : ℝ → ℝ} {K : ℕ} {b : ℝ} {G : Matrix V V ℝ} {x y : V}
    (hYt : ∀ t, Yt t y → Ya t y) (hS : ({t | Yt t y} : Finset κ).Nonempty)
    (hkh : ∀ d, k d ≠ 0 → h d = 1) (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ r, r ≤ η → ρ r = 1) (hb : 0 < b) (hG0 : ∀ w, 0 ≤ G x w)
    {M : ℝ} (hGM : ∑ w, G x w ≤ M) {c : ℝ} (hc : 0 ≤ c) (hK : 2 * (1 + c * M / η) ≤ K)
    (hpair : ∀ w, w ≠ y → (#{t | Yt t y ∧ Y t w} : ℝ) ≤ c * b * #{t | Yt t y}) :
    𝔼 t ∈ ({t | Ya t y} : Finset κ),
        b * ((dens {t | Ya t y} : ℝ) / dens {t | Yt t y}) * denseAtom Y Yt k h ρ K b G t x y =
      b * k (G x y / b) := by
  have hsub : ({t | Yt t y} : Finset κ) ⊆ ({t | Ya t y} : Finset κ) := by
    intro t ht
    exact mem_filter.mpr ⟨mem_univ _, hYt t (by simpa using ht)⟩
  have hchange := expect_mul_dens_div_of_subset hsub hS (fun t => denseAtom Y Yt k h ρ K b G t x y)
    (fun t _ ht => by
      have hnot : ¬ Yt t y := by simpa using ht
      simp [denseAtom, hnot])
  simp only [mul_assoc]
  rw [← mul_expect, hchange,
    expect_denseAtom hS hkh hρ0 hρ1 hη hρη hb hG0 hGM hc hK hpair]

variable {ι : Type*} [Fintype ι]

/-- The intermediate seed may be left unconditioned: the actual correction atom then has
mean `π_f * Q (G x z / f) * g₀ z`, where `π_f` is the exact density of its usage slice.
Its built-in mask supplies the support condition. -/
theorem expect_correctionAtom_unconditioned {I : ℝ → ℝ → ℝ} {τ Q h ρ : ℝ → ℝ}
    {K Kc : ℕ} {f : ℝ} {G : Matrix V V ℝ} {g₀ : V → ℝ}
    {X : ι → V → Prop} {Z Zt : κ → V → Prop}
    [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    {x z : V} (hSx : ({s | X s x} : Finset ι).Nonempty)
    (hSz : ({t | Zt t z} : Finset κ).Nonempty) (hQh : ∀ v, Q v ≠ 0 → h v = 1)
    (hρ0 : ∀ r, 0 ≤ ρ r) (hρ1 : ∀ r, ρ r ≤ 1) {η : ℝ} (hη : 0 < η)
    (hρη : ∀ r, r ≤ η → ρ r = 1) (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1)
    {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀) (hττ : ∀ r, r ≤ τ₀ → τ r = 1) {e : ℝ}
    (hI : ∀ v r, v ≤ e → I v r = 0) (hf : 0 < f) (hG0 : ∀ w, 0 ≤ G x w)
    {M : ℝ} (hGM : ∑ w, G x w ≤ M) {c : ℝ} (hc : 0 ≤ c)
    (hK : 4 * (1 + c * M / η) ≤ K)
    (hpairZ : ∀ w, w ≠ z → (#{t | Zt t z ∧ Z t w} : ℝ) ≤ c * f * #{t | Zt t z})
    {p : ℝ} (hp : 0 ≤ p)
    (hpairX : ∀ w, w ≠ x → (#{s | X s x ∧ X s w} : ℝ) ≤ p * #{s | X s x})
    {B : ℝ} (hB : g₀ z ≠ 0 → p * #({w | e < G w z / f} : Finset V) ≤ B)
    (hKc : 4 * (1 + B) ≤ Kc) :
    𝔼 d ∈ ({s | X s x} : Finset ι) ×ˢ (univ : Finset κ),
        correctionAtom I τ K Kc f G X Z Zt Q h ρ g₀ d x z =
      (dens {t | Zt t z} : ℝ) * (Q (G x z / f) * g₀ z) := by
  have hmean := expect_correctionAtom hSx hSz hQh hρ0 hρ1 hη hρη hτ0 hτ1 hτ₀ hττ hI
    hf hG0 hGM hc hK hpairZ hp hpairX hB hKc
  have hsupport : ∀ s, (𝔼 t, correctionAtom I τ K Kc f G X Z Zt Q h ρ g₀ (s, t) x z) =
      (dens {t | Zt t z} : ℝ) * 𝔼 t ∈ ({t | Zt t z} : Finset κ),
        correctionAtom I τ K Kc f G X Z Zt Q h ρ g₀ (s, t) x z := by
    intro s
    refine expect_eq_dens_mul_expect_of_eq_zero _ _ fun t ht => ?_
    have hnot : ¬ Zt t z := by simpa using ht
    simp [correctionAtom, hnot]
  rw [expect_product]
  simp_rw [hsupport]
  rw [← mul_expect, ← expect_product', hmean]

/-- **The true correction--dense product mean** [OpenAI2026LogSpace, Lemma 7.1]. Average the
actual sample over the source slice, all intermediate seeds, and the broad terminal slice.
The terminal density ratio changes to the usage slice; `f / πf` cancels intermediate sampling.
The result is the product of the two deterministic entries in their original matrix units.

The uniform intermediate hit probability is stated as the actual density equality `hZπ`.
All atom normalizations follow from their gate and pair-count hypotheses; none are postulated
as mean identities. The true right atom only uses the third seed coordinate. -/
theorem expect_correctionAtom_mul_denseAtom {υ : Type*} [Fintype υ]
    {I : ℝ → ℝ → ℝ} {τ Q hF ρF k hB ρB : ℝ → ℝ} {KF Kc KB : ℕ}
    {f b πf : ℝ} {G H : Matrix V V ℝ} {g₀ : V → ℝ}
    {X : ι → V → Prop} {Z Zt : κ → V → Prop} {Y Ya Yt : υ → V → Prop}
    [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    [∀ t v, Decidable (Y t v)] [∀ t v, Decidable (Ya t v)] [∀ t v, Decidable (Yt t v)]
    {x y : V} (hSx : ({s | X s x} : Finset ι).Nonempty)
    (hZπ : ∀ z, (dens {t | Zt t z} : ℝ) = πf) (hπf : 0 < πf)
    (hYt : ∀ t, Yt t y → Ya t y) (hSy : ({t | Yt t y} : Finset υ).Nonempty)
    (hQh : ∀ v, Q v ≠ 0 → hF v = 1) (hρF0 : ∀ r, 0 ≤ ρF r) (hρF1 : ∀ r, ρF r ≤ 1)
    {ηF : ℝ} (hηF : 0 < ηF) (hρFη : ∀ r, r ≤ ηF → ρF r = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) {τ₀ : ℝ} (hτ₀ : 0 ≤ τ₀)
    (hττ : ∀ r, r ≤ τ₀ → τ r = 1) {e : ℝ} (hI : ∀ v r, v ≤ e → I v r = 0)
    (hf : 0 < f) (hG0 : ∀ w, 0 ≤ G x w) {MF : ℝ} (hGM : ∑ w, G x w ≤ MF)
    {cF : ℝ} (hcF : 0 ≤ cF) (hKF : 4 * (1 + cF * MF / ηF) ≤ KF)
    (hpairZ : ∀ z w, w ≠ z → (#{t | Zt t z ∧ Z t w} : ℝ) ≤ cF * f * #{t | Zt t z})
    {p : ℝ} (hp : 0 ≤ p)
    (hpairX : ∀ w, w ≠ x → (#{s | X s x ∧ X s w} : ℝ) ≤ p * #{s | X s x})
    {R : ℝ} (hR : ∀ z, g₀ z ≠ 0 → p * #({w | e < G w z / f} : Finset V) ≤ R)
    (hKc : 4 * (1 + R) ≤ Kc)
    (hkh : ∀ v, k v ≠ 0 → hB v = 1) (hρB0 : ∀ r, 0 ≤ ρB r) (hρB1 : ∀ r, ρB r ≤ 1)
    {ηB : ℝ} (hηB : 0 < ηB) (hρBη : ∀ r, r ≤ ηB → ρB r = 1) (hb : 0 < b)
    (hH0 : ∀ z w, 0 ≤ H z w) {MB : ℝ} (hHM : ∀ z, ∑ w, H z w ≤ MB)
    {cB : ℝ} (hcB : 0 ≤ cB) (hKB : 2 * (1 + cB * MB / ηB) ≤ KB)
    (hpairY : ∀ w, w ≠ y → (#{t | Yt t y ∧ Y t w} : ℝ) ≤ cB * b * #{t | Yt t y}) :
    𝔼 d ∈ (({s | X s x} : Finset ι) ×ˢ (univ : Finset κ)) ×ˢ ({t | Ya t y} : Finset υ),
        b * ((dens {t | Ya t y} : ℝ) / dens {t | Yt t y}) * (f / πf) *
          ∑ z, correctionAtom I τ KF Kc f G X Z Zt Q hF ρF g₀ d.1 x z *
            denseAtom Y Yt k hB ρB KB b H d.2 z y =
      ∑ z, (f * Q (G x z / f) * g₀ z) * (b * k (H z y / b)) := by
  have hSz : ∀ z, ({t | Zt t z} : Finset κ).Nonempty := by
    intro z
    have hpos : (0 : ℝ) < dens {t | Zt t z} := by rw [hZπ]; exact hπf
    refine dens_ne_zero.mp ?_
    intro hz
    rw [hz] at hpos
    norm_num at hpos
  have hleft : ∀ z, (𝔼 d ∈ ({s | X s x} : Finset ι) ×ˢ (univ : Finset κ),
      correctionAtom I τ KF Kc f G X Z Zt Q hF ρF g₀ d x z) =
      πf * (Q (G x z / f) * g₀ z) := by
    intro z
    rw [expect_correctionAtom_unconditioned hSx (hSz z) hQh hρF0 hρF1 hηF hρFη hτ0 hτ1
      hτ₀ hττ hI hf hG0 hGM hcF hKF (hpairZ z) hp hpairX (hR z) hKc, hZπ]
  have hright : ∀ z, (𝔼 t ∈ ({t | Ya t y} : Finset υ),
      b * ((dens {t | Ya t y} : ℝ) / dens {t | Yt t y}) *
        denseAtom Y Yt k hB ρB KB b H t z y) = b * k (H z y / b) := by
    intro z
    exact expect_denseAtom_change_usage hYt hSy hkh hρB0 hρB1 hηB hρBη hb (hH0 z)
      (hHM z) hcB hKB hpairY
  simp_rw [mul_sum]
  rw [expect_sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [expect_product]
  calc
    _ = 𝔼 l ∈ ({s | X s x} : Finset ι) ×ˢ (univ : Finset κ),
        𝔼 t ∈ ({t | Ya t y} : Finset υ),
          ((f / πf) * correctionAtom I τ KF Kc f G X Z Zt Q hF ρF g₀ l x z) *
            (b * ((dens {t | Ya t y} : ℝ) / dens {t | Yt t y}) *
              denseAtom Y Yt k hB ρB KB b H t z y) := by
      refine expect_congr rfl fun l _ => expect_congr rfl fun t _ => ?_
      ring
    _ = _ := by
      rw [← expect_mul_expect, ← mul_expect, hleft z, hright z]
      field_simp

end Matrix
