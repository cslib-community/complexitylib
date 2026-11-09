/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Moore
public import Mathlib.RingTheory.Trace.Defs
import CslibFrontier.Foundations.FieldTheory.Finite.ReducedMonomial
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Products of Moore determinants of independent subspaces

Let `F` be a finite field with `2 ^ n` elements in which every proper subfield has at most
`2 ^ s` elements. Given `𝔽₂`-subspaces `Yᵢ` of `F` of dimensions `dᵢ > s` and integers
`2 ≤ kᵢ < dᵢ` with `∑ᵢ (dᵢ - kᵢ) ≥ n + 1 - maxᵢ dᵢ`, every nonzero `𝔽₂`-linear functional
`z ↦ Tr (μ z)` is nonzero on some product `∏ᵢ Δ(uᵢ)` of Moore determinants of families
`uᵢ : Fin kᵢ → Yᵢ`. This is the algebraic heart of the disperser for independent affine sources
of Ben-Sasson and Kopparty [BenSassonKopparty2012, Theorem 6.1], with the hypothesis that no
`Yᵢ` lies in a multiple of a proper subfield replaced by `dᵢ > s`; for a field of prime degree
`s = 1`.

The proof follows [BenSassonKopparty2012]. Parametrize `Yᵢ` by its image-subspace polynomial
`Qᵢ`; then `w ↦ Tr (μ ∏ᵢ Δ(Qᵢ ∘ wᵢ))` is a reduced polynomial function whose coefficient at
`∏ᵢ ∏ₗ wᵢₗ ^ 2 ^ τᵢₗ` is `∑_ρ μ ^ 2 ^ ρ ∏ᵢ per(Mᵢ[τᵢ - ρ]) ^ 2 ^ ρ`, where
`Mᵢ[τ] = (aᵢ (τ l - m) ^ 2 ^ m)`. Using the zero pattern of the coefficients `aᵢ`
(`Cslib.CoeffPattern`) we choose `τ` so that every `Mᵢ[τᵢ]` is triangular with
nonzero diagonal while for every rotation `ρ ≠ 0` some `Mᵢ[τᵢ - ρ]` has a zero row
[BenSassonKopparty2012, Claims 6.2 and 6.3]. That coefficient is then `μ ∏ᵢ per(Mᵢ[τᵢ]) ≠ 0`,
and a reduced polynomial with a nonzero coefficient is a nonzero function
(`FiniteField.eq_zero_of_forall_sum_mul_prod_pow_eq_zero`).

## Main results

* `Cslib.AffineDisperser.exists_trace_mul_prod_det_mooreMatrix_ne_zero`: the theorem above.

## References

* [E. Ben-Sasson, S. Kopparty, *Affine dispersers from subspace polynomials*][BenSassonKopparty2012]
-/

@[expose] public section

namespace Cslib.AffineDisperser

open Module

variable {F : Type*} [Field F]

/-! ### Choosing the monomial -/

section Choice

variable {n : ℕ} [NeZero n] {d k : ℕ} {a : ZMod n → F}

/-- `τ` makes the matrix `(a (τ l - m) ^ 2 ^ m)_{l, m}` upper triangular with nonzero
diagonal. -/
private def IsTriangular (a : ZMod n → F) (τ : Fin k → ZMod n) : Prop :=
  (∀ l : Fin k, a (τ l - (l : ℕ)) ≠ 0) ∧ ∀ l m : Fin k, m < l → a (τ l - (m : ℕ)) = 0

/-- The rotation of `τ` by `ρ` gives the matrix `(a (τ l - ρ - m) ^ 2 ^ m)` a zero row. -/
private def Kills (a : ZMod n → F) (τ : Fin k → ZMod n) (ρ : ZMod n) : Prop :=
  ∃ l : Fin k, ∀ m : Fin k, a (τ l - ρ - (m : ℕ)) = 0

private theorem coeffPattern_neg_eq_zero (hp : CoeffPattern n d a) {x : ℕ} (hx1 : 1 ≤ x)
    (hxd : x < d) : a (-(x : ZMod n)) = 0 := by
  have hdn := hp.le
  have : -(x : ZMod n) = ((n - d + (d - x) : ℕ) : ZMod n) := by
    rw [show n - d + (d - x) = n - x by omega, Nat.cast_sub (by omega : x ≤ n), ZMod.natCast_self,
      zero_sub]
  rw [this]
  exact hp.canonical _ (by omega) (by omega)

/-- A row `τ l` kills the `d - k` rotations just above it. -/
private theorem kills_of_eq_add (hp : CoeffPattern n d a) (hkd : k < d) {τ : Fin k → ZMod n}
    (l : Fin k) {c : ℕ} (hc1 : 1 ≤ c) (hc : c ≤ d - k) {ρ : ZMod n} (hρ : ρ = τ l + c) :
    Kills a τ ρ := by
  refine ⟨l, fun m => ?_⟩
  have : τ l - ρ - ((m : ℕ) : ZMod n) = -((c + m : ℕ) : ZMod n) := by
    rw [hρ]
    push_cast
    ring
  rw [this]
  exact coeffPattern_neg_eq_zero hp (by omega) (by have := m.2; omega)

/-- The choice `(b, n - d + 1, …, n - d + k - 1)` [BenSassonKopparty2012, Claim 6.2, first
case]. -/
private theorem exists_tau_one (hp : CoeffPattern n d a) (hk : 2 ≤ k) (hkd : k < d) {b : ℕ}
    (hb : a b ≠ 0) :
    ∃ τ : Fin k → ZMod n, IsTriangular a τ ∧
      (∀ c, 1 ≤ c → c ≤ d - k → Kills a τ ((b + c : ℕ) : ZMod n)) ∧
      ∀ ρ : ℕ, n - d + 2 ≤ ρ → ρ < n → Kills a τ ρ := by
  have hdn := hp.le
  refine ⟨fun l => if (l : ℕ) = 0 then (b : ZMod n) else ((n - d + l : ℕ) : ZMod n),
    ⟨fun l => ?_, fun l m hml => ?_⟩, fun c hc1 hc => ?_, fun ρ hρ1 hρn => ?_⟩
  · by_cases hl : (l : ℕ) = 0
    · simp only [hl, ↓reduceIte, Nat.cast_zero, sub_zero]
      exact hb
    · simp only [hl, ↓reduceIte]
      rw [← Nat.cast_sub (by omega), show n - d + l - l = n - d by omega]
      exact hp.lead
  · have hml' : (m : ℕ) < l := hml
    have hl : (l : ℕ) ≠ 0 := by omega
    simp only [hl, ↓reduceIte]
    rw [← Nat.cast_sub (by omega), show n - d + l - m = n - d + (l - m) by omega]
    exact hp.canonical _ (by omega) (by have := l.2; omega)
  · refine kills_of_eq_add hp hkd ⟨0, by omega⟩ hc1 hc ?_
    simp
  · refine kills_of_eq_add hp hkd ⟨min (k - 1) (ρ - (n - d) - 1), by omega⟩
      (c := ρ - (n - d) - min (k - 1) (ρ - (n - d) - 1)) (by omega) (by omega) ?_
    have hl0 : min (k - 1) (ρ - (n - d) - 1) ≠ 0 := by omega
    simp only [hl0, ↓reduceIte]
    rw [← Nat.cast_add, show n - d + min (k - 1) (ρ - (n - d) - 1) +
      (ρ - (n - d) - min (k - 1) (ρ - (n - d) - 1)) = ρ by omega]

/-- **The choice of the rows of one block** [BenSassonKopparty2012, Claims 6.2 and 6.3]: for every
`ℓ ≤ n - d` some triangular `τ` kills the rotations `ℓ + 1, …, ℓ + (d - k)`. -/
private theorem exists_tau_window (hp : CoeffPattern n d a) (hk : 2 ≤ k) (hkd : k < d) {ℓ : ℕ}
    (hℓ : ℓ ≤ n - d) :
    ∃ τ : Fin k → ZMod n, IsTriangular a τ ∧
      ∀ ρ : ℕ, ℓ + 1 ≤ ρ → ρ ≤ ℓ + (d - k) → Kills a τ ρ := by
  classical
  have hdn := hp.le
  by_cases hℓ0 : a ℓ ≠ 0
  · obtain ⟨τ, hτ, hkill, -⟩ := exists_tau_one hp hk hkd hℓ0
    refine ⟨τ, hτ, fun ρ hρ1 hρ2 => ?_⟩
    have := hkill (ρ - ℓ) (by omega) (by omega)
    rwa [show ℓ + (ρ - ℓ) = ρ by omega] at this
  push Not at hℓ0
  have hℓlt : ℓ < n - d := lt_of_le_of_ne hℓ fun h => hp.lead (h ▸ hℓ0)
  -- `jh`: the last nonzero coefficient below `ℓ`
  set jh := Nat.findGreatest (fun j => a (j : ZMod n) ≠ 0) ℓ with hjh
  have hjh_ne : a jh ≠ 0 :=
    Nat.findGreatest_spec (P := fun j => a (j : ZMod n) ≠ 0) (Nat.zero_le ℓ)
      (by simpa using hp.zero_ne)
  have hjh_lt : jh < ℓ := lt_of_le_of_ne (Nat.findGreatest_le ℓ) fun h => hjh_ne (h ▸ hℓ0)
  have hjh_max : ∀ j, jh < j → j ≤ ℓ → a j = 0 := fun j h1 h2 => by
    by_contra h
    exact absurd (Nat.le_findGreatest h2 h) (not_le.2 h1)
  -- `js`: the first nonzero coefficient above `ℓ`
  have hex : ∃ j, ℓ < j ∧ a (j : ZMod n) ≠ 0 := ⟨n - d, hℓlt, hp.lead⟩
  set js := Nat.find hex with hjs
  have hjs_spec : ℓ < js ∧ a js ≠ 0 := Nat.find_spec hex
  have hjs_le : js ≤ n - d := Nat.find_min' hex ⟨hℓlt, hp.lead⟩
  have hgap : ∀ j, jh < j → j < js → a j = 0 := fun j h1 h2 => by
    rcases le_or_gt j ℓ with h | h
    · exact hjh_max j h1 h
    · by_contra hne
      exact Nat.find_min hex h2 ⟨h, hne⟩
  -- the gap is shorter than `d - 1` [BenSassonKopparty2012, Lemma 3.10]
  have hjs_bound : js ≤ jh + d - 1 := by
    obtain ⟨c, hc, hne⟩ := hp.gap (jh + 1) (by omega) (by omega)
    by_contra hcon
    exact hne (hgap _ (by omega) (by omega))
  set s := min (js - jh - 1) (k - 1) with hs
  refine ⟨fun l => if (l : ℕ) = 0 then (js : ZMod n)
      else if (l : ℕ) ≤ s then ((jh + l : ℕ) : ZMod n) else ((n - d + l : ℕ) : ZMod n),
    ⟨fun l => ?_, fun l m hml => ?_⟩, fun ρ hρ1 hρ2 => ?_⟩
  · by_cases hl0 : (l : ℕ) = 0
    · simp only [hl0, ↓reduceIte, Nat.cast_zero, sub_zero]
      exact hjs_spec.2
    · by_cases hls : (l : ℕ) ≤ s
      · simp only [hl0, hls, ↓reduceIte]
        rw [← Nat.cast_sub (by omega), show jh + l - l = jh by omega]
        exact hjh_ne
      · simp only [hl0, hls, ↓reduceIte]
        rw [← Nat.cast_sub (by omega), show n - d + l - l = n - d by omega]
        exact hp.lead
  · have hml' : (m : ℕ) < l := hml
    have hl0 : (l : ℕ) ≠ 0 := by omega
    by_cases hls : (l : ℕ) ≤ s
    · simp only [hl0, hls, ↓reduceIte]
      rw [← Nat.cast_sub (by omega)]
      exact hgap _ (by omega) (by omega)
    · simp only [hl0, hls, ↓reduceIte]
      rw [← Nat.cast_sub (by omega), show n - d + l - m = n - d + (l - m) by omega]
      exact hp.canonical _ (by omega) (by have := l.2; omega)
  · by_cases hρs : ρ ≤ jh + s + (d - k)
    · -- a row placed in the gap
      refine kills_of_eq_add hp hkd ⟨min s (ρ - jh - 1), by omega⟩
        (c := ρ - jh - min s (ρ - jh - 1)) (by omega) (by omega) ?_
      have hl0 : min s (ρ - jh - 1) ≠ 0 := by omega
      have hls : min s (ρ - jh - 1) ≤ s := min_le_left _ _
      simp only [hl0, hls, ↓reduceIte]
      rw [← Nat.cast_add, show jh + min s (ρ - jh - 1) + (ρ - jh - min s (ρ - jh - 1)) = ρ by
        omega]
    · -- the row `js`
      refine kills_of_eq_add hp hkd ⟨0, by omega⟩ (c := ρ - js) (by omega) (by omega) ?_
      simp only [↓reduceIte]
      rw [← Nat.cast_add, show js + (ρ - js) = ρ by omega]

/-- **The choice of the monomial** [BenSassonKopparty2012, Claims 6.2 and 6.3]: given coefficient
patterns of dimensions `dᵢ`, the largest at `i₁`, and `2 ≤ kᵢ < dᵢ` with
`n < d_{i₁} + ∑ᵢ (dᵢ - kᵢ)`, there are triangular `τᵢ` such that every nonzero rotation is killed
by some block. -/
private theorem exists_tau {ι : Type*} [Fintype ι] (a : ι → ZMod n → F) (d k : ι → ℕ)
    (hp : ∀ i, CoeffPattern n (d i) (a i)) (hk : ∀ i, 2 ≤ k i) (hkd : ∀ i, k i < d i)
    (i₁ : ι) (hmax : ∀ i, d i ≤ d i₁) (hsum : n < d i₁ + ∑ i, (d i - k i)) :
    ∃ τ : (i : ι) → Fin (k i) → ZMod n, (∀ i, IsTriangular (a i) (τ i)) ∧
      ∀ ρ : ZMod n, ρ ≠ 0 → ∃ i, Kills (a i) (τ i) ρ := by
  classical
  let T := Fintype.card ι
  let e : Fin T ≃ ι := (Fintype.equivFin ι).symm
  let δ : ι → ℕ := fun i => d i - k i
  let δ' : ℕ → ℕ := fun q => if h : q < T then (if e ⟨q, h⟩ ≠ i₁ then δ (e ⟨q, h⟩) else 0) else 0
  let ℓ : ℕ → ℕ := fun p => δ i₁ + ∑ q ∈ Finset.range p, δ' q
  have hℓsucc : ∀ p, ℓ (p + 1) = ℓ p + δ' p := fun p => by
    simp only [ℓ, Finset.sum_range_succ, add_assoc]
  have hℓT : ℓ T = ∑ i, δ i := by
    simp only [ℓ]
    rw [← Fin.sum_univ_eq_sum_range δ' T]
    have : ∀ q : Fin T, δ' q = if e q ≠ i₁ then δ (e q) else 0 := fun q => by simp [δ', q.2]
    simp_rw [this]
    rw [Equiv.sum_comp e (fun i => if i ≠ i₁ then δ i else 0), ← Finset.sum_filter,
      Finset.filter_ne', Finset.add_sum_erase _ _ (Finset.mem_univ i₁)]
  have hblock : ∀ i, ∃ τ : Fin (k i) → ZMod n, IsTriangular (a i) τ ∧
      (i = i₁ → ∀ ρ : ℕ, 1 ≤ ρ → ρ < n → (ρ ≤ δ i₁ ∨ n - d i₁ + 2 ≤ ρ) → Kills (a i) τ ρ) ∧
      (i ≠ i₁ → ℓ (e.symm i) ≤ n - d i₁ → ∀ ρ : ℕ, ℓ (e.symm i) + 1 ≤ ρ →
        ρ ≤ ℓ (e.symm i) + δ i → Kills (a i) τ ρ) := by
    intro i
    have h0 : a i ((0 : ℕ) : ZMod n) ≠ 0 := by simpa using (hp i).zero_ne
    by_cases hi : i = i₁
    · subst hi
      obtain ⟨τ, hτ, h1, h2⟩ := exists_tau_one (hp i) (hk i) (hkd i) h0
      refine ⟨τ, hτ, fun _ ρ hρ1 hρn hρ => ?_, fun h => absurd rfl h⟩
      rcases hρ with hρ | hρ
      · have := h1 ρ hρ1 hρ
        rwa [zero_add] at this
      · exact h2 ρ hρ hρn
    · by_cases hℓ : ℓ (e.symm i) ≤ n - d i₁
      · obtain ⟨τ, hτ, hkill⟩ := exists_tau_window (hp i) (hk i) (hkd i)
          (ℓ := ℓ (e.symm i)) (by have := hmax i; omega)
        exact ⟨τ, hτ, fun h => absurd h hi, fun _ _ => hkill⟩
      · obtain ⟨τ, hτ, -, -⟩ := exists_tau_one (hp i) (hk i) (hkd i) h0
        exact ⟨τ, hτ, fun h => absurd h hi, fun _ h => absurd h hℓ⟩
  choose τ hτ hτ₁ hτw using hblock
  refine ⟨τ, hτ, fun ρ hρ => ?_⟩
  have hρr : ρ = (ρ.val : ZMod n) := (ZMod.natCast_zmod_val ρ).symm
  have hr1 : 1 ≤ ρ.val := Nat.pos_of_ne_zero ((ZMod.val_ne_zero ρ).2 hρ)
  have hrn : ρ.val < n := ZMod.val_lt ρ
  rw [hρr]
  by_cases hr : ρ.val ≤ δ i₁ ∨ n - d i₁ + 2 ≤ ρ.val
  · exact ⟨i₁, hτ₁ i₁ rfl ρ.val hr1 hrn hr⟩
  push Not at hr
  obtain ⟨hrδ, hrd⟩ := hr
  have hdn := (hp i₁).le
  have hex : ∃ p, ρ.val ≤ ℓ (p + 1) := ⟨T, by rw [hℓsucc, hℓT]; simp only [δ] at hsum ⊢; omega⟩
  set p := Nat.find hex
  have hp1 : ρ.val ≤ ℓ (p + 1) := Nat.find_spec hex
  have hp0 : ℓ p < ρ.val := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h]
      simp only [ℓ, Finset.range_zero, Finset.sum_empty, add_zero]
      exact hrδ
    · have := Nat.find_min hex (show p - 1 < p by omega)
      rw [show p - 1 + 1 = p by omega] at this
      omega
  have hδ' : 0 < δ' p := by
    rw [hℓsucc] at hp1
    omega
  have hpT : p < T := by
    by_contra h
    simp [δ', h] at hδ'
  have hi : e ⟨p, hpT⟩ ≠ i₁ := by
    intro h
    simp [δ', hpT, h] at hδ'
  have hδ'i : δ' p = δ (e ⟨p, hpT⟩) := by simp [δ', hpT, hi]
  have hsymm : ((e.symm (e ⟨p, hpT⟩) : Fin T) : ℕ) = p := by rw [e.symm_apply_apply]
  refine ⟨e ⟨p, hpT⟩, hτw _ hi (by rw [hsymm]; omega) ρ.val (by rw [hsymm]; omega) ?_⟩
  rw [hsymm]
  rw [hℓsucc, hδ'i] at hp1
  exact hp1

omit [NeZero n] in
private theorem permanent_eq_zero_of_kills {τ : Fin k → ZMod n} {ρ : ZMod n} (h : Kills a τ ρ) :
    (Matrix.of fun l m : Fin k => a (τ l - ρ - (m : ℕ)) ^ 2 ^ (m : ℕ)).permanent = 0 := by
  obtain ⟨l, hl⟩ := h
  refine Finset.sum_eq_zero fun σ _ => Finset.prod_eq_zero (Finset.mem_univ (σ.symm l)) ?_
  simp [hl]

omit [NeZero n] in
private theorem permanent_ne_zero_of_isTriangular [CharP F 2] {τ : Fin k → ZMod n}
    (h : IsTriangular a τ) :
    (Matrix.of fun l m : Fin k => a (τ l - (m : ℕ)) ^ 2 ^ (m : ℕ)).permanent ≠ 0 := by
  rw [← Matrix.det_eq_permanent_of_charTwo, Matrix.det_of_isUpperTriangular]
  · exact Finset.prod_ne_zero_iff.2 fun l _ => pow_ne_zero _ (h.1 l)
  · intro l m hml
    simp [h.2 l m hml]

end Choice

variable [Finite F] [Algebra (ZMod 2) F]

/-- **Moore products of independent sources** (after [BenSassonKopparty2012, Theorem 6.1]): in a
field with `2 ^ n` elements whose proper subfields have at most `2 ^ s` elements, let `Yᵢ` be
subspaces of dimensions `dᵢ > s`, and `2 ≤ kᵢ < dᵢ` with `n < d_{i₀} + ∑ᵢ (dᵢ - kᵢ)` for some
`i₀`. Then for every `μ ≠ 0` there are families `uᵢ : Fin kᵢ → Yᵢ` whose Moore determinants
satisfy `Tr (μ ∏ᵢ Δ(uᵢ)) ≠ 0`.

By `sum_cube_pow_eq_det_mooreMatrix`, `Δ(uᵢ)` is the `kᵢ`-th finite difference of
`x ↦ x ^ (2 ^ kᵢ - 1)` in the directions `uᵢ`. So the conclusion says that
`(xᵢ) ↦ Tr (μ ∏ᵢ xᵢ ^ (2 ^ kᵢ - 1))` has a nonzero mixed finite difference along the `Yᵢ`, the
form in which the paper's theorem is used. The threshold `n < maxᵢ dᵢ + ∑ᵢ (dᵢ - kᵢ)` is one
better than the paper's `∑ᵢ (dᵢ - kᵢ) > n - maxᵢ dᵢ + 1`. -/
theorem exists_trace_mul_prod_det_mooreMatrix_ne_zero {ι : Type*} [Fintype ι] {n s : ℕ}
    (hn : finrank (ZMod 2) F = n) (hs : ∀ K : Subfield F, K ≠ ⊤ → Nat.card K ≤ 2 ^ s)
    (Y : ι → Submodule (ZMod 2) F) (k : ι → ℕ) (hk : ∀ i, 2 ≤ k i)
    (hkY : ∀ i, k i < finrank (ZMod 2) (Y i)) (hsY : ∀ i, s < finrank (ZMod 2) (Y i)) (i₀ : ι)
    (hsum : n < finrank (ZMod 2) (Y i₀) + ∑ i, (finrank (ZMod 2) (Y i) - k i))
    {μ : F} (hμ : μ ≠ 0) :
    ∃ u : (i : ι) → Fin (k i) → F, (∀ i l, u i l ∈ Y i) ∧
      Algebra.trace (ZMod 2) F (μ * ∏ i, (mooreMatrix (u i)).det) ≠ 0 := by
  classical
  cases nonempty_fintype F
  have hn0 : 0 < n := hn ▸ Module.finrank_pos
  have : NeZero n := ⟨hn0.ne'⟩
  have hcard : Fintype.card F = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := F), ZMod.card, hn]
  -- the coefficient vectors of image-subspace polynomials of the `Y i`
  have hpat : ∀ i, ∃ a : ZMod n → F, (∀ x, linearizedEval a x ∈ Y i) ∧
      CoeffPattern n (finrank (ZMod 2) (Y i)) a :=
    fun i => exists_coeffPattern hn hs (Y i) (hsY i)
  choose a ha hpa using hpat
  -- the monomial that will have a nonzero coefficient
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun i => finrank (ZMod 2) (Y i))
    ⟨i₀, Finset.mem_univ _⟩
  obtain ⟨τ, hτ, hkill⟩ := exists_tau a (fun i => finrank (ZMod 2) (Y i)) k hpa hk hkY i₁
    (fun i => hi₁ i (Finset.mem_univ i))
    (lt_of_lt_of_le hsum (by have := hi₁ i₀ (Finset.mem_univ _); omega))
  -- the coefficients of `w ↦ Tr (μ ∏ᵢ Δ(Qᵢ ∘ wᵢ))`
  let P : (i : ι) → (Fin (k i) → ZMod n) → F := fun i σ =>
    (Matrix.of fun l m : Fin (k i) => a i (σ l - (m : ℕ)) ^ 2 ^ (m : ℕ)).permanent
  let C : ((i : ι) → Fin (k i) → ZMod n) → F := fun τ' =>
    ∑ ρ ∈ Finset.range n, μ ^ 2 ^ ρ * ∏ i, P i (fun l => τ' i l - (ρ : ZMod n)) ^ 2 ^ ρ
  have hexp : ∀ w : (i : ι) → Fin (k i) → F,
      algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F
        (μ * ∏ i, (mooreMatrix fun l => linearizedEval (a i) (w i l)).det)) =
      ∑ τ' : (i : ι) → Fin (k i) → ZMod n, C τ' * ∏ i, ∏ l, w i l ^ 2 ^ (τ' i l).val := by
    intro w
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hn, Nat.card_zmod]
    simp_rw [Matrix.det_eq_permanent_of_charTwo, permanent_mooreMatrix_linearizedEval hn]
    have hrot : ∀ (ρ : ℕ) (i : ι),
        (∑ σ : Fin (k i) → ZMod n, P i σ * ∏ l, w i l ^ 2 ^ (σ l).val) ^ 2 ^ ρ =
          ∑ σ : Fin (k i) → ZMod n,
            P i (fun l => σ l - (ρ : ZMod n)) ^ 2 ^ ρ * ∏ l, w i l ^ 2 ^ (σ l).val := by
      intro ρ i
      rw [sum_pow_char_pow]
      refine Fintype.sum_equiv (Equiv.addRight fun _ => (ρ : ZMod n)) _ _ fun σ => ?_
      simp only [Equiv.coe_addRight, Pi.add_apply, add_sub_cancel_right, mul_pow]
      congr 1
      rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun l _ => ?_
      rw [← pow_mul, ← pow_add, pow_two_pow_mod hn (w i l) ((σ l).val + ρ), ZMod.val_add,
        ZMod.val_natCast, Nat.add_mod_mod]
    simp only [P] at hrot
    simp_rw [mul_pow, ← Finset.prod_pow, hrot, Fintype.prod_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ' _ => ?_
    simp only [C, P, Finset.sum_mul, Finset.prod_mul_distrib, mul_assoc]
  by_contra hcon
  push Not at hcon
  -- every coefficient vanishes, since reduced monomials are independent
  have hC : ∀ τ', C τ' = 0 := by
    intro τ'
    refine FiniteField.eq_zero_of_forall_sum_mul_prod_pow_eq_zero (σ := Σ i, Fin (k i))
      (fun τ' v => 2 ^ (τ' v.1 v.2).val) ?_ ?_ C (fun x => ?_) τ'
    · intro τ₁ τ₂ h
      funext i l
      exact ZMod.val_injective _ (Nat.pow_right_injective le_rfl (congrFun h ⟨i, l⟩))
    · intro τ' v
      rw [hcard]
      exact Nat.pow_lt_pow_right (by norm_num) (ZMod.val_lt _)
    · have h0 : Algebra.trace (ZMod 2) F
          (μ * ∏ i, (mooreMatrix fun l => linearizedEval (a i) (x ⟨i, l⟩)).det) = 0 :=
        hcon (fun i l => linearizedEval (a i) (x ⟨i, l⟩)) fun i l => ha i _
      have := hexp fun i l => x ⟨i, l⟩
      beta_reduce at this
      rw [h0, map_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun τ' _ => by rw [Fintype.prod_sigma]
  -- but the coefficient of the chosen monomial is `μ ∏ᵢ per(Mᵢ[τᵢ]) ≠ 0`
  refine (show C τ ≠ 0 from ?_) (hC τ)
  simp only [C]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 hn0)]
  · simp only [pow_zero, pow_one, Nat.cast_zero, sub_zero]
    exact mul_ne_zero hμ
      (Finset.prod_ne_zero_iff.2 fun i _ => permanent_ne_zero_of_isTriangular (hτ i))
  · intro ρ hρ hρ0
    have hρ' : (ρ : ZMod n) ≠ 0 := by
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_cast_of_lt (Finset.mem_range.1 hρ), ZMod.val_zero] at this
      exact hρ0 this
    obtain ⟨i, hi⟩ := hkill _ hρ'
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ i) ?_)
    rw [show P i (fun l => τ i l - (ρ : ZMod n)) = 0 from permanent_eq_zero_of_kills hi]
    exact zero_pow (pow_ne_zero _ two_ne_zero)

end Cslib.AffineDisperser
