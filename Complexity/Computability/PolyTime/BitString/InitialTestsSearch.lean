/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.GenericRAM.Native.IndexFold
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Foundations.Combinatorics.Expander.TannerCode
public import Complexity.Foundations.Data.BitString.ParityTestBounds
import Complexity.Computability.GenericRAM.Native.BooleanFold
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Foundations.Data.BitString.InitialTests
import Complexity.Foundations.Data.BitString.Parity.DotProduct
import Complexity.Foundations.Data.List.OfFn
import Complexity.Foundations.Data.Nat.CeilDiv
import Complexity.Probability.SmallBias.Random
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Sequential initial-test search and shortened Tanner check matrices

Deterministic sequential search and shortened Tanner parity-check construction from
[OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1, Lemma 6.1 (pp. 40–42),
giving the executable counterpart to `Cslib.BitString.exists_initialTests`. Given `n, B ≥ 1` and
`m ≤ B * n`, `initialTestsRows m B` constructs a binary matrix `A^(0)` on `m` columns with at most
`3 * n` rows of weight at most `initialRowWeightBound B m` whose `GF(2)` kernel excludes every
nonzero vector of weight below `m / greedyRowListLength B m`, in `exp(poly(B, log(m + 2)))` bit
operations and `poly(n, m, B)` working space via `Cslib.GenericRAM.IndexFold.run`.

## Main definitions

* `dG`, `ellG`, `qG`, `cG`, `hDist`, `biasDen`: Lemma 6.1 parameter schedule.
* `checkSmallBiasShifts`, `checkLocalCodeDistance`, `findSmallBiasShifts`, `findLocalCheckMatrix`:
  streaming `IndexFold.run` checkers and sequential searchers.
* `buildShortenedTannerRows`, `initialTestsRows`: shortened Tanner check-matrix assembly.

## Main results

* `checkSmallBiasShifts_eq_true_iff`, `checkLocalCodeDistance_eq_true_iff`,
  `isSmallBias_findSmallBiasShifts`, `weight_le_of_findLocalCheckMatrix`: checker/searcher specs.
* `initialTestsRows_spec`, `map_ofList_initialTestsRows_spec`, `initialTestsRows_computableInO`,
  `initialTestsRows_computableInO_nmb`: unconditional Lemma 6.1 correctness and `ComputableInO`.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1, Lemma 6.1
* [R. M. Tanner, *A recursive approach to low complexity codes*][Tanner1981]
* [J. Naor, M. Naor, *Small-bias probability spaces*][NaorNaor1993]
-/

@[expose] public section

namespace Cslib.Complexity.InitialTestsSearch
open Finset Cslib.BitString Cslib.GenericRAM Cslib.Probability.PMF Turing.MultiTapeTM

/-! ### Lemma 6.1 integer parameter schedule -/
private abbrev mu (m : ℕ) : ℕ := Nat.log 2 m + 1

/-- Cayley degree `d_G = min(m, D₀)` (`D₀ = initialRowWeightBound B m`) of [OpenAI2026ETH],
Lemma 6.1. -/
def dG (m B : ℕ) : ℕ := min m (initialRowWeightBound B m)
/-- Cube dimension `ℓ_G = ⌈log₂ ⌈m / d_G⌉⌉` of [OpenAI2026ETH], Lemma 6.1 (`0` if `d_G = 0`). -/
def ellG (m B : ℕ) : ℕ := Nat.clog 2 ((m + dG m B - 1) / dG m B)
/-- Vertex-side size `q_G = 2 ^ ℓ_G` of the double cover in [OpenAI2026ETH], Lemma 6.1. -/
def qG (m B : ℕ) : ℕ := 2 ^ ellG m B
/-- Local parity-check row count `c_G = ⌈d_G / (8 B)⌉` of [OpenAI2026ETH], Lemma 6.1
(`0` if `B = 0`). -/
def cG (m B : ℕ) : ℕ := (dG m B + 8 * B - 1) / (8 * B)
/-- Maximum rejected weight `h = ⌈d_G / (100 B μ)⌉ - 1` for the local code of Lemma 6.1
(`0` if `d_G = 0` or `B = 0`). -/
def hDist (m B : ℕ) : ℕ :=
  (dG m B + 100 * B * (Nat.log 2 m + 1) - 1) / (100 * B * (Nat.log 2 m + 1)) - 1
/-- Reciprocal bias denominator `200 B μ` (`ε = 1 / biasDen m B`) in [OpenAI2026ETH], (6.2). -/
def biasDen (m B : ℕ) : ℕ := 200 * B * (Nat.log 2 m + 1)

theorem dG_pos {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : 0 < dG m B := by
  unfold dG initialRowWeightBound
  have : 0 < 320000 * B ^ 2 * (Nat.log 2 m + 1) ^ 3 := by positivity
  omega
theorem le_qG_mul_dG {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : m ≤ qG m B * dG m B := by
  have hd := dG_pos hm hB
  exact (Nat.le_ceilDiv_mul hd).trans (by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide : 1 < 2) _))
theorem qG_mul_dG_lt_two_mul {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : qG m B * dG m B < 2 * m := by
  have hd := dG_pos hm hB; set k := (m + dG m B - 1) / dG m B
  rcases le_or_gt k 1 with hk | hk
  · have h0 : ellG m B = 0 := Nat.clog_of_right_le_one hk 2
    have : dG m B ≤ m := Nat.min_le_left _ _; simp only [qG, h0, pow_zero, one_mul]; omega
  · have hell_pos : 0 < Nat.clog 2 k :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by simpa only [pow_zero] using hk)
    have hpow_lt : 2 ^ (Nat.clog 2 k - 1) < k :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (by omega)
    have hmul_le : dG m B * k ≤ m + dG m B - 1 := Nat.mul_div_le (m + dG m B - 1) (dG m B)
    have : m + dG m B - 1 + 1 = m + dG m B := by omega
    have : qG m B = 2 ^ (Nat.clog 2 k - 1) * 2 := by
      change 2 ^ Nat.clog 2 k = _; rw [← Nat.pow_succ]; exact congrArg (2 ^ ·) (by omega)
    nlinarith
theorem qG_lt_two_mul {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) : qG m B < 2 * m := by
  have := dG_pos hm hB; nlinarith [qG_mul_dG_lt_two_mul hm hB]
theorem qG_le_two_mul_add_one (m B : ℕ) : qG m B ≤ 2 * m + 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm; · simp only [qG, ellG, dG, Nat.zero_min]; decide
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [qG, ellG, show dG m 0 = 0 by
      simp only [dG, initialRowWeightBound, sq, mul_zero, zero_mul, Nat.min_zero],
      Nat.div_zero]; change 1 ≤ 2 * m + 1; omega
  have := qG_lt_two_mul hm hB; omega
private theorem dG_eq_of_ellG_pos {m B : ℕ} (hpos : 0 < ellG m B) :
    dG m B = initialRowWeightBound B m := by
  by_contra hne; have hd : dG m B = m := Nat.min_eq_left (by unfold dG at hne; omega)
  rcases Nat.eq_zero_or_pos m with rfl | hm; · rw [ellG, hd] at hpos; exact absurd hpos (by decide)
  have hdiv : (m + m - 1) / m ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hm).2 (by omega))
  have h0 : ellG m B = 0 := by unfold ellG; rw [hd]; exact Nat.clog_of_right_le_one hdiv 2
  omega
private theorem ellG_le_mu (m B : ℕ) : ellG m B ≤ mu m := by
  rw [ellG, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]
  rcases Nat.eq_zero_or_pos m with rfl | hm; · simp [dG]
  rcases Nat.eq_zero_or_pos (dG m B) with hd | hd; · simp [hd]
  refine ((Nat.div_le_iff_le_mul_add_pred hd).2 ?_).trans
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m).le
  have := Nat.le_mul_of_pos_left m hd; omega
private theorem cG_le_dG_add_one (m B : ℕ) : cG m B ≤ dG m B + 1 := by
  rcases Nat.eq_zero_or_pos B with rfl | hB; · simp [cG]
  exact Nat.le_of_lt_succ
    ((Nat.div_lt_iff_lt_mul (by omega : 0 < 8 * B)).2 ((Nat.sub_le _ _).trans_lt (by nlinarith)))
theorem two_mul_qG_mul_cG_le_three_mul {n m B : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hB : 1 ≤ B)
    (hmn : m ≤ B * n) : 2 * qG m B * cG m B ≤ 3 * n := by
  have hmul : 8 * B * cG m B ≤ dG m B + 8 * B - 1 := Nat.mul_div_le _ (8 * B)
  rcases Nat.eq_zero_or_pos (ellG m B) with h0 | hpos
  · have hq : qG m B = 1 := by simp only [qG, h0, pow_zero]
    have h1 := le_qG_mul_dG hm hB; have h2 : dG m B ≤ m := Nat.min_le_left _ _
    have hd : dG m B = m := by rw [hq, one_mul] at h1; omega
    rw [hq, mul_one]; rw [hd] at hmul; have : m + 8 * B - 1 + 1 = m + 8 * B := by omega
    nlinarith
  · have h8_le_dG : 8 * B ≤ dG m B := by
      rw [dG_eq_of_ellG_pos hpos, initialRowWeightBound]; have : B ≤ B ^ 2 := by nlinarith
      have : 0 < (Nat.log 2 m + 1) ^ 3 := by positivity
      nlinarith
    have : dG m B + 8 * B - 1 + 1 = dG m B + 8 * B := by omega
    nlinarith [qG_mul_dG_lt_two_mul hm hB]
private theorem hDist_succ_eq {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) :
    hDist m B + 1 = (dG m B + 100 * B * mu m - 1) / (100 * B * mu m) := by
  have hd : 1 ≤ dG m B := dG_pos hm hB; have hM : 0 < 100 * B * mu m := by positivity
  have hle : 1 * (100 * B * mu m) ≤ dG m B + 100 * B * mu m - 1 := by omega
  have := (Nat.le_div_iff_mul_le hM).2 hle; unfold hDist; dsimp only [mu] at *; omega
theorem dG_le_hDist_succ_mul {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) :
    dG m B ≤ (hDist m B + 1) * (100 * B * (Nat.log 2 m + 1)) := by
  change dG m B ≤ (hDist m B + 1) * (100 * B * mu m)
  rw [hDist_succ_eq hm hB, ← Nat.ceilDiv_eq_add_pred_div]
  exact Nat.le_ceilDiv_mul (by positivity)

private abbrev encMB : ℕ × ℕ ↪ List Bool := encPair encUnary encUnary
section
variable {α : Type} {ei : α ↪ List Bool} {m B : α → ℕ}
  (hm : ComputableInPolyTime m ei encUnary) (hB : ComputableInPolyTime B ei encUnary)
include hm hB
@[fun_prop] theorem greedyRowListLength_polyTime :
    ComputableInPolyTime (fun a => greedyRowListLength (B a) (m a)) ei encUnary := by
  unfold greedyRowListLength; fun_prop
@[fun_prop] theorem initialRowWeightBound_polyTime :
    ComputableInPolyTime (fun a => initialRowWeightBound (B a) (m a)) ei encUnary := by
  unfold initialRowWeightBound; fun_prop
@[fun_prop] theorem dG_polyTime :
    ComputableInPolyTime (fun a => dG (m a) (B a)) ei encUnary := by
  unfold dG initialRowWeightBound; fun_prop
@[fun_prop] theorem ellG_polyTime :
    ComputableInPolyTime (fun a => ellG (m a) (B a)) ei encUnary := by
  unfold ellG dG initialRowWeightBound; fun_prop
@[fun_prop] theorem qG_polyTime :
    ComputableInPolyTime (fun a => qG (m a) (B a)) ei encUnary := by
  unfold qG ellG dG initialRowWeightBound; fun_prop
@[fun_prop] theorem cG_polyTime :
    ComputableInPolyTime (fun a => cG (m a) (B a)) ei encUnary := by
  unfold cG dG initialRowWeightBound; fun_prop
@[fun_prop] theorem hDist_polyTime :
    ComputableInPolyTime (fun a => hDist (m a) (B a)) ei encUnary := by
  unfold hDist dG initialRowWeightBound; fun_prop
@[fun_prop] theorem biasDen_polyTime :
    ComputableInPolyTime (fun a => biasDen (m a) (B a)) ei encUnary := by
  unfold biasDen; fun_prop
end

/-! ### Private streaming `IndexFold` and matrix-search combinators -/

private abbrev pOf := @PolyBounded.of_polynomiallyBounded
private theorem add_mul_le_mul_add (A K B : ℕ) (hK : 1 ≤ K) : A + K * B ≤ K * (A + B) := by
  rw [Nat.mul_add]; exact Nat.add_le_add_right (Nat.le_mul_of_pos_left A hK) _
private theorem polyBounded_unary {α : Type} {ei : α ↪ List Bool} {f : α → ℕ}
    (hf : ComputableInPolyTime f ei encUnary) : PolyBounded (fun a => (ei a).length) f := by
  simpa only [Function.comp_apply, encUnary_apply, List.length_replicate] using
    hf.polyBounded_length
private theorem equivFin_symm_eq_zero_iff {width : ℕ} (k : Fin (2 ^ width)) :
    (equivFin width).symm k = 0 ↔ k.val = 0 := by
  rw [Equiv.symm_apply_eq, Fin.ext_iff, show (0 : BitString width) = fun _ => false from rfl,
    val_equivFin_false]
private theorem length_encList_listRows (count width : ℕ) (word : List Bool) :
    (encList encBits (listRows count width word)).length = count * (2 * width + 1) := by
  simp [length_encList, listRows, Function.comp_def]
private def HasKPolyCert {α β : Type} (f : α → β) (ei : α ↪ List Bool) (eo : β ↪ List Bool)
    (K : α → ℕ) : Prop :=
  ∃ (c : NativeCertificate f ei eo) (pT pS : ℕ → ℕ), Cslib.PolynomiallyBounded pT ∧
    Cslib.PolynomiallyBounded pS ∧ (∀ a, c.time a ≤ K a * pT (ei a).length) ∧
    (∀ a, c.space a ≤ pS (ei a).length)
private theorem HasKPolyCert.of_polyTime {α β : Type} {f : α → β} {ei : α ↪ List Bool}
    {eo : β ↪ List Bool} (hf : ComputableInPolyTime f ei eo) :
    HasKPolyCert f ei eo (fun _ => 1) := by
  obtain ⟨⟨pT, hpT, hT⟩, ⟨pS, hpS, hS⟩⟩ := NativeCertificate.ofPolyTime_isPolynomial hf
  exact ⟨.ofPolyTime hf, pT, pS, hpT, hpS, fun a => by simpa only [one_mul] using hT a, hS⟩
private theorem HasKPolyCert.congr {α β : Type} {f g : α → β} {ei : α ↪ List Bool}
    {eo : β ↪ List Bool} {K : α → ℕ} (hf : HasKPolyCert f ei eo K) (h : ∀ a, f a = g a) :
    HasKPolyCert g ei eo K := by
  obtain ⟨c, pT, pS, hpT, hpS, hT, hS⟩ := hf; exact ⟨c.congr h, pT, pS, hpT, hpS, hT, hS⟩
private theorem HasKPolyCert.snd {α β γ : Type} {f : α → β × γ} {ei : α ↪ List Bool}
    {em : β ↪ List Bool} {eo : γ ↪ List Bool} {K : α → ℕ}
    (hf : HasKPolyCert f ei (encPair em eo) K) : HasKPolyCert (fun a => (f a).2) ei eo K := by
  obtain ⟨c, pT, pS, hpT, hpS, hT, hS⟩ := hf; exact ⟨c.snd, pT, pS, hpT, hpS, hT, hS⟩
private theorem HasKPolyCert.mono_const {α β : Type} {f : α → β} {ei : α ↪ List Bool}
    {eo : β ↪ List Bool} {K₁ K₂ : α → ℕ} (C : ℕ) (hK : ∀ a, K₁ a ≤ C * K₂ a)
    (hf : HasKPolyCert f ei eo K₁) : HasKPolyCert f ei eo K₂ := by
  obtain ⟨c, pT, pS, hpT, hpS, hT, hS⟩ := hf
  refine ⟨c, fun n => C * pT n, pS, by fun_prop, hpS, fun a => ?_, hS⟩
  exact (hT a).trans ((Nat.mul_le_mul_right _ (hK a)).trans (by ring_nf; exact le_rfl))
private theorem HasKPolyCert.comp_polyPre {α β γ : Type} {g : α → β} {f : β → γ}
    {ei : α ↪ List Bool} {em : β ↪ List Bool} {eo : γ ↪ List Bool} {K : β → ℕ}
    (hK : ∀ b, 1 ≤ K b) (hg : ComputableInPolyTime g ei em) (hf : HasKPolyCert f em eo K) :
    HasKPolyCert (fun a => f (g a)) ei eo (fun a => K (g a)) := by
  obtain ⟨cf, pTf, pSf, hpTf, hpSf, hTf, hSf⟩ := hf; let cg := NativeCertificate.ofPolyTime hg
  have hcg := NativeCertificate.ofPolyTime_isPolynomial hg; have hgLen := hg.polyBounded_length
  obtain ⟨pT, hpT, hT⟩ := hcg.1.add ((pOf id hpTf).comp hgLen)
  obtain ⟨pS, hpS, hS⟩ := (hcg.2.add ((pOf id hpSf).comp hgLen)).mono (u := (cf.comp cg).space)
    fun a => Nat.add_le_add_left (hSf (g a)) _
  refine ⟨cf.comp cg, pT, pS, hpT, hpS, fun a => ?_, hS⟩
  exact (Nat.add_le_add_left (hTf (g a)) (cg.time a)).trans
    ((add_mul_le_mul_add _ _ _ (hK (g a))).trans (Nat.mul_le_mul_left _ (hT a)))
private theorem HasKPolyCert.polyPost {α β γ : Type} {g : α → β} {f : β → γ}
    {ei : α ↪ List Bool} {em : β ↪ List Bool} {eo : γ ↪ List Bool} {K : α → ℕ}
    (hK : ∀ a, 1 ≤ K a) (hg : HasKPolyCert g ei em K) (hf : ComputableInPolyTime f em eo) :
    HasKPolyCert (fun a => f (g a)) ei eo K := by
  let len (a : α) : ℕ := (ei a).length
  obtain ⟨cg, pTg, pSg, hpTg, hpSg, hTg, hSg⟩ := hg; obtain ⟨k, _, hl⟩ := cg.computes
  have hgLen : PolyBounded len (fun a => (em (g a)).length) :=
    ((PolyBounded.const k).mul ((pOf len hpSg).add (.const 1))).mono
      fun a => (hl a).trans (Nat.mul_le_mul_left k (Nat.add_le_add_right (hSg a) 1))
  let cf := NativeCertificate.ofPolyTime hf
  have hcf := NativeCertificate.ofPolyTime_isPolynomial hf
  obtain ⟨pT, hpT, hT⟩ := (hcf.1.comp hgLen).add (pOf len hpTg)
  obtain ⟨pS, hpS, hS⟩ := ((pOf len hpSg).add (hcf.2.comp hgLen)).mono (u := (cf.comp cg).space)
    fun a => Nat.add_le_add_right (hSg a) _
  refine ⟨cf.comp cg, pT, pS, hpT, hpS, fun a => ?_, hS⟩
  change cg.time a + cf.time (g a) ≤ _; rw [Nat.add_comm]
  exact (Nat.add_le_add_left (hTg a) (cf.time (g a))).trans
    ((add_mul_le_mul_add _ _ _ (hK a)).trans (Nat.mul_le_mul_left _ (hT a)))
private theorem HasKPolyCert.prod {α β γ : Type} {f : α → β} {g : α → γ}
    {ei : α ↪ List Bool} {em : β ↪ List Bool} {eo : γ ↪ List Bool} {K₁ K₂ : α → ℕ}
    (hf : HasKPolyCert f ei em K₁) (hg : HasKPolyCert g ei eo K₂) :
    HasKPolyCert (fun a => (f a, g a)) ei (encPair em eo) (fun a => K₁ a + K₂ a) := by
  let len (a : α) : ℕ := (ei a).length
  obtain ⟨cf, pTf, pSf, hpTf, hpSf, hTf, hSf⟩ := hf
  obtain ⟨cg, pTg, pSg, hpTg, hpSg, hTg, hSg⟩ := hg
  obtain ⟨pT, hpT, hT⟩ := (pOf len hpTf).add (pOf len hpTg)
  obtain ⟨pS, hpS, hS⟩ := ((pOf len hpSf).add (pOf len hpSg)).mono (u := (cf.prod cg).space)
    fun a => Nat.add_le_add (hSf a) (hSg a)
  refine ⟨cf.prod cg, pT, pS, hpT, hpS, fun a => ?_, hS⟩
  have hp1 := (Nat.le_add_right (pTf (len a)) (pTg (len a))).trans (hT a)
  have hp2 := (Nat.le_add_left (pTg (len a)) (pTf (len a))).trans (hT a)
  exact (Nat.add_le_add ((hTf a).trans (Nat.mul_le_mul_left _ hp1))
    ((hTg a).trans (Nat.mul_le_mul_left _ hp2))).trans_eq (Nat.add_mul _ _ _).symm
private theorem HasKPolyCert.indexFold {α β : Type} {encIn : α ↪ List Bool} {encB : β ↪ List Bool}
    {count : α → ℕ} {initial : α → β} {body : ℕ × β → β} {Kbody : ℕ × β → ℕ} {K B : α → ℕ}
    (hK : ∀ a, 1 ≤ K a) (hcount : ComputableInPolyTime count encIn encNat)
    (hinit : ComputableInPolyTime initial encIn encB)
    (hbody : HasKPolyCert body (encPair encNat encB) encB Kbody)
    (hBP : PolyBounded (fun a => (encIn a).length) B)
    (hKB : ∀ a j, j ≤ count a → Kbody (IndexFold.run body j (initial a)) ≤ K a)
    (hB : ∀ a j, j ≤ count a → (encB (IndexFold.run body j (initial a)).2).length ≤ B a) :
    HasKPolyCert (fun a => (IndexFold.run body (count a) (initial a)).2) encIn encB
      (fun a => (count a + 1) * K a) := by
  let len (a : α) : ℕ := (encIn a).length; obtain ⟨cb, pTb, pSb, hpTb, hpSb, hTb, hSb⟩ := hbody
  obtain ⟨pM, hpM, hmM, hleM⟩ := exists_mono_poly ((pOf id hpTb).add (pOf id hpSb))
  let cn := NativeCertificate.ofPolyTime hcount; let ci := NativeCertificate.ofPolyTime hinit
  have hcnP := NativeCertificate.ofPolyTime_isPolynomial hcount
  have hciP := NativeCertificate.ofPolyTime_isPolynomial hinit
  have hCntP := hcount.polyBounded_length
  let stLen (a : α) : ℕ := 2 * (encNat (count a)).length + 1 + B a
  let rBase (a : α) : ℕ := pM (stLen a)
  have hStP := (((PolyBounded.const 2).mul hCntP).add (.const 1)).add hBP
  have hrP : PolyBounded len rBase := (pOf id hpM).comp hStP
  have hCntSq := NativeCertificate.polyBounded_pow_of_polyBounded hCntP 1 2
  have hRun := IndexFold.computableInO cn ci cb (fun a => K a * rBase a) rBase B
    (fun a j hj => (hTb _).trans (Nat.mul_le_mul (hKB a j hj) ((Nat.le_add_right _ _).trans
      ((hleM _).trans (hmM (IndexFold.length_run_le body _ hj (hB a j hj)))))))
    (fun a j hj => (hSb _).trans ((Nat.le_add_left _ _).trans
      ((hleM _).trans (hmM (IndexFold.length_run_le body _ hj (hB a j hj)))))) hB
  let cert := (NativeCertificate.mk _ _ hRun).snd
  obtain ⟨pT, hpT, hBaseT⟩ := (hcnP.1.add (PolyBounded.self.add hciP.1)).add
    ((((hStP.add hCntSq).add hStP).add hCntSq).add hrP)
  obtain ⟨pS, hpS, hS⟩ := ((((hcnP.2.add (PolyBounded.self.add hciP.2)).add
    ((hStP.add (hCntP.add (.const 1))).add hrP)).add hStP).add hCntP).mono
    (u := cert.space) fun _ => le_rfl
  refine ⟨cert, pT, pS, hpT, hpS, fun a => ?_, hS⟩
  set K1 := count a + 1
  set U := (stLen a + ((encNat (count a)).length + 1) ^ 2) +
    stLen a + ((encNat (count a)).length + 1) ^ 2
  have hrew : cert.time a = (cn.time a + (len a + ci.time a)) + K1 * (U + K a * rBase a) := by
    change cn.time a + (len a + ci.time a) + K1 *
      ((stLen a + ((encNat (count a)).length + 1) ^ 2 + K a * rBase a) +
        stLen a + ((encNat (count a)).length + 1) ^ 2) = _; ring
  have h1 : cert.time a ≤ (cn.time a + (len a + ci.time a)) + (K1 * K a) * (U + rBase a) := by
    rw [hrew, Nat.mul_assoc]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left K1 (add_mul_le_mul_add _ _ _ (hK a))) _
  have hBT : cn.time a + (len a + ci.time a) + (U + rBase a) ≤ pT (encIn a).length := by
    have := hBaseT a; dsimp only [U, cn, ci, len, rBase, stLen] at this ⊢; omega
  exact (h1.trans (add_mul_le_mul_add _ (K1 * K a) _ (Nat.mul_pos (Nat.succ_pos _) (hK a)))).trans
    (Nat.mul_le_mul_left _ hBT)
private abbrev allPositiveIndices {γ : Type} (width : ℕ) (ctx : γ) (initOk : Bool)
    (test : γ → ℕ → Bool) : Bool :=
  (IndexFold.run
    (fun p : ℕ × (γ × Bool) => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1)))
    (2 ^ width) (ctx, initOk)).2.2
private theorem run_allIndex_fst {γ : Type} (test : γ → ℕ → Bool) (n : ℕ) (ctx : γ)
    (initOk : Bool) :
    (IndexFold.run
      (fun p : ℕ × (γ × Bool) => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1)))
      n (ctx, initOk)).2.1 = ctx := by
  induction n with | zero => rfl | succ n ih => simp only [IndexFold.run_succ, IndexFold.step, ih]
private theorem allPositiveIndices_eq_true_iff {γ : Type} (width : ℕ) (ctx : γ) (initOk : Bool)
    (test : γ → ℕ → Bool) :
    allPositiveIndices width ctx initOk test = true ↔
      initOk = true ∧ ∀ i < 2 ^ width, i ≠ 0 → test ctx i = true := by
  suffices ∀ n, (IndexFold.run
      (fun p : ℕ × (γ × Bool) => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1)))
      n (ctx, initOk)).2.2 = true ↔ initOk = true ∧ ∀ i < n, i ≠ 0 → test ctx i = true from
    this (2 ^ width)
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    rw [IndexFold.run_succ]; simp only [IndexFold.step, IndexFold.run_index, run_allIndex_fst,
      Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, ih]
    refine ⟨fun ⟨⟨hinit, hprev⟩, hlast⟩ => ⟨hinit, fun i hi hne => ?_⟩,
      fun ⟨hinit, hall⟩ => ⟨⟨hinit, fun i hi hne => hall i (Nat.lt_succ_of_lt hi) hne⟩, ?_⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · exact hprev i hlt hne
      · exact hlast.resolve_left hne
    · exact if h0 : n = 0 then Or.inl h0 else Or.inr (hall n (Nat.lt_succ_self n) h0)
private theorem allPositiveIndices_cert {α γ : Type} {encIn : α ↪ List Bool}
    {encCtx : γ ↪ List Bool} (width : α → ℕ) (ctx : α → γ) (initOk : α → Bool)
    (test : γ → ℕ → Bool) (hw : ComputableInPolyTime width encIn encUnary)
    (hctx : ComputableInPolyTime ctx encIn encCtx)
    (hinit : ComputableInPolyTime initOk encIn encBool)
    (htest : ComputableInPolyTime (fun q : γ × ℕ => test q.1 q.2)
      (encPair encCtx encNat) encBool) :
    HasKPolyCert (fun a => allPositiveIndices (width a) (ctx a) (initOk a) test) encIn encBool
      (fun a => 2 ^ width a + 1) := by
  have hcount : ComputableInPolyTime (fun a => 2 ^ width a) encIn encNat :=
    ComputableInPolyTime.binary_two_pow.comp hw
  let body := fun p : ℕ × (γ × Bool) => (p.2.1, p.2.2 && (decide (p.1 = 0) || test p.2.1 p.1))
  have hbody : ComputableInPolyTime body
      (encPair encNat (encPair encCtx encBool)) (encPair encCtx encBool) := by
    have heq0 : ComputableInPolyTime (fun p : ℕ × (γ × Bool) => decide (p.1 = 0))
        (encPair encNat (encPair encCtx encBool)) encBool :=
      ComputableInPolyTime.decide_eq' (ComputableInPolyTime.fst _ _) (.const 0)
    dsimp only [body]; fun_prop
  refine ((HasKPolyCert.indexFold (K := fun _ => 1) (B := fun a => 2 * (encCtx (ctx a)).length + 2)
    (fun _ => le_rfl) hcount (hctx.prod hinit) (.of_polyTime hbody)
    (((PolyBounded.const 2).mul hctx.polyBounded_length).add (.const 2))
    (fun _ _ _ => le_rfl) fun a j _ => ?_).snd).mono_const 1 (fun _ => by omega)
  rw [length_encPair, run_allIndex_fst test]; simp only [encBool_apply, List.length_singleton]
  omega
private abbrev searchMatrixStep {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool)
    (p : ℕ × (Q × (Bool × List (List Bool)))) : Q × (Bool × List (List Bool)) :=
  let q := p.2.1
  (q, if p.2.2.1 then p.2.2 else
    let cand := listRows (rowsOf q) (colsOf q) (lowBits (rowsOf q * colsOf q) p.1)
    if check q cand then (true, cand) else p.2.2)
private abbrev searchMatrix {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool) (q : Q) : List (List Bool) :=
  (IndexFold.run (searchMatrixStep rowsOf colsOf check) (2 ^ (rowsOf q * colsOf q))
    (q, (false, listRows (rowsOf q) (colsOf q) []))).2.2.2
private theorem run_searchMatrixStep_inv {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool) (n : ℕ) (q : Q) :
    let out := (IndexFold.run (searchMatrixStep rowsOf colsOf check) n
      (q, (false, listRows (rowsOf q) (colsOf q) []))).2
    out.1 = q ∧ (∃ w, out.2.2 = listRows (rowsOf q) (colsOf q) w) ∧
      (out.2.1 = true → check q out.2.2 = true) ∧
      ((∃ i < n, check q (listRows (rowsOf q) (colsOf q)
        (lowBits (rowsOf q * colsOf q) i)) = true) → out.2.1 = true) := by
  induction n with
  | zero => exact ⟨rfl, ⟨[], rfl⟩, fun h => Bool.noConfusion h,
      fun ⟨_, hi, _⟩ => (Nat.not_lt_zero _ hi).elim⟩
  | succ n ih =>
    obtain ⟨hq, ⟨w, hw⟩, hsound, hcomp⟩ := ih; dsimp only; rw [IndexFold.run_succ]
    set cur := (IndexFold.run (searchMatrixStep rowsOf colsOf check) n
      (q, (false, listRows (rowsOf q) (colsOf q) []))).2
    have hpair : IndexFold.run (searchMatrixStep rowsOf colsOf check) n
        (q, (false, listRows (rowsOf q) (colsOf q) [])) = (n, cur) :=
      Prod.ext (IndexFold.run_index _ _ _) rfl
    rw [hpair]; dsimp only [IndexFold.step, searchMatrixStep]; rw [hq]; refine ⟨rfl, ?_⟩
    cases hfound : cur.2.1
    · rw [ite_eq_right Bool.false_ne_true]
      set cand := listRows (rowsOf q) (colsOf q) (lowBits (rowsOf q * colsOf q) n)
      cases hcand : check q cand
      · rw [ite_eq_right Bool.false_ne_true]
        refine ⟨⟨w, hw⟩, fun h => Bool.noConfusion (hfound.symm.trans h), fun ⟨i, hi, hok⟩ => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact (Bool.false_ne_true (hfound.symm.trans (hcomp ⟨i, hlt, hok⟩))).elim
        · exact Bool.noConfusion (hcand.symm.trans hok)
      · rw [ite_eq_left rfl]; exact ⟨⟨_, rfl⟩, fun _ => hcand, fun _ => rfl⟩
    · rw [ite_eq_left rfl]; exact ⟨⟨w, hw⟩, fun _ => hsound hfound, fun _ => hfound⟩
private theorem searchMatrix_sound {Q : Type} (rowsOf colsOf : Q → ℕ)
    (check : Q → List (List Bool) → Bool) (q : Q)
    (hex : ∃ M : Fin (rowsOf q) → BitString (colsOf q),
      check q (List.ofFn fun r => List.ofFn (M r)) = true) :
    check q (searchMatrix rowsOf colsOf check q) = true := by
  obtain ⟨M, hM⟩ := hex
  have hinv := run_searchMatrixStep_inv rowsOf colsOf check (2 ^ (rowsOf q * colsOf q)) q
  let k : Fin (2 ^ (rowsOf q * colsOf q)) := equivFin (rowsOf q * colsOf q) (blocksEquiv.symm M)
  have hcand : listRows (rowsOf q) (colsOf q) (lowBits (rowsOf q * colsOf q) k.val) =
      List.ofFn (fun r => List.ofFn (M r)) := by
    rw [BooleanFold.lowBits_eq_word _ k, Equiv.symm_apply_apply, listRows_ofFn,
      block_blocksEquiv_symm]
  exact hinv.2.2.1 (hinv.2.2.2 ⟨k.val, k.isLt, by rwa [hcand]⟩)
private theorem searchMatrix_cert {α Q : Type} {encIn : α ↪ List Bool} {encQ : Q ↪ List Bool}
    {rowsOf colsOf wCheck : Q → ℕ} {qOf : α → Q} {check : Q → List (List Bool) → Bool}
    (hq : ComputableInPolyTime qOf encIn encQ) (hrows : ComputableInPolyTime rowsOf encQ encUnary)
    (hcols : ComputableInPolyTime colsOf encQ encUnary)
    (hCheck : HasKPolyCert (fun x : Q × List (List Bool) => check x.1 x.2)
      (encPair encQ (encList encBits)) encBool (fun x => 2 ^ wCheck x.1 + 1)) :
    HasKPolyCert (fun a => searchMatrix rowsOf colsOf check (qOf a)) encIn (encList encBits)
      (fun a => (2 ^ (rowsOf (qOf a) * colsOf (qOf a)) + 1) * (2 ^ wCheck (qOf a) + 1)) := by
  let encPay := encPair encBool (encList encBits)
  let encSt := encPair encQ encPay; let encFull := encPair encNat encSt
  have hra := hrows.comp hq; have hca := hcols.comp hq
  have hrcQ : ComputableInPolyTime (fun q => rowsOf q * colsOf q) encQ encUnary :=
    ComputableInPolyTime.unary_mul' hrows hcols
  have hcount : ComputableInPolyTime
      (fun a => 2 ^ (rowsOf (qOf a) * colsOf (qOf a))) encIn encNat :=
    ComputableInPolyTime.binary_two_pow.comp (hrcQ.comp hq)
  have hinit : ComputableInPolyTime
      (fun a => (qOf a, (false, listRows (rowsOf (qOf a)) (colsOf (qOf a)) []))) encIn encSt :=
    hq.prod ((ComputableInPolyTime.const false).prod
      (ComputableInPolyTime.bitsRowsWithInput hra hca (.const [])))
  have hpQ : ComputableInPolyTime (fun p : ℕ × Q × Bool × List (List Bool) => p.2.1)
      encFull encQ := by dsimp only [encFull, encSt, encPay]; fun_prop
  have hpPay : ComputableInPolyTime (fun p : ℕ × Q × Bool × List (List Bool) => p.2.2)
      encFull encPay := by dsimp only [encFull, encSt, encPay]; fun_prop
  have hcand := ComputableInPolyTime.bitsRowsWithInput (hrows.comp hpQ)
    (hcols.comp hpQ) (ComputableInPolyTime.bitsLow (hrcQ.comp hpQ)
      (ComputableInPolyTime.fst encNat encSt))
  have hSel : ComputableInPolyTime
      (fun x : ((Bool × List (List Bool)) × List (List Bool)) × Bool =>
        if x.1.1.1 then x.1.1 else if x.2 then (true, x.1.2) else x.1.1)
      (encPair (encPair encPay (encList encBits)) encBool) encPay := by
    dsimp only [encPay]; fun_prop
  have hPayStep := ((HasKPolyCert.of_polyTime (hpPay.prod hcand)).prod
    (hCheck.comp_polyPre (fun _ => Nat.le_add_left 1 _) (hpQ.prod hcand))).polyPost
    (fun _ => Nat.le_add_right 1 _) hSel
  have hStep : HasKPolyCert (searchMatrixStep rowsOf colsOf check) encFull encSt
      (fun p => 2 ^ wCheck p.2.1 + 1) :=
    (((HasKPolyCert.of_polyTime hpQ).prod hPayStep).mono_const 3
      (fun p => by dsimp only; generalize 2 ^ wCheck p.2.1 = z; omega)).congr (fun _ => rfl)
  let B (a : α) : ℕ :=
    2 * (encQ (qOf a)).length + 1 + (3 + rowsOf (qOf a) * (2 * colsOf (qOf a) + 1))
  have hBP : PolyBounded (fun a => (encIn a).length) B :=
    (((PolyBounded.const 2).mul hq.polyBounded_length).add (.const 1)).add
      ((PolyBounded.const 3).add ((polyBounded_unary hra).mul
        (((PolyBounded.const 2).mul (polyBounded_unary hca)).add (.const 1))))
  refine ((HasKPolyCert.indexFold (K := fun a => 2 ^ wCheck (qOf a) + 1) (B := B)
    (fun _ => Nat.le_add_left 1 _) hcount hinit hStep hBP
    (fun a j _ => by rw [(run_searchMatrixStep_inv rowsOf colsOf check j (qOf a)).1])
    fun a j _ => ?_).snd).snd
  set out := (IndexFold.run (searchMatrixStep rowsOf colsOf check) j
    (qOf a, (false, listRows (rowsOf (qOf a)) (colsOf (qOf a)) []))).2
  obtain ⟨hq_eq, ⟨w, hw⟩, -, -⟩ := run_searchMatrixStep_inv rowsOf colsOf check j (qOf a)
  have hmat : (encList encBits out.2.2).length = rowsOf (qOf a) * (2 * colsOf (qOf a) + 1) := by
    rw [show out.2.2 = listRows (rowsOf (qOf a)) (colsOf (qOf a)) w from hw]
    exact length_encList_listRows _ _ _
  have hqe : (encQ out.1).length = (encQ (qOf a)).length := by rw [hq_eq]
  change (encSt out).length ≤ B a
  simp only [encSt, encPay, length_encPair, encBool_apply, List.length_singleton, hqe, hmat, B]
  omega

/-! ### Polynomial-time and streaming checkers -/

private abbrev bitDot (u v : List Bool) : Bool := (u.zipWith Bool.and v).foldl Bool.xor false
private theorem bitDot_ofFn {n : ℕ} (u v : BitString n) :
    bitDot (List.ofFn u) (List.ofFn v) = (u ⬝ᵥ v) := (dotProduct_eq_foldl u v).symm
private theorem checkMatrixShape_polyTime {α : Type} {encIn : α ↪ List Bool} (r c : α → ℕ)
    (M : α → List (List Bool)) (hr : ComputableInPolyTime r encIn encUnary)
    (hc : ComputableInPolyTime c encIn encUnary)
    (hM : ComputableInPolyTime M encIn (encList encBits)) :
    ComputableInPolyTime (fun a => ((M a).length == r a) && (M a).all fun row => row.length == c a)
      encIn encBool := by
  have hall : ComputableInPolyTime (fun a => (M a).all fun row => row.length == c a)
      encIn encBool := by apply ComputableInPolyTime.allWithInput hM; fun_prop
  fun_prop
private theorem list_eq_ofFn_ofList {r c : ℕ} {M : List (List Bool)}
    (hlen : M.length = r) (hrows : ∀ row ∈ M, row.length = c) :
    M = List.ofFn fun i : Fin r => List.ofFn (ofList c (M.getD i.val [])) := by
  apply List.ext_getElem (by simp only [List.length_ofFn, hlen]); intro i hi _
  simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some, ofFn_ofList (hrows _ (List.getElem_mem hi))]
private theorem ofList_getD_ofFn {r c : ℕ} (A : Fin r → BitString c) (i : Fin r) :
    ofList c ((List.ofFn fun k => List.ofFn (A k)).getD i.val []) = A i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some, ofList_ofFn]
private abbrev BiasHdr := ℕ × ℕ × ℕ × ℕ
private abbrev BiasQ := BiasHdr × List (List Bool)
private abbrev encBiasHdr : BiasHdr ↪ List Bool :=
  encPair encUnary (encPair encUnary (encPair encNat encNat))
private abbrev encBiasQ : BiasQ ↪ List Bool := encPair encBiasHdr (encList encBits)

/-- Streaming small-bias shift checker ([OpenAI2026ETH], Lemma 6.1, eq. (6.2)): checks that
`shifts` has `d` rows of length `ell` and `|d - 2 * odd(b)| * maxBiasDen ≤ maxBiasNum * d` on all
nonzero masks `b ∈ {0, 1} ^ ell \ {0}`, returning `false` on any shape or bias violation. -/
def checkSmallBiasShifts (ell d maxBiasNum maxBiasDen : ℕ) (shifts : List (List Bool)) : Bool :=
  (IndexFold.run
    (fun p : ℕ × (((ℕ × ℕ × ℕ × ℕ) × List (List Bool)) × Bool) =>
      (p.2.1, p.2.2 && (decide (p.1 = 0) ||
        let odd := p.2.1.2.countP fun row =>
          (row.zipWith Bool.and (lowBits p.2.1.1.1 p.1)).foldl Bool.xor false
        let diff := (p.2.1.1.2.1 - 2 * odd) + (2 * odd - p.2.1.1.2.1)
        decide (diff * p.2.1.1.2.2.2 ≤ p.2.1.1.2.2.1 * p.2.1.1.2.1))))
    (2 ^ ell) (((ell, d, maxBiasNum, maxBiasDen), shifts),
      (shifts.length == d) && shifts.all (fun row => row.length == ell))).2.2

private theorem cast_nat_abs_sub (a b : ℕ) :
    (((a - b) + (b - a) : ℕ) : ℝ) = |(a : ℝ) - (b : ℝ)| := by
  rcases le_total a b with h | h <;>
    simp only [Nat.sub_eq_zero_of_le h, zero_add, add_zero, Nat.cast_sub h]
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
  · exact (abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))).symm

/-- Exact characterization of `checkSmallBiasShifts` for `d ≥ 1` and `0 < maxBiasDen`. -/
theorem checkSmallBiasShifts_eq_true_iff {ell d maxBiasNum maxBiasDen : ℕ} [NeZero d]
    (hden : 0 < maxBiasDen) (shifts : List (List Bool)) :
    checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = true ↔
      shifts.length = d ∧ (∀ row ∈ shifts, row.length = ell) ∧
        IsSmallBias ((maxBiasNum : ℝ) / maxBiasDen)
          ((uniformOfFintype (Fin d)).map fun j => ofList ell (shifts.getD j.val [])) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdenR : (0 : ℝ) < maxBiasDen := by exact_mod_cast hden
  rw [show checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = allPositiveIndices ell
    ((ell, d, maxBiasNum, maxBiasDen), shifts)
    ((shifts.length == d) && shifts.all (fun row => row.length == ell))
    (fun q idx => let odd := q.2.countP (fun row => bitDot row (lowBits q.1.1 idx))
      let diff := (q.1.2.1 - 2 * odd) + (2 * odd - q.1.2.1)
      decide (diff * q.1.2.2.2 ≤ q.1.2.2.1 * q.1.2.1)) from rfl, allPositiveIndices_eq_true_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  set s : Fin d → Fin ell → Bool := fun j => ofList ell (shifts.getD j.val [])
  have hodd_eq (hlen : shifts.length = d) (hrows : ∀ row ∈ shifts, row.length = ell)
      (k : Fin (2 ^ ell)) : shifts.countP (fun row => bitDot row (lowBits ell k.val)) =
        #{j : Fin d | parityOn {i : Fin ell | (equivFin ell).symm k i = true} (s j) = true} := by
    nth_rw 1 [list_eq_ofFn_ofList hlen hrows]
    rw [BooleanFold.lowBits_eq_word _ k, List.countP_ofFn, ← card_filter]; congr 1; ext j
    simp only [mem_filter, mem_univ, true_and]; rw [bitDot_ofFn, dotProduct_eq_parityOn]
  have hbias_iff (S : Finset (Fin ell)) :
      ((d - 2 * #{j : Fin d | parityOn S (s j) = true}) +
        (2 * #{j : Fin d | parityOn S (s j) = true} - d)) * maxBiasDen ≤ maxBiasNum * d ↔
        |bias ((uniformOfFintype (Fin d)).map s) S| ≤ (maxBiasNum : ℝ) / maxBiasDen := by
    rw [← @Nat.cast_le ℝ, Nat.cast_mul, Nat.cast_mul, cast_nat_abs_sub, Nat.cast_mul,
      Nat.cast_ofNat, ← sum_chi_eq S s, bias_uniformOfFintype_map, Fintype.expect_eq_sum_div_card,
      Fintype.card_fin, abs_div, abs_of_pos hdR, div_le_div_iff₀ hdR hdenR]
  refine ⟨fun ⟨⟨hlen, hrows⟩, hall⟩ => ⟨hlen, hrows, fun S hS => ?_⟩,
    fun ⟨hlen, hrows, hbias⟩ => ⟨⟨hlen, hrows⟩, fun idx hidx hne => ?_⟩⟩
  · let b : BitString ell := fun i => decide (i ∈ S); let k := equivFin ell b
    have hb0 : b ≠ 0 := by
      obtain ⟨i₀, hi₀⟩ := hS; intro h0; have := congrFun h0 i₀; simp [b, hi₀] at this
    have hk0 : k.val ≠ 0 := fun hk => hb0 <| by
      rw [← (equivFin ell).symm_apply_apply b]; exact (equivFin_symm_eq_zero_iff k).2 hk
    have htest := hall k.val k.isLt hk0
    have hS_eq : ({i : Fin ell | (equivFin ell).symm k i = true} : Finset (Fin ell)) = S := by
      rw [Equiv.symm_apply_apply]; ext i; simp [b]
    rw [decide_eq_true_eq, hodd_eq hlen hrows k, hS_eq] at htest; exact (hbias_iff S).1 htest
  · let k : Fin (2 ^ ell) := ⟨idx, hidx⟩; let b : BitString ell := (equivFin ell).symm k
    have hb0 : b ≠ 0 := fun h0 => hne ((equivFin_symm_eq_zero_iff k).1 h0)
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hb0; rw [decide_eq_true_eq, hodd_eq hlen hrows k]
    exact (hbias_iff _).2 (hbias _ ⟨i₀, mem_filter.mpr ⟨mem_univ i₀,
      Bool.eq_true_of_not_eq_false hi₀⟩⟩)
private theorem checkSmallBiasShifts_cert_aux :
    HasKPolyCert (fun q : BiasQ => checkSmallBiasShifts q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
      encBiasQ encBool (fun q => 2 ^ q.1.1 + 1) := by
  have hshape := checkMatrixShape_polyTime (encIn := encBiasQ) (fun q => q.1.2.1) (fun q => q.1.1)
    (fun q => q.2) (by dsimp only [encBiasQ, encBiasHdr]; fun_prop)
    (by dsimp only [encBiasQ, encBiasHdr]; fun_prop) (by dsimp only [encBiasQ]; fun_prop)
  let testFn (q : BiasQ) (idx : ℕ) : Bool :=
    let odd := q.2.countP (fun row => bitDot row (lowBits q.1.1 idx))
    let diff := (q.1.2.1 - 2 * odd) + (2 * odd - q.1.2.1)
    decide (diff * q.1.2.2.2 ≤ q.1.2.2.1 * q.1.2.1)
  have htest : ComputableInPolyTime (fun p : BiasQ × ℕ => testFn p.1 p.2)
      (encPair encBiasQ encNat) encBool := by
    unfold testFn bitDot
    have hodd : ComputableInPolyTime (fun p : BiasQ × ℕ => p.1.2.countP fun row =>
        ((row.zipWith Bool.and (lowBits p.1.1.1 p.2)).foldl Bool.xor false))
        (encPair encBiasQ encNat) encUnary := by
      apply ComputableInPolyTime.countPWithInput (by dsimp only [encBiasQ]; fun_prop)
      dsimp only [encBiasQ, encBiasHdr]; fun_prop
    have hle : ComputableInPolyTime (fun x : ℕ × ℕ => decide (x.1 ≤ x.2))
        (encPair encNat encNat) encBool := by fun_prop
    have hu2b : ComputableInPolyTime (fun n : ℕ => n) encUnary encNat := by fun_prop
    exact hle.comp
      ((ComputableInPolyTime.binary_mul'
        (hu2b.comp (by dsimp only [encBiasQ, encBiasHdr]; fun_prop))
        (by dsimp only [encBiasQ, encBiasHdr]; fun_prop)).prod
      (ComputableInPolyTime.binary_mul' (by dsimp only [encBiasQ, encBiasHdr]; fun_prop)
        (hu2b.comp (by dsimp only [encBiasQ, encBiasHdr]; fun_prop))))
  exact (allPositiveIndices_cert (fun q => q.1.1) id
    (fun q => (q.2.length == q.1.2.1) && q.2.all (fun row => row.length == q.1.1)) testFn
    (by dsimp only [encBiasQ, encBiasHdr]; fun_prop) (.of_eq fun _ => rfl) hshape htest).congr
    fun _ => rfl
/-- Native `ComputableInO` certificate for `checkSmallBiasShifts`. -/
theorem checkSmallBiasShifts_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encQ := encPair (encPair encUnary (encPair encUnary (encPair encNat encNat)))
        (encList encBits)
      ComputableInO (fun q : (ℕ × ℕ × ℕ × ℕ) × List (List Bool) =>
          checkSmallBiasShifts q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2) encQ encBool
        (fun q => (2 ^ q.1.1 + 1) * pT (encQ q).length) (fun q => pS (encQ q).length) := by
  obtain ⟨cert, pT, pS, hpT, hpS, hT, hS⟩ := checkSmallBiasShifts_cert_aux
  exact ⟨pT, pS, hpT, hpS, cert.computes.mono_le hT hS⟩
/-- Plain polynomial-time certificate for `checkSmallBiasShifts` when `2 ^ ell` is poly-bounded. -/
theorem checkSmallBiasShifts_polyTime {α : Type} {encIn : α ↪ List Bool}
    {ell d maxBiasNum maxBiasDen : α → ℕ} {shifts : α → List (List Bool)}
    (hell : ComputableInPolyTime ell encIn encUnary) (hd : ComputableInPolyTime d encIn encUnary)
    (hnum : ComputableInPolyTime maxBiasNum encIn encNat)
    (hden : ComputableInPolyTime maxBiasDen encIn encNat)
    (hshifts : ComputableInPolyTime shifts encIn (encList encBits))
    (hq : PolyBounded (fun a => (encIn a).length) (fun a => 2 ^ ell a)) :
    ComputableInPolyTime
      (fun a => checkSmallBiasShifts (ell a) (d a) (maxBiasNum a) (maxBiasDen a) (shifts a))
      encIn encBool := by
  obtain ⟨c, pT, pS, hpT, hpS, hT, hS⟩ :=
    checkSmallBiasShifts_cert_aux.comp_polyPre (fun _ => Nat.le_add_left 1 _)
      ((hell.prod (hd.prod (hnum.prod hden))).prod hshifts)
  exact c.polyTime ⟨((hq.add (.const 1)).mul (pOf _ hpT)).mono hT, (pOf _ hpS).mono hS⟩
/-- Specialization of `checkSmallBiasShifts_polyTime` when `2 ^ ell ≤ 2 * m + 1`. -/
theorem checkSmallBiasShifts_polyTime_of_two_pow_le {α : Type} {encIn : α ↪ List Bool}
    {m ell d maxBiasNum maxBiasDen : α → ℕ} {shifts : α → List (List Bool)}
    (hm : ComputableInPolyTime m encIn encUnary) (hell : ComputableInPolyTime ell encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hnum : ComputableInPolyTime maxBiasNum encIn encNat)
    (hden : ComputableInPolyTime maxBiasDen encIn encNat)
    (hshifts : ComputableInPolyTime shifts encIn (encList encBits))
    (hle : ∀ a, 2 ^ ell a ≤ 2 * m a + 1) :
    ComputableInPolyTime
      (fun a => checkSmallBiasShifts (ell a) (d a) (maxBiasNum a) (maxBiasDen a) (shifts a))
      encIn encBool :=
  checkSmallBiasShifts_polyTime hell hd hnum hden hshifts
    ((((PolyBounded.const 2).mul (polyBounded_unary hm)).add (.const 1)).mono hle)
private abbrev LocalHdr := ℕ × ℕ × ℕ
private abbrev LocalQ := LocalHdr × List (List Bool)
private abbrev encLocalHdr : LocalHdr ↪ List Bool := encPair encUnary (encPair encUnary encUnary)
private abbrev encLocalQ : LocalQ ↪ List Bool := encPair encLocalHdr (encList encBits)
/-- Streaming local-code distance checker ([OpenAI2026ETH], Lemma 6.1) via `IndexFold.run`:
checks that `H0` has `c` rows of length `d` and every nonzero `w ∈ {0, 1} ^ d \ {0}` in its
`GF(2)` kernel has Hamming weight at least `minDist`, returning `false` on any violation. -/
def checkLocalCodeDistance (c d minDist : ℕ) (H0 : List (List Bool)) : Bool :=
  (IndexFold.run
    (fun p : ℕ × (((ℕ × ℕ × ℕ) × List (List Bool)) × Bool) =>
      (p.2.1, p.2.2 && (decide (p.1 = 0) ||
        let w := lowBits p.2.1.1.2.1 p.1
        !(p.2.1.2.all fun row => !((row.zipWith Bool.and w).foldl Bool.xor false)) ||
          decide (p.2.1.1.2.2 ≤ w.count true))))
    (2 ^ d) (((c, d, minDist), H0),
      (H0.length == c) && H0.all (fun row => row.length == d))).2.2
/-- Exact characterization of `checkLocalCodeDistance`. -/
theorem checkLocalCodeDistance_eq_true_iff (c d minDist : ℕ) (H0 : List (List Bool)) :
    checkLocalCodeDistance c d minDist H0 = true ↔
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
        ∀ w : Fin d → Bool, w ≠ 0 →
          (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → minDist ≤ weight w := by
  rw [show checkLocalCodeDistance c d minDist H0 = allPositiveIndices d ((c, d, minDist), H0)
    ((H0.length == c) && H0.all (fun row => row.length == d))
    (fun q idx => let w := lowBits q.1.2.1 idx
      !(q.2.all (fun row => !bitDot row w)) || decide (q.1.2.2 ≤ w.count true)) from rfl,
    allPositiveIndices_eq_true_iff]
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  have hker_iff (hlen : H0.length = c) (hrows : ∀ row ∈ H0, row.length = d) (w : BitString d) :
      H0.all (fun row => !bitDot row (List.ofFn w)) = true ↔
        ∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false := by
    nth_rw 1 [list_eq_ofFn_ofList hlen hrows]
    simp only [List.all_eq_true, List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff,
      Bool.not_eq_true', bitDot_ofFn]
  refine ⟨fun ⟨⟨hlen, hrows⟩, hall⟩ => ⟨hlen, hrows, fun w hw0 hker => ?_⟩,
    fun ⟨hlen, hrows, hdist⟩ => ⟨⟨hlen, hrows⟩, fun idx hidx hne => ?_⟩⟩
  · let k := equivFin d w
    have hk0 : k.val ≠ 0 := fun hk => hw0 <| by
      rw [← (equivFin d).symm_apply_apply w]; exact (equivFin_symm_eq_zero_iff k).2 hk
    have htest := hall k.val k.isLt hk0
    rw [BooleanFold.lowBits_eq_word _ k, Equiv.symm_apply_apply,
      (hker_iff hlen hrows w).2 hker] at htest
    simpa only [Bool.not_true, Bool.false_or, decide_eq_true_eq, count_true_ofFn] using htest
  · let k : Fin (2 ^ d) := ⟨idx, hidx⟩; let w : BitString d := (equivFin d).symm k
    have hw0 : w ≠ 0 := fun h0 => hne ((equivFin_symm_eq_zero_iff k).1 h0)
    rw [BooleanFold.lowBits_eq_word _ k]
    by_cases hkerList : H0.all (fun row => !bitDot row (List.ofFn w)) = true
    · rw [hkerList, Bool.not_true, Bool.false_or, decide_eq_true_eq, count_true_ofFn]
      exact hdist w hw0 ((hker_iff hlen hrows w).1 hkerList)
    · rw [Bool.eq_false_iff.mpr hkerList]; rfl
private theorem checkLocalCodeDistance_cert_aux :
    HasKPolyCert (fun q : LocalQ => checkLocalCodeDistance q.1.1 q.1.2.1 q.1.2.2 q.2)
      encLocalQ encBool (fun q => 2 ^ q.1.2.1 + 1) := by
  have hshape := checkMatrixShape_polyTime (encIn := encLocalQ) (fun q => q.1.1)
    (fun q => q.1.2.1) (fun q => q.2) (by dsimp only [encLocalQ, encLocalHdr]; fun_prop)
    (by dsimp only [encLocalQ, encLocalHdr]; fun_prop) (by dsimp only [encLocalQ]; fun_prop)
  let testFn (q : LocalQ) (idx : ℕ) : Bool :=
    let w := lowBits q.1.2.1 idx
    !(q.2.all (fun row => !bitDot row w)) || decide (q.1.2.2 ≤ w.count true)
  have htest : ComputableInPolyTime (fun p : LocalQ × ℕ => testFn p.1 p.2)
      (encPair encLocalQ encNat) encBool := by
    unfold testFn bitDot
    have hker : ComputableInPolyTime (fun p : LocalQ × ℕ => p.1.2.all fun row =>
        !((row.zipWith Bool.and (lowBits p.1.1.2.1 p.2)).foldl Bool.xor false))
        (encPair encLocalQ encNat) encBool := by
      apply ComputableInPolyTime.allWithInput (by dsimp only [encLocalQ]; fun_prop)
      dsimp only [encLocalQ, encLocalHdr]; fun_prop
    dsimp only [encLocalQ, encLocalHdr]; fun_prop
  exact (allPositiveIndices_cert (fun q => q.1.2.1) id
    (fun q => (q.2.length == q.1.1) && q.2.all (fun row => row.length == q.1.2.1)) testFn
    (by dsimp only [encLocalQ, encLocalHdr]; fun_prop) (.of_eq fun _ => rfl) hshape htest).congr
    fun _ => rfl
/-- Native `ComputableInO` certificate for `checkLocalCodeDistance`. -/
theorem checkLocalCodeDistance_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encQ := encPair (encPair encUnary (encPair encUnary encUnary)) (encList encBits)
      ComputableInO (fun q : (ℕ × ℕ × ℕ) × List (List Bool) =>
          checkLocalCodeDistance q.1.1 q.1.2.1 q.1.2.2 q.2) encQ encBool
        (fun q => (2 ^ q.1.2.1 + 1) * pT (encQ q).length) (fun q => pS (encQ q).length) := by
  obtain ⟨cert, pT, pS, hpT, hpS, hT, hS⟩ := checkLocalCodeDistance_cert_aux
  exact ⟨pT, pS, hpT, hpS, cert.computes.mono_le hT hS⟩
/-! ### Sequential `IndexFold` searchers -/
/-- Sequential `IndexFold` search ([OpenAI2026ETH], Lemma 6.1) over `0 .. 2 ^ (d * ell) - 1`,
returning the first `d × ell` shift table passing `checkSmallBiasShifts`, or the total all-`false`
fallback `listRows d ell []` when no candidate passes. -/
def findSmallBiasShifts (ell d maxBiasNum maxBiasDen : ℕ) : List (List Bool) :=
  (IndexFold.run
    (fun p : ℕ × ((ℕ × ℕ × ℕ × ℕ) × (Bool × List (List Bool))) =>
      let q := p.2.1
      (q, if p.2.2.1 then p.2.2 else
        let cand := listRows q.2.1 q.1 (lowBits (q.2.1 * q.1) p.1)
        if checkSmallBiasShifts q.1 q.2.1 q.2.2.1 q.2.2.2 cand then (true, cand) else p.2.2))
    (2 ^ (d * ell)) ((ell, d, maxBiasNum, maxBiasDen), (false, listRows d ell []))).2.2.2
/-- Soundness of `findSmallBiasShifts` for `d ≥ 1` and `0 < maxBiasDen` when a witness exists. -/
theorem isSmallBias_findSmallBiasShifts {ell d maxBiasNum maxBiasDen : ℕ} [NeZero d]
    (hden : 0 < maxBiasDen) (hex : ∃ s : Fin d → Fin ell → Bool,
      IsSmallBias ((maxBiasNum : ℝ) / maxBiasDen) ((uniformOfFintype (Fin d)).map s)) :
    let shifts := findSmallBiasShifts ell d maxBiasNum maxBiasDen
    checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = true ∧
      shifts.length = d ∧ (∀ row ∈ shifts, row.length = ell) ∧
      IsSmallBias ((maxBiasNum : ℝ) / maxBiasDen)
        ((uniformOfFintype (Fin d)).map fun j => ofList ell (shifts.getD j.val [])) := by
  obtain ⟨s, hs⟩ := hex
  have hcheck : checkSmallBiasShifts ell d maxBiasNum maxBiasDen
      (findSmallBiasShifts ell d maxBiasNum maxBiasDen) = true := by
    apply searchMatrix_sound (fun q => q.2.1) (fun q => q.1)
      (fun q cand => checkSmallBiasShifts q.1 q.2.1 q.2.2.1 q.2.2.2 cand)
      (ell, d, maxBiasNum, maxBiasDen)
    refine ⟨s, (checkSmallBiasShifts_eq_true_iff hden _).2 ⟨by simp, by simp, ?_⟩⟩
    convert hs using 2; funext j; exact ofList_getD_ofFn s j
  exact ⟨hcheck, (checkSmallBiasShifts_eq_true_iff hden _).1 hcheck⟩
private theorem findSmallBiasShifts_cert_aux {α : Type} {encIn : α ↪ List Bool}
    (ell d maxBiasNum maxBiasDen : α → ℕ) (hell : ComputableInPolyTime ell encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hnum : ComputableInPolyTime maxBiasNum encIn encNat)
    (hden : ComputableInPolyTime maxBiasDen encIn encNat) :
    HasKPolyCert (fun a => findSmallBiasShifts (ell a) (d a) (maxBiasNum a) (maxBiasDen a))
      encIn (encList encBits) (fun a => (2 ^ (d a * ell a) + 1) * (2 ^ ell a + 1)) :=
  (searchMatrix_cert (encQ := encBiasHdr) (rowsOf := fun q => q.2.1) (colsOf := fun q => q.1)
    (wCheck := fun q => q.1)
    (check := fun q cand => checkSmallBiasShifts q.1 q.2.1 q.2.2.1 q.2.2.2 cand)
    (hell.prod (hd.prod (hnum.prod hden))) (by dsimp only [encBiasHdr]; fun_prop)
    (by dsimp only [encBiasHdr]; fun_prop) checkSmallBiasShifts_cert_aux).congr fun _ => rfl
/-- Native `ComputableInO` certificate for `findSmallBiasShifts`. -/
theorem findSmallBiasShifts_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encH := encPair encUnary (encPair encUnary (encPair encNat encNat))
      ComputableInO (fun p : ℕ × ℕ × ℕ × ℕ => findSmallBiasShifts p.1 p.2.1 p.2.2.1 p.2.2.2)
        encH (encList encBits)
        (fun p => (2 ^ (p.2.1 * p.1) + 1) * (2 ^ p.1 + 1) * pT (encH p).length)
        (fun p => pS (encH p).length) := by
  obtain ⟨cert, pT, pS, hpT, hpS, hT, hS⟩ := findSmallBiasShifts_cert_aux (encIn := encBiasHdr)
    (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2.1) (fun p => p.2.2.2)
    (by dsimp only [encBiasHdr]; fun_prop) (by dsimp only [encBiasHdr]; fun_prop)
    (by dsimp only [encBiasHdr]; fun_prop) (by dsimp only [encBiasHdr]; fun_prop)
  exact ⟨pT, pS, hpT, hpS, cert.computes.mono_le hT hS⟩
/-- Sequential `IndexFold` search ([OpenAI2026ETH], Lemma 6.1) over `0 .. 2 ^ (c * d) - 1`,
returning the first `c × d` check matrix passing `checkLocalCodeDistance`, or the total all-`false`
fallback `listRows c d []` when no candidate passes. -/
def findLocalCheckMatrix (c d minDist : ℕ) : List (List Bool) :=
  (IndexFold.run
    (fun p : ℕ × ((ℕ × ℕ × ℕ) × (Bool × List (List Bool))) =>
      let q := p.2.1
      (q, if p.2.2.1 then p.2.2 else
        let cand := listRows q.1 q.2.1 (lowBits (q.1 * q.2.1) p.1)
        if checkLocalCodeDistance q.1 q.2.1 q.2.2 cand then (true, cand) else p.2.2))
    (2 ^ (c * d)) ((c, d, minDist), (false, listRows c d []))).2.2.2
/-- Soundness of `findLocalCheckMatrix` when a check matrix of distance `minDist` exists. -/
theorem weight_le_of_findLocalCheckMatrix {c d minDist : ℕ}
    (hex : ∃ A : Fin c → Fin d → Bool,
      ∀ w : Fin d → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → minDist ≤ weight w) :
    let H0 := findLocalCheckMatrix c d minDist
    checkLocalCodeDistance c d minDist H0 = true ∧
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
      ∀ w : Fin d → Bool, w ≠ 0 →
        (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → minDist ≤ weight w := by
  obtain ⟨A, hA⟩ := hex
  have hcheck : checkLocalCodeDistance c d minDist (findLocalCheckMatrix c d minDist) = true := by
    apply searchMatrix_sound (fun q => q.1) (fun q => q.2.1)
      (fun q cand => checkLocalCodeDistance q.1 q.2.1 q.2.2 cand) (c, d, minDist)
    refine ⟨A, (checkLocalCodeDistance_eq_true_iff c d minDist _).2 ⟨by simp, by simp, ?_⟩⟩
    intro w hw0 hker; exact hA w hw0 fun i => by simpa only [ofList_getD_ofFn] using hker i
  exact ⟨hcheck, (checkLocalCodeDistance_eq_true_iff c d minDist _).1 hcheck⟩
private theorem findLocalCheckMatrix_cert_aux {α : Type} {encIn : α ↪ List Bool}
    (c d minDist : α → ℕ) (hc : ComputableInPolyTime c encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary)
    (hmin : ComputableInPolyTime minDist encIn encUnary) :
    HasKPolyCert (fun a => findLocalCheckMatrix (c a) (d a) (minDist a)) encIn (encList encBits)
      (fun a => (2 ^ (c a * d a) + 1) * (2 ^ d a + 1)) :=
  (searchMatrix_cert (encQ := encLocalHdr) (rowsOf := fun q => q.1) (colsOf := fun q => q.2.1)
    (wCheck := fun q => q.2.1)
    (check := fun q cand => checkLocalCodeDistance q.1 q.2.1 q.2.2 cand) (hc.prod (hd.prod hmin))
    (by dsimp only [encLocalHdr]; fun_prop) (by dsimp only [encLocalHdr]; fun_prop)
    checkLocalCodeDistance_cert_aux).congr fun _ => rfl
/-- Native `ComputableInO` certificate for `findLocalCheckMatrix`. -/
theorem findLocalCheckMatrix_computableInO :
    ∃ pT pS : ℕ → ℕ, Cslib.PolynomiallyBounded pT ∧ Cslib.PolynomiallyBounded pS ∧
      let encH := encPair encUnary (encPair encUnary encUnary)
      ComputableInO (fun p : ℕ × ℕ × ℕ => findLocalCheckMatrix p.1 p.2.1 p.2.2)
        encH (encList encBits)
        (fun p => (2 ^ (p.1 * p.2.1) + 1) * (2 ^ p.2.1 + 1) * pT (encH p).length)
        (fun p => pS (encH p).length) := by
  obtain ⟨cert, pT, pS, hpT, hpS, hT, hS⟩ := findLocalCheckMatrix_cert_aux (encIn := encLocalHdr)
    (fun p => p.1) (fun p => p.2.1) (fun p => p.2.2) (by dsimp only [encLocalHdr]; fun_prop)
    (by dsimp only [encLocalHdr]; fun_prop) (by dsimp only [encLocalHdr]; fun_prop)
  exact ⟨pT, pS, hpT, hpS, cert.computes.mono_le hT hS⟩

/-! ### Shortened Tanner parity-check matrix builder -/

private def edgeEmbedding {m ell d : ℕ} (hd : 0 < d) (hm : m ≤ 2 ^ ell * d) :
    Fin m ↪ (Fin ell → Bool) × Fin d where
  toFun e :=
    ((equivFin ell).symm ⟨e.val / d, (Nat.div_lt_iff_lt_mul hd).2 (e.isLt.trans_le hm)⟩,
      ⟨e.val % d, Nat.mod_lt e.val hd⟩)
  inj' e₁ e₂ h := by
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    have hdiv : e₁.val / d = e₂.val / d := congrArg Fin.val ((equivFin ell).symm.injective h₁)
    have hmod : e₁.val % d = e₂.val % d := congrArg Fin.val h₂
    ext; rw [← Nat.div_add_mod e₁.val d, ← Nat.div_add_mod e₂.val d, hdiv, hmod]

/-- Construct the `2 * 2 ^ ell * c` parity-check rows of length `m` for the shortened Tanner code
([OpenAI2026ETH], Lemma 6.1, p. 42), matching `Cslib.BitString.Tanner.shortRow`. Fills entries with
`false` when `d = 0` and pads/truncates missing `shifts` or `H0` entries with `false`. -/
def buildShortenedTannerRows (m ell d c : ℕ) (shifts H0 : List (List Bool)) : List (List Bool) :=
  [false, true].flatMap fun side =>
    (List.range (2 ^ ell)).flatMap fun vIdx =>
      let vBits := lowBits ell vIdx
      (List.range c).map fun i =>
        let aRow := H0.getD i []
        (List.range m).map fun e =>
          if d == 0 then false else
            let uBits := lowBits ell (e / d); let port := e % d
            let sBits := listRow ell 0 (shifts.getD port [])
            let endBits := if side then uBits.zipWith Bool.xor sBits else uBits
            if !(endBits.zipWith Bool.xor vBits).any id then aRow.getD port false else false

@[simp] theorem length_buildShortenedTannerRows (m ell d c : ℕ) (shifts H0 : List (List Bool)) :
    (buildShortenedTannerRows m ell d c shifts H0).length = 2 * 2 ^ ell * c := by
  simp only [buildShortenedTannerRows, List.flatMap_cons, List.flatMap_nil, List.length_append,
    List.length_nil, List.length_flatMap, List.length_map, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul]; ring
theorem length_mem_buildShortenedTannerRows {m ell d c : ℕ} {shifts H0 : List (List Bool)}
    {row : List Bool} (hrow : row ∈ buildShortenedTannerRows m ell d c shifts H0) :
    row.length = m := by
  simp only [buildShortenedTannerRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_range, List.mem_map] at hrow
  obtain ⟨_, _, _, _, _, _, rfl⟩ := hrow; simp
private theorem xor_any_eq_false_iff {ell : ℕ} (x y : BitString ell) :
    ((List.ofFn x).zipWith Bool.xor (List.ofFn y)).any id = false ↔ x = y := by
  have hxor (a b : Bool) : (a ^^ b) = false ↔ a = b := by cases a <;> cases b <;> decide
  rw [← ofFn_add, List.any_eq_false]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff, id_eq,
    Bool.not_eq_true, Pi.add_apply, Bool.add_eq_xor, hxor, funext_iff]
private theorem buildRow_eq_ofFn_shortRow {m ell d c : ℕ} (hd : 0 < d) (hm : m ≤ 2 ^ ell * d)
    (shifts H0 : List (List Bool)) (side : Bool) (v : Fin (2 ^ ell)) (i : Fin c) :
    (List.range m).map (fun e =>
      if d == 0 then false else
        let uBits := lowBits ell (e / d); let port := e % d
        let sBits := listRow ell 0 (shifts.getD port [])
        let endBits := if side then uBits.zipWith Bool.xor sBits else uBits
        if !(endBits.zipWith Bool.xor (lowBits ell v.val)).any id then
          (H0.getD i.val []).getD port false else false) =
      List.ofFn (Tanner.shortRow (fun j : Fin d => ofList ell (shifts.getD j.val []))
        (fun r : Fin c => ofList d (H0.getD r.val []))
        (edgeEmbedding hd hm) (side, (equivFin ell).symm v, i)) := by
  apply List.ext_getElem (by simp only [List.length_map, List.length_range, List.length_ofFn])
  intro e he _; simp only [List.length_map, List.length_range] at he; let ef : Fin m := ⟨e, he⟩
  set endPt := if side then (edgeEmbedding hd hm ef).1 +
      ofList ell (shifts.getD (edgeEmbedding hd hm ef).2.val []) else (edgeEmbedding hd hm ef).1
  have hu : lowBits ell (e / d) = List.ofFn (edgeEmbedding hd hm ef).1 :=
    BooleanFold.lowBits_eq_word _ ⟨e / d, (Nat.div_lt_iff_lt_mul hd).2 (he.trans_le hm)⟩
  have hs : listRow ell 0 (shifts.getD (e % d) []) =
      List.ofFn (ofList ell (shifts.getD (edgeEmbedding hd hm ef).2.val [])) :=
    listRow_zero ell (shifts.getD (e % d) [])
  have hend : (if side then (lowBits ell (e / d)).zipWith Bool.xor
        (listRow ell 0 (shifts.getD (e % d) [])) else lowBits ell (e / d)) = List.ofFn endPt := by
    dsimp only [endPt]; rw [hu, hs]; cases side <;> simp [ofFn_add]
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, beq_false_of_ne hd.ne',
    Bool.false_eq_true, ↓reduceIte, hend, BooleanFold.lowBits_eq_word _ v, Tanner.shortRow]
  change (if !((List.ofFn endPt).zipWith Bool.xor (List.ofFn ((equivFin ell).symm v))).any id then
      (H0.getD i.val []).getD (e % d) false else false) =
    if endPt = (equivFin ell).symm v then ofList d (H0.getD i.val []) (edgeEmbedding hd hm ef).2
      else false
  by_cases heq : endPt = (equivFin ell).symm v
  · rw [(xor_any_eq_false_iff _ _).2 heq]; simp only [heq, Bool.not_false, ↓reduceIte]; rfl
  · rw [Bool.eq_true_of_not_eq_false fun h => heq ((xor_any_eq_false_iff _ _).1 h)]
    simp only [heq, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
theorem count_true_mem_buildShortenedTannerRows_le {m ell d c : ℕ} (hd : 0 < d)
    (hm : m ≤ 2 ^ ell * d) {shifts H0 : List (List Bool)} {row : List Bool}
    (hrow : row ∈ buildShortenedTannerRows m ell d c shifts H0) : row.count true ≤ d := by
  simp only [buildShortenedTannerRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_range, List.mem_map] at hrow
  obtain ⟨side, _, vIdx, hv, i, hi, rfl⟩ := hrow
  rw [buildRow_eq_ofFn_shortRow hd hm shifts H0 side ⟨vIdx, hv⟩ ⟨i, hi⟩, count_true_ofFn]
  exact Tanner.weight_shortRow_le _ _ _ _

/-- Distance transfer from `Tanner.le_weight_of_shortRow` for `d ≥ 1`, `0 < maxBiasDen`. -/
theorem le_weight_of_buildShortenedTannerRows {m ell d c maxBiasNum maxBiasDen h : ℕ}
    [NeZero d] (hden : 0 < maxBiasDen) (hm : m ≤ 2 ^ ell * d) {shifts H0 : List (List Bool)}
    (hshifts : checkSmallBiasShifts ell d maxBiasNum maxBiasDen shifts = true)
    (hH0 : checkLocalCodeDistance c d (h + 1) H0 = true) {z : Fin m → Bool} (hz0 : z ≠ 0)
    (hz : ∀ row ∈ buildShortenedTannerRows m ell d c shifts H0, ofList m row ⬝ᵥ z = false) :
    ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ((maxBiasNum : ℝ) / maxBiasDen) * d) * 2 ^ ell ≤
      d * weight z := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdenR : (0 : ℝ) < maxBiasDen := by exact_mod_cast hden
  have hs := ((checkSmallBiasShifts_eq_true_iff hden shifts).1 hshifts).2.2
  have hA := ((checkLocalCodeDistance_eq_true_iff c d (h + 1) H0).1 hH0).2.2
  refine Tanner.le_weight_of_shortRow (fun j : Fin d => ofList ell (shifts.getD j.val []))
    (by positivity) hs (fun i : Fin c => ofList d (H0.getD i.val []))
    (fun w hw0 hker => Nat.lt_of_succ_le (hA w hw0 hker)) (edgeEmbedding hd hm) ?_ hz0
  rintro ⟨side, u, i⟩; let v : Fin (2 ^ ell) := equivFin ell u
  have hrow := hz _ (by
    simp only [buildShortenedTannerRows, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_range, List.mem_map]
    exact ⟨side, by cases side <;> simp, v.val, v.isLt, i.val, i.isLt, rfl⟩)
  rw [buildRow_eq_ofFn_shortRow hd hm shifts H0 side v i, ofList_ofFn,
    (equivFin ell).symm_apply_apply u] at hrow
  exact hrow
/-- Specialization of `buildShortenedTannerRows` to Lemma 6.1 (`1 ≤ n, m, B`, `m ≤ B * n`). -/
theorem le_mul_weight_of_buildShortenedTannerRows_params {n m B : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hB : 1 ≤ B) (hmn : m ≤ B * n) {shifts H0 : List (List Bool)}
    (hshifts : checkSmallBiasShifts (ellG m B) (dG m B) 1 (biasDen m B) shifts = true)
    (hH0 : checkLocalCodeDistance (cG m B) (dG m B) (hDist m B + 1) H0 = true) :
    let rows := buildShortenedTannerRows m (ellG m B) (dG m B) (cG m B) shifts H0
    rows.length ≤ 3 * n ∧
      (∀ row ∈ rows, row.length = m ∧ row.count true ≤ initialRowWeightBound B m) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ row ∈ rows, ofList m row ⬝ᵥ z = false) → m ≤ greedyRowListLength B m * weight z := by
  have hd : 0 < dG m B := dG_pos hm hB; have : NeZero (dG m B) := ⟨hd.ne'⟩
  have hqd : m ≤ 2 ^ ellG m B * dG m B := le_qG_mul_dG hm hB
  have hden : 0 < biasDen m B := by unfold biasDen; positivity
  refine ⟨(length_buildShortenedTannerRows _ _ _ _ _ _).le.trans
      (two_mul_qG_mul_cG_le_three_mul hn hm hB hmn),
    fun row hrow => ⟨length_mem_buildShortenedTannerRows hrow,
      (count_true_mem_buildShortenedTannerRows_le hd hqd hrow).trans (Nat.min_le_right _ _)⟩,
    fun z hz0 hz => ?_⟩
  have htan := le_weight_of_buildShortenedTannerRows hden hqd hshifts hH0 hz0 hz
  set D : ℝ := 100 * (B : ℝ) * (mu m : ℝ); have hM : 0 < D := by positivity
  have hh_ge : (dG m B : ℝ) / D ≤ ((hDist m B + 1 : ℕ) : ℝ) := by
    rw [div_le_iff₀ hM]; dsimp only [D, mu]; exact_mod_cast dG_le_hDist_succ_mul hm hB
  have hdiff_ge : (dG m B : ℝ) / (2 * D) ≤
      ((hDist m B + 1 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) / (biasDen m B : ℝ) * (dG m B : ℝ) := by
    have : ((1 : ℕ) : ℝ) / (biasDen m B : ℝ) * (dG m B : ℝ) = (dG m B : ℝ) / (2 * D) := by
      dsimp only [D]; unfold biasDen mu; push_cast; ring
    have : (dG m B : ℝ) / D = 2 * ((dG m B : ℝ) / (2 * D)) := by ring
    linarith
  have hd0 : 0 ≤ (dG m B : ℝ) / D := by positivity
  have hmulP := mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right
    (mul_le_mul hh_ge hdiff_ge (by positivity) (hd0.trans hh_ge)) (by positivity)).trans htan)
    (by unfold greedyRowListLength; positivity : (0 : ℝ) ≤ greedyRowListLength B m)
  have hP_ident :
      ((dG m B : ℝ) / D) * ((dG m B : ℝ) / (2 * D)) * 2 ^ ellG m B *
        (greedyRowListLength B m : ℝ) = (dG m B : ℝ) * ((qG m B * dG m B : ℕ) : ℝ) := by
    dsimp only [D]; unfold greedyRowListLength qG mu; push_cast; field_simp; ring
  rw [hP_ident] at hmulP; have hdR : (0 : ℝ) < dG m B := by exact_mod_cast hd
  have hqdR : (m : ℝ) ≤ ((qG m B * dG m B : ℕ) : ℝ) := by exact_mod_cast le_qG_mul_dG hm hB
  exact_mod_cast (by nlinarith : (m : ℝ) ≤ (greedyRowListLength B m : ℝ) * (weight z : ℝ))
/-- Plain polynomial-time certificate for `buildShortenedTannerRows` when `2 ^ ell ≤ bound`. -/
theorem buildShortenedTannerRows_polyTime {α : Type} {encIn : α ↪ List Bool}
    {m ell d c bound : α → ℕ} {shifts H0 : α → List (List Bool)}
    (hm : ComputableInPolyTime m encIn encUnary) (hell : ComputableInPolyTime ell encIn encUnary)
    (hd : ComputableInPolyTime d encIn encUnary) (hc : ComputableInPolyTime c encIn encUnary)
    (hbound : ComputableInPolyTime bound encIn encUnary)
    (hshifts : ComputableInPolyTime shifts encIn (encList encBits))
    (hH0 : ComputableInPolyTime H0 encIn (encList encBits)) (hle : ∀ a, 2 ^ ell a ≤ bound a) :
    ComputableInPolyTime
      (fun a => buildShortenedTannerRows (m a) (ell a) (d a) (c a) (shifts a) (H0 a))
      encIn (encList encBits) := by
  have hq : ComputableInPolyTime (fun a => 2 ^ ell a) encIn encUnary :=
    ComputableInPolyTime.binary_to_unary_bounded
      (ComputableInPolyTime.binary_two_pow.comp hell) hbound hle
  unfold buildShortenedTannerRows
  have hside (side : Bool) : ComputableInPolyTime
      (fun a => (List.range (2 ^ ell a)).flatMap fun vIdx =>
        let vBits := lowBits (ell a) vIdx
        (List.range (c a)).map fun i =>
          let aRow := (H0 a).getD i []
          (List.range (m a)).map fun e =>
            if d a == 0 then false else
              let uBits := lowBits (ell a) (e / d a); let port := e % d a
              let sBits := listRow (ell a) 0 ((shifts a).getD port [])
              let endBits := if side then uBits.zipWith Bool.xor sBits else uBits
              if !(endBits.zipWith Bool.xor vBits).any id then aRow.getD port false else false)
      encIn (encList encBits) := by
    apply ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.range.comp hq)
    apply ComputableInPolyTime.mapWithInput
      (ComputableInPolyTime.range.comp (hc.comp (by fun_prop)))
    apply ComputableInPolyTime.mapToBitsWithInput
      (ComputableInPolyTime.range.comp (hm.comp (by fun_prop)))
    dsimp only; fun_prop
  have happ : ComputableInPolyTime
      (fun p : List (List Bool) × List (List Bool) => p.1 ++ p.2)
      (encPair (encList encBits) (encList encBits)) (encList encBits) := by fun_prop
  refine (happ.comp ((hside false).prod (hside true))).of_enc_eq fun a => ?_
  simp only [Function.comp_apply, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-! ### Unconditional Lemma 6.1 initial-tests assembly and native resource bounds -/

private theorem exists_shifts_params {m B : ℕ} [NeZero (dG m B)] (hB : 1 ≤ B) :
    ∃ s : Fin (dG m B) → Fin (ellG m B) → Bool,
      IsSmallBias ((1 : ℝ) / biasDen m B) ((uniformOfFintype (Fin (dG m B))).map s) := by
  rcases Nat.eq_zero_or_pos (ellG m B) with h0 | hpos
  · exact ⟨fun _ => 0, fun _ ⟨i, _⟩ => absurd i.isLt (by omega)⟩
  · have hmu : 0 < mu m := Nat.succ_pos _
    have hdenR : (0 : ℝ) < biasDen m B := by unfold biasDen; positivity
    refine exists_isSmallBias_map_of_exp_lt (ι := Fin (ellG m B)) (d := dG m B) (by positivity) ?_
    rw [Fintype.card_fin]
    have hexp : ((1 : ℝ) / biasDen m B) ^ 2 * (dG m B : ℝ) / 2 = 4 * (mu m : ℝ) := by
      rw [dG_eq_of_ellG_pos hpos]
      unfold initialRowWeightBound biasDen mu; push_cast; field_simp; ring
    rw [hexp, Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos _), one_mul]
    have hell_mu := ellG_le_mu m B
    have h8 : (2 : ℝ) * 2 ^ ellG m B ≤ (8 : ℝ) ^ mu m :=
      calc (2 : ℝ) * 2 ^ ellG m B = (2 : ℝ) ^ (ellG m B + 1) := by rw [pow_succ']
        _ ≤ (2 : ℝ) ^ (3 * mu m) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = (8 : ℝ) ^ mu m := by rw [pow_mul]; norm_num
    have he4 : (8 : ℝ) < Real.exp 4 := by
      rw [show Real.exp 4 = Real.exp 1 ^ 4 by rw [← Real.exp_nat_mul]; norm_num]
      nlinarith [pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by decide : (4 : ℕ) ≠ 0)]
    rw [show (4 : ℝ) * (mu m : ℝ) = (mu m : ℝ) * 4 by ring, Real.exp_nat_mul]
    exact h8.trans_lt (pow_lt_pow_left₀ he4 (by norm_num) (by omega))
private theorem exists_localMatrix_params {m B : ℕ} (hm : 1 ≤ m) (hB : 1 ≤ B) :
    ∃ A : Fin (cG m B) → Fin (dG m B) → Bool,
      ∀ w : Fin (dG m B) → Bool, w ≠ 0 → (∀ i, A i ⬝ᵥ w = false) → hDist m B + 1 ≤ weight w := by
  suffices hball : #{w : Fin (dG m B) → Bool | w ≠ 0 ∧ weight w ≤ hDist m B} < 2 ^ cG m B by
    obtain ⟨A, hA⟩ := exists_forall_weight_le hball
    refine ⟨A, fun w hw0 hker => ?_⟩; by_contra hlt; obtain ⟨i, hi⟩ := hA w hw0 (by omega)
    exact Bool.false_ne_true ((hker i).symm.trans hi)
  have hd_lt : dG m B < 2 ^ mu m :=
    (Nat.min_le_left _ _).trans_lt (Nat.lt_pow_succ_log_self (by decide : 1 < 2) m)
  have hmu_h : mu m * hDist m B < cG m B := by
    have hc_ge : dG m B ≤ cG m B * (8 * B) := by
      rw [cG, ← Nat.ceilDiv_eq_add_pred_div]
      exact Nat.le_ceilDiv_mul (by omega)
    have hle := Nat.mul_div_le (dG m B + 100 * B * mu m - 1) (100 * B * mu m)
    rw [← hDist_succ_eq hm hB] at hle; have := dG_pos hm hB
    have : dG m B + 100 * B * mu m - 1 + 1 = dG m B + 100 * B * mu m := by omega
    have h1 : B * (100 * (mu m * hDist m B)) < B * (8 * cG m B) := by nlinarith
    have := Nat.lt_of_mul_lt_mul_left h1; omega
  calc #{w : Fin (dG m B) → Bool | w ≠ 0 ∧ weight w ≤ hDist m B}
      ≤ #{w : Fin (dG m B) → Bool | weight w ≤ hDist m B} :=
        card_le_card fun w hw => mem_filter.mpr ⟨mem_univ w, (mem_filter.mp hw).2.2⟩
    _ ≤ (dG m B + 1) ^ hDist m B := card_filter_weight_le_le (dG m B) (hDist m B)
    _ ≤ (2 ^ mu m) ^ hDist m B := Nat.pow_le_pow_left (by omega) _
    _ = 2 ^ (mu m * hDist m B) := (Nat.pow_mul 2 (mu m) (hDist m B)).symm
    _ < 2 ^ cG m B := Nat.pow_lt_pow_right (by decide) hmu_h

/-- Deterministic Lemma 6.1 construction of the initial parity-check matrix `A^(0)` via
`findSmallBiasShifts`, `findLocalCheckMatrix`, and `buildShortenedTannerRows`. Returns `[]` in the
degenerate cases `m = 0` or `B = 0`. -/
def initialTestsRows (m B : ℕ) : List (List Bool) :=
  buildShortenedTannerRows m (ellG m B) (dG m B) (cG m B)
    (findSmallBiasShifts (ellG m B) (dG m B) 1 (biasDen m B))
    (findLocalCheckMatrix (cG m B) (dG m B) (hDist m B + 1))

/-- Unconditional correctness of `initialTestsRows` ([OpenAI2026ETH], 6.1) for `1 ≤ n, B` and
`m ≤ B * n`. -/
theorem initialTestsRows_spec {n m B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B) (hmn : m ≤ B * n) :
    let rows := initialTestsRows m B
    rows.length ≤ 3 * n ∧
      (∀ row ∈ rows, row.length = m ∧ row.count true ≤ initialRowWeightBound B m) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ row ∈ rows, ofList m row ⬝ᵥ z = false) → m ≤ greedyRowListLength B m * weight z := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hc0 : cG 0 B = 0 := by
      simp only [cG, dG, Nat.zero_min, zero_add]; exact Nat.div_eq_of_lt (by omega)
    have hnil : initialTestsRows 0 B = [] := List.eq_nil_of_length_eq_zero
      (by rw [initialTestsRows, length_buildShortenedTannerRows, hc0, mul_zero])
    simp only [hnil, List.length_nil, Nat.zero_le, List.not_mem_nil, false_implies, implies_true,
      and_self]
  · have hd := dG_pos hm hB; have : NeZero (dG m B) := ⟨hd.ne'⟩
    have hden : 0 < biasDen m B := by unfold biasDen; positivity
    exact le_mul_weight_of_buildShortenedTannerRows_params hn hm hB hmn
      ((isSmallBias_findSmallBiasShifts (maxBiasNum := 1) hden
        (by simpa only [Nat.cast_one] using exists_shifts_params hB)).1)
      ((weight_le_of_findLocalCheckMatrix (exists_localMatrix_params hm hB)).1)
/-- Executable witness matching `Cslib.BitString.exists_initialTests` for `1 ≤ n, B` and
`m ≤ B * n`. -/
theorem map_ofList_initialTestsRows_spec {n m B : ℕ} (hn : 1 ≤ n) (hB : 1 ≤ B)
    (hmn : m ≤ B * n) :
    let rows := (initialTestsRows m B).map (ofList m)
    rows.length ≤ 3 * n ∧ (∀ r ∈ rows, weight r ≤ initialRowWeightBound B m) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ r ∈ rows, r ⬝ᵥ z = false) → m ≤ greedyRowListLength B m * weight z := by
  obtain ⟨hlen, hrows, hdist⟩ := initialTestsRows_spec hn hB hmn
  refine ⟨by simpa only [List.length_map] using hlen, fun r hr => ?_,
    fun z hz0 hz => hdist z hz0 fun row hmem => hz _ (List.mem_map.mpr ⟨row, hmem, rfl⟩)⟩
  obtain ⟨row, hmem, rfl⟩ := List.mem_map.mp hr
  rw [← count_true_ofFn, ofFn_ofList (hrows row hmem).1]; exact (hrows row hmem).2
/-- Real division corollary `(m : ℝ) / greedyRowListLength B m ≤ weight z` for `1 ≤ n, B` and
`m ≤ B * n`. -/
theorem div_greedyRowListLength_le_weight_of_initialTestsRows {n m B : ℕ} (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hmn : m ≤ B * n) {z : Fin m → Bool} (hz0 : z ≠ 0)
    (hz : ∀ row ∈ initialTestsRows m B, ofList m row ⬝ᵥ z = false) :
    (m : ℝ) / (greedyRowListLength B m : ℝ) ≤ (weight z : ℝ) := by
  have hP : (0 : ℝ) < greedyRowListLength B m := by unfold greedyRowListLength; positivity
  rw [div_le_iff₀ hP, mul_comm]; exact_mod_cast (initialTestsRows_spec hn hB hmn).2.2 z hz0 hz

private theorem two_pow_add_one_le (a : ℕ) : 2 ^ a + 1 ≤ 2 ^ (a + 1) := by
  have := @Nat.one_le_two_pow a; rw [Nat.pow_succ]; omega
private theorem mul_two_pow_add_one_le (a b : ℕ) :
    (2 ^ a + 1) * (2 ^ b + 1) ≤ 2 ^ (a + b + 2) :=
  (Nat.mul_le_mul (two_pow_add_one_le a) (two_pow_add_one_le b)).trans_eq
    (by rw [← Nat.pow_add]; congr 1; omega)
private theorem linear_mb_le_two_pow (m B : ℕ) :
    2 * m + 2 + B ≤ 2 ^ (B + Nat.log 2 (m + 2) + 4) := by
  set X := B + Nat.log 2 (m + 2)
  have hm : m + 2 < 2 ^ (X + 1) := (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m + 2)).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [X]; omega))
  have hB : B < 2 ^ (X + 1) := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [X]; omega))
  have : 2 ^ (X + 4) = 8 * 2 ^ (X + 1) := by
    rw [show X + 4 = (X + 1) + 3 by omega, Nat.pow_add]; ring
  omega
private theorem exists_pow_of_polyBounded_mb {u : ℕ × ℕ → ℕ}
    (hu : PolyBounded (fun p => (encMB p).length) u) :
    ∃ E : ℕ × ℕ → ℕ, PolyBounded (fun p => p.2 + Nat.log 2 (p.1 + 2)) E ∧ ∀ p, u p ≤ 2 ^ E p := by
  obtain ⟨c, d, hle⟩ := hu.exists_le
  refine ⟨fun p => c + d * (p.2 + Nat.log 2 (p.1 + 2) + 4),
    (PolyBounded.const c).add ((PolyBounded.const d).mul (PolyBounded.self.add (.const 4))),
    fun p => ?_⟩
  have hlen : (encMB p).length + 1 = 2 * p.1 + 2 + p.2 := by
    simp only [encMB, length_encPair, encUnary_apply, List.length_replicate]; omega
  rw [Nat.pow_add]; refine (hle p).trans (Nat.mul_le_mul Nat.lt_two_pow_self.le ?_)
  rw [Nat.mul_comm, Nat.pow_mul, hlen]; exact Nat.pow_le_pow_left (linear_mb_le_two_pow p.1 p.2) d
private abbrev encMid := encPair encMB (encPair (encList encBits) (encList encBits))

/-- Native `ComputableInO` certificate for `initialTestsRows` on unary `(m, B)`, proving pure
`2 ^ q (B + Nat.log 2 (m + 2))` time and `S (m + B)` space. -/
theorem initialTestsRows_computableInO :
    ∃ q S : ℕ → ℕ, Cslib.PolynomiallyBounded q ∧ Cslib.PolynomiallyBounded S ∧
      ComputableInO (fun p : ℕ × ℕ => initialTestsRows p.1 p.2)
        (encPair encUnary encUnary) (encList encBits)
        (fun p => 2 ^ q (p.2 + Nat.log 2 (p.1 + 2))) (fun p => S (p.1 + p.2)) := by
  let lenMB (p : ℕ × ℕ) : ℕ := (encMB p).length; let X (p : ℕ × ℕ) : ℕ := p.2 + Nat.log 2 (p.1 + 2)
  have hSh := findSmallBiasShifts_cert_aux (encIn := encMB)
    (fun p => ellG p.1 p.2) (fun p => dG p.1 p.2) (fun _ => 1) (fun p => biasDen p.1 p.2)
    (by dsimp only [encMB]; fun_prop) (by dsimp only [encMB]; fun_prop) (.const 1)
    ((show ComputableInPolyTime (fun n : ℕ => n) encUnary encNat by fun_prop).comp
      (biasDen_polyTime (by dsimp only [encMB]; fun_prop) (by dsimp only [encMB]; fun_prop)))
  have hLo := findLocalCheckMatrix_cert_aux (encIn := encMB)
    (fun p => cG p.1 p.2) (fun p => dG p.1 p.2) (fun p => hDist p.1 p.2 + 1)
    (by dsimp only [encMB]; fun_prop) (by dsimp only [encMB]; fun_prop)
    (by dsimp only [encMB]; fun_prop)
  have hBuild : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × (List (List Bool) × List (List Bool)) =>
        buildShortenedTannerRows x.1.1 (ellG x.1.1 x.1.2) (dG x.1.1 x.1.2) (cG x.1.1 x.1.2)
          x.2.1 x.2.2) encMid (encList encBits) :=
    buildShortenedTannerRows_polyTime (bound := fun x => 2 * x.1.1 + 1)
      (by dsimp only [encMid, encMB]; fun_prop) (by dsimp only [encMid, encMB]; fun_prop)
      (by dsimp only [encMid, encMB]; fun_prop) (by dsimp only [encMid, encMB]; fun_prop)
      (by dsimp only [encMid, encMB]; fun_prop) (by dsimp only [encMid, encMB]; fun_prop)
      (by dsimp only [encMid, encMB]; fun_prop) (fun x => qG_le_two_mul_add_one x.1.1 x.1.2)
  obtain ⟨cFull, pT, pS, hpT, hpS, hT, hS⟩ :=
    (((HasKPolyCert.of_polyTime (ComputableInPolyTime.of_eq fun _ => rfl)).prod
      (hSh.prod hLo)).polyPost (fun _ => Nat.le_add_right 1 _) hBuild).congr (fun _ => rfl)
  have hLenSum : PolyBounded (fun p : ℕ × ℕ => p.1 + p.2) lenMB :=
    (((PolyBounded.const 2).mul PolyBounded.self).add (.const 1)).mono fun p => by
      simp only [lenMB, encMB, length_encPair, encUnary_apply, List.length_replicate]; omega
  obtain ⟨S, hS_poly, hSpace⟩ := ((pOf lenMB hpS).mono hS).comp hLenSum
  obtain ⟨Ep, hEpP, hEp⟩ := exists_pow_of_polyBounded_mb (pOf lenMB hpT)
  have hB_X : PolyBounded X Prod.snd := PolyBounded.self.mono fun _ => by dsimp only [X]; omega
  have hmu_X : PolyBounded X (fun p => mu p.1) :=
    (PolyBounded.self.add (.const 1)).mono fun p => by
      have := Nat.add_le_add_right (Nat.log_mono_right (by omega : p.1 ≤ p.1 + 2) (b := 2)) 1
      dsimp only [X, mu] at this ⊢; omega
  have hdG_X : PolyBounded X (fun p => dG p.1 p.2) :=
    (((PolyBounded.const 320000).mul (hB_X.mul hB_X)).mul
      (hmu_X.mul (hmu_X.mul hmu_X))).mono fun p => by
      refine (Nat.min_le_right _ _).trans ?_; unfold initialRowWeightBound mu; ring_nf; exact le_rfl
  have hell_X : PolyBounded X (fun p => ellG p.1 p.2) := hmu_X.mono fun p => ellG_le_mu p.1 p.2
  have hcG_X : PolyBounded X (fun p => cG p.1 p.2) :=
    (hdG_X.add (.const 1)).mono fun p => cG_le_dG_add_one p.1 p.2
  let E1 (p : ℕ × ℕ) : ℕ := dG p.1 p.2 * ellG p.1 p.2 + ellG p.1 p.2 + 2
  let E2 (p : ℕ × ℕ) : ℕ := cG p.1 p.2 * dG p.1 p.2 + dG p.1 p.2 + 2
  obtain ⟨q, hq_poly, hEq⟩ := (((((hdG_X.mul hell_X).add hell_X).add (.const 2)).add
    (((hcG_X.mul hdG_X).add hdG_X).add (.const 2))).add hEpP).add (.const 2)
  refine ⟨q, S, hq_poly, hS_poly, cFull.computes.mono_le (fun p => ?_) hSpace⟩
  have h1le := (mul_two_pow_add_one_le (dG p.1 p.2 * ellG p.1 p.2) (ellG p.1 p.2)).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [E1, E2]; omega : _ ≤ E1 p + E2 p))
  have h2le := (mul_two_pow_add_one_le (cG p.1 p.2 * dG p.1 p.2) (dG p.1 p.2)).trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by dsimp only [E1, E2]; omega : _ ≤ E1 p + E2 p))
  have hKsum : 1 + ((2 ^ (dG p.1 p.2 * ellG p.1 p.2) + 1) * (2 ^ ellG p.1 p.2 + 1) +
      (2 ^ (cG p.1 p.2 * dG p.1 p.2) + 1) * (2 ^ dG p.1 p.2 + 1)) ≤ 2 ^ (E1 p + E2 p + 2) := by
    rw [Nat.pow_add]; have h0 := @Nat.one_le_two_pow (E1 p + E2 p); omega
  refine ((hT p).trans (Nat.mul_le_mul hKsum (hEp p))).trans ?_
  rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide : 0 < 2)
    (by have hEqp := hEq p; dsimp only [X, E1, E2] at hEqp ⊢; omega)
/-- Triple-input `(n, m, B)` form of `initialTestsRows_computableInO` on unary `(n, m, B)`,
proving `n + 2 ^ q (B + Nat.log 2 (m + 2))` time (where `+ n` scans past the unary `n` prefix on
the input tape) and `S (n + m + B)` space. -/
theorem initialTestsRows_computableInO_nmb :
    ∃ q S : ℕ → ℕ, Cslib.PolynomiallyBounded q ∧ Cslib.PolynomiallyBounded S ∧
      ComputableInO (fun p : ℕ × ℕ × ℕ => initialTestsRows p.2.1 p.2.2)
        (encPair encUnary (encPair encUnary encUnary)) (encList encBits)
        (fun p => p.1 + 2 ^ q (p.2.2 + Nat.log 2 (p.2.1 + 2)))
        (fun p => S (p.1 + p.2.1 + p.2.2)) := by
  obtain ⟨q, S, hq, hS, hcomp⟩ := initialTestsRows_computableInO
  let encNMB := encPair encUnary encMB
  let cRes := (NativeCertificate.mk _ _ hcomp).comp
    (NativeCertificate.linear (ComputableInO.snd encUnary encMB))
  let sz (p : ℕ × ℕ × ℕ) : ℕ := p.1 + p.2.1 + p.2.2
  have hLenNMB : PolyBounded sz (fun p => (encNMB p).length) :=
    (((PolyBounded.const 4).mul PolyBounded.self).add (.const 3)).mono fun p => by
      simp only [sz, encNMB, encMB, length_encPair, encUnary_apply, List.length_replicate]; omega
  obtain ⟨S', hS', hSpace⟩ := hLenNMB.add ((pOf id hS).comp ((PolyBounded.self (size := sz)).mono
    (u := fun p : ℕ × ℕ × ℕ => p.2.1 + p.2.2) fun _ => by dsimp only [sz]; omega))
  let q' (X : ℕ) : ℕ := q X + (X + 5)
  refine ⟨q', S', by dsimp only [q']; fun_prop, hS',
    cRes.computes.mono 2 (fun p => ?_) (fun p => ?_)⟩
  · change (encNMB p).length + 2 ^ q (p.2.2 + Nat.log 2 (p.2.1 + 2)) ≤
      2 * (p.1 + 2 ^ q' (p.2.2 + Nat.log 2 (p.2.1 + 2)) + 1)
    set X := p.2.2 + Nat.log 2 (p.2.1 + 2)
    have hlen : (encNMB p).length = 2 * p.1 + (2 * p.2.1 + 2 + p.2.2) := by
      simp only [encNMB, encMB, length_encPair, encUnary_apply, List.length_replicate]; omega
    have h1 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : X + 4 ≤ q X + (X + 4))
    have h2 := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : q X ≤ q X + (X + 4))
    have h3 : 2 ^ q' X = 2 * 2 ^ (q X + (X + 4)) := by
      dsimp only [q']; rw [show q X + (X + 5) = (q X + (X + 4)) + 1 by omega, Nat.pow_succ']
    have hmb : 2 * p.2.1 + 2 + p.2.2 ≤ 2 ^ (X + 4) := linear_mb_le_two_pow p.2.1 p.2.2; omega
  · change (encNMB p).length + S (p.2.1 + p.2.2) ≤ 2 * (S' (p.1 + p.2.1 + p.2.2) + 1)
    have hs : (encNMB p).length + S (p.2.1 + p.2.2) ≤ S' (p.1 + p.2.1 + p.2.2) := hSpace p
    omega

end Cslib.Complexity.InitialTestsSearch
