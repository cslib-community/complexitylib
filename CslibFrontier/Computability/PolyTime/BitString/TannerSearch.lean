/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.GenericRAM.Native.ExpTimePolySpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.PolyTime.BitString.InitialTestsSearch
public import CslibFrontier.Foundations.Data.Nat.CeilDiv
public import CslibFrontier.Probability.SmallBias.Random
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Preprocess
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Foundations.Data.BitString.InitialTests
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Unconditional exhaustive-search wrappers and M20 parity-test assembly

Unconditional specifications and resource bounds layered on
`CslibFrontier.Computability.PolyTime.BitString.InitialTestsSearch`:

1. **Small-bias shift search at `d ≥ ⌈4 (r + 1) / ε²⌉`**: `smallBiasCeil r p q` gives the integer
   threshold `⌈4 (r + 1) q² / p²⌉`. Combining `Cslib.BitString.exists_isSmallBias_map_of_ceil_le`
   with `InitialTestsSearch.findSmallBiasShifts` yields an unconditional `IsSmallBias (p / q)`
   certificate (`isSmallBias_findSmallBiasShifts_of_le`, `isSmallBias_findSmallBiasShiftsCeil`) and
   an explicit `ComputableInO` search bound (`findSmallBiasShiftsCeil_computableInO`).
2. **Local check matrix search under Gilbert–Varshamov bounds**: `findLocalCheckMatrix` succeeds
   unconditionally whenever the Hamming ball of nonzero strings of weight at most `h` has size less
   than `2 ^ c` (`weight_le_of_findLocalCheckMatrix_of_ball_lt`), in particular whenever
   `ballSize d h ≤ 2 ^ c` or `(d + 1) ^ h ≤ 2 ^ c`
   (`weight_le_of_findLocalCheckMatrix_of_ballSize_le`,
   `weight_le_of_findLocalCheckMatrix_of_pow_le`), with the search cost from
   `InitialTestsSearch.findLocalCheckMatrix_computableInO`.
3. **End-to-end M20 parity-test composition**: `tannerParityTests` pairs `findSmallBiasShifts`,
   `findLocalCheckMatrix`, and `buildShortenedTannerRows`, unconditionally producing at most
   `2 · 2 ^ r · c` rows of weight at most `d` with global relative-distance guarantee
   `δ * (δ - p / q) * (d * 2 ^ r) ≤ weight z` (`tannerParityTests_spec`). The exponential-time,
   polynomial-space resource certificate applies exactly to the bounded wrapper
   `tannerParityTestsWithBound` (`tannerParityTests_computableInO`), which clamps the
   dimension to a unary parameter to preserve the polynomial space bound.


## Main definitions

* `Cslib.Complexity.TannerSearch.smallBiasCeil`: computable ceiling `⌈4 (r + 1) q² / p²⌉`.
* `Cslib.Complexity.TannerSearch.SmallBiasCeilParams`,
  `Cslib.Complexity.TannerSearch.encSmallBiasCeilParams`,
  `Cslib.Complexity.TannerSearch.findSmallBiasShiftsCeil`: shift search at `smallBiasCeil`.
* `Cslib.Complexity.TannerSearch.TannerParityParams`,
  `Cslib.Complexity.TannerSearch.encTannerParityParams`,
  `Cslib.Complexity.TannerSearch.tannerParityTests`,
  `Cslib.Complexity.TannerSearch.tannerParityTestsWithBound`: end-to-end parity-test builders.

## Main results

* `Cslib.Complexity.TannerSearch.isSmallBias_findSmallBiasShifts_of_le`,
  `Cslib.Complexity.TannerSearch.isSmallBias_findSmallBiasShiftsCeil`,
  `Cslib.Complexity.TannerSearch.findSmallBiasShiftsCeil_computableInO`: unconditional small-bias
  shift search and cost.
* `Cslib.Complexity.TannerSearch.weight_le_of_findLocalCheckMatrix_of_ball_lt`,
  `Cslib.Complexity.TannerSearch.weight_le_of_findLocalCheckMatrix_of_ballSize_le`,
  `Cslib.Complexity.TannerSearch.weight_le_of_findLocalCheckMatrix_of_pow_le`: unconditional
  Gilbert–Varshamov local-code search bounds.
* `Cslib.Complexity.TannerSearch.tannerParityTests_spec`,
  `Cslib.Complexity.TannerSearch.tannerParityTests_computableInO`: end-to-end correctness and
  `ExpTimePolySpace` resource bounds.

## References

* [J. Naor, M. Naor, *Small-bias probability spaces*][NaorNaor1993]
* [M. Sipser, D. A. Spielman, *Expander codes*][SipserSpielman1996]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], §6.1
-/

public section

namespace Cslib.Complexity.TannerSearch

open Finset Cslib.BitString Cslib.Complexity.InitialTestsSearch Cslib.GenericRAM
open Cslib.Probability.PMF Turing.MultiTapeTM ComputableInPolyTime

section SearchComplexityHelper

private theorem search_computableInO_preprocess {α β γ : Type} {encI : α ↪ List Bool}
    {encH : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : β → γ} {g : α → β} {a b : β → ℕ} {pT pS : ℕ → ℕ}
    (hpT : Cslib.PolynomiallyBounded pT) (hpS : Cslib.PolynomiallyBounded pS)
    (hcomp : ComputableInO f encH encOut
      (fun q => (2 ^ a q + 1) * (2 ^ b q + 1) * pT (encH q).length)
      (fun q => pS (encH q).length))
    (hg : ComputableInPolyTime g encI encH) :
    ∃ eT eS : ℕ, ComputableInO (fun x => f (g x)) encI encOut
      (fun x => 2 ^ (a (g x) + b (g x)) * ((encI x).length + 1) ^ eT)
      (fun x => ((encI x).length + 1) ^ eS) := by
  obtain ⟨cT, dT, hT_le⟩ := (PolyBounded.of_polynomiallyBounded id hpT).exists_le
  obtain ⟨cS, dS, hS_le⟩ := (PolyBounded.of_polynomiallyBounded id hpS).exists_le
  have hmono : ComputableInO f encH encOut
      (fun q => 2 ^ (a q + b q) * ((encH q).length + 1) ^ dT)
      (fun q => ((encH q).length + 1) ^ dS) := by
    refine hcomp.mono (4 * cT + cS + 1) (fun q => ?_) (fun q => ?_)
    · have hpow : (2 ^ a q + 1) * (2 ^ b q + 1) ≤ 4 * 2 ^ (a q + b q) := by
        have ha : 1 ≤ 2 ^ a q := Nat.one_le_two_pow
        have hb : 1 ≤ 2 ^ b q := Nat.one_le_two_pow
        rw [pow_add]
        nlinarith
      calc
        (2 ^ a q + 1) * (2 ^ b q + 1) * pT (encH q).length
          ≤ (4 * 2 ^ (a q + b q)) * (cT * ((encH q).length + 1) ^ dT) :=
            Nat.mul_le_mul hpow (hT_le (encH q).length)
        _ ≤ _ := by
          have : 0 ≤ 2 ^ (a q + b q) * ((encH q).length + 1) ^ dT := Nat.zero_le _
          nlinarith
    · calc
        pS (encH q).length ≤ cS * ((encH q).length + 1) ^ dS := hS_le (encH q).length
        _ ≤ (4 * cT + cS + 1) * ((encH q).length + 1) ^ dS :=
            Nat.mul_le_mul_right _ (by omega)
        _ ≤ (4 * cT + cS + 1) * (((encH q).length + 1) ^ dS + 1) :=
            Nat.mul_le_mul_left _ (Nat.le_succ _)
  exact ComputableInO.comp_polyTime hmono hg (fun _ => le_rfl) (fun _ => le_rfl)

private theorem search_expTimePolySpace {α β γ : Type} {encI : α ↪ List Bool}
    {encH : β ↪ List Bool} {encOut : γ ↪ List Bool}
    {f : β → γ} {g : α → β} {a b : β → ℕ} {pT pS : ℕ → ℕ}
    (hpT : Cslib.PolynomiallyBounded pT) (hpS : Cslib.PolynomiallyBounded pS)
    (hcomp : ComputableInO f encH encOut
      (fun q => (2 ^ a q + 1) * (2 ^ b q + 1) * pT (encH q).length)
      (fun q => pS (encH q).length))
    (hg : ComputableInPolyTime g encI encH) :
    ∃ c : NativeCertificate (fun x => f (g x)) encI encOut,
      c.ExpTimePolySpace fun x => a (g x) + b (g x) := by
  obtain ⟨eT, eS, hO⟩ := search_computableInO_preprocess hpT hpS hcomp hg
  let c : NativeCertificate (fun x => f (g x)) encI encOut :=
    ⟨fun x => 2 ^ (a (g x) + b (g x)) * ((encI x).length + 1) ^ eT,
     fun x => ((encI x).length + 1) ^ eS, hO⟩
  refine ⟨c, 1, max eT eS, fun x => ⟨?_, ?_⟩⟩
  · have hsub : 1 ≤ (encI x).length + 1 := Nat.le_add_left 1 _
    calc
      c.time x ≤ 2 ^ (a (g x) + b (g x)) * ((encI x).length + 1) ^ max eT eS :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hsub (le_max_left _ _))
      _ = 1 * 2 ^ (a (g x) + b (g x)) * ((encI x).length + 1) ^ max eT eS := by ring
  · have hsub : 1 ≤ (encI x).length + 1 := Nat.le_add_left 1 _
    calc
      c.space x ≤ ((encI x).length + 1) ^ max eT eS :=
          Nat.pow_le_pow_right hsub (le_max_right _ _)
      _ = 1 * ((encI x).length + 1) ^ max eT eS := (one_mul _).symm

end SearchComplexityHelper

section SmallBias

/-- Computable natural ceiling `⌈4 (r + 1) q² / p²⌉` for bias `ε = p / q`. -/
@[expose]
def smallBiasCeil (r p q : ℕ) : ℕ :=
  (4 * (r + 1) * q ^ 2) ⌈/⌉ (p ^ 2)

/-- `smallBiasCeil r p q` is positive whenever `p > 0` and `q > 0`. -/
theorem smallBiasCeil_pos (r : ℕ) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < smallBiasCeil r p q := by
  have h := Nat.le_ceilDiv_mul (a := 4 * (r + 1) * q ^ 2) (Nat.pow_pos hp (n := 2))
  exact Nat.pos_of_ne_zero fun h0 => by
    rw [smallBiasCeil] at h0
    rw [h0, zero_mul] at h
    nlinarith [Nat.pow_pos hq (n := 2)]

/-- The real ceiling `⌈4 (r + 1) / (p / q)²⌉` is at most `smallBiasCeil r p q`. -/
theorem ceil_le_smallBiasCeil (r : ℕ) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    Nat.ceil (4 * ((r : ℝ) + 1) / ((p : ℝ) / q) ^ 2) ≤ smallBiasCeil r p q := by
  rw [Nat.ceil_le]
  have hp2 : (0 : ℝ) < (p ^ 2 : ℕ) := by exact_mod_cast Nat.pow_pos hp (n := 2)
  have hleNat : 4 * (r + 1) * q ^ 2 ≤ p ^ 2 * smallBiasCeil r p q := by
    rw [mul_comm (p ^ 2)]
    exact Nat.le_ceilDiv_mul (Nat.pow_pos hp (n := 2))
  have hle : ((4 * (r + 1) * q ^ 2 : ℕ) : ℝ) ≤
      (p ^ 2 : ℕ) * ((smallBiasCeil r p q : ℕ) : ℝ) := by
    exact_mod_cast hleNat
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ (by positivity)]
  calc
    4 * ((r : ℝ) + 1) = ((4 * (r + 1) * q ^ 2 : ℕ) : ℝ) / (q : ℝ) ^ 2 := by push_cast; field_simp
    _ ≤ ((p ^ 2 : ℕ) * ((smallBiasCeil r p q : ℕ) : ℝ)) / (q : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hle (by positivity)
    _ = ((smallBiasCeil r p q : ℕ) : ℝ) * ((p : ℝ) / q) ^ 2 := by push_cast; field_simp

/-- Unconditional correctness of `findSmallBiasShifts r d p q` whenever `d ≥ smallBiasCeil r p q`
and `p, q > 0`. -/
theorem isSmallBias_findSmallBiasShifts_of_le {r d p q : ℕ} [NeZero d] (hp : 0 < p) (hq : 0 < q)
    (hd : smallBiasCeil r p q ≤ d) :
    let shifts := findSmallBiasShifts r d p q
    checkSmallBiasShifts r d p q shifts = true ∧
      shifts.length = d ∧ (∀ row ∈ shifts, row.length = r) ∧
      IsSmallBias ((p : ℝ) / q)
        ((uniformOfFintype (Fin d)).map fun j => ofList r (shifts.getD j.val [])) := by
  have hε : (0 : ℝ) < (p : ℝ) / q := div_pos (by exact_mod_cast hp) (by exact_mod_cast hq)
  have hceil : Nat.ceil (4 * ((Fintype.card (Fin r) : ℝ) + 1) / ((p : ℝ) / q) ^ 2) ≤ d := by
    rw [Fintype.card_fin]
    exact (ceil_le_smallBiasCeil r hp hq).trans hd
  exact isSmallBias_findSmallBiasShifts hq (exists_isSmallBias_map_of_ceil_le hε hceil)

/-- Deterministic exhaustive search for `(p / q)`-biased shifts at size `smallBiasCeil r p q`. -/
@[expose]
def findSmallBiasShiftsCeil (r p q : ℕ) : List (List Bool) :=
  findSmallBiasShifts r (smallBiasCeil r p q) p q

/-- Unconditional correctness of `findSmallBiasShiftsCeil r p q` for `p > 0` and `q > 0`. -/
theorem isSmallBias_findSmallBiasShiftsCeil (r : ℕ) {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    let _ : Nonempty (Fin (smallBiasCeil r p q)) :=
      Fin.pos_iff_nonempty.mp (smallBiasCeil_pos r hp hq)
    let shifts := findSmallBiasShiftsCeil r p q
    checkSmallBiasShifts r (smallBiasCeil r p q) p q shifts = true ∧
      shifts.length = smallBiasCeil r p q ∧ (∀ row ∈ shifts, row.length = r) ∧
      IsSmallBias ((p : ℝ) / q)
        ((uniformOfFintype (Fin (smallBiasCeil r p q))).map
          fun j => ofList r (shifts.getD j.val [])) := by
  have hnz : NeZero (smallBiasCeil r p q) := ⟨(smallBiasCeil_pos r hp hq).ne'⟩
  simpa only [findSmallBiasShiftsCeil] using
    isSmallBias_findSmallBiasShifts_of_le (r := r) (d := smallBiasCeil r p q) hp hq le_rfl

private theorem smallBiasCeil_polyTime {α : Type} {encIn : α ↪ List Bool} {r p q : α → ℕ}
    (hr : ComputableInPolyTime r encIn encUnary)
    (hp : ComputableInPolyTime p encIn encUnary)
    (hq : ComputableInPolyTime q encIn encUnary) :
    ComputableInPolyTime (fun a => smallBiasCeil (r a) (p a) (q a)) encIn encUnary := by
  have hnum := unary_mul' (unary_mul' (.const 4) (unary_add' hr (.const 1))) (unary_mul' hq hq)
  have hden := unary_mul' hp hp
  have hdiv := unary_div' (unary_sub' (unary_add' hnum hden) (.const 1)) hden
  have heq : (fun a => (4 * (r a + 1) * (q a * q a) + p a * p a - 1) / (p a * p a)) =
      (fun a => smallBiasCeil (r a) (p a) (q a)) := by
    funext a
    by_cases h0 : p a ^ 2 = 0
    · have hmul : p a * p a = 0 := by simpa only [sq] using h0
      rw [smallBiasCeil, h0, ceilDiv_zero, hmul, Nat.div_zero]
    · rw [smallBiasCeil, Nat.ceilDiv_eq_add_pred_div]
      have hp2 : p a * p a = p a ^ 2 := (sq (p a)).symm
      have hq2 : q a * q a = q a ^ 2 := (sq (q a)).symm
      rw [hp2, hq2]
  rwa [heq] at hdiv

/-- Input parameters for `findSmallBiasShiftsCeil`: cube dimension `r` and bias numerator `p` and
denominator `q` (`ε = p / q`). -/
structure SmallBiasCeilParams where
  /-- Dimension `r` of the Boolean cube `Fin r → Bool`. -/
  r : ℕ
  /-- Bias numerator `p`. -/
  p : ℕ
  /-- Bias denominator `q`. -/
  q : ℕ
  deriving DecidableEq, Repr

/-- Unary encoding of `SmallBiasCeilParams`. -/
enc_structure encSmallBiasCeilParams : SmallBiasCeilParams where
  r : encUnary, p : encUnary, q : encUnary

/-- Native `ComputableInO` certificate for `findSmallBiasShiftsCeil` on unary
`SmallBiasCeilParams`, running in time `2 ^ (smallBiasCeil q.r q.p q.q * q.r + q.r)` times a
polynomial and polynomial space. -/
theorem findSmallBiasShiftsCeil_computableInO :
    ∃ eT eS : ℕ,
      ComputableInO
        (fun q : SmallBiasCeilParams => findSmallBiasShiftsCeil q.r q.p q.q)
        encSmallBiasCeilParams (encList encBits)
        (fun q =>
          2 ^ (smallBiasCeil q.r q.p q.q * q.r + q.r) *
            ((encSmallBiasCeilParams q).length + 1) ^ eT)
        (fun q => ((encSmallBiasCeilParams q).length + 1) ^ eS) := by
  obtain ⟨pT, pS, hpT, hpS, hcomp⟩ := findSmallBiasShifts_computableInO
  let encH := encPair encUnary (encPair encUnary (encPair encNat encNat))
  let hId : ComputableInPolyTime (fun x : SmallBiasCeilParams => x)
      encSmallBiasCeilParams encSmallBiasCeilParams := of_eq fun _ => rfl
  have hr := encSmallBiasCeilParams_r_polyTime hId
  have hp := encSmallBiasCeilParams_p_polyTime hId
  have hq := encSmallBiasCeilParams_q_polyTime hId
  have hd := smallBiasCeil_polyTime hr hp hq
  have hg : ComputableInPolyTime
      (fun x : SmallBiasCeilParams => (x.r, smallBiasCeil x.r x.p x.q, x.p, x.q))
      encSmallBiasCeilParams encH :=
    hr.prod (hd.prod ((unary_to_binary.comp hp).prod (unary_to_binary.comp hq)))
  exact search_computableInO_preprocess hpT hpS
    (a := fun q => q.2.1 * q.1) (b := fun q => q.1) hcomp hg

end SmallBias

section LocalCode

private theorem card_filter_nonzero_weight_lt (d h : ℕ) :
    #{w : Fin d → Bool | w ≠ 0 ∧ weight w ≤ h} < #{w : Fin d → Bool | weight w ≤ h} := by
  refine card_lt_card ⟨fun w hw => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact hw.2
  · have h0w : weight (0 : Fin d → Bool) = 0 := by simp [weight_eq_hammingNorm]
    have h0 : (0 : Fin d → Bool) ∈ ({w : Fin d → Bool | weight w ≤ h} : Finset _) := by
      simp only [mem_filter, mem_univ, true_and, h0w, zero_le]
    have h0' := hsub h0
    simp only [mem_filter, mem_univ, true_and, ne_eq, not_true_eq_false, false_and] at h0'

/-- Unconditional correctness of `findLocalCheckMatrix c d (h + 1)` whenever fewer than `2 ^ c`
nonzero strings in `Fin d → Bool` have weight at most `h`. -/
theorem weight_le_of_findLocalCheckMatrix_of_ball_lt {c d h : ℕ}
    (hball : #{w : Fin d → Bool | w ≠ 0 ∧ weight w ≤ h} < 2 ^ c) :
    let H0 := findLocalCheckMatrix c d (h + 1)
    checkLocalCodeDistance c d (h + 1) H0 = true ∧
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
      ∀ w : Fin d → Bool, w ≠ 0 →
        (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → h + 1 ≤ weight w := by
  refine weight_le_of_findLocalCheckMatrix ?_
  obtain ⟨A, hA⟩ := exists_forall_weight_le hball
  refine ⟨A, fun w hw0 hker => by_contra fun hlt => ?_⟩
  obtain ⟨i, hi⟩ := hA w hw0 (by omega)
  exact Bool.false_ne_true ((hker i).symm.trans hi)

/-- Unconditional correctness of `findLocalCheckMatrix c d (h + 1)` under the Hamming-ball
Gilbert–Varshamov hypothesis `ballSize d h ≤ 2 ^ c` (strictly excluding `0`). -/
theorem weight_le_of_findLocalCheckMatrix_of_ballSize_le {c d h : ℕ}
    (hb : ballSize d h ≤ 2 ^ c) :
    let H0 := findLocalCheckMatrix c d (h + 1)
    checkLocalCodeDistance c d (h + 1) H0 = true ∧
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
      ∀ w : Fin d → Bool, w ≠ 0 →
        (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → h + 1 ≤ weight w := by
  refine weight_le_of_findLocalCheckMatrix_of_ball_lt (lt_of_lt_of_le ?_ hb)
  rw [← card_filter_weight_le_eq_ballSize d h]
  exact card_filter_nonzero_weight_lt d h

/-- Unconditional correctness of `findLocalCheckMatrix c d (h + 1)` under `(d + 1) ^ h ≤ 2 ^ c`
(strict variant `(d + 1) ^ h < 2 ^ c` holds a fortiori). -/
theorem weight_le_of_findLocalCheckMatrix_of_pow_le {c d h : ℕ}
    (hp : (d + 1) ^ h ≤ 2 ^ c) :
    let H0 := findLocalCheckMatrix c d (h + 1)
    checkLocalCodeDistance c d (h + 1) H0 = true ∧
      H0.length = c ∧ (∀ row ∈ H0, row.length = d) ∧
      ∀ w : Fin d → Bool, w ≠ 0 →
        (∀ i : Fin c, ofList d (H0.getD i.val []) ⬝ᵥ w = false) → h + 1 ≤ weight w := by
  refine weight_le_of_findLocalCheckMatrix_of_ball_lt (lt_of_lt_of_le ?_ hp)
  exact lt_of_lt_of_le (card_filter_nonzero_weight_lt d h) (card_filter_weight_le_le d h)

end LocalCode

section EndToEnd

/-- End-to-end deterministic construction of shortened bipartite Tanner parity-check tests from
`(m, r, d, c, h, p, q)`: searches for `(p / q)`-biased `d` shifts in `Fin r → Bool` and a
`c × d` local check matrix of distance at least `h + 1`, then outputs the shortened Tanner rows. -/
@[expose]
def tannerParityTests (m r d c h p q : ℕ) : List (List Bool) :=
  buildShortenedTannerRows m r d c (findSmallBiasShifts r d p q) (findLocalCheckMatrix c d (h + 1))

/-- End-to-end unconditional specification of `tannerParityTests m r d c h p q`:
under `d > 0`, `m ≤ 2 ^ r * d`, `p, q > 0`, small-bias size `smallBiasCeil r p q ≤ d`, and
Gilbert–Varshamov `(d + 1) ^ h ≤ 2 ^ c`, every row has length `m` and weight at most `d`, and
every nonzero kernel word `z : Fin m → Bool` has weight at least `δ * (δ - p / q) * (d * 2 ^ r)`
with `δ = (h + 1) / d`. -/
theorem tannerParityTests_spec {m r d c h p q : ℕ} [NeZero d] (hm : m ≤ 2 ^ r * d)
    (hp : 0 < p) (hq : 0 < q) (hd_bias : smallBiasCeil r p q ≤ d) (hGV : (d + 1) ^ h ≤ 2 ^ c) :
    let rows := tannerParityTests m r d c h p q
    rows.length = 2 * 2 ^ r * c ∧
      (∀ row ∈ rows, row.length = m ∧ row.count true ≤ d) ∧
      ∀ z : Fin m → Bool, z ≠ 0 →
        (∀ row ∈ rows, ofList m row ⬝ᵥ z = false) →
          ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ((p : ℝ) / q) * d) * 2 ^ r ≤ d * weight z ∧
          (((h + 1 : ℕ) : ℝ) / d) * (((h + 1 : ℕ) : ℝ) / d - (p : ℝ) / q) * (d * 2 ^ r) ≤
            weight z := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hsh := (isSmallBias_findSmallBiasShifts_of_le hp hq hd_bias).1
  have hH0 := (weight_le_of_findLocalCheckMatrix_of_pow_le hGV).1
  refine ⟨length_buildShortenedTannerRows m r d c _ _, fun row hrow =>
    ⟨length_mem_buildShortenedTannerRows hrow,
      count_true_mem_buildShortenedTannerRows_le hd_pos hm hrow⟩, fun z hz0 hz => ?_⟩
  have hwt := le_weight_of_buildShortenedTannerRows hq hm hsh hH0 hz0 hz
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd_pos
  refine ⟨hwt, le_of_mul_le_mul_left ?_ hdR⟩
  calc
    (d : ℝ) * ((((h + 1 : ℕ) : ℝ) / d) * (((h + 1 : ℕ) : ℝ) / d - (p : ℝ) / q) * (d * 2 ^ r))
      = ((h + 1 : ℕ) : ℝ) * ((h + 1 : ℕ) - ((p : ℝ) / q) * d) * 2 ^ r := by field_simp
    _ ≤ (d : ℝ) * weight z := hwt

/-- Effective cube dimension clamped by `2 ^ r ≤ max M 1`, used for polynomial-space iteration in
`buildShortenedTannerRows`. Equal to `r` whenever `2 ^ r ≤ M` (`M ≥ 1`). -/
@[expose]
def effectiveCubeDim (M r : ℕ) : ℕ :=
  if 2 ^ r ≤ max M 1 then r else 0

@[simp]
theorem effectiveCubeDim_eq_of_le {M r : ℕ} (hM : 1 ≤ M) (hr : 2 ^ r ≤ M) :
    effectiveCubeDim M r = r := by
  simp [effectiveCubeDim, max_eq_left hM, hr]

/-- Parameterized parity-test builder bounded in output dimension by unary `M`, agreeing with
`tannerParityTests m r d c h p q` whenever `1 ≤ M` and `2 ^ r ≤ M`. -/
@[expose]
def tannerParityTestsWithBound (M m r d c h p q : ℕ) : List (List Bool) :=
  buildShortenedTannerRows m (effectiveCubeDim M r) d c
    (findSmallBiasShifts r d p q) (findLocalCheckMatrix c d (h + 1))

theorem tannerParityTestsWithBound_eq {M m r d c h p q : ℕ} (hM : 1 ≤ M) (hr : 2 ^ r ≤ M) :
    tannerParityTestsWithBound M m r d c h p q = tannerParityTests m r d c h p q := by
  simp [tannerParityTestsWithBound, tannerParityTests, effectiveCubeDim_eq_of_le hM hr]

private theorem two_pow_effectiveCubeDim_le (M r : ℕ) : 2 ^ effectiveCubeDim M r ≤ max M 1 := by
  unfold effectiveCubeDim
  split_ifs with h
  · exact h
  · rw [pow_zero]; exact le_max_right M 1

/-- Input parameters for bounded end-to-end parity-test construction: unary vertex-count upper
bound `maxVerts`, target block length `m`, cube dimension `r`, degree `d`, local check count `c`,
local weight parameter `h` (requiring minimum distance `h + 1`), and binary bias `p / q`. -/
structure TannerParityParams where
  /-- Unary upper bound `M` clamping `2 ^ r ≤ max M 1`. -/
  maxVerts : ℕ
  /-- Shortened target block length `m`. -/
  m : ℕ
  /-- Boolean cube dimension `r` (`2 ^ r` vertices per side). -/
  r : ℕ
  /-- Regularity / local code block length `d`. -/
  d : ℕ
  /-- Number of local parity checks `c` per vertex. -/
  c : ℕ
  /-- Local weight threshold `h` (enforcing minimum distance `≥ h + 1`). -/
  h : ℕ
  /-- Small-bias numerator `p`. -/
  p : ℕ
  /-- Small-bias denominator `q`. -/
  q : ℕ
  deriving DecidableEq, Repr

/-- Mixed unary/binary encoding of `TannerParityParams` (`maxVerts, m, r, d, c, h` unary; `p, q`
binary). -/
enc_structure encTannerParityParams : TannerParityParams where
  maxVerts : encUnary, m : encUnary, r : encUnary, d : encUnary,
  c : encUnary, h : encUnary, p : encNat, q : encNat

/-- End-to-end `ComputableInO` certificate for `tannerParityTestsWithBound` on `TannerParityParams`:
runs in time `2 ^ (d * r + r + c * d + d)` times a polynomial and polynomial space (including the
`O(maxVerts · c · m)` output). -/
theorem tannerParityTests_computableInO :
    ∃ e : ℕ,
      ComputableInO
        (fun q : TannerParityParams =>
          tannerParityTestsWithBound q.maxVerts q.m q.r q.d q.c q.h q.p q.q)
        encTannerParityParams (encList encBits)
        (fun q =>
          2 ^ (q.d * q.r + q.r + (q.c * q.d + q.d)) * ((encTannerParityParams q).length + 1) ^ e)
        (fun q => ((encTannerParityParams q).length + 1) ^ e) := by
  let hId : ComputableInPolyTime (fun x : TannerParityParams => x)
      encTannerParityParams encTannerParityParams := of_eq fun _ => rfl
  have p1 := encTannerParityParams_maxVerts_polyTime hId
  have p2 := encTannerParityParams_m_polyTime hId
  have p3 := encTannerParityParams_r_polyTime hId
  have p4 := encTannerParityParams_d_polyTime hId
  have p5 := encTannerParityParams_c_polyTime hId
  have p6 := encTannerParityParams_h_polyTime hId
  have p7 := encTannerParityParams_p_polyTime hId
  have p8 := encTannerParityParams_q_polyTime hId
  obtain ⟨pT1, pS1, hpT1, hpS1, hcomp1⟩ := findSmallBiasShifts_computableInO
  obtain ⟨c1, hc1⟩ := search_expTimePolySpace hpT1 hpS1
    (a := fun q => q.2.1 * q.1) (b := fun q => q.1) hcomp1 (p3.prod (p4.prod (p7.prod p8)))
  obtain ⟨pT2, pS2, hpT2, hpS2, hcomp2⟩ := findLocalCheckMatrix_computableInO
  obtain ⟨c2, hc2⟩ := search_expTimePolySpace hpT2 hpS2
    (a := fun q => q.1 * q.2.1) (b := fun q => q.2.1) hcomp2
    (p5.prod (p4.prod (unary_add' p6 (.const 1))))
  have hcProd := ((NativeCertificate.expTimePolySpace_ofPolyTime hId (fun _ => 0)).prod
    (hc1.prod hc2)).mono (fun _ => by simp only [zero_add]; exact le_rfl)
  let encMid := encPair encTannerParityParams (encPair (encList encBits) (encList encBits))
  have hFst : ComputableInPolyTime
      (fun x : TannerParityParams × List (List Bool) × List (List Bool) => x.1)
      encMid encTannerParityParams := fst _ _
  have hM_m := encTannerParityParams_maxVerts_polyTime hFst
  have hm_m := encTannerParityParams_m_polyTime hFst
  have hr_m := encTannerParityParams_r_polyTime hFst
  have hd_m := encTannerParityParams_d_polyTime hFst
  have hc_m := encTannerParityParams_c_polyTime hFst
  have hMax_m : ComputableInPolyTime
      (fun x : TannerParityParams × List (List Bool) × List (List Bool) => max x.1.maxVerts 1)
      encMid encUnary := by
    have hite := ite (unary_le' hM_m (.const 1)) (.const 1) hM_m
    have heq : (fun x : TannerParityParams × List (List Bool) × List (List Bool) =>
        if decide (x.1.maxVerts ≤ 1) = true then 1 else x.1.maxVerts) =
        (fun x => max x.1.maxVerts 1) := by
      funext x
      simp only [decide_eq_true_eq, max_def]
    rwa [heq] at hite
  have heff_m : ComputableInPolyTime
      (fun x : TannerParityParams × List (List Bool) × List (List Bool) =>
        effectiveCubeDim x.1.maxVerts x.1.r)
      encMid encUnary := by
    have hite := ite (binary_le.comp ((binary_two_pow.comp hr_m).prod
      (unary_to_binary.comp hMax_m))) hr_m (.const 0)
    have heq : (fun x : TannerParityParams × List (List Bool) × List (List Bool) =>
        if ((fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) ∘
          fun a => (((fun k => 2 ^ k) ∘ fun y => y.1.r) a,
            ((fun n => n) ∘ fun y => max y.1.maxVerts 1) a)) x = true then
          x.1.r
        else 0) =
        (fun x => effectiveCubeDim x.1.maxVerts x.1.r) := by
      funext x
      simp only [Function.comp_apply, decide_eq_true_eq]
      rfl
    rwa [heq] at hite
  have hsh_m := (fst (encList encBits) (encList encBits)).comp' (snd encTannerParityParams _)
  have hlo_m := (snd (encList encBits) (encList encBits)).comp' (snd encTannerParityParams _)
  have hBuild : ComputableInPolyTime
      (fun x : TannerParityParams × List (List Bool) × List (List Bool) =>
        buildShortenedTannerRows x.1.m (effectiveCubeDim x.1.maxVerts x.1.r)
          x.1.d x.1.c x.2.1 x.2.2)
      encMid (encList encBits) :=
    buildShortenedTannerRows_polyTime hm_m heff_m hd_m hc_m hMax_m hsh_m hlo_m
      fun x => two_pow_effectiveCubeDim_le x.1.maxVerts x.1.r
  exact (hcProd.comp_ofPolyTime hBuild).computableInO

end EndToEnd

end Cslib.Complexity.TannerSearch
