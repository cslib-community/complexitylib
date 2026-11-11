/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AverageCase.Ensemble
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeBinaryDivision
import CslibFrontier.Foundations.Data.Nat.Bitwise.CommonPrefix
import CslibFrontier.Tactic.PolyTime

/-!
# Compressing samples of a polynomial-time computable ensemble

[Bogdanov and Trevisan, Claim 20][BogdanovTrevisan2006]: for a polynomial-time computable ensemble
`D` there is a polynomial-time code `C`, injective on the words of each length, with
`|C(x)| ≤ 1 + min(|x|, log (1/D_n(x)))`. This is the step of Levin's completeness theorem that
makes samples of `D` almost uniform.

Let `a = D_n({y < x})` and `b = D_n({y ≤ x})`, so `D_n(x) = b - a`. A word with
`D_n(x) ≤ 2^{-n}` is coded as `0x`. Otherwise `C(x) = 1z`, where `z` is a binary word naming a
dyadic point strictly between `a` and `b` whose length `n - s` satisfies `2^{-(n-s)} ≥ b - a`; since
the intervals `(a, b]` of distinct words are disjoint, distinct heavy words get distinct codes.
The source takes `z` to be the longest common prefix of the infinite binary expansions of `a` and
`b`. Here `z` is the longest common prefix of the `n`-bit words of `A = ⌊a 2^n⌋` and
`B = ⌈b 2^n⌉ - 1`, computed exactly from the numerators and denominators of the cumulative
distribution (`Nat.lt_commonPrefix_mid_le`), so the code needs only finitely many bits.

## Main definitions

* `Cslib.Complexity.Compression.compress`: the code `C`, from a numerator and a denominator of the
  cumulative distribution.

## Main results

* `Cslib.Complexity.Compression.compress_polyTime`: `C` is computable in polynomial time.
* `Cslib.Complexity.Compression.length_compress_le`: `|C(x)| ≤ |x| + 1`.
* `Cslib.Complexity.Compression.two_pow_length_compress_mul_le`: `2^{|C(x)|} D_n(x) ≤ 2`, that is
  `|C(x)| ≤ 1 + log (1/D_n(x))`.
* `Cslib.Complexity.Compression.compress_injective`: `C` is injective on the words of each length
  (on all of them, not only those in the support of `D_n`).

## References

* [A. Bogdanov, L. Trevisan, *Average-Case Complexity*][BogdanovTrevisan2006]
-/

public section

namespace Cslib.Complexity

open scoped ENNReal
open Turing.MultiTapeTM

/-- The fixed-width binary word of a computed number is computable in polynomial time. -/
theorem binaryWord_polyTime {α : Type} {input : α ↪ List Bool} {w a : α → ℕ}
    (hw : ComputableInPolyTime w input encUnary) (ha : ComputableInPolyTime a input encNat) :
    ComputableInPolyTime (fun x => BitString.binaryWord (w x) (a x)) input encBits := by
  have hbits := (ComputableInPolyTime.of_eq (f := Nat.bits)
    (encIn := encNat) (encOut := encBits) fun _ => rfl).comp ha
  have hpadding := ComputableInPolyTime.unary_sub.comp
    (hw.prod (ComputableInPolyTime.length_bits.comp hbits))
  have hplain := ComputableInPolyTime.bitsAppend
    ((ComputableInPolyTime.bitsReplicate false).comp hpadding)
    (ComputableInPolyTime.bitsReverse.comp hbits)
  simpa only [BitString.binaryWord, Function.comp_def] using hplain

namespace Compression

variable (num den : List Bool → ℕ)

/-- The numerator of `D_n({y < x})`: that of the cumulative distribution at the predecessor of `x`,
or `0` at the least word. -/
def loNum (x : List Bool) : ℕ :=
  if decide (BitString.binaryValue x = 0) then 0 else num (BitString.predWord x)

/-- The denominator of `D_n({y < x})`, matching `Cslib.Complexity.Compression.loNum`. -/
def loDen (x : List Bool) : ℕ :=
  if decide (BitString.binaryValue x = 0) then 1 else den (BitString.predWord x)

/-- The numerator of `a = D_n({y < x})` over the common denominator `cQ`. -/
def cP (x : List Bool) : ℕ := loNum num x * den x

/-- The numerator of `b = D_n({y ≤ x})` over the common denominator `cQ`. -/
def cR (x : List Bool) : ℕ := num x * loDen den x

/-- The common denominator of `a` and `b`. -/
def cQ (x : List Bool) : ℕ := loDen den x * den x

/-- `A = ⌊a 2^n⌋`. -/
def cA (x : List Bool) : ℕ := cP num den x * 2 ^ x.length / cQ den x

/-- `B = ⌈b 2^n⌉ - 1`. -/
def cB (x : List Bool) : ℕ := (cR num den x * 2 ^ x.length - 1) / cQ den x

/-- The number `s` of low bits after the longest common prefix of the `n`-bit words of `A`
and `B`. -/
def cS (x : List Bool) : ℕ := (cA num den x ^^^ cB num den x).size

/-- `x` is *heavy* when `a 2^n + 1 < b 2^n`, that is `D_n(x) > 2^{-n}`. -/
def heavy (x : List Bool) : Bool :=
  decide (cP num den x * 2 ^ x.length + cQ den x < cR num den x * 2 ^ x.length)

/-- **The code of Claim 20**: `1z` for a heavy word, with `z` the common prefix of the `n`-bit words
of `A` and `B`, and `0x` otherwise. -/
def compress (x : List Bool) : List Bool :=
  if heavy num den x then
    true :: BitString.binaryWord (x.length - cS num den x) (cA num den x / 2 ^ cS num den x)
  else false :: x

variable {num den}

/-- The predecessor of a word is computable in polynomial time. -/
theorem predWord_polyTime : ComputableInPolyTime BitString.predWord encBits encBits := by
  unfold BitString.predWord
  exact binaryWord_polyTime ComputableInPolyTime.length_bits
    (ComputableInPolyTime.binary_sub' ComputableInPolyTime.bitsBinaryValue
      (ComputableInPolyTime.const 1))

/-- **Claim 20, running time.** The code is computable in polynomial time when the cumulative
distribution is. -/
theorem compress_polyTime (hnum : ComputableInPolyTime num encBits encNat)
    (hden : ComputableInPolyTime den encBits encNat) :
    ComputableInPolyTime (compress num den) encBits encBits := by
  have hpred := predWord_polyTime
  have hlo : ComputableInPolyTime (loNum num) encBits encNat := by
    unfold loNum
    polytime
  have hloD : ComputableInPolyTime (loDen den) encBits encNat := by
    unfold loDen
    polytime
  have hP : ComputableInPolyTime (cP num den) encBits encNat := by unfold cP; polytime
  have hR : ComputableInPolyTime (cR num den) encBits encNat := by unfold cR; polytime
  have hQ : ComputableInPolyTime (cQ den) encBits encNat := by unfold cQ; polytime
  have h2 : ComputableInPolyTime (fun x : List Bool => 2 ^ x.length) encBits encNat :=
    ComputableInPolyTime.binary_two_pow.comp ComputableInPolyTime.length_bits
  have hA : ComputableInPolyTime (cA num den) encBits encNat := by
    have : ComputableInPolyTime (fun x => cP num den x * 2 ^ x.length) encBits encNat := by
      polytime
    exact ComputableInPolyTime.binary_div.comp (this.prod hQ)
  have hB : ComputableInPolyTime (cB num den) encBits encNat := by
    have : ComputableInPolyTime (fun x => cR num den x * 2 ^ x.length - 1) encBits encNat :=
      ComputableInPolyTime.binary_sub' (by polytime) (ComputableInPolyTime.const 1)
    exact ComputableInPolyTime.binary_div.comp (this.prod hQ)
  have hS : ComputableInPolyTime (cS num den) encBits encUnary := by
    unfold cS
    exact ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.binary_xor' hA hB)
  have hH : ComputableInPolyTime (heavy num den) encBits encBool := by
    unfold heavy
    have h1 : ComputableInPolyTime (fun x => cP num den x * 2 ^ x.length) encBits encNat := by
      polytime
    have h2 : ComputableInPolyTime (fun x => cR num den x * 2 ^ x.length) encBits encNat := by
      polytime
    exact ComputableInPolyTime.binary_lt' (ComputableInPolyTime.binary_add.comp (h1.prod hQ)) h2
  have hZ : ComputableInPolyTime (fun x => cA num den x / 2 ^ cS num den x) encBits encNat := by
    exact ComputableInPolyTime.binary_div.comp
      (hA.prod (ComputableInPolyTime.binary_two_pow.comp hS))
  have hW : ComputableInPolyTime (fun x => x.length - cS num den x) encBits encUnary := by
    polytime
  unfold compress
  have := binaryWord_polyTime hW hZ
  polytime

/-- The arithmetic core of Claim 20: for `A = ⌊a 2^n⌋` and `B = ⌈b 2^n⌉ - 1` with a gap
`a 2^n + 1 < b 2^n`, the dyadic point `M = (2Z+1) 2^{s-1}` determined by the longest common
prefix of `A` and `B` lies strictly between `a 2^n` and `b 2^n`, and `(b - a) 2^n ≤ 2^s`. -/
private theorem core {A B n : ℕ} {a b : ℝ}
    (hA : (A : ℝ) ≤ a * 2 ^ n) (hA' : a * 2 ^ n < A + 1)
    (hB : (B : ℝ) < b * 2 ^ n) (hB' : b * 2 ^ n ≤ B + 1)
    (hgap : a * 2 ^ n + 1 < b * 2 ^ n) (hb1 : b ≤ 1) :
    A < 2 ^ n ∧ (A ^^^ B).size ≤ n ∧
      a * 2 ^ n < (((2 * (A / 2 ^ (A ^^^ B).size) + 1) * 2 ^ ((A ^^^ B).size - 1) : ℕ) : ℝ) ∧
      (((2 * (A / 2 ^ (A ^^^ B).size) + 1) * 2 ^ ((A ^^^ B).size - 1) : ℕ) : ℝ) < b * 2 ^ n ∧
      (b - a) * 2 ^ n ≤ 2 ^ (A ^^^ B).size := by
  have hAB : A < B := by
    have : (A : ℝ) < B := by linarith
    exact_mod_cast this
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hBn : B < 2 ^ n := by
    have h1 := mul_le_mul_of_nonneg_right hb1 h2n.le
    have : (B : ℝ) < 2 ^ n := by linarith
    exact_mod_cast this
  have hAn : A < 2 ^ n := hAB.trans hBn
  obtain ⟨hs1, heq, hM1, hM2⟩ := Nat.lt_commonPrefix_mid_le hAB
  set s := (A ^^^ B).size with hs
  have hsn : s ≤ n := Nat.size_le.mpr (Nat.xor_lt_two_pow hAn hBn)
  set Z := A / 2 ^ s with hZ
  have hZA : Z * 2 ^ s ≤ A := Nat.div_mul_le_self A _
  have hBZ : B < (Z + 1) * 2 ^ s := by
    have := Nat.lt_mul_div_succ B (show 0 < 2 ^ s by positivity)
    rw [← heq, mul_comm] at this
    exact this
  refine ⟨hAn, hsn, ?_, ?_, ?_⟩
  · have : (A : ℝ) + 1 ≤ (((2 * Z + 1) * 2 ^ (s - 1) : ℕ) : ℝ) := by exact_mod_cast hM1
    linarith
  · have : (((2 * Z + 1) * 2 ^ (s - 1) : ℕ) : ℝ) ≤ B := by exact_mod_cast hM2
    linarith
  · have h1 : ((B : ℝ) + 1) ≤ (((Z + 1) * 2 ^ s : ℕ) : ℝ) := by exact_mod_cast hBZ
    have h2 : (((Z * 2 ^ s : ℕ)) : ℝ) ≤ A := by exact_mod_cast hZA
    push_cast at h1 h2
    nlinarith

private theorem natCast_div_eq_ofReal {p q : ℕ} (hq : q ≠ 0) :
    (p : ℝ≥0∞) / q = ENNReal.ofReal ((p : ℝ) / q) := by
  rw [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hq)),
    ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]

variable (num den) in
/-- The real lower cumulative value `D_n(\{y < x\})`. -/
noncomputable def aR (x : List Bool) : ℝ := (loNum num x : ℝ) / loDen den x

variable (num den) in
/-- The real cumulative value `D_n(\{y ≤ x\})`. -/
noncomputable def bR (x : List Bool) : ℝ := (num x : ℝ) / den x

/-- The lower denominator is nonzero. -/
theorem loDen_ne_zero (hden : ∀ x, den x ≠ 0) (x : List Bool) : loDen den x ≠ 0 := by
  unfold loDen
  split
  · exact one_ne_zero
  · exact hden _

section Spec

variable {D : Ensemble} (hcdf : ∀ x, D.cdf x = (num x : ℝ≥0∞) / den x) (hden : ∀ x, den x ≠ 0)
include hcdf hden

/-- `D_n({y < x}) = a`. -/
theorem cdfLo_eq (x : List Bool) : D.cdfLo x = ENNReal.ofReal (aR num den x) := by
  unfold aR loNum loDen
  by_cases h : BitString.binaryValue x = 0
  · rw [D.cdfLo_of_binaryValue_eq_zero h]
    simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    rw [D.cdfLo_eq_cdf_predWord h, hcdf, natCast_div_eq_ofReal (hden _)]

/-- `D_n({y ≤ x}) = b`. -/
theorem cdf_eq (x : List Bool) : D.cdf x = ENNReal.ofReal (bR num den x) := by
  rw [hcdf, natCast_div_eq_ofReal (hden x)]
  rfl

omit hcdf hden in
theorem aR_nonneg (x : List Bool) : 0 ≤ aR num den x := by
  unfold aR; positivity

omit hcdf hden in
theorem bR_nonneg (x : List Bool) : 0 ≤ bR num den x := by
  unfold bR; positivity

theorem bR_le_one (x : List Bool) : bR num den x ≤ 1 := by
  have := D.cdf_le_one x
  rw [cdf_eq hcdf hden] at this
  exact ENNReal.ofReal_le_one.mp this

/-- `D_n(x) = b - a`. -/
theorem dist_eq (x : List Bool) :
    D.dist x.length x = ENNReal.ofReal (bR num den x - aR num den x) := by
  have h := D.cdf_eq_cdfLo_add x
  rw [cdf_eq hcdf hden, cdfLo_eq hcdf hden] at h
  rw [ENNReal.ofReal_sub _ (aR_nonneg x), h, add_comm,
    ENNReal.add_sub_cancel_right ENNReal.ofReal_ne_top]

theorem aR_le_bR (x : List Bool) : aR num den x ≤ bR num den x := by
  have h := D.cdf_eq_cdfLo_add x
  rw [cdf_eq hcdf hden, cdfLo_eq hcdf hden] at h
  have : ENNReal.ofReal (aR num den x) ≤ ENNReal.ofReal (bR num den x) := by
    rw [h]; exact le_self_add
  exact (ENNReal.ofReal_le_ofReal_iff (bR_nonneg x)).mp this

omit hcdf in
theorem aR_mul_eq (x : List Bool) : aR num den x * 2 ^ x.length =
    ((cP num den x * 2 ^ x.length : ℕ) : ℝ) / cQ den x := by
  have hd : (den x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hden x)
  have hl : (loDen den x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (loDen_ne_zero hden x)
  unfold aR cP cQ
  push_cast
  field_simp

omit hcdf in
theorem bR_mul_eq (x : List Bool) : bR num den x * 2 ^ x.length =
    ((cR num den x * 2 ^ x.length : ℕ) : ℝ) / cQ den x := by
  have hd : (den x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hden x)
  have hl : (loDen den x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (loDen_ne_zero hden x)
  unfold bR cR cQ
  push_cast
  field_simp

omit hcdf in
theorem cQ_pos (x : List Bool) : 0 < cQ den x :=
  Nat.mul_pos (Nat.pos_of_ne_zero (loDen_ne_zero hden x)) (Nat.pos_of_ne_zero (hden x))

omit hcdf in
/-- A word is heavy exactly when `a 2^n + 1 < b 2^n`. -/
theorem heavy_iff (x : List Bool) : heavy num den x = true ↔
    aR num den x * 2 ^ x.length + 1 < bR num den x * 2 ^ x.length := by
  have hQ : (0 : ℝ) < cQ den x := Nat.cast_pos.mpr (cQ_pos hden x)
  rw [aR_mul_eq hden, bR_mul_eq hden, div_add_one hQ.ne', div_lt_div_iff_of_pos_right hQ]
  unfold heavy
  rw [decide_eq_true_iff, ← Nat.cast_lt (α := ℝ)]
  push_cast
  rfl

omit hcdf in
/-- `A ≤ a 2^n < A + 1`. -/
theorem cA_bounds (x : List Bool) : (cA num den x : ℝ) ≤ aR num den x * 2 ^ x.length ∧
    aR num den x * 2 ^ x.length < cA num den x + 1 := by
  have hQ := cQ_pos hden x
  have hQ' : (0 : ℝ) < cQ den x := Nat.cast_pos.mpr hQ
  have h1 : cA num den x * cQ den x ≤ cP num den x * 2 ^ x.length := Nat.div_mul_le_self _ _
  have h2 : cP num den x * 2 ^ x.length < cA num den x * cQ den x + cQ den x :=
    Nat.lt_div_mul_add hQ
  rw [aR_mul_eq hden]
  constructor
  · rw [le_div_iff₀ hQ']; exact_mod_cast h1
  · rw [div_lt_iff₀ hQ']
    have : ((cP num den x * 2 ^ x.length : ℕ) : ℝ) < cA num den x * cQ den x + cQ den x := by
      exact_mod_cast h2
    linarith

omit hcdf in
/-- `B < b 2^n ≤ B + 1` for a heavy word. -/
theorem cB_bounds (x : List Bool) (hh : heavy num den x = true) :
    (cB num den x : ℝ) < bR num den x * 2 ^ x.length ∧
    bR num den x * 2 ^ x.length ≤ cB num den x + 1 := by
  have hQ := cQ_pos hden x
  have hQ' : (0 : ℝ) < cQ den x := Nat.cast_pos.mpr hQ
  have hpos : 0 < cR num den x * 2 ^ x.length := by
    unfold heavy at hh
    rw [decide_eq_true_iff] at hh
    omega
  have h1 : cB num den x * cQ den x ≤ cR num den x * 2 ^ x.length - 1 := Nat.div_mul_le_self _ _
  have h2 : cR num den x * 2 ^ x.length - 1 < cB num den x * cQ den x + cQ den x :=
    Nat.lt_div_mul_add hQ
  have h1' : cB num den x * cQ den x < cR num den x * 2 ^ x.length := by omega
  have h2' : cR num den x * 2 ^ x.length ≤ (cB num den x + 1) * cQ den x := by
    rw [add_mul, one_mul]; omega
  rw [bR_mul_eq hden]
  constructor
  · rw [lt_div_iff₀ hQ']; exact_mod_cast h1'
  · rw [div_le_iff₀ hQ']; exact_mod_cast h2'

/-- The facts about a word of large probability used by Claim 20. -/
theorem heavy_spec (x : List Bool) (hh : heavy num den x = true) :
    cS num den x ≤ x.length ∧
    cA num den x / 2 ^ cS num den x < 2 ^ (x.length - cS num den x) ∧
    aR num den x * 2 ^ x.length <
      (((2 * (cA num den x / 2 ^ cS num den x) + 1) * 2 ^ (cS num den x - 1) : ℕ) : ℝ) ∧
    (((2 * (cA num den x / 2 ^ cS num den x) + 1) * 2 ^ (cS num den x - 1) : ℕ) : ℝ) <
      bR num den x * 2 ^ x.length ∧
    (bR num den x - aR num den x) * 2 ^ (x.length - cS num den x) ≤ 1 := by
  obtain ⟨hA, hA'⟩ := cA_bounds hden x
  obtain ⟨hB, hB'⟩ := cB_bounds hden x hh
  have hgap := (heavy_iff hden x).mp hh
  obtain ⟨hAn, hsn, hM1, hM2, hlen⟩ := core hA hA' hB hB' hgap (bR_le_one hcdf hden x)
  have hS : cS num den x = (cA num den x ^^^ cB num den x).size := rfl
  rw [← hS] at hsn hM1 hM2 hlen
  have hsplit : (2 : ℕ) ^ x.length = 2 ^ (x.length - cS num den x) * 2 ^ cS num den x := by
    rw [← pow_add, Nat.sub_add_cancel hsn]
  refine ⟨hsn, ?_, hM1, hM2, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul (by positivity), ← hsplit]
    exact hAn
  · have hsplit' : (2 : ℝ) ^ x.length = 2 ^ (x.length - cS num den x) * 2 ^ cS num den x := by
      exact_mod_cast hsplit
    rw [hsplit', ← mul_assoc] at hlen
    have h2s : (0 : ℝ) < 2 ^ cS num den x := by positivity
    exact le_of_mul_le_mul_right (by linarith) h2s

end Spec

section Claim

variable {D : Ensemble} (hcdf : ∀ x, D.cdf x = (num x : ℝ≥0∞) / den x) (hden : ∀ x, den x ≠ 0)
include hcdf hden

/-- **Claim 20, length.** `|C(x)| ≤ |x| + 1`. -/
theorem length_compress_le (x : List Bool) : (compress num den x).length ≤ x.length + 1 := by
  unfold compress
  split
  · next hh =>
    obtain ⟨-, hZ, -⟩ := heavy_spec hcdf hden x hh
    rw [List.length_cons, BitString.length_binaryWord hZ]
    omega
  · rw [List.length_cons]

/-- **Claim 20, compression.** `2^{|C(x)|} D_{|x|}(x) ≤ 2`, that is `|C(x)| ≤ 1 + log (1/D(x))`. -/
theorem two_pow_length_compress_mul_le (x : List Bool) :
    (2 : ℝ≥0∞) ^ (compress num den x).length * D.dist x.length x ≤ 2 := by
  rw [dist_eq hcdf hden, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  unfold compress
  split
  · next hh =>
    obtain ⟨-, hZ, -, -, hlen⟩ := heavy_spec hcdf hden x hh
    rw [List.length_cons, BitString.length_binaryWord hZ, pow_succ]
    nlinarith
  · next hh =>
    have : ¬ (aR num den x * 2 ^ x.length + 1 < bR num den x * 2 ^ x.length) :=
      fun h => hh ((heavy_iff hden x).mpr h)
    rw [List.length_cons, pow_succ]
    nlinarith

/-- Heavy words of the same length with distinct values have distinct codes. -/
theorem not_compress_eq_of_lt {x x' : List Bool} (hlen : x.length = x'.length)
    (hh : heavy num den x = true) (hh' : heavy num den x' = true)
    (hlt : BitString.binaryValue x < BitString.binaryValue x')
    (h : compress num den x = compress num den x') : False := by
  obtain ⟨hs, hZ, -, hM2, -⟩ := heavy_spec hcdf hden x hh
  obtain ⟨hs', hZ', hM1', -, -⟩ := heavy_spec hcdf hden x' hh'
  simp only [compress, hh, hh', ite_true, List.cons.injEq, true_and] at h
  have hl := congrArg List.length h
  rw [BitString.length_binaryWord hZ, BitString.length_binaryWord hZ'] at hl
  have hss : cS num den x = cS num den x' := by omega
  have hv := congrArg BitString.binaryValue h
  rw [BitString.binaryValue_binaryWord, BitString.binaryValue_binaryWord] at hv
  rw [hv, hss, hlen] at hM2
  have hba : bR num den x ≤ aR num den x' := by
    have := D.cdf_le_cdfLo hlen hlt
    rw [cdf_eq hcdf hden, cdfLo_eq hcdf hden] at this
    exact (ENNReal.ofReal_le_ofReal_iff (aR_nonneg x')).mp this
  have := mul_le_mul_of_nonneg_right hba (by positivity : (0 : ℝ) ≤ 2 ^ x'.length)
  linarith

/-- **Claim 20, injectivity.** The code is injective on words of each length (on all of them,
not only on the support of `D_n`). -/
theorem compress_injective {x x' : List Bool} (hlen : x.length = x'.length)
    (h : compress num den x = compress num den x') : x = x' := by
  cases hh : heavy num den x <;> cases hh' : heavy num den x'
  · simpa [compress, hh, hh'] using h
  · simp [compress, hh, hh'] at h
  · simp [compress, hh, hh'] at h
  · rcases lt_trichotomy (BitString.binaryValue x) (BitString.binaryValue x') with hlt | heq | hgt
    · exact (not_compress_eq_of_lt hcdf hden hlen hh hh' hlt h).elim
    · exact BitString.binaryValue_injective_of_length_eq hlen heq
    · exact (not_compress_eq_of_lt hcdf hden hlen.symm hh' hh hgt h.symm).elim

end Claim

end Compression

end Cslib.Complexity
