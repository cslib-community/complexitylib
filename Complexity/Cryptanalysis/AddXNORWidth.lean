/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Cryptanalysis.AddXNORNPComplete
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Every positive rational width exponent

[WangLvShenZhang2027], Corollary 2, PDF p. 12. For positive integers
`a,b`, pad the actual guard reduction to `N = t^b` operands of width `m = t^a`.
The restriction is checked using integer inequalities, and is proved equivalent
to `m = ceil(N^(a/b))`. Neither hardness nor a desired map is a premise.
-/

public section

namespace Cslib.Cryptanalysis.AddXNOR

open Turing.MultiTapeTM Cslib.Complexity

/-- Exact integer test for the ceiling of a positive rational power. -/
@[expose] def powerShape (a b : ℕ) (p : ℕ × List ℕ) : Bool :=
  decide ((p.1 - 1) ^ b < p.2.length ^ a) && decide (p.2.length ^ a ≤ p.1 ^ b)

/-- The two-parameter decision problem restricted to `m = ceil(N^(a/b))`. -/
@[expose] def PowerDecision (a b : ℕ) : Set (ℕ × List ℕ) :=
  {p | powerShape a b p = true ∧ p ∈ WordDecision}

/-- The integer shape test agrees with the source's real-power ceiling. -/
theorem powerShape_iff {a b m N : ℕ} (hb : 0 < b) (hm : 0 < m) :
    powerShape a b (m, List.replicate N 0) = true ↔
      m = ⌈(N : ℝ) ^ ((a : ℝ) / b)⌉₊ := by
  have hroot : ((N : ℝ) ^ ((a : ℝ) / b)) ^ b = (N : ℝ) ^ a := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    have he : ((a : ℝ) / b) * b = a := by
      have : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
      field_simp
    rw [he, Real.rpow_natCast]
  rw [eq_comm (a := m), Nat.ceil_eq_iff hm.ne']
  simp only [powerShape, List.length_replicate, Bool.and_eq_true, decide_eq_true_eq]
  have hlow := pow_lt_pow_iff_left₀
    (show (0 : ℝ) ≤ (m - 1 : ℕ) by exact_mod_cast Nat.zero_le (m - 1))
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) ((a : ℝ) / b)) hb.ne'
  have hupp := pow_le_pow_iff_left₀ (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ N) ((a : ℝ) / b))
    (show (0 : ℝ) ≤ m by positivity) hb.ne'
  rw [hroot] at hlow hupp
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hlow.1 (by exact_mod_cast hl), hupp.1 (by exact_mod_cast hu)⟩
  · rintro ⟨hl, hu⟩
    exact ⟨by exact_mod_cast hlow.2 hl, by exact_mod_cast hupp.2 hu⟩

/-- The shape restriction is polynomial-time for each fixed exponent pair. -/
@[fun_prop] theorem powerShape_polyTime (a b : ℕ) :
    ComputableInPolyTime (powerShape a b) encInstance encBool := by
  have hm : ComputableInPolyTime (fun p : ℕ × List ℕ => p.1) encInstance encUnary := by fun_prop
  have hN : ComputableInPolyTime (fun p : ℕ × List ℕ => p.2.length) encInstance encUnary :=
    .of_tidy ((ComputableTidilyInPolyTime.length encNat).comp (by fun_prop))
  have hlow := ComputableInPolyTime.binary_pow'
    (ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.unary_sub' hm (.const 1))) (.const b)
  have hmid := ComputableInPolyTime.binary_pow'
    (ComputableInPolyTime.unary_to_binary.comp hN) (.const a)
  have hupp := ComputableInPolyTime.binary_pow'
    (ComputableInPolyTime.unary_to_binary.comp hm) (.const b)
  exact .of_tidy (ComputableTidilyInPolyTime.bool_and'
    (ComputableInPolyTime.binary_lt' hlow hmid).tidy
    (ComputableInPolyTime.binary_le' hmid hupp).tidy)

/-- Membership in NP includes an actual polynomial-time shape check. -/
theorem PowerDecision_mem_NP (a b : ℕ) : PowerDecision a b ∈ NP encInstance := by
  refine ⟨Polynomial.X, (fun p => powerShape a b p.1 && wordVerifier p), ?_,
    wordVerifier_isVerifier.guard⟩
  exact .of_tidy (ComputableTidilyInPolyTime.bool_and'
    ((powerShape_polyTime a b).comp (ComputableInPolyTime.fst encInstance encBits)).tidy
    wordVerifier_polyTime.tidy)

/-- The padded numerical map for the exponent pair. -/
@[expose] def toPowerAddXNOR (a b : ℕ) (x : List ℕ × ℕ) : ℕ × List ℕ :=
  let numbers := positiveNumbers x.1
  let h := numbers.sum.size
  let t := 4 * numbers.length + h + 3
  if x.2 ≤ numbers.sum then
    (t ^ a, rawOperands (t ^ a) (t ^ b - 4 * numbers.length - 2) numbers x.2)
  else (2, [1, 0])

private theorem no_word_instance : (2, [1, 0]) ∉ WordDecision := by
  rintro ⟨_, _, _, bs, hlen, he⟩
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
    at hlen he
  rcases bs with _ | ⟨op, bs⟩
  · simp at hlen
  have : bs = [] := by simpa using hlen
  subst bs
  cases op <;> simp [eval, step] at he

/-- Correctness of the actual padded construction for every source input. -/
theorem toPowerAddXNOR_mem_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (x : List ℕ × ℕ) :
    toPowerAddXNOR a b x ∈ PowerDecision a b ↔ x ∈ SubsetSum := by
  rw [mem_SubsetSum_iff_sublist]
  unfold toPowerAddXNOR
  dsimp only
  split_ifs with ht
  · let numbers := positiveNumbers x.1
    let h := numbers.sum.size
    let t := 4 * numbers.length + h + 3
    have htpos : 2 ≤ t := by dsimp [t]; omega
    have ha' : t ≤ t ^ a := Nat.le_pow ha
    have hb' : t ≤ t ^ b := Nat.le_pow hb
    have hbsize : 4 * numbers.length + 2 ≤ t ^ b := by
      have : 4 * numbers.length + 2 ≤ t := by dsimp [t]; omega
      exact this.trans hb'
    have hlen : (rawOperands (t ^ a) (t ^ b - 4 * numbers.length - 2) numbers x.2).length = t ^ b :=
      by
      rw [rawOperands_eq]
      simp only [List.length_cons, List.length_map]
      have hl := subsetOperands_length (t ^ a) (t ^ b - 4 * numbers.length - 2) numbers x.2
      omega
    have he : (t ^ a) ^ b = (t ^ b) ^ a := by rw [← pow_mul, ← pow_mul, Nat.mul_comm a b]
    have hshape : powerShape a b
        (t ^ a, rawOperands (t ^ a) (t ^ b - 4 * numbers.length - 2) numbers x.2) = true := by
      simp only [powerShape, hlen, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, he.symm.le⟩
      rw [← he]
      exact (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) hb.ne').2 (by omega)
    have hword := rawOperands_mem_WordDecision (q := t ^ b - 4 * numbers.length - 2)
      numbers x.2 ha' (fun s hs => of_decide_eq_true (List.mem_filter.1 hs).2)
      (Nat.lt_size_self _) ht
    change (powerShape a b _ = true ∧ _ ∈ WordDecision) ↔ _
    rw [and_iff_right hshape, hword]
    exact positiveNumbers_sublist_iff x.1 x.2
  · constructor
    · intro h
      exact (no_word_instance h.2).elim
    · rintro ⟨chosen, hc, he⟩
      have hsum : chosen.sum ≤ x.1.sum := hc.sum_le_sum (fun _ _ => Nat.zero_le _)
      rw [positiveNumbers_sum] at ht
      omega

/-- Polynomial time of the padded map for each fixed pair of exponents. -/
@[fun_prop] theorem toPowerAddXNOR_polyTime (a b : ℕ) :
    ComputableInPolyTime (toPowerAddXNOR a b) (encPair (encList encNat) encNat) encInstance := by
  let input := encPair (encList encNat) encNat
  have hnums : ComputableInPolyTime (fun p : List ℕ × ℕ => positiveNumbers p.1)
      input (encList encNat) := by unfold positiveNumbers; fun_prop
  have hsum : ComputableInPolyTime (fun p : List ℕ × ℕ => (positiveNumbers p.1).sum)
      input encNat := by fun_prop
  have hh := ComputableInPolyTime.binary_size.comp hsum
  have hlen : ComputableInPolyTime (fun p : List ℕ × ℕ => (positiveNumbers p.1).length)
      input encUnary := .of_tidy ((ComputableTidilyInPolyTime.length encNat).comp hnums.tidy)
  have ht := ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.unary_add' (ComputableInPolyTime.unary_mul'
      (.const 4) hlen) hh) (.const 3)
  have hM := (ComputableInPolyTime.unary_pow a).comp ht
  have hN := (ComputableInPolyTime.unary_pow b).comp ht
  have hq := ComputableInPolyTime.unary_sub'
    (ComputableInPolyTime.unary_sub' hN (ComputableInPolyTime.unary_mul'
      (.const 4) hlen)) (.const 2)
  have hraw : ComputableInPolyTime
      (fun p : List ℕ × ℕ => rawOperands
        ((4 * (positiveNumbers p.1).length + (positiveNumbers p.1).sum.size + 3) ^ a)
        ((4 * (positiveNumbers p.1).length + (positiveNumbers p.1).sum.size + 3) ^ b -
          4 * (positiveNumbers p.1).length - 2) (positiveNumbers p.1) p.2)
      input (encList encNat) := by
    have harg := ((hM.prod hq).prod hnums).prod (ComputableInPolyTime.snd (encList encNat) encNat)
    have h := rawOperands_polyTime.comp harg
    dsimp only [Function.comp_def] at h
    exact h
  have htest : ComputableInPolyTime
      (fun p : List ℕ × ℕ => decide (p.2 ≤ (positiveNumbers p.1).sum)) input encBool := by fun_prop
  have h := htest.ite (hM.prod hraw) (.const (2, [1, 0]))
  unfold toPowerAddXNOR
  dsimp only
  change ComputableInPolyTime _ input (encPair encUnary (encList encNat))
  simpa only [decide_eq_true_eq, Function.comp_def] using h

/-- Corollary 2: every fixed positive rational width exponent `a/b` gives an
NP-complete restriction, with a computable integer shape test. -/
theorem PowerDecision_npComplete (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    NPComplete encInstance (PowerDecision a b) :=
  ⟨PowerDecision_mem_NP a b, SubsetSum_npHard.trans
    ⟨toPowerAddXNOR a b, toPowerAddXNOR_polyTime a b,
      fun x => (toPowerAddXNOR_mem_iff a b ha hb x).symm⟩⟩

/-- Every positive rational exponent, stated using the source's ceiling
relation itself, rather than only an integer-power presentation. -/
theorem rational_width_npComplete (δ : ℚ) (hδ : 0 < δ) :
    NPComplete encInstance {p : ℕ × List ℕ |
      p.1 = ⌈(p.2.length : ℝ) ^ (δ : ℝ)⌉₊ ∧ p ∈ WordDecision} := by
  have ha : 0 < δ.num.toNat := by
    have := Rat.num_pos.2 hδ
    omega
  have hcast : ((δ.num.toNat : ℝ) / δ.den) = (δ : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hδ.le)
  have he : PowerDecision δ.num.toNat δ.den = {p : ℕ × List ℕ |
      p.1 = ⌈(p.2.length : ℝ) ^ (δ : ℝ)⌉₊ ∧ p ∈ WordDecision} := by
    ext p
    constructor
    · rintro ⟨hshape, hw⟩
      have hh := powerShape_iff (a := δ.num.toNat) (b := δ.den) (m := p.1)
        (N := p.2.length) δ.den_pos (by have := hw.1; omega)
      rw [hcast] at hh
      refine ⟨hh.1 ?_, hw⟩
      simpa only [powerShape, List.length_replicate] using hshape
    · rintro ⟨hshape, hw⟩
      have hh := powerShape_iff (a := δ.num.toNat) (b := δ.den) (m := p.1)
        (N := p.2.length) δ.den_pos (by have := hw.1; omega)
      rw [hcast] at hh
      refine ⟨?_, hw⟩
      simpa only [powerShape, List.length_replicate] using hh.2 hshape
  rw [← he]
  exact PowerDecision_npComplete δ.num.toNat δ.den ha δ.den_pos


end Cslib.Cryptanalysis.AddXNOR
