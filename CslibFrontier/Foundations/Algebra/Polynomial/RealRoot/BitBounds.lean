/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.Isolation
public import CslibFrontier.Foundations.Data.Nat.BinarySize

/-!
# Coefficient Bit-Size and Dyadic Endpoint Bounds for Real-Root Isolation

This module bounds the Cauchy root bound, cleared-denominator coefficient norm, Mignotte bisection
depth, and output rational interval endpoints in terms of input length `cs.length` and an input
coefficient bit-length bound `B`.

## Main definitions

* `Cslib.RealRoot.HasCoeffBitBound`: predicate asserting `Int.natAbs q.num ≤ 2 ^ B` and
  `q.den ≤ 2 ^ B` for every `q ∈ cs`.
* `Cslib.RealRoot.coeffBitBound`: computable bit-length bound satisfying
  `HasCoeffBitBound (coeffBitBound cs) cs`.
* `Cslib.RealRoot.DyadicBounded`: predicate asserting `q = (z : ℚ) / 2 ^ e` with
  `Int.natAbs z ≤ b * 2 ^ e`.

## Main results

* `Cslib.RealRoot.cauchyBoundNat_le_of_bitBound`,
  `Cslib.RealRoot.lcmDens_le_of_bitBound`,
  `Cslib.RealRoot.sqNormList_clearDenoms_le_of_bitBound`: explicit bounds on preprocessing
  quantities from `HasCoeffBitBound B cs`.
* `Cslib.RealRoot.mignotteBisectionDepth_le_of_bitBound`: unconditional polynomial bound
  `mignotteBisectionDepth cs ≤ (cs.length + 2) ^ 2 * (B + 2)`.
* `Cslib.RealRoot.DyadicBounded.den_le`, `Cslib.RealRoot.DyadicBounded.natAbs_num_le`,
  and `Cslib.RealRoot.isolateRoots_dyadicBounded`: dyadic numerator and denominator bounds on all
  endpoints produced by Sturm bisection.

## References

* [BasuPollackRoy2006] (locator unverified)
* [Mahler1964], pp. 257–262 (locator unverified)
* [Mignotte1982], pp. 259–263 (locator unverified; `HasCoeffBitBound`, `DyadicBounded`, and
  `mignotteBisectionDepth_le_of_bitBound` are specific to this module)
-/

public section

namespace Cslib.RealRoot

open Polynomial Cslib.Algorithms.Lean

/-- Every rational entry `q ∈ cs` has numerator and denominator bounded by `2 ^ B`. -/
@[expose] def HasCoeffBitBound (B : ℕ) (cs : List ℚ) : Prop :=
  ∀ q ∈ cs, Int.natAbs q.num ≤ 2 ^ B ∧ q.den ≤ 2 ^ B

/-- Computable bit-length bound on all numerators and denominators in `cs`. -/
@[expose] def coeffBitBound (cs : List ℚ) : ℕ :=
  cs.foldl (fun acc q => max acc (max (Int.natAbs q.num).size q.den.size)) 0

private theorem foldl_coeffBitBound_ge (cs : List ℚ) (init : ℕ) :
    init ≤ cs.foldl (fun acc q => max acc (max (Int.natAbs q.num).size q.den.size)) init := by
  induction cs generalizing init with
  | nil => exact le_rfl
  | cons q qs ih =>
    simp only [List.foldl_cons]
    exact (le_max_left _ _).trans (ih _)

/-- Every coefficient list `cs` satisfies `HasCoeffBitBound (coeffBitBound cs) cs`. -/
theorem hasCoeffBitBound_coeffBitBound (cs : List ℚ) :
    HasCoeffBitBound (coeffBitBound cs) cs := by
  have haux : ∀ (qs : List ℚ) (init : ℕ) (q : ℚ), q ∈ qs →
      let M := qs.foldl (fun acc r => max acc (max (Int.natAbs r.num).size r.den.size)) init
      Int.natAbs q.num ≤ 2 ^ M ∧ q.den ≤ 2 ^ M := by
    intro qs
    induction qs with
    | nil => intro _ _ hq; cases hq
    | cons a as ih =>
      intro init q hq
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hq with rfl | hmem
      · have hle := foldl_coeffBitBound_ge as
          (max init (max (Int.natAbs q.num).size q.den.size))
        have hn_sz : (Int.natAbs q.num).size ≤
            as.foldl (fun acc r => max acc (max (Int.natAbs r.num).size r.den.size))
              (max init (max (Int.natAbs q.num).size q.den.size)) :=
          ((le_max_left _ _).trans (le_max_right _ _)).trans hle
        have hd_sz : q.den.size ≤
            as.foldl (fun acc r => max acc (max (Int.natAbs r.num).size r.den.size))
              (max init (max (Int.natAbs q.num).size q.den.size)) :=
          ((le_max_right _ _).trans (le_max_right _ _)).trans hle
        exact ⟨(Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right zero_lt_two hn_sz),
          (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right zero_lt_two hd_sz)⟩
      · exact ih _ q hmem
  intro q hq
  exact haux cs 0 q hq

private theorem mem_of_mem_trim {q : ℚ} {cs : List ℚ} (hq : q ∈ trim cs) : q ∈ cs := by
  induction cs with
  | nil => simp only [trim, List.not_mem_nil] at hq
  | cons a as ih =>
    simp only [trim] at hq
    by_cases he : (trim as).isEmpty = true
    · simp only [he, ↓reduceIte] at hq
      by_cases ha : a = 0
      · simp only [ha, ↓reduceIte, List.not_mem_nil] at hq
      · rw [ite_eq_right (fun h => absurd h ha), List.mem_singleton] at hq
        subst hq
        exact List.mem_cons_self
    · simp only [he, Bool.false_eq_true, ↓reduceIte, List.mem_cons] at hq
      rcases hq with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (ih hmem)

/-- `HasCoeffBitBound B` is preserved by `trim`. -/
theorem HasCoeffBitBound.trim {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    HasCoeffBitBound B (Cslib.RealRoot.trim cs) :=
  fun q hq => hB q (mem_of_mem_trim hq)

private theorem abs_rat_le_two_pow {B : ℕ} {q : ℚ} (hn : Int.natAbs q.num ≤ 2 ^ B) :
    |q| ≤ (2 : ℚ) ^ B := by
  have hden_ge : (1 : ℚ) ≤ (q.den : ℚ) := by exact_mod_cast q.den_pos
  have hnum_eq : |(q.num : ℚ)| = (Int.natAbs q.num : ℚ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  calc |q| = |(q.num : ℚ) / (q.den : ℚ)| := by rw [Rat.num_div_den]
    _ = |(q.num : ℚ)| / |(q.den : ℚ)| := abs_div _ _
    _ = (Int.natAbs q.num : ℚ) / (q.den : ℚ) := by rw [hnum_eq, Nat.abs_cast]
    _ ≤ (Int.natAbs q.num : ℚ) := div_le_self (Nat.cast_nonneg _) hden_ge
    _ ≤ ((2 ^ B : ℕ) : ℚ) := by exact_mod_cast hn
    _ = (2 : ℚ) ^ B := by push_cast; rfl

private theorem maxAbsList_le_two_pow {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    maxAbsList cs ≤ (2 : ℚ) ^ B := by
  induction cs with
  | nil => simp only [maxAbsList]; positivity
  | cons q qs ih =>
    simp only [maxAbsList]
    refine max_le (abs_rat_le_two_pow (hB q List.mem_cons_self).1) ?_
    exact ih fun r hr => hB r (List.mem_cons_of_mem q hr)

/-- Upper bound `cauchyBoundNat cs ≤ 2 ^ (2 * B) + 2` under `HasCoeffBitBound B cs`. -/
theorem cauchyBoundNat_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    cauchyBoundNat cs ≤ 2 ^ (2 * B) + 2 := by
  let t := trim cs
  have htB : HasCoeffBitBound B t := hB.trim
  dsimp only [cauchyBoundNat]
  split_ifs with hlen
  · exact (by decide : 1 ≤ 2).trans (Nat.le_add_left 2 _)
  · have htnil : t ≠ [] := fun hnil => by
      dsimp only [t] at hnil
      simp only [hnil, List.length_nil] at hlen
      omega
    obtain ⟨lc, hlc, hlc0⟩ := (isTrimmed_trim cs).getLast?_ne_zero htnil
    have hlc_mem : lc ∈ t := List.mem_of_getLast? hlc
    have hlc_den : lc.den ≤ 2 ^ B := (htB lc hlc_mem).2
    have hlc_num_pos : 1 ≤ Int.natAbs lc.num :=
      Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hlc0)
    have hlc_abs_ge : (1 : ℚ) / (2 : ℚ) ^ B ≤ |lc| := by
      have hnum_eq : |(lc.num : ℚ)| = (Int.natAbs lc.num : ℚ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      have hden_pos : (0 : ℚ) < (lc.den : ℚ) := by exact_mod_cast lc.den_pos
      have hpow_pos : (0 : ℚ) < (2 : ℚ) ^ B := by positivity
      have hden_le : (lc.den : ℚ) ≤ (2 : ℚ) ^ B := by
        calc (lc.den : ℚ) ≤ ((2 ^ B : ℕ) : ℚ) := by exact_mod_cast hlc_den
          _ = (2 : ℚ) ^ B := by push_cast; rfl
      calc (1 : ℚ) / (2 : ℚ) ^ B
          ≤ (Int.natAbs lc.num : ℚ) / (2 : ℚ) ^ B := by
              gcongr; exact_mod_cast hlc_num_pos
        _ ≤ (Int.natAbs lc.num : ℚ) / (lc.den : ℚ) :=
              div_le_div_of_nonneg_left (Nat.cast_nonneg _) hden_pos hden_le
        _ = |(lc.num : ℚ) / (lc.den : ℚ)| := by rw [abs_div, hnum_eq, Nat.abs_cast]
        _ = |lc| := by rw [Rat.num_div_den]
    have hdropB : HasCoeffBitBound B t.dropLast :=
      fun q hq => htB q (List.dropLast_subset t hq)
    have hm_le : maxAbsList t.dropLast ≤ (2 : ℚ) ^ B := maxAbsList_le_two_pow hdropB
    have hlc_eq : Option.getD t.getLast? 1 = lc := by rw [hlc, Option.getD_some]
    rw [hlc_eq]
    let b := maxAbsList t.dropLast / |lc| + 1
    have hb_nonneg : 0 ≤ b :=
      add_nonneg (div_nonneg (maxAbsList_nonneg _) (abs_nonneg _)) zero_le_one
    have hdiv_le : maxAbsList t.dropLast / |lc| ≤ (2 : ℚ) ^ (2 * B) := by
      have hpos1 : (0 : ℚ) < (1 : ℚ) / (2 : ℚ) ^ B := by positivity
      calc maxAbsList t.dropLast / |lc|
          ≤ maxAbsList t.dropLast / ((1 : ℚ) / (2 : ℚ) ^ B) :=
              div_le_div_of_nonneg_left (maxAbsList_nonneg _) hpos1 hlc_abs_ge
        _ = maxAbsList t.dropLast * (2 : ℚ) ^ B := by rw [one_div, div_inv_eq_mul]
        _ ≤ (2 : ℚ) ^ B * (2 : ℚ) ^ B :=
              mul_le_mul_of_nonneg_right hm_le (by positivity)
        _ = (2 : ℚ) ^ (2 * B) := by rw [two_mul, pow_add]
    have hb_le : b ≤ ((2 ^ (2 * B) + 1 : ℕ) : ℚ) := by
      dsimp only [b]
      push_cast
      linarith
    have hfloor_le : ((Int.natAbs b.num / b.den : ℕ) : ℚ) ≤ b := by
      have hden_pos : (0 : ℚ) < (b.den : ℚ) := by exact_mod_cast b.den_pos
      have hmul : ((Int.natAbs b.num / b.den : ℕ) : ℚ) * (b.den : ℚ) ≤ (Int.natAbs b.num : ℚ) := by
        exact_mod_cast Nat.div_mul_le_self (Int.natAbs b.num) b.den
      have hnum_eq : (Int.natAbs b.num : ℚ) / (b.den : ℚ) = b := by
        calc (Int.natAbs b.num : ℚ) / (b.den : ℚ)
            = |(b.num : ℚ)| / |(b.den : ℚ)| := by
                rw [Nat.abs_cast, ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
          _ = |(b.num : ℚ) / (b.den : ℚ)| := (abs_div _ _).symm
          _ = |b| := by rw [Rat.num_div_den]
          _ = b := abs_of_nonneg hb_nonneg
      calc ((Int.natAbs b.num / b.den : ℕ) : ℚ)
          ≤ (Int.natAbs b.num : ℚ) / (b.den : ℚ) := (le_div_iff₀ hden_pos).mpr hmul
        _ = b := hnum_eq
    have hnat_le : Int.natAbs b.num / b.den ≤ 2 ^ (2 * B) + 1 := by
      exact_mod_cast hfloor_le.trans hb_le
    exact Nat.add_le_add_right hnat_le 1

/-- Logarithmic bound `Nat.clog 4 (cauchyBoundNat cs) ≤ B + 1` under `HasCoeffBitBound B cs`. -/
theorem clog4_cauchyBoundNat_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    Nat.clog 4 (cauchyBoundNat cs) ≤ B + 1 := by
  refine Nat.clog_le_of_le_pow ?_
  have hcb := cauchyBoundNat_le_of_bitBound hB
  have h4 : 2 ^ (2 * B) = 4 ^ B := by
    rw [pow_mul]
    rfl
  have h1 : 1 ≤ 4 ^ B := Nat.one_le_pow B 4 (by decide)
  rw [pow_succ]
  omega

/-- `lcmDens cs ≤ 2 ^ (cs.length * B)` under `HasCoeffBitBound B cs`. -/
theorem lcmDens_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    lcmDens cs ≤ 2 ^ (cs.length * B) := by
  induction cs with
  | nil => simp only [lcmDens, List.length_nil, zero_mul, pow_zero, le_refl]
  | cons q qs ih =>
    simp only [lcmDens, List.length_cons]
    have hq_den : q.den ≤ 2 ^ B := (hB q List.mem_cons_self).2
    have hih : lcmDens qs ≤ 2 ^ (qs.length * B) :=
      ih fun r hr => hB r (List.mem_cons_of_mem q hr)
    have hlcm_le : Nat.lcm q.den (lcmDens qs) ≤ q.den * lcmDens qs :=
      Nat.lcm_le_mul q.den_pos (one_le_lcmDens qs)
    calc Nat.lcm q.den (lcmDens qs)
        ≤ q.den * lcmDens qs := hlcm_le
      _ ≤ 2 ^ B * 2 ^ (qs.length * B) := Nat.mul_le_mul hq_den hih
      _ = 2 ^ ((qs.length + 1) * B) := by rw [Nat.add_one_mul, add_comm, pow_add]

private theorem foldl_sqNorm_le_of_bound (ns : List ℤ) (M acc : ℕ)
    (hM : ∀ z ∈ ns, Int.natAbs z ≤ M) :
    ns.foldl (fun s a => s + Int.natAbs a ^ 2) acc ≤ acc + ns.length * M ^ 2 := by
  induction ns generalizing acc with
  | nil => simp only [List.foldl_nil, List.length_nil, zero_mul, add_zero, le_refl]
  | cons a ns ih =>
    simp only [List.foldl_cons, List.length_cons]
    have ha : Int.natAbs a ^ 2 ≤ M ^ 2 :=
      Nat.pow_le_pow_left (hM a List.mem_cons_self) 2
    have hrec := ih (acc + Int.natAbs a ^ 2) fun z hz => hM z (List.mem_cons_of_mem a hz)
    calc ns.foldl (fun s b => s + Int.natAbs b ^ 2) (acc + Int.natAbs a ^ 2)
        ≤ (acc + Int.natAbs a ^ 2) + ns.length * M ^ 2 := hrec
      _ ≤ acc + M ^ 2 + ns.length * M ^ 2 := by omega
      _ = acc + (ns.length + 1) * M ^ 2 := by ring

/-- Upper bound on cleared-denominator `sqNormList` under `HasCoeffBitBound B cs`. -/
theorem sqNormList_clearDenoms_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    sqNormList (Prod.snd (clearDenomsList (trim cs))) ≤
      cs.length * 4 ^ ((cs.length + 1) * B) := by
  let t := trim cs
  let n := cs.length
  have ht_len : t.length ≤ n := trim_length_le cs
  have htB : HasCoeffBitBound B t := hB.trim
  have hD_le : lcmDens t ≤ 2 ^ (n * B) :=
    (lcmDens_le_of_bitBound htB).trans
      (Nat.pow_le_pow_right zero_lt_two (Nat.mul_le_mul_right B ht_len))
  let ns := Prod.snd (clearDenomsList t)
  have hns_len : ns.length = t.length := by
    simp only [ns, clearDenomsList, List.length_map]
  have hns_bound : ∀ z ∈ ns, Int.natAbs z ≤ 2 ^ ((n + 1) * B) := by
    intro z hz
    simp only [ns, clearDenomsList, List.mem_map] at hz
    obtain ⟨q, hq, rfl⟩ := hz
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    have hq_num : Int.natAbs q.num ≤ 2 ^ B := (htB q hq).1
    have hdiv : lcmDens t / q.den ≤ 2 ^ (n * B) := (Nat.div_le_self _ _).trans hD_le
    calc Int.natAbs q.num * (lcmDens t / q.den)
        ≤ 2 ^ B * 2 ^ (n * B) := Nat.mul_le_mul hq_num hdiv
      _ = 2 ^ ((n + 1) * B) := by rw [Nat.add_one_mul, add_comm, pow_add]
  have hsq : sqNormList ns ≤ ns.length * (2 ^ ((n + 1) * B)) ^ 2 := by
    have h1 := foldl_sqNorm_le_of_bound ns (2 ^ ((n + 1) * B)) 0 hns_bound
    simpa only [sqNormList, zero_add] using h1
  have h4 : (2 ^ ((n + 1) * B)) ^ 2 = 4 ^ ((n + 1) * B) := by
    rw [← pow_mul, mul_comm _ 2, pow_mul]
    rfl
  rw [h4, hns_len] at hsq
  exact hsq.trans (Nat.mul_le_mul_right _ ht_len)

/-- Logarithmic bound on `sqNormList (clearDenomsList (trim cs)).2`
under `HasCoeffBitBound B cs`. -/
theorem clog4_sqNormList_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    Nat.clog 4 (sqNormList (Prod.snd (clearDenomsList (trim cs)))) ≤
      cs.length + (cs.length + 1) * B := by
  refine Nat.clog_le_of_le_pow ?_
  have hsq := sqNormList_clearDenoms_le_of_bitBound hB
  have hn4 : cs.length ≤ 4 ^ cs.length :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by decide : 2 ≤ 4) cs.length)
  rw [pow_add]
  exact hsq.trans (Nat.mul_le_mul_right _ hn4)

/-- Unconditional polynomial upper bound on `mignotteBisectionDepth cs` in terms of `cs.length`
and an input coefficient bit-length bound `B`. -/
theorem mignotteBisectionDepth_le_of_bitBound {B : ℕ} {cs : List ℚ} (hB : HasCoeffBitBound B cs) :
    mignotteBisectionDepth cs ≤ (cs.length + 2) ^ 2 * (B + 2) := by
  by_cases hd : 2 ≤ (ofCoeffList cs).natDegree
  · have hbase := mignotteBisectionDepth_le cs hd
    have hcb := clog4_cauchyBoundNat_le_of_bitBound hB
    have hsn := clog4_sqNormList_le_of_bitBound hB
    have hd_le_n : (ofCoeffList cs).natDegree ≤ cs.length :=
      (natDegree_ofCoeffList_le cs).trans (Nat.sub_le _ _)
    have hclog_d : Nat.clog 4 (ofCoeffList cs).natDegree ≤ cs.length := by
      refine Nat.clog_le_of_le_pow ?_
      exact hd_le_n.trans
        (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by decide : 2 ≤ 4) cs.length))
    have h1 : ((ofCoeffList cs).natDegree + 2) * Nat.clog 4 (ofCoeffList cs).natDegree ≤
        (cs.length + 2) * cs.length :=
      Nat.mul_le_mul (Nat.add_le_add_right hd_le_n 2) hclog_d
    have h2 : ((ofCoeffList cs).natDegree - 1) *
          Nat.clog 4 (sqNormList (Prod.snd (clearDenomsList (trim cs)))) ≤
        cs.length * (cs.length + (cs.length + 1) * B) :=
      Nat.mul_le_mul ((Nat.sub_le _ _).trans hd_le_n) hsn
    have hsum : 1 + 2 * (B + 1) + (cs.length + 2) * cs.length +
        cs.length * (cs.length + (cs.length + 1) * B) ≤ (cs.length + 2) ^ 2 * (B + 2) := by
      nlinarith
    omega
  · rw [mignotteBisectionDepth_eq_zero_of_natDegree_le_one (by omega)]
    exact Nat.zero_le _

/-- Predicate asserting that `q : ℚ` is a dyadic rational `z / 2 ^ e` with `|z| ≤ b * 2 ^ e`. -/
def DyadicBounded (b e : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, q = (z : ℚ) / (2 : ℚ) ^ e ∧ Int.natAbs z ≤ b * 2 ^ e

/-- Any natural number `(b : ℚ)` satisfies `DyadicBounded b 0`. -/
theorem DyadicBounded.of_nat (b : ℕ) : DyadicBounded b 0 (b : ℚ) :=
  ⟨(b : ℤ), by simp only [pow_zero, div_one, Int.cast_natCast], by simp only [Int.natAbs_natCast,
    pow_zero, mul_one, le_refl]⟩

/-- `-(b : ℚ)` satisfies `DyadicBounded b 0`. -/
theorem DyadicBounded.of_neg_nat (b : ℕ) : DyadicBounded b 0 (-(b : ℚ)) :=
  ⟨-(b : ℤ), by simp only [pow_zero, div_one, Int.cast_neg, Int.cast_natCast],
    by simp only [Int.natAbs_neg, Int.natAbs_natCast, pow_zero, mul_one, le_refl]⟩

/-- Monotonicity of `DyadicBounded` in the exponent `e ≤ e'`. -/
theorem DyadicBounded.mono {b e e' : ℕ} {q : ℚ} (hq : DyadicBounded b e q) (he : e ≤ e') :
    DyadicBounded b e' q := by
  obtain ⟨z, rfl, hz⟩ := hq
  refine ⟨z * (2 : ℤ) ^ (e' - e), ?_, ?_⟩
  · have hpow : (2 : ℚ) ^ e' = (2 : ℚ) ^ e * (2 : ℚ) ^ (e' - e) := by
      rw [← pow_add, Nat.add_sub_of_le he]
    have hne : (2 : ℚ) ^ (e' - e) ≠ 0 := by positivity
    rw [hpow, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    exact (mul_div_mul_right (z : ℚ) ((2 : ℚ) ^ e) hne).symm
  · rw [Int.natAbs_mul, Int.natAbs_pow]
    change Int.natAbs z * 2 ^ (e' - e) ≤ b * 2 ^ e'
    calc Int.natAbs z * 2 ^ (e' - e)
        ≤ (b * 2 ^ e) * 2 ^ (e' - e) := Nat.mul_le_mul_right _ hz
      _ = b * (2 ^ e * 2 ^ (e' - e)) := by ring
      _ = b * 2 ^ e' := by rw [← pow_add, Nat.add_sub_of_le he]

/-- Midpoint rule: if `u` and `v` satisfy `DyadicBounded b e`, then `(u + v) / 2` satisfies
`DyadicBounded b (e + 1)`. -/
theorem DyadicBounded.mid {b e : ℕ} {u v : ℚ}
    (hu : DyadicBounded b e u) (hv : DyadicBounded b e v) :
    DyadicBounded b (e + 1) ((u + v) / 2) := by
  obtain ⟨zu, rfl, hzu⟩ := hu
  obtain ⟨zv, rfl, hzv⟩ := hv
  refine ⟨zu + zv, ?_, ?_⟩
  · rw [pow_succ, Int.cast_add]
    ring
  · calc Int.natAbs (zu + zv)
        ≤ Int.natAbs zu + Int.natAbs zv := Int.natAbs_add_le _ _
      _ ≤ b * 2 ^ e + b * 2 ^ e := Nat.add_le_add hzu hzv
      _ = b * 2 ^ (e + 1) := by rw [pow_succ]; ring

/-- Denominator bound `q.den ≤ 2 ^ e` for any `DyadicBounded b e q`. -/
theorem DyadicBounded.den_le {b e : ℕ} {q : ℚ} (hq : DyadicBounded b e q) :
    q.den ≤ 2 ^ e := by
  obtain ⟨z, hq_eq, _⟩ := hq
  have hdiv : q = Rat.divInt z ((2 : ℤ) ^ e) := by
    rw [Rat.divInt_eq_div, Int.cast_pow, Int.cast_ofNat]
    exact hq_eq
  have hdvdZ : (q.den : ℤ) ∣ (2 : ℤ) ^ e := by
    rw [hdiv]
    exact Rat.den_dvd z ((2 : ℤ) ^ e)
  have hdvd : q.den ∣ 2 ^ e := by exact_mod_cast hdvdZ
  exact Nat.le_of_dvd (Nat.pow_pos zero_lt_two) hdvd

/-- Numerator magnitude bound `Int.natAbs q.num ≤ b * 2 ^ e` for any `DyadicBounded b e q`. -/
theorem DyadicBounded.natAbs_num_le {b e : ℕ} {q : ℚ} (hq : DyadicBounded b e q) :
    Int.natAbs q.num ≤ b * 2 ^ e := by
  have hden := hq.den_le
  obtain ⟨z, hq_eq, hz⟩ := hq
  have hnum_div : (q.num : ℚ) / (q.den : ℚ) = (z : ℚ) / (2 : ℚ) ^ e := by
    rw [Rat.num_div_den]
    exact hq_eq
  have hden0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hpow0 : (2 : ℚ) ^ e ≠ 0 := by positivity
  have hcrossQ : (q.num : ℚ) * (2 : ℚ) ^ e = (z : ℚ) * (q.den : ℚ) :=
    (div_eq_div_iff hden0 hpow0).mp hnum_div
  have hcrossZ : q.num * (2 : ℤ) ^ e = z * (q.den : ℤ) := by exact_mod_cast hcrossQ
  have hcrossN : Int.natAbs q.num * 2 ^ e = Int.natAbs z * q.den := by
    have h := congrArg Int.natAbs hcrossZ
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] at h
    exact h
  have hmul_le : Int.natAbs q.num * 2 ^ e ≤ (b * 2 ^ e) * 2 ^ e := by
    rw [hcrossN]
    exact Nat.mul_le_mul hz hden
  exact Nat.le_of_mul_le_mul_right hmul_le (Nat.pow_pos zero_lt_two)

private theorem refineLeftLoopM_dyadicBounded (t : List ℚ) (seq : List (List ℚ)) :
    ∀ (fuel b e : ℕ) (u v : ℚ) (vu : ℕ),
      DyadicBounded b e u → DyadicBounded b e v →
      let I := (refineLeftLoopM t seq fuel u v vu).ret
      DyadicBounded b (e + fuel) I.lower ∧ DyadicBounded b (e + fuel) I.upper
  | 0, b, e, u, v, _, hu, hv => by
    simp only [refineLeftLoopM, TimeM.ret_pure, Nat.add_zero]
    exact ⟨hu, hv⟩
  | fuel + 1, b, e, u, v, vu, hu, hv => by
    dsimp only [refineLeftLoopM]
    rw [TimeM.ret_bind, sturmVariationsM_ret]
    have hm : DyadicBounded b (e + 1) ((u + v) / 2) := hu.mid hv
    split_ifs with hvm
    · rw [TimeM.ret_pure]
      exact ⟨hm.mono (by omega), hv.mono (by omega)⟩
    · rw [TimeM.ret_bind, evalListM_ret]
      split_ifs with hem
      · rw [TimeM.ret_pure]
        exact ⟨hm.mono (by omega), hm.mono (by omega)⟩
      · have ih := refineLeftLoopM_dyadicBounded t seq fuel b (e + 1) u ((u + v) / 2) vu
          (hu.mono (by omega)) hm
        have heq : e + 1 + fuel = e + (fuel + 1) := by omega
        simpa only [heq] using ih

private theorem refineLeftRootM_dyadicBounded (t : List ℚ) (seq : List (List ℚ))
    (fuel b e : ℕ) (u v : ℚ) (vu : ℕ)
    (hu : DyadicBounded b e u) (hv : DyadicBounded b e v) :
    let I := (refineLeftRootM t seq fuel u v vu).ret
    DyadicBounded b (e + fuel) I.lower ∧ DyadicBounded b (e + fuel) I.upper := by
  dsimp only [refineLeftRootM]
  rw [TimeM.ret_bind, evalListM_ret]
  split_ifs with hev
  · rw [TimeM.ret_pure]
    exact ⟨hv.mono (by omega), hv.mono (by omega)⟩
  · rw [TimeM.ret_bind, evalListM_ret]
    split_ifs with heu
    · rw [TimeM.ret_pure]
      exact ⟨hu.mono (by omega), hv.mono (by omega)⟩
    · exact refineLeftLoopM_dyadicBounded t seq fuel b e u v vu hu hv

private theorem isolateIocM_dyadicBounded (t : List ℚ) (seq : List (List ℚ)) (depthBound : ℕ) :
    ∀ (fuel b e : ℕ) (u v : ℚ) (vu vv : ℕ),
      DyadicBounded b e u → DyadicBounded b e v →
      ∀ I ∈ (isolateIocM t seq depthBound fuel u v vu vv).ret,
        DyadicBounded b (e + fuel + depthBound) I.lower ∧
          DyadicBounded b (e + fuel + depthBound) I.upper
  | fuel, b, e, u, v, vu, vv, hu, hv => by
    unfold isolateIocM
    dsimp only
    split_ifs with hc0 hc1
    · rw [TimeM.ret_pure]
      intro _ h; cases h
    · rw [TimeM.ret_bind, TimeM.ret_pure]
      intro I hI
      rw [List.mem_singleton] at hI
      subst hI
      have href := refineLeftRootM_dyadicBounded t seq depthBound b e u v vu hu hv
      exact ⟨href.1.mono (by omega), href.2.mono (by omega)⟩
    · cases fuel with
      | zero =>
        rw [TimeM.ret_pure]
        intro _ h; cases h
      | succ fuel' =>
        simp only [TimeM.ret_bind, sturmVariationsM_ret, TimeM.ret_pure]
        have hm : DyadicBounded b (e + 1) ((u + v) / 2) := hu.mid hv
        intro I hI
        rw [List.mem_append] at hI
        have heq : e + 1 + fuel' + depthBound = e + (fuel' + 1) + depthBound := by omega
        rcases hI with hL | hR
        · have h := isolateIocM_dyadicBounded t seq depthBound fuel' b (e + 1) u ((u + v) / 2)
            vu _ (hu.mono (by omega)) hm I hL
          simpa only [heq] using h
        · have h := isolateIocM_dyadicBounded t seq depthBound fuel' b (e + 1) ((u + v) / 2) v
            _ vv hm (hv.mono (by omega)) I hR
          simpa only [heq] using h

/-- Unconditional dyadic endpoint bound: every interval in `isolateRoots cs` has endpoints of the
form `z / 2 ^ (2 * mignotteBisectionDepth cs)` with
`Int.natAbs z ≤ cauchyBoundNat cs * 2 ^ (2 * mignotteBisectionDepth cs)`. -/
theorem isolateRoots_dyadicBounded (cs : List ℚ) :
    ∀ I ∈ isolateRoots cs,
      DyadicBounded (cauchyBoundNat cs) (2 * mignotteBisectionDepth cs) I.lower ∧
        DyadicBounded (cauchyBoundNat cs) (2 * mignotteBisectionDepth cs) I.upper := by
  simp only [isolateRoots, isolateRootsM]
  by_cases he : (trim cs).isEmpty = true
  · simp only [he, ↓reduceIte, TimeM.ret_pure]
    intro _ h; cases h
  · simp only [he, Bool.false_eq_true, ↓reduceIte, TimeM.ret_bind, sturmVariationsM_ret]
    intro I hI
    let b := cauchyBoundNat cs
    let k := mignotteBisectionDepth cs
    have h := isolateIocM_dyadicBounded (trim cs) (sturmSeqList cs) k k b 0
      (-(b : ℚ)) (b : ℚ) _ _ (DyadicBounded.of_neg_nat b) (DyadicBounded.of_nat b) I hI
    have heq : 0 + k + k = 2 * k := by omega
    simpa only [heq] using h

end Cslib.RealRoot
