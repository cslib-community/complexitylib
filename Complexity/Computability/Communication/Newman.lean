/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Randomized
public import Mathlib.Analysis.SpecialFunctions.Exp
import Complexity.Probability.PMF.Event
import Complexity.Probability.Concentration
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Nat.Log

/-!
# Newman's theorem

Public coins can replace private coins, and Newman's theorem bounds the converse: private coins
cost only a few more bits than public coins on finite inputs [Newman1991],
[Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]. Let a public-coin protocol `μ` solve
`R` on `A × B` with error `ε`, sending at most `c` bits. Draw `2 ^ k` protocols from `μ`
independently. On each pair of inputs the fraction of them that err is, by Hoeffding's inequality
(`Cslib.Probability.PMF.pi_sum_ge_mean_add`), at least `ε + δ` with probability at most
`exp (-2 δ² 2 ^ k)`. If `|X| |Y| exp (-2 δ² 2 ^ k) < 1`, a union bound over the inputs leaves some
choice of `2 ^ k` protocols in which, on every pair of inputs, fewer than a fraction `ε + δ` err.
Alice then picks one of them with `k` private random bits, sends her choice, and both run it: a
private-coin protocol with error `ε + δ` sending at most `k + c` bits
(`PublicCoin.Solves.exists_privateCoin`, `PrivateCoin.ecomplexity_le_add`).

For inputs of at most `n` bits, `k = ⌈log₂ ⌈n / δ²⌉⌉` random bits suffice, that is
`O(log n + log (1 / δ))` extra bits (`PrivateCoin.ecomplexity_le_add_clog`).

## Main results

* `Cslib.Communication.PublicCoin.Solves.exists_privateCoin`: the private-coin protocol.
* `Cslib.Communication.PrivateCoin.ecomplexity_le_add`: Newman's theorem for finite inputs.
* `Cslib.Communication.PrivateCoin.ecomplexity_le_add_clog`: Newman's theorem for inputs of `n`
  bits.

## References

* [I. Newman, *Private vs. common random bits in communication complexity*][Newman1991]
* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Probability Finset MeasureTheory

variable {X Y Z : Type*} {R : X → Y → Z → Prop} {A : Set X} {B : Set Y}

open Classical in
/-- On a valid pair of inputs `(x, y) ∈ A × B`, the probability under `2 ^ k` independent draws
from `μ` that at least `2 ^ k * (ε + δ)` protocols err on `(x, y)` is at most
`exp (-2 * δ ^ 2 * 2 ^ k)`. -/
private theorem pi_sum_err_ge_toReal_le [Finite X] [Finite Y] {μ : PublicCoin X Y Z}
    {ε δ : ℝ} (k : ℕ) (hμ : μ.Solves ε R A B) (hδ : 0 ≤ δ) {x : X} (hx : x ∈ A)
    {y : Y} (hy : y ∈ B) :
    let err : Protocol X Y Z → X × Y → Bool := fun p q => decide (¬R q.1 q.2 (p.run q.1 q.2))
    let S : PMF (BitString k → X × Y → Bool) := PMF.pi fun _ => μ.map err
    (S.toOuterMeasure {s | 2 ^ k * (ε + δ) ≤ ∑ i, if s i (x, y) then 1 else 0}).toReal ≤
      Real.exp (-2 * δ ^ 2 * 2 ^ k) := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  intro err S
  let ν : PMF (X × Y → Bool) := μ.map err
  have hcard : (Fintype.card (BitString k) : ℝ) = 2 ^ k := by simp
  have hmean : ∑ s, (ν s).toReal * (if s (x, y) then 1 else 0) ≤ ε := by
    have hev : ν.toOuterMeasure {s | s (x, y) = true} =
        μ.toOuterMeasure {p | ¬R x y (p.run x y)} := by
      rw [PMF.toOuterMeasure_map_apply]
      congr 1
      ext p
      simp [err]
    refine le_trans (le_of_eq ?_) (hμ x hx y hy)
    rw [PublicCoin.errorProb, ← hev, PMF.toOuterMeasure_apply_toReal]
    refine sum_congr rfl fun s _ => ?_
    by_cases hs : s (x, y) <;> simp [hs]
  have h := PMF.pi_sum_ge_mean_add (fun _ : BitString k => ν)
    (fun _ s => if s (x, y) then (1 : ℝ) else 0) (bound := 1) (ε := 2 ^ k * δ) zero_le_one
    (fun _ _ _ => by split_ifs <;> simp) (by positivity)
  refine le_trans (ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _) (measure_mono ?_))
    (h.trans_eq ?_)
  · intro s hs
    simp only [Set.mem_ofPred_eq] at hs ⊢
    have hsum : ∑ _i : BitString k, ∑ s, (ν s).toReal * (if s (x, y) then (1 : ℝ) else 0) ≤
        2 ^ k * ε := by
      rw [sum_const, card_univ, nsmul_eq_mul, hcard]
      exact mul_le_mul_of_nonneg_left hmean (by positivity)
    linarith
  · rw [hcard]
    field_simp

open Classical in
/-- By a union bound over `F = {q | q.1 ∈ A ∧ q.2 ∈ B}`, when `|X| |Y| exp (-2 δ² 2 ^ k) < 1`,
some draw `s` from `2 ^ k` independent copies of `μ.map err` has fewer than `2 ^ k * (ε + δ)`
errors on every pair of inputs in `A × B`. -/
private theorem exists_mem_support_forall_count_lt [Finite X] [Finite Y]
    {μ : PublicCoin X Y Z} {ε δ : ℝ} (k : ℕ) (hμ : μ.Solves ε R A B) (hδ : 0 ≤ δ)
    (hk : Nat.card X * Nat.card Y * Real.exp (-2 * δ ^ 2 * 2 ^ k) < 1) :
    let err : Protocol X Y Z → X × Y → Bool := fun p q => decide (¬R q.1 q.2 (p.run q.1 q.2))
    let S : PMF (BitString k → X × Y → Bool) := PMF.pi fun _ => μ.map err
    ∃ s ∈ S.support, ∀ x ∈ A, ∀ y ∈ B,
      (∑ i, if s i (x, y) then (1 : ℝ) else 0) < 2 ^ k * (ε + δ) := by
  have := Fintype.ofFinite X
  have := Fintype.ofFinite Y
  intro err S
  let count (s : BitString k → X × Y → Bool) (q : X × Y) : ℝ := ∑ i, if s i q then 1 else 0
  let F : Finset (X × Y) := {q | q.1 ∈ A ∧ q.2 ∈ B}
  let bad (q : X × Y) : Set (BitString k → X × Y → Bool) := {s | 2 ^ k * (ε + δ) ≤ count s q}
  -- Hoeffding's inequality on each pair of inputs.
  have hbad (q : X × Y) (hq : q ∈ F) :
      (S.toOuterMeasure (bad q)).toReal ≤ Real.exp (-2 * δ ^ 2 * 2 ^ k) := by
    obtain ⟨hx, hy⟩ : q.1 ∈ A ∧ q.2 ∈ B := by simpa [F] using hq
    exact pi_sum_err_ge_toReal_le k hμ hδ hx hy
  -- A union bound over the inputs.
  have hunion : (S.toOuterMeasure (⋃ q ∈ F, bad q)).toReal < 1 := by
    calc (S.toOuterMeasure (⋃ q ∈ F, bad q)).toReal
        ≤ (∑ q ∈ F, S.toOuterMeasure (bad q)).toReal :=
          ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun _ _ => PMF.toOuterMeasure_ne_top _ _)
            (measure_biUnion_finset_le F bad)
      _ = ∑ q ∈ F, (S.toOuterMeasure (bad q)).toReal :=
          ENNReal.toReal_sum fun _ _ => PMF.toOuterMeasure_ne_top _ _
      _ ≤ ∑ _q ∈ F, Real.exp (-2 * δ ^ 2 * 2 ^ k) := sum_le_sum hbad
      _ ≤ Nat.card X * Nat.card Y * Real.exp (-2 * δ ^ 2 * 2 ^ k) := by
          rw [sum_const, nsmul_eq_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          have : F.card ≤ Nat.card X * Nat.card Y := by
            simpa [Nat.card_eq_fintype_card] using card_le_univ F
          exact_mod_cast this
      _ < 1 := hk
  obtain ⟨s, hs, hgood⟩ : ∃ s ∈ S.support, s ∉ ⋃ q ∈ F, bad q := by
    by_contra! h
    have h1 := (PMF.toOuterMeasure_apply_eq_one_iff S _).mpr h
    rw [h1, ENNReal.toReal_one] at hunion
    exact lt_irrefl _ hunion
  refine ⟨s, hs, fun x hx y hy => ?_⟩
  have hq : (x, y) ∈ F := by simp [F, hx, hy]
  simpa [bad, count] using fun h => hgood (Set.mem_biUnion hq h)

/-- **Newman's theorem**, the construction. If a public-coin protocol solves `R` on `A × B` with
error `ε` sending at most `c` bits, and `|X| |Y| exp (-2 δ² 2 ^ k) < 1` for some `δ ≥ 0`, then a
private-coin protocol in which Alice holds `k` random bits and Bob none solves `R` on `A × B` with
error `ε + δ` sending at most `k + c` bits. -/
theorem PublicCoin.Solves.exists_privateCoin [Finite X] [Finite Y] {μ : PublicCoin X Y Z}
    {ε δ : ℝ} {c k : ℕ} (hμ : μ.Solves ε R A B) (hc : μ.depth ≤ c) (hδ : 0 ≤ δ)
    (hk : Nat.card X * Nat.card Y * Real.exp (-2 * δ ^ 2 * 2 ^ k) < 1) :
    ∃ P : PrivateCoin k 0 X Y Z, P.Solves (ε + δ) R A B ∧ P.depth ≤ k + c := by
  classical
  let err : Protocol X Y Z → X × Y → Bool := fun p q => decide (¬R q.1 q.2 (p.run q.1 q.2))
  -- Some choice of `2 ^ k` protocols errs rarely on every pair of inputs.
  obtain ⟨s, hs, hgood⟩ := exists_mem_support_forall_count_lt k hμ hδ hk
  have hchoose (i : BitString k) : ∃ p ∈ μ.support, err p = s i :=
    (PMF.mem_support_map_iff _ _ _).mp ((PMF.mem_support_pi_iff _ s).mp hs i)
  choose p hp hps using hchoose
  -- Alice sends her random bits and both run the chosen protocol.
  refine ⟨Protocol.aliceSend k (fun xr => xr.2) fun m => (p m).comap Prod.fst Prod.fst,
    fun x hx y hy => ?_, Protocol.depth_aliceSend_le fun m => ?_⟩
  · have hlt := hgood x hx y hy
    have hcount : (∑ i : BitString k, if s i (x, y) then (1 : ℝ) else 0) =
        ∑ i : BitString k, if ¬R x y ((p i).run x y) then 1 else 0 := by
      refine sum_congr rfl fun i _ => ?_
      rw [← hps i]
      simp [err]
    rw [PrivateCoin.errorProb, PMF.toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
    simp only [Fintype.sum_unique, Set.mem_ofPred_eq, Protocol.run_aliceSend,
      Protocol.run_comap, PMF.uniformOfFintype_apply, Fintype.card_prod]
    have hpos : (0 : ℝ) < 2 ^ k := by positivity
    calc _ = (2 ^ k)⁻¹ * ∑ i : BitString k, if s i (x, y) then (1 : ℝ) else 0 := by
          rw [hcount, mul_sum]
          refine sum_congr rfl fun i _ => ?_
          split_ifs <;> simp
      _ ≤ ε + δ := by
          rw [inv_mul_le_iff₀ hpos]
          exact hlt.le
  · have := (PublicCoin.depth_le_depth (hp m)).trans hc
    simpa using this

/-- **Newman's theorem** for finite inputs: if `|X| |Y| exp (-2 δ² 2 ^ k) < 1` for some `δ ≥ 0`,
private coins cost at most `k` more bits than public coins, for an extra error `δ`. -/
theorem PrivateCoin.ecomplexity_le_add [Finite X] [Finite Y] {ε δ : ℝ} (hδ : 0 ≤ δ) {k : ℕ}
    (hk : Nat.card X * Nat.card Y * Real.exp (-2 * δ ^ 2 * 2 ^ k) < 1) :
    PrivateCoin.ecomplexity (ε + δ) R A B ≤ PublicCoin.ecomplexity ε R A B + k := by
  cases h : PublicCoin.ecomplexity ε R A B using ENat.recTopCoe with
  | top => simp
  | coe c =>
    obtain ⟨μ, hμ, hc⟩ := PublicCoin.ecomplexity_le_iff.mp h.le
    obtain ⟨P, hP, hd⟩ := hμ.exists_privateCoin hc hδ hk
    refine (PrivateCoin.ecomplexity_le_depth hP).trans ?_
    exact_mod_cast (by omega : P.depth ≤ c + k)

/-- For `1 ≤ n`, `4 ^ n < exp (2 * n)`. -/
private theorem four_pow_lt_exp_two_mul {n : ℕ} (hn : 0 < n) :
    (4 : ℝ) ^ n < Real.exp (2 * n) := by
  have h4 : (4 : ℝ) < Real.exp 2 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith
  rw [mul_comm, Real.exp_nat_mul]
  exact pow_lt_pow_left₀ h4 (by norm_num) hn.ne'

/-- **Newman's theorem** for inputs of at most `n` bits: for `δ > 0`, private coins cost at most
`⌈log₂ ⌈n / δ²⌉⌉` more bits than public coins, for an extra error `δ`. -/
theorem PrivateCoin.ecomplexity_le_add_clog [Finite X] [Finite Y] {n : ℕ}
    (hX : Nat.card X ≤ 2 ^ n) (hY : Nat.card Y ≤ 2 ^ n) {ε δ : ℝ} (hδ : 0 < δ) :
    PrivateCoin.ecomplexity (ε + δ) R A B ≤
      PublicCoin.ecomplexity ε R A B + Nat.clog 2 ⌈n / δ ^ 2⌉₊ := by
  refine PrivateCoin.ecomplexity_le_add hδ.le ?_
  set T : ℝ := 2 ^ Nat.clog 2 ⌈n / δ ^ 2⌉₊ with hTdef
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hT : (n : ℝ) ≤ δ ^ 2 * T := by
    have h₁ : (n : ℝ) / δ ^ 2 ≤ T := (Nat.le_ceil _).trans (by
      rw [hTdef]
      exact_mod_cast Nat.le_pow_clog one_lt_two _)
    rw [div_le_iff₀ hδ2] at h₁
    linarith
  have hTpos : 0 < T := by positivity
  have hcard : (Nat.card X * Nat.card Y : ℝ) ≤ 4 ^ n := by
    have : Nat.card X * Nat.card Y ≤ 4 ^ n := by
      calc Nat.card X * Nat.card Y ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul hX hY
        _ = 4 ^ n := by rw [← mul_pow]; norm_num
    exact_mod_cast this
  have hexp : Real.exp (-2 * δ ^ 2 * T) ≤ Real.exp (-2 * n) :=
    Real.exp_le_exp.mpr (by linarith)
  calc (Nat.card X * Nat.card Y : ℝ) * Real.exp (-2 * δ ^ 2 * T)
      ≤ 4 ^ n * Real.exp (-2 * δ ^ 2 * T) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ < 1 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have : Real.exp (-2 * δ ^ 2 * T) < 1 :=
          Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hδ2 hTpos])
        simpa using this
      · have : 4 ^ n * Real.exp (-2 * n) < 1 := by
          rw [show (-2 * n : ℝ) = -(2 * n) by ring, Real.exp_neg,
            ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
          exact four_pow_lt_exp_two_mul hn
        calc 4 ^ n * Real.exp (-2 * δ ^ 2 * T) ≤ 4 ^ n * Real.exp (-2 * n) :=
              mul_le_mul_of_nonneg_left hexp (by positivity)
          _ < 1 := this

end Cslib.Communication
