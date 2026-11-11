/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.WordSum.LayerWeight
public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.WordSum.Runs

/-!
# The sum over type words

The second trace moment of the `IMM_{n,n}` operator is bounded by a sum over words
`τ : Fin n → Bool` that give every layer a type, `true` for type `𝒟` and `false` for type `𝒩`
[OpenAI, §4][OpenAI2026DepthFive]. The weight of a word is

`n ^ (-w τ) * α ^ (-d_V τ) * β ^ (d_U τ) * ∏ t ∈ N_V τ, (1 + α⁻¹ * n ^ (-h_t))`,

where `w τ` counts the switches of type between consecutive layers, `d_V τ` and `d_U τ` count
the layers of type `𝒟` that are differentiated and multiplied, `N_V τ` is the set of
differentiated layers of type `𝒩`, and `h_t` counts the neighbours of layer `t` of type `𝒩`.

The sum of the weights of all words is `exp (O(√n))` [OpenAI, §5][OpenAI2026DepthFive]. A
layer of type `𝒩` whose correction factor is large lies between two layers of type `𝒟`, and its
two switches pay for the factor. The remaining weight is bounded run by run in
`Cslib.Circuits.DepthFive.runWeight_le`, which gives a bound that decays geometrically in the
number of switches, and a word is determined by its first type and its set of switches.

## Main definitions

* `Params.wordWeight`: the weight of a type word.

## Main results

* `Params.sum_wordWeight_le`: the weights of all type words sum to at most `exp (8 * √n)`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §5, word-sum lemma (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive.Params

variable (p : Params) (τ : Fin p.n → Bool)

/-- The number of switches of a type word: positions whose type differs from the previous one. -/
def switches : ℕ :=
  (Finset.univ.filter fun j : Fin p.n => ∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j).card

/-- The number of differentiated layers of type `𝒟`. -/
def dV : ℕ := (Finset.univ.filter fun t : Fin p.n => p.isV t ∧ τ t).card

/-- The number of multiplied layers of type `𝒟`. -/
def dU : ℕ := (Finset.univ.filter fun t : Fin p.n => ¬ p.isV t ∧ τ t).card

/-- The number of layers adjacent to layer `t` that have type `𝒩`. For a layer `t` of type `𝒩`
this is the number of internal vertices of `t` whose two incident layers have type `𝒩`. -/
def nbrN (t : Fin p.n) : ℕ :=
  (Finset.univ.filter fun i : Fin p.n =>
    ((i : ℕ) + 1 = t ∨ (t : ℕ) + 1 = i) ∧ τ i = false).card

/-- The weight of a type word [OpenAI, §5][OpenAI2026DepthFive]. -/
noncomputable def wordWeight : ℝ :=
  ((p.n : ℝ)⁻¹) ^ p.switches τ * (p.α⁻¹) ^ p.dV τ * p.β ^ p.dU τ *
    ∏ t ∈ Finset.univ.filter fun t : Fin p.n => p.isV t ∧ τ t = false,
      (1 + p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t)

variable {p} {τ}

/-- The extension of a type word to all natural numbers by type `𝒩`. -/
private def wordExt (τ : Fin p.n → Bool) (t : ℕ) : Bool := if h : t < p.n then τ ⟨t, h⟩ else false

private theorem wordExt_val (t : Fin p.n) : wordExt τ t = τ t := by simp [wordExt]

private theorem switch_iff (j : Fin p.n) :
    (∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j) ↔
      1 ≤ (j : ℕ) ∧ wordExt τ (j - 1) ≠ wordExt τ j := by
  constructor
  · rintro ⟨i, hi, h⟩
    have : (j : ℕ) - 1 = i := by omega
    exact ⟨by omega, by rwa [this, wordExt_val, wordExt_val]⟩
  · rintro ⟨hj, h⟩
    refine ⟨⟨j - 1, by omega⟩, by simp; omega, ?_⟩
    simpa [wordExt, show (j : ℕ) - 1 < p.n by omega] using h

private theorem switches_eq (hn : 0 < p.n) :
    p.switches τ = switchCount (wordExt τ) (p.n - 1) := by
  rw [switches, Finset.card_filter, switchCount, Nat.sub_add_cancel hn,
    ← Fin.sum_univ_eq_sum_range fun t => if 1 ≤ t ∧ wordExt τ (t - 1) ≠ wordExt τ t then 1 else 0]
  exact Finset.sum_congr rfl fun j _ => if_congr (switch_iff j) rfl rfl

/-- A word is determined by its first type and its switches, so the words with `w` switches
are at most `2 * choose n w`. -/
private theorem sum_pow_switches_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ τ : Fin p.n → Bool, x ^ p.switches τ ≤ 2 * (1 + x) ^ p.n := by
  classical
  let Φ (τ : Fin p.n → Bool) : Bool × Finset (Fin p.n) :=
    (wordExt τ 0, Finset.univ.filter fun j : Fin p.n => ∃ i : Fin p.n, (i : ℕ) + 1 = j ∧ τ i ≠ τ j)
  have hΦ : Function.Injective Φ := by
    intro τ τ' h
    have h₀ : wordExt τ 0 = wordExt τ' 0 := congrArg Prod.fst h
    have h₁ (j : Fin p.n) : (1 ≤ (j : ℕ) ∧ wordExt τ (j - 1) ≠ wordExt τ j) ↔
        (1 ≤ (j : ℕ) ∧ wordExt τ' (j - 1) ≠ wordExt τ' j) := by
      rw [← switch_iff, ← switch_iff]
      simpa [Φ] using Finset.ext_iff.1 (congrArg Prod.snd h) j
    have key (t : ℕ) : wordExt τ t = wordExt τ' t := by
      induction t with
      | zero => exact h₀
      | succ t ih =>
        by_cases ht : t + 1 < p.n
        · have := h₁ ⟨t + 1, ht⟩
          simp only [Nat.le_add_left, Nat.add_sub_cancel, true_and, ih] at this
          revert this
          cases wordExt τ' t <;> cases wordExt τ (t + 1) <;> cases wordExt τ' (t + 1) <;> simp
        · simp [wordExt, ht]
    funext t
    rw [← wordExt_val (τ := τ) t, ← wordExt_val (τ := τ') t, key]
  calc ∑ τ : Fin p.n → Bool, x ^ p.switches τ
      = ∑ y ∈ Finset.univ.image Φ, x ^ y.2.card := by
        rw [Finset.sum_image fun _ _ _ _ h => hΦ h]; rfl
    _ ≤ ∑ y : Bool × Finset (Fin p.n), x ^ y.2.card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
    _ = 2 * (1 + x) ^ p.n := by
        rw [Fintype.sum_prod_type, add_comm, ← Fin.sum_pow_mul_eq_add_pow]
        simp [two_mul]

private theorem pow_dV_mul_pow_dU :
    p.α⁻¹ ^ p.dV τ * p.β ^ p.dU τ =
      ∏ t ∈ Finset.range p.n, if wordExt τ t then p.layerWeight t else 1 := by
  rw [← Fin.prod_univ_eq_prod_range fun t => if wordExt τ t then p.layerWeight t else 1,
    dV, dU, ← Finset.prod_const, ← Finset.prod_const, Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [wordExt_val, layerWeight_val]
  cases p.isV t <;> cases τ t <;> simp

/-- The correction factors of the layers of type `𝒩`: the first layer costs `1 + √n`, an
isolated layer twice its weight, and every other layer `1 + 1 / √n`. -/
private theorem prod_correction_le (hp : p.Good) :
    ∏ t ∈ Finset.univ.filter fun t : Fin p.n => p.isV t ∧ τ t = false,
        (1 + p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t) ≤
      (1 + √(p.n : ℝ)) * (1 + (√(p.n : ℝ))⁻¹) ^ p.n *
        ∏ t ∈ Finset.range (p.n - 1), if 1 ≤ t ∧ p.isVNat t ∧ wordExt τ (t - 1) ∧
          wordExt τ t = false ∧ wordExt τ (t + 1) then 2 * p.layerWeight t else 1 := by
  set y := √(p.n : ℝ) with hy
  have hy1 : 1 ≤ y := hp.one_le_sqrt
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hn := hp.n_pos
  have hα := hp.α_pos
  have hA1 : 1 ≤ p.α⁻¹ := (one_le_inv₀ hα).2 hp.α_lt_one.le
  have hAy : p.α⁻¹ ≤ y := hp.inv_α_le
  have hyy : (p.n : ℝ) = y * y := (Real.mul_self_sqrt (Nat.cast_nonneg _)).symm
  have hn1 : (p.n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  have hn0 : 0 ≤ (p.n : ℝ)⁻¹ := by positivity
  let F (t : ℕ) : ℝ := if 1 ≤ t ∧ p.isVNat t ∧ wordExt τ (t - 1) ∧
    wordExt τ t = false ∧ wordExt τ (t + 1) then 2 * p.layerWeight t else 1
  have hF (t : ℕ) : 1 ≤ F t := by
    simp only [F]
    split_ifs with h
    · rw [layerWeight, ite_eq_left h.2.1]; linarith
    · exact le_rfl
  have hlast : F (p.n - 1) = 1 := by
    simp [F, wordExt, Nat.sub_add_cancel hn]
  have hrange := Finset.prod_range_succ F (p.n - 1)
  rw [Nat.sub_add_cancel hn, hlast, mul_one] at hrange
  have hpt (t : Fin p.n) : (if p.isV t ∧ τ t = false
      then 1 + p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t else 1) ≤
      (if (t : ℕ) = 0 then 1 + y else 1) * (1 + y⁻¹) * F t := by
    have hf2 : 1 ≤ 1 + y⁻¹ := by linarith [inv_pos.2 hy0]
    have hf1 : (1 : ℝ) ≤ if (t : ℕ) = 0 then 1 + y else 1 := by split_ifs <;> linarith
    by_cases hNV : p.isV t = true ∧ τ t = false
    · rw [ite_eq_left hNV]
      have hx : ((p.n : ℝ)⁻¹) ^ p.nbrN τ t ≤ 1 := pow_le_one₀ hn0 hn1
      have hφ : 1 + p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t ≤ 1 + p.α⁻¹ := by
        nlinarith [mul_le_mul_of_nonneg_left hx (zero_le_one.trans hA1)]
      by_cases ht0 : (t : ℕ) = 0
      · rw [ite_eq_left ht0]
        calc _ ≤ 1 + y := by linarith
          _ ≤ (1 + y) * (1 + y⁻¹) := le_mul_of_one_le_right (by linarith) hf2
          _ ≤ _ := le_mul_of_one_le_right (by positivity) (hF t)
      · rw [ite_eq_right ht0, one_mul]
        have hV : p.isVNat t := by simpa [isV] using hNV.1
        have ht : wordExt τ t = false := by rw [wordExt_val]; exact hNV.2
        have htn : (t : ℕ) + 1 < p.n := by
          by_contra h
          have := p.not_isV_last t (by omega)
          simp [this] at hNV
        by_cases hiso : wordExt τ (t - 1) = true ∧ wordExt τ (t + 1) = true
        · have : F t = 2 * p.α⁻¹ := by
            simp only [F]
            rw [ite_eq_left ⟨by omega, hV, hiso.1, ht, hiso.2⟩, layerWeight, ite_eq_left hV]
          rw [this]
          calc _ ≤ 1 * (2 * p.α⁻¹) := by linarith
            _ ≤ _ := mul_le_mul_of_nonneg_right hf2 (by positivity)
        · have hpos : 1 ≤ p.nbrN τ t := by
            rw [nbrN, Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Finset.card_pos]
            by_cases h1 : wordExt τ (t - 1) = true
            · refine ⟨⟨t + 1, htn⟩, ?_⟩
              have : wordExt τ (t + 1) = false := by simpa [h1] using hiso
              simpa [wordExt, htn] using this
            · refine ⟨⟨t - 1, by omega⟩, ?_⟩
              have h1' : wordExt τ (t - 1) = false := by simpa using h1
              have : (t : ℕ) - 1 + 1 = t := by omega
              simpa [wordExt, show (t : ℕ) - 1 < p.n by omega, this] using h1'
          have hx' : ((p.n : ℝ)⁻¹) ^ p.nbrN τ t ≤ (p.n : ℝ)⁻¹ := by
            simpa using pow_le_pow_of_le_one hn0 hn1 hpos
          have hle : p.α⁻¹ * ((p.n : ℝ)⁻¹) ^ p.nbrN τ t ≤ y⁻¹ :=
            calc _ ≤ y * (p.n : ℝ)⁻¹ := mul_le_mul hAy hx' (by positivity) hy0.le
              _ = y⁻¹ := by rw [hyy]; field_simp
          calc _ ≤ 1 + y⁻¹ := by linarith
            _ ≤ _ := le_mul_of_one_le_right (by positivity) (hF t)
    · rw [ite_eq_right hNV]
      exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf1 hf2) (hF t)
  rw [Finset.prod_filter]
  refine (Finset.prod_le_prod₀ (fun t _ => ?_) fun t _ => hpt t).trans_eq ?_
  · split_ifs <;> positivity
  · rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Fin.prod_univ_eq_prod_range (fun t => if t = 0 then 1 + y else 1),
      Finset.prod_ite_eq', ite_eq_left (Finset.mem_range.2 hn), Fin.prod_univ_eq_prod_range F,
      hrange]

/-- The weight of a word decays geometrically in its number of switches. -/
private theorem wordWeight_le (hp : p.Good) (τ : Fin p.n → Bool) :
    p.wordWeight τ ≤ (1 + √(p.n : ℝ)) * (1 + (√(p.n : ℝ))⁻¹) ^ p.n * (2 * √(p.n : ℝ)) ^ 2 *
      (2 * √(p.n : ℝ) / p.n) ^ p.switches τ := by
  have hn := hp.n_pos
  have hy1 := hp.one_le_sqrt
  have hrun := runWeight_le (τ := wordExt τ) (S := p.isVNat) (c := p.layerWeight)
    (B := 2 * √(p.n : ℝ)) (N := p.n - 1)
    (fun t => by unfold layerWeight; split_ifs <;> [exact inv_nonneg.2 hp.α_pos.le;
      exact hp.β_pos.le]) (by linarith) (by nlinarith)
    fun i j hj => prod_layerWeight_le hp i (by omega)
  rw [← switches_eq hn, runWeight, Nat.sub_add_cancel hn, ← pow_dV_mul_pow_dU] at hrun
  have hD : 0 ≤ p.α⁻¹ ^ p.dV τ * p.β ^ p.dU τ :=
    mul_nonneg (pow_nonneg (inv_nonneg.2 hp.α_pos.le) _) (pow_nonneg hp.β_pos.le _)
  rw [wordWeight]
  refine (mul_le_mul_of_nonneg_left (prod_correction_le hp)
    (by rw [mul_assoc]; exact mul_nonneg (by positivity) hD)).trans ?_
  have h := mul_le_mul_of_nonneg_left hrun
    (by positivity : 0 ≤ (1 + √(p.n : ℝ)) * (1 + (√(p.n : ℝ))⁻¹) ^ p.n *
      ((p.n : ℝ)⁻¹) ^ p.switches τ)
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · ring
  · rw [div_eq_mul_inv, mul_pow _ (p.n : ℝ)⁻¹, pow_add]; ring

/-- The sum of the weights of all type words is `exp (O(√n))`: the word-sum lemma of
[OpenAI, §5][OpenAI2026DepthFive]. -/
theorem sum_wordWeight_le (hp : p.Good) :
    ∑ τ : Fin p.n → Bool, p.wordWeight τ ≤ Real.exp (8 * √(p.n : ℝ)) := by
  set y := √(p.n : ℝ) with hy
  have hy1 : 1 ≤ y := hp.one_le_sqrt
  have hy0 : 0 < y := zero_lt_one.trans_le hy1
  have hn : (0 : ℝ) < p.n := by exact_mod_cast hp.n_pos
  have hyy : (p.n : ℝ) = y * y := (Real.mul_self_sqrt hn.le).symm
  have h₁ : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have h₂ : (1 + y⁻¹) ^ p.n ≤ Real.exp y := by
    calc (1 + y⁻¹) ^ p.n ≤ Real.exp y⁻¹ ^ p.n :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp y⁻¹]) _
      _ = Real.exp y := by rw [← Real.exp_nat_mul, hyy]; congr 1; field_simp
  have h₃ : (1 + 2 * y / p.n) ^ p.n ≤ Real.exp (2 * y) := by
    calc (1 + 2 * y / p.n) ^ p.n ≤ Real.exp (2 * y / p.n) ^ p.n :=
          pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * y / p.n)]) _
      _ = Real.exp (2 * y) := by rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h₄ : (2 * y) ^ 2 * 2 ≤ Real.exp (4 * y) := by
    have := Real.quadratic_le_exp_of_nonneg (x := 4 * y) (by positivity)
    nlinarith
  calc ∑ τ : Fin p.n → Bool, p.wordWeight τ
      ≤ ∑ τ : Fin p.n → Bool, (1 + y) * (1 + y⁻¹) ^ p.n * (2 * y) ^ 2 *
          (2 * y / p.n) ^ p.switches τ := Finset.sum_le_sum fun τ _ => wordWeight_le hp τ
    _ ≤ (1 + y) * (1 + y⁻¹) ^ p.n * (2 * y) ^ 2 * (2 * (1 + 2 * y / p.n) ^ p.n) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_pow_switches_le (by positivity)) (by positivity)
    _ = (1 + y) * (1 + y⁻¹) ^ p.n * ((2 * y) ^ 2 * 2) * (1 + 2 * y / p.n) ^ p.n := by ring
    _ ≤ Real.exp y * Real.exp y * Real.exp (4 * y) * Real.exp (2 * y) := by gcongr
    _ = Real.exp (8 * y) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf

end Cslib.Circuits.DepthFive.Params
