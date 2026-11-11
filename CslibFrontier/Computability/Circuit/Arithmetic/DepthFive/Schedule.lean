/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.DepthFive.Params

/-!
# The balanced layer schedule

The rank lower bound for `IMM_{n,n}` differentiates in `k` of the `n` matrix layers and
multiplies in the other `m = k + s`. The layers are ordered by the word
`V U^{ℓ₁} V U^{ℓ₂} ⋯ V U^{ℓ_k}` with `ℓᵢ = 1 + ⌊i s / k⌋ - ⌊(i - 1) s / k⌋`
[OpenAI, §4][OpenAI2026DepthFive]: the `i`-th differentiated layer, counting from zero, is
layer `2 i + ⌊i s / k⌋`. No two differentiated layers are adjacent, the first layer is
differentiated and the last is multiplied, and every interval of layers is balanced up to a
bounded discrepancy.

## Main definitions

* `Params.isV`: whether a layer is differentiated.
* `Params.layerVar`: the variables of the differentiated layers of `IMM_{n,n}`.

## Main results

* `Params.card_isV`: exactly `k` layers are differentiated.
* `Params.isV_zero`, `Params.not_isV_last`, `Params.not_isV_succ`: the first layer is
  differentiated, the last is multiplied, and no two differentiated layers are adjacent.
* `Params.discrepancy_le`: an interval with `a` differentiated and `u` multiplied layers has
  `a - ρ * u ≤ 1 + ρ`.

## References

* [OpenAI, *Homogeneous depth-five lower bounds for iterated matrix
  multiplication*][OpenAI2026DepthFive], §4 and §5 (unrefereed preprint)
-/

@[expose] public section

namespace Cslib.Circuits.DepthFive.Params

variable (p : Params)

/-- Whether layer `t` is differentiated in the balanced schedule: the `i`-th differentiated layer
is layer `2 * i + i * s / k`. -/
def isV (t : Fin p.n) : Bool :=
  decide (∃ i < p.k, (t : ℕ) = 2 * i + i * p.s / p.k)

/-- The variables of `IMM_{n,n}` that belong to a differentiated layer. Every layer keeps all
its `n ^ 2` variables. -/
def layerVar (x : Fin p.n × Fin p.n × Fin p.n) : Prop := p.isV x.1

instance : DecidablePred p.layerVar := fun x => inferInstanceAs (Decidable (p.isV x.1 = true))

variable {p}

/-- Consecutive differentiated layers are at least two apart. -/
private theorem pos_add_two_le {r r' : ℕ} (h : r < r') :
    2 * r + r * p.s / p.k + 2 ≤ 2 * r' + r' * p.s / p.k := by
  have := Nat.div_le_div_right (c := p.k) (Nat.mul_le_mul_right p.s h.le)
  omega

/-- Every differentiated layer is followed by a layer. -/
private theorem pos_add_two_le_n {r : ℕ} (h : r < p.k) : 2 * r + r * p.s / p.k + 2 ≤ p.n := by
  have h₁ : r * p.s / p.k ≤ p.s :=
    Nat.div_le_of_le_mul (Nat.mul_le_mul_right p.s h.le)
  have := p.hkm; have := p.hks
  omega

/-- The differentiated layers that satisfy `Q` correspond to their indices. -/
private theorem card_filter_isV (Q : ℕ → Prop) [DecidablePred Q] :
    (Finset.univ.filter fun t : Fin p.n => Q t ∧ p.isV t).card =
      ((Finset.range p.k).filter fun r => Q (2 * r + r * p.s / p.k)).card := by
  symm
  refine Finset.card_bij
    (fun r hr => ⟨2 * r + r * p.s / p.k, by
      have := pos_add_two_le_n (Finset.mem_range.1 (Finset.mem_filter.1 hr).1); omega⟩)
    (fun r hr => ?_) (fun r hr r' hr' h => ?_) (fun t ht => ?_)
  · simp only [Finset.mem_filter, Finset.mem_range] at hr
    simpa [isV] using ⟨hr.2, r, hr.1, rfl⟩
  · have h := congrArg Fin.val h
    simp only at h
    rcases lt_trichotomy r r' with h' | h' | h'
    · have := pos_add_two_le (p := p) h'; omega
    · exact h'
    · have := pos_add_two_le (p := p) h'; omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isV, decide_eq_true_eq] at ht
    obtain ⟨hQ, r, hr, ht⟩ := ht
    exact ⟨r, by simpa [hr, ← ht] using hQ, Fin.ext ht.symm⟩

/-- The balanced schedule differentiates exactly `k` layers. -/
theorem card_isV : (Finset.univ.filter fun t : Fin p.n => p.isV t).card = p.k := by
  simpa using card_filter_isV (p := p) fun _ => True

/-- The first layer is differentiated. -/
theorem isV_zero (hk : 0 < p.k) (t : Fin p.n) (ht : (t : ℕ) = 0) : p.isV t := by
  simpa [isV] using ⟨0, hk, by simpa using ht⟩

/-- The last layer is multiplied. -/
theorem not_isV_last (t : Fin p.n) (ht : (t : ℕ) + 1 = p.n) : p.isV t = false := by
  simp only [isV, decide_eq_false_iff_not, not_exists, not_and]
  intro r hr h
  have := pos_add_two_le_n hr
  omega

/-- No two differentiated layers are adjacent. -/
theorem not_isV_succ {t t' : Fin p.n} (ht : p.isV t) (h : (t : ℕ) + 1 = t') :
    p.isV t' = false := by
  simp only [isV, decide_eq_true_eq, decide_eq_false_iff_not, not_exists, not_and] at ht ⊢
  obtain ⟨r, -, hr⟩ := ht
  intro r' _ hr'
  rcases lt_trichotomy r r' with h' | h' | h'
  · have := pos_add_two_le (p := p) h'; omega
  · subst h'; omega
  · have := pos_add_two_le (p := p) h'; omega

/-- The arithmetic of the discrepancy bound: `d + 1` consecutive differentiated layers span more
than `d * n / k` layers. -/
private theorem discrepancy_arith {r d c L : ℕ} (hk : 0 < p.k) (hc : c ≤ d + 1)
    (hL : 2 * (r + d) + (r + d) * p.s / p.k + 1 - (2 * r + r * p.s / p.k) ≤ L) :
    p.n * c ≤ p.k * L + p.n := by
  have hd₁ : p.k * (r * p.s / p.k) ≤ r * p.s := Nat.mul_div_le _ _
  have hd₂ : (r + d) * p.s < p.k * ((r + d) * p.s / p.k) + p.k := Nat.lt_mul_div_succ _ hk
  have hn : p.n = 2 * p.k + p.s := by have := p.hkm; have := p.hks; omega
  have hmono := Nat.div_le_div_right (c := p.k) (Nat.mul_le_mul_right p.s (Nat.le_add_right r d))
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hmono
  have hL' : 2 * d + e + 1 ≤ L := by omega
  rw [he] at hd₂
  calc p.n * c ≤ p.n * (d + 1) := Nat.mul_le_mul_left _ hc
    _ ≤ p.k * (2 * d + e + 1) + p.n := by rw [hn]; nlinarith
    _ ≤ _ := by gcongr

/-- An interval of layers with `a` differentiated layers among `L` has `n * a ≤ k * L + n`. -/
private theorem discrepancy_nat (i j : ℕ) :
    p.n * (Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ p.isV t).card ≤
      p.k * (Finset.univ.filter fun t : Fin p.n => i ≤ t ∧ (t : ℕ) < j).card + p.n := by
  rw [card_filter_isV fun t => i ≤ t ∧ t < j]
  set R := (Finset.range p.k).filter fun r => i ≤ 2 * r + r * p.s / p.k ∧
    2 * r + r * p.s / p.k < j with hR
  rcases R.eq_empty_or_nonempty with h0 | hne
  · simp [h0]
  have hmem {r : ℕ} (hr : r ∈ R) : r < p.k ∧ i ≤ 2 * r + r * p.s / p.k ∧
      2 * r + r * p.s / p.k < j := by simpa [hR] using hr
  obtain ⟨h₁k, h₁i, -⟩ := hmem (R.min'_mem hne)
  obtain ⟨h₂k, -, h₂j⟩ := hmem (R.max'_mem hne)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (R.min'_le _ (R.max'_mem hne))
  rw [hd] at h₂k h₂j
  have hn₂ := pos_add_two_le_n h₂k
  refine discrepancy_arith (r := R.min' hne) (d := d) (by omega) ?_ ?_
  · have := Nat.card_Icc (R.min' hne) (R.max' hne)
    have := Finset.card_le_card (s := R) (t := Finset.Icc (R.min' hne) (R.max' hne))
      fun r hr => Finset.mem_Icc.2 ⟨R.min'_le r hr, R.le_max' r hr⟩
    omega
  · have hn₁ := pos_add_two_le_n h₁k
    have := Fin.card_Icc (a := (⟨2 * R.min' hne + R.min' hne * p.s / p.k, by omega⟩ : Fin p.n))
      (b := ⟨2 * (R.min' hne + d) + (R.min' hne + d) * p.s / p.k, by omega⟩)
    simp only at this
    rw [← this]
    refine Finset.card_le_card fun t ht => ?_
    simp only [Finset.mem_Icc, Fin.le_def] at ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

/-- Every interval of layers is balanced: the number of differentiated layers exceeds `ρ` times
the number of multiplied layers by at most `1 + ρ` [OpenAI, §5][OpenAI2026DepthFive]. -/
theorem discrepancy_le (i j : ℕ) :
    ((Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ p.isV t).card : ℝ) -
      p.ρ * (Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ ¬ p.isV t).card ≤
      1 + p.ρ := by
  have h := discrepancy_nat (p := p) i j
  rw [← Finset.card_filter_add_card_filter_not (fun t : Fin p.n => p.isV t)
    (s := Finset.univ.filter fun t : Fin p.n => i ≤ t ∧ (t : ℕ) < j),
    Finset.filter_filter, Finset.filter_filter] at h
  set a := (Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ p.isV t).card
  set u := (Finset.univ.filter fun t : Fin p.n => (i ≤ t ∧ (t : ℕ) < j) ∧ ¬ p.isV t).card
  rcases Nat.eq_zero_or_pos p.m with hm | hm
  · have hk : p.k = 0 := by have := p.hks; omega
    have hn : p.n = 0 := by have := p.hkm; omega
    have ha : a = 0 := Finset.card_eq_zero.2 <| Finset.filter_eq_empty_iff.2
      fun t => absurd t.isLt (by omega)
    simp [ρ, hk, ha]
  · have hm' : (0 : ℝ) < p.m := by exact_mod_cast hm
    have h' : (p.n : ℝ) * a ≤ p.k * (a + u) + p.n := by exact_mod_cast h
    have hn : (p.n : ℝ) = p.k + p.m := by exact_mod_cast p.hkm.symm
    rw [ρ, ← sub_nonneg]
    have : 1 + (p.k : ℝ) / p.m - (a - p.k / p.m * u) =
        (p.k * (a + u) + p.n - p.n * a) / p.m := by
      rw [hn]; field_simp; ring
    rw [this]
    exact div_nonneg (by linarith) hm'.le

end Cslib.Circuits.DepthFive.Params
