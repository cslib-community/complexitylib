/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.DenseRestrictionPredictor
public import CslibFrontier.Computability.Circuit.Boolean.MajorityFormula
public import CslibFrontier.Computability.Circuit.Boolean.Memorize
public import CslibFrontier.Computability.Circuit.Boolean.DepthFunctions
import CslibFrontier.Probability.Minimax
import CslibFrontier.Probability.PMF.Event
import Mathlib.Tactic

/-!
# Hard distributions for shallow formulas

The first two steps of the proof of [ChukhinKulikovMihajlinSmal2026], Lemma 6.3 (printed p. 15;
PDF p. 16). This is not Lemma 6.3 itself: its final step, rounding the distribution to a set, is
not formalized here.

* **A hard distribution** (`exists_hardDistribution`). If `D(g) > d + 18 + 3 ⌈log₂ n⌉`, some
  distribution `μ` on `{0, 1}ⁿ` makes every formula of `binaryCost` depth at most `d` predict `g`
  with accuracy below `9/16`. Otherwise minimax gives a distribution over such formulas that is
  right with probability at least `9/16` at every input
  (`Probability.PMF.exists_forall_toOuterMeasure_le`, the source's Lemma 3.6). Lemma 3.7 for
  formulas (`exists_eq_of_forall_sum_ne_le`, with `ε = 1/16`) then computes `g` in depth
  `d + 18 + 3 ⌈log₂ n⌉` (`exists_computes_of_forall_exists_accuracy_ge`). The source writes this
  added depth as `O(log n)`.
* **Removing the heavy points** (`exists_spread_hardDistribution`). For such a `μ` and
  `d ≥ ⌈log₂ n⌉ + ⌈log₂ K⌉`, memorizing `g` on the `K` heaviest points (`exists_memorize`) shows
  that they carry weight below `1/8`. The conditional distribution `ν` outside them has
  `ν(x) < 1/(7K)`, and every formula of depth at most `d` has accuracy below `9/14` under `ν`.

`exists_spread_hardDistribution_of_lt_formulaDepth` chains the two steps for
`d = ⌈log₂ n⌉ + ⌈log₂ K⌉`. Its hypothesis holds for some function on every number of bits `n` with
`(4n + 4)^{2^t} < 2 · 2^{2^n}` (`exists_lt_formulaDepth`, by the count of `depthFunctions`).

The source states the spread step for the formulas of depth at most `t ≤ d`; here all depths up
to `d` are covered. The source's assumption that the support of `μ` has more than `K` points is not
needed. If there are at most `K` points, they are all memorized and the accuracy would be one.

Still missing for Lemma 6.3:
* rounding `ν` to a random set `S` (including `x` with probability `K ν(x)`);
* Bernstein's inequality for `w_h = Σ_{x ∈ S} (1[h(x) = g(x)] - 2/3)`;
* the union bound over `depthFunctions n t` with `K = c_K 2^t log₂(4n + 4)`.

## Main results

* `Cslib.Circuits.Boolean.exists_computes_of_forall_exists_accuracy_ge`: minimax and
  amplification.
* `Cslib.Circuits.Boolean.exists_hardDistribution`: the hard distribution.
* `Cslib.Circuits.Boolean.exists_spread_hardDistribution`: removing the heavy points.
* `Cslib.Circuits.Boolean.exists_spread_hardDistribution_of_lt_formulaDepth`: both steps.
* `Cslib.Circuits.Boolean.exists_lt_formulaDepth`: deep functions exist.

## References

* [N. Chukhin, A. S. Kulikov, I. Mihajlin and A. V. Smal, *Solving One of Many Instances is
  Almost as Hard as Solving One*][ChukhinKulikovMihajlinSmal2026]
-/

public section

namespace Cslib.Circuits.Boolean

open Formula Cslib.Probability.PMF

variable {n : ℕ}

/-- The accuracy of a formula and its probability of missing `g` add up to one. -/
theorem accuracy_add_toOuterMeasure_ne (ν : PMF (BitString n)) (g : BitString n → Bool)
    (F : Formula signature n) :
    accuracy ν g F + (ν.toOuterMeasure {x | F.eval interpretation x ≠ g x}).toReal = 1 := by
  rw [toOuterMeasure_apply_toReal, accuracy, ← Finset.sum_add_distrib]
  refine (Finset.sum_congr rfl fun x _ => ?_).trans (sum_toReal ν)
  by_cases h : F.eval interpretation x = g x <;> simp [h]

/-- **Formulas that predict well against every distribution give a formula** (proof of
[ChukhinKulikovMihajlinSmal2026], Lemma 6.3, printed p. 15; PDF p. 16). If against every
distribution on `{0, 1}ⁿ` some formula of `binaryCost` depth at most `d` predicts `g` with accuracy
at least `9/16`, then some formula of depth at most `d + 18 + 3 ⌈log₂ n⌉` computes `g`. Minimax
(`Probability.PMF.exists_forall_toOuterMeasure_le`, the source's Lemma 3.6) gives a distribution
over these formulas that is right with probability `9/16` at every input; its push-forward to the
computed functions is amplified by Lemma 3.7 for formulas (`exists_eq_of_forall_sum_ne_le`) with
`ε = 1/16`, `m₁ = 5` and `m₂ = ⌈log₂ n⌉`. -/
theorem exists_computes_of_forall_exists_accuracy_ge (g : BooleanFunction n) (d : ℕ)
    (h : ∀ ν : PMF (BitString n), ∃ F : Formula signature n,
      F.depthWith binaryCost ≤ d ∧ 9 / 16 ≤ accuracy ν g F) :
    ∃ G : Formula signature n, G.Computes interpretation g ∧
      G.depthWith binaryCost ≤ d + 18 + 3 * Nat.clog 2 n := by
  classical
  let I := {F : Formula signature n // F.depthWith binaryCost ≤ d}
  have : Nonempty I := ⟨⟨.const false, by simp⟩⟩
  obtain ⟨μ, -, hμ⟩ := exists_forall_toOuterMeasure_le (I := I) (J := BitString n)
    (fun F x => F.1.eval interpretation x ≠ g x) (ε := 7 / 16) fun ν => by
      obtain ⟨F, hd, hacc⟩ := h ν
      exact ⟨⟨F, hd⟩, by have := accuracy_add_toOuterMeasure_ne ν g F; linarith⟩
  -- Push the distribution forward to the finitely many computed functions.
  set Λ := μ.map fun F : I => F.1.eval interpretation
  let H : (BitString n → Bool) → Formula signature n := fun f =>
    if hf : ∃ F : I, F.1.eval interpretation = f then hf.choose.1 else .const false
  have hH (f : BitString n → Bool) : (H f).depthWith binaryCost ≤ d := by
    simp only [H]
    split_ifs with hf
    · exact hf.choose.2
    · simp
  have hHeval (f : BitString n → Bool) (hf : Λ f ≠ 0) : (H f).eval interpretation = f := by
    have hmem : f ∈ Λ.support := hf
    rw [PMF.support_map] at hmem
    obtain ⟨F, -, hF⟩ := hmem
    have hex : ∃ F : I, F.1.eval interpretation = f := ⟨F, hF⟩
    simp only [H]
    rw [dite_eq_left_of_eq_true (eq_true hex)]
    exact hex.choose_spec
  obtain ⟨G, hG, hd⟩ := exists_eq_of_forall_sum_ne_le (w := fun f => (Λ f).toReal)
    (fun _ => ENNReal.toReal_nonneg) (sum_toReal Λ) hH Finset.univ g (ε := 1 / 16) (by norm_num)
    (fun x _ => by
      calc ∑ f with (H f).eval interpretation x ≠ g x, (Λ f).toReal
          = ∑ f, if f ∈ {f : BitString n → Bool | f x ≠ g x} then (Λ f).toReal else 0 := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun f _ => ?_
            by_cases hf : Λ f = 0
            · simp [hf]
            · simp [hHeval f hf]
        _ = (Λ.toOuterMeasure {f : BitString n → Bool | f x ≠ g x}).toReal := by
            convert (toOuterMeasure_apply_toReal Λ _).symm
        _ ≤ 1 / 2 - 1 / 16 := by
            rw [PMF.toOuterMeasure_map_apply]
            have : (fun F : I => F.1.eval interpretation) ⁻¹' {f | f x ≠ g x} =
                {F : I | F.1.eval interpretation x ≠ g x} := rfl
            rw [this]
            linarith [hμ x])
    (m₁ := 5) (m₂ := Nat.clog 2 n) (by norm_num)
    (by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      exact Nat.pow_le_pow_right two_pos (Nat.le_pow_clog one_lt_two n))
  exact ⟨G, fun x => hG x (Finset.mem_univ x), by omega⟩

/-- **A hard distribution** ([ChukhinKulikovMihajlinSmal2026], proof of Lemma 6.3, printed
p. 15; PDF p. 16). If `D(g)` exceeds `d + 18 + 3 ⌈log₂ n⌉`, the depth that Lemma 3.7 adds for
`ε = 1/16` and `Z = {0, 1}ⁿ`, then some distribution `μ` makes every formula of `binaryCost` depth
at most `d` inaccurate: `Pr_{x ∼ μ}[h(x) = g(x)] < 9/16`. -/
theorem exists_hardDistribution (g : BooleanFunction n) {d : ℕ}
    (hd : d + 18 + 3 * Nat.clog 2 n < formulaDepth g) :
    ∃ μ : PMF (BitString n), ∀ F : Formula signature n, F.depthWith binaryCost ≤ d →
      accuracy μ g F < 9 / 16 := by
  by_contra hno
  push Not at hno
  obtain ⟨G, hG, hGd⟩ := exists_computes_of_forall_exists_accuracy_ge g d fun ν => by
    obtain ⟨F, hF, hacc⟩ := hno ν
    exact ⟨F, hF, hacc⟩
  have := formulaDepth_le hG
  omega

open scoped Classical in
/-- Some set `T` of at most `K` points carries the largest weight: every point outside has weight at
most the average `μ(T) / K`. It is a `K`-set of largest weight, or every point when there are at
most `K`. -/
private theorem exists_heavy (μ : PMF (BitString n)) (K : ℕ) :
    ∃ T : Finset (BitString n), T.card ≤ K ∧
      ∀ x ∉ T, K * (μ x).toReal ≤ ∑ y ∈ T, (μ y).toReal := by
  by_cases hK : K ≤ (Finset.univ : Finset (BitString n)).card
  · obtain ⟨T, hT, hmax⟩ := (Finset.univ.powersetCard K).exists_max_image
      (fun T => ∑ y ∈ T, (μ y).toReal) (Finset.powersetCard_nonempty.2 hK)
    rw [Finset.mem_powersetCard] at hT
    refine ⟨T, hT.2.le, fun x hx => ?_⟩
    have hle (y : BitString n) (hy : y ∈ T) : (μ x).toReal ≤ (μ y).toReal := by
      have hxe : x ∉ T.erase y := fun h => hx (Finset.mem_of_mem_erase h)
      have hT' : insert x (T.erase y) ∈ Finset.univ.powersetCard K := by
        rw [Finset.mem_powersetCard, Finset.card_insert_of_notMem hxe,
          Finset.card_erase_of_mem hy, hT.2]
        have : 0 < T.card := Finset.card_pos.2 ⟨y, hy⟩
        exact ⟨Finset.subset_univ _, by omega⟩
      have h₁ := hmax _ hT'
      rw [Finset.sum_insert hxe] at h₁
      have h₂ := Finset.sum_erase_add T (fun y => (μ y).toReal) hy
      linarith
    calc (K : ℝ) * (μ x).toReal = ∑ _y ∈ T, (μ x).toReal := by
          rw [Finset.sum_const, hT.2, nsmul_eq_mul]
      _ ≤ ∑ y ∈ T, (μ y).toReal := Finset.sum_le_sum hle
  · exact ⟨Finset.univ, by omega, fun x hx => (hx (Finset.mem_univ x)).elim⟩

open scoped Classical in
/-- **Removing the heavy points** ([ChukhinKulikovMihajlinSmal2026], proof of Lemma 6.3, printed
p. 15; PDF p. 16). Let every formula of `binaryCost` depth at most `d` have accuracy below `9/16`
under `μ`, where `d ≥ ⌈log₂ n⌉ + ⌈log₂ K⌉` and `K ≥ 1`. Memorizing `g` on the `K` heaviest points
and using the better constant elsewhere would have accuracy `μ(T) + (1 - μ(T))/2`, so `μ(T) < 1/8`.
The conditional distribution `ν` of `μ` outside `T` then has `ν(x) < 1/(7K)` at every point, and
every formula of depth at most `d` has accuracy below `(9/16)/(7/8) = 9/14` under `ν`. -/
theorem exists_spread_hardDistribution (g : BitString n → Bool) {d K : ℕ}
    (hdK : Nat.clog 2 n + Nat.clog 2 K ≤ d) {μ : PMF (BitString n)}
    (hμ : ∀ F : Formula signature n, F.depthWith binaryCost ≤ d → accuracy μ g F < 9 / 16) :
    ∃ ν : PMF (BitString n), (∀ x, 7 * K * (ν x).toReal < 1) ∧
      ∀ F : Formula signature n, F.depthWith binaryCost ≤ d → accuracy ν g F < 9 / 14 := by
  obtain ⟨T, hTK, hheavy⟩ := exists_heavy μ K
  set m : BitString n → ℝ := fun x => (μ x).toReal
  have hm0 (x : BitString n) : 0 ≤ m x := ENNReal.toReal_nonneg
  have hm1 : ∑ x, m x = 1 := sum_toReal μ
  set a := ∑ x ∈ T, m x
  have hcompl : ∑ x ∈ Tᶜ, m x = 1 - a := by
    rw [← hm1, ← Finset.sum_compl_add_sum T]
    ring
  set A : Bool → ℝ := fun b => ∑ x ∈ Tᶜ, if g x = b then m x else 0
  have hA : A true + A false = 1 - a := by
    rw [← hcompl]
    simp only [A, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    cases g x <;> simp
  obtain ⟨b, hb⟩ : ∃ b, (1 - a) / 2 ≤ A b := by
    by_cases h : (1 - a) / 2 ≤ A true
    · exact ⟨true, h⟩
    · exact ⟨false, by linarith⟩
  -- Memorizing `g` on `T` with the better constant `b` outside.
  obtain ⟨F, hFT, hFc, hFd⟩ := exists_memorize g T b
  have hacc : accuracy μ g F = a + A b := by
    rw [accuracy, ← Finset.sum_add_sum_compl T]
    congr 1
    · exact Finset.sum_congr rfl fun x hx => by simp [hFT x hx, m]
    · refine Finset.sum_congr rfl fun x hx => ?_
      rw [hFc x (Finset.mem_compl.1 hx)]
      by_cases h : g x = b
      · simp [h, m]
      · simp [h, Ne.symm h]
  have ha : a < 1 / 8 := by
    have := hμ F (hFd.trans (by have := Nat.clog_mono_right 2 hTK; omega))
    linarith
  set c := 1 - a
  have hc : 7 / 8 < c := by linarith
  have hc0 : 0 < c := by linarith
  -- The conditional distribution outside `T`.
  have hw0 (x : BitString n) : 0 ≤ if x ∈ T then 0 else m x / c := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hm0 x) hc0.le
  have hsum : ∑ x, ENNReal.ofReal (if x ∈ T then 0 else m x / c) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg fun x _ => hw0 x, ← ENNReal.ofReal_one]
    congr 1
    have h1 : ∑ x, (if x ∈ T then 0 else m x / c) = ∑ x ∈ Tᶜ, m x / c := by
      rw [← Finset.sum_compl_add_sum T, Finset.sum_eq_zero (s := T) fun x hx => by simp [hx],
        add_zero]
      exact Finset.sum_congr rfl fun x hx => by simp [Finset.mem_compl.1 hx]
    rw [h1, ← Finset.sum_div, hcompl, div_self hc0.ne']
  set ν := PMF.ofFintype _ hsum
  have hν (x : BitString n) : (ν x).toReal = if x ∈ T then 0 else m x / c := by
    simp only [ν, PMF.ofFintype_apply]
    exact ENNReal.toReal_ofReal (hw0 x)
  refine ⟨ν, fun x => ?_, fun F hF => ?_⟩
  · rw [hν]
    split_ifs with hx
    · simp
    · have := hheavy x hx
      rw [show (7 : ℝ) * K * (m x / c) = 7 * (K * m x) / c by ring, div_lt_one hc0]
      nlinarith
  · have hle : accuracy ν g F ≤ accuracy μ g F / c := by
      rw [accuracy, accuracy, Finset.sum_div]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [hν]
      have hi : (0 : ℝ) ≤ if F.eval interpretation x = g x then 1 else 0 := by
        split_ifs <;> norm_num
      by_cases hx : x ∈ T
      · simp only [hx, ite_true, zero_mul]
        exact div_nonneg (mul_nonneg (hm0 x) hi) hc0.le
      · simp only [hx, ite_false]
        exact le_of_eq (by ring)
    have h1 := hμ F hF
    have h0 : 0 ≤ accuracy μ g F := Finset.sum_nonneg fun x _ =>
      mul_nonneg (hm0 x) (by split_ifs <;> norm_num)
    have h2 : accuracy μ g F / c < 9 / 14 := by
      rw [div_lt_iff₀ hc0]
      nlinarith
    linarith

/-- **A spread hard distribution** ([ChukhinKulikovMihajlinSmal2026], proof of Lemma 6.3, printed
p. 15; PDF p. 16): the two steps together. If `D(g)` exceeds `d + 18 + 3 ⌈log₂ n⌉` for
`d = ⌈log₂ n⌉ + ⌈log₂ K⌉`, then some distribution `ν` has `ν(x) < 1/(7K)` at every point, and every
formula of `binaryCost` depth at most `d` predicts `g` under `ν` with accuracy below `9/14`. -/
theorem exists_spread_hardDistribution_of_lt_formulaDepth (g : BooleanFunction n) {K : ℕ}
    (hg : Nat.clog 2 n + Nat.clog 2 K + 18 + 3 * Nat.clog 2 n < formulaDepth g) :
    ∃ ν : PMF (BitString n), (∀ x, 7 * K * (ν x).toReal < 1) ∧
      ∀ F : Formula signature n, F.depthWith binaryCost ≤ Nat.clog 2 n + Nat.clog 2 K →
        accuracy ν g F < 9 / 14 :=
  let ⟨_, hμ⟩ := exists_hardDistribution g hg
  exists_spread_hardDistribution g le_rfl hμ

/-- **Most functions are deep** (a counting argument): if `(4n + 4)^{2^t} < 2 · 2^{2^n}`, some
function on `n` bits has formula depth larger than `t`, because formulas of depth at most `t`
compute at most `(4n + 4)^{2^t} / 2` functions (`two_mul_card_depthFunctions_le`). -/
theorem exists_lt_formulaDepth {t : ℕ} (ht : (4 * n + 4) ^ 2 ^ t < 2 * 2 ^ 2 ^ n) :
    ∃ g : BooleanFunction n, t < formulaDepth g := by
  classical
  have hcard : (depthFunctions n t).card < (Finset.univ : Finset (BooleanFunction n)).card := by
    have := two_mul_card_depthFunctions_le (n := n) t
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    omega
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨g, Nat.lt_of_not_le fun hle => hg ?_⟩
  obtain ⟨F, hF, hd⟩ := exists_computes_depthWith_eq_formulaDepth g
  have := (eval_mem_depthFunctions F (hd.trans_le hle)).1
  rwa [computes_iff.1 hF] at this

end Cslib.Circuits.Boolean
