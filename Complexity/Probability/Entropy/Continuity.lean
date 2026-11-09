/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import Complexity.Probability.MutualInformation
public import Complexity.Probability.StatisticalDistance
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Complexity.Probability.Divergence
import Complexity.Probability.Entropy.Fano
import Complexity.Probability.PMF.Map

/-!
# Continuity of conditional entropy

Conditional entropy and conditional mutual information are uniformly continuous in statistical
distance, with a modulus that does not depend on the alphabet of the observation. For joint laws
`P` and `Q` of an observation `Y` and a hidden value `X : α` with `dist P Q ≤ ε`,
`|H(X | Y)_P - H(X | Y)_Q| ≤ ε log₂ |α| + (1 + ε) h₂(ε / (1 + ε))`, where `h₂` is the binary
entropy in bits. This is the classical case of the Alicki–Fannes–Winter bound in the form of
Winter [Winter2016]. Bounds of this kind move entropy estimates between statistically close real
and simulated views, as in information-theoretic lower bounds for garbled circuits
[JanuzelliRosulekRoy2025].

The proof is Winter's. Write `P + d Δ⁻ = Q + d Δ⁺` with `d = dist P Q`, where `Δ⁺` and `Δ⁻` are
the normalized positive and negative parts of `P - Q`, and compare both sides through the mixture
that tosses a coin with bias `d / (1 + d)`. Conditional entropy is concave
(`sum_mul_conditionalEntropy_le_conditionalEntropy_bind`) and fails to be convex by at most the
entropy of the coin (`conditionalEntropy_bind_le`); the coin contributes the modulus.

## Main definitions

* `Cslib.Probability.PMF.condEntropyModulus`: the modulus `(1 + ε) h₂(ε / (1 + ε))`, in bits.

## Main results

* `Cslib.Probability.PMF.sum_mul_conditionalEntropy_le_conditionalEntropy_bind`: concavity of
  conditional entropy.
* `Cslib.Probability.PMF.conditionalEntropy_bind_le`: a mixture adds at most the entropy of the
  mixing law.
* `Cslib.Probability.PMF.abs_conditionalEntropy_sub_le`: continuity of conditional entropy.
* `Cslib.Probability.PMF.sub_le_conditionalEntropy_of_dist_le`: transfer of a lower bound on
  conditional entropy to a statistically close law.
* `Cslib.Probability.PMF.abs_condMutualInfo_sub_le`: continuity of conditional mutual
  information, with twice the modulus.

## References

* [A. Winter, *Tight uniform continuity bounds for quantum entropies: conditional entropy,
  relative entropy distance and energy constraints*][Winter2016]
* [J. Januzelli, M. Rosulek, L. Roy, *Lower Bounds for Garbled Circuits from Shannon-Type
  Information Inequalities*][JanuzelliRosulekRoy2025]
-/

public section

namespace Cslib.Probability.PMF

open scoped NNReal

variable {ι Ω α β γ : Type*}

/-! ### Mixtures -/

/-- Tagging each component of a mixture with its index, the conditional entropy given the tag
and the observation is the average conditional entropy of the components. -/
private theorem conditionalEntropy_bind_tag [Fintype ι] [Finite β] [Finite α] (p : PMF ι)
    (R : ι → PMF (β × α)) :
    conditionalEntropy ((p.bind fun i => (R i).map (i, ·)).map
        fun t => ((t.1, t.2.1), t.2.2)) =
      ∑ i, (p i).toReal * conditionalEntropy (R i) := by
  set M := p.bind fun i => (R i).map (i, ·)
  have hM : entropy (M.map fun t => ((t.1, t.2.1), t.2.2)) = entropy M :=
    entropy_map_of_injective M fun s t h => by
      obtain ⟨i, b, a⟩ := s
      obtain ⟨j, b', a'⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h]
  have hfst : (M.map fun t => ((t.1, t.2.1), t.2.2)).map Prod.fst =
      p.bind fun i => ((R i).map Prod.fst).map (i, ·) := by
    simp only [M, PMF.map_bind, PMF.map_comp]
    rfl
  rw [conditionalEntropy, hM, hfst, entropy_bind_pair, entropy_bind_pair]
  simp only [conditionalEntropy, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Forgetting the tag of a tagged mixture leaves the mixture. -/
private theorem map_snd_bind_tag (p : PMF ι) (R : ι → PMF (β × α)) :
    (p.bind fun i => (R i).map (i, ·)).map Prod.snd = p.bind R := by
  simp only [PMF.map_bind, PMF.map_comp]
  exact congrArg p.bind (funext fun i => PMF.map_id (R i))

/-- **Concavity of conditional entropy**: the conditional entropy of a mixture of joint laws is
at least the average conditional entropy of its components. -/
theorem sum_mul_conditionalEntropy_le_conditionalEntropy_bind [Fintype ι] [Finite β] [Finite α]
    (p : PMF ι) (R : ι → PMF (β × α)) :
    ∑ i, (p i).toReal * conditionalEntropy (R i) ≤ conditionalEntropy (p.bind R) := by
  set M := p.bind fun i => (R i).map (i, ·)
  have h := conditionalEntropy_map_fst_ge (M.map fun t => ((t.1, t.2.1), t.2.2)) Prod.snd
  rw [conditionalEntropy_bind_tag, PMF.map_comp] at h
  rwa [show ((fun pair : (ι × β) × α => (pair.1.2, pair.2)) ∘
      fun t : ι × β × α => ((t.1, t.2.1), t.2.2)) = Prod.snd from rfl,
    map_snd_bind_tag] at h

/-- A mixture of joint laws has at most the average conditional entropy of its components plus
the entropy of the mixing law. -/
theorem conditionalEntropy_bind_le [Fintype ι] [Finite β] [Finite α] (p : PMF ι)
    (R : ι → PMF (β × α)) :
    conditionalEntropy (p.bind R) ≤ ∑ i, (p i).toReal * conditionalEntropy (R i) + entropy p := by
  set M := p.bind fun i => (R i).map (i, ·)
  set L := p.bind fun i => ((R i).map Prod.fst).map (i, ·)
  have hW : M.map Prod.snd = p.bind R := map_snd_bind_tag p R
  have hMW := entropy_map_le M Prod.snd
  have hLsub := entropy_le_entropy_map_fst_add_entropy_map_snd L
  have hLfst : L.map Prod.fst = p := map_fst_bind_pair p _
  have hLsnd : L.map Prod.snd = (p.bind R).map Prod.fst := by
    simp only [L, PMF.map_bind, PMF.map_comp]
    rfl
  rw [hLfst, hLsnd] at hLsub
  rw [hW] at hMW
  have hM := entropy_bind_pair p R
  have hL := entropy_bind_pair p fun i => (R i).map Prod.fst
  simp only [conditionalEntropy, mul_sub, Finset.sum_sub_distrib]
  linarith

/-! ### The modulus -/

/-- The modulus `(1 + ε) h₂(ε / (1 + ε))` of the continuity bound, in bits. It equals
`(1 + ε) log₂ (1 + ε) - ε log₂ ε` for `ε > 0`. -/
noncomputable def condEntropyModulus (ε : ℝ) : ℝ :=
  (1 + ε) * Real.binEntropy (ε / (1 + ε)) / Real.log 2

@[simp] theorem condEntropyModulus_zero : condEntropyModulus 0 = 0 := by
  simp [condEntropyModulus]

theorem condEntropyModulus_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ condEntropyModulus ε := by
  have h1 : 0 < 1 + ε := by linarith
  refine div_nonneg (mul_nonneg h1.le (Real.binEntropy_nonneg (div_nonneg hε h1.le) ?_))
    (Real.log_nonneg one_le_two)
  rw [div_le_one h1]
  linarith

/-- The modulus is monotone on `[0, 1]`. -/
theorem condEntropyModulus_monotoneOn : MonotoneOn condEntropyModulus (Set.Icc 0 1) := by
  rintro d ⟨hd, -⟩ ε ⟨-, hε⟩ hdε
  have hd1 : 0 < 1 + d := by linarith
  have hε1 : 0 < 1 + ε := by linarith
  have ht : d / (1 + d) ≤ ε / (1 + ε) := by
    rw [div_le_div_iff₀ hd1 hε1]
    nlinarith
  have htε : ε / (1 + ε) ≤ 2⁻¹ := by
    rw [div_le_iff₀ hε1]
    linarith
  have hh : Real.binEntropy (d / (1 + d)) ≤ Real.binEntropy (ε / (1 + ε)) :=
    Real.binEntropy_strictMonoOn.monotoneOn ⟨div_nonneg hd hd1.le, ht.trans htε⟩
      ⟨div_nonneg (hd.trans hdε) hε1.le, htε⟩ ht
  have hh0 : 0 ≤ Real.binEntropy (d / (1 + d)) :=
    Real.binEntropy_nonneg (div_nonneg hd hd1.le) ((div_le_one hd1).mpr (by linarith))
  unfold condEntropyModulus
  gcongr

/-! ### Winter's coupling -/

/-- The coin showing `true` with probability `d / (1 + d)`. -/
private noncomputable def coin (d : ℝ) (hd : 0 ≤ d) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (cond b (d / (1 + d)) (1 / (1 + d)))) (by
    have h1 : (1 + d) ≠ 0 := by linarith
    rw [Fintype.sum_bool, Bool.cond_true, Bool.cond_false,
      ← ENNReal.ofReal_add (div_nonneg hd (by linarith)) (div_nonneg zero_le_one (by linarith)),
      ← add_div, add_comm, div_self h1, ENNReal.ofReal_one])

private theorem coin_true (d : ℝ) (hd : 0 ≤ d) : (coin d hd true).toReal = d / (1 + d) := by
  rw [coin, PMF.ofFintype_apply, Bool.cond_true,
    ENNReal.toReal_ofReal (div_nonneg hd (by linarith))]

private theorem coin_false (d : ℝ) (hd : 0 ≤ d) : (coin d hd false).toReal = 1 / (1 + d) := by
  rw [coin, PMF.ofFintype_apply, Bool.cond_false,
    ENNReal.toReal_ofReal (div_nonneg zero_le_one (by linarith))]

private theorem mul_entropy_coin (d : ℝ) (hd : 0 ≤ d) :
    (1 + d) * entropy (coin d hd) = condEntropyModulus d := by
  rw [entropy_bool, coin_true, condEntropyModulus, mul_div_assoc]

/-- The mixture of `R₀` and `R₁` with weights `1 / (1 + d)` and `d / (1 + d)`. -/
private noncomputable def mix (d : ℝ) (hd : 0 ≤ d) (R₀ R₁ : PMF Ω) : PMF Ω :=
  (coin d hd).bind fun b => cond b R₁ R₀

private theorem map_mix {Ω' : Type*} (d : ℝ) (hd : 0 ≤ d) (R₀ R₁ : PMF Ω) (f : Ω → Ω') :
    (mix d hd R₀ R₁).map f = mix d hd (R₀.map f) (R₁.map f) := by
  simp only [mix, PMF.map_bind]
  exact congrArg _ (funext fun b => by cases b <;> rfl)

/-- Two decompositions of the same mixture compare up to the modulus. -/
private theorem conditionalEntropy_add_mul_le_of_mix_eq [Finite β] [Finite α] {d : ℝ}
    (hd : 0 ≤ d) {R₀ R₁ S₀ S₁ : PMF (β × α)} (h : mix d hd R₀ R₁ = mix d hd S₀ S₁) :
    conditionalEntropy R₀ + d * conditionalEntropy R₁ ≤
      conditionalEntropy S₀ + d * conditionalEntropy S₁ + condEntropyModulus d := by
  have hlow := sum_mul_conditionalEntropy_le_conditionalEntropy_bind (coin d hd)
    fun b => cond b R₁ R₀
  have hup := conditionalEntropy_bind_le (coin d hd) fun b => cond b S₁ S₀
  change _ ≤ conditionalEntropy (mix d hd R₀ R₁) at hlow
  change conditionalEntropy (mix d hd S₀ S₁) ≤ _ at hup
  rw [h] at hlow
  simp only [Fintype.sum_bool, Bool.cond_true, Bool.cond_false, coin_true, coin_false] at hlow hup
  have h1 : (0 : ℝ) < 1 + d := by linarith
  have key := mul_le_mul_of_nonneg_left (hlow.trans hup) h1.le
  rw [← mul_entropy_coin d hd]
  have e1 : (1 + d) * (d / (1 + d) * conditionalEntropy R₁ + 1 / (1 + d) * conditionalEntropy R₀) =
      conditionalEntropy R₀ + d * conditionalEntropy R₁ := by
    field_simp
    ring
  have e2 : (1 + d) * (d / (1 + d) * conditionalEntropy S₁ + 1 / (1 + d) * conditionalEntropy S₀ +
      entropy (coin d hd)) =
      conditionalEntropy S₀ + d * conditionalEntropy S₁ + (1 + d) * entropy (coin d hd) := by
    field_simp
    ring
  linarith

/-- The part of `p` exceeding `q`, normalized by `dist p q`. -/
private noncomputable def excess [Fintype Ω] (p q : PMF Ω) (h : 0 < dist p q) : PMF Ω :=
  PMF.ofFintype (fun a => ENNReal.ofReal (max ((p a).toReal - (q a).toReal) 0 / dist p q)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg fun a _ => div_nonneg (le_max_right _ _) dist_nonneg,
      ← Finset.sum_div]
    have hsum : ∑ a, max ((p a).toReal - (q a).toReal) 0 = dist p q := by
      rw [dist_eq_sum_filter_lt, Finset.sum_filter]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs with hlt
      · exact max_eq_left (sub_pos.mpr hlt).le
      · exact max_eq_right (sub_nonpos.mpr (not_lt.mp hlt))
    rw [hsum, div_self h.ne', ENNReal.ofReal_one])

private theorem excess_toReal [Fintype Ω] (p q : PMF Ω) (h : 0 < dist p q) (a : Ω) :
    (excess p q h a).toReal = max ((p a).toReal - (q a).toReal) 0 / dist p q := by
  rw [excess, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (div_nonneg (le_max_right _ _) dist_nonneg)]

/-- Winter's coupling: `P + d Δ⁻ = Q + d Δ⁺` for `d = dist P Q`. -/
private theorem mix_excess_eq [Fintype Ω] (P Q : PMF Ω) (h : 0 < dist P Q) :
    mix (dist P Q) dist_nonneg P (excess Q P (by rwa [dist_comm])) =
      mix (dist P Q) dist_nonneg Q (excess P Q h) := by
  have h1 : (0 : ℝ) < 1 + dist P Q := by linarith
  ext a
  refine (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ a) (PMF.apply_ne_top _ a)).mp ?_
  simp only [mix, bind_apply_toReal, Fintype.sum_bool, Bool.cond_true, Bool.cond_false, coin_true,
    coin_false, excess_toReal, dist_comm Q P]
  field_simp
  rcases le_total (P a).toReal (Q a).toReal with hPQ | hPQ
  · rw [max_eq_left (sub_nonneg.mpr hPQ), max_eq_right (sub_nonpos.mpr hPQ)]
    ring
  · rw [max_eq_right (sub_nonpos.mpr hPQ), max_eq_left (sub_nonneg.mpr hPQ)]
    ring

/-- A functional that is bounded and compares decompositions of mixtures up to `k` moduli is
continuous with the corresponding bound. -/
private theorem abs_sub_le_of_mix [Fintype Ω] (F : PMF Ω → ℝ) {L k : ℝ} (hk : 0 ≤ k)
    (h0 : ∀ R, 0 ≤ F R) (hL : ∀ R, F R ≤ L)
    (hmix : ∀ {d : ℝ} (hd : 0 ≤ d) {R₀ R₁ S₀ S₁ : PMF Ω}, mix d hd R₀ R₁ = mix d hd S₀ S₁ →
      F R₀ + d * F R₁ ≤ F S₀ + d * F S₁ + k * condEntropyModulus d)
    {P Q : PMF Ω} {ε : ℝ} (h : dist P Q ≤ ε) :
    |F P - F Q| ≤ ε * L + k * condEntropyModulus ε := by
  have hε : 0 ≤ ε := dist_nonneg.trans h
  have hL0 : 0 ≤ L := (h0 P).trans (hL P)
  have hmod : 0 ≤ k * condEntropyModulus ε := mul_nonneg hk (condEntropyModulus_nonneg hε)
  have side : ∀ A B : PMF Ω, dist A B ≤ ε → F A - F B ≤ ε * L + k * condEntropyModulus ε := by
    intro A B hAB
    rcases le_or_gt 1 ε with hε1 | hε1
    · nlinarith [h0 B, hL A]
    rcases (dist_nonneg : 0 ≤ dist A B).eq_or_lt with hd | hd
    · rw [dist_eq_zero.mp hd.symm, sub_self]
      positivity
    have hc := hmix dist_nonneg (mix_excess_eq A B hd)
    have hmono := condEntropyModulus_monotoneOn ⟨dist_nonneg, dist_le_one A B⟩ ⟨hε, hε1.le⟩ hAB
    nlinarith [h0 (excess B A (by rwa [dist_comm])), hL (excess A B hd)]
  rw [abs_sub_le_iff]
  exact ⟨side P Q h, side Q P (by rwa [dist_comm])⟩

/-! ### Continuity -/

/-- **Continuity of conditional entropy** [Winter2016]: for joint laws `P` and `Q` of an
observation and a hidden value `X : α` with `dist P Q ≤ ε`,
`|H(X | Y)_P - H(X | Y)_Q| ≤ ε log₂ |α| + (1 + ε) h₂(ε / (1 + ε))`. The bound does not depend on
the observation's alphabet. -/
theorem abs_conditionalEntropy_sub_le [Fintype β] [Fintype α] {P Q : PMF (β × α)} {ε : ℝ}
    (h : dist P Q ≤ ε) :
    |conditionalEntropy P - conditionalEntropy Q| ≤
      ε * Real.logb 2 (Fintype.card α) + condEntropyModulus ε := by
  simpa using abs_sub_le_of_mix conditionalEntropy zero_le_one conditionalEntropy_nonneg
    conditionalEntropy_le_log_card
    (fun hd _ _ _ _ hm => by simpa using conditionalEntropy_add_mul_le_of_mix_eq hd hm) h

/-- **Transfer** of a lower bound on conditional entropy to a law at statistical distance at
most `ε`: if `t ≤ H(X | Y)_Q` and `dist P Q ≤ ε`, then
`t - ε log₂ |α| - (1 + ε) h₂(ε / (1 + ε)) ≤ H(X | Y)_P`. -/
theorem sub_le_conditionalEntropy_of_dist_le [Fintype β] [Fintype α] {P Q : PMF (β × α)}
    {ε t : ℝ} (hdist : dist P Q ≤ ε) (ht : t ≤ conditionalEntropy Q) :
    t - ε * Real.logb 2 (Fintype.card α) - condEntropyModulus ε ≤ conditionalEntropy P := by
  have h := abs_conditionalEntropy_sub_le hdist
  rw [abs_sub_le_iff] at h
  linarith [h.2]

/-- `I(A; B | C) = H(A | C) - H(A | C, B)`. -/
private theorem condMutualInfo_eq_sub [Finite γ] [Finite α] [Finite β] (J : PMF (γ × α × β)) :
    condMutualInfo J = conditionalEntropy (J.map fun t => (t.1, t.2.1)) -
      conditionalEntropy (J.map fun t => ((t.1, t.2.2), t.2.1)) := by
  have hJ : entropy (J.map fun t => ((t.1, t.2.2), t.2.1)) = entropy J :=
    entropy_map_of_injective J fun s t h => by
      obtain ⟨c, a, b⟩ := s
      obtain ⟨c', a', b'⟩ := t
      simp only [Prod.mk.injEq] at h
      simp [h]
  have hmap := condMutualInfo_map J Prod.fst (fun t => t.2.1) (fun t => t.2.2)
  rw [show (fun t : γ × α × β => (t.1, t.2.1, t.2.2)) = id from rfl, PMF.map_id] at hmap
  simp only [hmap, conditionalEntropy, PMF.map_comp, hJ]
  have e1 : (Prod.fst ∘ fun t : γ × α × β => (t.1, t.2.1)) = Prod.fst := rfl
  have e2 : (Prod.fst ∘ fun t : γ × α × β => ((t.1, t.2.2), t.2.1)) =
      fun t => (t.1, t.2.2) := rfl
  rw [e1, e2]
  ring

/-- **Continuity of conditional mutual information**: for joint laws `P` and `Q` of `(C, A, B)`
with `dist P Q ≤ ε`, `|I(A; B | C)_P - I(A; B | C)_Q| ≤ ε log₂ |A| + 2 (1 + ε) h₂(ε / (1 + ε))`. -/
theorem abs_condMutualInfo_sub_le [Fintype γ] [Fintype α] [Fintype β] {P Q : PMF (γ × α × β)}
    {ε : ℝ} (h : dist P Q ≤ ε) :
    |condMutualInfo P - condMutualInfo Q| ≤
      ε * Real.logb 2 (Fintype.card α) + 2 * condEntropyModulus ε := by
  refine abs_sub_le_of_mix condMutualInfo zero_le_two condMutualInfo_nonneg
    (fun R => (condMutualInfo_le_conditionalEntropy_fst R).trans
      (conditionalEntropy_le_log_card _)) (fun hd R₀ R₁ S₀ S₁ hm => ?_) h
  have h1 := conditionalEntropy_add_mul_le_of_mix_eq hd
    (by simpa only [map_mix] using congrArg (PMF.map fun t => (t.1, t.2.1)) hm)
  have h2 := conditionalEntropy_add_mul_le_of_mix_eq hd
    (by simpa only [map_mix] using congrArg (PMF.map fun t => ((t.1, t.2.2), t.2.1)) hm.symm)
  simp only [condMutualInfo_eq_sub]
  linarith

end Cslib.Probability.PMF
