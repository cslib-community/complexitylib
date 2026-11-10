/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Operations
public import CslibFrontier.Computability.Communication.Randomized
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF

/-!
# Amplification of public-coin protocols

A public-coin protocol computing a Boolean function `f` with error `ε ≤ 1 / 2` can be run `2 r`
times with independent coins, answering with the strict majority of the outputs
(`BitString.strictMajorityOn`) [Kushilevitz and Nisan, Chapter 3][KushilevitzNisan1997]. The
majority is wrong only if at least `r` of the runs err
(`BitString.card_filter_eq_le_half_of_strictMajorityOn_ne`), which happens with probability at most
`(4 ε (1 - ε)) ^ r` by the majority tail bound `Probability.PMF.iid_card_ge_le`, applied to the
indicators of the runs that err. The repeated protocol sends at most `2 r` times as many bits
(`PublicCoin.ecomplexity_le_two_mul_mul`, `PublicCoin.ecomplexityFun_le_two_mul_mul`). For error
`1 / 3`, `2 r` runs reduce the error to `(8 / 9) ^ r`
(`PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`).

The runs are sequenced with `Protocol.runAll`, which runs a tuple of protocols one after another
before combining their outputs. The protocols are drawn independently with
`Probability.PMF.iid`, which unlike the product `Probability.PMF.pi` applies to the infinite type
of protocols.

## Main definitions

* `Cslib.Communication.PublicCoin.amplify`: the strict majority of `2 r` independent runs.

## Main results

* `Cslib.Communication.PublicCoin.Solves.amplify`: the error of the majority of `2 r` runs.
* `Cslib.Communication.PublicCoin.ecomplexity_le_two_mul_mul`,
  `Cslib.Communication.PublicCoin.ecomplexityFun_le_two_mul_mul`: amplification of public-coin
  protocols for Boolean functions.
* `Cslib.Communication.PublicCoin.ecomplexityFun_le_two_mul_mul_one_third`: amplification from
  error `1 / 3`.

## References

* [E. Kushilevitz and N. Nisan, *Communication Complexity*][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Communication

open Probability

variable {X Y : Type*}

namespace PublicCoin

/-- If the strict majority of `2 r` bits is not `b`, then at least `r` of them are not `b`. -/
private theorem le_card_filter_ne_of_strictMajorityOn_ne {r : ℕ} {v : Fin (2 * r) → Bool}
    {b : Bool} (h : BitString.strictMajorityOn Finset.univ v ≠ b) :
    r ≤ (Finset.univ.filter fun i => ¬v i = b).card := by
  have h₁ := BitString.card_filter_eq_le_half_of_strictMajorityOn_ne Finset.univ v b h
  have h₂ := Finset.card_filter_add_card_filter_not (s := Finset.univ) fun i => v i = b
  rw [Finset.card_univ, Fintype.card_fin] at h₁ h₂
  omega

/-- The strict majority of `2 r` independent runs of `μ`. -/
noncomputable def amplify (μ : PublicCoin X Y Bool) (r : ℕ) : PublicCoin X Y Bool :=
  (PMF.iid μ (2 * r)).map fun ps => Protocol.runAll ps (BitString.strictMajorityOn Finset.univ)

variable {μ : PublicCoin X Y Bool} {f : X → Y → Bool} {A : Set X} {B : Set Y} {ε : ℝ}

/-- The majority of `2 r` runs sends at most `2 r` times as many bits. -/
theorem depth_amplify_le {c : ℕ} (hμ : μ.depth ≤ c) (r : ℕ) : (μ.amplify r).depth ≤ 2 * r * c := by
  refine depth_le_iff.mpr fun p hp => ?_
  obtain ⟨ps, hps, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hp
  have hd : ∀ i, (ps i).depth ≤ c := fun i => by
    exact_mod_cast (depth_le_depth ((PMF.mem_support_iid_iff _ _).mp hps i)).trans hμ
  exact_mod_cast Protocol.depth_runAll_le hd

/-- **Amplification**: if `μ` computes `f` on `A × B` with error `ε ≤ 1 / 2`, then the majority of
`2 r` independent runs computes it with error `(4 ε (1 - ε)) ^ r`. -/
theorem Solves.amplify (hμ : μ.Solves ε (fun x y b => f x y = b) A B) (hε : ε ≤ 1 / 2)
    (r : ℕ) : (μ.amplify r).Solves ((4 * ε * (1 - ε)) ^ r) (fun x y b => f x y = b) A B := by
  intro x hx y hy
  set e : Protocol X Y Bool → Bool := fun p => decide (p.run x y ≠ f x y)
  have he : ((μ.map e) true).toReal ≤ ε := by
    have h := hμ x hx y hy
    rw [errorProb] at h
    rwa [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
      show e ⁻¹' {true} = {p | ¬f x y = p.run x y} by
        ext p
        simp only [e, Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq,
          Set.mem_ofPred_eq]
        exact ne_comm]
  refine le_trans ?_ (PMF.iid_card_ge_le he hε r)
  rw [errorProb, PublicCoin.amplify, PMF.toOuterMeasure_map_apply, PMF.iid_map,
    PMF.toOuterMeasure_map_apply]
  refine ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top _ _)
    (PMF.toOuterMeasure_mono _ fun ps hps => ?_)
  replace hps := hps.1
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Protocol.run_runAll] at hps ⊢
  simpa [e] using le_card_filter_ne_of_strictMajorityOn_ne (Ne.symm hps)

/-- **Amplification** of public-coin protocols: for error `ε ≤ 1 / 2`, computing a Boolean function
on `A × B` with error `(4 ε (1 - ε)) ^ r` costs at most `2 r` times as much as with error `ε`. -/
theorem ecomplexity_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexity ((4 * ε * (1 - ε)) ^ r) (fun x y b => f x y = b) A B ≤
      2 * r * ecomplexity ε (fun x y b => f x y = b) A B := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · -- With no runs, the error `1` is achieved by any deterministic answer.
    rw [pow_zero, Nat.cast_zero, mul_zero, zero_mul]
    exact (ecomplexity_le_depth (μ := PMF.pure (.output true))
      fun x _ y _ => errorProb_le_one).trans (by simp)
  cases h : ecomplexity ε (fun x y b => f x y = b) A B using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast (Nat.mul_pos two_pos hr).ne')]
    exact le_top
  | coe c =>
    obtain ⟨μ, hμ, hc⟩ := ecomplexity_le_iff.mp h.le
    exact (ecomplexity_le_depth (hμ.amplify hε r)).trans
      (depth_amplify_le hc r)

/-- **Amplification** of public-coin protocols for Boolean functions: for error `ε ≤ 1 / 2`,
computing `f` with error `(4 ε (1 - ε)) ^ r` costs at most `2 r` times as much as with error
`ε`. -/
theorem ecomplexityFun_le_two_mul_mul (hε : ε ≤ 1 / 2) (r : ℕ) :
    ecomplexityFun ((4 * ε * (1 - ε)) ^ r) f ≤ 2 * r * ecomplexityFun ε f :=
  ecomplexity_le_two_mul_mul hε r

/-- **Amplification** from error `1 / 3`: `2 r` runs reduce the error to `(8 / 9) ^ r`. -/
theorem ecomplexityFun_le_two_mul_mul_one_third (r : ℕ) :
    ecomplexityFun ((8 / 9) ^ r) f ≤ 2 * r * ecomplexityFun (1 / 3) f := by
  have h := ecomplexityFun_le_two_mul_mul (f := f) (ε := 1 / 3) (by norm_num) r
  rwa [show (4 * (1 / 3) * (1 - 1 / 3) : ℝ) = 8 / 9 by norm_num] at h

end PublicCoin

end Cslib.Communication
