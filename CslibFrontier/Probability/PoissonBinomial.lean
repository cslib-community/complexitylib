/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Product
public import Mathlib.Probability.Distributions.Binomial
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Data.Nat.Choose.Basic

/-!
# Poisson-binomial distributions

The Poisson-binomial distribution `Cslib.Probability.PMF.poissonBinomial ps` is the law of the
sum of independent Bernoulli random variables with success probabilities `ps : List unitInterval`.

## Main definitions

* `Cslib.Probability.PMF.poissonBinomial`: the Poisson-binomial `PMF ℕ` for a parameter list
  `ps : List unitInterval`.

## Main results

* `Cslib.Probability.PMF.poissonBinomial_cons_zero`,
  `Cslib.Probability.PMF.poissonBinomial_cons_succ`: Pascal recurrence for `poissonBinomial`.
* `Cslib.Probability.PMF.poissonBinomial_append`: convolution identity under list concatenation.
* `Cslib.Probability.PMF.poissonBinomial_perm`: permutation invariance of the parameter list.
* `Cslib.Probability.PMF.poissonBinomial_eq_map_pi`: equivalence with the sum of independent
  `Cslib.Probability.PMF.coin` trials.
* `Cslib.Probability.PMF.toMeasure_poissonBinomial_replicate`: specialization on
  `List.replicate n p` to Mathlib's `ProbabilityTheory.binomial n p`.
* `Cslib.Probability.PMF.tsum_mul_poissonBinomial`: expectation of `poissonBinomial ps`.
-/

public section

namespace Cslib.Probability.PMF

open MeasureTheory
open scoped BigOperators ENNReal unitInterval

/-- The Poisson-binomial distribution on `ℕ` for independent Bernoulli trials with success
probabilities `ps : List I`. -/
@[expose]
noncomputable def poissonBinomial : List I → PMF ℕ
  | [] => PMF.pure 0
  | p :: ps => (coin p).bind fun b => (poissonBinomial ps).map fun k => if b then k + 1 else k

@[simp]
theorem poissonBinomial_nil : poissonBinomial [] = PMF.pure 0 :=
  rfl

theorem poissonBinomial_cons (p : I) (ps : List I) :
    poissonBinomial (p :: ps) =
      (coin p).bind fun b => (poissonBinomial ps).map fun k => if b then k + 1 else k :=
  rfl

/-- Probability mass of `0` under `poissonBinomial (p :: ps)`. -/
theorem poissonBinomial_cons_zero (p : I) (ps : List I) :
    poissonBinomial (p :: ps) 0 = ENNReal.ofReal (1 - (p : ℝ)) * poissonBinomial ps 0 := by
  rw [poissonBinomial_cons, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  have hmap_true :
      ((poissonBinomial ps).map fun k => if (true : Bool) then k + 1 else k) 0 = 0 := by
    simp only [↓reduceIte, PMF.map_apply]
    refine (tsum_congr fun m => ?_).trans tsum_zero
    simp
  have hmap_false :
      ((poissonBinomial ps).map fun k => if (false : Bool) then k + 1 else k) 0 =
        poissonBinomial ps 0 := by
    simp only [Bool.false_eq_true, ↓reduceIte, PMF.map_apply]
    simp_rw [@eq_comm _ 0]
    exact tsum_ite_eq 0 (poissonBinomial ps)
  rw [hmap_true, hmap_false]
  simp [coin_apply]

/-- Probability mass of `k + 1` under `poissonBinomial (p :: ps)`. -/
theorem poissonBinomial_cons_succ (p : I) (ps : List I) (k : ℕ) :
    poissonBinomial (p :: ps) (k + 1) =
      ENNReal.ofReal (1 - (p : ℝ)) * poissonBinomial ps (k + 1) +
        ENNReal.ofReal (p : ℝ) * poissonBinomial ps k := by
  rw [poissonBinomial_cons, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  have hmap_true :
      ((poissonBinomial ps).map fun m => if (true : Bool) then m + 1 else m) (k + 1) =
        poissonBinomial ps k := by
    simp only [↓reduceIte, PMF.map_apply, Nat.add_right_cancel_iff]
    simp_rw [@eq_comm _ k]
    exact tsum_ite_eq k (poissonBinomial ps)
  have hmap_false :
      ((poissonBinomial ps).map fun m => if (false : Bool) then m + 1 else m) (k + 1) =
        poissonBinomial ps (k + 1) := by
    simp only [Bool.false_eq_true, ↓reduceIte, PMF.map_apply]
    simp_rw [@eq_comm _ (k + 1)]
    exact tsum_ite_eq (k + 1) (poissonBinomial ps)
  rw [hmap_true, hmap_false, coin_apply, coin_apply]
  simp [add_comm]

/-- Real-valued probability mass of `0` under `poissonBinomial (p :: ps)`. -/
theorem poissonBinomial_cons_zero_toReal (p : I) (ps : List I) :
    (poissonBinomial (p :: ps) 0).toReal = (1 - (p : ℝ)) * (poissonBinomial ps 0).toReal := by
  rw [poissonBinomial_cons_zero, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2)]

/-- Real-valued probability mass of `k + 1` under `poissonBinomial (p :: ps)`. -/
theorem poissonBinomial_cons_succ_toReal (p : I) (ps : List I) (k : ℕ) :
    (poissonBinomial (p :: ps) (k + 1)).toReal =
      (1 - (p : ℝ)) * (poissonBinomial ps (k + 1)).toReal +
        (p : ℝ) * (poissonBinomial ps k).toReal := by
  rw [poissonBinomial_cons_succ, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (PMF.apply_ne_top _ _)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr p.2.2),
    ENNReal.toReal_ofReal p.2.1]

/-- Any value in the support of `poissonBinomial ps` is at most `ps.length`. -/
theorem mem_support_poissonBinomial_le {ps : List I} {k : ℕ}
    (hk : k ∈ (poissonBinomial ps).support) :
    k ≤ ps.length := by
  induction ps generalizing k with
  | nil =>
    simp only [poissonBinomial_nil, PMF.support_pure, Set.mem_singleton_iff] at hk
    simp [hk]
  | cons p ps ih =>
    rw [poissonBinomial_cons, PMF.mem_support_bind_iff] at hk
    rcases hk with ⟨b, _, hb⟩
    rw [PMF.mem_support_map_iff] at hb
    rcases hb with ⟨m, hm, rfl⟩
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons] <;>
      linarith [ih hm]

/-- `poissonBinomial ps k = 0` whenever `ps.length < k`. -/
theorem poissonBinomial_eq_zero_of_lt {ps : List I} {k : ℕ} (hk : ps.length < k) :
    poissonBinomial ps k = 0 := by
  by_contra hne
  exact absurd (mem_support_poissonBinomial_le hne) (not_le.mpr hk)

/-- Appending parameter lists corresponds to convolving their Poisson-binomial laws. -/
theorem poissonBinomial_append (ps qs : List I) :
    poissonBinomial (ps ++ qs) =
      (poissonBinomial ps).bind fun a => (poissonBinomial qs).map fun b => a + b := by
  induction ps with
  | nil =>
    rw [List.nil_append, poissonBinomial_nil, PMF.pure_bind]
    have hmap : PMF.map (fun b : ℕ => 0 + b) (poissonBinomial qs) =
        PMF.map id (poissonBinomial qs) := by
      congr 1
      ext b
      exact Nat.zero_add b
    rw [hmap, PMF.map_id]
  | cons p ps ih =>
    rw [List.cons_append, poissonBinomial_cons, ih, poissonBinomial_cons, PMF.bind_bind]
    refine congr_arg (PMF.bind (coin p)) (funext fun b => ?_)
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hid : ((poissonBinomial ps).map fun k => k) = poissonBinomial ps := PMF.map_id _
      rw [hid, PMF.map_bind]
      refine congr_arg (PMF.bind (poissonBinomial ps)) (funext fun a => ?_)
      exact PMF.map_id _
    · simp only [↓reduceIte]
      conv_lhs => rw [PMF.map_bind]
      conv_rhs => rw [PMF.bind_map]
      refine congr_arg (PMF.bind (poissonBinomial ps)) (funext fun a => ?_)
      rw [PMF.map_comp]
      refine congr_arg (fun f => PMF.map f (poissonBinomial qs)) (funext fun c => ?_)
      dsimp only [Function.comp_apply]
      omega

private theorem poissonBinomial_swap (p q : I) (ps : List I) :
    poissonBinomial (p :: q :: ps) = poissonBinomial (q :: p :: ps) := by
  rw [poissonBinomial_cons, poissonBinomial_cons, poissonBinomial_cons, poissonBinomial_cons]
  have rewrite_pair (x y : I) :
      ((coin x).bind fun b₁ =>
          PMF.map (fun k => if b₁ then k + 1 else k)
            ((coin y).bind fun b₂ => PMF.map (fun k => if b₂ then k + 1 else k)
              (poissonBinomial ps))) =
        (coin x).bind fun b₁ => (coin y).bind fun b₂ =>
          (poissonBinomial ps).map fun k =>
            k + (if b₁ then 1 else 0) + (if b₂ then 1 else 0) := by
    refine congr_arg (PMF.bind (coin x)) (funext fun b₁ => ?_)
    rw [PMF.map_bind]
    refine congr_arg (PMF.bind (coin y)) (funext fun b₂ => ?_)
    rw [PMF.map_comp]
    refine congr_arg (fun f => PMF.map f (poissonBinomial ps)) (funext fun k => ?_)
    cases b₁ <;> cases b₂ <;> simp [add_assoc]
  rw [rewrite_pair p q, rewrite_pair q p, PMF.bind_comm (coin p) (coin q)]
  refine congr_arg (PMF.bind (coin q)) (funext fun b₂ => ?_)
  refine congr_arg (PMF.bind (coin p)) (funext fun b₁ => ?_)
  refine congr_arg (fun f => PMF.map f (poissonBinomial ps)) (funext fun k => ?_)
  omega

/-- Reordering the trial probabilities does not change `poissonBinomial`. -/
theorem poissonBinomial_perm {ps qs : List I} (h : ps.Perm qs) :
    poissonBinomial ps = poissonBinomial qs := by
  induction h with
  | nil => rfl
  | cons p _ ih => simp only [poissonBinomial_cons, ih]
  | swap p q ps => exact poissonBinomial_swap q p ps
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Equivalence between `poissonBinomial ps` and the sum of independent `coin` indicators. -/
theorem poissonBinomial_eq_map_pi (ps : List I) :
    poissonBinomial ps =
      (pi fun i : Fin ps.length => coin ps[i]).map
        (fun f => ∑ i : Fin ps.length, if f i then 1 else 0) := by
  induction ps with
  | nil =>
    ext k
    let f₀ : Fin ([] : List I).length → Bool := fun i => Fin.elim0 (i.cast (by simp))
    have hsub : Subsingleton (Fin ([] : List I).length → Bool) :=
      ⟨fun f g => funext fun i => Fin.elim0 (i.cast (by simp))⟩
    rw [poissonBinomial_nil, PMF.map_apply,
      tsum_eq_single f₀ (fun g hg => absurd (Subsingleton.elim g f₀) hg)]
    have hpi : (pi fun i : Fin ([] : List I).length => coin ([][i])) f₀ = 1 := by
      rw [pi_apply]
      exact Finset.prod_eq_one fun i _ => Fin.elim0 (i.cast (by simp))
    have hsum : (∑ i : Fin ([] : List I).length, if f₀ i then (1 : ℕ) else 0) = 0 :=
      Finset.sum_eq_zero fun i _ => Fin.elim0 (i.cast (by simp))
    rw [hsum, hpi, PMF.pure_apply]
  | cons p ps ih =>
    rw [poissonBinomial_cons, ih]
    have hcons :
        (pi fun i : Fin (p :: ps).length => coin (p :: ps)[i]) =
          (coin p).bind fun b => (pi fun i : Fin ps.length => coin ps[i]).map (Fin.cons b) := by
      let e := Fin.consEquiv (fun _ : Fin (ps.length + 1) => Bool)
      calc
        _ = ((coin p).bind fun b =>
              (pi fun i : Fin ps.length => coin ps[i]).map (b, ·)).map e := by
          ext f
          rw [map_equiv_apply, bind_map_prodMk_apply, pi_apply, pi_apply]
          simpa [e, Fin.consEquiv, Fin.tail, List.length_cons] using
            (Fin.prod_univ_succ fun i : Fin (ps.length + 1) => coin (p :: ps)[i] (f i))
        _ = _ := by
          simp [PMF.map_bind, PMF.map_comp, Function.comp_def, e, Fin.consEquiv]
    rw [hcons]
    conv_rhs => rw [PMF.map_bind]
    refine congr_arg (PMF.bind (coin p)) (funext fun b => ?_)
    rw [PMF.map_comp, PMF.map_comp]
    refine congr_arg (fun f => PMF.map f (pi fun i : Fin ps.length => coin ps[i]))
      (funext fun g => ?_)
    simp only [Function.comp_apply]
    have hsum :
        (∑ i : Fin (p :: ps).length, if Fin.cons (α := fun _ => Bool) b g i = true then 1 else 0) =
          (if b = true then 1 else 0) + ∑ i : Fin ps.length, if g i = true then 1 else 0 :=
      Fin.sum_univ_succ fun i : Fin (ps.length + 1) =>
        if Fin.cons (α := fun _ => Bool) b g i = true then 1 else 0
    rw [hsum]
    cases b <;> simp [add_comm]

/-- Real-valued probability mass function of `poissonBinomial (List.replicate n p)`. -/
theorem poissonBinomial_replicate_apply_toReal (n k : ℕ) (p : I) :
    (poissonBinomial (List.replicate n p) k).toReal =
      (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - p) ^ (n - k) := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp
  | succ n ih =>
    rw [List.replicate_succ]
    cases k with
    | zero =>
      rw [poissonBinomial_cons_zero_toReal, ih 0]
      simp [pow_succ']
    | succ k =>
      rw [poissonBinomial_cons_succ_toReal, ih (k + 1), ih k]
      have hchoose : ((n + 1).choose (k + 1) : ℝ) = (n.choose (k + 1) : ℝ) + n.choose k := by
        exact_mod_cast (Nat.choose_succ_succ' n k).trans (Nat.add_comm _ _)
      rw [hchoose]
      by_cases hkn : k + 1 ≤ n
      · have hexp : n - k = (n - (k + 1)) + 1 := by omega
        have hnk : (n + 1) - (k + 1) = n - k := by omega
        rw [hnk, hexp, pow_succ, pow_succ]
        ring
      · have hzero : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have hnk : (n + 1) - (k + 1) = 0 := by omega
        have hnk' : n - k = 0 := by omega
        simp [hzero, hnk, hnk', pow_succ]
        ring

/-- Singletons under `poissonBinomial (List.replicate n p)` equal Mathlib's
`ProbabilityTheory.binomial n p`. -/
theorem poissonBinomial_replicate_apply (n k : ℕ) (p : I) :
    poissonBinomial (List.replicate n p) k = ProbabilityTheory.binomial n p {k} := by
  rw [ProbabilityTheory.binomial_singleton, ← poissonBinomial_replicate_apply_toReal,
    ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

/-- On `List.replicate n p`, `poissonBinomial` induces Mathlib's
`ProbabilityTheory.binomial n p`. -/
theorem toMeasure_poissonBinomial_replicate (n : ℕ) (p : I) :
    (poissonBinomial (List.replicate n p)).toMeasure = ProbabilityTheory.binomial n p := by
  refine Measure.ext_of_singleton fun k => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton k),
    poissonBinomial_replicate_apply]

private theorem sum_range_poissonBinomial_toReal (ps : List I) :
    ∑ k ∈ Finset.range (ps.length + 1), (poissonBinomial ps k).toReal = 1 := by
  have hsum : ∑' k : ℕ, (poissonBinomial ps k).toReal = 1 := by
    simp [tsum_toReal]
  rw [← hsum]
  refine (tsum_eq_sum ?_).symm
  intro k hk
  simp only [Finset.mem_range, not_lt] at hk
  rw [poissonBinomial_eq_zero_of_lt (by omega), ENNReal.toReal_zero]

/-- Finite-range expectation identity for `poissonBinomial ps`. -/
theorem sum_mul_poissonBinomial (ps : List I) :
    ∑ k ∈ Finset.range (ps.length + 1), (k : ℝ) * (poissonBinomial ps k).toReal =
      (ps.map fun p : I => (p : ℝ)).sum := by
  induction ps with
  | nil =>
    simp
  | cons p ps ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hsplit (k : ℕ) :
        ((k + 1 : ℕ) : ℝ) * (poissonBinomial (p :: ps) (k + 1)).toReal =
          (1 - (p : ℝ)) * (((k + 1 : ℕ) : ℝ) * (poissonBinomial ps (k + 1)).toReal) +
            (p : ℝ) * (((k : ℝ) * (poissonBinomial ps k).toReal) +
              (poissonBinomial ps k).toReal) := by
      rw [poissonBinomial_cons_succ_toReal]
      push_cast
      ring
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum]
    have hshift :
        ∑ k ∈ Finset.range (ps.length + 1),
            ((k + 1 : ℕ) : ℝ) * (poissonBinomial ps (k + 1)).toReal =
          ∑ k ∈ Finset.range (ps.length + 1), (k : ℝ) * (poissonBinomial ps k).toReal := by
      have h1 :
          ∑ k ∈ Finset.range (ps.length + 1),
              ((k + 1 : ℕ) : ℝ) * (poissonBinomial ps (k + 1)).toReal =
            ∑ k ∈ Finset.range (ps.length + 2), (k : ℝ) * (poissonBinomial ps k).toReal := by
        symm
        rw [Finset.sum_range_succ']
        simp
      rw [h1, Finset.sum_range_succ, poissonBinomial_eq_zero_of_lt (by omega)]
      simp
    rw [hshift, ih]
    simp_rw [Finset.sum_add_distrib]
    rw [ih, sum_range_poissonBinomial_toReal]
    ring

/-- Expectation series identity for `poissonBinomial ps`. -/
theorem tsum_mul_poissonBinomial (ps : List I) :
    ∑' k : ℕ, (k : ℝ) * (poissonBinomial ps k).toReal = (ps.map fun p : I => (p : ℝ)).sum := by
  rw [tsum_eq_sum]
  · exact sum_mul_poissonBinomial ps
  · intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    rw [poissonBinomial_eq_zero_of_lt (by omega), ENNReal.toReal_zero, mul_zero]

end Cslib.Probability.PMF
