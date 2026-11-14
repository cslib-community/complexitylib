/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PoissonBinomial
public import CslibFrontier.Foundations.Data.BitString.Weight
import CslibFrontier.Probability.PMF.Coin.Complement

/-!
# Bit weights and binomial reflection

A Poisson-binomial law is the Hamming weight of independent Boolean trials.
For a homogeneous parameter, complementing every trial reflects the count
around the number of trials. The proof reuses coordinatewise PMF mapping and
the existing Hamming-weight complement identity.

## Main results

* `poissonBinomial_eq_map_weight`: the named Hamming-weight characterization.
* `poissonBinomial_replicate_map_sub`: homogeneous count reflection, including boundary parameters.
-/

public section
namespace Cslib.Probability.PMF
open scoped unitInterval

/-- The Poisson-binomial law is the Hamming weight of its independent coin vector. -/
theorem poissonBinomial_eq_map_weight (ps : List I) :
    poissonBinomial ps =
      (pi fun i : Fin ps.length => coin ps[i]).map Cslib.BitString.weight := by
  rw [poissonBinomial_eq_map_pi]
  congr 1
  funext f
  rw [Cslib.BitString.weight_eq_sum_toNat]
  apply Finset.sum_congr rfl
  intro i _
  cases f i <;> rfl

/-- Reflecting a binomial count around its trial budget complements the coin
parameter. No strict positivity or nontrivial-budget hypothesis is needed. -/
theorem poissonBinomial_replicate_map_sub (n : ℕ) (p : I) :
    (poissonBinomial (List.replicate n p)).map (fun k => n - k) =
      poissonBinomial (List.replicate n (σ p)) := by
  classical
  have he (q : I) : poissonBinomial (List.replicate n q) =
      (pi fun _ : Fin n => coin q).map Cslib.BitString.weight := by
    have h := poissonBinomial_eq_map_weight (List.replicate n q)
    generalize hps : List.replicate n q = ps at h
    have hlen : ps.length = n := by rw [← hps, List.length_replicate]
    have hget (i : Fin ps.length) : ps[i] = q := by simp [← hps]
    subst n
    simpa only [hget] using h
  rw [he p, he (σ p), PMF.map_comp]
  have hp : (pi fun _ : Fin n => coin (σ p)) =
      (pi fun _ : Fin n => coin p).map (fun x i => !(x i)) := by
    simp_rw [← coin_map_not]
    exact pi_map (fun _ : Fin n => coin p) (fun _ => Bool.not)
  rw [hp, PMF.map_comp]
  congr 1
  funext x
  simpa only [Function.comp_apply, Fintype.card_fin] using (Cslib.BitString.weight_not x).symm

end Cslib.Probability.PMF
