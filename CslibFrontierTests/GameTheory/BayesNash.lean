/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Mechanism.FirstPrice

/-!
# Bayes–Nash equilibrium and the first-price auction

One-dimensional incentive compatibility holds for the interim rules of the second-price auction
with two uniform bidders and fails for a decreasing allocation curve. In the first-price auction
with two uniform bidders, bidding half one's value is a Bayes–Nash equilibrium, a bid of `1/4` wins
with probability `1/2`, truthful bidding is not an equilibrium, and both the first- and the
second-price auction earn `1/3`. With three bidders each bids `2/3` of its value and both auctions
earn `1/2`. A lone bidder bids `0`.
-/

namespace ComplexityTests.GameTheory.BayesNash

open MeasureTheory Set Cslib.GameTheory.SingleParameter

/-- The uniform distribution on `[0, 1]`. -/
local notation "𝒰" => (volume.restrict (Icc (0 : ℝ) 1) : Measure ℝ)

/-! ### One-dimensional incentive compatibility -/

/-- The interim rules `x(v) = v`, `p(v) = v² / 2` of the second-price auction with two uniform
bidders ([Hartline2021], Example 2.7.1) are incentive compatible on `[0, 1]`. -/
example : IsTruthfulOn (fun v => v) (fun v => v ^ 2 / 2) (Icc 0 1) := by
  refine isTruthfulOn_of_payment_eq (fun _ _ _ _ h => h) fun v _ => ?_
  simp only [integral_id]
  ring

/-- A decreasing allocation curve is not incentive compatible: the type `1` prefers the outcome of
the type `0`. -/
example : ¬ IsTruthfulOn (fun v => -v) (fun _ => 0) (Icc 0 1) := by
  intro h
  have := h 1 ⟨zero_le_one, le_rfl⟩ 0 ⟨le_rfl, zero_le_one⟩
  norm_num at this

/-! ### Two uniform bidders -/

theorem uniformBid_fin_two :
    (fun _ : Fin 2 => FirstPrice.uniformBid (Fintype.card (Fin 2))) = fun _ v => v / 2 := by
  funext _ v
  rw [Fintype.card_fin, FirstPrice.uniformBid_two]

/-- Bidding half one's value is a Bayes–Nash equilibrium of the first-price auction with two
uniform bidders ([Hartline2021], §2.3). -/
example :
    FirstPrice.mechanism.IsBayesNash (fun _ : Fin 2 => 𝒰) (fun _ => 1) (fun _ v => v / 2) := by
  rw [← uniformBid_fin_two]
  exact FirstPrice.isBayesNash_uniformBid

/-- Against an opponent bidding half its value, a bid of `1/4` wins with probability `1/2` and pays
`1/4` when it wins. -/
example : FirstPrice.mechanism.interimAllocation (fun _ : Fin 2 => 𝒰) (fun _ v => v / 2) 0 (1 / 4) =
      1 / 2 ∧
    FirstPrice.mechanism.interimPayment (fun _ : Fin 2 => 𝒰) (fun _ v => v / 2) 0 (1 / 4) =
      1 / 8 := by
  have h : FirstPrice.mechanism.interimAllocation (fun _ : Fin 2 => 𝒰) (fun _ v => v / 2) 0
      (1 / 4) = 1 / 2 := by
    rw [← uniformBid_fin_two, FirstPrice.interimAllocation_uniformBid 0 (by norm_num),
      Fintype.card_fin]
    norm_num
  refine ⟨h, ?_⟩
  rw [FirstPrice.interimPayment_eq, h]
  norm_num

/-- Truthful bidding is not a Bayes–Nash equilibrium of the first-price auction with two bidders. -/
example : ¬ FirstPrice.mechanism.IsBayesNash (fun _ : Fin 2 => 𝒰) (fun _ => 1) (fun _ v => v) :=
  FirstPrice.not_isBayesNash_id (by rw [Fintype.card_fin]; norm_num)

/-- With two uniform bidders the first-price auction (bids `v / 2`) and the second-price auction
(truthful bids) both earn `1/3` ([Hartline2021], §2.7). -/
example : ∫ v, ∑ i, FirstPrice.mechanism.payment (fun j => v j / 2) i
      ∂Measure.pi (fun _ : Fin 2 => 𝒰) = 1 / 3 ∧
    ∫ v, ∑ i, Vickrey.mechanism.payment v i ∂Measure.pi (fun _ : Fin 2 => 𝒰) = 1 / 3 := by
  refine ⟨?_, ?_⟩
  · have h := FirstPrice.integral_sum_payment_uniformBid (ι := Fin 2)
    simp only [Fintype.card_fin, FirstPrice.uniformBid_two] at h
    rw [h]
    norm_num
  · rw [FirstPrice.integral_sum_payment_vickrey, Fintype.card_fin]
    norm_num

/-! ### Three uniform bidders -/

/-- With three uniform bidders each bids `2/3` of its value, and both auctions earn `1/2`. -/
example : FirstPrice.uniformBid (Fintype.card (Fin 3)) (3 / 4) = 1 / 2 ∧
    ∫ v, ∑ i, FirstPrice.mechanism.payment (fun j => FirstPrice.uniformBid 3 (v j)) i
      ∂Measure.pi (fun _ : Fin 3 => 𝒰) = 1 / 2 ∧
    ∫ v, ∑ i, Vickrey.mechanism.payment v i ∂Measure.pi (fun _ : Fin 3 => 𝒰) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.card_fin, FirstPrice.uniformBid]
    norm_num
  · have h := FirstPrice.integral_sum_payment_uniformBid (ι := Fin 3)
    rw [Fintype.card_fin] at h
    rw [h]
    norm_num
  · rw [FirstPrice.integral_sum_payment_vickrey, Fintype.card_fin]
    norm_num

/-! ### One bidder -/

/-- A lone bidder bids `0`: bidding nothing is a Bayes–Nash equilibrium of the first-price auction
with one bidder, and the auction earns nothing. -/
example : FirstPrice.mechanism.IsBayesNash (fun _ : Fin 1 => 𝒰) (fun _ => 1) (fun _ _ => 0) ∧
    ∫ v, ∑ i, FirstPrice.mechanism.payment (fun j => FirstPrice.uniformBid 1 (v j)) i
      ∂Measure.pi (fun _ : Fin 1 => 𝒰) = 0 := by
  have hb : (fun _ : Fin 1 => FirstPrice.uniformBid (Fintype.card (Fin 1))) = fun _ _ => 0 := by
    funext _ v
    rw [Fintype.card_fin, FirstPrice.uniformBid, Nat.cast_one, sub_self, zero_div, zero_mul]
  refine ⟨hb ▸ FirstPrice.isBayesNash_uniformBid, ?_⟩
  have h := FirstPrice.integral_sum_payment_uniformBid (ι := Fin 1)
  rw [Fintype.card_fin] at h
  rw [h]
  norm_num

end ComplexityTests.GameTheory.BayesNash
