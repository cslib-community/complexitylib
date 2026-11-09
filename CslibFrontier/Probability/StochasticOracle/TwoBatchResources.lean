/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.TwoBatchApproximation
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.RatBinary
import Mathlib.Tactic

/-!
# Encoded inputs and rounded-selector resource bounds

The binary inputs in [Wang2027], Theorem 2(2), PDF pp. 7–8, consist of the
deadline, tolerance and the ordered list of probability/cost/cutoff triples.
Rationals use reduced signed numerator/positive denominator binary encodings.
The integer `m` is an inverse-tolerance budget satisfying `1 ≤ ε*m`, not a
polynomial bound on the numerical sizes of the input costs.

These bounds concern the actual enumerated tables and rational operands. They
do not assert a native binary-machine execution certificate for the selector.

## Main results

* `candidates_length_le`: a uniform polynomial bound on all retained candidates.
* `inputSize_bounds`: the encoded input bounds its population and rational fields.
* `batchFailure_binaryWidth_le`, `batchCost_binaryWidth_le`, `gain_binaryWidth_le`:
  polynomial binary widths of exact scheduling objectives.
* `branch_product_binaryWidth_le`: binary widths of retained DP products.
-/

public section
namespace Cslib.Probability.StochasticOracle.TwoBatchApproximation
open Cslib.Algorithms.Lean.DynamicProgramming.MinProduct
open Turing.MultiTapeTM

variable {k : ℕ} (I : FullCoverInstance (Fin k) ℚ)

/-- The actual binary input word, including the tolerance and deadline. List and
pair framing are the standard machine encodings. The population size is recovered
from the list; proofs of positivity or validity are not input fields. -/
@[expose] def inputEncoding (ε D : ℚ) : List Bool :=
  encPair encRatBin (encPair encRatBin
    (encList (encPair encRatBin (encPair encRatBin encRatBin))))
      (ε,D,(population.map (fun i => (I.success i,I.cost i,I.cutoff i))))

/-- Size of the complete binary input, not its numerical cost magnitudes. -/
@[expose] def inputSize (ε D : ℚ) : ℕ := (inputEncoding I ε D).length

private theorem list_encoding_length (xs : List (ℚ × ℚ × ℚ)) :
    (encList (encPair encRatBin (encPair encRatBin encRatBin)) xs).length =
      (xs.map (fun (p,c,l) =>
        2 * (encRatBin p).length + 2 * (encRatBin c).length +
          (encRatBin l).length + 2)).sum * 2 + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases x with ⟨p,c,l⟩
    simp only [encList_cons, List.length_append, length_frame, length_encPair,
      ih, List.map_cons, List.sum_cons, List.length_cons]
    omega

/-- Every encoded input field and the number of opportunities are bounded by
the complete input word. This justifies polynomial bounds in `inputSize`. -/
theorem inputSize_bounds (ε D : ℚ) :
    k ≤ inputSize I ε D ∧ ε.binaryWidth ≤ inputSize I ε D ∧
      D.binaryWidth ≤ inputSize I ε D ∧
      ∀ i, (I.success i).binaryWidth ≤ inputSize I ε D ∧
        (I.cost i).binaryWidth ≤ inputSize I ε D ∧
        (I.cutoff i).binaryWidth ≤ inputSize I ε D := by
  let xs := population.map (fun i => (I.success i,I.cost i,I.cutoff i))
  have hlen := list_encoding_length xs
  have he : inputSize I ε D =
      2 * (encRatBin ε).length + 1 + 2 * (encRatBin D).length + 1 +
        (encList (encPair encRatBin (encPair encRatBin encRatBin)) xs).length := by
    unfold inputSize inputEncoding
    rw [length_encPair, length_encPair]
    change 2 * (encRatBin ε).length + 1 +
      (2 * (encRatBin D).length + 1 +
        (encList (encPair encRatBin (encPair encRatBin encRatBin)) xs).length) = _
    omega
  have hxs : xs.length = k := by simp [xs, population]
  have hε := binaryWidth_le_length_encRatBin ε
  have hD := binaryWidth_le_length_encRatBin D
  refine ⟨by omega,by omega,by omega,?_⟩
  intro i
  have hi : (I.success i,I.cost i,I.cutoff i) ∈ xs :=
    List.mem_map.mpr ⟨i,by simp [population],rfl⟩
  have hmem : 2 * (encRatBin (I.success i)).length +
      2 * (encRatBin (I.cost i)).length + (encRatBin (I.cutoff i)).length + 2 ≤
      (xs.map (fun (p,c,l) => 2 * (encRatBin p).length +
        2 * (encRatBin c).length + (encRatBin l).length + 2)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨_,hi,rfl⟩)
  have hp := binaryWidth_le_length_encRatBin (I.success i)
  have hc := binaryWidth_le_length_encRatBin (I.cost i)
  have hl := binaryWidth_le_length_encRatBin (I.cutoff i)
  exact ⟨by omega,by omega,by omega⟩

/-- All retained candidates across all cutoff families and maximum-cost branches
have a polynomial total count. No exhaustive-subset specification is counted
as executable code. `m` pays inverse tolerance, separately from binary input size. -/
theorem candidates_length_le {ε : ℚ} (hε : 0 < ε) (m : ℕ) (hm : 1 ≤ ε * m)
    (D : ℚ) :
    (candidates I ε D).length ≤ k * (k + 1) *
      (1 + k * ((k + 1) ^ 2 * m + 1)) := by
  let M := (k + 1) ^ 2 * m + 1
  have hflat {α β : Type} (xs : List α) (f : α → List β) (N : ℕ)
      (h : ∀ x ∈ xs, (f x).length ≤ N) : (xs.flatMap f).length ≤ xs.length * N := by
    rw [List.length_flatMap]
    have hh := List.sum_le_length_nsmul (xs.map (fun x => (f x).length)) N
      (by intro j hj; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hj; exact h x hx)
    simpa only [List.length_map, smul_eq_mul] using hh
  have hbranch (a b : ℚ) (r : Fin k) : (maximumBranch I ε a b r).length ≤ M := by
    unfold maximumBranch
    simp only [List.length_map]
    have hb := (branch_budget I.cost (failure I)
      (outside := failureProduct I
        ((optional I a b).filter (fun i => I.cost r < I.cost i))) r (I.cost_pos r) hε m hm
      ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r))
      (by intro i hi; exact (of_decide_eq_true (List.mem_filter.mp hi).2).1)).1
    have hn : ((optional I a b).filter
        (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)).length ≤ k := by
      exact (List.length_filter_le ..).trans ((List.length_filter_le ..).trans_eq
        (by simp [population]))
    exact hb.trans (by dsimp [M]; gcongr)
  have hfamily (a b : ℚ) : (familyCandidates I ε a b).length ≤ 1 + k * M := by
    unfold familyCandidates
    split_ifs
    · apply (List.length_filter_le ..).trans
      simp only [List.length_cons]
      have hh := hflat (optional I a b) (maximumBranch I ε a b) M
        (fun r _ => hbranch a b r)
      have hn : (optional I a b).length ≤ k :=
        (List.length_filter_le ..).trans_eq (by simp [population])
      nlinarith
    · simp
  unfold candidates
  apply (hflat _ _ ((k + 1) * (1 + k * M)) ?_).trans_eq
    (by simp [population, M, Nat.mul_assoc])
  intro a _
  have hh := hflat (0 :: population.map I.cutoff)
    (fun b => if a + b ≤ D then familyCandidates I ε a b else [])
    (1 + k * M) (by
      intro b _
      split_ifs
      · exact hfamily a b
      · simp)
  simpa only [List.length_cons, List.length_map, population, List.length_finRange,
    Nat.add_comm k 1] using hh

/-- Every independent failure-product operand, for every batch, has width
linear in the population times the binary input length. This includes products
computed when comparing reconstructed candidates. -/
theorem batchFailure_binaryWidth_le (ε D : ℚ) (A : Finset (Fin k)) :
    (I.batchFailure A).binaryWidth ≤ k * (inputSize I ε D + 2) + 1 := by
  have hw (i : Fin k) : (failure I i).binaryWidth ≤ inputSize I ε D + 2 := by
    have h := Rat.binaryWidth_sub_le 1 (I.success i)
    have hi := (inputSize_bounds I ε D).2.2.2 i
    simp only [Rat.binaryWidth_one] at h
    unfold failure
    omega
  have hs := List.sum_le_length_nsmul
    ((A.toList.map (failure I)).map Rat.binaryWidth) (inputSize I ε D + 2) (by
      intro j hj
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
      exact hw i)
  simp only [List.length_map, smul_eq_mul] at hs
  have hp := Rat.binaryWidth_prod_le (A.toList.map (failure I))
  have hlen : A.toList.length ≤ k := by
    simpa only [Finset.length_toList, Fintype.card_fin] using Finset.card_le_univ A
  have heq : (A.toList.map (failure I)).prod = I.batchFailure A := by
    rw [← List.prod_toFinset _ A.nodup_toList, Finset.toList_toFinset]
    rfl
  rw [heq] at hp
  exact hp.trans (by nlinarith)

/-- Summed expected costs use polynomially bounded binary operands, even when
the input cost magnitudes are exponential in their encoded lengths. -/
theorem batchCost_binaryWidth_le (ε D : ℚ) (A : Finset (Fin k)) :
    (I.batchCost A).binaryWidth ≤ k * (inputSize I ε D + 1) + 1 := by
  have hs := List.sum_le_length_nsmul
    ((A.toList.map I.cost).map (fun q => q.binaryWidth + 1))
    (inputSize I ε D + 1) (by
      intro j hj
      obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hj
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hq
      exact Nat.add_le_add_right ((inputSize_bounds I ε D).2.2.2 i).2.1 1)
  have hp := Rat.binaryWidth_sum_le (A.toList.map I.cost)
  have hlen : A.toList.length ≤ k := by
    simpa only [Finset.length_toList, Fintype.card_fin] using Finset.card_le_univ A
  have heq : (A.toList.map I.cost).sum = I.batchCost A := by
    rw [← List.sum_toFinset _ A.nodup_toList, Finset.toList_toFinset]
    rfl
  rw [heq] at hp
  simp only [List.length_map, smul_eq_mul] at hs
  exact hp.trans (by nlinarith)

/-- The exact savings used in every final comparison have polynomial binary
width. This bounds the actual comparison values rather than substituting a
rounded objective or real-number comparison oracle. -/
theorem gain_binaryWidth_le (ε D : ℚ) (A : Finset (Fin k)) :
    (gain I A).binaryWidth ≤ k * (2 * inputSize I ε D + 3) + 4 := by
  have hp := batchFailure_binaryWidth_le I ε D A
  have hc := batchCost_binaryWidth_le I ε D (Finset.univ \ A)
  have hs := Rat.binaryWidth_sub_le 1 (I.batchFailure A)
  have hm := Rat.binaryWidth_mul_le (1 - I.batchFailure A)
    (I.batchCost (Finset.univ \ A))
  simp only [Rat.binaryWidth_one] at hs
  unfold gain
  nlinarith

/-- Every retained branch product has polynomial binary width in the complete
input. The initial outside product and all intermediate tail tables are covered
by the same estimate; no bound on the numerical probability denominators is assumed. -/
theorem branch_product_binaryWidth_le (ε D a b : ℚ) (r : Fin k)
    {e : Entry (Fin k)}
    (he : e ∈ branch I.cost (failure I) ε r
      (failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i)))
      ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r))) :
    e.product.binaryWidth ≤ 2 * k * (inputSize I ε D + 2) + 1 := by
  have hw (i : Fin k) : (failure I i).binaryWidth ≤ inputSize I ε D + 2 := by
    have h := Rat.binaryWidth_sub_le 1 (I.success i)
    have hi := (inputSize_bounds I ε D).2.2.2 i
    simp only [Rat.binaryWidth_one] at h
    unfold failure
    omega
  have hlen (p : Fin k → Bool) : ((optional I a b).filter p).length ≤ k :=
    (List.length_filter_le ..).trans ((List.length_filter_le ..).trans_eq
      (by simp [population]))
  have hs (xs : List (Fin k)) :
      (xs.map (fun i => (failure I i).binaryWidth)).sum ≤
        xs.length * (inputSize I ε D + 2) := by
    have hh := List.sum_le_length_nsmul
      (xs.map (fun i => (failure I i).binaryWidth)) (inputSize I ε D + 2) (by
        intro j hj
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
        exact hw i)
    simpa only [List.length_map, smul_eq_mul] using hh
  have hp := Rat.binaryWidth_prod_le
    (((optional I a b).filter (fun i => I.cost r < I.cost i)).map (failure I))
  have hb := run_product_binaryWidth_le _ _ _ _ he
  change e.product.binaryWidth ≤
    (failureProduct I ((optional I a b).filter (fun i => I.cost r < I.cost i))).binaryWidth +
      (((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)).map
        (fun i => (failure I i).binaryWidth)).sum at hb
  have hs₀ := hs ((optional I a b).filter (fun i => I.cost r < I.cost i))
  have hs₁ := hs ((optional I a b).filter (fun i => I.cost i ≤ I.cost r ∧ i ≠ r))
  have hl₀ := hlen (fun i => I.cost r < I.cost i)
  have hl₁ := hlen (fun i => I.cost i ≤ I.cost r ∧ i ≠ r)
  simp only [List.map_map, Function.comp_def] at hp
  change _ ≤ (failureProduct I _).binaryWidth + _ at hb
  unfold failureProduct at hb
  nlinarith

end Cslib.Probability.StochasticOracle.TwoBatchApproximation
