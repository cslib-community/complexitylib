/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Algorithms.Lean.VectorConvolution
import CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorProbability
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for convolution in `[r]^d` and the base-`r` trial

Concrete runs of `CslibFrontier.Algorithms.Lean.VectorConvolution` on `[3]^2`, with inputs
supported on vectors of size `1` and threshold `s = 1`:

* the returned entries, computed by running the program and checked against `ret_solveM`: the
  binomial convolution counts `f (1, 0) g (1, 0)` twice at `(2, 0)`;
* the vector convolution through `ret_solveM_factorial`;
* the exact tick count, computed and checked against `time_solveM`.

One base-`3` trial of `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.VectorTrial` with
`A = {1, 2}`, `B = {3, 5}`, `C = {4, 6, 9}`, `d = 3` (balanced vectors are the permutations of
`(0, 1, 2)`), `p = 29 ≥ 3 ^ 3` and the seed `(ξ, α, β) = (1, 0, 3)`: the hashes `1 = (1, 0, 0)` and
`6 = (0, 2, 0)` add up without carries to the balanced `7 = (1, 2, 0)`, so `4 = 1 + 3` is reported.
Soundness excludes `9` for every seed, and the success count of `card_vaccepts_add_ge` applies to
`c = 4`.
-/

namespace CslibFrontierTests.Algorithms.Lean.VectorConvolution

open Finset Cslib Cslib.Algorithms.Lean.VectorConvolution Cslib.Algorithms.Lean.SubsetConvThreeSum

/-- Left input: weight `2` on `(1, 0)` and `3` on `(0, 1)`. -/
def f : (Fin 2 → ℕ) → ℤ := fun x => if x = ![1, 0] then 2 else if x = ![0, 1] then 3 else 0

/-- Right input: weight `5` on `(1, 0)` and `7` on `(0, 1)`. -/
def g : (Fin 2 → ℕ) → ℤ := fun x => if x = ![1, 0] then 5 else if x = ![0, 1] then 7 else 0

/-- The three queries of size `2` in `[3]^2`. -/
def queries : List (Fin 2 → ℕ) := [![2, 0], ![1, 1], ![0, 2]]

theorem f_ranked : ∀ a, f a ≠ 0 → ∑ i, a i = 1 := by
  intro a h
  unfold f at h
  split_ifs at h with h₀ h₁ <;> simp_all [Fin.sum_univ_two]

theorem g_ranked : ∀ b, g b ≠ 0 → ∑ i, b i = 1 := by
  intro b h
  unfold g at h
  split_ifs at h with h₀ h₁ <;> simp_all [Fin.sum_univ_two]

theorem queries_ok : ∀ C ∈ queries, (∀ i, C i < 3) ∧ ∑ i, C i = 1 + 1 := by
  decide

/-- Running the program: `2 · 2 · 5 = 20` at `(2, 0)`, `2 · 7 + 3 · 5 = 29` at `(1, 1)` and
`3 · 7 = 21`, counted twice, at `(0, 2)`. -/
example : (solveM (List.finRange 2) 3 1 f g queries).ret = [20, 29, 42] := by decide +kernel

/-- The same answers are the binomial convolutions, by `ret_solveM`. -/
example : queries.map (binomConvolution f g) = [20, 29, 42] := by
  rw [← ret_solveM (List.nodup_finRange 2) List.mem_finRange f_ranked g_ranked queries_ok
    (by norm_num : 1 ≤ 1 + 1)]
  decide +kernel

/-- With factorial weights (all `1` on vectors of size `1`), the answers are
`(∏ i, C i !) (f ⋆ g) C`: the vector convolutions are `10, 29, 21`. -/
example : queries.map (fun C => (vecFactorial C : ℤ) * vecConvolution f g C) = [20, 29, 42] := by
  rw [← ret_solveM_factorial (List.nodup_finRange 2) List.mem_finRange f_ranked g_ranked
    queries_ok (by norm_num : 1 ≤ 1 + 1)]
  decide +kernel

/-- The tick count of the run: `3 (3 · 2 + 1) (3 + (2 + 3 + 2)) = 210`. -/
example : (solveM (List.finRange 2) 3 1 f g queries).time = 210 := by decide +kernel

/-- The same count from `time_solveM`. -/
example : (solveM (List.finRange 2) 3 1 f g queries).time = 210 := by
  rw [time_solveM (List.nodup_finRange 2) List.mem_finRange]
  decide +kernel

/-! ### A base-`3` trial -/

instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩

/-- The seed `(1, 0, 3)` reports exactly `4 = 1 + 3`. -/
example : (vtrialM 3 3 1 (⟨1, 0, 3⟩ : Seed 29) [1, 2] [3, 5] [4, 6, 9]).ret = [4] := by
  decide +kernel

/-- Soundness: `9` is accepted under no seed, since it is not a sum. -/
example (σ : Seed 29) : ¬ VAccepts 3 3 σ [1, 2] [3, 5] 9 := fun h => by
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_vaccepts h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

/-- No pair of `{1, 2} × {3, 5}` sums to `4` modulo `29` without summing to `4`. -/
theorem falsePairs_four : falsePairs 29 4 [1, 2] [3, 5] = ∅ := by decide

/-- The success count of one base-`3` trial, applied to `c = 4`: at least `#P · 28` seeds
accept. -/
example : #(balancedPairs 3 3) * 28 ≤
    #((seeds 29).filter fun s => VAccepts 3 3 s [1, 2] [3, 5] 4) := by
  have h := card_vaccepts_add_ge (p := 29) (r := 3) (d := 3) (by norm_num)
    (A := [1, 2]) (B := [3, 5]) (fun _ h => h) (fun _ h => h) (a := 1) (b := 3) (c := 4)
    (by simp) (by simp) (by decide) (by decide) rfl
  rwa [falsePairs_four, card_empty, zero_mul, mul_zero, add_zero] at h

end CslibFrontierTests.Algorithms.Lean.VectorConvolution
