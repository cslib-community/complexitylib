/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.DecisionTree.Basic
public import Complexity.Foundations.Data.BitString.Threshold

/-!
# Decision trees for symmetric functions

A function of `n` bits is *evasive* when every decision tree computing it queries all `n` bits in
the worst case, that is, when its decision tree complexity [Jukna, Chapter 14][Jukna2012] is `n`.
Every nonconstant symmetric function is evasive
(`DecisionTree.complexity_eq_card_of_isSymmetric`), although its sensitivity can be as small as
about `n / 2`, as for majority.

The proof is an adversary argument on subcubes
(`DecisionTree.card_le_depth_of_eval_eq_comp_card_filter`). Suppose that on the inputs agreeing
with `a` off a set `S` of free coordinates, a tree's output depends only on the number `k` of true
free bits, through a profile `g`, and that `g` changes between two consecutive counts `m` and
`m + 1` with `m + 1 ≤ #S`. When the tree queries a free bit, the adversary answers `false` if the
change still fits among the remaining free bits, and `true` otherwise, shifting the profile by one.
Either way the hypotheses persist with one free bit fewer, so a leaf cannot be reached before all
free bits are queried.

## Main results

* `Cslib.DecisionTree.card_le_depth_of_eval_eq_comp_card_filter`: the adversary argument.
* `Cslib.DecisionTree.complexity_eq_card_of_isSymmetric`: nonconstant symmetric functions are
  evasive.
* `Cslib.DecisionTree.complexity_threshold`, `Cslib.DecisionTree.complexity_majority`: threshold
  functions `Th^n_j` with `1 ≤ j ≤ n`, and majority, are evasive.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

open BitString Finset

namespace DecisionTree

variable {ι β : Type*}

/-- Some assignment agrees with `a` off `S` and has exactly `m` true bits in `S`. -/
private theorem exists_eq_off_card_filter_eq (S : Finset ι) (a : ι → Bool) {m : ℕ}
    (hm : m ≤ #S) :
    ∃ x : ι → Bool, (∀ j ∉ S, x j = a j) ∧ #(S.filter fun j => x j = true) = m := by
  classical
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hm
  refine ⟨fun j => if j ∈ S then decide (j ∈ T) else a j, fun j hj => by simp [hj], ?_⟩
  have : (S.filter fun j => (if j ∈ S then decide (j ∈ T) else a j) = true) = T := by
    ext j
    constructor
    · intro h
      obtain ⟨hjS, h⟩ := mem_filter.1 h
      simpa [hjS] using h
    · intro hj
      exact mem_filter.2 ⟨hTS hj, by simp [hTS hj, hj]⟩
  rw [this, hT]

/-- Inputs agreeing with `Function.update a i b` off `S.erase i` agree with `a` off `S`, have bit
`i` equal to `b`, and shift the count of true bits in `S` by `if b then 1 else 0`. -/
private theorem eq_off_and_card_filter_of_eq_off_erase [DecidableEq ι] {S : Finset ι} {i : ι}
    (hi : i ∈ S) (a : ι → Bool) (b : Bool) (x : ι → Bool)
    (hx : ∀ j ∉ S.erase i, x j = Function.update a i b j) :
    (∀ j ∉ S, x j = a j) ∧ x i = b ∧
      #(S.filter fun j => x j = true) =
        #((S.erase i).filter fun j => x j = true) + (if b then 1 else 0) := by
  have hxi : x i = b := by simpa using hx i (by simp)
  refine ⟨fun j hj => ?_, hxi, ?_⟩
  · have hji : j ≠ i := fun h => hj (h ▸ hi)
    simpa [Function.update_of_ne hji] using hx j fun h => hj (mem_of_mem_erase h)
  · rw [← insert_erase hi, filter_insert, erase_insert (notMem_erase i S)]
    cases b with
    | false => simp [hxi]
    | true =>
      simp only [hxi, ite_true]
      rw [card_insert_of_notMem (by simp)]

/-- A leaf tree cannot agree with a profile `g` that takes two distinct values at counts
`m, m + 1 ≤ #S`. -/
private theorem false_of_leaf_eval_eq_comp_card_filter (b : β) (S : Finset ι) (a : ι → Bool)
    (g : ℕ → β) (m : ℕ)
    (ht : ∀ x : ι → Bool, (∀ j ∉ S, x j = a j) →
      (DecisionTree.leaf b : DecisionTree ι β).eval x = g #(S.filter fun j => x j = true))
    (hm : m + 1 ≤ #S) (hg : g m ≠ g (m + 1)) : False := by
  obtain ⟨x, hx, hxc⟩ := exists_eq_off_card_filter_eq S a (m := m) (by omega)
  obtain ⟨y, hy, hyc⟩ := exists_eq_off_card_filter_eq S a (m := m + 1) hm
  have h1 := ht x hx
  have h2 := ht y hy
  rw [hxc, eval_leaf] at h1
  rw [hyc, eval_leaf] at h2
  exact hg (h1.symm.trans h2)

/-- **Adversary argument for symmetric functions.** If, on the inputs agreeing with `a` off a set
`S` of free coordinates, a tree's output depends only on the number of true free bits, through a
profile `g` that changes between two consecutive counts `m, m + 1 ≤ #S`, then the tree has depth
at least `#S`. The output type is arbitrary. -/
theorem card_le_depth_of_eval_eq_comp_card_filter (t : DecisionTree ι β) (S : Finset ι)
    (a : ι → Bool) (g : ℕ → β) (m : ℕ)
    (ht : ∀ x : ι → Bool, (∀ j ∉ S, x j = a j) → t.eval x = g #(S.filter fun j => x j = true))
    (hm : m + 1 ≤ #S) (hg : g m ≠ g (m + 1)) : #S ≤ t.depth := by
  classical
  induction t generalizing S a g m with
  | leaf b => exact (false_of_leaf_eval_eq_comp_card_filter b S a g m ht hm hg).elim
  | node i t₀ t₁ ih₀ ih₁ =>
    rw [depth_node]
    by_cases hi : i ∈ S
    · -- the queried bit is free: the adversary fixes it and recurses on `S.erase i`
      have hcard : #(S.erase i) + 1 = #S := card_erase_add_one hi
      rcases Nat.lt_or_ge #S 2 with hS | hS
      · omega
      by_cases hm' : m + 1 ≤ #(S.erase i)
      · -- answer `false`: the count is unchanged
        have := ih₀ (S.erase i) (Function.update a i false) g m (fun x hx => by
          obtain ⟨hx', hxi, hc⟩ := eq_off_and_card_filter_of_eq_off_erase hi a false x hx
          have := ht x hx'
          rw [eval_node, hxi] at this
          simpa [hc] using this) hm' hg
        omega
      · -- answer `true`: the count shifts by one
        have hm1 : 1 ≤ m := by omega
        have := ih₁ (S.erase i) (Function.update a i true) (fun k => g (k + 1)) (m - 1)
          (fun x hx => by
            obtain ⟨hx', hxi, hc⟩ := eq_off_and_card_filter_of_eq_off_erase hi a true x hx
            have := ht x hx'
            rw [eval_node, hxi] at this
            simpa [hc] using this) (by omega) (by rwa [Nat.sub_add_cancel hm1])
        omega
    · -- the queried bit is fixed: follow the branch of `a i`
      cases hai : a i with
      | false =>
        have := ih₀ S a g m (fun x hx => by
          have := ht x hx
          rwa [eval_node, hx i hi, hai] at this) hm hg
        omega
      | true =>
        have := ih₁ S a g m (fun x hx => by
          have := ht x hx
          rwa [eval_node, hx i hi, hai] at this) hm hg
        omega

/-- A function `g : ℕ → Bool` taking different values at two points `≤ n` changes between two
consecutive points `≤ n`. -/
private theorem exists_add_one_le_ne {g : ℕ → Bool} {n u v : ℕ} (hu : u ≤ n) (hv : v ≤ n)
    (h : g u ≠ g v) : ∃ m, m + 1 ≤ n ∧ g m ≠ g (m + 1) := by
  by_contra hc
  push Not at hc
  have key (k : ℕ) (hk : k ≤ n) : g k = g 0 := by
    induction k with
    | zero => rfl
    | succ k ih => rw [← hc k hk, ih (by omega)]
  exact h ((key u hu).trans (key v hv).symm)

variable {n : ℕ}

/-- **Nonconstant symmetric functions are evasive**: every decision tree computing a nonconstant
symmetric function of `n` bits queries all of them in the worst case. -/
theorem complexity_eq_card_of_isSymmetric {f : BooleanFunction n} (hf : f.IsSymmetric)
    (hnc : ¬ Function.IsConst f) : complexity f = n := by
  refine le_antisymm ((complexity_le_card f).trans_eq (Fintype.card_fin n)) ?_
  obtain ⟨g, hg⟩ := hf.exists_eq_comp_weight
  obtain ⟨x, y, hxy⟩ : ∃ x y, f x ≠ f y := by
    by_contra h
    push Not at h
    exact hnc h
  obtain ⟨m, hm, hgm⟩ := exists_add_one_le_ne (g := g) (weight_le_length x) (weight_le_length y)
    (by rwa [hg, hg])
  refine le_complexity_iff.2 fun t ht => ?_
  simpa using card_le_depth_of_eval_eq_comp_card_filter t univ (fun _ => false) g m
    (fun z _ => by rw [ht z, ← hg z]; rfl) (by simpa using hm) hgm

/-- **Threshold functions are evasive**: `D(Th^n_j) = n` for `1 ≤ j ≤ n`. -/
theorem complexity_threshold {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n) :
    complexity (threshold n j) = n := by
  refine complexity_eq_card_of_isSymmetric (isSymmetric_threshold j) fun h => ?_
  have h0 : threshold n j (fun _ => false) = false := by
    have : weight (fun _ : Fin n => false) = 0 := by simp [weight]
    rw [threshold_apply, decide_eq_false_iff_not, this]
    omega
  have h1 : threshold n j (fun _ => true) = true := by
    rw [threshold_apply, decide_eq_true_iff]
    simpa [weight] using hjn
  exact Bool.false_ne_true (h0.symm.trans ((h _ _).trans h1))

/-- **Majority is evasive**: `D(MAJ_n) = n` for `n ≥ 1`. -/
theorem complexity_majority (hn : 1 ≤ n) : complexity (majority n) = n :=
  complexity_threshold (by omega) (by omega)

end DecisionTree

end Cslib
