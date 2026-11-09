/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Streaming.Frequency
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-!
# Graph streams

The **graph stream** of a word `a : Fin n → γ` lists the pairs `(i, a i)` in order
(`Cslib.Streaming.graphStream`); its items are distinct. In the concatenation of the graph streams
of two words `a` and `b`, every position where `a` and `b` agree contributes one item seen twice
and every other position two items seen once, so its `k`-th frequency moment is
`2 ^ k · #{i | a i = b i} + 2 · d(a, b)`, where `d` is the Hamming distance
(`Cslib.Streaming.freqMoment_graphStream_append_eq`). For `k ≠ 1` it is `2 n` exactly when `a` and
`b` agree nowhere (`Cslib.Streaming.freqMoment_graphStream_append_eq_two_mul_iff`).

These streams are the hard instances of the `Ω(n)` lower bounds for the frequency moments of Alon,
Matias and Szegedy [AlonMatiasSzegedy1999, Propositions 3.7 and 3.8] in
`CslibFrontier.Computability.Streaming.MomentLowerBound`: for Proposition 3.7 the graphs of two
codewords of a code of relative distance `1 / 2`, for Proposition 3.8 graphs encoding two sets.

## Main definitions

* `Cslib.Streaming.graphStream`: the stream of the pairs `(i, a i)`.

## Main results

* `Cslib.Streaming.freqMoment_graphStream_append`,
  `Cslib.Streaming.freqMoment_graphStream_append_eq`: the frequency moments of two concatenated
  graph streams.
* `Cslib.Streaming.freqMoment_graphStream_append_eq_two_mul_iff`: for `k ≠ 1`, `F_k = 2 n` exactly
  when the two words agree nowhere.

## References

* [N. Alon, Y. Matias, M. Szegedy, *The space complexity of approximating the frequency
  moments*][AlonMatiasSzegedy1999]
-/

public section

namespace Cslib.Streaming

open Finset

variable {n : ℕ} {γ : Type*}

/-- The **graph stream** `(0, a 0), …, (n - 1, a (n - 1))` of a word `a : Fin n → γ`. -/
def graphStream (a : Fin n → γ) : List (Fin n × γ) :=
  List.ofFn fun i => (i, a i)

@[simp] theorem length_graphStream (a : Fin n → γ) : (graphStream a).length = n :=
  List.length_ofFn

@[simp] theorem mem_graphStream {a : Fin n → γ} {p : Fin n × γ} :
    p ∈ graphStream a ↔ a p.1 = p.2 := by
  simp only [graphStream, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    rfl
  · intro h
    exact ⟨p.1, Prod.ext rfl h⟩

theorem nodup_graphStream (a : Fin n → γ) : (graphStream a).Nodup :=
  List.nodup_ofFn_ofInjective fun _ _ h => (Prod.ext_iff.1 h).1

variable [DecidableEq γ]

theorem count_graphStream (a : Fin n → γ) (p : Fin n × γ) :
    (graphStream a).count p = if a p.1 = p.2 then 1 else 0 := by
  rw [List.Nodup.count (nodup_graphStream a)]
  simp only [mem_graphStream]

/-- **The frequency moments of two concatenated graph streams**: each position where the words
agree contributes an item seen twice, and each other position two items seen once. -/
theorem freqMoment_graphStream_append (k : ℕ) (a b : Fin n → γ) :
    freqMoment k (graphStream a ++ graphStream b) = ∑ i, if a i = b i then 2 ^ k else 2 := by
  have hT : (graphStream a ++ graphStream b).toFinset =
      (univ : Finset (Fin n)).biUnion fun i => {(i, a i), (i, b i)} := by
    ext p
    simp only [List.mem_toFinset, List.mem_append, mem_graphStream, mem_biUnion, mem_univ,
      true_and, mem_insert, mem_singleton]
    constructor
    · rintro (h | h)
      · exact ⟨p.1, Or.inl (Prod.ext rfl h.symm)⟩
      · exact ⟨p.1, Or.inr (Prod.ext rfl h.symm)⟩
    · rintro ⟨i, rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
  unfold freqMoment
  rw [hT, sum_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    have hc (j : γ) : (graphStream a ++ graphStream b).count (i, j) =
        (if a i = j then 1 else 0) + (if b i = j then 1 else 0) := by
      rw [List.count_append, count_graphStream, count_graphStream]
    split_ifs with hab
    · rw [hab, pair_eq_singleton, sum_singleton, hc]
      simp [hab]
    · rw [sum_pair (fun h => hab (Prod.ext_iff.1 h).2), hc, hc]
      simp [hab, Ne.symm hab]
  · intro i _ j _ hij
    simp only [Function.onFun, disjoint_left, mem_insert, mem_singleton]
    rintro p (rfl | rfl) (h | h) <;> exact hij (Prod.ext_iff.1 h).1

/-- The frequency moments of two concatenated graph streams, through the number of positions where
the words agree and their Hamming distance. -/
theorem freqMoment_graphStream_append_eq (k : ℕ) (a b : Fin n → γ) :
    freqMoment k (graphStream a ++ graphStream b) =
      2 ^ k * #{i | a i = b i} + 2 * hammingDist a b := by
  rw [freqMoment_graphStream_append, sum_ite, sum_const, sum_const, smul_eq_mul, smul_eq_mul]
  simp only [hammingDist]
  ring

/-- For `k ≠ 1`, the `k`-th frequency moment of two concatenated graph streams of length `n` is
`2 n` exactly when the words agree nowhere. For `k = 1` it is always `2 n`. -/
theorem freqMoment_graphStream_append_eq_two_mul_iff {k : ℕ} (hk : k ≠ 1) (a b : Fin n → γ) :
    freqMoment k (graphStream a ++ graphStream b) = 2 * n ↔ ∀ i, a i ≠ b i := by
  have hsum := card_filter_eq_add_hammingDist a b
  rw [Fintype.card_fin] at hsum
  rw [freqMoment_graphStream_append_eq]
  have hP : 2 ^ k ≠ 2 := fun h =>
    hk (Nat.pow_right_injective (le_refl 2) (h.trans (pow_one 2).symm))
  have hiff : #{i | a i = b i} = 0 ↔ ∀ i, a i ≠ b i := by
    simp only [card_eq_zero, filter_eq_empty_iff, mem_univ, true_imp_iff, ne_eq]
  rw [← hiff]
  generalize #{i | a i = b i} = c at hsum ⊢
  generalize hammingDist a b = δ at hsum ⊢
  subst hsum
  constructor
  · intro h
    by_contra hc
    have h2 : 2 ^ k * c = 2 * c := by omega
    exact hP (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hc) h2)
  · intro hc
    subst hc
    simp

end Cslib.Streaming
