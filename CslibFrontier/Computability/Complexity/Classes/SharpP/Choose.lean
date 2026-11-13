/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.SharpP.Closure
public import CslibFrontier.Foundations.Data.BitString.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.BitString.WordCount

/-!
# Binomial coefficients of #P counts

If `f` is in `#P` and `g` is computed in polynomial time with unary output, then
`a ↦ C(f a, g a)` is in `#P` [Beigel and Gill, Property 8(ii)][BeigelGill1992]
(`Cslib.Complexity.SharpP.choose_mem`). A certificate lists `g a` accepted certificates of the
original verifier in strictly increasing lexicographic order, so each `g a`-element set of
accepted certificates is counted exactly once.

The word test `Cslib.Complexity.SharpP.subsetTest` reads `K` rows of `Z` bits. The first `k` rows
must be accepted by `acc` and strictly increasing, and the remaining rows must be zero, so it
accepts `C(N, k)` words when `acc` accepts `N` words of length `Z` and `k ≤ K`
(`Cslib.Complexity.SharpP.card_filter_subsetTest`). The extra zero rows let Toda's counting test
use one row budget for every subset size (`Cslib.Complexity.Toda.countingTest`).

## Main definitions

* `Cslib.Complexity.SharpP.subsetTest`: strictly increasing accepted rows, padded by zero rows.

## Main results

* `Cslib.Complexity.SharpP.card_filter_subsetTest`: the test accepts `C(N, k)` words.
* `Cslib.Complexity.SharpP.computableInPolyTime_subsetTest`: the test runs in polynomial time.
* `Cslib.Complexity.SharpP.choose_mem`: binomial coefficients of #P counts are in #P.

## References

* [R. Beigel, J. Gill, *Counting classes: thresholds, parity, mods, and fewness*][BeigelGill1992]
-/

public section

namespace Cslib.Complexity.SharpP

open Finset BitString Turing.MultiTapeTM

/-- The `k`-subset test on `K` rows of `Z` bits: the first `k` rows are accepted by `acc` and
strictly increasing, and the other rows are zero. -/
def subsetTest (acc : List Bool → Bool) (K Z k : ℕ) (zs : List Bool) : Bool :=
  ((BitString.listRows K Z zs).zipIdx.all fun p =>
      if p.2 < k then acc p.1 else !(p.1.any fun b => b)) &&
    (List.range (k - 1)).all fun i =>
      BitString.wordLt (BitString.listRow Z i zs) (BitString.listRow Z (i + 1) zs)

@[fun_prop]
theorem computableInPolyTime_subsetTest {γ : Type} {input : γ ↪ List Bool}
    {acc : γ → List Bool → Bool}
    (hacc : ComputableInPolyTime (fun p : γ × List Bool => acc p.1 p.2)
      (encPair input encBits) encBool)
    {K Z k : γ → ℕ} {zs : γ → List Bool}
    (hK : ComputableInPolyTime K input encUnary)
    (hZ : ComputableInPolyTime Z input encUnary)
    (hk : ComputableInPolyTime k input encUnary)
    (hzs : ComputableInPolyTime zs input encBits) :
    ComputableInPolyTime (fun c => subsetTest (acc c) (K c) (Z c) (k c) (zs c)) input
      encBool := by
  unfold subsetTest
  fun_prop

/-- The block-level predicate corresponding to `subsetTest`: the first `k` blocks are accepted and
strictly increasing in lexicographic order, and the remaining blocks are zero. -/
private def SubsetBlockPred (acc : List Bool → Bool) {K Z k : ℕ} (hk : k ≤ K)
    (t : Fin K → BitString Z) : Prop :=
  (∀ j : Fin K, ((j : ℕ) < k → acc (List.ofFn (t j)) = true) ∧ (k ≤ j → t j = 0)) ∧
    ∀ (i : ℕ) (h : i + 1 < k), toLex (t ⟨i, by omega⟩) < toLex (t ⟨i + 1, by omega⟩)

/-- `subsetTest` on `List.ofFn v` holds if and only if `SubsetBlockPred` holds on the blocks of
`v`. -/
private theorem subsetTest_ofFn_iff (acc : List Bool → Bool) {K k Z : ℕ} (hk : k ≤ K)
    (v : Fin (K * Z) → Bool) :
    subsetTest acc K Z k (List.ofFn v) = true ↔
      SubsetBlockPred acc hk (BitString.blocksEquiv v) := by
  -- the test on blocks
  have hrows : BitString.listRows K Z (List.ofFn v) =
      List.ofFn fun j => List.ofFn (BitString.blocksEquiv v j) := by
    rw [BitString.listRows_eq_ofFn, BitString.ofList_ofFn]
    rfl
  have hrow (i : ℕ) (hi : i < K) :
      BitString.listRow Z i (List.ofFn v) = List.ofFn (BitString.blocksEquiv v ⟨i, hi⟩) := by
    rw [BitString.listRow_eq_ofFn (count := K) Z ⟨i, hi⟩, BitString.ofList_ofFn]
    rfl
  simp only [subsetTest, Bool.and_eq_true, hrows, SubsetBlockPred]
  refine and_congr ?_ ?_
  · simp only [List.all_eq_true, Prod.forall]
    refine ⟨fun h j => ?_, fun h w j hw => ?_⟩
    · have hj := h (List.ofFn (BitString.blocksEquiv v j)) j
        (by rw [List.mem_zipIdx_iff_getElem?]; simp)
      refine ⟨fun hjk => by simpa [hjk] using hj, fun hjk => ?_⟩
      rw [ite_eq_right (by omega)] at hj
      exact (not_any_ofFn_eq_true_iff _).1 hj
    · rw [List.mem_zipIdx_iff_getElem?, List.getElem?_ofFn] at hw
      simp only at hw
      split at hw
      · rename_i hjK
        rw [← Option.some.inj hw]
        split
        · exact (h ⟨j, hjK⟩).1 (by simpa)
        · rename_i hjk
          exact (not_any_ofFn_eq_true_iff _).2 ((h ⟨j, hjK⟩).2 (Nat.le_of_not_lt hjk))
      · exact absurd hw (by simp)
  · simp only [List.all_eq_true, List.mem_range]
    refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
    · have := h i (by omega)
      rwa [hrow i (by omega), hrow (i + 1) (by omega), BitString.wordLt_ofFn_iff] at this
    · rw [hrow i (by omega), hrow (i + 1) (by omega), BitString.wordLt_ofFn_iff]
      exact h i (by omega)

/-- **The `k`-subset test counts `k`-element sets of accepted words**, for `k ≤ K`. -/
theorem card_filter_subsetTest (acc : List Bool → Bool) {K k : ℕ} (Z : ℕ) (hk : k ≤ K) :
    (univ.filter fun zs : Fin (K * Z) → Bool => subsetTest acc K Z k (List.ofFn zs) = true).card =
      ((univ.filter fun z : Fin Z → Bool => acc (List.ofFn z) = true).card).choose k := by
  classical
  set A := univ.filter fun z : Fin Z → Bool => acc (List.ofFn z) = true with hA
  set P := SubsetBlockPred acc (Z := Z) hk with hP
  rw [show (univ.filter fun zs : Fin (K * Z) → Bool => subsetTest acc K Z k (List.ofFn zs) = true)
      = univ.filter fun zs => P (BitString.blocksEquiv zs) by
    simp only [subsetTest_ofFn_iff _ hk, hP]]
  rw [show (univ.filter fun zs : Fin (K * Z) → Bool => P (BitString.blocksEquiv zs)).card =
      (univ.filter P).card from card_equiv BitString.blocksEquiv
        (fun v => by simp only [mem_filter, mem_univ, true_and])]
  -- restricting to the first `k` blocks
  have hrestrict : (univ.filter P).card = (univ.filter fun g : Fin k → Lex (Fin Z → Bool) =>
      StrictMono g ∧ ∀ i, g i ∈ A.map toLex.toEmbedding).card := by
    refine card_bij (fun t _ i => toLex (t (Fin.castLE hk i))) ?_ ?_ ?_
    · intro t ht
      simp only [mem_filter, mem_univ, true_and, hP, SubsetBlockPred] at ht ⊢
      refine ⟨strictMono_of_lt_succ fun i hi => ht.2 i hi, fun i => ?_⟩
      rw [mem_map]
      exact ⟨_, by rw [hA, mem_filter]; exact ⟨mem_univ _, (ht.1 _).1 i.2⟩, rfl⟩
    · intro t ht t' ht' h
      simp only [mem_filter, mem_univ, true_and, hP, SubsetBlockPred] at ht ht'
      funext j
      by_cases hj : (j : ℕ) < k
      · exact toLex.injective (congrFun h ⟨j, hj⟩)
      · rw [(ht.1 j).2 (by omega), (ht'.1 j).2 (by omega)]
    · intro g hg
      simp only [mem_filter, mem_univ, true_and] at hg
      refine ⟨fun j => if h : (j : ℕ) < k then ofLex (g ⟨j, h⟩) else 0, ?_,
        funext fun i => by simp [i.2]⟩
      simp only [mem_filter, mem_univ, true_and, hP, SubsetBlockPred]
      refine ⟨fun j => ⟨fun hj => ?_, fun hj => by simp [show ¬(j : ℕ) < k by omega]⟩,
        fun i hi => ?_⟩
      · obtain ⟨z, hz, hzg⟩ := mem_map.1 (hg.2 ⟨j, hj⟩)
        simp only [hj, ↓reduceDIte, ← hzg]
        simpa [hA] using hz
      · simp only [show i < k by omega, hi, dite_true]
        exact hg.1 (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
  rw [hrestrict, card_filter_strictMono, card_map]

variable {α : Type} {enc : α ↪ List Bool}

/-- **Binomial coefficients of #P counts are in #P** [Beigel and Gill,
Property 8(ii)][BeigelGill1992]. If `f` is in `#P` with certificate length `q(|a|)` and `g` is
computed in polynomial time in unary, the new certificate consists of `g a` rows of `q(|a|)` bits:
accepted certificates of the original verifier in strictly increasing lexicographic order. -/
theorem choose_mem {f g : α → ℕ} (hf : f ∈ SharpP enc)
    (hg : ComputableInPolyTime g enc encUnary) :
    (fun a => (f a).choose (g a)) ∈ SharpP enc := by
  obtain ⟨q, V, hV, hf⟩ := mem_SharpP.mp hf
  let Z : α → ℕ := fun a => q.eval (enc a).length
  have hZ : ComputableInPolyTime Z enc encUnary := by dsimp [Z]; fun_prop
  have hW : ComputableInPolyTime
      (fun x : α × List Bool => subsetTest (fun w => V (x.1, w)) (g x.1) (Z x.1) (g x.1) x.2)
      (encPair enc encBits) encBool := by
    fun_prop
  convert mem_SharpP_of_polyTime_length hW (ComputableInPolyTime.unary_mul.comp (hg.prod hZ))
    using 1
  ext a
  change _ = acceptCount _ a (g a * Z a)
  rw [hf a]
  exact (card_filter_subsetTest (fun w => V (a, w)) (Z a) le_rfl).symm

end Cslib.Complexity.SharpP
