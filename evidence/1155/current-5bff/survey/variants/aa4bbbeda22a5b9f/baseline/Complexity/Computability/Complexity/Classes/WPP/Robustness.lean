/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.WPP
public import Complexity.Computability.Complexity.Classes.SharpP.Aggregation
import Complexity.Computability.Complexity.Classes.SharpP.Products
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Foundations.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Polynomial-family robustness of WPP and LWPP

Uniform polynomial-time lists of nonzero binary integers may replace the single accepting
target in WPP and LWPP. The accepting index is existential, with no computability assumption.
For LWPP the list depends only on unary input length. List output size charges both the number
of targets and their bit lengths; fixed finite lists are only a special case.

The interpolation product follows [Hemaspaandra et al., Theorems 3.1 and 3.7]
[HemaspaandraEtAl2018]. We prove its uniform GapP membership by expanding over Boolean subsets:
each term is a polynomial-time product of selected targets times a unary power of the gap.
Thus the proof uses certified word sums and powers, without assuming indexed-product closure.
The two-sided acceptance/rejection-target generalization is proved in `WPP.TwoSided`.
Oracle lowness is a separate result.

The public polynomial-time interfaces use `Turing.MultiTapeTM.ComputableInPolyTime`, following
the plain-statement convention of #456. Private machine-construction lemmas remain tidy.

## Main results

* `GapP.prod_sub_mem`: uniform interpolation products are GapP.
* `mem_WPP_iff_exists_polyTime_targets`, `mem_LWPP_iff_exists_polyTime_targets`:
  full one-sided polynomial-family robustness, stated with target lists.
* `mem_WPP_of_polyTime_targets`, `mem_LWPP_of_polyTime_targets`: list constructors.
* `polyTime_indexedTargets`: plain computability of an indexed target list.
* `mem_WPP_of_indexed_targets`, `mem_LWPP_of_indexed_targets`: indexed-family forms.

## References

* [E. Hemaspaandra, L. A. Hemaspaandra, H. Spakowski, O. Watanabe,
  *The Robustness of LWPP and WPP, with an Application to Graph Reconstruction*]
  [HemaspaandraEtAl2018], Theorems 3.1 and 3.7.
* [S. Fenner, L. Fortnow, S. Kurtz, *Gap-definable counting classes*][FennerFortnowKurtz1994].
-/

@[expose] public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

private def selectedProduct (xs : List ℤ) (w : List Bool) : ℤ :=
  (xs.zipIdx.map fun zi => if w.getD zi.2 false then 1 else zi.1).prod

private theorem selectedProduct_ofFn (xs : List ℤ) (w : Fin xs.length → Bool) :
    selectedProduct xs (List.ofFn w) = ∏ i, if w i then 1 else xs.get i := by
  have he : (xs.zipIdx.map fun zi => if (List.ofFn w).getD zi.2 false then 1 else zi.1) =
      List.ofFn (fun i => if w i then 1 else xs.get i) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp only [List.getElem_map, List.getElem_zipIdx]
      have hi : i < xs.length := by simpa only [List.length_ofFn] using h₂
      simp [List.getD, hi]
  rw [selectedProduct, he, List.prod_ofFn]


private theorem expansion_list (xs : List ℤ) (g : ℤ) :
    (xs.map (fun z => z - g)).prod = ∑ w : Fin xs.length → Bool,
      selectedProduct xs (List.ofFn w) * (-g) ^ (List.ofFn w).countP id := by
  have he : (xs.map (fun z => z - g)).prod = ∏ i, (xs.get i - g * 1) := by
    rw [mul_one, ← List.ofFn_getElem_eq_map xs (fun z => z - g), List.prod_ofFn]
    rfl
  rw [he, prod_sub_mul_eq_sum]
  apply sum_congr rfl
  intro w _
  rw [selectedProduct_ofFn, mul_comm]

private theorem polyTime_selectedProduct {α : Type} {enc : α ↪ List Bool} {f : α → List ℤ}
    (hf : ComputableTidilyInPolyTime f enc (encList encIntBin)) :
    ComputableTidilyInPolyTime (fun x : α × List Bool => selectedProduct (f x.1) x.2)
      (encPair enc encBits) encIntBin := by
  unfold selectedProduct
  apply ComputableTidilyInPolyTime.intBin_prod.comp
  apply ComputableTidilyInPolyTime.mapWithInput
  · exact (ComputableTidilyInPolyTime.zipIdx encIntBin).comp
      (hf.comp (.fst enc encBits))
  · fun_prop


/-- A product of differences between a uniformly computed list of binary FP targets and one GapP
value is GapP. The list length and its total encoded size may depend polynomially on the input. -/
theorem GapP.prod_sub_mem {α : Type} {enc : α ↪ List Bool}
    {f : α → List ℤ} {g : α → ℤ}
    (hf : ComputableInPolyTime f enc (encList encIntBin)) (hg : g ∈ GapP enc) :
    (fun a => ((f a).map (fun z => z - g a)).prod) ∈ GapP enc := by
  have hf := hf.tidy
  have hc := mem_GapP_of_polyTime (.of_tidy (polyTime_selectedProduct hf))
  have hp := GapP.pow_mem_polyTime
    (GapP.comp_mem (GapP.neg_mem hg) (.of_tidy (ComputableTidilyInPolyTime.fst enc encBits)))
    (.of_tidy (show ComputableTidilyInPolyTime (fun x : α × List Bool => x.2.countP id)
      (encPair enc encBits) encUnary by fun_prop))
  have hs := GapP.sum_bits_mem (GapP.mul_mem hc hp)
    (.of_tidy (show ComputableTidilyInPolyTime (fun a => (f a).length) enc encUnary by fun_prop))
  convert hs using 1
  ext a
  rw [expansion_list]
  rfl

private theorem targetWitness {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {f : α → List ℤ} (hg : g ∈ GapP enc)
    (hf : ComputableTidilyInPolyTime f enc (encList encIntBin))
    (hn : ∀ a, (0 : ℤ) ∉ f a)
    (hy : ∀ a, a ∈ A → g a ∈ f a) (hno : ∀ a, a ∉ A → g a = 0) :
    ∃ G ∈ GapP enc, (∀ a, G a = 0 ∨ G a = (f a).prod) ∧
      ∀ a, a ∈ A ↔ G a = (f a).prod := by
  let F : α → ℤ := fun a => (f a).prod
  let P : α → ℤ := fun a => ((f a).map (fun z => z - g a)).prod
  have hF := ComputableTidilyInPolyTime.intBin_prod.comp hf
  have hP := GapP.prod_sub_mem hf.computableInPolyTime hg
  have hFn (a : α) : F a ≠ 0 := List.prod_ne_zero (hn a)
  have hyes (a : α) (ha : a ∈ A) : P a = 0 := by
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨g a, hy a ha, sub_self _⟩
  have hnon (a : α) (ha : a ∉ A) : P a = F a := by
    simp [P, F, hno a ha]
  refine ⟨F - P, GapP.sub_mem' (mem_GapP_of_polyTime (.of_tidy hF)) hP,
    fun a => ?_, fun a => ?_⟩
  · change (F - P) a = 0 ∨ (F - P) a = F a
    by_cases ha : a ∈ A
    · exact Or.inr (by simp [Pi.sub_apply, hyes a ha])
    · exact Or.inl (by simp [Pi.sub_apply, hnon a ha])
  · change a ∈ A ↔ (F - P) a = F a
    by_cases ha : a ∈ A
    · simp [ha, Pi.sub_apply, hyes a ha]
    · simp [ha, Pi.sub_apply, hnon a ha, Ne.symm (hFn a)]


/-- **Polynomial-family robustness of WPP.** A GapP value which is zero on nonmembers and
belongs to a uniformly computed list of nonzero binary integer targets on members witnesses WPP.
The accepting target index need not be computable; the list length may vary with the input. -/
theorem mem_WPP_of_polyTime_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {f : α → List ℤ} (hg : g ∈ GapP enc)
    (hf : ComputableInPolyTime f enc (encList encIntBin))
    (hn : ∀ a, (0 : ℤ) ∉ f a)
    (hy : ∀ a, a ∈ A → g a ∈ f a) (hno : ∀ a, a ∉ A → g a = 0) :
    A ∈ WPP enc := by
  obtain ⟨G, hG, hR, hA⟩ := targetWitness hg hf.tidy hn hy hno
  exact ⟨G, hG, _, .of_tidy (ComputableTidilyInPolyTime.intBin_prod.comp hf.tidy),
    fun a => List.prod_ne_zero (hn a), hR, hA⟩

/-- **Polynomial-family robustness of LWPP.** The target list is uniformly computed from unary
input length. Its length may grow polynomially, and the accepting index is only existential. -/
theorem mem_LWPP_of_polyTime_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {f : ℕ → List ℤ} (hg : g ∈ GapP enc)
    (hf : ComputableInPolyTime f encUnary (encList encIntBin))
    (hn : ∀ n, (0 : ℤ) ∉ f n)
    (hy : ∀ a, a ∈ A → g a ∈ f (enc a).length) (hno : ∀ a, a ∉ A → g a = 0) :
    A ∈ LWPP enc := by
  obtain ⟨G, hG, hR, hA⟩ := targetWitness hg (hf.tidy.comp (.encoding_length enc))
    (fun a => hn (enc a).length) hy hno
  exact ⟨G, hG, fun n => (f n).prod, .of_tidy (ComputableTidilyInPolyTime.intBin_prod.comp hf.tidy),
    fun n => List.prod_ne_zero (hn n), hR, hA⟩

/-- The list of targets `f (a, 0), ..., f (a, r a - 1)` for an indexed target family. -/
def indexedTargets {α : Type} (f : α × ℕ → ℤ) (r : α → ℕ) (a : α) : List ℤ :=
  (List.range (r a)).map fun i => f (a, i)

/-- Uniformly indexed binary integer targets over a unary-computable range form a polynomial-time
target list. -/
theorem polyTime_indexedTargets {α : Type} {enc : α ↪ List Bool} {f : α × ℕ → ℤ}
    {r : α → ℕ} (hf : ComputableInPolyTime f (encPair enc encUnary) encIntBin)
    (hr : ComputableInPolyTime r enc encUnary) :
    ComputableInPolyTime (indexedTargets f r) enc (encList encIntBin) :=
  .of_tidy (ComputableTidilyInPolyTime.mapWithInput
    (ComputableTidilyInPolyTime.range.comp hr.tidy) hf.tidy)

/-- A value matching `f (a, i)` for some `i < r a` belongs to `indexedTargets f r a`. -/
theorem mem_indexedTargets {α : Type} {f : α × ℕ → ℤ} {r : α → ℕ}
    {a : α} {z : ℤ} (h : ∃ i < r a, z = f (a, i)) : z ∈ indexedTargets f r a := by
  obtain ⟨i, hi, he⟩ := h
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, he.symm⟩

/-- Indexed polynomial-family WPP robustness, with a uniform binary-integer target function and
a unary-computable number of targets. Indices run from zero to `r a - 1`; no procedure for
selecting an accepting index is assumed. This includes [Hemaspaandra et al., Theorem 3.7]
[HemaspaandraEtAl2018] by taking `r a` to be a polynomial in encoded input length. -/
theorem mem_WPP_of_indexed_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {f : α × ℕ → ℤ} {r : α → ℕ} (hg : g ∈ GapP enc)
    (hf : ComputableInPolyTime f (encPair enc encUnary) encIntBin)
    (hr : ComputableInPolyTime r enc encUnary)
    (hn : ∀ a i, i < r a → f (a, i) ≠ 0)
    (hy : ∀ a, a ∈ A → ∃ i < r a, g a = f (a, i))
    (hno : ∀ a, a ∉ A → g a = 0) : A ∈ WPP enc := by
  apply mem_WPP_of_polyTime_targets hg (polyTime_indexedTargets hf hr)
  · intro a hz
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
    exact hn a i (List.mem_range.mp hi) he
  · exact fun a ha => mem_indexedTargets (hy a ha)
  · exact hno

/-- Indexed polynomial-family LWPP robustness: both the target family and its size depend only
on unary input length. Zero-based indexing translates the one-based family in
[Hemaspaandra et al., Theorem 3.1][HemaspaandraEtAl2018]. -/
theorem mem_LWPP_of_indexed_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {f : ℕ × ℕ → ℤ} {r : ℕ → ℕ} (hg : g ∈ GapP enc)
    (hf : ComputableInPolyTime f (encPair encUnary encUnary) encIntBin)
    (hr : ComputableInPolyTime r encUnary encUnary)
    (hn : ∀ n i, i < r n → f (n, i) ≠ 0)
    (hy : ∀ a, a ∈ A → ∃ i < r (enc a).length, g a = f ((enc a).length, i))
    (hno : ∀ a, a ∉ A → g a = 0) : A ∈ LWPP enc := by
  apply mem_LWPP_of_polyTime_targets hg (polyTime_indexedTargets hf hr)
  · intro n hz
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
    exact hn n i (List.mem_range.mp hi) he
  · exact fun a ha => mem_indexedTargets (hy a ha)
  · exact hno

/-- **Poly-WPP = WPP**, stated through uniformly computed lists of nonzero binary integer targets.
A polynomial number of targets of polynomial bit length can be computed as one such list,
and a singleton list gives the converse. This is the verifier-based form of
[Hemaspaandra et al., Theorem 3.7][HemaspaandraEtAl2018]. -/
theorem mem_WPP_iff_exists_polyTime_targets {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ WPP enc ↔ ∃ g ∈ GapP enc, ∃ f : α → List ℤ,
      ComputableInPolyTime f enc (encList encIntBin) ∧
      (∀ a, (0 : ℤ) ∉ f a) ∧ (∀ a, a ∈ A → g a ∈ f a) ∧
      ∀ a, a ∉ A → g a = 0 := by
  constructor
  · rw [mem_WPP]
    rintro ⟨g, hg, f, hf, hn, hr, hA⟩
    refine ⟨g, hg, fun a => [f a], by fun_prop, ?_, ?_, ?_⟩
    · intro a
      simpa only [List.mem_singleton] using Ne.symm (hn a)
    · intro a ha
      simpa only [List.mem_singleton] using (hA a).mp ha
    · intro a ha
      exact (hr a).resolve_right (fun h => ha ((hA a).mpr h))
  · rintro ⟨g, hg, f, hf, hn, hy, hno⟩
    exact mem_WPP_of_polyTime_targets hg hf hn hy hno

/-- **Poly-LWPP = LWPP**, with the target list computed from unary input length. This is the
verifier-based form of [Hemaspaandra et al., Theorem 3.1][HemaspaandraEtAl2018]; the accepting
index is not required to be computable. -/
theorem mem_LWPP_iff_exists_polyTime_targets {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ LWPP enc ↔ ∃ g ∈ GapP enc, ∃ f : ℕ → List ℤ,
      ComputableInPolyTime f encUnary (encList encIntBin) ∧
      (∀ n, (0 : ℤ) ∉ f n) ∧ (∀ a, a ∈ A → g a ∈ f (enc a).length) ∧
      ∀ a, a ∉ A → g a = 0 := by
  constructor
  · rw [mem_LWPP]
    rintro ⟨g, hg, f, hf, hn, hr, hA⟩
    refine ⟨g, hg, fun n => [f n], by fun_prop, ?_, ?_, ?_⟩
    · intro n
      simpa only [List.mem_singleton] using Ne.symm (hn n)
    · intro a ha
      simpa only [List.mem_singleton] using (hA a).mp ha
    · intro a ha
      exact (hr a).resolve_right (fun h => ha ((hA a).mpr h))
  · rintro ⟨g, hg, f, hf, hn, hy, hno⟩
    exact mem_LWPP_of_polyTime_targets hg hf hn hy hno

end Cslib.Complexity
