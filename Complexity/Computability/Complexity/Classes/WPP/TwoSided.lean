/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.WPP.Robustness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Two-sided polynomial-target robustness of WPP and LWPP

Uniform polynomial-time accepting and rejecting target lists preserve WPP and LWPP when
these lists are disjoint at each input, or each natural length for LWPP. Original targets
may be zero, negative or repeated; only cross-family disjointness is required. The target
indices need not be computable. Binary list output charges both counts and bit lengths.

The proof follows [Hemaspaandra et al., Appendix A][HemaspaandraEtAl2018]: take the product
of the differences between rejection targets and the original gap. This vanishes on rejection,
and on acceptance takes one of a uniformly computed family of nonzero products. The uniform
product theorem and one-sided robustness then finish the construction.

The public interfaces ask for `Turing.MultiTapeTM.ComputableInPolyTime` certificates.

## Main results

* `mem_WPP_of_disjoint_targets`, `mem_LWPP_of_disjoint_targets`: two-sided robustness.
* `mem_WPP_of_disjoint_indexed_targets`, `mem_LWPP_of_disjoint_indexed_targets`:
  indexed two-sided robustness.
* `mem_WPP_iff_exists_disjoint_targets`, `mem_LWPP_iff_exists_disjoint_targets`:
  the full two-sided polynomial-family characterizations.

## References

* [E. Hemaspaandra, L. A. Hemaspaandra, H. Spakowski, O. Watanabe,
  *The Robustness of LWPP and WPP, with an Application to Graph Reconstruction*]
  [HemaspaandraEtAl2018], Definition 3.8, Corollary 3.11, Theorem 3.12 and Appendix A
  of the full version (arXiv:1711.01250).
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

private def transformedTargets (yes no : List ℤ) : List ℤ :=
  yes.map fun z => (no.map fun r => r - z).prod

private theorem polyTime_transformedTargets {α : Type} {enc : α ↪ List Bool}
    {yes no : α → List ℤ}
    (hy : ComputableInPolyTime yes enc (encList encIntBin))
    (hn : ComputableInPolyTime no enc (encList encIntBin)) :
    ComputableInPolyTime (fun a => transformedTargets (yes a) (no a))
      enc (encList encIntBin) := by
  unfold transformedTargets
  apply ComputableInPolyTime.mapWithInput hy
  apply (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.intBin_prod).comp
  apply ComputableInPolyTime.mapWithInput (hn.comp (.fst enc encIntBin))
  fun_prop

private theorem transformedTargets_nonzero {yes no : List ℤ} (hd : yes.Disjoint no) :
    (0 : ℤ) ∉ transformedTargets yes no := by
  intro h
  obtain ⟨z, hz, he⟩ := List.mem_map.mp h
  obtain ⟨r, hr, heq⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp he)
  exact List.disjoint_left.mp hd hz (sub_eq_zero.mp heq ▸ hr)

/-- Two-sided WPP robustness for disjoint uniformly computed binary integer target lists.
Neither original list is required to avoid zero; no accepting or rejecting index is computed. -/
theorem mem_WPP_of_disjoint_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {yes no : α → List ℤ} (hg : g ∈ GapP enc)
    (hy : ComputableInPolyTime yes enc (encList encIntBin))
    (hn : ComputableInPolyTime no enc (encList encIntBin))
    (hd : ∀ a, (yes a).Disjoint (no a))
    (hyes : ∀ a, a ∈ A → g a ∈ yes a) (hno : ∀ a, a ∉ A → g a ∈ no a) :
    A ∈ WPP enc := by
  apply mem_WPP_of_polyTime_targets (GapP.prod_sub_mem hn hg)
    (polyTime_transformedTargets hy hn)
    (fun a => transformedTargets_nonzero (hd a))
  · intro a ha
    exact List.mem_map.mpr ⟨g a, hyes a ha, rfl⟩
  · intro a ha
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨g a, hno a ha, sub_self _⟩

/-- Two-sided LWPP robustness with both target lists computed from unary input length.
Disjointness is required at every natural length, including zero. Original zero targets are
allowed on either side, provided the two lists remain disjoint. -/
theorem mem_LWPP_of_disjoint_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {yes no : ℕ → List ℤ} (hg : g ∈ GapP enc)
    (hy : ComputableInPolyTime yes encUnary (encList encIntBin))
    (hn : ComputableInPolyTime no encUnary (encList encIntBin))
    (hd : ∀ n, (yes n).Disjoint (no n))
    (hyes : ∀ a, a ∈ A → g a ∈ yes (enc a).length)
    (hno : ∀ a, a ∉ A → g a ∈ no (enc a).length) : A ∈ LWPP enc := by
  apply mem_LWPP_of_polyTime_targets
    (GapP.prod_sub_mem
      (hn.comp (ComputableInPolyTime.encoding_length enc)) hg)
    (polyTime_transformedTargets hy hn)
    (fun n => transformedTargets_nonzero (hd n))
  · intro a ha
    exact List.mem_map.mpr ⟨g a, hyes a ha, rfl⟩
  · intro a ha
    apply List.prod_eq_zero_iff.mpr
    exact List.mem_map.mpr ⟨g a, hno a ha, sub_self _⟩

private theorem indexedTargets_disjoint {α : Type} {yes no : α × ℕ → ℤ}
    {ry rn : α → ℕ} (a : α)
    (hd : ∀ i < ry a, ∀ j < rn a, yes (a, i) ≠ no (a, j)) :
    (indexedTargets yes ry a).Disjoint (indexedTargets no rn a) := by
  rw [List.disjoint_left]
  intro z hz hn
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hz
  obtain ⟨j, hj, he⟩ := List.mem_map.mp hn
  exact hd i (List.mem_range.mp hi) j (List.mem_range.mp hj) he.symm

/-- Two-sided WPP robustness for uniform indexed families, with each count computed in polynomial
 time with unary output. Disjointness concerns used indices; zero targets are allowed. -/
theorem mem_WPP_of_disjoint_indexed_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {yes no : α × ℕ → ℤ} {ry rn : α → ℕ} (hg : g ∈ GapP enc)
    (hy : ComputableInPolyTime yes (encPair enc encUnary) encIntBin)
    (hn : ComputableInPolyTime no (encPair enc encUnary) encIntBin)
    (hry : ComputableInPolyTime ry enc encUnary)
    (hrn : ComputableInPolyTime rn enc encUnary)
    (hd : ∀ a i, i < ry a → ∀ j, j < rn a → yes (a, i) ≠ no (a, j))
    (hyes : ∀ a, a ∈ A → ∃ i < ry a, g a = yes (a, i))
    (hno : ∀ a, a ∉ A → ∃ j < rn a, g a = no (a, j)) : A ∈ WPP enc :=
  mem_WPP_of_disjoint_targets hg (polyTime_indexedTargets hy hry)
    (polyTime_indexedTargets hn hrn) (fun a => indexedTargets_disjoint a (hd a))
    (fun a ha => mem_indexedTargets (hyes a ha)) (fun a ha => mem_indexedTargets (hno a ha))

/-- Two-sided LWPP robustness for uniform indexed target families depending only on unary length.
Cross-family disjointness holds at all natural lengths and both counts have unary polynomial-time
certificates. The standard positive polynomial-size families are instances. -/
theorem mem_LWPP_of_disjoint_indexed_targets {α : Type} {enc : α ↪ List Bool} {A : Set α}
    {g : α → ℤ} {yes no : ℕ × ℕ → ℤ} {ry rn : ℕ → ℕ} (hg : g ∈ GapP enc)
    (hy : ComputableInPolyTime yes (encPair encUnary encUnary) encIntBin)
    (hn : ComputableInPolyTime no (encPair encUnary encUnary) encIntBin)
    (hry : ComputableInPolyTime ry encUnary encUnary)
    (hrn : ComputableInPolyTime rn encUnary encUnary)
    (hd : ∀ n i, i < ry n → ∀ j, j < rn n → yes (n, i) ≠ no (n, j))
    (hyes : ∀ a, a ∈ A → ∃ i < ry (enc a).length, g a = yes ((enc a).length, i))
    (hno : ∀ a, a ∉ A → ∃ j < rn (enc a).length, g a = no ((enc a).length, j)) :
    A ∈ LWPP enc :=
  mem_LWPP_of_disjoint_targets hg (polyTime_indexedTargets hy hry)
    (polyTime_indexedTargets hn hrn) (fun n => indexedTargets_disjoint n (hd n))
    (fun a ha => mem_indexedTargets (hyes a ha)) (fun a ha => mem_indexedTargets (hno a ha))

/-- **(Poly,Poly)-WPP = WPP**, with disjoint uniformly computed binary integer target lists.
The converse uses singleton acceptance and zero-rejection lists. -/
theorem mem_WPP_iff_exists_disjoint_targets {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ WPP enc ↔ ∃ g ∈ GapP enc, ∃ yes no : α → List ℤ,
      ComputableInPolyTime yes enc (encList encIntBin) ∧
      ComputableInPolyTime no enc (encList encIntBin) ∧
      (∀ a, (yes a).Disjoint (no a)) ∧
      (∀ a, a ∈ A → g a ∈ yes a) ∧ ∀ a, a ∉ A → g a ∈ no a := by
  constructor
  · rw [mem_WPP]
    rintro ⟨g, hg, f, hf, hn, hr, hA⟩
    refine ⟨g, hg, fun a => [f a], fun _ => [0], by fun_prop, .const _, ?_, ?_, ?_⟩
    · intro a
      simpa using Ne.symm (hn a)
    · intro a ha
      simpa only [List.mem_singleton] using (hA a).mp ha
    · intro a ha
      simpa only [List.mem_singleton] using
        (hr a).resolve_right (fun h => ha ((hA a).mpr h))
  · rintro ⟨g, hg, yes, no, hy, hn, hd, hyes, hno⟩
    exact mem_WPP_of_disjoint_targets hg hy hn hd hyes hno

/-- **(Poly,Poly)-LWPP = LWPP**, with disjoint target lists uniformly computed from unary
length, including length zero. This is
[Hemaspaandra et al., Corollary 3.11][HemaspaandraEtAl2018]. -/
theorem mem_LWPP_iff_exists_disjoint_targets {α : Type} {enc : α ↪ List Bool} {A : Set α} :
    A ∈ LWPP enc ↔ ∃ g ∈ GapP enc, ∃ yes no : ℕ → List ℤ,
      ComputableInPolyTime yes encUnary (encList encIntBin) ∧
      ComputableInPolyTime no encUnary (encList encIntBin) ∧
      (∀ n, (yes n).Disjoint (no n)) ∧
      (∀ a, a ∈ A → g a ∈ yes (enc a).length) ∧
      ∀ a, a ∉ A → g a ∈ no (enc a).length := by
  constructor
  · rw [mem_LWPP]
    rintro ⟨g, hg, f, hf, hn, hr, hA⟩
    refine ⟨g, hg, fun n => [f n], fun _ => [0], by fun_prop, .const _, ?_, ?_, ?_⟩
    · intro n
      simpa using Ne.symm (hn n)
    · intro a ha
      simpa only [List.mem_singleton] using (hA a).mp ha
    · intro a ha
      simpa only [List.mem_singleton] using
        (hr a).resolve_right (fun h => ha ((hA a).mpr h))
  · rintro ⟨g, hg, yes, no, hy, hn, hd, hyes, hno⟩
    exact mem_LWPP_of_disjoint_targets hg hy hn hd hyes hno

end Cslib.Complexity
