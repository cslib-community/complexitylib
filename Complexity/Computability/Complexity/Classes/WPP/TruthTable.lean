/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.WPP.Robustness
public import Complexity.Computability.Complexity.Classes.SharpP.Products
public import Complexity.Computability.Complexity.Reduction.TruthTable
import Complexity.Computability.Complexity.Classes.SharpP.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Cslib.Foundations.Data.Polynomial.Monotone

/-!
# Truth-table closure of wide-gap classes

For each guessed answer word, multiply the accepting gap on true answers and target minus gap
on false answers. Every incorrect word contributes zero. The correct word contributes the same
nonzero product target, independent of the guessed word. Summing those products selected by an
arbitrary polynomial-time Boolean combiner proves nonadaptive closure.

LWPP first normalizes query lengths by many-one closure. Polynomial-family robustness then
normalizes the possible prefix targets for an input-dependent query count.

## Main results

* `truthTable_mem_WPP`, `truthTable_mem_LWPP`: arbitrary polynomial-time Boolean combinations
  of one jointly uniform family over a computed unary bound.
* `PolyTimeTruthTableReducible.mem_WPP`, `PolyTimeTruthTableReducible.mem_LWPP`:
  closure under polynomial-time truth-table reductions.

## References

The WPP argument is [Spakowski, Thakur and Tripathi, Theorem 5.6(a)][SpakowskiThakurTripathi2005].
The LWPP result is a deduction using the counting algebra of
[Fenner, Fortnow and Kurtz][FennerFortnowKurtz1994] and polynomial-family robustness of
[Hemaspaandra, Hemaspaandra, Spakowski and Watanabe, Theorem 3.1][HemaspaandraEtAl2018].
These are results for the encoded verifier model. They do not prove adaptive WPP closure:
[Spakowski, Thakur and Tripathi, Theorem 5.9][SpakowskiThakurTripathi2005] give a relativized
obstruction to that stronger statement. Their separate UP-oracle containment is not formalized.
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

private def answerGap {α : Type} (g f : α × ℕ → ℤ) (r : α → ℕ)
    (d : α × List Bool → Bool) (a : α) : ℤ :=
  ∑ w : Fin (r a) → Bool, (if d (a, List.ofFn w) then 1 else 0) *
    ∏ i ∈ range (r a), if (List.ofFn w).getD i false then g (a, i) else f (a, i) - g (a, i)

private theorem answerGap_mem {α : Type} {enc : α ↪ List Bool}
    {g f : α × ℕ → ℤ} {r : α → ℕ} {d : α × List Bool → Bool}
    (hg : g ∈ GapP (encPair enc encUnary)) (hf : f ∈ GapP (encPair enc encUnary))
    (hr : ComputableTidilyInPolyTime r enc encUnary)
    (hd : ComputableTidilyInPolyTime d (encPair enc encBits) encBool) :
    answerGap g f r d ∈ GapP enc := by
  let q : (α × List Bool) × ℕ → α × ℕ := fun x => (x.1.1, x.2)
  have hq : ComputableTidilyInPolyTime q
      (encPair (encPair enc encBits) encUnary) (encPair enc encUnary) := by dsimp [q]; fun_prop
  have hs : (fun x : (α × List Bool) × ℕ =>
      if x.1.2.getD x.2 false then g (x.1.1, x.2) else
        f (x.1.1, x.2) - g (x.1.1, x.2)) ∈
      GapP (encPair (encPair enc encBits) encUnary) :=
    GapP.ite_mem (.of_tidy (by fun_prop)) (GapP.comp_mem hg (.of_tidy hq))
      (GapP.comp_mem (GapP.sub_mem' hf hg) (.of_tidy hq))
  have hp := GapP.prod_range_mem hs (.of_tidy (hr.comp (.fst enc encBits)))
  have hw : ComputableTidilyInPolyTime
      (fun x => if d x then (1 : ℤ) else 0) (encPair enc encBits) encIntBin := by fun_prop
  exact GapP.sum_bits_mem (GapP.mul_mem (mem_GapP_of_polyTime (.of_tidy hw)) hp) (.of_tidy hr)

private theorem answerGap_eq {α : Type} {A : Set (α × ℕ)} {g f : α × ℕ → ℤ}
    {r : α → ℕ} {d : α × List Bool → Bool}
    (hR : ∀ x, g x = 0 ∨ g x = f x) (hA : ∀ x, x ∈ A ↔ g x = f x)
    (a : α) :
    answerGap g f r d a = if d (a, truthTableAnswers A r a) then
      ∏ i ∈ range (r a), f (a, i) else 0 := by
  classical
  let v : Fin (r a) → Bool := fun i => decide ((a, i.1) ∈ A)
  have hg (i : Fin (r a)) : g (a, i) = if v i then f (a, i) else 0 := by
    by_cases h : (a, i.1) ∈ A
    · simp [v, h, (hA _).mp h]
    · simp only [v, decide_eq_false h, Bool.false_eq_true, ↓reduceIte]
      exact (hR _).resolve_right (fun he => h ((hA _).mpr he))
  have hp (w : Fin (r a) → Bool) :
      (∏ i ∈ range (r a), if (List.ofFn w).getD i false then g (a, i) else
        f (a, i) - g (a, i)) = if w = v then ∏ i ∈ range (r a), f (a, i) else 0 := by
    rw [← Fin.prod_univ_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left, Fin.isLt,
      Option.getD_some]
    by_cases hw : w = v
    · subst w
      rw [ite_eq_left rfl]
      apply prod_congr rfl
      intro i _
      rw [hg]
      cases v i <;> simp
    · rw [ite_eq_right hw]
      obtain ⟨i, hi⟩ : ∃ i, w i ≠ v i := Function.ne_iff.mp hw
      apply prod_eq_zero (mem_univ i)
      rw [hg]
      cases hw : w i <;> cases hv : v i <;> simp_all
  unfold answerGap
  simp_rw [hp]
  rw [sum_eq_single v]
  · simp only [ite_true, v, truthTableAnswers]
    split_ifs <;> simp_all
  · intro w _ hw
    simp [hw]
  · simp

variable {α : Type} {enc : α ↪ List Bool} {A : Set (α × ℕ)}
  {r : α → ℕ} {d : α × List Bool → Bool}

/-- A jointly WPP family supports any polynomial-time Boolean combination of a computed batch. -/
theorem truthTable_mem_WPP (hA : A ∈ WPP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary)
    (hd : ComputableInPolyTime d (encPair enc encBits) encBool) :
    {a | d (a, truthTableAnswers A r a) = true} ∈ WPP enc := by
  have hr := hr.tidy
  have hd := hd.tidy
  rw [mem_WPP] at hA ⊢
  obtain ⟨g, hg, f, hf, hn, hR, hA⟩ := hA
  have hF (a) : (∏ i ∈ range (r a), f (a, i)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => hn (a, i)
  refine ⟨answerGap g f r d, answerGap_mem hg (mem_GapP_of_polyTime hf) hr hd,
    _, .of_tidy (ComputableTidilyInPolyTime.intBin_prod_range hf.tidy hr), hF, ?_, ?_⟩
  · intro a
    rw [answerGap_eq hR hA]
    split_ifs <;> simp
  · intro a
    change d (a, truthTableAnswers A r a) = true ↔ _
    rw [answerGap_eq hR hA]
    cases hd : d (a, truthTableAnswers A r a) <;> simp [(hF a).symm]

/-- A jointly LWPP family supports any polynomial-time Boolean combination of a computed batch.
Polynomial-family robustness normalizes the prefix target for the input-dependent batch size. -/
theorem truthTable_mem_LWPP (hA : A ∈ LWPP (encPair enc encUnary))
    (hr : ComputableInPolyTime r enc encUnary)
    (hd : ComputableInPolyTime d (encPair enc encBits) encBool) :
    {a | d (a, truthTableAnswers A r a) = true} ∈ LWPP enc := by
  have hr := hr.tidy
  have hd := hd.tidy
  obtain ⟨g, hg, f, hf, hn, hR, hA⟩ := mem_LWPP.mp hA
  let F (x : α × ℕ) := f ((encPair enc encUnary x).length)
  have hF : ComputableTidilyInPolyTime F (encPair enc encUnary) encIntBin :=
    hf.tidy.comp (.encoding_length _)
  have he := answerGap_eq (f := F) (r := r) (d := d) hR hA
  obtain ⟨p, hb⟩ := hr.polyBounded.exists_polynomial
  let T (x : ℕ × ℕ) := ∏ i ∈ range x.2, f (2 * x.1 + 1 + i)
  have hT : ComputableTidilyInPolyTime T (encPair encUnary encUnary) encIntBin := by
    have hf := hf.tidy
    apply ComputableTidilyInPolyTime.intBin_prod_range
      (f := fun x : (ℕ × ℕ) × ℕ => f (2 * x.1.1 + 1 + x.2)) <;> fun_prop
  have hp : ComputableTidilyInPolyTime (fun n => p.eval n + 1) encUnary encUnary := by fun_prop
  apply mem_LWPP_of_indexed_targets (answerGap_mem hg (mem_GapP_of_polyTime (.of_tidy hF)) hr hd)
    hT.computableInPolyTime hp.computableInPolyTime
  · intro n k _
    exact prod_ne_zero_iff.mpr fun i _ => hn _
  · intro a ha
    change d (a, truthTableAnswers A r a) = true at ha
    refine ⟨r a, ?_, ?_⟩
    · exact Nat.lt_succ_of_le (hb a)
    · rw [he, ite_eq_left ha]
      simp [F, T]
  · intro a ha
    change ¬ d (a, truthTableAnswers A r a) = true at ha
    rw [he, ite_eq_right ha]

/-- WPP is closed under polynomial-time truth-table reductions
[Spakowski, Thakur and Tripathi, Theorem 5.6(a)][SpakowskiThakurTripathi2005]. -/
theorem PolyTimeTruthTableReducible.mem_WPP {β : Type} {encB : β ↪ List Bool}
    {L : Set α} {B : Set β} (h : PolyTimeTruthTableReducible enc encB L B)
    (hB : B ∈ WPP encB) : L ∈ WPP enc := by
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := h
  have hqB : q ⁻¹' B ∈ WPP (encPair enc encUnary) :=
    PolyTimeReducible.mem_WPP ⟨q, hq, fun _ => Iff.rfl⟩ hB
  convert truthTable_mem_WPP hqB hr hd using 1
  ext a
  exact hL a

/-- LWPP is closed under polynomial-time truth-table reductions. Many-one closure normalizes
varying query lengths before the joint-family theorem normalizes the query count. This is a
consequence of the LWPP counting algebra; no adaptive-oracle theorem is asserted here. -/
theorem PolyTimeTruthTableReducible.mem_LWPP {β : Type} {encB : β ↪ List Bool}
    {L : Set α} {B : Set β} (h : PolyTimeTruthTableReducible enc encB L B)
    (hB : B ∈ LWPP encB) : L ∈ LWPP enc := by
  obtain ⟨r, q, d, hr, hq, hd, hL⟩ := h
  have hqB : q ⁻¹' B ∈ LWPP (encPair enc encUnary) :=
    PolyTimeReducible.mem_LWPP ⟨q, hq, fun _ => Iff.rfl⟩ hB
  convert truthTable_mem_LWPP hqB hr hd using 1
  ext a
  exact hL a

end Cslib.Complexity
