/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized.Compression
public import CslibFrontier.Computability.Complexity.Parameterized.Distillation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.BitString.ShortWords
import CslibFrontier.Foundations.Data.List.EraseDupsBy
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Cross-composition and kernelization lower bounds

An *OR-cross-composition* of a problem `A` into a parameterized problem `(Q, κ)`
[BodlaenderJansenKratsch2014, Definition 9] (`Cslib.Complexity.IsORCrossComposition`) maps, in
polynomial time, a nonempty list of instances of `A` that are equivalent under a polynomial
equivalence relation (`Cslib.Complexity.IsPolyEquivalence`) to one instance of `Q`, which is a
yes-instance exactly when some entry of the list is, and whose parameter is bounded by a
polynomially bounded function of the largest length of an entry plus the logarithm of the length
of the list. Bodlaender, Jansen and Kratsch showed that if an `NP`-hard problem OR-cross-composes
into `(Q, κ)`, then `(Q, κ)` has no polynomial kernel and no polynomial compression unless
`NP ⊆ coNP/poly` [BodlaenderJansenKratsch2014, Corollary 2]
(`Cslib.Complexity.coNP_subset_NPPoly_of_orCrossComposes`,
`Cslib.Complexity.not_hasPolyKernel_of_orCrossComposes`). Corollary 2 also concludes that the
OR-distillation conjecture fails; that conclusion is not formalized here, and neither is the
collapse of the polynomial hierarchy that follows from `NP ⊆ coNP/poly` by Yap's theorem.

The proof follows [BodlaenderJansenKratsch2014, Theorem 5]. Given a list of instances, keep the
entries related to every entry, and erase repeated entries. On a list of related instances of
length at most `n` nothing is dropped but repeats, and fewer than `2 ^ (n + 1)` distinct instances
remain, so the logarithm of their number is at most `n`. Neither `g` nor `h` is assumed monotone,
so the proof bounds them by monotone polynomial majorants `G m = c_g (m + 1) ^ d_g` of `g` and
`H k = c_h (k + 1) ^ d_h` of `h`. Cross-composing the remaining entries gives a parameter at most
`G (2 n)`, and compressing the result gives a word of length at most `H (G (2 n))`, a polynomial in
`n` independent of the length of the list. (`h (g (2 n))` itself need not bound that length.)
Lists of `t n = H (G (2 n)) + 1` related instances are thus compressed to shorter words, and the
class-wise theorem of Fortnow and Santhanam (`Cslib.Complexity.compl_mem_NPPoly_of_orCompression`,
`Cslib.Complexity.coNP_subset_NPPoly_of_orCompression`) puts the complement of `A` in `NP/poly`.
Theorem 5 builds instead a weak OR-distillation into the OR of the target language, compressing
each equivalence class separately; the class-wise theorem covers the classes directly.

The cross-composition is computed in time polynomial in the length `t + 2 (|x₁| + ⋯ + |xₜ|)` of
the encoded list `[x₁, …, xₜ]`, where Definition 9 bounds it by a polynomial in `∑ |xᵢ|`, and it is
a total map on lists: its value on lists that are empty or not pairwise equivalent is
unconstrained. As for `Cslib.Complexity.IsORDistillation`, the hypothesis here is therefore
weaker, and the theorem stronger. The parameter bound uses `⌊log₂ t⌋`, within one of `log₂ t`, and
holds whenever every entry has length at most `n`; for a monotone bound this is the bound by the
largest length of an entry, and every polynomially bounded function has a monotone polynomially
bounded majorant.

A polynomial compression [BodlaenderJansenKratsch2014, Definition 2]
(`Cslib.Complexity.HasPolyCompression`) runs in time polynomial in `|enc a| + κ a`; polynomial
kernels (`Cslib.Complexity.HasPolyKernel`) and generalized polynomial kernels
[BodlaenderJansenKratsch2014, Definition 1], whose outputs have encoded length bounded by a
polynomial in the parameter, are polynomial compressions.

## Main definitions

* `Cslib.Complexity.IsORCrossComposition`, `Cslib.Complexity.ORCrossComposes`: OR-cross-composition.

## Main results

* `Cslib.Complexity.compl_mem_NPPoly_of_orCrossComposes`: if `A` OR-cross-composes into a
  parameterized problem with a polynomial compression, then the complement of `A` is in `NP/poly`.
* `Cslib.Complexity.coNP_subset_NPPoly_of_orCrossComposes`,
  `Cslib.Complexity.NP_subset_coNPPoly_of_orCrossComposes`: **Bodlaender–Jansen–Kratsch**: if an
  `NP`-hard problem OR-cross-composes into a parameterized problem with a polynomial compression,
  then `coNP ⊆ NP/poly`, equivalently `NP ⊆ coNP/poly`.
* `Cslib.Complexity.not_hasPolyCompression_of_orCrossComposes`,
  `Cslib.Complexity.not_hasPolyKernel_of_orCrossComposes`: the contrapositive, a kernelization
  lower bound under `coNP ⊄ NP/poly`.

## References

* [H. L. Bodlaender, B. M. P. Jansen, S. Kratsch, *Kernelization lower bounds by
  cross-composition*][BodlaenderJansenKratsch2014]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Finset

section Defs

variable {α β : Type}

/-- `C` is an *OR-cross-composition* of `A` into the parameterized problem `(Q, κ)` with respect to
the relation `r`, with parameter bound `g` [BodlaenderJansenKratsch2014, Definition 9]: it maps
lists of instances of `A` to instances of `Q` in polynomial time, such that for every nonempty list
`l` of pairwise related instances, `C l ∈ Q` exactly when some entry of `l` is in `A`, and
`κ (C l) ≤ g (n + ⌊log₂ |l|⌋)` when every entry has length at most `n`. The value of `C` on other
lists is unconstrained. The relation is intended to be a polynomial equivalence relation
(`Cslib.Complexity.IsPolyEquivalence`), as in `Cslib.Complexity.ORCrossComposes`. -/
structure IsORCrossComposition (enc : α ↪ List Bool) (r : α × α → Bool) (A : Set α)
    (encQ : β ↪ List Bool) (κ : β → ℕ) (Q : Set β) (C : List α → β) (g : ℕ → ℕ) : Prop where
  /-- The cross-composition is computable in polynomial time. -/
  polyTime : ComputableInPolyTime C (encList enc) encQ
  /-- On a nonempty list of related instances, the output is a yes-instance exactly when some
  entry is. -/
  mem_iff : ∀ l : List α, l ≠ [] → (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) →
    (C l ∈ Q ↔ ∃ a ∈ l, a ∈ A)
  /-- On a nonempty list of related instances of length at most `n`, the parameter of the output
  is at most `g (n + ⌊log₂ |l|⌋)`. -/
  parameter_le : ∀ n (l : List α), l ≠ [] → (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) →
    (∀ a ∈ l, (enc a).length ≤ n) → κ (C l) ≤ g (n + Nat.log 2 l.length)

/-- `A` *OR-cross-composes* into the parameterized problem `(Q, κ)`
[BodlaenderJansenKratsch2014, Definition 9]: it has an OR-cross-composition into `(Q, κ)` with
respect to a polynomial equivalence relation, with a polynomially bounded parameter bound. -/
@[expose] def ORCrossComposes (enc : α ↪ List Bool) (A : Set α) (encQ : β ↪ List Bool) (κ : β → ℕ)
    (Q : Set β) : Prop :=
  ∃ (r : α × α → Bool) (C : List α → β) (g : ℕ → ℕ), IsPolyEquivalence enc r ∧
    PolynomiallyBounded g ∧ IsORCrossComposition enc r A encQ κ Q C g

end Defs

variable {α β γ : Type} {enc : α ↪ List Bool} {A : Set α} {encQ : β ↪ List Bool} {κ : β → ℕ}
  {Q : Set β}

/-! ### Selecting related instances without repeats -/

/-- The entries of `l` related by `r` to every entry of `l`, without repeats. -/
private def select [DecidableEq α] (r : α × α → Bool) (l : List α) : List α :=
  (l.filter fun a => l.all fun b => r (a, b)).eraseDupsBy fun a b => decide (a = b)

private theorem mem_select [DecidableEq α] {r : α × α → Bool} {l : List α} {a : α} :
    a ∈ select r l ↔ a ∈ l ∧ ∀ b ∈ l, r (a, b) = true := by
  simp only [select, List.mem_eraseDupsBy_eq, List.mem_filter, List.all_eq_true]

/-- The selected entries are pairwise related. -/
private theorem select_pairwise [DecidableEq α] {r : α × α → Bool} (l : List α) :
    ∀ a ∈ select r l, ∀ b ∈ select r l, r (a, b) = true :=
  fun _ ha _ hb => (mem_select.1 ha).2 _ (mem_select.1 hb).1

/-- On a list of pairwise related instances, an instance is selected exactly when it is an entry. -/
private theorem mem_select_of_pairwise [DecidableEq α] {r : α × α → Bool} {l : List α}
    (hl : ∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) {a : α} : a ∈ select r l ↔ a ∈ l :=
  mem_select.trans ⟨And.left, fun ha => ⟨ha, hl a ha⟩⟩

/-- Fewer than `2 ^ (n + 1)` distinct instances have length at most `n`, so the logarithm of the
number of selected entries is at most `n`. -/
private theorem log_length_select_le [DecidableEq α] (r : α × α → Bool) {l : List α} {n : ℕ}
    (hl : ∀ a ∈ l, (enc a).length ≤ n) : Nat.log 2 (select r l).length ≤ n := by
  have hnodup : ((select r l).map enc).Nodup :=
    (List.nodup_eraseDupsBy_eq _).map enc.injective
  have hsub : ((select r l).map enc).toFinset ⊆ BitString.shortWords n := by
    intro w hw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hw)
    exact BitString.mem_shortWords.2 (hl a (mem_select.1 ha).1)
  have hlt : (select r l).length < 2 ^ (n + 1) := by
    have := (card_le_card hsub).trans_lt (BitString.card_shortWords_lt n)
    rwa [List.toFinset_card_of_nodup hnodup, List.length_map] at this
  rcases Nat.eq_zero_or_pos (select r l).length with h0 | hpos
  · rw [h0, Nat.log_zero_right]
    exact Nat.zero_le _
  · exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' hlt)

/-- Selecting related entries without repeats is computable in polynomial time. -/
private theorem select_computableInPolyTime [DecidableEq α] {r : α × α → Bool}
    (hr : ComputableInPolyTime r (encPair enc enc) encBool) :
    ComputableInPolyTime (select r) (encList enc) (encList enc) := by
  have hfilter : ComputableInPolyTime (fun l : List α => l.filter fun a => l.all fun b => r (a, b))
      (encList enc) (encList enc) :=
    filterWithInput id' (allWithInput (fst _ _) (hr.comp ((fst _ _).snd'.prod (snd _ _))))
  exact eraseDupsByWithInput hfilter (decide_eq' ((fst _ _).snd') (snd _ _))

/-! ### From a cross-composition and a compression to an OR-compression -/

/-- **Cross-composing and compressing** [BodlaenderJansenKratsch2014, Theorem 5]: an
OR-cross-composition of `A` into `(Q, κ)` followed by a compression of `(Q, κ)` into `B`, after
selecting the related entries without repeats, maps lists of related instances with the OR
property in polynomial time, and lists of `t n` related instances of length at most `n` to words
shorter than `t n`, for a polynomially bounded `t`. -/
private theorem exists_orCompression_of_orCrossComposition {r : α × α → Bool}
    (hr : IsPolyEquivalence enc r) {C : List α → β} {g : ℕ → ℕ} (hg : PolynomiallyBounded g)
    (hC : IsORCrossComposition enc r A encQ κ Q C g) {encB : γ ↪ List Bool} {B : Set γ}
    {K : β → γ} {h : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hK : IsCompression encQ κ Q encB B K h) :
    ∃ (f : List α → γ) (t : ℕ → ℕ), ComputableInPolyTime f (encList enc) encB ∧
      (∀ l : List α, l ≠ [] → (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) →
        (f l ∈ B ↔ ∃ a ∈ l, a ∈ A)) ∧ PolynomiallyBounded t ∧
      ∀ n (l : List α), l.length = t n → (∀ a ∈ l, (enc a).length ≤ n) →
        (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) → (encB (f l)).length < t n := by
  classical
  obtain ⟨cg, dg, hcg⟩ := polynomiallyBounded_iff_le.mp hg
  obtain ⟨ch, dh, hch⟩ := polynomiallyBounded_iff_le.mp hh
  -- the selected entries form a nonempty list of related instances, on which `C` is bounded
  have hsel_ne {l : List α} (hl : l ≠ []) (hrel : ∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) :
      select r l ≠ [] := by
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l hl
    exact List.ne_nil_of_mem ((mem_select_of_pairwise hrel).2 ha)
  have hpar {n : ℕ} {l : List α} (hne : select r l ≠ []) (hl : ∀ a ∈ l, (enc a).length ≤ n) :
      κ (C (select r l)) ≤ cg * (2 * n + 1) ^ dg := by
    refine (hC.parameter_le n _ hne (select_pairwise l)
      fun a ha => hl a (mem_select.1 ha).1).trans ((hcg _).trans ?_)
    have := log_length_select_le (enc := enc) r hl
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  refine ⟨fun l => K (C (select r l)), fun n => ch * (cg * (2 * n + 1) ^ dg + 1) ^ dh + 1,
    hK.computableInPolyTime_comp (hC.polyTime.comp (select_computableInPolyTime hr.polyTime))
      ?_,
    fun l hl hrel => ?_, by fun_prop, fun n l hlen hl hrel => ?_⟩
  · -- the parameter of the cross-composed instance is polynomially bounded
    have hbound : PolyBounded (fun l : List α => (encList enc l).length)
        fun l => κ (C []) + cg * (2 * (encList enc l).length + 1) ^ dg := by growth_poly
    refine hbound.mono fun l => ?_
    by_cases hne : select r l = []
    · simp only [hne]
      exact Nat.le_add_right _ _
    · exact (hpar hne fun a ha =>
        SizedListEncoding.length_elem_le (encL := encList enc) l a ha).trans
        (Nat.le_add_left _ _)
  · rw [hK.mem_iff, hC.mem_iff _ (hsel_ne hl hrel) (select_pairwise l)]
    simp only [mem_select_of_pairwise hrel]
  · have hne : l ≠ [] := List.ne_nil_of_length_pos (by rw [hlen]; exact Nat.succ_pos _)
    refine Nat.lt_succ_of_le ((hK.length_le _).trans ((hch _).trans ?_))
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by
      have := hpar (hsel_ne hne hrel) hl
      omega) _)

/-! ### The theorem of Bodlaender, Jansen and Kratsch -/

/-- **Cross-composition and compression put the complement in `NP/poly`**: if `A` has an
OR-cross-composition into `(Q, κ)` with respect to a polynomial equivalence relation, with a
polynomially bounded parameter bound, and `(Q, κ)` has a compression into a problem `B` with a
polynomially bounded size bound, then the complement of `A` is in `NP/poly`. The decoder `D`
parses the lists of instances in certificates. -/
theorem IsORCrossComposition.compl_mem_NPPoly (D : Decoder enc) {r : α × α → Bool}
    (hr : IsPolyEquivalence enc r) {C : List α → β} {g : ℕ → ℕ} (hg : PolynomiallyBounded g)
    (hC : IsORCrossComposition enc r A encQ κ Q C g) {encB : γ ↪ List Bool} {B : Set γ}
    {K : β → γ} {h : ℕ → ℕ} (hh : PolynomiallyBounded h)
    (hK : IsCompression encQ κ Q encB B K h) : Aᶜ ∈ NPPoly enc := by
  obtain ⟨f, t, hf, hOR, ht, hshort⟩ :=
    exists_orCompression_of_orCrossComposition hr hg hC hh hK
  exact compl_mem_NPPoly_of_orCompression D hr hf hOR ht
    fun n l hlen hl hrel => hshort n l hlen (fun a ha => (hl a ha).le) hrel

/-- **Cross-composition and polynomial compression put the complement in `NP/poly`**: if `A`
OR-cross-composes into a parameterized problem with a polynomial compression, then the complement
of `A` is in `NP/poly`. The decoder `D` parses the lists of instances in certificates. -/
theorem compl_mem_NPPoly_of_orCrossComposes (D : Decoder enc)
    (hA : ORCrossComposes enc A encQ κ Q) (hQ : HasPolyCompression encQ κ Q) :
    Aᶜ ∈ NPPoly enc :=
  let ⟨_, _, _, hr, hg, hC⟩ := hA
  let ⟨_, _, _, hh, hK⟩ := hQ
  hC.compl_mem_NPPoly D hr hg hh hK

/-- **Bodlaender–Jansen–Kratsch**, the `NP ⊆ coNP/poly` conclusion of
[BodlaenderJansenKratsch2014, Corollary 2], stated as `coNP ⊆ NP/poly`: if an `NP`-hard problem
OR-cross-composes into a parameterized problem with a polynomial compression, then
`coNP ⊆ NP/poly`, for every encoding of instances. The failure of the OR-distillation conjecture,
the other conclusion of Corollary 2, and the collapse of the polynomial hierarchy that follows by
Yap's theorem are not formalized. -/
theorem coNP_subset_NPPoly_of_orCrossComposes (hA : NPHard enc A)
    (hAQ : ORCrossComposes enc A encQ κ Q) (hQ : HasPolyCompression encQ κ Q) {δ : Type}
    (encC : δ ↪ List Bool) : coNP encC ⊆ NPPoly encC := by
  obtain ⟨r, C, g, hr, hg, hC⟩ := hAQ
  obtain ⟨B, K, h, hh, hK⟩ := hQ
  obtain ⟨f, t, hf, hOR, ht, hshort⟩ :=
    exists_orCompression_of_orCrossComposition hr hg hC hh hK
  exact coNP_subset_NPPoly_of_orCompression hA hr hf hOR ht hshort encC

/-- **Bodlaender–Jansen–Kratsch**, the `NP ⊆ coNP/poly` conclusion of
[BodlaenderJansenKratsch2014, Corollary 2]: if an `NP`-hard problem OR-cross-composes into a
parameterized problem with a polynomial compression, then `NP ⊆ coNP/poly`, for every encoding of
instances. -/
theorem NP_subset_coNPPoly_of_orCrossComposes (hA : NPHard enc A)
    (hAQ : ORCrossComposes enc A encQ κ Q) (hQ : HasPolyCompression encQ κ Q) {δ : Type}
    (encC : δ ↪ List Bool) : NP encC ⊆ coNPPoly encC :=
  coNP_subset_NPPoly_iff.1 (coNP_subset_NPPoly_of_orCrossComposes hA hAQ hQ encC)

/-- **Kernelization lower bound by cross-composition** [BodlaenderJansenKratsch2014, Corollary 2]:
if an `NP`-hard problem OR-cross-composes into `(Q, κ)` and `coNP ⊄ NP/poly` for some encoding of
instances, then `(Q, κ)` has no polynomial compression. -/
theorem not_hasPolyCompression_of_orCrossComposes (hA : NPHard enc A)
    (hAQ : ORCrossComposes enc A encQ κ Q) {δ : Type} {encC : δ ↪ List Bool}
    (hcoNP : ¬ coNP encC ⊆ NPPoly encC) : ¬ HasPolyCompression encQ κ Q :=
  fun hQ => hcoNP (coNP_subset_NPPoly_of_orCrossComposes hA hAQ hQ encC)

/-- **Kernelization lower bound by cross-composition** [BodlaenderJansenKratsch2014, Corollary 2]:
if an `NP`-hard problem OR-cross-composes into `(Q, κ)` and `coNP ⊄ NP/poly` for some encoding of
instances, then `(Q, κ)` has no polynomial kernel. -/
theorem not_hasPolyKernel_of_orCrossComposes (hA : NPHard enc A)
    (hAQ : ORCrossComposes enc A encQ κ Q) {δ : Type} {encC : δ ↪ List Bool}
    (hcoNP : ¬ coNP encC ⊆ NPPoly encC) : ¬ HasPolyKernel encQ κ Q :=
  fun hQ => not_hasPolyCompression_of_orCrossComposes hA hAQ hcoNP hQ.hasPolyCompression

end Cslib.Complexity
