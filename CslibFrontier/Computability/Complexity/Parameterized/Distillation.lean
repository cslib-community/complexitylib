/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Advice
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Combinatorics.TupleCover
import CslibFrontier.Foundations.Data.BitString.ShortWords
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import Cslib.Foundations.Data.Polynomial.Monotone
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.List.OfFn

/-!
# OR-distillation and `coNP ⊆ NP/poly`

A *weak OR-distillation* of a problem `A` into a problem `B`
[BodlaenderJansenKratsch2014, Definition 4] (`Cslib.Complexity.IsORDistillation`) maps a nonempty
list of instances of `A`, in polynomial time, to one instance of `B` that is a yes-instance exactly
when some entry of the list is, and whose length is bounded by a polynomially bounded function of
the largest length of an entry, whatever the length of the list. Fortnow and Santhanam proved that
no `NP`-hard problem has one unless `coNP ⊆ NP/poly`: this is the `NP ⊆ coNP/poly` conclusion of
[BodlaenderJansenKratsch2014, Theorem 2] (`Cslib.Complexity.coNP_subset_NPPoly_of_orDistillation`,
with `Cslib.Complexity.NPPoly`). Its other conclusion, the collapse of the polynomial hierarchy to
its third level by Yap's theorem, is not formalized here.

The proof is a counting argument. Fix a length `n`, and compress lists of `t(n)` no-instances of
length `n` to words shorter than `t(n)`. Fewer than `2 ^ t(n)` such words exist, so
`⌊log₂ 2 ^ n⌋ + 1 = n + 1` of them cover all no-instances of length `n`: each no-instance is an
entry of a list compressed to one of them (`Finset.exists_tupleCover`). These words are the advice.
To certify that `a` is a no-instance, a verifier guesses a list containing `a` and checks that it is
compressed to an advice word; then every entry is a no-instance, as the advice word is the image of
a list of no-instances, and the OR property applies to both lists.

The theorem is proved here in the class-wise form underlying the cross-composition framework of
Bodlaender, Jansen and Kratsch [BodlaenderJansenKratsch2014, Section 3]. The lists are restricted to
pairwise equivalent instances, for an equivalence relation that is decidable in polynomial time and
splits the instances up to any length `n` into polynomially many classes in `n`
(`Cslib.Complexity.IsPolyEquivalence`, [BodlaenderJansenKratsch2014, Definition 8]). The OR
property is required only for nonempty lists of equivalent instances, and compression to fewer than
`t(n)` bits only for lists of exactly `t(n)` equivalent instances of length exactly `n`
(`Cslib.Complexity.compl_mem_NPPoly_of_orCompression`). The advice covers each of the
polynomially many classes separately, as in the proof of [BodlaenderJansenKratsch2014, Theorem 6].
Taking the relation relating all instances recovers the OR-distillation theorem
(`Cslib.Complexity.IsORDistillation.compl_mem_NPPoly`).

The core theorem needs a decoder for the encoding of instances (`Turing.MultiTapeTM.Decoder`), to
parse the list of instances in a certificate. The corollaries for `NP`-hard problems need none:
they transfer the hypotheses along a reduction from `SAT`
(`Cslib.Complexity.CookLevin.SAT_npComplete`), whose formulas have a decoder, and the relation
along the reduction (`Cslib.Complexity.IsPolyEquivalence.comap`). Equality of a key computed in
polynomial time with unary output, such as a number of vertices, is a polynomial equivalence
relation (`Cslib.Complexity.IsPolyEquivalence.of_key`).

The distillation is computed in time polynomial in the length `t + 2 (|x₁| + ⋯ + |xₜ|)` of the
encoded list `[x₁, …, xₜ]` (`Turing.MultiTapeTM.encList`, `Turing.MultiTapeTM.length_encList`);
[BodlaenderJansenKratsch2014, Definition 4] bounds the time by a polynomial in `∑ |xᵢ|`. A bound
polynomial in `∑ |xᵢ|` is also polynomial in the encoded length, so the time hypothesis here is
weaker, and the theorem correspondingly stronger; the two agree up to the polynomial when no
instance has the empty encoding, as then `t ≤ ∑ |xᵢ|`. The OR property and the length bound are
required only for nonempty lists, as Definition 4 concerns `t ≥ 1` instances.

## Main definitions

* `Cslib.Complexity.IsPolyEquivalence`: a polynomial equivalence relation.
* `Cslib.Complexity.IsORDistillation`: a weak OR-distillation.

## Main results

* `Cslib.Complexity.compl_mem_NPPoly_of_orCompression`: compressing lists of equivalent instances
  puts the complement in `NP/poly`.
* `Cslib.Complexity.IsORDistillation.compl_mem_NPPoly`: the complement of a problem with an
  OR-distillation is in `NP/poly`.
* `Cslib.Complexity.coNP_subset_NPPoly_of_orCompression`,
  `Cslib.Complexity.coNP_subset_NPPoly_of_orDistillation`,
  `Cslib.Complexity.NP_subset_coNPPoly_of_orDistillation`: **Fortnow–Santhanam**: if an `NP`-hard
  problem has an OR-distillation, then `coNP ⊆ NP/poly`, equivalently `NP ⊆ coNP/poly`.

## References

* [H. L. Bodlaender, B. M. P. Jansen, S. Kratsch, *Kernelization lower bounds by
  cross-composition*][BodlaenderJansenKratsch2014]
* [L. Fortnow, R. Santhanam, *Infeasibility of instance compression and succinct PCPs for
  NP*][FortnowSanthanam2011]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Finset

/-! ### Polynomial equivalence relations -/

section Defs

variable {α β : Type}

/-- `r` is a *polynomial equivalence relation* on the instances encoded by `enc`
[BodlaenderJansenKratsch2014, Definition 8]: an equivalence relation, decidable in polynomial time,
such that for some polynomially bounded `c`, the instances whose encodings have length at most `n`
meet at most `c n` classes, given by representatives `T`. -/
structure IsPolyEquivalence (enc : α ↪ List Bool) (r : α × α → Bool) : Prop where
  /-- `r` is an equivalence relation. -/
  equivalence : Equivalence fun a b => r (a, b) = true
  /-- `r` is decidable in polynomial time. -/
  polyTime : ComputableInPolyTime r (encPair enc enc) encBool
  /-- The instances up to any length meet polynomially many classes. -/
  classes : ∃ c : ℕ → ℕ, PolynomiallyBounded c ∧ ∀ n, ∃ T : Finset α, #T ≤ c n ∧
    ∀ a, (enc a).length ≤ n → ∃ z ∈ T, r (z, a) = true

/-- `f` is a *weak OR-distillation* of `A` into `B` with size bound `s`
[BodlaenderJansenKratsch2014, Definition 4]: it maps lists of instances of `A` in polynomial time to
instances of `B`, such that for every nonempty list `l`, `f l ∈ B` exactly when some entry of `l`
is in `A`, and the output has length at most `s n` when every entry has length at most `n`. The
value of `f` on the empty list is unconstrained. -/
structure IsORDistillation (encA : α ↪ List Bool) (encB : β ↪ List Bool) (A : Set α) (B : Set β)
    (f : List α → β) (s : ℕ → ℕ) : Prop where
  /-- The distillation is computable in polynomial time. -/
  polyTime : ComputableInPolyTime f (encList encA) encB
  /-- On a nonempty list, the output is a yes-instance exactly when some entry is. -/
  mem_iff : ∀ l, l ≠ [] → (f l ∈ B ↔ ∃ a ∈ l, a ∈ A)
  /-- On a nonempty list, the output length is bounded by a function of the largest length of an
  entry. -/
  length_le : ∀ n l, l ≠ [] → (∀ a ∈ l, (encA a).length ≤ n) → (encB (f l)).length ≤ s n

end Defs

variable {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- The relation relating all instances is a polynomial equivalence relation, with one class. -/
theorem isPolyEquivalence_const_true (enc : α ↪ List Bool) :
    IsPolyEquivalence enc fun _ => true := by
  refine ⟨⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩, const true, fun _ => 1, by fun_prop,
    fun n => ?_⟩
  rcases isEmpty_or_nonempty α with hα | ⟨⟨z⟩⟩
  · exact ⟨∅, by simp, fun a => isEmptyElim a⟩
  · exact ⟨{z}, by simp, fun _ _ => ⟨z, mem_singleton_self z, rfl⟩⟩

/-- **Pulling back a polynomial equivalence relation** along a polynomial-time map `g` gives a
polynomial equivalence relation: `a` and `b` are related when `g a` and `g b` are. -/
theorem IsPolyEquivalence.comap {encC : β ↪ List Bool} {r : β × β → Bool}
    (hr : IsPolyEquivalence encC r) {g : α → β} (hg : ComputableInPolyTime g enc encC) :
    IsPolyEquivalence enc fun p => r (g p.1, g p.2) := by
  classical
  obtain ⟨c, hc, hT⟩ := hr.classes
  obtain ⟨q, hq⟩ := ((encoding_length encC).comp hg).polyBounded.exists_polynomial
  refine ⟨⟨fun a => hr.equivalence.refl _, fun h => hr.equivalence.symm h,
    fun h h' => hr.equivalence.trans h h'⟩,
    hr.polyTime.comp ((hg.comp (fst enc enc)).prod (hg.comp (snd enc enc))),
    fun n => c (q.eval n), by fun_prop, fun n => ?_⟩
  obtain ⟨T, hTc, hTr⟩ := hT (q.eval n)
  -- the classes met by images of instances up to length `n`, each with a chosen preimage
  let P : β → Prop := fun z => ∃ y, (enc y).length ≤ n ∧ r (z, g y) = true
  refine ⟨(T.filter P).attach.image fun z => (mem_filter.1 z.2).2.choose,
    card_image_le.trans (card_attach.trans_le ((card_filter_le _ _).trans hTc)),
    fun a ha => ?_⟩
  obtain ⟨z, hzT, hz⟩ := hTr (g a) ((hq a).trans (q.eval_mono ha))
  have hPz : P z := ⟨a, ha, hz⟩
  refine ⟨hPz.choose, mem_image.2 ⟨⟨z, mem_filter.2 ⟨hzT, hPz⟩⟩, mem_attach _ _, rfl⟩, ?_⟩
  exact hr.equivalence.trans (hr.equivalence.symm hPz.choose_spec.2) hz

/-- Equality of unary numbers is a polynomial equivalence relation, with the `n + 1` classes of the
numbers `m ≤ n` up to length `n`. -/
theorem isPolyEquivalence_eq_unary :
    IsPolyEquivalence encUnary fun p : ℕ × ℕ => decide (p.1 = p.2) := by
  refine ⟨⟨fun _ => decide_eq_true rfl, fun h => decide_eq_true (of_decide_eq_true h).symm,
    fun h h' => decide_eq_true ((of_decide_eq_true h).trans (of_decide_eq_true h'))⟩,
    decide_eq' (fst _ _) (snd _ _), fun n => n + 1, by fun_prop, fun n => ?_⟩
  refine ⟨range (n + 1), (card_range _).le, fun a ha => ⟨a, ?_, decide_eq_true rfl⟩⟩
  rw [encUnary_apply, List.length_replicate] at ha
  exact mem_range.2 (Nat.lt_succ_of_le ha)

/-- **Equal keys** form a polynomial equivalence relation, for a key computable in polynomial time
with unary output: instances are related when they have the same key. -/
theorem IsPolyEquivalence.of_key {key : α → ℕ} (hkey : ComputableInPolyTime key enc encUnary) :
    IsPolyEquivalence enc fun p => decide (key p.1 = key p.2) :=
  isPolyEquivalence_eq_unary.comap hkey

/-! ### The advice -/

/-- **The advice for one length.** Let lists of `t n` pairwise `r`-related instances of length `n`
be compressed by `f` to words shorter than `t n`, and let every instance of length `n` be related to
one of the representatives `T`. Then a set `S` of at most `#T * (n + 1)` words shorter than `t n`
covers the no-instances of length `n`: each is an entry of a list of `t n` related no-instances of
length `n` compressed into `S`, and each word in `S` is the compression of a nonempty list of
related no-instances. -/
private theorem exists_orCompression_advice {r : α × α → Bool}
    (hr : Equivalence fun a b => r (a, b) = true) (f : List α → β) (t : ℕ → ℕ) (n : ℕ)
    (hshort : ∀ l : List α, l.length = t n → (∀ a ∈ l, (enc a).length = n) →
      (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) → (encB (f l)).length < t n)
    (T : Finset α) (hT : ∀ a, (enc a).length ≤ n → ∃ z ∈ T, r (z, a) = true) :
    ∃ S : Finset (List Bool), #S ≤ #T * (n + 1) ∧ (∀ w ∈ S, w.length < t n) ∧
      (∀ a, a ∉ A → (enc a).length = n → ∃ l : List α, a ∈ l ∧ (∀ b ∈ l, r (a, b) = true) ∧
        encB (f l) ∈ S ∧ (encList enc l).length ≤ t n * (2 * n + 1)) ∧
      (∀ w ∈ S, ∃ l : List α, l ≠ [] ∧ (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) ∧
        (∀ a ∈ l, a ∉ A) ∧ encB (f l) = w) := by
  classical
  -- the instances of length `n`, and the no-instances among them related to `z`
  let I : Finset α := (BitString.shortWords n).preimage enc enc.injective.injOn
  have hI : #I < 2 ^ (n + 1) := by
    refine lt_of_le_of_lt (card_le_card_of_injOn enc (fun a ha => mem_preimage.1 ha)
      enc.injective.injOn) (BitString.card_shortWords_lt n)
  let R : α → Finset α := fun z => I.filter fun a => (enc a).length = n ∧ a ∉ A ∧ r (z, a) = true
  have hR (z a : α) : a ∈ R z ↔ (enc a).length = n ∧ a ∉ A ∧ r (z, a) = true := by
    simp only [R, I, mem_filter, mem_preimage, BitString.mem_shortWords, and_iff_right_iff_imp]
    exact fun h => h.1.le
  have hlog (z : α) : Nat.log 2 #(R z) ≤ n := by
    have hlt : #(R z) < 2 ^ (n + 1) := (card_filter_le _ _).trans_lt hI
    rcases Nat.eq_zero_or_pos #(R z) with h0 | hpos
    · rw [h0, Nat.log_zero_right]
      exact Nat.zero_le _
    · exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hpos.ne' hlt)
  -- compress a tuple of instances
  let F : (Fin (t n) → α) → List Bool := fun g => encB (f (List.ofFn g))
  have hpair (z : α) (g : Fin (t n) → α) (hg : ∀ i, g i ∈ R z) :
      ∀ a ∈ List.ofFn g, ∀ b ∈ List.ofFn g, r (a, b) = true := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
    exact hr.trans (hr.symm ((hR z _).1 (hg i)).2.2) ((hR z _).1 (hg j)).2.2
  have hFshort (z : α) (g : Fin (t n) → α) (hg : ∀ i, g i ∈ R z) : (F g).length < t n := by
    refine hshort _ (List.length_ofFn) (fun a ha => ?_) (hpair z g hg)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    exact ((hR z _).1 (hg i)).1
  have htpos : 0 < t n := by
    by_contra h0
    have h0 : t n = 0 := by omega
    have := hshort [] (by simp [h0]) (by simp) (by simp)
    omega
  -- the compressions of tuples of related no-instances are fewer than `2 ^ t n` words
  let Y : α → Finset (List Bool) := fun z => (Fintype.piFinset fun _ => R z).image F
  have hY (z : α) : #(Y z) < 2 ^ t n := by
    have hsub : Y z ⊆ BitString.shortWords (t n - 1) := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := mem_image.1 hw
      have := hFshort z g (Fintype.mem_piFinset.1 hg)
      rw [BitString.mem_shortWords]
      omega
    have := (card_le_card hsub).trans_lt (BitString.card_shortWords_lt (t n - 1))
    rwa [Nat.sub_add_cancel htpos] at this
  have hcover (z : α) : ∃ S ⊆ Y z, #S ≤ n + 1 ∧
      ∀ a ∈ R z, ∃ g : Fin (t n) → α, (∀ i, g i ∈ R z) ∧ a ∈ Set.range g ∧ F g ∈ S := by
    obtain ⟨S, hSY, hScard, hScov⟩ := exists_tupleCover F (Y z) (hY z) (R z)
      fun g hg => mem_image.2 ⟨g, Fintype.mem_piFinset.2 hg, rfl⟩
    exact ⟨S, hSY, hScard.trans (by have := hlog z; omega), hScov⟩
  choose S' hS'Y hS'card hS'cov using hcover
  refine ⟨T.biUnion S', ?_, fun w hw => ?_, fun a ha han => ?_, fun w hw => ?_⟩
  · refine card_biUnion_le.trans ?_
    simpa using sum_le_card_nsmul T (fun z => #(S' z)) (n + 1) fun z _ => hS'card z
  · obtain ⟨z, -, hwz⟩ := mem_biUnion.1 hw
    obtain ⟨g, hg, rfl⟩ := mem_image.1 (hS'Y z hwz)
    exact hFshort z g (Fintype.mem_piFinset.1 hg)
  · obtain ⟨z, hzT, hz⟩ := hT a han.le
    obtain ⟨g, hg, ⟨i, hi⟩, hgS⟩ := hS'cov z a ((hR z a).2 ⟨han, ha, hz⟩)
    refine ⟨List.ofFn g, List.mem_ofFn.2 ⟨i, hi⟩, fun b hb => ?_,
      mem_biUnion.2 ⟨z, hzT, hgS⟩, ?_⟩
    · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hb
      exact hr.trans (hr.symm hz) ((hR z _).1 (hg j)).2.2
    · rw [length_encList]
      have := List.sum_le_length_nsmul ((List.ofFn g).map fun b => 2 * (enc b).length + 1)
        (2 * n + 1) (by
          simp only [List.mem_map, List.mem_ofFn]
          rintro _ ⟨b, ⟨j, rfl⟩, rfl⟩
          rw [((hR z _).1 (hg j)).1])
      simpa using this
  · obtain ⟨z, -, hwz⟩ := mem_biUnion.1 hw
    obtain ⟨g, hg, rfl⟩ := mem_image.1 (hS'Y z hwz)
    have hg' := Fintype.mem_piFinset.1 hg
    refine ⟨List.ofFn g, fun h => by rw [List.ofFn_eq_nil_iff] at h; omega, hpair z g hg',
      fun a ha => ?_, rfl⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    exact ((hR z _).1 (hg' i)).2.1

/-! ### The theorem of Fortnow and Santhanam -/

/-- **Compressing lists of equivalent instances puts the complement in `NP/poly`**, in the
class-wise form of [BodlaenderJansenKratsch2014, Theorem 6] of the theorem of Fortnow and Santhanam
(the `NP ⊆ coNP/poly` conclusion of [BodlaenderJansenKratsch2014, Theorem 2]). Let `r` be a
polynomial equivalence relation, and let
`f : List α → β` be computable in polynomial time, with `f l ∈ B` exactly when some entry of `l` is
in `A` for every nonempty list `l` of pairwise related instances. If, for a polynomially bounded
`t`, every list of `t n` pairwise related instances of length `n` is mapped to an instance of `B`
of length less than `t n`, then the complement of `A` is in `NP/poly`. The decoder `D` parses the
lists of instances in certificates. -/
theorem compl_mem_NPPoly_of_orCompression (D : Decoder enc) {r : α × α → Bool}
    (hr : IsPolyEquivalence enc r) {f : List α → β}
    (hf : ComputableInPolyTime f (encList enc) encB)
    (hOR : ∀ l : List α, l ≠ [] → (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) →
      (f l ∈ B ↔ ∃ a ∈ l, a ∈ A))
    {t : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hshort : ∀ n (l : List α), l.length = t n → (∀ a ∈ l, (enc a).length = n) →
      (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) → (encB (f l)).length < t n) :
    Aᶜ ∈ NPPoly enc := by
  classical
  obtain ⟨c, hc, hT⟩ := hr.classes
  choose T hTc hT using hT
  choose S hScard hSshort hScomplete hSsound using fun n =>
    exists_orCompression_advice (A := A) hr.equivalence f t n (hshort n) (T n) (hT n)
  obtain ⟨Q, hQ⟩ := (PolyBounded.of_polynomiallyBounded id
    (show PolynomiallyBounded fun n => t n * (2 * n + 1) by fun_prop)).exists_polynomial
  let adv : ℕ → List Bool := fun n => encList encBits (S n).toList
  let D' := Decoder.list Decoder.bits
  -- the verifier checks a list containing the instance, of related instances, compressed to an
  -- advice word, and not too long
  let check : (List Bool × α) × List α → Bool := fun p =>
    decide (p.1.2 ∈ p.2) && p.2.all (fun b => r (p.1.2, b)) &&
      decide (encB (f p.2) ∈ D'.decode p.1.1) &&
      decide ((encList enc p.2).length ≤ Q.eval (enc p.1.2).length)
  have hcheck : ComputableInPolyTime check (encPair (encPair encBits enc) (encList enc))
      encBool := by
    have hx : ComputableInPolyTime (fun p : (List Bool × α) × List α => p.1.2)
        (encPair (encPair encBits enc) (encList enc)) enc := (fst _ _).snd'
    have hl : ComputableInPolyTime (fun p : (List Bool × α) × List α => p.2)
        (encPair (encPair encBits enc) (encList enc)) (encList enc) := snd _ _
    have hw : ComputableInPolyTime (fun p : (List Bool × α) × List α => p.1.1)
        (encPair (encPair encBits enc) (encList enc)) encBits := (fst _ _).fst'
    refine bool_and' (bool_and' (bool_and' (decide_mem hl hx) ?_) ?_) ?_
    · exact allWithInput hl (hr.polyTime.comp ((hx.comp (fst _ enc)).prod (snd _ enc)))
    · exact decide_mem (D'.computableInPolyTime.comp hw)
        (of_enc_eq (hf.comp hl) fun _ => rfl)
    · exact unary_le' ((encoding_length (encList enc)).comp hl)
        ((unary_eval Q).comp ((encoding_length enc).comp hx))
  have hNP : {x : List Bool × α | ∃ l, check (x, l) = true} ∈ NP (encPair encBits enc) := by
    refine mem_NP_of_witness (p := Q) (R := fun x l => check (x, l) = true) (Decoder.list D) hcheck
      (fun _ _ => Iff.rfl) fun x l hl => ⟨l, hl, ?_⟩
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hl
    exact hl.2.trans (Q.eval_mono (length_le_encPair_right _ _ _))
  refine ⟨adv, ?_, _, hNP, fun a => ?_⟩
  · refine PolynomiallyBounded.mono_of_le (g := fun n => c n * (n + 1) * (2 * t n + 1))
      (by fun_prop) fun n => ?_
    simp only [adv, length_encList, encBits_apply]
    have hsum := List.sum_le_length_nsmul ((S n).toList.map fun w => 2 * w.length + 1)
      (2 * t n + 1) (by
        simp only [List.mem_map, Finset.mem_toList]
        rintro _ ⟨w, hw, rfl⟩
        have := hSshort n w hw
        omega)
    rw [List.length_map, Finset.length_toList, smul_eq_mul] at hsum
    exact hsum.trans (Nat.mul_le_mul_right _ ((hScard n).trans (Nat.mul_le_mul_right _ (hTc n))))
  · have hdec : D'.decode (adv (enc a).length) = (S (enc a).length).toList := D'.decode_enc _
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, check, hdec, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, Finset.mem_toList]
    constructor
    · intro ha
      obtain ⟨l, hal, hrel, hS, hlen⟩ := hScomplete (enc a).length a ha rfl
      exact ⟨l, ⟨⟨hal, hrel⟩, hS⟩, hlen.trans (hQ (enc a).length)⟩
    · rintro ⟨l, ⟨⟨hal, hrel⟩, hS⟩, -⟩ haA
      obtain ⟨l', hl'ne, hl'rel, hl'A, hl'f⟩ := hSsound _ _ hS
      have hfl : f l' = f l := encB.injective hl'f
      have hnot : f l ∉ B := by
        rw [← hfl, hOR l' hl'ne hl'rel]
        rintro ⟨b, hb, hbA⟩
        exact hl'A b hb hbA
      have hpair : ∀ b ∈ l, ∀ b' ∈ l, r (b, b') = true := fun b hb b' hb' =>
        hr.equivalence.trans (hr.equivalence.symm (hrel b hb)) (hrel b' hb')
      exact hnot ((hOR l (List.ne_nil_of_mem hal) hpair).2 ⟨a, hal, haA⟩)

/-- **Fortnow–Santhanam for compressions of equivalent instances**, the `NP ⊆ coNP/poly`
conclusion of [BodlaenderJansenKratsch2014, Theorem 2] in the class-wise form of
[BodlaenderJansenKratsch2014, Theorem 6]: if an `NP`-hard problem `A` has a polynomial-time
map `f` with the OR property on nonempty lists of instances equivalent under a polynomial
equivalence relation `r`, which maps every list of `t n` equivalent instances of length at most `n`
to an instance of length less than `t n`, for a polynomially bounded `t`, then `coNP ⊆ NP/poly`. -/
theorem coNP_subset_NPPoly_of_orCompression (hA : NPHard enc A) {r : α × α → Bool}
    (hr : IsPolyEquivalence enc r) {f : List α → β}
    (hf : ComputableInPolyTime f (encList enc) encB)
    (hOR : ∀ l : List α, l ≠ [] → (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) →
      (f l ∈ B ↔ ∃ a ∈ l, a ∈ A))
    {t : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hshort : ∀ n (l : List α), l.length = t n → (∀ a ∈ l, (enc a).length ≤ n) →
      (∀ a ∈ l, ∀ b ∈ l, r (a, b) = true) → (encB (f l)).length < t n)
    {γ : Type} (encC : γ ↪ List Bool) : coNP encC ⊆ NPPoly encC := by
  obtain ⟨red, hred, hSAT⟩ := hA encCNF SAT CookLevin.SAT_npComplete.1
  obtain ⟨q, hq⟩ := ((encoding_length enc).comp hred).polyBounded.exists_polynomial
  -- transfer everything to `SAT`, whose formulas have a decoder
  have hUNSAT : SATᶜ ∈ NPPoly encCNF := by
    refine compl_mem_NPPoly_of_orCompression (B := B) cnfDecoder (hr.comap hred)
      (hf.comp (ComputableInPolyTime.map hred)) (fun l hl hrel => ?_)
      (t := fun n => t (q.eval n)) (ht.comp (PolynomiallyBounded.polynomial_eval q))
      fun n l hlen hl hrel => ?_
    · rw [Function.comp_apply, hOR (l.map red) (by simpa using hl) (by simpa using hrel)]
      simp only [List.mem_map, exists_exists_and_eq_and, hSAT]
    · exact hshort (q.eval n) (l.map red) (by simpa using hlen)
        (by
          simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
          exact fun a ha => (hq a).trans (q.eval_mono (hl a ha).le))
        (by simpa using hrel)
  intro C hC
  have hred' : PolyTimeReducible encC encCNF Cᶜ SAT := CookLevin.SAT_npComplete.2 encC Cᶜ hC
  simpa using hred'.compl.mem_NPPoly hUNSAT

/-- **OR-distillations put the complement in `NP/poly`**: if `f` is an OR-distillation of `A` with
a polynomially bounded size bound, then the complement of `A` is in `NP/poly`. The decoder `D`
parses the lists of instances in certificates. -/
theorem IsORDistillation.compl_mem_NPPoly (D : Decoder enc) {f : List α → β} {s : ℕ → ℕ}
    (h : IsORDistillation enc encB A B f s) (hs : PolynomiallyBounded s) : Aᶜ ∈ NPPoly enc :=
  compl_mem_NPPoly_of_orCompression D (isPolyEquivalence_const_true enc) h.polyTime
    (fun l hl _ => h.mem_iff l hl) (t := fun n => s n + 1) (by fun_prop)
    fun n l hlen hl _ => Nat.lt_succ_of_le (h.length_le n l (List.ne_nil_of_length_pos
      (by rw [hlen]; exact Nat.succ_pos _)) fun a ha => (hl a ha).le)

/-- **Fortnow–Santhanam**, the `NP ⊆ coNP/poly` conclusion of
[BodlaenderJansenKratsch2014, Theorem 2], stated as `coNP ⊆ NP/poly`: if an `NP`-hard problem has
an OR-distillation into any problem, with a polynomially bounded size bound, then
`coNP ⊆ NP/poly`, for every encoding of instances. The collapse of the polynomial hierarchy that
Theorem 2 derives from it by Yap's theorem is not formalized. -/
theorem coNP_subset_NPPoly_of_orDistillation (hA : NPHard enc A) {f : List α → β} {s : ℕ → ℕ}
    (h : IsORDistillation enc encB A B f s) (hs : PolynomiallyBounded s) {γ : Type}
    (encC : γ ↪ List Bool) : coNP encC ⊆ NPPoly encC :=
  coNP_subset_NPPoly_of_orCompression hA (isPolyEquivalence_const_true enc) h.polyTime
    (fun l hl _ => h.mem_iff l hl) (t := fun n => s n + 1) (by fun_prop)
    (fun n l hlen hl _ => Nat.lt_succ_of_le (h.length_le n l (List.ne_nil_of_length_pos
      (by rw [hlen]; exact Nat.succ_pos _)) hl)) encC

/-- **Fortnow–Santhanam**, the `NP ⊆ coNP/poly` conclusion of
[BodlaenderJansenKratsch2014, Theorem 2]: if an `NP`-hard problem has an OR-distillation into any
problem, with a polynomially bounded size bound, then `NP ⊆ coNP/poly`, for every encoding of
instances. The collapse of the polynomial hierarchy that Theorem 2 derives from it by Yap's theorem
is not formalized. -/
theorem NP_subset_coNPPoly_of_orDistillation (hA : NPHard enc A) {f : List α → β} {s : ℕ → ℕ}
    (h : IsORDistillation enc encB A B f s) (hs : PolynomiallyBounded s) {γ : Type}
    (encC : γ ↪ List Bool) : NP encC ⊆ coNPPoly encC :=
  coNP_subset_NPPoly_iff.1 (coNP_subset_NPPoly_of_orDistillation hA h hs encC)

end Cslib.Complexity
