/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Closure
public import CslibFrontier.Computability.Complexity.Classes.UniformDiagonalization
public import CslibFrontier.Foundations.Data.BitString.Enumeration
import CslibFrontier.Computability.Complexity.Classes.EXP.Decidable
import CslibFrontier.Computability.Complexity.Classes.Immune
import CslibFrontier.Computability.Complexity.Classes.Inclusions
import CslibFrontier.Computability.Complexity.Reduction.Isomorphism.Conjecture
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.TwoPow
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BoundedSearch
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Unpair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partrec
import Mathlib.Data.Set.Finite.List

/-!
# Recursive presentations of polynomial-time degrees and Ladner's density theorem

Ladner proved that polynomial-time many-one reducibility is dense on the decidable problems
outside `P` [Ladner][Ladner1975a], and Schöning derived this density from uniform diagonalization
by recursively presenting polynomial-time degrees [Schöning][Schoening1982].

This module builds an effective enumeration of all polynomial-time transducers
`List Bool → List Bool` (`Cslib.Complexity.Ladner.transducerIndexed`), proves that lower
`≤ₘᵖ`-cones and polynomial-time `m`-degrees (`Cslib.Complexity.polyTimeDegree`) of decidable
problems outside `P` are recursively presentable and closed under finite variations, and deduces
both Ladner's downward theorem and the full Ladner density theorem:

* **Downward theorem** (`Cslib.Complexity.exists_isDecidable_notMem_P_lt`): for every decidable
  `B ∉ P` on bit words, some `G ∈ P` makes `G.ite ∅ B` decidable, outside `P`, and strictly
  `≤ₘᵖ`-below `B`. When `B ∈ NP`, this problem also lies in `NP`
  (`Cslib.Complexity.exists_mem_NP_notMem_P_lt`), so if `P ≠ NP` every `NP`-complete problem on bit
  words has an `NP`-intermediate problem strictly below it
  (`Cslib.Complexity.NPComplete.exists_NP_not_P_not_npComplete_lt`).
* **Full density theorem** (`Cslib.Complexity.exists_isDecidable_between_of_notMem_P`,
  `Cslib.Complexity.exists_mem_NP_between_of_notMem_P`): for any decidable `A, B` on bit words with
  `B ∉ P`, `A ≤ₘᵖ B`, and `¬(B ≤ₘᵖ A)`, there is a decidable `C` (in `NP` when `A, B ∈ NP`)
  strictly between `A` and `B`: `A <ₘᵖ C <ₘᵖ B`.

The hypothesis `B ∉ P` in the full density theorem is necessary: `∅ <ₘᵖ {[true]}`, yet every set
between `∅` and `{[true]}` lies in `P` and has a non-member, so it is either empty or
`≤ₘᵖ`-equivalent to `{[true]}` (checked in `CslibFrontierTests.UniformDiagonalization`).

## Source notes

The printed theorem numbers in [Ladner][Ladner1975a] and [Schöning][Schoening1982] were not
consulted directly; statements are paraphrased in the library's binary-alphabet (`encBits`) and
total native machine (`Turing.MultiTapeTM`) conventions without quotation.

## Main definitions

* `Cslib.Complexity.PolyTimeEquiv`: polynomial-time many-one interreducibility (`≡ₘᵖ`).
* `Cslib.Complexity.polyTimeDegree`: the polynomial-time `m`-degree `{A | A ≡ₘᵖ B}` on bit words.
* `Cslib.Complexity.Ladner.transducerIndexed`: the clocked enumeration of polynomial-time
  transducers on bit words.

## Main results

* `Cslib.Complexity.recursivelyPresentable_polyTimeReducible_le`,
  `Cslib.Complexity.closedUnderFiniteVariation_polyTimeReducible_le`: lower `≤ₘᵖ`-cones of
  decidable nontrivial sets meet Schöning's hypotheses.
* `Cslib.Complexity.PolyTimeComplete.recursivelyPresentable`: a class on bit words closed under
  `≤ₘᵖ` with a decidable `≤ₘᵖ`-complete problem is recursively presentable.
* `Cslib.Complexity.recursivelyPresentable_polyTimeDegree`,
  `Cslib.Complexity.closedUnderFiniteVariation_polyTimeDegree`: the polynomial-time `m`-degree of a
  decidable `B ∉ P` meets Schöning's hypotheses.
* `Cslib.Complexity.exists_mem_P_ite_empty_lt`,
  `Cslib.Complexity.exists_isDecidable_notMem_P_lt`,
  `Cslib.Complexity.exists_mem_NP_notMem_P_lt`,
  `Cslib.Complexity.NPComplete.exists_NP_not_P_not_npComplete_lt`: Ladner's downward theorem and
  `NP`-intermediate sets below arbitrary `NP`-complete languages.
* `Cslib.Complexity.exists_isDecidable_between_of_notMem_P`,
  `Cslib.Complexity.exists_mem_NP_between_of_notMem_P`: Ladner's density theorem for decidable sets
  and within `NP`.

## References

* [R. E. Ladner, *On the Structure of Polynomial Time Reducibility*][Ladner1975a]
* [U. Schöning, *A uniform approach to obtain diagonal sets in complexity
  classes*][Schoening1982]
-/

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableInPolyTime
open scoped symmDiff

public section

namespace Cslib.Complexity

/-! ### Polynomial-time many-one equivalence and degrees -/

/-- Two problems are **polynomial-time many-one equivalent** (`A ≡ₘᵖ B`) when each reduces to the
other in polynomial time. -/
@[expose] def PolyTimeEquiv {α β : Type*} (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (A : Set α) (B : Set β) : Prop :=
  PolyTimeReducible encA encB A B ∧ PolyTimeReducible encB encA B A

namespace PolyTimeEquiv

variable {α β γ : Type*} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {A : Set α} {B : Set β} {C : Set γ}

@[refl]
theorem refl (encA : α ↪ List Bool) (A : Set α) : PolyTimeEquiv encA encA A A :=
  ⟨.refl encA A, .refl encA A⟩

@[symm]
theorem symm (h : PolyTimeEquiv encA encB A B) : PolyTimeEquiv encB encA B A :=
  ⟨h.2, h.1⟩

@[trans]
theorem trans (hAB : PolyTimeEquiv encA encB A B) (hBC : PolyTimeEquiv encB encC B C) :
    PolyTimeEquiv encA encC A C :=
  ⟨hAB.1.trans hBC.1, hBC.2.trans hAB.2⟩

theorem compl (h : PolyTimeEquiv encA encB A B) : PolyTimeEquiv encA encB Aᶜ Bᶜ :=
  ⟨h.1.compl, h.2.compl⟩

theorem mem_P_iff {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (h : PolyTimeEquiv encA encB A B) : A ∈ P encA ↔ B ∈ P encB :=
  ⟨fun hA => h.2.mem_P hA, fun hB => h.1.mem_P hB⟩

theorem mem_NP_iff {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {A : Set α} {B : Set β} (h : PolyTimeEquiv encA encB A B) : A ∈ NP encA ↔ B ∈ NP encB :=
  ⟨fun hA => h.2.mem_NP hA, fun hB => h.1.mem_NP hB⟩

end PolyTimeEquiv

/-- The **polynomial-time many-one degree** of `B` on bit words: the sets polynomial-time many-one
equivalent to `B`. -/
@[expose] def polyTimeDegree (B : Set (List Bool)) : Set (Set (List Bool)) :=
  {A | PolyTimeEquiv encBits encBits A B}

theorem self_mem_polyTimeDegree (B : Set (List Bool)) : B ∈ polyTimeDegree B :=
  PolyTimeEquiv.refl encBits B

/-! ### Non-triviality and finite-variation patching of reductions -/

/-- A problem outside `P` is neither `∅` nor `Set.univ`, so it has a non-member and a member. -/
theorem exists_notMem_and_mem_of_notMem_P {α : Type} {enc : α ↪ List Bool} {B : Set α}
    (hB : B ∉ P enc) : (∃ y₀, y₀ ∉ B) ∧ (∃ y₁, y₁ ∈ B) := by
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hB ((Set.eq_univ_of_forall fun y => not_not.mp fun hy => h ⟨y, hy⟩) ▸ univ_mem_P)
  · by_contra h
    have heq : B = ∅ := Set.ext fun y => ⟨fun hy => absurd ⟨y, hy⟩ h, False.elim⟩
    exact hB (heq ▸ empty_mem_P)

/-- Modifying the source of a polynomial-time reduction on finitely many instances preserves
reducibility whenever the target has a non-member and a member. -/
theorem polyTimeReducible_of_symmDiff_finite_left {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {L L' : Set α} {B : Set β} (hLB : PolyTimeReducible encA encB L B)
    (hfin : (L ∆ L').Finite) {b₀ b₁ : β} (hb₀ : b₀ ∉ B) (hb₁ : b₁ ∈ B) :
    PolyTimeReducible encA encB L' B := by
  obtain ⟨f, hf, hL⟩ := hLB
  obtain ⟨g₁, hg₁, hS₁⟩ :=
    (hfin.subset (t := (L ∆ L') ∩ L') Set.inter_subset_left).mem_P (enc := encA)
  obtain ⟨g₀, hg₀, hS₀⟩ :=
    (hfin.subset (t := (L ∆ L') \ L') Set.sdiff_subset).mem_P (enc := encA)
  refine ⟨fun w => if g₁ w then b₁ else if g₀ w then b₀ else f w,
    hg₁.ite (.const b₁) (hg₀.ite (.const b₀) hf), fun w => ?_⟩
  by_cases hw₁ : w ∈ (L ∆ L') ∩ L'
  · have hg₁w : g₁ w = true := (hS₁ w).mp hw₁
    simp only [hg₁w, ↓reduceIte, hw₁.2, hb₁]
  · have hg₁w : g₁ w = false := Bool.eq_false_iff.mpr fun h => hw₁ ((hS₁ w).mpr h)
    by_cases hw₀ : w ∈ (L ∆ L') \ L'
    · have hg₀w : g₀ w = true := (hS₀ w).mp hw₀
      simp only [hg₁w, hg₀w, Bool.false_eq_true, ↓reduceIte, hw₀.2, hb₀]
    · have hg₀w : g₀ w = false := Bool.eq_false_iff.mpr fun h => hw₀ ((hS₀ w).mpr h)
      have hsame : w ∈ L' ↔ w ∈ L := by
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_symmDiff] at hw₁ hw₀
        tauto
      simp only [hg₁w, hg₀w, Bool.false_eq_true, ↓reduceIte, hsame, hL w]

/-- The lower `≤ₘᵖ`-cone of a problem with a non-member and a member is closed under finite
variations. -/
theorem closedUnderFiniteVariation_polyTimeReducible_le {α β : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {B : Set β} {b₀ b₁ : β} (hb₀ : b₀ ∉ B) (hb₁ : b₁ ∈ B) :
    ClosedUnderFiniteVariation {L : Set α | PolyTimeReducible encA encB L B} :=
  fun _ _ hLB hfin => polyTimeReducible_of_symmDiff_finite_left hLB hfin hb₀ hb₁

/-- Modifying the target of a polynomial-time reduction on finitely many words preserves
reducibility whenever the modified target still has a non-member and a member. -/
theorem polyTimeReducible_of_symmDiff_finite_right {α : Type} {enc : α ↪ List Bool}
    {B : Set α} {L L' : Set (List Bool)} (hBL : PolyTimeReducible enc encBits B L)
    (hfin : (L ∆ L').Finite) {z₀ z₁ : List Bool} (hz₀ : z₀ ∉ L') (hz₁ : z₁ ∈ L') :
    PolyTimeReducible enc encBits B L' := by
  obtain ⟨r, hr, hB⟩ := hBL
  have hP₁ : r ⁻¹' ((L ∆ L') ∩ L) ∈ P enc :=
    PolyTimeReducible.mem_P ⟨r, hr, fun _ => Iff.rfl⟩
      ((hfin.subset Set.inter_subset_left).mem_P (enc := encBits))
  have hP₀ : r ⁻¹' ((L ∆ L') \ L) ∈ P enc :=
    PolyTimeReducible.mem_P ⟨r, hr, fun _ => Iff.rfl⟩
      ((hfin.subset Set.sdiff_subset).mem_P (enc := encBits))
  obtain ⟨g₁, hg₁, hS₁⟩ := hP₁
  obtain ⟨g₀, hg₀, hS₀⟩ := hP₀
  refine ⟨fun x => if g₁ x then z₁ else if g₀ x then z₀ else r x,
    hg₁.ite (.const z₁) (hg₀.ite (.const z₀) hr), fun x => ?_⟩
  by_cases hx₁ : r x ∈ (L ∆ L') ∩ L
  · have hg₁x : g₁ x = true := (hS₁ x).mp hx₁
    simp only [hg₁x, ↓reduceIte, hB x, hx₁.2, hz₁]
  · have hg₁x : g₁ x = false := Bool.eq_false_iff.mpr fun h => hx₁ ((hS₁ x).mpr h)
    by_cases hx₀ : r x ∈ (L ∆ L') \ L
    · have hg₀x : g₀ x = true := (hS₀ x).mp hx₀
      simp only [hg₁x, hg₀x, Bool.false_eq_true, ↓reduceIte, hB x, hx₀.2, hz₀]
    · have hg₀x : g₀ x = false := Bool.eq_false_iff.mpr fun h => hx₀ ((hS₀ x).mpr h)
      have hsame : r x ∈ L ↔ r x ∈ L' := by
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_symmDiff] at hx₁ hx₀
        tauto
      simp only [hg₁x, hg₀x, Bool.false_eq_true, ↓reduceIte, hB x, hsame]

/-! ### Enumerating polynomial-time transducers -/

namespace Ladner

private theorem map_ne_zero_map_eBit (w : List Bool) : (w.map eBit).map (· != 0) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> exact congrArg (_ :: ·) ih

private def decodeRunOutput (r : List ℕ × Bool) : List Bool :=
  if r.2 then r.1.map (· != 0) else []

private theorem computableInPolyTime_decodeRunOutput :
    ComputableInPolyTime decodeRunOutput eOut encBits :=
  ComputableInPolyTime.ite (.snd (encList encUnary) encBool)
    (computableInPolyTime_map_ne_zero.comp (.fst (encList encUnary) encBool)) (.const [])

/-- The output of the `i`-th machine on `w` within its polynomial clock `clock i |w|`, decoded as a
bit word if the machine has halted, and `[]` otherwise. -/
def transducerIndexed (p : ℕ × List Bool) : List Bool :=
  decodeRunOutput (runIndexed p.1 p.2 (clock p.1 p.2.length))

/-- For each fixed index `i`, `w ↦ transducerIndexed (i, w)` is computable in polynomial time. -/
theorem computableInPolyTime_transducerIndexed (i : ℕ) :
    ComputableInPolyTime (fun w => transducerIndexed (i, w)) encBits encBits := by
  have hc : ComputableInPolyTime (fun w : List Bool => clock i w.length) encBits encUnary :=
    (unary_pow i).comp (by fun_prop)
  have hrun : ComputableInPolyTime (fun w : List Bool => runIndexed i w (clock i w.length))
      encBits eOut := by fun_prop
  exact computableInPolyTime_decodeRunOutput.comp hrun

/-- Every polynomial-time function `List Bool → List Bool` is realized by `transducerIndexed` at
arbitrarily large indices. -/
theorem exists_transducerIndexed_eq {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) (B : ℕ) :
    ∃ i, B ≤ i ∧ ∀ w, transducerIndexed (i, w) = f w := by
  obtain ⟨t, s, ht, -, k, State, hfinite, tm, htm⟩ := hf
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  obtain ⟨c, e, hle⟩ := (PolyBounded.of_polynomiallyBounded List.length ht).exists_le
  obtain ⟨i, hi, hdesc⟩ := exists_index_ge (desc eS eBit tm) (B + c + e)
  have hclock (w : List Bool) : t w.length ≤ clock i w.length := by
    calc t w.length ≤ c * (w.length + 1) ^ e := hle w
      _ ≤ 2 ^ i * (w.length + 1) ^ i :=
          Nat.mul_le_mul ((Nat.lt_two_pow_self (n := i)).le.trans' (by omega))
            (Nat.pow_le_pow_right (by omega) (by omega))
      _ = clock i w.length := by rw [clock, ← mul_pow]; ring_nf
  refine ⟨i, by omega, fun w => ?_⟩
  have hrun : runIndexed i w (clock i w.length) = ((f w).map eBit, true) := by
    rw [runIndexed, hdesc]
    exact universal_desc_of_halted_map eS tm (fun x => (htm x).runFrom_of_le le_rfl) (hclock w)
  simp only [transducerIndexed, decodeRunOutput, hrun, ↓reduceIte, map_ne_zero_map_eBit]

private def transducerIndexedCap (p : (ℕ × List Bool) × ℕ) : List Bool :=
  decodeRunOutput (runIndexed p.1.1 p.1.2 (capPow (2 * p.1.2.length + 2) p.1.1 p.2))

private theorem computableInPolyTime_transducerIndexedCap :
    ComputableInPolyTime transducerIndexedCap
      (encPair (encPair encUnary encBits) encUnary) encBits := by
  have hrun : ComputableInPolyTime
      (fun p : (ℕ × List Bool) × ℕ =>
        runIndexed p.1.1 p.1.2 (capPow (2 * p.1.2.length + 2) p.1.1 p.2))
      (encPair (encPair encUnary encBits) encUnary) eOut := by fun_prop
  exact computableInPolyTime_decodeRunOutput.comp hrun

/-- **The enumeration of polynomial-time transducers is computable**, with the index in unary. -/
theorem isComputable_transducerIndexed :
    IsComputable transducerIndexed (encPair encUnary encBits) encBits := by
  have hL : ComputableInPolyTime (fun p : ℕ × List Bool => (p.2.length + 1) * p.1)
      (encPair encUnary encBits) encUnary := by fun_prop
  obtain ⟨C, c, hpad, -⟩ := hL.exists_computableInO_unary_two_pow
  have hpair := (isComputable_id (encPair encUnary encBits)).prod
    (enc := encPair (encPair encUnary encBits) encUnary) hpad.isComputable
  have h := computableInPolyTime_transducerIndexedCap.isComputable.comp hpair
  have heq : transducerIndexed =
      transducerIndexedCap ∘ fun a => (id a, 2 ^ ((a.2.length + 1) * a.1)) := by
    funext p
    have hc := UniformDiagonalization.clock_le_two_pow p.1 p.2.length
    rw [clock] at hc
    simp only [Function.comp_apply, id, transducerIndexedCap, transducerIndexed, capPow, clock,
      min_eq_left hc]
  exact heq ▸ h

end Ladner

open Ladner (transducerIndexed computableInPolyTime_transducerIndexed
  exists_transducerIndexed_eq isComputable_transducerIndexed)

/-! ### Presenting lower cones and classes with a complete problem -/

/-- **The lower `≤ₘᵖ`-cone of a decidable problem on bit words is recursively presentable.** -/
theorem recursivelyPresentable_polyTimeReducible_le {B : Set (List Bool)}
    (hB : IsDecidable B encBits) :
    RecursivelyPresentable encBits {L | PolyTimeReducible encBits encBits L B} := by
  obtain ⟨b, hb, hB'⟩ := hB.exists_isComputable
  refine ⟨b ∘ transducerIndexed, hb.comp isComputable_transducerIndexed, ?_⟩
  ext L
  simp only [Set.mem_ofPred_eq, Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨f, hf, hLB⟩
    obtain ⟨i, -, hi⟩ := exists_transducerIndexed_eq hf 0
    refine ⟨i, Set.ext fun w => ?_⟩
    simp only [Set.mem_ofPred_eq, hi w, ← hB' (f w), ← hLB w]
  · rintro ⟨i, rfl⟩
    exact ⟨fun w => transducerIndexed (i, w), computableInPolyTime_transducerIndexed i,
      fun w => (hB' _).symm⟩

/-- **Any class on bit words closed under `≤ₘᵖ` that has a decidable `≤ₘᵖ`-complete problem is
recursively presentable.** -/
theorem PolyTimeComplete.recursivelyPresentable
    {𝒞 : ∀ {α : Type}, (α ↪ List Bool) → Set (Set α)} {B : Set (List Bool)}
    (hB : PolyTimeComplete 𝒞 encBits B) (hdec : IsDecidable B encBits)
    (hclosed : ∀ ⦃A : Set (List Bool)⦄, PolyTimeReducible encBits encBits A B → A ∈ 𝒞 encBits) :
    RecursivelyPresentable encBits (𝒞 encBits) := by
  have heq : 𝒞 encBits = {A | PolyTimeReducible encBits encBits A B} :=
    Set.ext fun A => ⟨fun hA => hB.2 encBits A hA, fun hAB => hclosed hAB⟩
  exact heq ▸ recursivelyPresentable_polyTimeReducible_le hdec

/-! ### Bounded universal quantification for computable predicates -/

namespace Ladner

private theorem isComputable_ite_bool {α : Type} {encIn : α ↪ List Bool}
    {c t e : α → Bool} (hc : IsComputable c encIn encBool)
    (ht : IsComputable t encIn encBool) (he : IsComputable e encIn encBool) :
    IsComputable (fun x => if c x then t x else e x) encIn encBool := by
  have hte := ht.prod (enc := encPair encBool encBool) he
  have hcte := hc.prod (enc := encPair encBool (encPair encBool encBool)) hte
  have hsel := IsComputable.of_finite (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encBool) fun q : Bool × Bool × Bool => if q.1 then q.2.1 else q.2.2
  exact hsel.comp hcte

/-- Bounded existential search over words of exact unary length preserves `IsComputable`. -/
theorem isComputable_exists_bits {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} (htest : IsComputable test (encPair encC encBits) encBool) :
    IsComputable (fun p : C × ℕ => (Cslib.BitString.enumList p.2).any fun w => test (p.1, w))
      (encPair encC encUnary) encBool := by
  obtain ⟨Tf, Sf, hc⟩ := htest
  have hcO : ComputableInO test (encPair encC encBits) encBool Tf Sf :=
    ⟨1, hc.mono (fun _ => by omega) fun _ => by omega,
      fun x => by cases test x <;> (simp only [encBool_apply, List.length_singleton]; omega)⟩
  let T : C × ℕ → ℕ := fun p => listMax (fun w => Tf (p.1, w)) (Cslib.BitString.enumList p.2)
  let S : C × ℕ → ℕ := fun p => listMax (fun w => Sf (p.1, w)) (Cslib.BitString.enumList p.2)
  obtain ⟨_, _, _, hsearch, -⟩ := ComputableInO.exists_bits hcO (T := T) (S := S)
    (fun p w hw => le_listMax (f := fun w => Tf (p.1, w)) (Cslib.BitString.mem_enumList.mpr hw))
    (fun p w hw => le_listMax (f := fun w => Sf (p.1, w)) (Cslib.BitString.mem_enumList.mpr hw))
  exact hsearch.isComputable

/-- Bounded universal search over words of exact unary length preserves `IsComputable`. -/
theorem isComputable_forall_bits {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} (htest : IsComputable test (encPair encC encBits) encBool) :
    IsComputable (fun p : C × ℕ => (Cslib.BitString.enumList p.2).all fun w => test (p.1, w))
      (encPair encC encUnary) encBool := by
  have hnot := (IsComputable.of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp
    (isComputable_exists_bits
      ((IsComputable.of_finite (encIn := encBool) (encMid := encBool) Bool.not).comp htest))
  convert hnot using 1
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, List.all_eq_true, Bool.not_eq_true', List.any_eq_false]
  exact forall₂_congr fun x _ => by cases test (p.1, x) <;> decide

/-- Testing whether `test (c, x) = true` for all bit words `x` strictly shorter than `n`: pad `x`
to length `n` with `false` followed by `n - 1 - |x|` ones (`Cslib.Complexity.Ladner.pad`), and scan
all words of length `n`. -/
private def checkShorter {C : Type} (test : C × List Bool → Bool) (p : C × ℕ) : Bool :=
  (Cslib.BitString.enumList p.2).all fun u =>
    if decide ((unpad u).2 < p.2) then test (p.1, (unpad u).1) else true

private theorem checkShorter_eq_true_iff {C : Type} {test : C × List Bool → Bool}
    {c : C} {n : ℕ} :
    checkShorter test (c, n) = true ↔ ∀ x : List Bool, x.length < n → test (c, x) = true := by
  simp only [checkShorter, List.all_eq_true, Cslib.BitString.mem_enumList]
  constructor
  · intro h x hx
    have hlen : (pad x (n - 1 - x.length)).length = n := by
      rw [length_pad]
      omega
    have hu := h (pad x (n - 1 - x.length)) hlen
    rw [unpad_pad] at hu
    have hlt : n - 1 - x.length < n := by omega
    simpa only [decide_eq_true hlt, ↓reduceIte] using hu
  · intro h u hu
    split_ifs with hlt
    · replace hlt := of_decide_eq_true hlt
      have hpad := pad_unpad (hu ▸ hlt)
      have hlen := congrArg List.length hpad
      rw [length_pad, hu] at hlen
      exact h (unpad u).1 (by omega)
    · rfl

private theorem isComputable_checkShorter {C : Type} {encC : C ↪ List Bool}
    {test : C × List Bool → Bool} (htest : IsComputable test (encPair encC encBits) encBool) :
    IsComputable (checkShorter test) (encPair encC encUnary) encBool := by
  let body : (C × ℕ) × List Bool → Bool := fun q =>
    if decide ((unpad q.2).2 < q.1.2) then test (q.1.1, (unpad q.2).1) else true
  have hguard : ComputableInPolyTime (fun q : (C × ℕ) × List Bool => decide ((unpad q.2).2 < q.1.2))
      (encPair (encPair encC encUnary) encBits) encBool := by fun_prop
  have harg : ComputableInPolyTime (fun q : (C × ℕ) × List Bool => (q.1.1, (unpad q.2).1))
      (encPair (encPair encC encUnary) encBits) (encPair encC encBits) := by fun_prop
  have htrue : ComputableInPolyTime (fun _ : (C × ℕ) × List Bool => true)
      (encPair (encPair encC encUnary) encBits) encBool := .const true
  have hbody : IsComputable body (encPair (encPair encC encUnary) encBits) encBool :=
    isComputable_ite_bool hguard.isComputable (htest.comp harg.isComputable) htrue.isComputable
  have h := isComputable_forall_bits hbody
  have hdup : ComputableInPolyTime (fun p : C × ℕ => (p, p.2))
      (encPair encC encUnary) (encPair (encPair encC encUnary) encUnary) := by fun_prop
  exact h.comp hdup.isComputable

end Ladner

/-! ### Presenting polynomial-time degrees and density cones -/

section DegreeCone

/-- A generalized degree cone `{L | L ≤ₘᵖ B ∧ B ≤ₘᵖ W L}` for a set transformer `W` preserving
finite variations and realized on indicators by `wval`. `W = id` gives `polyTimeDegree B`, and
`W = markedUnion A` gives the cone needed for full Ladner density. -/
private def coneOf (W : Set (List Bool) → Set (List Bool)) (B : Set (List Bool)) :
    Set (Set (List Bool)) :=
  {L | PolyTimeReducible encBits encBits L B ∧ PolyTimeReducible encBits encBits B (W L)}

private theorem closedUnderFiniteVariation_coneOf {W : Set (List Bool) → Set (List Bool)}
    {B : Set (List Bool)} (hB : B ∉ P encBits)
    (hWsymm : ∀ ⦃L L' : Set (List Bool)⦄, (L ∆ L').Finite → (W L ∆ W L').Finite) :
    ClosedUnderFiniteVariation (coneOf W B) := by
  obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hB
  intro L L' ⟨hLB, hBWL⟩ hfin
  have hL'B := polyTimeReducible_of_symmDiff_finite_left hLB hfin hb₀ hb₁
  have hWL_notP : W L ∉ P encBits := fun hP => hB (hBWL.mem_P hP)
  have hWL'_notP : W L' ∉ P encBits :=
    fun hP => hWL_notP ((closedUnderFiniteVariation_P encBits) hP
      (symmDiff_comm (W L) (W L') ▸ hWsymm hfin))
  obtain ⟨⟨z₀, hz₀⟩, ⟨z₁, hz₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hWL'_notP
  exact ⟨hL'B, polyTimeReducible_of_symmDiff_finite_right hBWL (hWsymm hfin) hz₀ hz₁⟩

private theorem recursivelyPresentable_coneOf {W : Set (List Bool) → Set (List Bool)}
    {B : Set (List Bool)} (hdec : IsDecidable B encBits) (hB : B ∉ P encBits)
    (hWB : PolyTimeReducible encBits encBits B (W B))
    (hWsymm : ∀ ⦃L L' : Set (List Bool)⦄, (L ∆ L').Finite → (W L ∆ W L').Finite)
    {wval : (List Bool → Bool) → List Bool → Bool}
    (hwval : ∀ g : List Bool → Bool, {u | wval g u = true} = W {u | g u = true})
    (hwcomp : ∀ {G : ℕ × List Bool → Bool}, IsComputable G (encPair encUnary encBits) encBool →
      IsComputable (fun p : ℕ × List Bool => wval (fun u => G (p.1, u)) p.2)
        (encPair encUnary encBits) encBool) :
    RecursivelyPresentable encBits (coneOf W B) := by
  have hclosed := closedUnderFiniteVariation_coneOf hB hWsymm
  have hBmem : B ∈ coneOf W B := ⟨.refl encBits B, hWB⟩
  obtain ⟨b, hb, hB'⟩ := hdec.exists_isComputable
  let g : ℕ × List Bool → Bool := fun p => b (transducerIndexed p)
  have hg : IsComputable g (encPair encUnary encBits) encBool :=
    hb.comp isComputable_transducerIndexed
  let wg := fun p : ℕ × List Bool => wval (fun u => g (p.1, u)) p.2
  have hwg : IsComputable wg (encPair encUnary encBits) encBool := hwcomp hg
  let eqTest : (ℕ × ℕ) × List Bool → Bool := fun q =>
    decide (b q.2 = wg (q.1.1, transducerIndexed (q.1.2, q.2)))
  have heqTest : IsComputable eqTest (encPair (encPair encUnary encUnary) encBits) encBool := by
    have hfst : ComputableInPolyTime (fun q : (ℕ × ℕ) × List Bool => q.2)
        (encPair (encPair encUnary encUnary) encBits) encBits := by fun_prop
    have hj : ComputableInPolyTime (fun q : (ℕ × ℕ) × List Bool => (q.1.2, q.2))
        (encPair (encPair encUnary encUnary) encBits) (encPair encUnary encBits) := by fun_prop
    have hi : ComputableInPolyTime (fun q : (ℕ × ℕ) × List Bool => q.1.1)
        (encPair (encPair encUnary encUnary) encBits) encUnary := by fun_prop
    have hbeq := IsComputable.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
      fun p : Bool × Bool => decide (p.1 = p.2)
    have hwgArg := hi.isComputable.prod (enc := encPair encUnary encBits)
      (isComputable_transducerIndexed.comp hj.isComputable)
    exact hbeq.comp ((hb.comp hfst.isComputable).prod (enc := encPair encBool encBool)
      (hwg.comp hwgArg))
  let present : ℕ × List Bool → Bool := fun p =>
    if Ladner.checkShorter eqTest (p.1.unpair, p.2.length) then g (p.1.unpair.1, p.2) else b p.2
  have hpresent : IsComputable present (encPair encUnary encBits) encBool := by
    have hchkArg : ComputableInPolyTime (fun p : ℕ × List Bool => (p.1.unpair, p.2.length))
        (encPair encUnary encBits) (encPair (encPair encUnary encUnary) encUnary) := by fun_prop
    have hgArg : ComputableInPolyTime (fun p : ℕ × List Bool => (p.1.unpair.1, p.2))
        (encPair encUnary encBits) (encPair encUnary encBits) := by fun_prop
    have hbArg : ComputableInPolyTime (fun p : ℕ × List Bool => p.2)
        (encPair encUnary encBits) encBits := by fun_prop
    exact Ladner.isComputable_ite_bool
      ((Ladner.isComputable_checkShorter heqTest).comp hchkArg.isComputable)
      (hg.comp hgArg.isComputable) (hb.comp hbArg.isComputable)
  refine ⟨present, hpresent, Set.ext fun L => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨f₁, hf₁, hL₁⟩, ⟨f₂, hf₂, hL₂⟩⟩
    obtain ⟨i, -, hi⟩ := exists_transducerIndexed_eq hf₁ 0
    obtain ⟨j, -, hj⟩ := exists_transducerIndexed_eq hf₂ 0
    have hLi : {u | g (i, u) = true} = L := Set.ext fun u => by
      simp only [Set.mem_ofPred_eq, g, hi u, ← hB' (f₁ u), ← hL₁ u]
    have hWLi : {u | wg (i, u) = true} = W L := by
      simpa only [wg, hLi] using hwval (fun u => g (i, u))
    have hall : ∀ x : List Bool, eqTest ((i, j), x) = true := fun x => by
      simp only [eqTest, decide_eq_true_eq, hj x]
      apply Bool.eq_iff_iff.mpr
      rw [← hB' x, hL₂ x, ← hWLi, Set.mem_ofPred_eq]
    refine ⟨Nat.pair i j, Set.ext fun w => ?_⟩
    have hchk : Ladner.checkShorter eqTest ((i, j), w.length) = true :=
      Ladner.checkShorter_eq_true_iff.mpr fun x _ => hall x
    simp only [Set.mem_ofPred_eq, present, Nat.unpair_pair, hchk, ↓reduceIte]
    exact Set.ext_iff.mp hLi w
  · rintro ⟨m, rfl⟩
    dsimp only
    set i := m.unpair.1
    set j := m.unpair.2
    by_cases hall : ∀ x : List Bool, eqTest ((i, j), x) = true
    · have hchk : ∀ w : List Bool, Ladner.checkShorter eqTest ((i, j), w.length) = true :=
        fun w => Ladner.checkShorter_eq_true_iff.mpr fun x _ => hall x
      have heq : {a | present (m, a) = true} = {u | g (i, u) = true} := by
        ext w
        simp only [Set.mem_ofPred_eq, present, show m.unpair = (i, j) from rfl, hchk w, ↓reduceIte]
      rw [heq]
      refine ⟨⟨fun w => transducerIndexed (i, w), computableInPolyTime_transducerIndexed i,
        fun w => (hB' _).symm⟩, ⟨fun w => transducerIndexed (j, w),
        computableInPolyTime_transducerIndexed j, fun x => ?_⟩⟩
      have hx := of_decide_eq_true (hall x)
      rw [hB' x, hx, ← hwval (fun u => g (i, u)), Set.mem_ofPred_eq]
    · push Not at hall
      obtain ⟨x₀, hx₀⟩ := hall
      replace hx₀ : eqTest ((i, j), x₀) = false := Bool.eq_false_iff.mpr hx₀
      have hfin : (B ∆ {a | present (m, a) = true}).Finite := by
        refine (List.finite_length_lt Bool (x₀.length + 1)).subset fun w hw => ?_
        by_contra hlen
        rw [Set.mem_ofPred_eq, not_lt] at hlen
        have hfalse : Ladner.checkShorter eqTest ((i, j), w.length) = false := by
          rw [Bool.eq_false_iff]
          intro htrue
          have := Ladner.checkShorter_eq_true_iff.mp htrue x₀ (by omega)
          rw [hx₀] at this
          cases this
        have hpw : (present (m, w) = true) ↔ w ∈ B := by
          simp only [present, show m.unpair = (i, j) from rfl, hfalse, Bool.false_eq_true,
            ↓reduceIte, hB' w]
        simp only [Set.mem_symmDiff, Set.mem_ofPred_eq, hpw] at hw
        tauto
      exact hclosed hBmem hfin

/-- **The polynomial-time `m`-degree of a problem outside `P` is closed under finite
variations.** -/
theorem closedUnderFiniteVariation_polyTimeDegree {B : Set (List Bool)} (hB : B ∉ P encBits) :
    ClosedUnderFiniteVariation (polyTimeDegree B) :=
  closedUnderFiniteVariation_coneOf (W := id) hB fun _ _ h => h

/-- **The polynomial-time `m`-degree of a decidable problem outside `P` is recursively
presentable.** -/
theorem recursivelyPresentable_polyTimeDegree {B : Set (List Bool)}
    (hdec : IsDecidable B encBits) (hB : B ∉ P encBits) :
    RecursivelyPresentable encBits (polyTimeDegree B) :=
  recursivelyPresentable_coneOf (W := id) (wval := fun g u => g u) hdec hB
    (.refl encBits B) (fun _ _ h => h) (fun _ => rfl) (fun hG => hG)

end DegreeCone

/-! ### Marked-union helpers -/

theorem polyTimeReducible_left_markedUnion (A B : Set (List Bool)) :
    PolyTimeReducible encBits encBits A (markedUnion A B) :=
  ⟨fun w => false :: w, by fun_prop, fun w => (cons_mem_markedUnion (b := false)).symm⟩

theorem polyTimeReducible_right_markedUnion (A B : Set (List Bool)) :
    PolyTimeReducible encBits encBits B (markedUnion A B) :=
  ⟨fun w => true :: w, by fun_prop, fun w => (cons_mem_markedUnion (b := true)).symm⟩

theorem polyTimeReducible_markedUnion {A B C : Set (List Bool)}
    (hAC : PolyTimeReducible encBits encBits A C)
    (hBC : PolyTimeReducible encBits encBits B C)
    {c₀ : List Bool} (hc₀ : c₀ ∉ C) :
    PolyTimeReducible encBits encBits (markedUnion A B) C := by
  obtain ⟨fA, hfA, hA⟩ := hAC
  obtain ⟨fB, hfB, hB⟩ := hBC
  let step : List Bool → List Bool := fun w =>
    if w.isEmpty then c₀ else if w.headD false then fB w.tail else fA w.tail
  have hstep : ComputableInPolyTime step encBits encBits := by
    unfold step
    fun_prop
  refine ⟨step, hstep, fun w => ?_⟩
  cases w with
  | nil =>
    simp only [step, List.isEmpty_nil, ↓reduceIte, hc₀, iff_false]
    rintro ⟨x, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> cases h
  | cons b u =>
    rw [cons_mem_markedUnion]
    cases b <;> simp [step, hA u, hB u]

theorem isDecidable_markedUnion {A B : Set (List Bool)}
    (hA : IsDecidable A encBits) (hB : IsDecidable B encBits) :
    IsDecidable (markedUnion A B) encBits := by
  obtain ⟨fA, hfA, hA'⟩ := hA.exists_isComputable
  obtain ⟨fB, hfB, hB'⟩ := hB.exists_isComputable
  let dec : List Bool → Bool := fun w =>
    if w.isEmpty then false else if w.headD false then fB w.tail else fA w.tail
  have hempty : ComputableInPolyTime List.isEmpty encBits encBool := by fun_prop
  have hhead : ComputableInPolyTime (fun w : List Bool => w.headD false) encBits encBool := by
    fun_prop
  have htail : ComputableInPolyTime (fun w : List Bool => w.tail) encBits encBits := by fun_prop
  have hfalse : ComputableInPolyTime (fun _ : List Bool => false) encBits encBool := .const false
  refine isDecidable_iff.mpr ⟨dec, Ladner.isComputable_ite_bool hempty.isComputable
    hfalse.isComputable (Ladner.isComputable_ite_bool hhead.isComputable
      (hfB.comp htail.isComputable) (hfA.comp htail.isComputable)), fun w => ?_⟩
  cases w with
  | nil =>
    simp only [dec, List.isEmpty_nil, ↓reduceIte, Bool.false_eq_true, iff_false]
    rintro ⟨x, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> cases h
  | cons b u =>
    rw [cons_mem_markedUnion]
    cases b <;> simp [dec, hA' u, hB' u]

theorem markedUnion_mem_NP {A B : Set (List Bool)}
    (hA : A ∈ NP encBits) (hB : B ∈ NP encBits) :
    markedUnion A B ∈ NP encBits := by
  have hL :
      {w : List Bool | (w.isEmpty = false ∧ w.headD false = false) ∧ w.tail ∈ A} ∈ NP encBits := by
    have h₁ : {w : List Bool | w.isEmpty = false ∧ w.headD false = false} ∈ P encBits :=
      ⟨fun w => !w.isEmpty && !w.headD false, by fun_prop, fun w => by
        cases w with
        | nil => simp
        | cons b u => cases b <;> simp⟩
    have h₂ : {w : List Bool | w.tail ∈ A} ∈ NP encBits :=
      PolyTimeReducible.mem_NP ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩ hA
    exact inter_mem_NP (P_subset_NP h₁) h₂
  have hR :
      {w : List Bool | (w.isEmpty = false ∧ w.headD false = true) ∧ w.tail ∈ B} ∈ NP encBits := by
    have h₁ : {w : List Bool | w.isEmpty = false ∧ w.headD false = true} ∈ P encBits :=
      ⟨fun w => !w.isEmpty && w.headD false, by fun_prop, fun w => by
        cases w with
        | nil => simp
        | cons b u => cases b <;> simp⟩
    have h₂ : {w : List Bool | w.tail ∈ B} ∈ NP encBits :=
      PolyTimeReducible.mem_NP ⟨List.tail, by fun_prop, fun _ => Iff.rfl⟩ hB
    exact inter_mem_NP (P_subset_NP h₁) h₂
  convert union_mem_NP hL hR using 1
  ext w
  cases w with
  | nil =>
    simp only [Set.mem_union, Set.mem_ofPred_eq, List.isEmpty_nil, Bool.true_eq_false, false_and,
      or_self, iff_false]
    rintro ⟨x, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> cases h
  | cons b u =>
    rw [cons_mem_markedUnion]
    cases b <;> simp

theorem ite_mem_NP {α : Type} {enc : α ↪ List Bool} {G A₁ A₂ : Set α}
    (hG : G ∈ P enc) (hA₁ : A₁ ∈ NP enc) (hA₂ : A₂ ∈ NP enc) :
    G.ite A₁ A₂ ∈ NP enc := by
  have heq : G.ite A₁ A₂ = A₁ ∩ G ∪ A₂ ∩ Gᶜ := by
    ext a
    simp only [Set.ite, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_compl_iff]
  exact heq ▸ union_mem_NP (inter_mem_NP hA₁ (P_subset_NP hG))
    (inter_mem_NP hA₂ (P_subset_NP (compl_mem_P hG)))

/-! ### Ladner's downward theorem and `NP`-intermediate problems -/

/-- **Ladner's downward theorem, gap-set form.** For every decidable `B ∉ P` on bit words, some
`G ∈ P` makes `G.ite ∅ B` lie outside `P` and strictly `≤ₘᵖ`-below `B`. -/
theorem exists_mem_P_ite_empty_lt {B : Set (List Bool)}
    (hdec : IsDecidable B encBits) (hB : B ∉ P encBits) :
    ∃ G ∈ P encBits, G.ite ∅ B ∉ P encBits ∧
      PolyTimeReducible encBits encBits (G.ite ∅ B) B ∧
      ¬PolyTimeReducible encBits encBits B (G.ite ∅ B) := by
  obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hB
  have hempty : (∅ : Set (List Bool)) ∉ polyTimeDegree B := fun h =>
    hB (h.2.mem_P empty_mem_P)
  obtain ⟨G, hG, hnotDeg, hnotP⟩ := exists_mem_P_ite_notMem
    (recursivelyPresentable_polyTimeDegree hdec hB) recursivelyPresentable_P
    (closedUnderFiniteVariation_polyTimeDegree hB) (closedUnderFiniteVariation_P encBits)
    (isDecidable_of_mem_P empty_mem_P) hdec hempty hB
  have hred : PolyTimeReducible encBits encBits (G.ite ∅ B) B :=
    polyTimeReducible_ite_of_mem_P hG empty_mem_P hb₀ hb₁
  exact ⟨G, hG, hnotP, hred, fun hback => hnotDeg ⟨hred, hback⟩⟩

/-- **Ladner's downward theorem.** Every decidable `B ∉ P` on bit words has a decidable `A ∉ P`
strictly `≤ₘᵖ`-below it [Ladner][Ladner1975a], [Schöning][Schoening1982]. -/
theorem exists_isDecidable_notMem_P_lt {B : Set (List Bool)}
    (hdec : IsDecidable B encBits) (hB : B ∉ P encBits) :
    ∃ A : Set (List Bool), IsDecidable A encBits ∧ A ∉ P encBits ∧
      PolyTimeReducible encBits encBits A B ∧ ¬PolyTimeReducible encBits encBits B A := by
  obtain ⟨G, hG, hnotP, hAB, hBA⟩ := exists_mem_P_ite_empty_lt hdec hB
  exact ⟨G.ite ∅ B,
    isDecidable_ite (isDecidable_of_mem_P hG) (isDecidable_of_mem_P empty_mem_P) hdec,
    hnotP, hAB, hBA⟩

/-- Every problem `B ∈ NP \ P` on bit words has an `NP`-intermediate problem strictly `≤ₘᵖ`-below
it. -/
theorem exists_mem_NP_notMem_P_lt {B : Set (List Bool)}
    (hBNP : B ∈ NP encBits) (hB : B ∉ P encBits) :
    ∃ A ∈ NP encBits, A ∉ P encBits ∧ ¬NPComplete encBits A ∧
      PolyTimeReducible encBits encBits A B ∧ ¬PolyTimeReducible encBits encBits B A := by
  have hdec : IsDecidable B encBits := isDecidable_of_mem_EXP (NP_subset_EXP hBNP)
  obtain ⟨G, hG, hnotP, hAB, hBA⟩ := exists_mem_P_ite_empty_lt hdec hB
  refine ⟨G.ite ∅ B, ite_mem_NP hG (P_subset_NP empty_mem_P) hBNP, hnotP,
    fun hcomp => hBA (hcomp.2 encBits B hBNP), hAB, hBA⟩

/-- **If `P ≠ NP`, every `NP`-complete problem on bit words has an `NP`-intermediate problem
strictly below it.** This strengthens `Cslib.Complexity.Ladner.exists_NP_not_P_not_npComplete` from
exhibiting one `NP`-intermediate language to placing one strictly below any chosen `NP`-complete
language [Ladner][Ladner1975a], [Schöning][Schoening1982]. -/
theorem NPComplete.exists_NP_not_P_not_npComplete_lt {α : Type} {enc : α ↪ List Bool}
    {B : Set (List Bool)} (hB : NPComplete encBits B) (hne : P enc ≠ NP enc) :
    ∃ A ∈ NP encBits, A ∉ P encBits ∧ ¬NPComplete encBits A ∧
      PolyTimeReducible encBits encBits A B ∧ ¬PolyTimeReducible encBits encBits B A :=
  exists_mem_NP_notMem_P_lt hB.1 fun hBP => hne (hB.P_eq_NP_of_mem_P hBP enc)

/-! ### Full Ladner density theorem -/

private theorem symmDiff_markedUnion_finite (A : Set (List Bool)) {L L' : Set (List Bool)}
    (hfin : (L ∆ L').Finite) : (markedUnion A L ∆ markedUnion A L').Finite := by
  refine (hfin.image (true :: ·)).subset fun w hw => ?_
  cases w with
  | nil =>
    have hnil : ∀ S, ([] : List Bool) ∉ markedUnion A S := by
      rintro S ⟨x, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> cases h
    simp [Set.mem_symmDiff, hnil] at hw
  | cons b u =>
    cases b
    · simp [Set.mem_symmDiff, cons_mem_markedUnion] at hw
    · simp only [Set.mem_symmDiff, cons_mem_markedUnion, ↓reduceIte] at hw
      exact ⟨u, hw, rfl⟩

private theorem polyTimeReducible_ite_of_reducible {G A B : Set (List Bool)}
    (hG : G ∈ P encBits) (hAB : PolyTimeReducible encBits encBits A B) :
    PolyTimeReducible encBits encBits (G.ite B A) B := by
  obtain ⟨g, hg, hG'⟩ := hG
  obtain ⟨r, hr, hAB'⟩ := hAB
  refine ⟨fun w => if g w then w else r w, hg.ite .id' hr, fun w => ?_⟩
  by_cases hw : w ∈ G
  · have hgw : g w = true := (hG' w).mp hw
    simp [Set.ite, hw, hgw]
  · have hgw : g w = false := Bool.eq_false_iff.mpr fun h => hw ((hG' w).mpr h)
    simp [Set.ite, hw, hgw, hAB' w]

/-- Core witness for full Ladner density when both `A` and `B` lie outside `P`: uniform
diagonalization yields `G ∈ P` such that `markedUnion A (G.ite B A)` sits strictly between `A` and
`B`. -/
private theorem exists_mem_P_markedUnion_ite_between {A B : Set (List Bool)}
    (hdecA : IsDecidable A encBits) (hdecB : IsDecidable B encBits)
    (hAP : A ∉ P encBits) (hBP : B ∉ P encBits)
    (hAB : PolyTimeReducible encBits encBits A B)
    (hBA : ¬PolyTimeReducible encBits encBits B A) :
    ∃ G ∈ P encBits,
      let C := markedUnion A (G.ite B A)
      PolyTimeReducible encBits encBits A C ∧ ¬PolyTimeReducible encBits encBits C A ∧
        PolyTimeReducible encBits encBits C B ∧ ¬PolyTimeReducible encBits encBits B C := by
  obtain ⟨⟨a₀, ha₀⟩, ⟨a₁, ha₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hAP
  obtain ⟨⟨b₀, hb₀⟩, -⟩ := exists_notMem_and_mem_of_notMem_P hBP
  obtain ⟨fa, hfa, hA'⟩ := hdecA.exists_isComputable
  let wval : (List Bool → Bool) → List Bool → Bool := fun g w =>
    if w.isEmpty then false else if w.headD false then g w.tail else fa w.tail
  have hwval (g : List Bool → Bool) :
      {u | wval g u = true} = markedUnion A {u | g u = true} := by
    ext w
    cases w with
    | nil =>
      simp only [Set.mem_ofPred_eq, wval, List.isEmpty_nil, ↓reduceIte, Bool.false_eq_true]
      refine ⟨False.elim, ?_⟩
      rintro ⟨x, ⟨h, -⟩ | ⟨h, -⟩⟩ <;> cases h
    | cons b u =>
      rw [cons_mem_markedUnion]
      cases b <;> simp [wval, hA' u]
  have hwcomp {G : ℕ × List Bool → Bool}
      (hG : IsComputable G (encPair encUnary encBits) encBool) :
      IsComputable (fun p : ℕ × List Bool => wval (fun u => G (p.1, u)) p.2)
        (encPair encUnary encBits) encBool := by
    have hempty : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.isEmpty)
        (encPair encUnary encBits) encBool := by fun_prop
    have hhead : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.headD false)
        (encPair encUnary encBits) encBool := by fun_prop
    have hgArg : ComputableInPolyTime (fun p : ℕ × List Bool => (p.1, p.2.tail))
        (encPair encUnary encBits) (encPair encUnary encBits) := by fun_prop
    have haArg : ComputableInPolyTime (fun p : ℕ × List Bool => p.2.tail)
        (encPair encUnary encBits) encBits := by fun_prop
    have hfalse : ComputableInPolyTime (fun _ : ℕ × List Bool => false)
        (encPair encUnary encBits) encBool := .const false
    exact Ladner.isComputable_ite_bool hempty.isComputable hfalse.isComputable
      (Ladner.isComputable_ite_bool hhead.isComputable
        (hG.comp hgArg.isComputable) (hfa.comp haArg.isComputable))
  have hC₁_pres := recursivelyPresentable_polyTimeReducible_le hdecA
  have hC₁_fv :=
    closedUnderFiniteVariation_polyTimeReducible_le (encA := encBits) (encB := encBits) ha₀ ha₁
  have hC₂_pres := recursivelyPresentable_coneOf (W := markedUnion A) (wval := wval)
    hdecB hBP (polyTimeReducible_right_markedUnion A B) (fun _ _ => symmDiff_markedUnion_finite A)
    hwval hwcomp
  have hC₂_fv := closedUnderFiniteVariation_coneOf (W := markedUnion A) hBP
    (fun _ _ => symmDiff_markedUnion_finite A)
  have hA_not_C₂ : A ∉ coneOf (markedUnion A) B := by
    rintro ⟨-, hB_mAA⟩
    exact hBA (hB_mAA.trans (polyTimeReducible_markedUnion (.refl encBits A) (.refl encBits A) ha₀))
  obtain ⟨G, hG, hnotC₁, hnotC₂⟩ := exists_mem_P_ite_notMem
    hC₁_pres hC₂_pres hC₁_fv hC₂_fv hdecB hdecA hBA hA_not_C₂
  have hDB : PolyTimeReducible encBits encBits (G.ite B A) B :=
    polyTimeReducible_ite_of_reducible hG hAB
  refine ⟨G, hG, polyTimeReducible_left_markedUnion A (G.ite B A),
    fun hCA => hnotC₁ ((polyTimeReducible_right_markedUnion A (G.ite B A)).trans hCA),
    polyTimeReducible_markedUnion hAB hDB hb₀,
    fun hBC => hnotC₂ ⟨hDB, hBC⟩⟩

/-- **Ladner's density theorem.** Between any two decidable problems `A <ₘᵖ B` on bit words with
`B ∉ P`, there is a decidable problem `C` strictly between them: `A <ₘᵖ C` and `C <ₘᵖ B`
[Ladner][Ladner1975a], [Schöning][Schoening1982]. -/
theorem exists_isDecidable_between_of_notMem_P {A B : Set (List Bool)}
    (hdecA : IsDecidable A encBits) (hdecB : IsDecidable B encBits)
    (hBP : B ∉ P encBits) (hAB : PolyTimeReducible encBits encBits A B)
    (hBA : ¬PolyTimeReducible encBits encBits B A) :
    ∃ C : Set (List Bool), IsDecidable C encBits ∧
      PolyTimeReducible encBits encBits A C ∧ ¬PolyTimeReducible encBits encBits C A ∧
      PolyTimeReducible encBits encBits C B ∧ ¬PolyTimeReducible encBits encBits B C := by
  by_cases hAP : A ∈ P encBits
  · obtain ⟨C, hdecC, hCP, hCB, hBC⟩ := exists_isDecidable_notMem_P_lt hdecB hBP
    obtain ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hCP
    exact ⟨C, hdecC, polyTimeReducible_of_mem_P hAP hc₁ hc₀,
      fun hCA => hCP (hCA.mem_P hAP), hCB, hBC⟩
  · obtain ⟨G, hG, h₁, h₂, h₃, h₄⟩ :=
      exists_mem_P_markedUnion_ite_between hdecA hdecB hAP hBP hAB hBA
    exact ⟨markedUnion A (G.ite B A),
      isDecidable_markedUnion hdecA (isDecidable_ite (isDecidable_of_mem_P hG) hdecB hdecA),
      h₁, h₂, h₃, h₄⟩

/-- **Ladner's density theorem within `NP`.** Between any two problems `A <ₘᵖ B` in `NP` on bit
words with `B ∉ P`, there is a problem `C ∈ NP` strictly between them: `A <ₘᵖ C` and `C <ₘᵖ B`
[Ladner][Ladner1975a], [Schöning][Schoening1982]. -/
theorem exists_mem_NP_between_of_notMem_P {A B : Set (List Bool)}
    (hANP : A ∈ NP encBits) (hBNP : B ∈ NP encBits) (hBP : B ∉ P encBits)
    (hAB : PolyTimeReducible encBits encBits A B)
    (hBA : ¬PolyTimeReducible encBits encBits B A) :
    ∃ C ∈ NP encBits,
      PolyTimeReducible encBits encBits A C ∧ ¬PolyTimeReducible encBits encBits C A ∧
      PolyTimeReducible encBits encBits C B ∧ ¬PolyTimeReducible encBits encBits B C := by
  by_cases hAP : A ∈ P encBits
  · obtain ⟨C, hCNP, hCP, -, hCB, hBC⟩ := exists_mem_NP_notMem_P_lt hBNP hBP
    obtain ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩⟩ := exists_notMem_and_mem_of_notMem_P hCP
    exact ⟨C, hCNP, polyTimeReducible_of_mem_P hAP hc₁ hc₀,
      fun hCA => hCP (hCA.mem_P hAP), hCB, hBC⟩
  · have hdecA : IsDecidable A encBits := isDecidable_of_mem_EXP (NP_subset_EXP hANP)
    have hdecB : IsDecidable B encBits := isDecidable_of_mem_EXP (NP_subset_EXP hBNP)
    obtain ⟨G, hG, h₁, h₂, h₃, h₄⟩ :=
      exists_mem_P_markedUnion_ite_between hdecA hdecB hAP hBP hAB hBA
    exact ⟨markedUnion A (G.ite B A),
      markedUnion_mem_NP hANP (ite_mem_NP hG hBNP hANP), h₁, h₂, h₃, h₄⟩

end Cslib.Complexity
