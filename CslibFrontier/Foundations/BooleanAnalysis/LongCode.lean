/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Fourier
public import CslibFrontier.Foundations.Data.Code.Hadamard
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Tactic.Linarith

/-!
# The long code, odd Boolean functions, folding, and projections of characters

The *long code* of a label `a : ι` is the dictator `r ↦ r a`, the evaluation `Function.eval a` on
`ι → Bool` (`BitString.longCode`) [Arora and Barak, Chapter 22][AroraBarak09]. It is the Hadamard
encoding of the unit vector of `a` (`BitString.longCode_eq_hadamardCode`), so a table within
relative distance `1/4` of a long code determines its label
(`BitString.eq_of_hammingDist_longCode_lt`).

A Boolean function `B : (ι → Bool) → Bool` is *odd* (`BitString.IsOdd`) when complementing its
input complements its output, `B (f + 1) = !B f`; in `±1` notation this is `F (-x) = -F x`, and
such functions are also called *self-dual*. In PCP constructions, odd long code tables are called
*folded*. Every long code is odd (`BitString.isOdd_longCode`), every table can be folded around a
coordinate into an odd one (`BitString.foldTable`), and the Fourier coefficients of an odd function
vanish on every set of even cardinality (`BitString.IsOdd.fourierCoeff_of_even`), in particular on
`∅` (`BitString.IsOdd.fourierCoeff_empty`).

For a map `π : β → γ`, the *mod-2 projection* `BitString.projectSet π T` of `T : Finset β` is the
set of points of `γ` with an odd number of preimages in `T`. Pulling a character back along `π`
projects its frequency set: `chi T (f ∘ π) = chi (projectSet π T) f`
(`BitString.chi_comp_eq_chi_projectSet`) [Håstad][Hastad2001].

## Main definitions

* `Cslib.BitString.longCode`: the long code of a label.
* `Cslib.BitString.IsOdd`: odd (folded) Boolean functions.
* `Cslib.BitString.foldTable`: folding a table around a coordinate.
* `Cslib.BitString.projectSet`: the mod-2 projection of a set along a map.
* `Cslib.BitString.longCodeSubcubeAccept`, `Cslib.BitString.longCodeSubcubeProb`: the two-query
  subcube test on a long-code table (`B f || !B g` for `g ≤ f`) and its acceptance probability.

## Main results

* `Cslib.BitString.longCode_eq_hadamardCode`, `Cslib.BitString.eq_of_hammingDist_longCode_lt`: the
  long code is a Hadamard code, and unique decoding of the long code.
* `Cslib.BitString.isOdd_longCode`, `Cslib.BitString.isOdd_foldTable`: long codes and folded
  tables are odd.
* `Cslib.BitString.IsOdd.fourierCoeff_empty`, `Cslib.BitString.IsOdd.fourierCoeff_of_even`: odd
  functions have no Fourier weight on sets of even cardinality.
* `Cslib.BitString.chi_comp_eq_chi_projectSet`: pulling a character back along a map.
* `Cslib.BitString.longCodeSubcubeProb_longCode`,
  `Cslib.BitString.longCodeSubcubeProb_hadamardCode`,
  `Cslib.BitString.longCodeSubcubeProb_hadamardCode_le`,
  `Cslib.BitString.longCodeSubcubeProb_le_of_linear`: every long code passes the subcube test with
  probability `1`, while every nonzero linear function `hadamardCode s` passes with probability
  `3 / 4 + (1 / 2) ^ (#{i | s i} + 1)` (`≤ 7 / 8` when `2 ≤ #{i | s i}`, i.e. whenever `B` is
  linear, nonzero, and not a long-code codeword).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*, draft of
  2007-01-08][AroraBarak07]
* [J. Håstad, *Some optimal inapproximability results*][Hastad2001]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

@[expose] public section

open Finset
open scoped BigOperators symmDiff

namespace Cslib.BitString

variable {ι α β γ : Type*}

/-! ### The long code -/

/-- The **long code** of a label `a : ι`: the dictator `r ↦ r a` on `ι → Bool`, that is, the
evaluation `Function.eval a` [Arora and Barak, Chapter 22][AroraBarak09]. It is the Hadamard
encoding of the unit vector of `a` (`longCode_eq_hadamardCode`). -/
def longCode (a : ι) : (ι → Bool) → Bool :=
  Function.eval a

/-- The long code of `a` reads the bit of `r` at `a`. -/
@[simp]
theorem longCode_apply (a : ι) (r : ι → Bool) : longCode a r = r a :=
  rfl

section Decoding

variable [Fintype ι] [DecidableEq ι]

/-- The long code of `a` is the Hadamard encoding of the unit vector of `a`. -/
theorem longCode_eq_hadamardCode (a : ι) : longCode a = hadamardCode (Pi.single a true) := by
  funext r
  rw [hadamardCode_comm, hadamardCode_single, longCode_apply]

/-- **Unique decoding of the long code**: a Boolean function within relative distance less than
`1/4` of the long codes of `a` and of `b` forces `a = b`. -/
theorem eq_of_hammingDist_longCode_lt {f : (ι → Bool) → Bool} {a b : ι}
    (ha : (hammingDist f (longCode a) : ℝ) / 2 ^ Fintype.card ι < 1 / 4)
    (hb : (hammingDist f (longCode b) : ℝ) / 2 ^ Fintype.card ι < 1 / 4) : a = b := by
  rw [longCode_eq_hadamardCode] at ha hb
  have h := congrFun (eq_of_hammingDist_hadamardCode_le (max_lt ha hb) (le_max_left _ _)
    (le_max_right _ _)) a
  simpa [Pi.single_apply, Bool.zero_eq_false] using h.symm

end Decoding

/-! ### Odd functions and folding -/

/-- In `±1` notation, the long code `longCode x` is the singleton character `chi ℝ {x}`. -/
theorem signVal_longCode (x : α) (f : α → Bool) :
    signVal (longCode x f) = chi ℝ {x} f :=
  (chi_singleton x f).symm

/-- A Boolean function `B : (α → Bool) → Bool` is **odd** when complementing the input
(`f + fun _ => true`) complements the output. In `±1` notation this says `F (-x) = -F x`; such
functions are also called self-dual, and odd long code tables are called *folded*. -/
def IsOdd (B : (α → Bool) → Bool) : Prop :=
  ∀ f : α → Bool, B (f + fun _ => true) = !B f

/-- Every long code `longCode x` is odd. -/
theorem isOdd_longCode (x : α) : IsOdd (longCode x) := fun f => by
  change (f x + true) = !(f x)
  cases f x <;> rfl

/-- **Folding a table** around the coordinate `x₀ : α`: it reads `B f` when `f x₀ = false` and
`!B (f + fun _ => true)` when `f x₀ = true`. -/
def foldTable (x₀ : α) (B : (α → Bool) → Bool) (f : α → Bool) : Bool :=
  if f x₀ then !B (f + fun _ => true) else B f

/-- Folding any table produces an odd table. -/
theorem isOdd_foldTable (x₀ : α) (B : (α → Bool) → Bool) : IsOdd (foldTable x₀ B) := by
  intro f
  have h1 : (f + fun _ : α => true) x₀ = !f x₀ := by
    change (f x₀ + true) = !f x₀
    cases f x₀ <;> rfl
  have h2 : (f + fun _ : α => true) + (fun _ : α => true) = f := by
    funext x
    change (f x + true) + true = f x
    cases f x <;> rfl
  simp only [foldTable, h1, h2]
  cases f x₀ <;> simp

/-- Folding an odd table leaves it unchanged. -/
theorem IsOdd.foldTable_eq {B : (α → Bool) → Bool} (hB : IsOdd B) (x₀ : α) :
    foldTable x₀ B = B := by
  funext f
  simp only [foldTable, hB f, Bool.not_not, ite_self]

/-- An odd function has Fourier coefficient `0` on every set of even cardinality. -/
theorem IsOdd.fourierCoeff_of_even [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsOdd B) {S : Finset α} (hS : Even #S) :
    fourierCoeff (fun f => signVal (B f)) S = 0 := by
  rw [fourierCoeff]
  have hchi : chi ℝ S (fun _ : α => true) = 1 := by
    rw [chi_eq_prod_signVal, prod_const]
    obtain ⟨m, hm⟩ := hS
    rw [hm, pow_add, ← mul_pow]
    norm_num
  have h1 : (𝔼 f : α → Bool, signVal (B f) * chi ℝ S f) =
      𝔼 f : α → Bool, signVal (B ((fun _ => true) + f)) * chi ℝ S ((fun _ => true) + f) :=
    (Fintype.expect_add_left (fun f : α → Bool => signVal (B f) * chi ℝ S f)
      (fun _ => true)).symm
  have h2 (f : α → Bool) :
      signVal (B ((fun _ => true) + f)) * chi ℝ S ((fun _ => true) + f) =
        -(signVal (B f) * chi ℝ S f) := by
    rw [add_comm (fun _ => true) f, hB f, signVal_not, chi_add, hchi]
    ring
  simp only [h2, expect_neg_distrib] at h1
  linarith

/-- **An odd function has zero empty Fourier coefficient**: its `±1` values at `f` and
`f + fun _ => true` cancel. This is the case `S = ∅` of `IsOdd.fourierCoeff_of_even`. -/
theorem IsOdd.fourierCoeff_empty [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsOdd B) : fourierCoeff (fun f => signVal (B f)) ∅ = 0 :=
  hB.fourierCoeff_of_even (by simp)

/-! ### Mod-2 projection of subsets and character pullback -/

section Projection

variable [Fintype γ] [DecidableEq γ]

/-- The **mod-2 projection** `π₂(T)` of `T : Finset β` along `π : β → γ`: the set of `y : γ`
whose fiber in `T` under `π` has odd cardinality [Håstad][Hastad2001]. -/
def projectSet (π : β → γ) (T : Finset β) : Finset γ :=
  univ.filter fun y => Odd #{x ∈ T | π x = y}

/-- `y` lies in the mod-2 projection of `T` exactly when its fiber in `T` has odd cardinality. -/
@[simp]
theorem mem_projectSet {π : β → γ} {T : Finset β} {y : γ} :
    y ∈ projectSet π T ↔ Odd #{x ∈ T | π x = y} := by
  simp [projectSet]

/-- The mod-2 projection of the empty set is empty. -/
@[simp]
theorem projectSet_empty (π : β → γ) : projectSet π ∅ = ∅ := by
  ext y
  simp [projectSet]

/-- Every element of `projectSet π T` lies in the image of `T` under `π`. -/
theorem exists_mem_of_mem_projectSet {π : β → γ} {T : Finset β} {y : γ}
    (hy : y ∈ projectSet π T) : ∃ x ∈ T, π x = y := by
  rw [mem_projectSet] at hy
  have hpos : 0 < #{x ∈ T | π x = y} := Nat.pos_of_ne_zero (by rintro h0; simp [h0] at hy)
  obtain ⟨x, hx⟩ := card_pos.1 hpos
  exact ⟨x, (mem_filter.1 hx).1, (mem_filter.1 hx).2⟩

/-- The mod-2 projection of `T` along `π` is contained in the image `T.image π`. -/
theorem projectSet_subset_image (π : β → γ) (T : Finset β) :
    projectSet π T ⊆ T.image π := fun y hy => by
  obtain ⟨x, hx, rfl⟩ := exists_mem_of_mem_projectSet hy
  exact mem_image_of_mem π hx

/-- The mod-2 projection never increases cardinality: `#(projectSet π T) ≤ #T`. -/
theorem card_projectSet_le (π : β → γ) (T : Finset β) : #(projectSet π T) ≤ #T :=
  (card_le_card (projectSet_subset_image π T)).trans card_image_le

variable [DecidableEq β]

/-- Inserting `x ∉ T` toggles `π x` in `projectSet π T`. -/
theorem projectSet_insert (π : β → γ) {x : β} {T : Finset β} (hx : x ∉ T) :
    projectSet π (insert x T) = symmDiff (projectSet π T) {π x} := by
  ext y
  rw [mem_projectSet, mem_symmDiff, mem_projectSet, mem_singleton, filter_insert]
  by_cases hxy : π x = y
  · subst hxy
    have hx' : x ∉ {z ∈ T | π z = π x} := fun h => hx (mem_filter.1 h).1
    simp only [↓reduceIte, card_insert_of_notMem hx', Nat.odd_add_one, not_true_eq_false,
      and_false, true_and, false_or]
  · have hyx : y ≠ π x := Ne.symm hxy
    simp [hxy, hyx]

omit [DecidableEq β] in
/-- **Pulling a character back along `π` projects the frequency set by `projectSet π`**:
`chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f`. -/
theorem chi_comp_eq_chi_projectSet (π : β → γ) (T : Finset β) (f : γ → Bool) :
    chi ℝ T (f ∘ π) = chi ℝ (projectSet π T) f := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert x T hx ih =>
    rw [projectSet_insert π hx, ← chi_mul_chi, chi_singleton, ← ih, chi_eq_prod_signVal,
      prod_insert hx, ← chi_eq_prod_signVal, Function.comp_apply, mul_comm]

end Projection

/-! ### The subcube test on the long code -/

/-- **The long-code subcube test predicate** ([Arora and Barak][AroraBarak07],
Chapter 18, Exercise 16(d)): on random `f, h : α → Bool`, if `B f = false`, check that
`B (fun i => f i && h i) = false` (where `fun i => f i && h i` is a uniformly random point in the
subcube `{g | ∀ i, g i ≤ f i}`); equivalently, `B (fun i => f i && h i) ≤ B f`
(`B f || !B (fun i => f i && h i)`). -/
def longCodeSubcubeAccept (B : (α → Bool) → Bool) (f h : α → Bool) : Bool :=
  B f || !B (fun i => f i && h i)

/-- Every long code passes `longCodeSubcubeAccept` on every query pair `(f, h)`. -/
@[simp]
theorem longCodeSubcubeAccept_longCode (x : α) (f h : α → Bool) :
    longCodeSubcubeAccept (longCode x) f h = true := by
  change f x || !(f x && h x) = true
  cases f x <;> cases h x <;> rfl

/-- Evaluating the character `chi ℝ S` at `fun i => f i && h i` restricts the frequency set `S` to
`{i ∈ S | f i}` on `h`. -/
theorem chi_and_eq_chi_filter (S : Finset α) (f h : α → Bool) :
    chi ℝ S (fun i => f i && h i) = chi ℝ {i ∈ S | f i} h := by
  rw [chi_eq_prod_signVal, chi_eq_prod_signVal, prod_filter]
  exact prod_congr rfl fun i _ => by cases f i <;> rfl

section SubcubeTest

variable [DecidableEq α]

private theorem ite_filter_eq_empty_eq_pow_mul_sum_powerset (S : Finset α) (f : α → Bool) :
    (if {i ∈ S | f i} = ∅ then (1 : ℝ) else 0) =
      (1 / 2 : ℝ) ^ #S * ∑ T ∈ S.powerset, chi ℝ T f := by
  have hprod : ∏ i ∈ S, (signVal (f i) + 1) = ∑ T ∈ S.powerset, chi ℝ T f := by
    have h := prod_add (fun i => signVal (f i)) (fun _ => (1 : ℝ)) S
    simp only [prod_const_one, mul_one, ← chi_eq_prod_signVal] at h
    exact h
  rw [← hprod, ← prod_const, ← prod_mul_distrib]
  split_ifs with hempty
  · symm
    refine prod_eq_one fun i hi => ?_
    have hfi : f i = false := by
      by_contra htrue
      exact notMem_empty i (hempty ▸ mem_filter.2 ⟨hi, Bool.eq_true_of_not_eq_false htrue⟩)
    norm_num [hfi]
  · obtain ⟨i, hi⟩ := nonempty_iff_ne_empty.2 hempty
    obtain ⟨hiS, hfi⟩ := mem_filter.1 hi
    exact (prod_eq_zero hiS (by simp [hfi])).symm

variable [Fintype α]

/-- **The long-code subcube test acceptance probability** ([Arora and Barak][AroraBarak07],
Chapter 18, Exercise 16(d)): the probability over independent uniform `f, h : α → Bool` that
`longCodeSubcubeAccept B f h = true`. -/
noncomputable def longCodeSubcubeProb (B : (α → Bool) → Bool) : ℝ :=
  𝔼 f : α → Bool, 𝔼 h : α → Bool, bitVal ℝ (longCodeSubcubeAccept B f h)

/-- **Completeness of the long-code subcube test** ([Arora and Barak][AroraBarak07],
Chapter 18, Exercise 16(d)): every long code passes the subcube test with probability `1`. -/
@[simp]
theorem longCodeSubcubeProb_longCode (x : α) :
    longCodeSubcubeProb (longCode x) = 1 := by
  simp [longCodeSubcubeProb, bitVal]

/-- For fixed `f : α → Bool`, the bitwise conjunction `fun i => f i && h i` with a uniform
`h : α → Bool` is uniformly distributed on the subcube `{g : α → Bool | ∀ i, g i ≤ f i}`: each
`g` in the subcube has fiber `{h | ∀ i, (h + g) i ≤ !f i}`, a coset of `{k | ∀ i, k i ≤ !f i}`. -/
theorem expect_and_eq_expect_filter_le (f : α → Bool) (φ : (α → Bool) → ℝ) :
    (𝔼 h : α → Bool, φ (fun i => f i && h i)) =
      𝔼 g ∈ ({g : α → Bool | ∀ i, g i ≤ f i} : Finset (α → Bool)), φ g := by
  classical
  set S : Finset (α → Bool) := {g : α → Bool | ∀ i, g i ≤ f i}
  set T : Finset (α → Bool) := {k : α → Bool | ∀ i, k i ≤ !f i}
  have hmaps : ∀ h ∈ (univ : Finset (α → Bool)), (fun i => f i && h i) ∈ S := fun h _ =>
    mem_filter.2 ⟨mem_univ _, fun i => by
      change (f i && h i) ≤ f i
      cases f i <;> cases h i <;> decide⟩
  have hfiber : ∀ g ∈ S, #{h : α → Bool | (fun i => f i && h i) = g} = #T := by
    intro g hg
    have hg' : ∀ i, g i ≤ f i := (mem_filter.1 hg).2
    have hiff : ∀ h : α → Bool, (fun i => f i && h i) = g ↔ h + g ∈ T := by
      intro h
      rw [funext_iff, mem_filter, and_iff_right (mem_univ _)]
      refine forall_congr' fun i => ?_
      have hgi := hg' i
      revert hgi
      change g i ≤ f i → ((f i && h i) = g i ↔ (h i + g i) ≤ !f i)
      cases f i <;> cases g i <;> cases h i <;> decide
    refine Finset.card_bij (fun h _ => h + g) (fun h hh => (hiff h).1 (mem_filter.1 hh).2)
      (fun h₁ _ h₂ _ h12 => add_right_cancel h12) (fun k hk => ⟨k + g, ?_, ?_⟩)
    · refine mem_filter.2 ⟨mem_univ _, (hiff (k + g)).2 ?_⟩
      convert hk using 1
      ext i
      change (k i + g i) + g i = k i
      cases k i <;> cases g i <;> rfl
    · ext i
      change (k i + g i) + g i = k i
      cases k i <;> cases g i <;> rfl
  have hcard : #S * #T = #(univ : Finset (α → Bool)) := by
    rw [← sum_const_nat hfiber, sum_card_fiberwise_eq_card_filter]
    exact congrArg card (filter_true_of_mem hmaps)
  have hsum : (∑ h : α → Bool, φ (fun i => f i && h i)) = (#T : ℝ) * ∑ g ∈ S, φ g := by
    rw [← sum_fiberwise_of_maps_to hmaps]
    have hinner : ∀ g ∈ S,
        (∑ h ∈ {h : α → Bool | (fun i => f i && h i) = g}, φ (fun i => f i && h i)) =
          (#T : ℝ) * φ g := by
      intro g hg
      rw [sum_congr rfl (fun h hh => congrArg φ (mem_filter.1 hh).2), sum_const, hfiber g hg,
        nsmul_eq_mul]
    rw [sum_congr rfl hinner, ← mul_sum]
  have hT0 : (#T : ℝ) ≠ 0 := by
    have h0 : (0 : α → Bool) ∈ T := mem_filter.2 ⟨mem_univ _, fun _ => Bool.false_le _⟩
    exact Nat.cast_ne_zero.2 (card_pos.2 ⟨0, h0⟩).ne'
  rw [expect_eq_sum_div_card, expect_eq_sum_div_card, hsum, ← hcard, Nat.cast_mul,
    mul_comm (#S : ℝ) (#T : ℝ), mul_div_mul_left _ _ hT0]

/-- The acceptance probability of the long-code subcube test equals the expectation over uniform
`f : α → Bool` and uniform `g` in the subcube `{g : α → Bool | ∀ i, g i ≤ f i}` of
`bitVal ℝ (B f || !B g)`. -/
theorem longCodeSubcubeProb_eq_expect_filter_le (B : (α → Bool) → Bool) :
    longCodeSubcubeProb B =
      𝔼 f : α → Bool, 𝔼 g ∈ ({g : α → Bool | ∀ i, g i ≤ f i} : Finset (α → Bool)),
        bitVal ℝ (B f || !B g) := by
  unfold longCodeSubcubeProb
  refine expect_congr rfl fun f _ => ?_
  exact expect_and_eq_expect_filter_le f (fun g => bitVal ℝ (B f || !B g))

/-- Averaging `chi ℝ S (fun i => f i && h i)` over independent uniform `f, h : α → Bool` yields
`(1 / 2) ^ #S`, the probability that `f` vanishes on `S`. -/
theorem expect_chi_and (S : Finset α) :
    (𝔼 f : α → Bool, 𝔼 h : α → Bool, chi ℝ S (fun i => f i && h i)) = (1 / 2 : ℝ) ^ #S := by
  simp only [chi_and_eq_chi_filter, expect_chi, ite_filter_eq_empty_eq_pow_mul_sum_powerset,
    ← mul_expect, expect_sum_comm]
  rw [sum_eq_single ∅ (fun T _ hT => ite_eq_right hT)
    (fun h => False.elim (h (mem_powerset.2 (empty_subset S)))), ite_eq_left rfl, mul_one]

/-- **Acceptance probability of the long-code subcube test on a nonzero linear function**
([Arora and Barak][AroraBarak07], Chapter 18, Exercise 16(d)): for any `s : α → Bool` with `s ≠ 0`,
the Hadamard codeword `hadamardCode s` passes the subcube test with probability
`3 / 4 + (1 / 2) ^ (#{i | s i} + 1)`. -/
theorem longCodeSubcubeProb_hadamardCode {s : α → Bool} (hs : s ≠ 0) :
    longCodeSubcubeProb (hadamardCode s) = 3 / 4 + (1 / 2 : ℝ) ^ (#{i | s i} + 1) := by
  set S : Finset α := {i | s i}
  have hS : S ≠ ∅ := by
    intro h0
    apply hs
    funext i
    by_contra hi
    exact notMem_empty i (h0 ▸ mem_filter.2 ⟨mem_univ i, Bool.eq_true_of_not_eq_false hi⟩)
  have hinner : ∀ f : α → Bool,
      (𝔼 h : α → Bool, bitVal ℝ (longCodeSubcubeAccept (hadamardCode s) f h)) =
        (3 : ℝ) / 4 - (1 / 4 : ℝ) * chi ℝ S f +
          (1 / 2 : ℝ) * (if {i ∈ S | f i} = ∅ then 1 else 0) := by
    intro f
    have hstep : ∀ h : α → Bool,
        bitVal ℝ (longCodeSubcubeAccept (hadamardCode s) f h) =
          (3 : ℝ) / 4 - (1 / 4 : ℝ) * chi ℝ S f +
            (1 / 4 : ℝ) * (1 + chi ℝ S f) * chi ℝ {i ∈ S | f i} h := by
      intro h
      rw [← chi_and_eq_chi_filter S f h, chi_eq_signVal_parityOn, chi_eq_signVal_parityOn]
      unfold longCodeSubcubeAccept
      rw [hadamardCode_eq_parityOn s]
      change bitVal ℝ (parityOn S f || !parityOn S (fun i => f i && h i)) = _
      cases parityOn S f <;> cases parityOn S (fun i => f i && h i) <;>
        simp [bitVal, signVal] <;> ring
    simp only [hstep, expect_add_distrib, expect_const univ_nonempty, mul_assoc, ← mul_expect,
      expect_chi]
    split_ifs with h0
    · have hchi1 : chi ℝ S f = 1 := by
        rw [chi_eq_prod_signVal]
        refine prod_eq_one fun i hi => ?_
        have hfi : f i = false := by
          by_contra htrue
          exact notMem_empty i (h0 ▸ mem_filter.2 ⟨hi, Bool.eq_true_of_not_eq_false htrue⟩)
        simp [hfi]
      rw [hchi1]
      ring
    · ring
  unfold longCodeSubcubeProb
  simp only [hinner, expect_add_distrib, expect_sub_distrib, expect_const univ_nonempty,
    ← mul_expect, expect_chi, ite_eq_right hS, ite_filter_eq_empty_eq_pow_mul_sum_powerset,
    expect_sum_comm]
  rw [sum_eq_single ∅ (fun T _ hT => ite_eq_right hT)
    (fun h => False.elim (h (mem_powerset.2 (empty_subset S)))), ite_eq_left rfl, pow_succ]
  ring

/-- **Soundness of the long-code subcube test against linear functions of weight at least `2`**
([Arora and Barak][AroraBarak07], Chapter 18, Exercise 16(d)): if `2 ≤ #{i | s i}`, then
`hadamardCode s` passes the subcube test with probability at most `7 / 8`. -/
theorem longCodeSubcubeProb_hadamardCode_le {s : α → Bool}
    (hs : 2 ≤ #{i | s i}) : longCodeSubcubeProb (hadamardCode s) ≤ 7 / 8 := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [Bool.zero_eq_false] at hs
  rw [longCodeSubcubeProb_hadamardCode hs0]
  have hpow : (1 / 2 : ℝ) ^ (#{i | s i} + 1) ≤ (1 / 2 : ℝ) ^ (2 + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right hs 1)
  linarith

/-- **Soundness of the long-code subcube test against nonzero non-dictator linear functions**
([Arora and Barak][AroraBarak07], Chapter 18, Exercise 16(d)): if `B : (α → Bool) → Bool` is a
linear function (`∀ f g, B (f + g) = (B f ^^ B g)`) that is nonzero and not a long-code codeword,
then `B` passes the subcube test with probability at most `7 / 8`. -/
theorem longCodeSubcubeProb_le_of_linear {B : (α → Bool) → Bool}
    (hlin : ∀ f g, B (f + g) = (B f ^^ B g)) (hB0 : B ≠ 0) (hnotLC : ∀ x, B ≠ longCode x) :
    longCodeSubcubeProb B ≤ 7 / 8 := by
  obtain ⟨s, rfl⟩ := exists_eq_hadamardCode_iff.2 hlin
  refine longCodeSubcubeProb_hadamardCode_le ?_
  have hs0 : ∃ x, s x = true := by
    by_contra! h
    apply hB0
    have hs : s = 0 := funext fun x => Bool.eq_false_iff.2 (h x)
    subst hs
    exact funext fun a => zero_dotProduct a
  obtain ⟨x, hx⟩ := hs0
  have hsx : ∃ y, y ≠ x ∧ s y = true := by
    by_contra! h
    apply hnotLC x
    rw [longCode_eq_hadamardCode]
    congr 1
    funext y
    by_cases hyx : y = x
    · subst hyx
      simp [hx]
    · simp [Pi.single_eq_of_ne hyx, Bool.zero_eq_false, Bool.eq_false_iff.2 (h y hyx)]
  obtain ⟨y, hyx, hy⟩ := hsx
  rw [← card_pair hyx.symm]
  refine card_le_card fun z hz => ?_
  rcases mem_insert.1 hz with rfl | hz
  · exact mem_filter.2 ⟨mem_univ _, hx⟩
  · rw [mem_singleton.1 hz]
    exact mem_filter.2 ⟨mem_univ _, hy⟩

end SubcubeTest

end Cslib.BitString
