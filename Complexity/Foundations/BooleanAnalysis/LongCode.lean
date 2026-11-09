/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.Fourier
public import Complexity.Foundations.Data.Code.Hadamard
import Complexity.Foundations.Data.Finset.Expect
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

## Main results

* `Cslib.BitString.longCode_eq_hadamardCode`, `Cslib.BitString.eq_of_hammingDist_longCode_lt`: the
  long code is a Hadamard code, and unique decoding of the long code.
* `Cslib.BitString.isOdd_longCode`, `Cslib.BitString.isOdd_foldTable`: long codes and folded
  tables are odd.
* `Cslib.BitString.IsOdd.fourierCoeff_empty`, `Cslib.BitString.IsOdd.fourierCoeff_of_even`: odd
  functions have no Fourier weight on sets of even cardinality.
* `Cslib.BitString.chi_comp_eq_chi_projectSet`: pulling a character back along a map.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
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

/-- **An odd function has zero empty Fourier coefficient**: its `±1` values at `f` and
`f + fun _ => true` cancel. -/
theorem IsOdd.fourierCoeff_empty [Fintype α] [DecidableEq α] {B : (α → Bool) → Bool}
    (hB : IsOdd B) : fourierCoeff (fun f => signVal (B f)) ∅ = 0 := by
  rw [BitString.fourierCoeff_empty]
  have h1 : (𝔼 f : α → Bool, signVal (B f)) =
      𝔼 f : α → Bool, signVal (B ((fun _ => true) + f)) :=
    (Fintype.expect_add_left (fun f : α → Bool => signVal (B f)) (fun _ => true)).symm
  have h2 (f : α → Bool) : signVal (B ((fun _ => true) + f)) = -signVal (B f) := by
    rw [add_comm (fun _ => true) f, hB f, signVal_not]
  simp only [h2, expect_neg_distrib] at h1
  linarith

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

end Cslib.BitString
