/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Communication.Lifting.Gadget
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Basic.Real.Basic
import Complexity.Foundations.Combinatorics.Janson
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Dense pointer sets and the full-range lemma

A set `X` of Alice's pointer vectors `x : Fin n → Fin m` is `τ`-*dense* on a set `F` of
coordinates (`Communication.Lifting.IsDense`) when no assignment to a nonempty set `I ⊆ F` of
coordinates is shared by more than a `τ ^ (-#I)` fraction of `X`. This is blockwise min-entropy
`log₂ τ` [Göös, Pitassi and Watson 2017][GoosPitassiWatson2017], [Mertz and Pitassi,
Definition 2.2][MertzPitassi2020].

**Full range.** Let `X` be `r`-dense on `F`, let `Y` be a set of Bob's inputs with at most `D`
bits of deficiency on the blocks in `F`, and let `16 #F (D + 1) ≤ r`. If both sets are fixed
outside `F`, then some pair `(x, y) ∈ X × Y` gives the index gadget the value `β x` on `F`, for
any target values `β x` (`Communication.Lifting.exists_forall_eq_of_isDense`)
[Mertz and Pitassi, Lemma 3.2][MertzPitassi2020]. The pointer vectors of `X`, read as sets of
pointers into the blocks, form an `r`-spread family. So few sets of Bob's ones avoid every
target pattern (`Cslib.card_filter_avoidsPatterns_mul_two_pow_le_of_spread`), and `Y` is too
large to avoid them all. Mertz and Pitassi use the blockwise approximate sunflower lemma for this
step and need only `r ≥ C #F log (#F / ε)`. The greedy Janson bound used here needs the larger
spread `r ≥ 16 #F (D + 1)`, which still allows gadget size polynomial in `n`.

## Main definitions

* `Cslib.Communication.Lifting.IsDense`: blockwise density of a set of pointer vectors.

## Main results

* `Cslib.Communication.Lifting.IsDense.of_subset`: large subsets of dense sets are dense.
* `Cslib.Communication.Lifting.exists_forall_eq_of_isDense`: the full-range lemma.

## References

* [I. Mertz and T. Pitassi, *Lifting: As Easy As 1, 2, 3*][MertzPitassi2020]
* [M. Göös, T. Pitassi and T. Watson, *Query-to-communication lifting for
  BPP*][GoosPitassiWatson2017]
-/

@[expose] public section

namespace Cslib.Communication.Lifting

open Finset

variable {n m : ℕ}

/-- `X` is `τ`-dense on the coordinates `F`: for every nonempty `I ⊆ F` and every assignment `α`,
at most a `τ ^ (-#I)` fraction of `X` agrees with `α` on `I`. -/
def IsDense (τ : ℝ) (F : Finset (Fin n)) (X : Finset (Fin n → Fin m)) : Prop :=
  ∀ I ⊆ F, I.Nonempty → ∀ α : Fin n → Fin m,
    (#(X.filter fun x => ∀ i ∈ I, x i = α i) : ℝ) * τ ^ #I ≤ #X

/-- A subset holding at least a `1 / c` fraction of a `τ`-dense set is `τ / c`-dense. -/
theorem IsDense.of_subset {τ c : ℝ} {F : Finset (Fin n)} {X X' : Finset (Fin n → Fin m)}
    (hX : IsDense τ F X) (hτ : 0 ≤ τ) (hc : 1 ≤ c) (hsub : X' ⊆ X) (hcard : (#X : ℝ) ≤ c * #X') :
    IsDense (τ / c) F X' := by
  intro I hI hne α
  have hc0 : 0 < c := by linarith
  have h1 := hX I hI hne α
  have h2 : (#(X'.filter fun x => ∀ i ∈ I, x i = α i) : ℝ) ≤
      #(X.filter fun x => ∀ i ∈ I, x i = α i) := by
    exact_mod_cast card_le_card (filter_subset_filter _ hsub)
  have hcI : c ≤ c ^ #I := le_self_pow₀ hc (card_ne_zero.mpr hne)
  have h3 : (τ / c) ^ #I * c ≤ τ ^ #I := by
    rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left hcI (by positivity)
  have h4 : (0 : ℝ) ≤ (τ / c) ^ #I := by positivity
  have h5 : (0 : ℝ) ≤ #(X'.filter fun x => ∀ i ∈ I, x i = α i) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h3 h5, mul_le_mul_of_nonneg_right h2 h4]

/-- A set dense on `F` is dense on every subset of `F`. -/
theorem IsDense.mono {τ : ℝ} {F F' : Finset (Fin n)} {X : Finset (Fin n → Fin m)}
    (hX : IsDense τ F X) (hF : F' ⊆ F) : IsDense τ F' X :=
  fun I hI => hX I (hI.trans hF)

section FullRange

/-- The pointer of `x` into block `i`, for `i ∈ F`, as a pointer into the free blocks. -/
private def pointerGraph (F : Finset (Fin n)) (x : Fin n → Fin m) : Finset (F × Fin m) :=
  univ.map ⟨fun i => (i, x i), fun _ _ h => (Prod.mk.inj h).1⟩

private theorem mem_pointerGraph {F : Finset (Fin n)} {x : Fin n → Fin m} {p : F × Fin m} :
    p ∈ pointerGraph F x ↔ x p.1 = p.2 := by
  simp only [pointerGraph, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩; rfl
  · intro h; exact ⟨p.1, Prod.ext rfl h⟩

private theorem card_pointerGraph (F : Finset (Fin n)) (x : Fin n → Fin m) :
    #(pointerGraph F x) = #F := by
  simp [pointerGraph]

/-- The ones of Bob's input in the blocks of `F`. -/
private def onesOn (F : Finset (Fin n)) (y : Fin n → Fin m → Bool) : Finset (F × Fin m) :=
  univ.filter fun p => y p.1 p.2 = true

/-- When `X` is fixed outside `F`, `pointerGraph F` is injective on `X`. -/
private theorem pointerGraph_injOn {F : Finset (Fin n)} {X : Finset (Fin n → Fin m)}
    (hXfix : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∉ F, x i = x' i) :
    Set.InjOn (pointerGraph F) (X : Set (Fin n → Fin m)) := by
  intro x hx x' hx' h
  funext i
  by_cases hi : i ∈ F
  · have : (⟨i, hi⟩, x i) ∈ pointerGraph F x' := h ▸ mem_pointerGraph.mpr rfl
    exact (mem_pointerGraph.mp this).symm
  · exact hXfix x hx x' hx' i hi

/-- When `X` is `r`-dense on `F` and fixed outside `F`, the pointer graphs of `X` are `r`-spread:
at most `#(X.image (pointerGraph F)) / r ^ #T` pointer graphs contain a nonempty set `T`. -/
private theorem card_filter_subset_image_pointerGraph_mul_pow_le {F : Finset (Fin n)}
    {X : Finset (Fin n → Fin m)} {r : ℝ} (hr : 0 < r)
    (hXfix : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∉ F, x i = x' i) (hdense : IsDense r F X)
    (T : Finset (F × Fin m)) (hT : T.Nonempty) :
    (#((X.image (pointerGraph F)).filter (T ⊆ ·)) : ℝ) * r ^ #T ≤
      #(X.image (pointerGraph F)) := by
  classical
  set Xh := X.image (pointerGraph F)
  have hXh : #Xh = #X := card_image_of_injOn (pointerGraph_injOn hXfix)
  by_cases hex : ∃ x₀ ∈ X, T ⊆ pointerGraph F x₀
  · obtain ⟨x₀, hx₀, hTx₀⟩ := hex
    set I : Finset (Fin n) := T.image fun p => p.1.1
    have hIF : I ⊆ F := by
      intro i hi
      obtain ⟨p, -, rfl⟩ := mem_image.mp hi
      exact p.1.2
    have hIT : #I = #T := by
      refine card_image_of_injOn fun p hp q hq h => ?_
      have hp' := mem_pointerGraph.mp (hTx₀ hp)
      have hq' := mem_pointerGraph.mp (hTx₀ hq)
      have h1 : p.1 = q.1 := Subtype.ext h
      exact Prod.ext h1 (by rw [← hp', ← hq', h1])
    have hfilt : Xh.filter (T ⊆ ·) ⊆
        (X.filter fun x => ∀ i ∈ I, x i = x₀ i).image (pointerGraph F) := by
      intro s hs
      obtain ⟨hsXh, hTs⟩ := mem_filter.mp hs
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hsXh
      refine mem_image.mpr ⟨x, mem_filter.mpr ⟨hx, fun i hi => ?_⟩, rfl⟩
      obtain ⟨p, hp, rfl⟩ := mem_image.mp hi
      rw [mem_pointerGraph.mp (hTs hp), mem_pointerGraph.mp (hTx₀ hp)]
    have h1 : (#(Xh.filter (T ⊆ ·)) : ℝ) ≤ #(X.filter fun x => ∀ i ∈ I, x i = x₀ i) := by
      exact_mod_cast (card_le_card hfilt).trans card_image_le
    have h2 := hdense I hIF (hT.image _) x₀
    rw [hIT] at h2
    rw [hXh]
    nlinarith [pow_pos hr #T]
  · push Not at hex
    have : Xh.filter (T ⊆ ·) = ∅ := by
      refine filter_eq_empty_iff.mpr fun s hs hTs => ?_
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
      exact hex x hx hTs
    rw [this, card_empty, Nat.cast_zero, zero_mul]
    positivity

/-- When `Y` is fixed outside `F`, `onesOn F` is injective on `Y`. -/
private theorem onesOn_injOn {F : Finset (Fin n)} {Y : Finset (Fin n → Fin m → Bool)}
    (hYfix : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ i ∉ F, y i = y' i) :
    Set.InjOn (onesOn F) (Y : Set (Fin n → Fin m → Bool)) := by
  intro y hy y' hy' h
  funext i a
  by_cases hi : i ∈ F
  · have := congrArg (fun s => (⟨i, hi⟩, a) ∈ s) h
    simp only [onesOn, mem_filter, mem_univ, true_and, eq_iff_iff] at this
    cases hya : y i a <;> cases hya' : y' i a <;> simp_all
  · rw [hYfix y hy y' hy' i hi]

/-- **The full-range lemma.** Let `X` be `r`-dense on `F` and let `Y` have at most `D` bits of
deficiency on the blocks of `F`, with `16 #F (D + 1) ≤ r`, both fixed outside `F`. Then for any
target values `β x`, some `x ∈ X` and `y ∈ Y` give the index gadget the value `β x` on `F`
[Mertz and Pitassi, Lemma 3.2][MertzPitassi2020]. -/
theorem exists_forall_eq_of_isDense {F : Finset (Fin n)} {X : Finset (Fin n → Fin m)}
    {Y : Finset (Fin n → Fin m → Bool)} {r : ℝ} {D : ℕ} (hr : 0 < r) (hX : X.Nonempty)
    (hXfix : ∀ x ∈ X, ∀ x' ∈ X, ∀ i ∉ F, x i = x' i) (hdense : IsDense r F X)
    (hYfix : ∀ y ∈ Y, ∀ y' ∈ Y, ∀ i ∉ F, y i = y' i)
    (hY : (2 : ℝ) ^ (#F * m) ≤ 2 ^ D * #Y) (hrD : 16 * #F * (D + 1) ≤ r)
    (β : (Fin n → Fin m) → Fin n → Bool) :
    ∃ x ∈ X, ∃ y ∈ Y, ∀ i ∈ F, y i (x i) = β x i := by
  classical
  by_contra hcon
  push Not at hcon
  -- the pointer sets of `X`
  have hGinj := pointerGraph_injOn hXfix
  set Xh := X.image (pointerGraph F)
  have hcardXh : ∀ s ∈ Xh, #s = #F := by
    intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.mp hs
    exact card_pointerGraph F x
  have hspread := card_filter_subset_image_pointerGraph_mul_pow_le hr hXfix hdense
  -- the target patterns
  set βh : Finset (F × Fin m) → F × Fin m → Bool := fun s p =>
    if h : ∃ x ∈ X, pointerGraph F x = s then β h.choose p.1.1 else false
  have hβh : ∀ x ∈ X, ∀ p, βh (pointerGraph F x) p = β x p.1.1 := by
    intro x hx p
    have h : ∃ x' ∈ X, pointerGraph F x' = pointerGraph F x := ⟨x, hx, rfl⟩
    simp only [βh]
    rw [dite_eq_left_of_eq_true (eq_true h), hGinj h.choose_spec.1 hx h.choose_spec.2]
  have hbound := card_filter_avoidsPatterns_mul_two_pow_le_of_spread hr hspread hcardXh
    (hX.image _) (D := D) (by simpa using hrD) βh
  -- every `y ∈ Y` avoids the patterns
  have hmaps : Y.image (onesOn F) ⊆
      (univ : Finset (Finset (F × Fin m))).filter (AvoidsPatterns Xh id βh) := by
    intro s hs
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hs
    refine mem_filter.mpr ⟨mem_univ _, fun t ht => ?_⟩
    obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
    obtain ⟨i, hi, hne⟩ := hcon x hx y hy
    refine ⟨(⟨i, hi⟩, x i), mem_pointerGraph.mpr rfl, ?_⟩
    rw [hβh x hx]
    simpa [onesOn] using hne
  have hY' : (#Y : ℝ) ≤
      #((univ : Finset (Finset (F × Fin m))).filter (AvoidsPatterns Xh id βh)) := by
    rw [← card_image_of_injOn (onesOn_injOn hYfix)]
    exact_mod_cast card_le_card hmaps
  have hU : Fintype.card (F × Fin m) = #F * m := by simp
  have hpow : (2 : ℝ) ^ (D + 1) = 2 * 2 ^ D := by rw [pow_succ, mul_comm]
  rw [hU, hpow] at hbound
  nlinarith [mul_le_mul_of_nonneg_left hY' (by positivity : (0 : ℝ) ≤ 2 ^ D),
    (by positivity : (0 : ℝ) < 2 ^ (#F * m))]

end FullRange

end Cslib.Communication.Lifting
