/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Restrict
public import Mathlib.Logic.Function.DependsOn
import Complexity.Foundations.Data.Set.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rectangles, rectangle-free sets and bias

An *input* is a function `x : ι → U` from a type of coordinates to an alphabet. A set of
coordinates `X` cuts an input into two parts: its restriction to `X` and its restriction to the
complement `Xᶜ`. The *rectangle* with sides `A` and `B` is the set of inputs whose part on `X`
lies in `A` and whose part on `Xᶜ` lies in `B`: a combinatorial rectangle in the sense of
communication complexity, for the cut of the coordinates into `X` and `Xᶜ`.

A set of inputs `S` is `K`-*rectangle-free* when every rectangle inside `S`, for every cut of the
coordinates, has a side with fewer than `K` elements. This is the property of a hard set that the
worst-case frontier lower bounds use.

**Thick or small** (`exists_thick_or_ncard_lt`). A set that ignores coordinates carrying at least
`K` assignments is a rectangle with both sides of size at least `K`, or it has fewer than
`|U| K ^ 2` elements. Two consequences:

* **the support lemma** (`RectangleFree.pow_ncard_compl_lt`): a large rectangle-free set depends
  on all but fewer than `log_|U| K` coordinates;
* **bias on sets that ignore many coordinates**
  (`RectangleBias.abs_signedCount_le_of_dependsOn`).

The average-case lower bounds use a quantitative form of rectangle-freeness: `S` has *bias* at
most `b` on large rectangles (`RectangleBias`) when on every rectangle with both sides of size at
least `K`, the density of `S` is within `b` of `1/2`. Then the inputs of such a rectangle in `S`
and those outside `S` differ in number by at most a `2 b` fraction (`signedCount`).

## Main definitions

* `Cslib.Circuits.Frontier.rectangle`: the rectangle with sides `A` on `X` and `B` on `Xᶜ`.
* `Cslib.Circuits.Frontier.RectangleFree`: every rectangle inside `S` has a side with fewer
  than `K` elements.
* `Cslib.Circuits.Frontier.signedCount`: the inputs of `R` in `S` minus those outside `S`.
* `Cslib.Circuits.Frontier.RectangleBias`: on every rectangle with both sides of size at
  least `K`, the density of `S` is within `b` of `1/2`.

## Main results

* `Cslib.Circuits.Frontier.ncard_rectangle`: a rectangle has `|A| |B|` inputs.
* `Cslib.Circuits.Frontier.signedCount_eq_sum`: the signed count as a sum over the counted set.
* `Cslib.Circuits.Frontier.exists_thick_or_ncard_lt`: thick or small.
* `Cslib.Circuits.Frontier.RectangleFree.pow_ncard_compl_lt`: the support lemma.
* `Cslib.Circuits.Frontier.RectangleBias.abs_signedCount_le_of_dependsOn`: bias on a set that
  ignores many coordinates.
* `Cslib.Circuits.Frontier.rectangleBias_one_half`: every set has bias at most `1/2`.

## References

* [E. Kushilevitz, N. Nisan, *Communication Complexity*, Ch. 1][KushilevitzNisan1997]
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

open Set
open scoped Finset

variable {ι U : Type*}

/-- The *rectangle* with sides `A` and `B` for the cut `X`: the inputs whose part on `X` lies
in `A` and whose part on the complement `Xᶜ` lies in `B`. -/
def rectangle (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) : Set (ι → U) :=
  {x | X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B}

/-- An input `x` belongs to `rectangle X A B` iff its restriction to `X` belongs to `A` and its
restriction to `Xᶜ` belongs to `B`. -/
@[simp]
theorem mem_rectangle {X : Set ι} {A : Set (X → U)} {B : Set (↥Xᶜ → U)} {x : ι → U} :
    x ∈ rectangle X A B ↔ X.domRestrict x ∈ A ∧ Xᶜ.domRestrict x ∈ B :=
  Iff.rfl

/-- A rectangle has as many inputs as pairs of its sides. -/
theorem ncard_rectangle (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)) :
    (rectangle X A B).ncard = A.ncard * B.ncard := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U
  have hpre : rectangle X A B = e ⁻¹' (A ×ˢ B) := rfl
  rw [hpre, ncard_preimage_of_injective_subset_range e.injective (by simp [e.surjective.range_eq]),
    ncard_prod]

/-- An input is determined by its two parts: cutting along `X` is injective. -/
theorem domRestrict_prodMk_injective (X : Set ι) :
    Function.Injective fun x : ι → U => (X.domRestrict x, Xᶜ.domRestrict x) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (· ∈ X) fun _ => U).injective

/-- A set that does not depend on the coordinates in `D` is the rectangle whose side on `D` is
every assignment and whose side on `Dᶜ` is the set of its parts there. -/
theorem eq_rectangle_of_dependsOn {T : Set (ι → U)} {D : Set ι} (hD : DependsOn (· ∈ T) Dᶜ) :
    T = rectangle D univ (Dᶜ.domRestrict '' T) := by
  refine subset_antisymm (fun x hx => ⟨mem_univ _, x, hx, rfl⟩) ?_
  rintro z ⟨-, y, hy, hyz⟩
  have : (y ∈ T) = (z ∈ T) := hD fun i hi => congrFun hyz ⟨i, hi⟩
  exact this ▸ hy

/-- **Thick or small.** Let `T` depend only on the coordinates in `R`, and let the other
coordinates carry at least `K ≥ 1` assignments. Then `T` is a rectangle with both sides of size
at least `K`, or `T` has fewer than `|U| K ^ 2` elements.

Take a smallest set `D` of ignored coordinates carrying at least `K` assignments, so that
`|U| ^ |D| ≤ |U| (K - 1)`. Then `T` is the rectangle whose side on `D` is everything; if its
other side has fewer than `K` elements, `T` has at most `|U| ^ |D| (K - 1)` of them. -/
theorem exists_thick_or_ncard_lt [Finite ι] [Finite U] [Nonempty U] {T : Set (ι → U)}
    {R : Set ι} (hR : DependsOn (· ∈ T) R) {K : ℕ} (hK : 1 ≤ K)
    (hle : K ≤ Nat.card U ^ Rᶜ.ncard) :
    (∃ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
      T = rectangle X A B ∧ K ≤ A.ncard ∧ K ≤ B.ncard) ∨ T.ncard < Nat.card U * K ^ 2 := by
  have hq : 0 < Nat.card U := Nat.card_pos
  have hex : ∃ d, K ≤ Nat.card U ^ d := ⟨_, hle⟩
  obtain ⟨d, hdK, hdmin⟩ : ∃ d, K ≤ Nat.card U ^ d ∧ ∀ d' < d, Nat.card U ^ d' < K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun d' hd' => not_le.mp (Nat.find_min hex hd')⟩
  have hdR : d ≤ Rᶜ.ncard := by
    by_contra! h
    exact absurd hle (not_le.mpr (hdmin _ h))
  obtain ⟨D, hDR, rfl⟩ := exists_subset_card_eq hdR
  set B : Set (↥Dᶜ → U) := Dᶜ.domRestrict '' T
  have hT : T = rectangle D univ B :=
    eq_rectangle_of_dependsOn (hR.mono (subset_compl_comm.mp hDR))
  have hA : (univ : Set (D → U)).ncard = Nat.card U ^ D.ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
  by_cases hB : K ≤ B.ncard
  · exact Or.inl ⟨D, univ, B, hT, hA ▸ hdK, hB⟩
  refine Or.inr ?_
  have hcard : T.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := by
    calc T.ncard
        ≤ ((univ : Set (D → U)) ×ˢ B).ncard :=
          ncard_le_ncard_of_injOn _ (fun x hx => ⟨mem_univ _, x, hx, rfl⟩)
            (domRestrict_prodMk_injective D).injOn
      _ = Nat.card U ^ D.ncard * B.ncard := by rw [ncard_prod, hA]
      _ ≤ Nat.card U ^ D.ncard * (K - 1) := Nat.mul_le_mul_left _ (by omega)
  -- Minimality of `|D|` gives `|U| ^ |D| ≤ |U| (K - 1)` once `D` is nonempty.
  rcases Nat.eq_zero_or_pos D.ncard with hd | hd
  · rw [hd, pow_zero, one_mul] at hcard
    calc T.ncard ≤ K - 1 := hcard
      _ < K := by omega
      _ ≤ Nat.card U * K ^ 2 :=
          (Nat.le_self_pow two_ne_zero K).trans (Nat.le_mul_of_pos_left _ hq)
  · have hlt : Nat.card U ^ (D.ncard - 1) < K := hdmin _ (by omega)
    have hpow : Nat.card U ^ D.ncard = Nat.card U * Nat.card U ^ (D.ncard - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    calc T.ncard ≤ Nat.card U ^ D.ncard * (K - 1) := hcard
      _ ≤ Nat.card U * (K - 1) * (K - 1) := by
          rw [hpow]
          gcongr
          omega
      _ < Nat.card U * K ^ 2 := by
          rw [mul_assoc, sq]
          exact Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul'' (by omega) (by omega)) hq

/-! ### Rectangle-free sets -/

/-- A set of inputs `S` is `K`-*rectangle-free* when every rectangle contained in `S`, for
every cut of the coordinates, has a side with fewer than `K` elements.

Sides are counted with `Set.encard`, so that an infinite side is never small. Over finitely many
coordinates and a finite alphabet the sides may be counted with `Set.ncard` instead
(`rectangleFree_iff`). -/
def RectangleFree (S : Set (ι → U)) (K : ℕ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
    rectangle X A B ⊆ S → A.encard < K ∨ B.encard < K

namespace RectangleFree

variable {S T : Set (ι → U)} {K K' : ℕ}

/-- Inside a rectangle-free set, one side of every rectangle is a finite set with fewer than `K`
elements. -/
theorem ncard_lt_or (hS : RectangleFree S K) (X : Set ι) (A : Set (X → U))
    (B : Set (↥Xᶜ → U)) (hAB : rectangle X A B ⊆ S) : A.ncard < K ∨ B.ncard < K :=
  (hS X A B hAB).imp (fun h => (encard_lt_coe_iff_finite_ncard_lt.mp h).2)
    fun h => (encard_lt_coe_iff_finite_ncard_lt.mp h).2

/-- The threshold of a rectangle-free set is positive: the empty rectangle has empty sides. -/
theorem pos (h : RectangleFree S K) : 0 < K := by
  rcases h univ ∅ ∅ (by simp [rectangle]) with h | h <;> simpa using h

/-- A nonempty `K`-rectangle-free set has `1 < K`: a single input is a rectangle with sides of
one element each, for the cut of the coordinates into all and none. -/
theorem one_lt (h : RectangleFree S K) (hS : S.Nonempty) : 1 < K := by
  obtain ⟨x, hx⟩ := hS
  have hsub : rectangle univ {univ.domRestrict x} {(univ : Set ι)ᶜ.domRestrict x} ⊆ S := by
    rintro y ⟨hy, -⟩
    obtain rfl : y = x := funext fun i => congrFun (mem_singleton_iff.mp hy) ⟨i, mem_univ i⟩
    exact hx
  simpa using h.ncard_lt_or _ _ _ hsub

/-- A subset of a rectangle-free set is rectangle-free. -/
theorem subset (h : RectangleFree S K) (hTS : T ⊆ S) : RectangleFree T K :=
  fun X A B hAB => h X A B (hAB.trans hTS)

/-- Raising the threshold keeps a set rectangle-free. -/
theorem mono (h : RectangleFree S K) (hK : K ≤ K') : RectangleFree S K' :=
  fun X A B hAB => (h X A B hAB).imp (·.trans_le (by exact_mod_cast hK))
    (·.trans_le (by exact_mod_cast hK))

/-- **The support lemma.** A `K`-rectangle-free set with at least `|U| * K ^ 2` elements depends
on all but fewer than `log_|U| K` coordinates: if `S` depends only on the coordinates in `R`,
then `|U| ^ |Rᶜ| < K`. -/
theorem pow_ncard_compl_lt [Finite ι] [Finite U] [Nonempty U] (hS : RectangleFree S K)
    {R : Set ι} (hR : DependsOn (· ∈ S) R) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ Rᶜ.ncard < K := by
  by_contra! hle
  rcases exists_thick_or_ncard_lt hR hS.pos hle with ⟨X, A, B, hSAB, hA, hB⟩ | h
  · rcases hS.ncard_lt_or X A B hSAB.symm.subset with h | h <;> omega
  · omega

end RectangleFree

/-- Over finitely many coordinates and a finite alphabet, a set is `K`-rectangle-free exactly
when every rectangle inside it has a side with fewer than `K` elements counted with `ncard`. -/
theorem rectangleFree_iff [Finite ι] [Finite U] {S : Set (ι → U)} {K : ℕ} :
    RectangleFree S K ↔ ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)),
      rectangle X A B ⊆ S → A.ncard < K ∨ B.ncard < K := by
  refine ⟨RectangleFree.ncard_lt_or, fun h X A B hAB => ?_⟩
  exact (h X A B hAB).imp (fun h => encard_lt_coe_iff_finite_ncard_lt.mpr ⟨toFinite _, h⟩)
    fun h => encard_lt_coe_iff_finite_ncard_lt.mpr ⟨toFinite _, h⟩

/-! ### Bias -/

/-- The *signed count* of `S` on `R`: the number of inputs of `R` in `S` minus the number of
inputs of `R` outside `S`. -/
noncomputable def signedCount (S R : Set (ι → U)) : ℝ :=
  ((R ∩ S).ncard : ℝ) - (R \ S).ncard

/-- The signed count of `S` on `R` is the sum of `±1` over `R`: `+1` on the inputs in `S` and `-1`
on the others. -/
theorem signedCount_eq_sum [Fintype ι] [Fintype U] [DecidableEq ι] (S R : Set (ι → U))
    [DecidablePred (· ∈ S)] [DecidablePred (· ∈ R)] :
    signedCount S R = ∑ x with x ∈ R, if x ∈ S then (1 : ℝ) else -1 := by
  have h₁ : (R ∩ S).toFinset = Finset.univ.filter fun x => x ∈ R ∧ x ∈ S := by
    ext x
    simp
  have h₂ : (R \ S).toFinset = Finset.univ.filter fun x => x ∈ R ∧ x ∉ S := by
    ext x
    simp
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one,
    mul_neg_one, signedCount, ncard_eq_toFinset_card', ncard_eq_toFinset_card', h₁, h₂,
    Finset.filter_filter, Finset.filter_filter, sub_eq_add_neg]

section Finite

variable [Finite ι] [Finite U]

/-- A signed count is at most the size of the set counted. -/
theorem abs_signedCount_le (S R : Set (ι → U)) : |signedCount S R| ≤ R.ncard := by
  have : ((R ∩ S).ncard : ℝ) + (R \ S).ncard = R.ncard := by
    exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard R S
  rw [signedCount, abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (R ∩ S).ncard,
    Nat.cast_nonneg (α := ℝ) (R \ S).ncard]

/-- Signed counts add over a set `R` and its complement in a larger set `D`. -/
theorem signedCount_eq_add_sdiff (S : Set (ι → U)) {R D : Set (ι → U)} (h : R ⊆ D) :
    signedCount S D = signedCount S R + signedCount S (D \ R) := by
  have hsplit (P : Set (ι → U)) : D ∩ P = (R ∩ P) ∪ ((D \ R) ∩ P) := by
    ext x
    simp only [mem_inter_iff, mem_union, mem_sdiff]
    have := @h x
    tauto
  have hdisj (P : Set (ι → U)) : Disjoint (R ∩ P) ((D \ R) ∩ P) :=
    disjoint_left.mpr fun x hx hx' => hx'.1.2 hx.1
  have hi := ncard_union_eq (hdisj S)
  have hd := ncard_union_eq (hdisj Sᶜ)
  rw [← hsplit] at hi hd
  simp only [← sdiff_eq] at hd
  rw [signedCount, signedCount, signedCount, hi, hd]
  push_cast
  ring

/-- The signed count is twice the deviation of `|R ∩ S|` from `|R| / 2`. -/
private theorem signedCount_eq_two_mul (S R : Set (ι → U)) :
    signedCount S R = 2 * (((R ∩ S).ncard : ℝ) - R.ncard / 2) := by
  have : ((R ∩ S).ncard : ℝ) + (R \ S).ncard = R.ncard := by
    exact_mod_cast ncard_inter_add_ncard_sdiff_eq_ncard R S
  rw [signedCount]
  linarith

end Finite

/-- A set of inputs `S` has *bias at most `b`* on rectangles with both sides of size at least
`K` when on every such rectangle `R`, for every cut of the coordinates, the density of `S` is
within `b` of `1/2`:

`| |R ∩ S| - |R| / 2 | ≤ b |R|`.

Sizes are counted with `Set.ncard`, so the notion is meant for finitely many coordinates and a
finite alphabet. -/
def RectangleBias (S : Set (ι → U)) (K : ℕ) (b : ℝ) : Prop :=
  ∀ (X : Set ι) (A : Set (X → U)) (B : Set (↥Xᶜ → U)), K ≤ A.ncard → K ≤ B.ncard →
    |((rectangle X A B ∩ S).ncard : ℝ) - (rectangle X A B).ncard / 2| ≤
      b * (rectangle X A B).ncard

/-- **Every set has bias at most `1/2`**: the size of `R ∩ S` lies between `0` and `|R|`. -/
theorem rectangleBias_one_half [Finite ι] [Finite U] (S : Set (ι → U)) (K : ℕ) :
    RectangleBias S K (1 / 2) := by
  intro X A B _ _
  have h₁ : ((rectangle X A B ∩ S).ncard : ℝ) ≤ (rectangle X A B).ncard := by
    exact_mod_cast ncard_le_ncard inter_subset_left (toFinite _)
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (rectangle X A B ∩ S).ncard]

namespace RectangleBias

variable {S : Set (ι → U)} {K K' : ℕ} {b : ℝ}

/-- A bias bound for rectangles with sides of size at least `K` holds for larger sides. -/
theorem mono (h : RectangleBias S K b) (hK : K ≤ K') : RectangleBias S K' b :=
  fun X A B hA hB => h X A B (hK.trans hA) (hK.trans hB)

variable [Finite ι] [Finite U]

/-- On a rectangle with both sides of size at least `K`, a set with bias at most `b` has signed
count at most `2 b` times the size of the rectangle. -/
theorem abs_signedCount_rectangle_le (hS : RectangleBias S K b) {X : Set ι} {A : Set (X → U)}
    {B : Set (↥Xᶜ → U)} (hA : K ≤ A.ncard) (hB : K ≤ B.ncard) :
    |signedCount S (rectangle X A B)| ≤ 2 * b * (rectangle X A B).ncard := by
  rw [signedCount_eq_two_mul, abs_mul, abs_two]
  linarith [hS X A B hA hB]

/-- A bias bound is nonnegative once half of the coordinates carry at least `K` assignments:
the whole input space is then a rectangle with both sides of size at least `K`. -/
theorem nonneg [Nonempty U] (hS : RectangleBias S K b) (hK : K ≤ Nat.card U ^ (Nat.card ι / 2)) :
    0 ≤ b := by
  obtain ⟨X, -, hX⟩ := exists_subset_card_eq (s := (univ : Set ι)) (n := Nat.card ι / 2)
    (by rw [ncard_univ]; exact Nat.div_le_self _ _)
  have hXc : Nat.card ι / 2 ≤ Xᶜ.ncard := by
    have := ncard_add_ncard_compl X
    omega
  have hA : K ≤ (univ : Set (X → U)).ncard := by
    rwa [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq, hX]
  have hB : K ≤ (univ : Set (↥Xᶜ → U)).ncard := by
    rw [ncard_univ, Nat.card_fun, Nat.card_coe_set_eq]
    exact hK.trans (Nat.pow_le_pow_right Nat.card_pos hXc)
  have hR : (0 : ℝ) < (rectangle X (univ : Set (X → U)) univ).ncard := by
    rw [show rectangle X (univ : Set (X → U)) univ = univ by ext; simp [rectangle], ncard_univ]
    exact_mod_cast Nat.card_pos
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hS X univ univ hA hB)) hR

/-- **Bias on a set that ignores many coordinates.** If `T` depends only on the coordinates in
`R` and the others carry at least `K ≥ 1` assignments, then either `T` is a rectangle with both
sides of size at least `K`, on which `S` has bias at most `b`, or `T` is small. Either way the
signed count of `S` on `T` is at most `2 b |T| + |U| K ^ 2`. -/
theorem abs_signedCount_le_of_dependsOn [Nonempty U] (hS : RectangleBias S K b) (hb : 0 ≤ b)
    {T : Set (ι → U)} {R : Set ι} (hR : DependsOn (· ∈ T) R) (hK : 1 ≤ K)
    (hle : K ≤ Nat.card U ^ Rᶜ.ncard) :
    |signedCount S T| ≤ 2 * b * T.ncard + (Nat.card U * K ^ 2 : ℕ) := by
  rcases exists_thick_or_ncard_lt hR hK hle with ⟨X, A, B, rfl, hA, hB⟩ | h
  · exact (hS.abs_signedCount_rectangle_le hA hB).trans
      (le_add_of_nonneg_right (Nat.cast_nonneg _))
  · have : (T.ncard : ℝ) ≤ (Nat.card U * K ^ 2 : ℕ) := by exact_mod_cast h.le
    linarith [abs_signedCount_le S T, mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * b)
      (Nat.cast_nonneg (α := ℝ) T.ncard)]

end RectangleBias

end Cslib.Circuits.Frontier
