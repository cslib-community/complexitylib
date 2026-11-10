/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.EXP
public import Complexity.Computability.Complexity.Classes.Ladner.Basic
import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Order.Filter.AtTopBot.Finite

/-!
# Resource-bounded measure

Lutz's resource-bounded measure [Lutz][Lutz1992] makes "most languages in exponential time"
precise. A language `A ⊆ {0,1}*` is identified with its characteristic sequence along the standard
enumeration `s₀ = λ, s₁ = 0, s₂ = 1, s₃ = 00, s₄ = 01, …` of binary words, ordered by length and
then lexicographically (`Cslib.Complexity.Measure.stdWord`). The first `n` bits of that sequence
are `Cslib.Complexity.Measure.charPrefix A n`.

A **martingale** (`Cslib.Complexity.Measure.IsMartingale`) is a nonnegative function
`d : {0,1}* → ℝ` with `d w = (d (w0) + d (w1)) / 2`: the capital of a gambler betting on the
successive bits of a hidden sequence with fair payoffs. It **succeeds** on `A` when its capital
along the prefixes of the characteristic sequence of `A` is unbounded, equivalently has limit
superior `∞` (`Cslib.Complexity.Measure.successSet`,
`Cslib.Complexity.Measure.mem_successSet_iff_limsup`).

A **p-martingale** (`Cslib.Complexity.Measure.IsPMartingale`) is a martingale with a
polynomial-time approximation: a function `dhat : ℕ × {0,1}* → ℕ`, computable in time polynomial
in `r + |w|` with the precision `r` in unary, such that `|dhat (r, w) / 2 ^ r - d w| ≤ 2 ^ (-r)`.
A class `X` of languages has **p-measure zero** (`Cslib.Complexity.Measure.HasPMeasureZero`) when
some p-martingale succeeds on every member of `X`, and **measure zero in `E`**
(`Cslib.Complexity.Measure.HasMeasureZeroInE`) when `X ∩ E` has p-measure zero.

The p-measure-zero classes are closed under subsets and finite unions
(`Cslib.Complexity.Measure.HasPMeasureZero.mono`, `Cslib.Complexity.Measure.HasPMeasureZero.union`,
`Cslib.Complexity.Measure.hasPMeasureZero_biUnion`): a sum of p-martingales is a p-martingale,
and it succeeds wherever a summand does. The Measure Conservation Theorem, that `E` does not have
p-measure zero, is in `Complexity.Computability.Complexity.Classes.Measure.Conservation`; the
p-measure zero of each class `DTIME (2 ^ (k * n))` is in
`Complexity.Computability.Complexity.Classes.Measure.DTIME`.

## Source conventions

Lutz [Lutz][Lutz1992] (Definitions 3.1–3.7) works with density systems and approximations with
values in the nonnegative dyadic rationals, and proves that this is equivalent to the martingale
formulation (Theorem 3.19). The martingale formulation used here is that of the survey
[Lutz][Lutz1997] (Section 3) and of Juedes and Lutz [Juedes and Lutz][JuedesLutz1995b]
(Section 3): `d̂ : ℕ × {0,1}* → ℚ` computable in time polynomial in `r + |w|`, with
`|d̂ r w - d w| ≤ 2 ^ (-r)`. Here the approximation returns a natural number `dhat (r, w)`, in
binary, standing for the dyadic rational `dhat (r, w) / 2 ^ r`. The two forms are equivalent:
rounding `d̂ (r + 2) w` to the nearest multiple of `2 ^ (-r)`, and clamping at `0` (which only
moves the value closer to `d w ≥ 0`), gives an approximation of the present form, and a present
approximation is a rational one.

## Main definitions

* `Cslib.Complexity.Measure.stdWord`, `Cslib.Complexity.Measure.stdIndex`: the standard
  enumeration of binary words and its inverse.
* `Cslib.Complexity.Measure.charPrefix`: the first `n` bits of the characteristic sequence.
* `Cslib.Complexity.Measure.cylinder`: the languages whose characteristic sequence starts with a
  given word.
* `Cslib.Complexity.Measure.IsMartingale`: martingales.
* `Cslib.Complexity.Measure.successSet`: the languages on which a martingale succeeds.
* `Cslib.Complexity.Measure.IsPMartingale`: martingales with polynomial-time approximations.
* `Cslib.Complexity.Measure.HasPMeasureZero`, `Cslib.Complexity.Measure.HasMeasureZeroInE`:
  p-measure zero and measure zero in `E`.

## Main results

* `Cslib.Complexity.Measure.mem_successSet_iff_limsup`: success means that the limit superior of
  the capital is `∞`.
* `Cslib.Complexity.Measure.IsPMartingale.add`: a sum of p-martingales is a p-martingale.
* `Cslib.Complexity.Measure.HasPMeasureZero.mono`,
  `Cslib.Complexity.Measure.HasPMeasureZero.union`,
  `Cslib.Complexity.Measure.hasPMeasureZero_biUnion`: closure under subsets and finite unions
  [Lutz, Lemma 3.10][Lutz1992].
* `Cslib.Complexity.Measure.HasMeasureZeroInE.mono`,
  `Cslib.Complexity.Measure.HasMeasureZeroInE.union`: the same for measure zero in `E`.

## References

* [J. H. Lutz, *Almost everywhere high nonuniform complexity*][Lutz1992]
* [J. H. Lutz, *The quantitative structure of exponential time*][Lutz1997]
* [D. W. Juedes, J. H. Lutz, *Weak completeness in E and E₂*][JuedesLutz1995b]
-/

public section

namespace Cslib.Complexity.Measure

open Turing Turing.MultiTapeTM Filter

/-! ### The standard enumeration of binary words -/

/-- The `n`-th binary word in the standard enumeration `λ, 0, 1, 00, 01, 10, 11, 000, …`, ordered by
length and then lexicographically: the binary digits of `n + 1`, most significant first, without
the leading `1`. It is the reverse of the co-lexicographic enumeration
`Cslib.Complexity.Ladner.word`. -/
def stdWord (n : ℕ) : List Bool := (Ladner.word n).reverse

/-- The position of a word in the standard enumeration. -/
@[expose]
def stdIndex (w : List Bool) : ℕ := Ladner.index w.reverse

@[simp]
theorem stdWord_stdIndex (w : List Bool) : stdWord (stdIndex w) = w := by
  rw [stdWord, stdIndex, Ladner.word_index, List.reverse_reverse]

@[simp]
theorem stdIndex_stdWord (n : ℕ) : stdIndex (stdWord n) = n := by
  rw [stdWord, stdIndex, List.reverse_reverse, Ladner.index_word]

theorem stdWord_injective : Function.Injective stdWord := fun i j h => by
  rw [← stdIndex_stdWord i, h, stdIndex_stdWord]

theorem stdWord_eq_iff {n : ℕ} {w : List Bool} : stdWord n = w ↔ n = stdIndex w :=
  ⟨fun h => by rw [← h, stdIndex_stdWord], fun h => by rw [h, stdWord_stdIndex]⟩

/-- The words of length `l` come before position `2 ^ (l + 1) - 1`. -/
theorem stdIndex_add_two_le (w : List Bool) : stdIndex w + 2 ≤ 2 ^ (w.length + 1) := by
  simpa [stdIndex] using Ladner.index_add_two_le w.reverse

/-- The word at position `n` has length at most `log₂ (n + 1)`. -/
theorem two_pow_length_stdWord_le (n : ℕ) : 2 ^ (stdWord n).length ≤ n + 1 := by
  simpa [stdWord] using Ladner.two_pow_length_word_le n

/-- The word at a position, in unary, is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_stdWord : ComputableInPolyTime stdWord encUnary encBits := by
  unfold stdWord
  fun_prop

/-! ### Characteristic sequences -/

open Classical in
/-- The first `n` bits of the characteristic sequence of `A`: bit `j` records whether the `j`-th
word of the standard enumeration is in `A`. -/
noncomputable def charPrefix (A : Set (List Bool)) (n : ℕ) : List Bool :=
  (List.range n).map fun j => decide (stdWord j ∈ A)

@[simp]
theorem length_charPrefix (A : Set (List Bool)) (n : ℕ) : (charPrefix A n).length = n := by
  simp [charPrefix]

/-- Bit `j` of the characteristic sequence of `A` records whether the `j`-th word is in `A`. -/
theorem getElem_charPrefix_eq_true_iff {A : Set (List Bool)} {n j : ℕ}
    (hj : j < (charPrefix A n).length) : (charPrefix A n)[j] = true ↔ stdWord j ∈ A := by
  simp [charPrefix]

/-- A word is the prefix of length `|l|` of the characteristic sequence of `A` exactly when its
bits record membership in `A`. -/
theorem charPrefix_eq_iff {A : Set (List Bool)} {l : List Bool} :
    charPrefix A l.length = l ↔ ∀ j (hj : j < l.length), (l[j] = true ↔ stdWord j ∈ A) := by
  constructor
  · intro h j hj
    have hj' : j < (charPrefix A l.length).length := by rwa [length_charPrefix]
    rw [← getElem_charPrefix_eq_true_iff hj']
    simp only [h]
  · intro h
    refine List.ext_getElem (length_charPrefix A _) fun j hj hj' => ?_
    rw [Bool.eq_iff_iff, getElem_charPrefix_eq_true_iff hj, h j hj']

/-- The **cylinder** of `z`: the languages whose characteristic sequence starts with `z`. Lutz's
cylinders `C_z` [Lutz, Section 3][Lutz1992] also allow unspecified bits; these are the cylinders
of prefixes. -/
def cylinder (z : List Bool) : Set (Set (List Bool)) := {A | charPrefix A z.length = z}

theorem mem_cylinder_iff {z : List Bool} {A : Set (List Bool)} :
    A ∈ cylinder z ↔ charPrefix A z.length = z := Iff.rfl

@[simp]
theorem cylinder_nil : cylinder [] = Set.univ := by
  ext A
  simp [mem_cylinder_iff, charPrefix]

/-! ### Martingales -/

/-- A **martingale** [Lutz, Section 3][Lutz1997]: a nonnegative function on binary words whose value
at each word is the average of its values at the two one-bit extensions. -/
structure IsMartingale (d : List Bool → ℝ) : Prop where
  nonneg : ∀ w, 0 ≤ d w
  average : ∀ w, d w = (d (w ++ [false]) + d (w ++ [true])) / 2

/-- The **success set** of `d` [Lutz, Section 3][Lutz1997]: the languages `A` along whose
characteristic sequence the values of `d` are unbounded. For nonnegative `d`, this says that their
limit superior is `∞` (`Cslib.Complexity.Measure.mem_successSet_iff_limsup`). -/
def successSet (d : List Bool → ℝ) : Set (Set (List Bool)) :=
  {A | ∀ C : ℝ, ∃ n, C < d (charPrefix A n)}

theorem mem_successSet_iff {d : List Bool → ℝ} {A : Set (List Bool)} :
    A ∈ successSet d ↔ ∀ C : ℝ, ∃ n, C < d (charPrefix A n) := Iff.rfl

theorem notMem_successSet_iff {d : List Bool → ℝ} {A : Set (List Bool)} :
    A ∉ successSet d ↔ ∃ C : ℝ, ∀ n, d (charPrefix A n) ≤ C := by
  simp [mem_successSet_iff]

/-- **Success is a limit superior of `∞`**, as in Lutz's definition: the values of `d` along the
characteristic sequence of `A`, in the extended reals, have limit superior `⊤`. -/
theorem mem_successSet_iff_limsup {d : List Bool → ℝ} {A : Set (List Bool)} :
    A ∈ successSet d ↔ limsup (fun n => (d (charPrefix A n) : EReal)) atTop = ⊤ := by
  rw [← top_le_iff, le_limsup_iff]
  constructor
  · intro h y hy
    rw [frequently_atTop]
    intro N
    obtain ⟨m, hm⟩ := h (|y.toReal| + ∑ n ∈ Finset.range N, |d (charPrefix A n)|)
    have hsum : 0 ≤ ∑ n ∈ Finset.range N, |d (charPrefix A n)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨m, ?_, ?_⟩
    · by_contra hmN
      have := Finset.single_le_sum (f := fun n => |d (charPrefix A n)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_of_not_le hmN))
      have := le_abs_self (d (charPrefix A m))
      have := abs_nonneg y.toReal
      linarith
    · calc y ≤ (y.toReal : EReal) := EReal.le_coe_toReal hy.ne
        _ < d (charPrefix A m) := EReal.coe_lt_coe_iff.mpr
          (lt_of_le_of_lt (by linarith [le_abs_self y.toReal]) hm)
  · intro h C
    obtain ⟨n, hn⟩ := (h C (EReal.coe_lt_top C)).exists
    exact ⟨n, EReal.coe_lt_coe_iff.mp hn⟩

/-- If `d ≤ d'` pointwise, then `d'` succeeds wherever `d` does. -/
theorem successSet_mono {d d' : List Bool → ℝ} (h : ∀ w, d w ≤ d' w) :
    successSet d ⊆ successSet d' := fun A hA C => by
  obtain ⟨n, hn⟩ := hA C
  exact ⟨n, hn.trans_le (h _)⟩

/-- A sum of martingales is a martingale. -/
theorem IsMartingale.add {d d' : List Bool → ℝ} (hd : IsMartingale d) (hd' : IsMartingale d') :
    IsMartingale (d + d') where
  nonneg w := add_nonneg (hd.nonneg w) (hd'.nonneg w)
  average w := by
    simp only [Pi.add_apply]
    rw [hd.average w, hd'.average w]
    ring

/-- A constant nonnegative function is a martingale. -/
theorem isMartingale_const {c : ℝ} (hc : 0 ≤ c) : IsMartingale fun _ => c where
  nonneg _ := hc
  average _ := by ring

theorem successSet_const (c : ℝ) : successSet (fun _ => c) = ∅ := by
  ext A
  simp only [mem_successSet_iff, Set.mem_empty_iff_false, iff_false, not_forall, not_exists,
    not_lt]
  exact ⟨c, fun _ => le_rfl⟩

/-! ### Polynomial-time martingales -/

/-- A **p-martingale** [Lutz, Section 3][Lutz1997]: a martingale `d` with an approximation `dhat`,
computable in time polynomial in `r + |w|` from the precision `r` in unary and the word `w`, such
that the dyadic rational `dhat (r, w) / 2 ^ r` is within `2 ^ (-r)` of `d w`. -/
structure IsPMartingale (d : List Bool → ℝ) : Prop where
  isMartingale : IsMartingale d
  exists_approx : ∃ dhat : ℕ × List Bool → ℕ,
    ComputableInPolyTime dhat (encPair encUnary encBits) encNat ∧
      ∀ r w, |(dhat (r, w) : ℝ) / 2 ^ r - d w| ≤ 1 / 2 ^ r

/-- A constant nonnegative natural number is a p-martingale. -/
theorem isPMartingale_const (c : ℕ) : IsPMartingale fun _ => (c : ℝ) where
  isMartingale := isMartingale_const (Nat.cast_nonneg c)
  exists_approx := ⟨fun p => c * 2 ^ p.1, by fun_prop, fun r w => by
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_div_cancel_right₀ _ (by positivity),
      sub_self, abs_zero]
    positivity⟩

/-- Rounding the sum of two approximations at precision `r + 2` to precision `r` stays within
`2 ^ (-r)`. -/
private theorem abs_shiftRight_add_sub_le {r a b : ℕ} {x y : ℝ}
    (ha : |(a : ℝ) / 2 ^ (r + 2) - x| ≤ 1 / 2 ^ (r + 2))
    (hb : |(b : ℝ) / 2 ^ (r + 2) - y| ≤ 1 / 2 ^ (r + 2)) :
    |(((a + b + 2) >>> 2 : ℕ) : ℝ) / 2 ^ r - (x + y)| ≤ 1 / 2 ^ r := by
  set q := (a + b + 2) >>> 2
  have hq : (a + b + 2) / 4 = q := by simp [q, Nat.shiftRight_eq_div_pow]
  have hq₁ : (4 * q : ℝ) ≤ a + b + 2 := by exact_mod_cast (by omega : 4 * q ≤ a + b + 2)
  have hq₂ : (a + b + 2 : ℝ) < 4 * q + 4 := by exact_mod_cast (by omega : a + b + 2 < 4 * q + 4)
  have hP : (0 : ℝ) < 2 ^ r := by positivity
  have h4 : (2 : ℝ) ^ (r + 2) = 4 * 2 ^ r := by rw [pow_add]; ring
  have hP4 : (0 : ℝ) < 4 * 2 ^ r := by positivity
  rw [h4, div_sub' hP4.ne', abs_div, abs_of_pos hP4, div_le_div_iff_of_pos_right hP4,
    abs_le] at ha hb
  rw [div_sub' hP.ne', abs_div, abs_of_pos hP, div_le_div_iff_of_pos_right hP, abs_le]
  constructor <;> nlinarith

/-- **A sum of p-martingales is a p-martingale** (cf. the proof of [Lutz, Lemma 3.10][Lutz1992],
which sums density systems): approximate both summands to precision `r + 2` and round the sum to
precision `r`. -/
theorem IsPMartingale.add {d d' : List Bool → ℝ} (hd : IsPMartingale d) (hd' : IsPMartingale d') :
    IsPMartingale (d + d') where
  isMartingale := hd.isMartingale.add hd'.isMartingale
  exists_approx := by
    obtain ⟨dhat, hc, happ⟩ := hd.exists_approx
    obtain ⟨dhat', hc', happ'⟩ := hd'.exists_approx
    refine ⟨fun p => (dhat (p.1 + 2, p.2) + dhat' (p.1 + 2, p.2) + 2) >>> 2, by fun_prop,
      fun r w => ?_⟩
    exact abs_shiftRight_add_sub_le (happ (r + 2) w) (happ' (r + 2) w)

/-! ### Measure zero -/

/-- A class of languages has **p-measure zero** [Lutz, Section 3][Lutz1997]: some p-martingale
succeeds on every language in it. This is the martingale characterization [Lutz, Theorem
3.19][Lutz1992] of Lutz's Definition 3.5, which uses density systems. -/
def HasPMeasureZero (X : Set (Set (List Bool))) : Prop :=
  ∃ d, IsPMartingale d ∧ X ⊆ successSet d

theorem hasPMeasureZero_iff {X : Set (Set (List Bool))} :
    HasPMeasureZero X ↔ ∃ d, IsPMartingale d ∧ X ⊆ successSet d := Iff.rfl

/-- A class has **measure zero in `E`** [Lutz, Definition 3.7][Lutz1992], [Lutz, Section
3][Lutz1997]: its intersection with `E = DTIME (2 ^ O(n))` has p-measure zero. -/
def HasMeasureZeroInE (X : Set (Set (List Bool))) : Prop :=
  HasPMeasureZero (X ∩ E encBits)

theorem hasMeasureZeroInE_iff {X : Set (Set (List Bool))} :
    HasMeasureZeroInE X ↔ HasPMeasureZero (X ∩ E encBits) := Iff.rfl

/-- p-measure zero implies measure zero in `E`. -/
theorem HasPMeasureZero.hasMeasureZeroInE {X : Set (Set (List Bool))} (h : HasPMeasureZero X) :
    HasMeasureZeroInE X := by
  obtain ⟨d, hd, hX⟩ := h
  exact ⟨d, hd, Set.inter_subset_left.trans hX⟩

/-- **Subsets of p-measure-zero classes have p-measure zero** [Lutz, Lemma 3.10][Lutz1992]. -/
theorem HasPMeasureZero.mono {X Y : Set (Set (List Bool))} (hY : HasPMeasureZero Y) (h : X ⊆ Y) :
    HasPMeasureZero X := by
  obtain ⟨d, hd, hY⟩ := hY
  exact ⟨d, hd, h.trans hY⟩

theorem hasPMeasureZero_empty : HasPMeasureZero ∅ :=
  ⟨fun _ => ((0 : ℕ) : ℝ), isPMartingale_const 0, Set.empty_subset _⟩

/-- **Unions of two p-measure-zero classes have p-measure zero** [Lutz, Lemma 3.10][Lutz1992]:
the sum of the two martingales succeeds wherever either does. -/
theorem HasPMeasureZero.union {X Y : Set (Set (List Bool))} (hX : HasPMeasureZero X)
    (hY : HasPMeasureZero Y) : HasPMeasureZero (X ∪ Y) := by
  obtain ⟨d, hd, hX⟩ := hX
  obtain ⟨d', hd', hY⟩ := hY
  refine ⟨d + d', hd.add hd', Set.union_subset (hX.trans (successSet_mono fun w => ?_))
    (hY.trans (successSet_mono fun w => ?_))⟩
  · simpa using hd'.isMartingale.nonneg w
  · simpa using hd.isMartingale.nonneg w

/-- **Finite unions of p-measure-zero classes have p-measure zero** [Lutz, Lemma 3.10][Lutz1992].
-/
theorem hasPMeasureZero_biUnion {ι : Type*} {s : Set ι} (hs : s.Finite)
    {X : ι → Set (Set (List Bool))} (hX : ∀ i ∈ s, HasPMeasureZero (X i)) :
    HasPMeasureZero (⋃ i ∈ s, X i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using hasPMeasureZero_empty
  | @insert a s _ _ ih =>
    rw [Set.biUnion_insert]
    exact (hX a (Set.mem_insert a s)).union (ih fun i hi => hX i (Set.mem_insert_of_mem a hi))

/-- Subsets of classes of measure zero in `E` have measure zero in `E`. -/
theorem HasMeasureZeroInE.mono {X Y : Set (Set (List Bool))} (hY : HasMeasureZeroInE Y)
    (h : X ⊆ Y) : HasMeasureZeroInE X :=
  HasPMeasureZero.mono hY (Set.inter_subset_inter_left _ h)

/-- Unions of two classes of measure zero in `E` have measure zero in `E`. -/
theorem HasMeasureZeroInE.union {X Y : Set (Set (List Bool))} (hX : HasMeasureZeroInE X)
    (hY : HasMeasureZeroInE Y) : HasMeasureZeroInE (X ∪ Y) := by
  rw [hasMeasureZeroInE_iff, Set.union_inter_distrib_right]
  exact HasPMeasureZero.union hX hY

end Cslib.Complexity.Measure
