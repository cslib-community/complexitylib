/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Tuple
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.PiLex

/-!
# Arbitrary-base lexicographic tuple numbering

The first coordinate is most significant, as required by Immerman's ordered first-order queries.
Coordinate reversal converts the existing colexicographic tuple numbering to this convention.
For every base `n` and dimension `k`, the resulting map is a bijection with `Fin (n ^ k)`;
its order agrees with Mathlib's `Pi.Lex`. No power-of-two restriction or binary concatenation
is used. The standard canonical constants use `n ≥ 2`, and the tuple for one needs positive
dimension. The zero-dimensional universe still has one element.

This numbers the full tuple universe; native tuple BIT is constructed in `Ordered.TupleBit`.
Numeric-preserving full-tuple composition is supplied in `Ordered.FullTuple.Composition`.
Numeric predicates on restricted domains require separate constructions.

## Main definitions

* `Cslib.Logic.FO.Ordered.lexEquiv`: first-coordinate-most-significant tuple numbering.
* `Cslib.Logic.FO.Ordered.lexRank`: the natural-number rank of a tuple.
* `Cslib.Logic.FO.Ordered.tupleZero`, `Cslib.Logic.FO.Ordered.tupleOne`,
  `Cslib.Logic.FO.Ordered.tupleMax`: the canonical full-domain tuples.

## Main results

* `Cslib.Logic.FO.Ordered.lexRank_lt_iff`: order is determined by the first differing coordinate.
* `Cslib.Logic.FO.Ordered.lexRank_lt_iff_lex`: agreement with Mathlib's lexicographic relation.
* `Cslib.Logic.FO.Ordered.lexRank_comp_lt_lexRank_comp_iff`: increasing maps of coordinates
  preserve lexicographic order.
* `Cslib.Logic.FO.Ordered.lexRank_tupleZero`, `Cslib.Logic.FO.Ordered.lexRank_tupleOne`,
  `Cslib.Logic.FO.Ordered.lexRank_tupleMax`: exact canonical ranks.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Remark 1.32 and Exercise 1.33(1),
  with the full-domain hypothesis. `Ordered.TupleBit` supplies Exercise 1.33(3).
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered

/-- Number full tuples in arbitrary base, with the first coordinate most significant. -/
def lexEquiv {n k : ℕ} : (Fin k → Fin n) ≃ Fin (n ^ k) := tupleEquiv Fin.revPerm

/-- The natural-number rank of a tuple in lexicographic order. -/
def lexRank {n k : ℕ} (x : Fin k → Fin n) : ℕ := lexEquiv x

/-- Lexicographic rank is the existing colexicographic index after coordinate reversal. -/
theorem lexRank_eq_tupleIndex {n k : ℕ} (x : Fin k → Fin n) :
    lexRank x = tupleIndex (x ∘ Fin.rev) := rfl

/-- Digit `i` has weight `n ^ (k - 1 - i)`; `i.rev` is that reversed position. -/
theorem lexRank_apply {n k : ℕ} (x : Fin k → Fin n) :
    lexRank x = ∑ i, (x i).val * n ^ i.rev.val := by
  rw [lexRank_eq_tupleIndex, tupleIndex_apply]
  simpa only [Fin.revPerm_apply, Fin.rev_rev, Function.comp_apply] using
    (Equiv.sum_comp Fin.revPerm (fun i : Fin k => (x i).val * n ^ i.rev.val))

/-- Decode a lexicographic rank by division and remainder in the original base. -/
theorem lexEquiv_symm_apply_val {n k : ℕ} (r : Fin (n ^ k)) (i : Fin k) :
    ((lexEquiv.symm r) i).val = r.val / n ^ i.rev.val % n :=
  tupleEquiv_symm_apply_val Fin.revPerm r i

/-- The lexicographic rank of a `k`-tuple over `Fin n` is strictly less than `n ^ k`. -/
theorem lexRank_lt {n k : ℕ} (x : Fin k → Fin n) : lexRank x < n ^ k :=
  (lexEquiv x).isLt

/-- Lexicographic rank is injective on `Fin k → Fin n`. -/
theorem lexRank_injective {n k : ℕ} : Function.Injective (lexRank (n := n) (k := k)) :=
  fun _ _ h => lexEquiv.injective (Fin.ext h)

/-- Numerical order agrees with the first coordinate at which the tuples differ. -/
theorem lexRank_lt_iff {n k : ℕ} (x y : Fin k → Fin n) :
    lexRank x < lexRank y ↔ ∃ i, x i < y i ∧ ∀ j, j < i → x j = y j := by
  rw [lexRank_eq_tupleIndex, lexRank_eq_tupleIndex, tupleIndex_lt_iff]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨i.rev, hi, fun j hji => ?_⟩
    simpa only [Function.comp_apply, Fin.rev_rev] using hj j.rev (Fin.lt_rev_iff.mp hji)
  · rintro ⟨i, hi, hj⟩
    refine ⟨i.rev, ?_, fun j hji => ?_⟩
    · simpa only [Function.comp_apply, Fin.rev_rev] using hi
    · exact hj j.rev (Fin.rev_lt_iff.mpr hji)

/-- The canonical numbering agrees with Mathlib's lexicographic relation. -/
theorem lexRank_lt_iff_lex {n k : ℕ} (x y : Fin k → Fin n) :
    lexRank x < lexRank y ↔ Pi.Lex (· < ·) (· < ·) x y := by
  rw [lexRank_lt_iff, Pi.Lex]
  exact exists_congr fun _ => and_comm

/-- Applying an increasing map to every coordinate preserves lexicographic order. -/
theorem lexRank_comp_lt_lexRank_comp_iff {n n' k : ℕ} {f : Fin n → Fin n'} (hf : StrictMono f)
    (x y : Fin k → Fin n) : lexRank (f ∘ x) < lexRank (f ∘ y) ↔ lexRank x < lexRank y := by
  simp only [lexRank_lt_iff, Function.comp_apply, hf.lt_iff_lt, hf.injective.eq_iff]

variable {n k : ℕ} [Fact (2 ≤ n)]

/-- The all-zero tuple. -/
def tupleZero : Fin k → Fin n := fun _ => ⟨0, by have := Fact.out (p := 2 ≤ n); lia⟩

/-- The tuple whose last coordinate is one and whose other coordinates are zero. -/
def tupleOne : Fin (k + 1) → Fin n := fun i =>
  if i = Fin.last k then ⟨1, by have := Fact.out (p := 2 ≤ n); lia⟩ else tupleZero i

/-- The tuple with every coordinate at its maximum. -/
def tupleMax : Fin k → Fin n := fun _ =>
  ⟨n - 1, by have := Fact.out (p := 2 ≤ n); lia⟩

/-- The all-zero tuple has rank `0`. -/
theorem lexRank_tupleZero : lexRank (tupleZero (n := n) (k := k)) = 0 := by
  simp [lexRank_apply, tupleZero]

/-- The tuple with last coordinate one and the others zero has rank `1`. -/
theorem lexRank_tupleOne : lexRank (tupleOne (n := n) (k := k)) = 1 := by
  rw [lexRank_apply, Fintype.sum_eq_single (Fin.last k)]
  · simp [tupleOne]
  · intro i hi
    simp [tupleOne, hi, tupleZero]

/-- The tuple of maximal coordinates has the largest rank, `n ^ k - 1`. -/
theorem lexRank_tupleMax : lexRank (tupleMax (n := n) (k := k)) = n ^ k - 1 := by
  have hn : 0 < n := by have := Fact.out (p := 2 ≤ n); lia
  have hp := Nat.pow_pos hn (n := k)
  have hb := lexRank_lt (tupleMax (n := n) (k := k))
  by_contra h
  have hl : lexRank (tupleMax (n := n) (k := k)) < n ^ k - 1 := by lia
  let r : Fin (n ^ k) := ⟨n ^ k - 1, by lia⟩
  have hr : lexRank (lexEquiv.symm r) = n ^ k - 1 :=
    congrArg Fin.val (lexEquiv.apply_symm_apply r)
  rw [← hr, lexRank_lt_iff] at hl
  obtain ⟨i, hi, _⟩ := hl
  have hi' := (lexEquiv.symm r i).isLt
  change n - 1 < (lexEquiv.symm r i).val at hi
  lia

end Cslib.Logic.FO.Ordered
