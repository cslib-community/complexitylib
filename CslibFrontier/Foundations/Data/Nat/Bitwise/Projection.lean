/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Bit projections and highest differing positions

Natural numbers represent bit strings, with an explicit width for bounded-word comparisons.
Projections retain selected positions in list order; finite-set sketches sort those positions
by significance. Prefix boundaries replace the low bits with fixed masks.

## Main definitions

* `differingBits`, `highestDiff`: differing positions below a given width and their maximum.
* `projectBits`, `sketch`: list and finite-set bit projections.
* `lowerBoundary`, `upperBoundary`: words with a shared high prefix and fixed low-bit masks.

## Main results

* `highestDiff_spec`: distinct bounded words differ at their highest differing position.
* `projectBits_lt`: a selected highest differing position preserves strict order.
* `projectBits_ofFn_eq_sum`: the positional numeric value of a projection.
* `boundary_prefix`: both boundaries preserve the high prefix.

## References

See [FredmanWillard1993] for the use of significant-bit projections in fusion trees.
-/

@[expose] public section

namespace Cslib.BitString

open scoped BigOperators

/-- The positions below `w` where the binary representations of `x` and `y` differ. -/
def differingBits (w x y : ℕ) : Finset ℕ :=
  (Finset.range w).filter fun i => x.testBit i ≠ y.testBit i

/-- The highest differing position below `w`, or zero when there are no differing positions. -/
def highestDiff (w x y : ℕ) : ℕ :=
  (differingBits w x y).sup id

/-- All bits at or above the word width of a bounded natural number vanish. -/
theorem _root_.Nat.testBit_eq_false_of_lt_two_pow {w x i : ℕ} (hx : x < 2 ^ w) (hi : w ≤ i) :
    x.testBit i = false :=
  Nat.testBit_eq_false_of_lt (hx.trans_le (Nat.pow_le_pow_right (by decide) hi))

/-- Distinct bounded words have a differing bit below their word width. -/
private theorem differingBits_nonempty {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hne : x ≠ y) : (differingBits w x y).Nonempty := by
  by_contra h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < w
  · by_contra hbit
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hbit⟩⟩
  · rw [Nat.testBit_eq_false_of_lt_two_pow hx (by omega),
      Nat.testBit_eq_false_of_lt_two_pow hy (by omega)]

/-- The highest differing bit is below the word width and really differs. -/
theorem highestDiff_mem {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hne : x ≠ y) : highestDiff w x y ∈ differingBits w x y := by
  have h := Finset.sup_mem_of_nonempty (f := id) (differingBits_nonempty hx hy hne)
  simpa only [highestDiff, Set.image_id, Finset.mem_coe] using h

/-- Two bounded words agree at every position above their highest differing bit. -/
theorem testBit_eq_of_highestDiff_lt {w x y i : ℕ} (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) (hi : highestDiff w x y < i) : x.testBit i = y.testBit i := by
  by_cases hiw : i < w
  · by_contra hbit
    have hmem : i ∈ differingBits w x y :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiw, hbit⟩
    have := Finset.le_sup (f := id) hmem
    exact (not_le_of_gt hi) this
  · rw [Nat.testBit_eq_false_of_lt_two_pow hx (by omega),
      Nat.testBit_eq_false_of_lt_two_pow hy (by omega)]

/-- Unequal bounded words differ at `highestDiff` and share all more significant bits. -/
theorem highestDiff_spec {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hne : x ≠ y) :
    highestDiff w x y < w ∧
      x.testBit (highestDiff w x y) ≠ y.testBit (highestDiff w x y) ∧
      ∀ i, highestDiff w x y < i → x.testBit i = y.testBit i := by
  have h := Finset.mem_filter.mp (highestDiff_mem hx hy hne)
  exact ⟨Finset.mem_range.mp h.1, h.2, fun _ => testBit_eq_of_highestDiff_lt hx hy⟩

/-- For distinct bounded words, deleting their lowest `cut` bits leaves the same prefix exactly
when `cut` lies above their highest differing position. -/
theorem highestDiff_lt_iff_shiftRight_eq {w x y cut : ℕ} (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) (hne : x ≠ y) :
    highestDiff w x y < cut ↔ x >>> cut = y >>> cut := by
  constructor
  · intro hcut
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
    exact testBit_eq_of_highestDiff_lt hx hy (by omega)
  · intro heq
    by_contra hcut
    have hbit := congrArg (fun z => z.testBit (highestDiff w x y - cut)) heq
    rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight,
      Nat.add_sub_of_le (by omega : cut ≤ highestDiff w x y)] at hbit
    exact (highestDiff_spec hx hy hne).2.1 hbit

/-- The prefix above the highest differing bit is shared. -/
theorem shiftRight_highestDiff_add_one_eq {w x y : ℕ} (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) (hne : x ≠ y) :
    x >>> (highestDiff w x y + 1) = y >>> (highestDiff w x y + 1) :=
  (highestDiff_lt_iff_shiftRight_eq hx hy hne).mp (Nat.lt_succ_self _)

/-- The prefix including the highest differing bit is not shared. -/
theorem shiftRight_highestDiff_ne {w x y : ℕ} (hx : x < 2 ^ w)
    (hy : y < 2 ^ w) (hne : x ≠ y) :
    x >>> highestDiff w x y ≠ y >>> highestDiff w x y := by
  intro heq
  exact (Nat.lt_irrefl _) ((highestDiff_lt_iff_shiftRight_eq hx hy hne).mpr heq)

/-- At the highest differing bit, the smaller word has zero and the larger word has one. -/
theorem highestDiff_bits_of_lt {w x y : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hxy : x < y) :
    x.testBit (highestDiff w x y) = false ∧ y.testBit (highestDiff w x y) = true := by
  obtain ⟨_, hdiff, habove⟩ := highestDiff_spec hx hy (Nat.ne_of_lt hxy)
  cases hxb : x.testBit (highestDiff w x y) <;>
    cases hyb : y.testBit (highestDiff w x y)
  · exact False.elim (hdiff (hxb.trans hyb.symm))
  · exact ⟨rfl, rfl⟩
  · exact False.elim (Nat.not_lt_of_ge hxy.le
      (Nat.lt_of_testBit _ hyb hxb fun i hi => (habove i hi).symm))
  · exact False.elim (hdiff (hxb.trans hyb.symm))

/-- Pack the indicated bits, least significant position first. Repeated or unordered positions
are allowed; order preservation additionally requires the list to be strictly increasing. -/
def projectBits : List ℕ → ℕ → ℕ
  | [], _ => 0
  | i :: positions, x => Nat.bit (x.testBit i) (projectBits positions x)

/-- Agreement at all selected positions implies equal projections. -/
theorem projectBits_eq {positions : List ℕ} {x y : ℕ}
    (h : ∀ i ∈ positions, x.testBit i = y.testBit i) :
    projectBits positions x = projectBits positions y := by
  induction positions with
  | nil => rfl
  | cons i positions ih =>
    rw [projectBits, projectBits, h i (by simp), ih (fun j hj => h j (by simp [hj]))]

/-- Bit `i` of the packed projection is the input bit at the `i`-th selected position. -/
theorem testBit_projectBits (positions : List ℕ) (x i : ℕ) (hi : i < positions.length) :
    (projectBits positions x).testBit i = x.testBit positions[i] := by
  induction positions generalizing i with
  | nil => simp at hi
  | cons p positions ih =>
    cases i with
    | zero => simp [projectBits]
    | succ i =>
      simpa only [projectBits, Nat.testBit_bit_succ, List.getElem_cons_succ] using
        ih i (by simpa using hi)

/-- A selected highest differing bit makes the projection strictly ordered. -/
theorem projectBits_lt {positions : List ℕ} {x y b : ℕ}
    (hsorted : positions.Pairwise (· < ·)) (hb : b ∈ positions)
    (hx : x.testBit b = false) (hy : y.testBit b = true)
    (habove : ∀ i, b < i → x.testBit i = y.testBit i) :
    projectBits positions x < projectBits positions y := by
  induction positions with
  | nil => simp at hb
  | cons i positions ih =>
    obtain ⟨hi, htail⟩ := List.pairwise_cons.mp hsorted
    rcases List.mem_cons.mp hb with rfl | hb
    · have heq := projectBits_eq (fun j hj => habove j (hi j hj))
      rw [projectBits, projectBits, hx, hy, heq, Nat.bit_false, Nat.bit_true]
      exact Nat.lt_succ_self _
    · exact Nat.bit_lt_bit _ _ (ih htail hb)

/-- Every projection fits in the number of bits selected by its position list. -/
theorem projectBits_lt_two_pow (positions : List ℕ) (x : ℕ) :
    projectBits positions x < 2 ^ positions.length := by
  induction positions with
  | nil => simp [projectBits]
  | cons i positions ih =>
    simp only [projectBits, List.length_cons, pow_succ]
    cases x.testBit i <;> simp only [Nat.bit_false, Nat.bit_true] <;> omega

/-- The perfect sketch packs the bits in a finite set in increasing significance order. -/
def sketch (positions : Finset ℕ) (x : ℕ) : ℕ :=
  projectBits (positions.sort (· ≤ ·)) x

/-- A perfect sketch is a word with one bit per selected position. -/
theorem sketch_lt_two_pow (positions : Finset ℕ) (x : ℕ) :
    sketch positions x < 2 ^ positions.card := by
  simpa only [sketch, Finset.length_sort] using
    projectBits_lt_two_pow (positions.sort (· ≤ ·)) x

/-- Retaining the highest differing bit suffices to preserve an ordered pair of bounded words. -/
theorem sketch_lt_of_highestDiff_mem {w x y : ℕ} {positions : Finset ℕ}
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) (hxy : x < y)
    (hmem : highestDiff w x y ∈ positions) : sketch positions x < sketch positions y := by
  obtain ⟨hxb, hyb⟩ := highestDiff_bits_of_lt hx hy hxy
  exact projectBits_lt positions.sortedLT_sort.pairwise
    ((Finset.mem_sort _).mpr hmem) hxb hyb (fun _ => testBit_eq_of_highestDiff_lt hx hy)

/-- Deleting a fixed number of low bits preserves weak order. -/
theorem _root_.Nat.shiftRight_le_shiftRight {x y : ℕ} (h : x ≤ y) (cut : ℕ) :
    x >>> cut ≤ y >>> cut := by
  simpa only [Nat.shiftRight_eq_div_pow] using Nat.div_le_div_right (c := 2 ^ cut) h

/-- A prefix shared by the endpoints of an interval is shared by every word between them. -/
theorem _root_.Nat.shiftRight_eq_of_between {x y z cut : ℕ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hprefix : x >>> cut = z >>> cut) : y >>> cut = x >>> cut := by
  have h₁ := Nat.shiftRight_le_shiftRight hxy cut
  have h₂ := Nat.shiftRight_le_shiftRight hyz cut
  omega

/-- Equal prefixes imply agreement at all positions retained by the prefix. -/
theorem _root_.Nat.testBit_eq_of_shiftRight_eq {x y cut : ℕ} (h : x >>> cut = y >>> cut)
    {b : ℕ} (hb : cut ≤ b) : x.testBit b = y.testBit b := by
  have hbit := congrArg (fun z : ℕ => z.testBit (b - cut)) h
  simpa only [Nat.testBit_shiftRight, Nat.add_sub_of_le hb] using hbit

/-- A differing bit with agreement everywhere above it is the highest differing bit. -/
theorem highestDiff_eq_of_testBit {w x y p : ℕ} (hp : p < w)
    (hdiff : x.testBit p ≠ y.testBit p)
    (habove : ∀ b, p < b → x.testBit b = y.testBit b) : highestDiff w x y = p := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro b hb
    change b ≤ p
    have h := (Finset.mem_filter.mp hb).2
    by_contra hle
    exact h (habove b (by omega))
  · exact Finset.le_sup (f := id)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, hdiff⟩)

/-- Keep the prefix above `p`, set bit `p` to zero, and set every lower bit to one. -/
def lowerBoundary (q p : ℕ) : ℕ := ((q >>> (p + 1)) <<< (p + 1)) ||| (2 ^ p - 1)

/-- Keep the prefix above `p`, set bit `p` to one, and set every lower bit to zero. -/
def upperBoundary (q p : ℕ) : ℕ := ((q >>> (p + 1)) <<< (p + 1)) ||| 2 ^ p

/-- The lower boundary agrees with the query above `p` and has the indicated low-bit mask. -/
theorem testBit_lowerBoundary (q p b : ℕ) :
    (lowerBoundary q p).testBit b =
      if p < b then q.testBit b else decide (b < p) := by
  simp only [lowerBoundary, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases h : p < b
  · have hle : p + 1 ≤ b := by omega
    simp only [hle, decide_true, Bool.true_and, Nat.add_sub_of_le hle,
      show ¬b < p by omega, decide_false, Bool.or_false, h, ↓reduceIte]
  · have hle : ¬b ≥ p + 1 := by omega
    simp only [hle, decide_false, Bool.false_and, Bool.false_or, h, ↓reduceIte]

/-- The upper boundary agrees with the query above `p` and has only bit `p` set below it. -/
theorem testBit_upperBoundary (q p b : ℕ) :
    (upperBoundary q p).testBit b =
      if p < b then q.testBit b else decide (b = p) := by
  simp only [upperBoundary, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow]
  by_cases h : p < b
  · have hle : p + 1 ≤ b := by omega
    simp only [hle, decide_true, Bool.true_and, Nat.add_sub_of_le hle,
      show ¬p = b by omega, decide_false, Bool.or_false, h, ↓reduceIte]
  · have hle : ¬b ≥ p + 1 := by omega
    simp only [hle, decide_false, Bool.false_and, Bool.false_or, h, ↓reduceIte,
      eq_comm]

/-- Both correction boundaries keep the query's full prefix above `p`. -/
theorem boundary_prefix (q p : ℕ) :
    lowerBoundary q p >>> (p + 1) = q >>> (p + 1) ∧
      upperBoundary q p >>> (p + 1) = q >>> (p + 1) := by
  constructor <;> apply Nat.eq_of_testBit_eq <;> intro b
  · simp only [Nat.testBit_shiftRight, testBit_lowerBoundary,
      show p < p + 1 + b by omega, ↓reduceIte]
  · simp only [Nat.testBit_shiftRight, testBit_upperBoundary,
      show p < p + 1 + b by omega, ↓reduceIte]

/-- Pointwise implication between selected bits implies weak order of the packed sketches. -/
theorem projectBits_le {positions : List ℕ} {x y : ℕ}
    (h : ∀ b ∈ positions, x.testBit b = true → y.testBit b = true) :
    projectBits positions x ≤ projectBits positions y := by
  induction positions with
  | nil => exact le_rfl
  | cons b positions ih =>
    have htail := ih (fun i hi => h i (List.mem_cons_of_mem b hi))
    have hb := h b (List.mem_cons_self ..)
    simp only [projectBits]
    cases hx : x.testBit b <;> cases hy : y.testBit b <;>
      simp only [Nat.bit_false, Nat.bit_true] <;>
      first | omega | exact False.elim (Bool.noConfusion (hy.symm.trans (hb hx)))

/-- Different prefixes compare in the same direction as the full words. -/
theorem _root_.Nat.lt_iff_shiftRight_lt_of_ne {x y cut : ℕ} (hne : x >>> cut ≠ y >>> cut) :
    x < y ↔ x >>> cut < y >>> cut := by
  constructor
  · intro h
    exact lt_of_le_of_ne (Nat.shiftRight_le_shiftRight h.le cut) hne
  · intro h
    exact lt_of_not_ge (fun hle => not_le_of_gt h (Nat.shiftRight_le_shiftRight hle cut))

/-- Within a prefix block whose bit `p` is zero, the lower correction boundary has a sketch
at least as large as every word in that block. -/
theorem sketch_le_lowerBoundary {positions : Finset ℕ} {x q p : ℕ}
    (hprefix : x >>> (p + 1) = q >>> (p + 1)) (hbit : x.testBit p = false) :
    sketch positions x ≤ sketch positions (lowerBoundary q p) := by
  apply projectBits_le
  intro b _ hb
  rw [testBit_lowerBoundary]
  by_cases hpb : p < b
  · rw [ite_eq_left hpb]
    exact (Nat.testBit_eq_of_shiftRight_eq hprefix (by omega)).symm.trans hb
  · rw [ite_eq_right hpb]
    have hbp : b < p := by
      by_contra h
      have heq : b = p := by omega
      subst b
      rw [hbit] at hb
      contradiction
    exact decide_eq_true hbp

/-- Within a prefix block whose bit `p` is one, the upper correction boundary has a sketch
at most as large as every word in that block. -/
theorem upperBoundary_le_sketch {positions : Finset ℕ} {x q p : ℕ}
    (hprefix : x >>> (p + 1) = q >>> (p + 1)) (hbit : x.testBit p = true) :
    sketch positions (upperBoundary q p) ≤ sketch positions x := by
  apply projectBits_le
  intro b _ hb
  rw [testBit_upperBoundary] at hb
  by_cases hpb : p < b
  · rw [ite_eq_left hpb] at hb
    exact (Nat.testBit_eq_of_shiftRight_eq hprefix (by omega)).trans hb
  · rw [ite_eq_right hpb] at hb
    have heq : b = p := of_decide_eq_true hb
    subst b
    exact hbit

/-- A projection's bits have their usual positional numeric value. -/
theorem projectBits_ofFn_eq_sum {r : ℕ} (b : Fin r → ℕ) (x : ℕ) :
    projectBits (List.ofFn b) x = ∑ i, (x.testBit (b i)).toNat * 2 ^ i.val := by
  induction r with
  | zero => simp [projectBits]
  | succ r ih =>
    rw [List.ofFn_succ, projectBits, ih, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ,
      ← mul_assoc, ← Finset.sum_mul]
    cases x.testBit (b 0) <;> simp only [Nat.bit_false, Nat.bit_true,
      Bool.toNat_false, Bool.toNat_true] <;> ring

end Cslib.BitString
