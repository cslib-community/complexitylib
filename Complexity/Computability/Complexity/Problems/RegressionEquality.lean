/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SubsetSum
public import Complexity.Statistics.LeastSquares.SimpleMatrix
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Tactic

/-!
# Equality-target regression deletion

The equality target of [XuGaoHu2027], Theorem 3.7 (PDF p. 8): integer responses,
a binary regressor and an intercept, with a nonsingular retained design.
The input records the responses at regressor one; one additional observation
at regressor zero has response zero. Deletion ranges over all sublists of the
actual observations, including the option to remove that additional observation.
Numbers use signed binary encoding, rather than unary magnitudes.

## Main definitions

* `ExactFit`: nonsingular real inverse-matrix OLS with slope exactly zero.
* `BinaryProblem`: deletion on explicitly supplied binary/integer observations.
* `fromSubsetSum`, `expand`: the actual numerical reduction and row materialization.

## Main results

* `reduction_mem_iff`: correctness of the composed map on every Subset-Sum input.
* `computableInPolyTime_reduction`: polynomial time for the actual binary encodings.
* `binary_npHard`: Theorem 3.7 on explicit binary/integer observations.
-/

public section

namespace Cslib.LeastSquares.EqualityDeletion

open Cslib.Complexity Turing.MultiTapeTM
open scoped List

/-- An observation with rational regressor and response. -/
abbrev Point := ℚ × ℚ

/-- Actual design rows: one zero observation and the listed integer responses
at regressor one. Equal-valued rows retain their multiplicities. -/
@[expose] def data (l : List ℤ) : List Point := (0, 0) :: l.map (fun z : ℤ => (1, (z : ℚ)))

/-- Real regressor read from the retained observations. -/
@[expose] def x (l : List Point) (i : Fin l.length) : ℝ := (l.get i).1
/-- Real response read from the retained observations. -/
@[expose] def y (l : List Point) (i : Fin l.length) : ℝ := (l.get i).2

/-- The actual two-column OLS fit is nonsingular and its slope is exactly zero. -/
@[expose] noncomputable def ExactFit (l : List Point) : Prop :=
  (weightedGram 0 Finset.univ (Simple.design (x l)) (fun _ => 1)).PosDef ∧
    weightedEstimate 0 0 Finset.univ (Simple.design (x l)) (y l) (fun _ => 1) 0 = 0

/-- Inspectable scalar characterization of the actual inverse-matrix target. -/
theorem exactFit_iff (l : List Point) : ExactFit l ↔
    0 < Simple.mass (fun _ : Fin l.length => (1 : ℝ)) ∧
      0 < Simple.xNumerator (x l) (fun _ => 1) ∧
      Simple.crossNumerator (x l) (y l) (fun _ => 1) = 0 := by
  rw [ExactFit, Simple.gram_posDef_iff _ _ (by intro _; norm_num)]
  constructor
  · rintro ⟨⟨hm, hv⟩, he⟩
    rw [Simple.inverse_estimate _ _ _ (by intro _; norm_num) hm hv] at he
    simp only [Matrix.cons_val_zero, Simple.slope, div_eq_zero_iff] at he
    exact ⟨hm, hv, he.resolve_right (ne_of_gt hv)⟩
  · rintro ⟨hm, hv, he⟩
    refine ⟨⟨hm, hv⟩, ?_⟩
    rw [Simple.inverse_estimate _ _ _ (by intro _; norm_num) hm hv]
    simp [Simple.slope, he]

private theorem one_sums (l : List ℤ) :
    (∑ i : Fin (data l).length, x (data l) i) = (l.length : ℝ) ∧
    (∑ i : Fin (data l).length, y (data l) i) = (l.sum : ℝ) ∧
    (∑ i : Fin (data l).length, x (data l) i * y (data l) i) = (l.sum : ℝ) ∧
    (∑ i : Fin (data l).length, x (data l) i * x (data l) i) = (l.length : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [Function.comp_def, x, List.get_eq_getElem, data,
      List.map_const', List.sum_replicate] using
      Fin.sum_univ_fun_getElem (data l) (fun p => (p.1 : ℝ))
  · simpa [Function.comp_def, y, List.get_eq_getElem, data, ← Int.cast_sum] using
      Fin.sum_univ_fun_getElem (data l) (fun p => (p.2 : ℝ))
  · simpa [Function.comp_def, x, y, List.get_eq_getElem, data, ← Int.cast_sum] using
      Fin.sum_univ_fun_getElem (data l) (fun p => (p.1 : ℝ) * (p.2 : ℝ))
  · simpa [Function.comp_def, x, List.get_eq_getElem, data,
      List.map_const', List.sum_replicate] using
      Fin.sum_univ_fun_getElem (data l) (fun p => (p.1 : ℝ) * (p.1 : ℝ))

/-- For the binary design, nonsingularity forces both groups to survive and
zero slope is exactly a zero response sum in the regressor-one group. -/
theorem exactFit_data_iff (l : List ℤ) : ExactFit (data l) ↔ l ≠ [] ∧ l.sum = 0 := by
  obtain ⟨hx, hy, hxy, hxx⟩ := one_sums l
  have hm : Simple.mass (fun _ : Fin (data l).length => (1 : ℝ)) = l.length + 1 := by
    simp only [Simple.mass, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_univ, Fintype.card_fin]
    simp [data]
  have hv : Simple.xNumerator (x (data l)) (fun _ => 1) = (l.length : ℝ) := by
    simp only [Simple.xNumerator, Simple.crossNumerator, one_mul, hx, hxx, hm]
    ring
  have hc : Simple.crossNumerator (x (data l)) (y (data l)) (fun _ => 1) =
      (l.sum : ℝ) := by
    simp only [Simple.crossNumerator, one_mul, hx, hy, hxy, hm]
    ring
  rw [exactFit_iff, hm, hv, hc]
  have hpos : (0 : ℝ) < l.length + 1 := by positivity
  simp only [hpos, true_and, Int.cast_eq_zero, Nat.cast_pos,
    List.length_pos_iff_ne_nil]

/-- Removing the sole regressor-zero observation leaves a singular design. -/
theorem not_exactFit_ones (l : List ℤ) :
    ¬ ExactFit (l.map fun z : ℤ => ((1 : ℚ), (z : ℚ))) := by
  intro h
  have hv := (exactFit_iff _).mp h |>.2.1
  have hz : Simple.xNumerator (x (l.map fun z : ℤ => ((1 : ℚ), (z : ℚ))))
      (fun _ => 1) = 0 := by
    have hx : x (l.map fun z : ℤ => ((1 : ℚ), (z : ℚ))) = fun _ => 1 := by
      funext i
      simp [x, List.get_eq_getElem]
    simp only [Simple.xNumerator, Simple.crossNumerator]
    rw [hx]
    simp [Simple.mass]
  linarith

/-- Equality-target deletion on the actual observations. The budget is an upper
bound; a singular remainder is never accepted, even though division is total. -/
@[expose] noncomputable def Problem : Set (List ℤ × ℕ) :=
  {a | ∃ kept, kept <+ data a.1 ∧
    (data a.1).length - kept.length ≤ a.2 ∧ ExactFit kept}

/-- The inverse-matrix deletion problem is precisely a nonempty zero-sum
sublist problem. This is proved, rather than used as the definition of OLS. -/
theorem mem_problem_iff (l : List ℤ) (k : ℕ) : (l, k) ∈ Problem ↔
    ∃ kept, kept <+ l ∧ kept ≠ [] ∧ kept.sum = 0 ∧ l.length - kept.length ≤ k := by
  constructor
  · rintro ⟨kept, hs, hk, hf⟩
    change kept <+ (0, 0) :: l.map (fun z : ℤ => ((1 : ℚ), (z : ℚ))) at hs
    obtain hs | ⟨tail, rfl, ht⟩ := List.sublist_cons_iff.mp hs
    · obtain ⟨s, hs, rfl⟩ := List.sublist_map_iff.mp hs
      exact False.elim (not_exactFit_ones s hf)
    · obtain ⟨s, hsl, rfl⟩ := List.sublist_map_iff.mp ht
      have he := (exactFit_data_iff s).mp hf
      exact ⟨s, hsl, he.1, he.2, by simpa [data] using hk⟩
  · rintro ⟨kept, hs, hn, hz, hk⟩
    exact ⟨data kept, (hs.map _).cons_cons _, by simpa [data] using hk,
      (exactFit_data_iff kept).mpr ⟨hn, hz⟩⟩

/-- Remove zero entries before using the paper's positive-integer reduction. -/
@[expose] def positive (l : List ℕ) : List ℕ := l.filter fun n => n ≠ 0

private theorem sum_positive (l : List ℕ) : (positive l).sum = l.sum := by
  induction l with
  | nil => rfl
  | cons n ns ih =>
    by_cases hn : n = 0
    · simpa only [positive, hn, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false, List.sum_cons, zero_add] using ih
    · simpa [positive, hn] using congrArg (n + ·) ih

private theorem subsetSum_positive (l : List ℕ) (t : ℕ) :
    (positive l, t) ∈ SubsetSum ↔ (l, t) ∈ SubsetSum := by
  rw [mem_SubsetSum_iff_sublist, mem_SubsetSum_iff_sublist]
  constructor
  · rintro ⟨s, hs, hz⟩
    exact ⟨s, hs.trans List.filter_sublist, hz⟩
  · rintro ⟨s, hs, hz⟩
    exact ⟨positive s, hs.filter _, (sum_positive s).trans hz⟩

/-- Actual numerical construction: positive responses, a negative target, and
a zero response, with deletion budget r-1. The zero-target case is sent to a
fixed yes instance. No desired reduction map is supplied as an assumption. -/
@[expose] def fromSubsetSum (a : List ℕ × ℕ) : List ℤ × ℕ :=
  if a.2 = 0 then ([0], 0) else
    ((positive a.1).map (fun n : ℕ => (n : ℤ)) ++ [0 - (a.2 : ℤ), 0],
      (positive a.1).length - 1)

private theorem positive_reduction (a : List ℕ) (t : ℕ)
    (hpos : ∀ n ∈ a, 0 < n) (ht : 0 < t) :
    (a.map (fun n : ℕ => (n : ℤ)) ++ [0 - (t : ℤ), 0], a.length - 1) ∈ Problem ↔
      (a, t) ∈ SubsetSum := by
  rw [mem_problem_iff, mem_SubsetSum_iff_sublist]
  have hempty : ∀ s : List ℕ, s <+ a → s.sum = 0 → s = [] := by
    intro s hs hz
    cases s with
    | nil => rfl
    | cons n ns =>
      have hn := hpos n (hs.subset (by simp))
      simp only [List.sum_cons] at hz
      omega
  constructor
  · rintro ⟨kept, hs, _, hz, hk⟩
    obtain ⟨u, v, rfl, hu, hv⟩ := List.sublist_append_iff.mp hs
    obtain ⟨s, hsa, rfl⟩ := List.sublist_map_iff.mp hu
    have hcases : v = [] ∨ v = [0 - (t : ℤ)] ∨ v = [0] ∨ v = [0 - (t : ℤ), 0] := by
      simpa [List.sublists, or_assoc, or_left_comm, or_comm] using List.mem_sublists.mpr hv
    simp only [List.sum_append, ← Nat.cast_list_sum] at hz
    rcases hcases with rfl | rfl | rfl | rfl
    · have he : s.sum = 0 := by
        have he : (s.sum : ℤ) = 0 := by
          simpa only [List.sum_cons, List.sum_nil, add_zero] using hz
        exact_mod_cast he
      have hs0 := hempty s hsa he
      simp only [hs0, List.map_nil, List.append_nil, List.length_nil,
        List.length_append, List.length_map, List.length_cons] at hk
      omega
    · simp only [List.sum_cons, List.sum_nil, add_zero, zero_sub] at hz
      exact ⟨s, hsa, by omega⟩
    · have he : s.sum = 0 := by
        have he : (s.sum : ℤ) = 0 := by
          simpa only [List.sum_cons, List.sum_nil, add_zero] using hz
        exact_mod_cast he
      have hs0 := hempty s hsa he
      simp only [hs0, List.map_nil, List.nil_append, List.length_cons, List.length_nil,
        List.length_append, List.length_map] at hk
      omega
    · simp only [List.sum_cons, List.sum_nil, add_zero, zero_sub] at hz
      exact ⟨s, hsa, by omega⟩
  · rintro ⟨s, hs, hz⟩
    have hsn : s ≠ [] := by intro h; simp [h] at hz; omega
    have hlen : 0 < s.length := List.length_pos_iff_ne_nil.mpr hsn
    refine ⟨s.map (fun n : ℕ => (n : ℤ)) ++ [0 - (t : ℤ), 0],
      (hs.map _).append (List.Sublist.refl _), by simp, ?_, ?_⟩
    · simp [← Nat.cast_list_sum, hz]
    · simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
      have := hs.length_le
      omega

/-- Soundness and completeness for every binary Subset-Sum input, including
zero entries and zero target. The retained design is actually nonsingular. -/
theorem fromSubsetSum_mem_iff (a : List ℕ × ℕ) :
    fromSubsetSum a ∈ Problem ↔ a ∈ SubsetSum := by
  obtain ⟨l, t⟩ := a
  by_cases ht : t = 0
  · subst t
    simp only [fromSubsetSum]
    have hyes : ([0], 0) ∈ Problem := (mem_problem_iff _ _).mpr
      ⟨[0], List.Sublist.refl _, by simp, by simp, by simp⟩
    have hsub : (l, 0) ∈ SubsetSum := mem_SubsetSum_iff_sublist.mpr ⟨[], by simp, rfl⟩
    exact iff_of_true hyes hsub
  · simp only [fromSubsetSum, ht]
    exact (positive_reduction (positive l) t (by
      intro n hn
      have := (List.mem_filter.mp hn).2
      simp only [ne_eq, decide_eq_true_eq] at this
      omega) (Nat.pos_of_ne_zero ht)).trans (subsetSum_positive l t)

/-- Signed binary input for the restricted binary design. The omitted regressor
coordinates are all fixed bits; the one additional zero observation is fixed. -/
@[expose] def encoding : (List ℤ × ℕ) ↪ List Bool :=
  encPair (encList encIntBin) encNat

/-- The actual reduction runs in polynomial time in the binary input length.
Filtering, signed casts, target negation, appending and the budget calculation
are all certified operations on their specified encodings. -/
@[fun_prop]
theorem computableInPolyTime_fromSubsetSum :
    ComputableInPolyTime fromSubsetSum (encPair (encList encNat) encNat) encoding := by
  apply ComputableInPolyTime.of_tidy
  have hl : ComputableTidilyInPolyTime
      (fun a : List ℕ × ℕ => positive a.1) (encPair (encList encNat) encNat)
      (encList encNat) := by unfold positive; fun_prop
  have hlen : ComputableTidilyInPolyTime
      (fun a : List ℕ × ℕ => (positive a.1).length)
      (encPair (encList encNat) encNat) encNat :=
    ComputableTidilyInPolyTime.unary_to_binary.comp
      ((ComputableTidilyInPolyTime.length_list encNat).comp hl)
  have hb : ComputableTidilyInPolyTime
      (fun a : List ℕ × ℕ => (positive a.1).length - 1)
      (encPair (encList encNat) encNat) encNat :=
    ComputableTidilyInPolyTime.binary_sub.comp (hlen.prod
      (ComputableTidilyInPolyTime.const 1))
  have hn : ComputableTidilyInPolyTime
      (fun a : List ℕ × ℕ => (a.2 : ℤ)) (encPair (encList encNat) encNat) encIntBin :=
    ComputableTidilyInPolyTime.intBin_natCast.comp (ComputableTidilyInPolyTime.snd _ _)
  unfold fromSubsetSum encoding
  fun_prop

/-- Theorem 3.7, weak NP-hardness for an actual equality target with integer
responses and nonsingular remainder. This is a polynomial-time many-one
reduction from the existing binary Subset-Sum problem, not an assumed hardness
or assumed-map transfer. The regressors are fixed binary coordinates. -/
theorem npHard : NPHard encoding Problem :=
  SubsetSum_npHard.trans ⟨fromSubsetSum, computableInPolyTime_fromSubsetSum,
    fun a => (fromSubsetSum_mem_iff a).symm⟩

/-- Convert explicit binary-regressor/integer-response observations to the
rational observations used by the actual real inverse-matrix estimator. -/
@[expose] def observations (l : List (Bool × ℤ)) : List Point :=
  l.map fun p : Bool × ℤ => ((if p.1 then 1 else 0 : ℚ), (p.2 : ℚ))

/-- The unrestricted binary-design equality-target deletion problem.
Every observation can be deleted, and the retained OLS design must be nonsingular. -/
@[expose] noncomputable def BinaryProblem : Set (List (Bool × ℤ) × ℕ) :=
  {a | ∃ kept, kept <+ observations a.1 ∧
    (observations a.1).length - kept.length ≤ a.2 ∧ ExactFit kept}

/-- Each regressor is a bit, each response a signed binary integer, and the
nonnegative deletion budget is binary. -/
@[expose] def binaryEncoding : (List (Bool × ℤ) × ℕ) ↪ List Bool :=
  encPair (encList (encPair encBool encIntBin)) encNat

/-- Materialize every actual input observation, including the sole regressor-zero row. -/
@[expose] def expand (a : List ℤ × ℕ) : List (Bool × ℤ) × ℕ :=
  ((false, 0) :: a.1.map (fun z : ℤ => (true, z)), a.2)

/-- Expanding the restricted representation preserves actual deletion and OLS semantics. -/
theorem expand_mem_iff (a : List ℤ × ℕ) : expand a ∈ BinaryProblem ↔ a ∈ Problem := by
  have he : observations (expand a).1 = data a.1 := by
    simp [observations, expand, data, Function.comp_def]
  change (∃ kept, kept <+ observations (expand a).1 ∧
    (observations (expand a).1).length - kept.length ≤ a.2 ∧ ExactFit kept) ↔ _
  rw [he]
  rfl

/-- Materializing all binary observations is certified polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_expand :
    ComputableInPolyTime expand encoding binaryEncoding := by
  unfold expand encoding binaryEncoding
  fun_prop

/-- **Theorem 3.7** on explicitly encoded observations: binary regressors,
integer responses, an intercept, an at-most deletion budget and an exactly-zero
OLS slope on a nonsingular remainder. Hardness is weak (numbers are binary),
and no general-position assumption is imposed. -/
theorem binary_npHard : NPHard binaryEncoding BinaryProblem :=
  npHard.trans ⟨expand, computableInPolyTime_expand, fun a => (expand_mem_iff a).symm⟩

/-- The complete map from binary Subset Sum to explicitly encoded observations. -/
@[fun_prop]
theorem computableInPolyTime_reduction :
    ComputableInPolyTime (fun a => expand (fromSubsetSum a))
      (encPair (encList encNat) encNat) binaryEncoding :=
  computableInPolyTime_expand.comp computableInPolyTime_fromSubsetSum

/-- End-to-end soundness and completeness of the actual polynomial-time map. -/
theorem reduction_mem_iff (a : List ℕ × ℕ) :
    expand (fromSubsetSum a) ∈ BinaryProblem ↔ a ∈ SubsetSum :=
  (expand_mem_iff _).trans (fromSubsetSum_mem_iff a)

end Cslib.LeastSquares.EqualityDeletion
