/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Measure.Basic
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Iteration
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Mathlib.Data.List.GetD

/-!
# The Measure Conservation Theorem

**`E` does not have p-measure zero** [Lutz, Theorem 3.13 and Corollary 3.14][Lutz1992]: no
p-martingale succeeds on every language in `E = DTIME (2 ^ O(n))`
(`Cslib.Complexity.Measure.not_hasPMeasureZero_E`), so `E` does not have measure zero in `E`
(`Cslib.Complexity.Measure.not_hasMeasureZeroInE_E`). Measure zero in `E` is thus a notion of
smallness inside `E`: a class of measure zero in `E` misses some language in `E`
(`Cslib.Complexity.Measure.HasMeasureZeroInE.exists_mem_E_notMem`).

The proof diagonalizes against the martingale. Let `d` be a p-martingale with approximation
`dhat`. The diagonal sequence (`Cslib.Complexity.Measure.diagBits`) extends the current prefix
`w` by the bit `b` whose approximation `dhat (|w| + 2, w b)` is smaller
(`Cslib.Complexity.Measure.diagStep`). Since `d w` is the average of `d (w0)` and `d (w1)`, the
capital grows by at most `2 ^ (-(|w| + 1))` at that step, so it stays below `d z + 1` along the
whole sequence (`Cslib.Complexity.Measure.le_of_diagBits`), and `d` fails on the language
`Cslib.Complexity.Measure.diagLanguage` with that characteristic sequence. The first `n` bits of
the sequence take `n` polynomial-time steps on words of length below `n`, so membership of `y`,
the bit at position below `2 ^ (|y| + 1)`, is decided in time `2 ^ O(|y|)`
(`Cslib.Complexity.Measure.diagLanguage_mem_E`).

Starting the diagonal sequence after a prefix `z` puts the language in the cylinder of `z`, so
no cylinder has measure zero in `E` (`Cslib.Complexity.Measure.not_hasMeasureZeroInE_cylinder`),
which is Lutz's Corollary 3.14 for cylinders of prefixes. Lutz's Theorem 3.13 is quantitative: a
p-computable density function covering `C_z ∩ E` has `d λ ≥ 2 ^ (-|z|)`. Only the qualitative
consequence is formalized here.

## Main definitions

* `Cslib.Complexity.Measure.diagStep`, `Cslib.Complexity.Measure.diagBits`,
  `Cslib.Complexity.Measure.diagLanguage`: the diagonal language against an approximation.

## Main results

* `Cslib.Complexity.Measure.le_of_diagBits`: the martingale stays below `d z + 1` along the
  diagonal sequence.
* `Cslib.Complexity.Measure.diagLanguage_mem_E`: the diagonal language is in `E`.
* `Cslib.Complexity.Measure.IsPMartingale.exists_mem_cylinder_inter_E_notMem_successSet`,
  `Cslib.Complexity.Measure.IsPMartingale.exists_mem_E_notMem_successSet`: every p-martingale
  fails on some language in `E`, in every cylinder.
* `Cslib.Complexity.Measure.not_hasMeasureZeroInE_cylinder`: no cylinder has measure zero in `E`.
* `Cslib.Complexity.Measure.not_hasPMeasureZero_E`,
  `Cslib.Complexity.Measure.not_hasMeasureZeroInE_E`: **the Measure Conservation Theorem**.
* `Cslib.Complexity.Measure.HasMeasureZeroInE.exists_mem_E_notMem`,
  `Cslib.Complexity.Measure.HasMeasureZeroInE.exists_mem_cylinder_inter_E_notMem`: a class of
  measure zero in `E` misses a language in `E`, in every cylinder.

## References

* [J. H. Lutz, *Almost everywhere high nonuniform complexity*][Lutz1992]
* [J. H. Lutz, *The quantitative structure of exponential time*][Lutz1997]
-/

public section

namespace Cslib.Complexity.Measure

open Turing Turing.MultiTapeTM

/-! ### The diagonal language -/

/-- One step of the diagonalization against the approximation `dhat`: extend `w` by the bit whose
extension has the smaller approximation at precision `|w| + 2`, preferring `false` on ties. -/
def diagStep (dhat : ℕ × List Bool → ℕ) (w : List Bool) : List Bool :=
  w ++ [decide (dhat (w.length + 2, w ++ [true]) < dhat (w.length + 2, w ++ [false]))]

/-- The prefix `z` followed by the first `n` diagonal bits against `dhat`. -/
def diagBits (dhat : ℕ × List Bool → ℕ) (z : List Bool) (n : ℕ) : List Bool :=
  (diagStep dhat)^[n] z

/-- The language whose characteristic sequence is `z` followed by the diagonal sequence against
`dhat`. -/
def diagLanguage (dhat : ℕ × List Bool → ℕ) (z : List Bool) : Set (List Bool) :=
  {w | (diagBits dhat z (stdIndex w + 1)).getD (stdIndex w) false = true}

variable {dhat : ℕ × List Bool → ℕ} {z : List Bool}

theorem diagBits_zero : diagBits dhat z 0 = z := by
  rw [diagBits, Function.iterate_zero, id_eq]

theorem diagBits_succ (n : ℕ) :
    diagBits dhat z (n + 1) = diagStep dhat (diagBits dhat z n) := by
  rw [diagBits, Function.iterate_succ_apply']
  rfl

@[simp]
theorem length_diagBits (n : ℕ) : (diagBits dhat z n).length = z.length + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [diagBits_succ, diagStep, List.length_append, ih, List.length_singleton, Nat.add_assoc]

theorem diagBits_prefix {m n : ℕ} (h : m ≤ n) : diagBits dhat z m <+: diagBits dhat z n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih =>
    rw [diagBits_succ, diagStep]
    exact ih.trans (List.prefix_append _ _)

/-- Bits of the diagonal sequence do not change as it grows. -/
theorem getD_diagBits {m n j : ℕ} (hm : j < z.length + m) (hn : j < z.length + n) :
    (diagBits dhat z m).getD j false = (diagBits dhat z n).getD j false := by
  wlog h : m ≤ n generalizing m n
  · exact (this hn hm (by omega)).symm
  rw [List.getD_eq_getElem _ _ (by simpa using hm), List.getD_eq_getElem _ _ (by simpa using hn)]
  exact (diagBits_prefix h).getElem _

/-- The characteristic sequence of the diagonal language is `z` followed by the diagonal
sequence. -/
theorem charPrefix_diagLanguage (n : ℕ) :
    charPrefix (diagLanguage dhat z) (z.length + n) = diagBits dhat z n := by
  conv_lhs => rw [← length_diagBits (dhat := dhat) (z := z) n]
  refine charPrefix_eq_iff.mpr fun j hj => ?_
  simp only [diagLanguage, Set.mem_ofPred_eq, stdIndex_stdWord]
  rw [getD_diagBits (n := n) (by omega) (by simpa using hj), List.getD_eq_getElem _ _ hj]

/-- The diagonal language is in the cylinder of `z`. -/
theorem diagLanguage_mem_cylinder : diagLanguage dhat z ∈ cylinder z := by
  rw [mem_cylinder_iff, ← Nat.add_zero z.length, charPrefix_diagLanguage, diagBits_zero]

/-! ### The martingale fails on the diagonal language -/

/-- One diagonal step raises a martingale by at most `2 ^ (-(|w| + 1))`. -/
theorem le_diagStep {d : List Bool → ℝ} (hd : IsMartingale d)
    (happ : ∀ r w, |(dhat (r, w) : ℝ) / 2 ^ r - d w| ≤ 1 / 2 ^ r) (w : List Bool) :
    d (diagStep dhat w) ≤ d w + 1 / 2 ^ (w.length + 1) := by
  set Q : ℝ := 2 ^ (w.length + 2) with hQdef
  have hQ : (0 : ℝ) < Q := by positivity
  have hmul : ∀ v, |(dhat (w.length + 2, v) : ℝ) - Q * d v| ≤ 1 := fun v => by
    have := happ (w.length + 2) v
    rwa [div_sub' hQ.ne', abs_div, abs_of_pos hQ, div_le_div_iff_of_pos_right hQ] at this
  have h0 := abs_le.mp (hmul (w ++ [false]))
  have h1 := abs_le.mp (hmul (w ++ [true]))
  have havg : Q * d w = (Q * d (w ++ [false]) + Q * d (w ++ [true])) / 2 := by
    rw [hd.average w]
    ring
  have hgoal : (1 : ℝ) / 2 ^ (w.length + 1) = 2 / Q := by
    rw [div_eq_div_iff (by positivity) hQ.ne', hQdef]
    ring
  rw [hgoal, ← mul_le_mul_iff_of_pos_left hQ, mul_add, mul_div_cancel₀ _ hQ.ne']
  unfold diagStep
  by_cases hlt : dhat (w.length + 2, w ++ [true]) < dhat (w.length + 2, w ++ [false])
  · rw [decide_eq_true hlt]
    have : (dhat (w.length + 2, w ++ [true]) : ℝ) < dhat (w.length + 2, w ++ [false]) := by
      exact_mod_cast hlt
    linarith
  · rw [decide_eq_false hlt]
    have : (dhat (w.length + 2, w ++ [false]) : ℝ) ≤ dhat (w.length + 2, w ++ [true]) := by
      exact_mod_cast Nat.le_of_not_lt hlt
    linarith

/-- **A martingale stays below `d z + 1` along the diagonal sequence against its approximation.**
-/
theorem le_of_diagBits {d : List Bool → ℝ} (hd : IsMartingale d)
    (happ : ∀ r w, |(dhat (r, w) : ℝ) / 2 ^ r - d w| ≤ 1 / 2 ^ r) (n : ℕ) :
    d (diagBits dhat z n) ≤ d z + 1 - 1 / 2 ^ n := by
  induction n with
  | zero => simp [diagBits_zero]
  | succ n ih =>
    have h := le_diagStep hd happ (diagBits dhat z n)
    have hle : (1 : ℝ) / 2 ^ ((diagBits dhat z n).length + 1) ≤ 1 / 2 ^ (n + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (pow_le_pow_right₀ (by norm_num) (by simp))
    rw [diagBits_succ]
    have : (1 : ℝ) / 2 ^ (n + 1) = 1 / 2 ^ n / 2 := by rw [pow_succ]; field_simp
    rw [this] at hle ⊢
    linarith

/-- A martingale fails on the diagonal language against its approximation. -/
theorem diagLanguage_notMem_successSet {d : List Bool → ℝ} (hd : IsMartingale d)
    (happ : ∀ r w, |(dhat (r, w) : ℝ) / 2 ^ r - d w| ≤ 1 / 2 ^ r) :
    diagLanguage dhat z ∉ successSet d := by
  rw [notMem_successSet_iff]
  set S := ∑ m ∈ Finset.range z.length, |d (charPrefix (diagLanguage dhat z) m)|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨S + (d z + 1), fun m => ?_⟩
  rcases lt_or_ge m z.length with hm | hm
  · -- the finitely many prefixes of `z`
    have := Finset.single_le_sum (f := fun m => |d (charPrefix (diagLanguage dhat z) m)|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr hm)
    have := le_abs_self (d (charPrefix (diagLanguage dhat z) m))
    have := hd.nonneg z
    linarith
  · -- the diagonal steps
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [charPrefix_diagLanguage]
    have := le_of_diagBits (z := z) hd happ n
    have : (0 : ℝ) < 1 / 2 ^ n := by positivity
    linarith

/-! ### The diagonal language is in `E` -/

/-- **The diagonal sequence is polynomial-time** in its length, in unary, for a polynomial-time
approximation. -/
theorem computableInPolyTime_diagBits
    (hc : ComputableInPolyTime dhat (encPair encUnary encBits) encNat) :
    ComputableInPolyTime (diagBits dhat z) encUnary encBits := by
  have hstep : ComputableInPolyTime (diagStep dhat) encBits encBits := by
    unfold diagStep
    fun_prop
  exact ComputableInPolyTime.iterate_of_bounded_growth (count := fun n => n)
    (init := fun _ => z) (by fun_prop) (by fun_prop) hstep (growth := 1)
    fun w => by simp [diagStep, encBits_apply]

/-- Membership of `y`, read from the first `|z| + 2 * N` bits of the diagonal sequence. -/
private def memDiag (dhat : ℕ × List Bool → ℕ) (z : List Bool) (p : List Bool × ℕ) : Bool :=
  ((List.range (2 * p.2)).find? fun j => decide (stdWord j = p.1)).elim false
    fun j => (diagBits dhat z (2 * p.2)).getD j false

private theorem computableInPolyTime_memDiag
    (hc : ComputableInPolyTime dhat (encPair encUnary encBits) encNat) :
    ComputableInPolyTime (memDiag dhat z) (encPair encBits encUnary) encBool := by
  have h := computableInPolyTime_diagBits (z := z) hc
  unfold memDiag
  fun_prop

private theorem memDiag_iff {y : List Bool} {N : ℕ} (hN : stdIndex y < 2 * N) :
    memDiag dhat z (y, N) = true ↔ y ∈ diagLanguage dhat z := by
  have hfind : (List.range (2 * N)).find? (fun j => decide (stdWord j = y)) =
      some (stdIndex y) := by
    rw [List.find?_range_eq_some]
    refine ⟨by simp, List.mem_range.mpr hN, fun j hj => ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
    rintro rfl
    rw [stdIndex_stdWord] at hj
    exact lt_irrefl _ hj
  rw [memDiag, hfind, Option.elim_some, diagLanguage, Set.mem_ofPred_eq,
    getD_diagBits (n := stdIndex y + 1) (by omega) (by omega)]

/-- **The diagonal language is in `E`.** -/
theorem diagLanguage_mem_E (hc : ComputableInPolyTime dhat (encPair encUnary encBits) encNat) :
    diagLanguage dhat z ∈ E encBits := by
  have h := setOf_mem_E_of_computableInPolyTime_pad (computableInPolyTime_memDiag (z := z) hc)
  convert h using 1
  ext y
  simp only [Set.mem_ofPred_eq]
  rw [memDiag_iff]
  have := stdIndex_add_two_le y
  rw [pow_succ] at this
  omega

/-! ### The Measure Conservation Theorem -/

/-- **Every p-martingale fails on some language in `E` in every cylinder**: the qualitative form
of [Lutz, Theorem 3.13][Lutz1992]. -/
theorem IsPMartingale.exists_mem_cylinder_inter_E_notMem_successSet {d : List Bool → ℝ}
    (hd : IsPMartingale d) (z : List Bool) :
    ∃ A ∈ cylinder z ∩ E encBits, A ∉ successSet d := by
  obtain ⟨dhat, hc, happ⟩ := hd.exists_approx
  exact ⟨diagLanguage dhat z, ⟨diagLanguage_mem_cylinder, diagLanguage_mem_E hc⟩,
    diagLanguage_notMem_successSet hd.isMartingale happ⟩

/-- **Every p-martingale fails on some language in `E`**: the qualitative form of
[Lutz, Theorem 3.13][Lutz1992]. -/
theorem IsPMartingale.exists_mem_E_notMem_successSet {d : List Bool → ℝ} (hd : IsPMartingale d) :
    ∃ A ∈ E encBits, A ∉ successSet d := by
  obtain ⟨A, ⟨-, hA⟩, hAd⟩ := hd.exists_mem_cylinder_inter_E_notMem_successSet []
  exact ⟨A, hA, hAd⟩

/-- **No cylinder has measure zero in `E`** [Lutz, Corollary 3.14][Lutz1992]. -/
theorem not_hasMeasureZeroInE_cylinder (z : List Bool) : ¬ HasMeasureZeroInE (cylinder z) := by
  rw [hasMeasureZeroInE_iff, hasPMeasureZero_iff]
  rintro ⟨d, hd, hX⟩
  obtain ⟨A, hA, hAd⟩ := hd.exists_mem_cylinder_inter_E_notMem_successSet z
  exact hAd (hX hA)

/-- **`E` does not have p-measure zero.** -/
theorem not_hasPMeasureZero_E : ¬ HasPMeasureZero (E encBits) := by
  rw [hasPMeasureZero_iff]
  rintro ⟨d, hd, hE⟩
  obtain ⟨A, hA, hAd⟩ := hd.exists_mem_E_notMem_successSet
  exact hAd (hE hA)

/-- **The Measure Conservation Theorem: `E` does not have measure zero in `E`**
[Lutz, Theorem 3.13 and Corollary 3.14][Lutz1992], [Lutz, Theorem 3.3][Lutz1997]. -/
theorem not_hasMeasureZeroInE_E : ¬ HasMeasureZeroInE (E encBits) := fun h =>
  not_hasPMeasureZero_E ((hasMeasureZeroInE_iff.mp h).mono fun _ hA => ⟨hA, hA⟩)

/-- **A class of measure zero in `E` misses a language in `E` in every cylinder.** -/
theorem HasMeasureZeroInE.exists_mem_cylinder_inter_E_notMem {X : Set (Set (List Bool))}
    (hX : HasMeasureZeroInE X) (z : List Bool) : ∃ A ∈ cylinder z ∩ E encBits, A ∉ X := by
  by_contra! h
  obtain ⟨d, hd, hXd⟩ := hasPMeasureZero_iff.mp (hasMeasureZeroInE_iff.mp hX)
  obtain ⟨A, hA, hAd⟩ := hd.exists_mem_cylinder_inter_E_notMem_successSet z
  exact hAd (hXd ⟨h A hA, hA.2⟩)

/-- **A class of measure zero in `E` misses a language in `E`.** -/
theorem HasMeasureZeroInE.exists_mem_E_notMem {X : Set (Set (List Bool))}
    (hX : HasMeasureZeroInE X) : ∃ A ∈ E encBits, A ∉ X := by
  obtain ⟨A, ⟨-, hA⟩, hAX⟩ := hX.exists_mem_cylinder_inter_E_notMem []
  exact ⟨A, hA, hAX⟩

end Cslib.Complexity.Measure
