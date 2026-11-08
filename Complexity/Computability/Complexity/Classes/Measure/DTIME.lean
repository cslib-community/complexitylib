/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Measure.Conservation
import Complexity.Computability.Complexity.Classes.Ladner.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential
import Mathlib.Data.List.GetD

/-!
# Fixed exponential time has measure zero in `E`

For each `k`, the class `DTIME (2 ^ (k * n))` has p-measure zero, hence measure zero in `E`
(`Cslib.Complexity.Measure.hasPMeasureZero_DTIME`,
`Cslib.Complexity.Measure.hasMeasureZeroInE_DTIME`).
With the Measure Conservation Theorem this separates every such class from `E`
(`Cslib.Complexity.Measure.DTIME_ssubset_E`). Every finite set of languages in `E`, in particular
every singleton, has p-measure zero (`Cslib.Complexity.Measure.hasPMeasureZero_singleton`,
`Cslib.Complexity.Measure.hasPMeasureZero_of_finite`) [Lutz, Lemma 3.12][Lutz1992], and so does
`P` (`Cslib.Complexity.Measure.hasPMeasureZero_P`).

The martingale (`Cslib.Complexity.Measure.TimeMartingale.martingale`) is the weighted sum, over
machine indices `i`, of the martingale `dᵢ` that holds its capital `2 ^ (-i)` while betting on
the first `i` bits, and from bit `i` on stakes all its capital on the prediction of machine `i`.
The prediction for bit `j` (`Cslib.Complexity.Measure.TimeMartingale.predicts`) is the output of
machine `i` on the `j`-th word `s_j`, run by the universal function for `(j + 1) ^ (k + 1)` steps.
The sum of the `dᵢ` is `num w / 2 ^ |w|` with `num w = 2 + ∑ 4 ^ (|w| - i)` over the indices
`i < |w|` whose predictions agree with `w` from bit `i` on
(`Cslib.Complexity.Measure.TimeMartingale.num`). It is computed exactly, in time polynomial in
`|w|`.

If a machine decides `A` within time `c₁ 2 ^ (k n) + c₂`, then so does every index `i` of it.
Since `2 ^ |s_j| ≤ j + 1`, the time bound at `s_j` is at most `(j + 1) ^ (k + 1)` once
`j + 1 ≥ c₁ + c₂`. Choosing the index `i ≥ c₁ + c₂`, all predictions of machine `i` from bit `i`
on are correct, and the capital along the characteristic sequence of `A` is at least
`4 ^ (n - i) / 2 ^ n`, which is unbounded.

Lutz derives the measure zero of `DTIME (2 ^ (k * n))` from the measure zero of p-countable
unions of p-measure-zero classes [Lutz, Lemmas 3.10 and 3.12][Lutz1992]; the weighted sum above is
that argument specialized to the enumeration of the time-bounded machines.

## Main definitions

* `Cslib.Complexity.Measure.TimeMartingale.martingale`: a p-martingale succeeding on
  `DTIME (2 ^ (k * n))`.

## Main results

* `Cslib.Complexity.Measure.TimeMartingale.isPMartingale`: it is a p-martingale.
* `Cslib.Complexity.Measure.TimeMartingale.DTIME_subset_successSet`: it succeeds on every language
  in `DTIME (2 ^ (k * n))`.
* `Cslib.Complexity.Measure.hasPMeasureZero_DTIME`,
  `Cslib.Complexity.Measure.hasMeasureZeroInE_DTIME`: `DTIME (2 ^ (k * n))` has p-measure zero
  and measure zero in `E`.
* `Cslib.Complexity.Measure.DTIME_ssubset_E`: `DTIME (2 ^ (k * n)) ⊂ E`.
* `Cslib.Complexity.Measure.hasPMeasureZero_singleton`,
  `Cslib.Complexity.Measure.hasPMeasureZero_of_finite`: finite sets of languages in `E` have
  p-measure zero.
* `Cslib.Complexity.Measure.hasPMeasureZero_P`: `P` has p-measure zero.

## References

* [J. H. Lutz, *Almost everywhere high nonuniform complexity*][Lutz1992]
* [J. H. Lutz, *The quantitative structure of exponential time*][Lutz1997]
-/

public section

namespace Cslib.Complexity.Measure

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal Ladner

namespace TimeMartingale

/-! ### The martingale -/

/-- The prediction of machine `i` for bit `j`: it accepts the `j`-th word within
`(j + 1) ^ (k + 1)` steps. -/
def predicts (k i j : ℕ) : Bool :=
  decide (runIndexed i (stdWord j) ((j + 1) ^ (k + 1)) = ([eBit true], true))

/-- The predictions of machine `i` agree with the bits of `w` from bit `i` on. -/
def agrees (k : ℕ) (w : List Bool) (i : ℕ) : Bool :=
  (List.range w.length).all fun j => decide (j < i) || (w.getD j false == predicts k i j)

/-- The contribution of machine `i` to `num k w`: `4 ^ (|w| - i)` if its predictions agree with
`w` from bit `i` on. -/
def term (k : ℕ) (w : List Bool) (i : ℕ) : ℕ :=
  if agrees k w i then 2 ^ (2 * (w.length - i)) else 0

/-- `2 ^ |w|` times the capital of the martingale at `w`: `2` for the machines `i ≥ |w|`, which
have not bet yet, and `4 ^ (|w| - i)` for each machine `i < |w|` whose predictions agree with `w`.
-/
def num (k : ℕ) (w : List Bool) : ℕ := 2 + ((List.range w.length).map (term k w)).sum

/-- **A martingale succeeding on `DTIME (2 ^ (k * n))`**: `num k w / 2 ^ |w|`. -/
noncomputable def martingale (k : ℕ) (w : List Bool) : ℝ := num k w / 2 ^ w.length

/-- The exact approximation: `num k w / 2 ^ |w|` rounded down to a multiple of `2 ^ (-r)`. -/
def approx (k : ℕ) (p : ℕ × List Bool) : ℕ := num k p.2 * 2 ^ p.1 / 2 ^ p.2.length

theorem agrees_iff {k : ℕ} {w : List Bool} {i : ℕ} :
    agrees k w i = true ↔ ∀ j (hj : j < w.length), i ≤ j → w[j] = predicts k i j := by
  simp only [agrees, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  refine forall_congr' fun j => ⟨fun h hj hij => ?_, fun h hj => ?_⟩
  · rw [← List.getD_eq_getElem _ false hj]
    exact (h hj).resolve_left (by omega)
  · by_cases hij : j < i
    · exact Or.inl hij
    · rw [List.getD_eq_getElem _ false hj]
      exact Or.inr (h hj (by omega))

/-- Extending `w` by a bit keeps the agreement of machine `i < |w|` exactly when the bit is its
prediction. -/
private theorem agrees_append {k : ℕ} {w : List Bool} {i : ℕ} (hi : i ≤ w.length) (b : Bool) :
    agrees k (w ++ [b]) i = (agrees k w i && (b == predicts k i w.length)) := by
  rw [Bool.eq_iff_iff, Bool.and_eq_true, beq_iff_eq, agrees_iff, agrees_iff]
  constructor
  · intro h
    refine ⟨fun j hj hij => ?_, ?_⟩
    · have := h j (by simp; omega) hij
      rwa [List.getElem_append_left hj] at this
    · have := h w.length (by simp) hi
      simpa using this
  · rintro ⟨h, hb⟩ j hj hij
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [List.getElem_append_left hj]
      exact h j hj hij
    · simpa using hb

/-- Machine `i ≤ |w|` contributes four times as much to the two extensions of `w` together. -/
private theorem term_append_add {k : ℕ} {w : List Bool} {i : ℕ} (hi : i ≤ w.length) :
    term k (w ++ [false]) i + term k (w ++ [true]) i =
      (if agrees k w i then 4 * 2 ^ (2 * (w.length - i)) else 0) := by
  have hlen : ∀ b : Bool, (w ++ [b]).length - i = w.length - i + 1 := fun b => by
    simp only [List.length_append, List.length_singleton]
    omega
  simp only [term, agrees_append hi, hlen]
  cases agrees k w i <;> cases predicts k i w.length <;> simp [pow_succ, mul_add] <;> ring

/-- **The fairness of the martingale**: `num (w0) + num (w1) = 4 num w`. -/
theorem num_append_add (k : ℕ) (w : List Bool) :
    num k (w ++ [false]) + num k (w ++ [true]) = 4 * num k w := by
  have hlen : ∀ b : Bool, (w ++ [b]).length = w.length + 1 := fun b => by simp
  simp only [num, hlen, List.range_succ, List.map_append, List.map_singleton, List.sum_append,
    List.sum_singleton]
  -- the machine `|w|` starts betting and contributes `4` to one extension and `0` to the other
  have hlast : term k (w ++ [false]) w.length + term k (w ++ [true]) w.length = 4 := by
    rw [term_append_add le_rfl, Nat.sub_self]
    have : agrees k w w.length = true :=
      agrees_iff.mpr fun j hj hij => absurd hj (by omega)
    simp [this]
  -- the machines below `|w|` contribute four times as much
  have hmid : ((List.range w.length).map (term k (w ++ [false]))).sum +
      ((List.range w.length).map (term k (w ++ [true]))).sum =
      4 * ((List.range w.length).map (term k w)).sum := by
    rw [← List.sum_map_add, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    rw [term_append_add (List.mem_range.mp hi).le, term]
    split <;> simp
  omega

/-- **The martingale is a martingale.** -/
theorem isMartingale (k : ℕ) : IsMartingale (martingale k) where
  nonneg w := by unfold martingale; positivity
  average w := by
    have h := num_append_add k w
    have h' : (num k (w ++ [false]) : ℝ) + num k (w ++ [true]) = 4 * num k w := by
      exact_mod_cast h
    simp only [martingale, List.length_append, List.length_singleton, pow_succ]
    field_simp
    linarith

/-- The approximation is polynomial-time. -/
theorem computableInPolyTime_approx (k : ℕ) :
    ComputableInPolyTime (approx k) (encPair encUnary encBits) encNat := by
  have hpred : ComputableInPolyTime (fun p : ℕ × ℕ => predicts k p.1 p.2)
      (encPair encUnary encUnary) encBool := by
    unfold predicts
    fun_prop
  have hagree : ComputableInPolyTime (fun p : List Bool × ℕ => agrees k p.1 p.2)
      (encPair encBits encUnary) encBool := by
    unfold agrees
    fun_prop
  have hterm : ComputableInPolyTime (fun p : List Bool × ℕ => term k p.1 p.2)
      (encPair encBits encUnary) encNat := by
    unfold term
    fun_prop
  have hnum : ComputableInPolyTime (num k) encBits encNat := by
    unfold num
    fun_prop
  unfold approx
  fun_prop

/-- The approximation is within `2 ^ (-r)`. -/
theorem abs_approx_sub_le (k r : ℕ) (w : List Bool) :
    |(approx k (r, w) : ℝ) / 2 ^ r - martingale k w| ≤ 1 / 2 ^ r := by
  set q := approx k (r, w)
  have hq₁ : q * 2 ^ w.length ≤ num k w * 2 ^ r := Nat.div_mul_le_self _ _
  have hq₂ : num k w * 2 ^ r < (q + 1) * 2 ^ w.length := by
    rw [Nat.add_one_mul]
    exact Nat.lt_div_mul_add (by positivity)
  have hq₁' : (q : ℝ) * 2 ^ w.length ≤ num k w * 2 ^ r := by exact_mod_cast hq₁
  have hq₂' : (num k w : ℝ) * 2 ^ r < (q + 1) * 2 ^ w.length := by exact_mod_cast hq₂
  have hP : (0 : ℝ) < 2 ^ r := by positivity
  have hL : (0 : ℝ) < 2 ^ w.length := by positivity
  have hx : martingale k w = (num k w : ℝ) * 2 ^ r / 2 ^ w.length / 2 ^ r := by
    rw [martingale]
    field_simp
  have h₁ : (q : ℝ) ≤ num k w * 2 ^ r / 2 ^ w.length := by rwa [le_div_iff₀ hL]
  have h₂ : (num k w : ℝ) * 2 ^ r / 2 ^ w.length < q + 1 := by rwa [div_lt_iff₀ hL]
  rw [hx, ← sub_div, abs_div, abs_of_pos hP, div_le_div_iff_of_pos_right hP, abs_le]
  constructor <;> linarith

/-- **The martingale is a p-martingale**, with the exact approximation `approx`. -/
theorem isPMartingale (k : ℕ) : IsPMartingale (martingale k) where
  isMartingale := isMartingale k
  exists_approx := ⟨approx k, computableInPolyTime_approx k, abs_approx_sub_le k⟩

/-! ### The martingale succeeds on `DTIME (2 ^ (k * n))` -/

/-- From `j + 1 ≥ c₁ + c₂` on, the time bound `c₁ 2 ^ (k |s_j|) + c₂` is at most
`(j + 1) ^ (k + 1)`. -/
private theorem time_le {c₁ c₂ k j : ℕ} (hj : c₁ + c₂ ≤ j + 1) :
    c₁ * 2 ^ (k * (stdWord j).length) + c₂ ≤ (j + 1) ^ (k + 1) := by
  have h₁ : 2 ^ (k * (stdWord j).length) ≤ (j + 1) ^ k := by
    rw [mul_comm, pow_mul]
    exact Nat.pow_le_pow_left (two_pow_length_stdWord_le j) k
  have h₂ : 1 ≤ (j + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos j)
  calc c₁ * 2 ^ (k * (stdWord j).length) + c₂ ≤ c₁ * (j + 1) ^ k + c₂ * (j + 1) ^ k :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h₁) (Nat.le_mul_of_pos_right _ h₂)
    _ = (c₁ + c₂) * (j + 1) ^ k := by ring
    _ ≤ (j + 1) * (j + 1) ^ k := Nat.mul_le_mul_right _ hj
    _ = (j + 1) ^ (k + 1) := by ring

/-- **Every language in `DTIME (2 ^ (k * n))` is predicted correctly** by a machine `i`, from
bit `i` on. -/
theorem exists_predicts_iff {k : ℕ} {A : Set (List Bool)}
    (hA : A ∈ DTIME encBits fun n => 2 ^ (k * n)) :
    ∃ i, ∀ j, i ≤ j → (predicts k i j = true ↔ stdWord j ∈ A) := by
  obtain ⟨c₁, c₂, s, hdec⟩ := hA
  obtain ⟨g, ⟨kt, State, hfinite, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hdec
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  have hrun (x : List Bool) :
      (tm.runFrom (tm.initCfg x) (c₁ * 2 ^ (k * x.length) + c₂)).Halted ∧
        (tm.runFrom (tm.initCfg x) (c₁ * 2 ^ (k * x.length) + c₂)).output = [g x] :=
    (htm x).runFrom_of_le le_rfl
  obtain ⟨i, hi, hdesc⟩ := exists_index_ge (desc eS eBit tm) (c₁ + c₂)
  refine ⟨i, fun j hij => ?_⟩
  rw [predicts, decide_eq_true_iff, runIndexed, hdesc,
    universal_desc_of_halted eS tm (t := fun x => c₁ * 2 ^ (k * x.length) + c₂) hrun
      (time_le (by omega)), hg]
  constructor
  · intro h
    exact eBit.injective (List.singleton_inj.mp (Prod.mk.inj h).1)
  · intro h
    rw [h]

/-- The capital at `w` is at least the contribution of machine `i`. -/
private theorem term_le_num (k : ℕ) {w : List Bool} {i : ℕ} (hi : i < w.length) :
    term k w i ≤ num k w := by
  have := List.le_sum_of_mem (List.mem_map_of_mem (f := term k w) (List.mem_range.mpr hi))
  rw [num]
  omega

/-- **The martingale succeeds on every language in `DTIME (2 ^ (k * n))`.** -/
theorem DTIME_subset_successSet (k : ℕ) :
    DTIME encBits (fun n => 2 ^ (k * n)) ⊆ successSet (martingale k) := by
  intro A hA
  rw [mem_successSet_iff]
  intro C
  obtain ⟨i, hi⟩ := exists_predicts_iff hA
  -- from bit `i` on, machine `i` predicts the characteristic sequence of `A`
  have hagree (n : ℕ) : agrees k (charPrefix A n) i = true := by
    refine agrees_iff.mpr fun j hj hij => ?_
    rw [Bool.eq_iff_iff, getElem_charPrefix_eq_true_iff, hi j hij]
  obtain ⟨m, hm⟩ := exists_nat_gt (C * 2 ^ i)
  refine ⟨i + m + 1, ?_⟩
  have hnum : 2 ^ (2 * (m + 1)) ≤ num k (charPrefix A (i + m + 1)) := by
    have := term_le_num k (w := charPrefix A (i + m + 1)) (i := i) (by simp)
    rwa [term, ite_eq_left (hagree _), length_charPrefix,
      show i + m + 1 - i = m + 1 by omega] at this
  have hnum' : (2 : ℝ) ^ (2 * (m + 1)) ≤ num k (charPrefix A (i + m + 1)) := by
    exact_mod_cast hnum
  have hmpow : (m : ℝ) < 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self
  rw [martingale, length_charPrefix, lt_div_iff₀ (by positivity)]
  have h₁ : C * 2 ^ (i + m + 1) < 2 ^ m * 2 ^ (m + 1) := by
    rw [show i + m + 1 = i + (m + 1) by ring, pow_add, ← mul_assoc]
    exact mul_lt_mul_of_pos_right (hm.trans hmpow) (by positivity)
  have h₂ : (2 : ℝ) ^ m * 2 ^ (m + 1) ≤ 2 ^ (2 * (m + 1)) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

end TimeMartingale

open TimeMartingale

/-! ### Consequences -/

/-- **`DTIME (2 ^ (k * n))` has p-measure zero.** -/
theorem hasPMeasureZero_DTIME (k : ℕ) :
    HasPMeasureZero (DTIME encBits fun n => 2 ^ (k * n)) :=
  hasPMeasureZero_iff.mpr ⟨martingale k, isPMartingale k, DTIME_subset_successSet k⟩

/-- **`DTIME (2 ^ (k * n))` has measure zero in `E`.** -/
theorem hasMeasureZeroInE_DTIME (k : ℕ) :
    HasMeasureZeroInE (DTIME encBits fun n => 2 ^ (k * n)) :=
  (hasPMeasureZero_DTIME k).hasMeasureZeroInE

/-- **`DTIME (2 ^ (k * n))` is a proper subclass of `E`**, by the Measure Conservation Theorem.
-/
theorem DTIME_ssubset_E (k : ℕ) : DTIME encBits (fun n => 2 ^ (k * n)) ⊂ E encBits := by
  refine (Set.subset_iUnion (fun k => DTIME encBits fun n => 2 ^ (k * n)) k).ssubset_of_ne
    fun h => not_hasPMeasureZero_E ?_
  rw [E, ← h]
  exact hasPMeasureZero_DTIME k

/-- **Every singleton of a language in `E` has p-measure zero** [Lutz, Lemma 3.12][Lutz1992]. -/
theorem hasPMeasureZero_singleton {A : Set (List Bool)} (hA : A ∈ E encBits) :
    HasPMeasureZero {A} := by
  obtain ⟨k, hk⟩ := mem_E_iff.mp hA
  exact (hasPMeasureZero_DTIME k).mono (Set.singleton_subset_iff.mpr hk)

/-- **Every finite set of languages in `E` has p-measure zero** [Lutz, Lemma 3.12][Lutz1992]. -/
theorem hasPMeasureZero_of_finite {X : Set (Set (List Bool))} (hX : X.Finite)
    (hXE : X ⊆ E encBits) : HasPMeasureZero X := by
  have h := hasPMeasureZero_biUnion hX fun A hA => hasPMeasureZero_singleton (hXE hA)
  rwa [Set.biUnion_of_singleton] at h

/-- **`P` has p-measure zero**: it is within `DTIME (2 ^ n)`. -/
theorem hasPMeasureZero_P : HasPMeasureZero (P encBits) := by
  refine (hasPMeasureZero_DTIME 1).mono fun A hA => ?_
  obtain ⟨k, hk⟩ := mem_P_iff_exists_mem_DTIME.mp hA
  refine DTIME_mono_of_eventually_le ?_ hk
  filter_upwards [PolynomiallyBounded.eventually_lt_two_pow (f := (· ^ k)) (by fun_prop)]
    with n hn
  simpa only [one_mul] using hn.le

/-- **`P` has measure zero in `E`.** -/
theorem hasMeasureZeroInE_P : HasMeasureZeroInE (P encBits) :=
  hasPMeasureZero_P.hasMeasureZeroInE

end Cslib.Complexity.Measure
