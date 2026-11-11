/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.NearNeighbor.LSH
public import CslibFrontier.Probability.LocalitySensitiveHash.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Real

/-!
# Approximate near neighbours for probability-measure LSH families

`CslibFrontier.DataStructure.NearNeighbor.LSH` establishes the `(c, r)`-approximate near-neighbour
structure (`candidates`, `query`, `queryRepeat`, and parameters `rho`, `numHashes`, `numTables`)
over discrete seed laws `PMF ι`. This module extends the failure bounds to arbitrary
probability measures `ν : Measure ι` drawn independently across tables via `Measure.pi`, assuming
only that each pairwise collision event `{i | g i x = g i q}` is measurable.

All structural definitions (`candidates`, `query`, `queryRepeat`) and parameter lemmas (`rho`,
`numHashes`, `numTables`, `mul_pow_numHashes_le`, `one_le_numTables_mul_pow`) are reused directly
from `CslibFrontier.DataStructure.NearNeighbor.LSH`.

## Main results

* `Cslib.DataStructure.NearNeighbor.lintegral_pi_countP_candidates_le`: expected far candidates over
  `L` independent tables is at most `L |P| P₂`.
* `Cslib.DataStructure.NearNeighbor.measureReal_query_eq_none_le`: the failure bound
  `(1 - P₁) ^ L + L |P| P₂ / T` for probability-measure table seeds.
* `Cslib.DataStructure.NearNeighbor.measureReal_query_andHash_eq_none_le`: the AND-table bound
  `(1 - p₁ ^ k) ^ L + L |P| p₂ ^ k / T`.
* `Cslib.DataStructure.NearNeighbor.measureReal_query_numTables_eq_none_le`: failure at most
  `e⁻¹ + 1 / 3` with parameters `numHashes`, `numTables`, and `3 L`.
* `Cslib.DataStructure.NearNeighbor.measureReal_queryRepeat_numTables_eq_none_le`: `R` independent
  repetitions fail with probability at most `(e⁻¹ + 1 / 3) ^ R`.

## References

* [P. Indyk, R. Motwani, *Approximate Nearest Neighbors: Towards Removing the Curse of
  Dimensionality*][IndykMotwani1998]
* [S. Har-Peled, P. Indyk, R. Motwani, *Approximate Nearest Neighbor: Towards Removing the Curse
  of Dimensionality*][HarPeledIndykMotwani2012], Section 3.
-/

public section

namespace Cslib.DataStructure.NearNeighbor

open Cslib.Probability MeasureTheory
open scoped ENNReal

variable {ι X Y : Type*} [MeasurableSpace ι] [DecidableEq Y]

/-- A list count of measurable events, each of probability at most `B`, is measurable and has
Lebesgue integral at most `l.length * B`. -/
private theorem measurable_and_lintegral_countP_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Ω → X → Prop) [∀ ω x, Decidable (E ω x)] (B : ℝ≥0∞) :
    ∀ l : List X, (∀ x ∈ l, MeasurableSet {ω | E ω x}) →
      (∀ x ∈ l, μ {ω | E ω x} ≤ B) →
        Measurable (fun ω => ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞)) ∧
          ∫⁻ ω, ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞) ∂μ ≤ l.length * B
  | [], _, _ => by
      simp only [List.countP_nil, Nat.cast_zero, lintegral_zero, List.length_nil, zero_mul]
      exact ⟨measurable_const, le_rfl⟩
  | y :: l, hm, hl => by
      have hmy := hm y List.mem_cons_self
      have hy := hl y List.mem_cons_self
      obtain ⟨hm_ih, hi_ih⟩ := measurable_and_lintegral_countP_le μ E B l
        (fun x hx => hm x (List.mem_cons_of_mem y hx))
        (fun x hx => hl x (List.mem_cons_of_mem y hx))
      have hfun : (fun ω => (((y :: l).countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞)) =
          fun ω => {ω | E ω y}.indicator 1 ω + ((l.countP fun x => decide (E ω x) : ℕ) : ℝ≥0∞) := by
        funext ω
        rw [List.countP_cons]
        by_cases hω : E ω y
        · simp only [hω, decide_true, ite_true, Nat.cast_add, Nat.cast_one,
            Set.indicator_of_mem (show ω ∈ {ω | E ω y} from hω), Pi.one_apply, add_comm]
        · simp only [hω, decide_false, Bool.false_eq_true, ite_false, Nat.add_zero,
            Set.indicator_of_notMem (show ω ∉ {ω | E ω y} from hω), zero_add]
      rw [hfun]
      refine ⟨(measurable_one.indicator hmy).add hm_ih, ?_⟩
      rw [lintegral_add_left (measurable_one.indicator hmy), lintegral_indicator_one hmy,
        List.length_cons, Nat.cast_add, Nat.cast_one, add_comm (l.length : ℝ≥0∞) 1,
        add_mul, one_mul]
      exact add_le_add hy hi_ih

/-- A list count of far colliding candidates in a single table is measurable and bounded in
expectation by `P.length * ENNReal.ofReal P₂`. -/
private theorem measurable_and_lintegral_table_le {far : X → X → Prop} [DecidableRel far]
    (ν : Measure ι) [IsProbabilityMeasure ν] (g : ι → X → Y) (L : ℕ) (P : List X) (q : X)
    {P₂ : ℝ} (hmeas : ∀ x ∈ P, MeasurableSet {i | g i x = g i q})
    (hfar : ∀ x ∈ P, far x q → measureCollisionProb ν g x q ≤ P₂) (j : Fin L) :
    Measurable (fun s : Fin L → ι =>
        ((P.countP fun x => decide (g (s j) x = g (s j) q ∧ far x q) : ℕ) : ℝ≥0∞)) ∧
      ∫⁻ s, ((P.countP fun x => decide (g (s j) x = g (s j) q ∧ far x q) : ℕ) : ℝ≥0∞)
          ∂(Measure.pi fun _ : Fin L => ν) ≤ P.length * ENNReal.ofReal P₂ := by
  refine measurable_and_lintegral_countP_le (Measure.pi fun _ : Fin L => ν)
    (fun s x => g (s j) x = g (s j) q ∧ far x q) (ENNReal.ofReal P₂) P ?_ ?_
  · intro x hx
    by_cases hxf : far x q
    · have hset : {s : Fin L → ι | g (s j) x = g (s j) q ∧ far x q} =
          (fun s : Fin L → ι => s j) ⁻¹' {i | g i x = g i q} := by
        ext s
        simp only [Set.mem_preimage, Set.mem_ofPred_eq, hxf, and_true]
      rw [hset]
      exact (measurable_pi_apply j) (hmeas x hx)
    · have hset : {s : Fin L → ι | g (s j) x = g (s j) q ∧ far x q} = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, hxf, and_false, Set.mem_empty_iff_false]
      rw [hset]
      exact MeasurableSet.empty
  · intro x hx
    by_cases hxf : far x q
    · have hset : {s : Fin L → ι | g (s j) x = g (s j) q ∧ far x q} =
          Set.pi Set.univ fun k : Fin L => if k = j then {i | g i x = g i q} else Set.univ := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, hxf, and_true]
        exact ⟨fun hs k => by split_ifs with h <;> simp [h, hs], fun h => by simpa using h j⟩
      rw [hset, Measure.pi_pi]
      simp_rw [apply_ite (fun s => ν s), measure_univ]
      rw [Finset.prod_ite_eq', ite_eq_left (Finset.mem_univ j)]
      calc ν {i | g i x = g i q}
          = ENNReal.ofReal (measureCollisionProb ν g x q) := by
            rw [measureCollisionProb, measureReal_def,
              ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ ENNReal.ofReal P₂ := ENNReal.ofReal_le_ofReal (hfar x hx hxf)
    · have hset : {s : Fin L → ι | g (s j) x = g (s j) q ∧ far x q} = ∅ := by
        ext s
        simp only [Set.mem_ofPred_eq, hxf, and_false, Set.mem_empty_iff_false]
      rw [hset, measure_empty]
      exact bot_le

/-- **The far candidates are few on average**: over `L` independent probability-measure table
seeds, the expected number of far candidates is at most `L * |P| * P₂`. -/
theorem lintegral_pi_countP_candidates_le {far : X → X → Prop} [DecidableRel far]
    (ν : Measure ι) [IsProbabilityMeasure ν] (g : ι → X → Y) (L : ℕ) (P : List X) (q : X)
    {P₂ : ℝ} (hmeas : ∀ x ∈ P, MeasurableSet {i | g i x = g i q})
    (hfar : ∀ x ∈ P, far x q → measureCollisionProb ν g x q ≤ P₂) :
    Measurable (fun s : Fin L → ι =>
        (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞)) ∧
      ∫⁻ s, (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞)
          ∂(Measure.pi fun _ : Fin L => ν) ≤ L * (P.length * ENNReal.ofReal P₂) := by
  have hfun : (fun s : Fin L → ι =>
        (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞)) =
      fun s => ∑ j : Fin L,
        ((P.countP fun x => decide (g (s j) x = g (s j) q ∧ far x q) : ℕ) : ℝ≥0∞) := by
    funext s
    rw [countP_candidates, Nat.cast_sum]
  rw [hfun]
  have htab := measurable_and_lintegral_table_le (far := far) ν g L P q hmeas hfar
  refine ⟨Finset.measurable_sum _ fun j _ => (htab j).1, ?_⟩
  rw [lintegral_finsetSum _ fun j _ => (htab j).1]
  calc ∑ j : Fin L, ∫⁻ s,
        ((P.countP fun x => decide (g (s j) x = g (s j) q ∧ far x q) : ℕ) : ℝ≥0∞)
          ∂(Measure.pi fun _ : Fin L => ν)
      ≤ ∑ _j : Fin L, (P.length * ENNReal.ofReal P₂) :=
        Finset.sum_le_sum fun j _ => (htab j).2
    _ = L * (P.length * ENNReal.ofReal P₂) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The LSH failure bound for probability-measure seeds**: with `L` independent tables drawn
from `ν` and stop rule `T > 0`, `query` returns `none` with probability at most
`(1 - P₁) ^ L + L * |P| * P₂ / T`. -/
theorem measureReal_query_eq_none_le {far : X → X → Prop} [DecidableRel far]
    (ν : Measure ι) [IsProbabilityMeasure ν] (g : ι → X → Y) (L : ℕ) {T : ℕ} (hT : 0 < T)
    {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P) (hnf : ¬ far x₀ q) {P₁ P₂ : ℝ}
    (hmeas : ∀ x ∈ P, MeasurableSet {i | g i x = g i q})
    (hP₁ : P₁ ≤ measureCollisionProb ν g x₀ q) (hP₂ : 0 ≤ P₂)
    (hfar : ∀ x ∈ P, far x q → measureCollisionProb ν g x q ≤ P₂) :
    (Measure.pi fun _ : Fin L => ν).real {s | query g far s T P q = none} ≤
      (1 - P₁) ^ L + L * P.length * P₂ / T := by
  set μ := Measure.pi fun _ : Fin L => ν
  set A : Set (Fin L → ι) := Set.pi Set.univ fun _ : Fin L => {i | g i x₀ = g i q}ᶜ
  set f : (Fin L → ι) → ℝ≥0∞ := fun s =>
    (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞)
  set B : Set (Fin L → ι) := {s | (T : ℝ≥0∞) ≤ f s}
  have hsub : {s | query g far s T P q = none} ⊆ A ∪ B := by
    intro s hs
    by_cases hj : ∃ j, g (s j) x₀ = g (s j) q
    · exact Or.inr (show (T : ℝ≥0∞) ≤ f s from Nat.cast_le.2 (le_countP_candidates hx₀ hnf hj hs))
    · refine Or.inl fun j _ hj' => hj ⟨j, hj'⟩
  have hA : μ A = ν {i | g i x₀ = g i q}ᶜ ^ L := by
    rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  obtain ⟨hfm, hfl⟩ := lintegral_pi_countP_candidates_le ν g L P q hmeas hfar
  have hB : μ B ≤ L * (P.length * ENNReal.ofReal P₂) / T := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hT.ne'))
      (Or.inl (ENNReal.natCast_ne_top T)), mul_comm]
    exact (mul_meas_ge_le_lintegral hfm (T : ℝ≥0∞)).trans hfl
  have hcompl : (ν {i | g i x₀ = g i q}ᶜ).toReal = 1 - measureCollisionProb ν g x₀ q := by
    rw [← measureReal_def, probReal_compl_eq_one_sub (hmeas x₀ hx₀), measureCollisionProb]
  have hBfin : L * (P.length * ENNReal.ofReal P₂) / (T : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top))
      (by exact_mod_cast hT.ne')
  have hle : μ {s | query g far s T P q = none} ≤
      ν {i | g i x₀ = g i q}ᶜ ^ L + L * (P.length * ENNReal.ofReal P₂) / T := by
    refine (measure_mono hsub).trans ((measure_union_le A B).trans ?_)
    rw [hA]
    exact add_le_add le_rfl hB
  refine (ENNReal.toReal_le_add hle (ENNReal.pow_ne_top (measure_ne_top _ _)) hBfin).trans ?_
  rw [ENNReal.toReal_pow, hcompl, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hP₂, ← mul_assoc]
  have h1 : 0 ≤ 1 - measureCollisionProb ν g x₀ q :=
    sub_nonneg.2 (measureCollisionProb_le_one _ _ _ _)
  gcongr

/-- **The failure bound for AND tables under probability-measure seeds**: `(1 - p₁ ^ k) ^ L +
L * |P| * p₂ ^ k / T`. -/
theorem measureReal_query_andHash_eq_none_le {near far : X → X → Prop} [DecidableRel far]
    {seed : Measure ι} [IsProbabilityMeasure seed] {hash : ι → X → Y} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂) (hp₂ : 0 ≤ p₂)
    (hp : p₂ < p₁) (k L : ℕ) {T : ℕ} (hT : 0 < T) {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P)
    (hmeas : ∀ x ∈ P, MeasurableSet {i | hash i x = hash i q}) (hnear : near x₀ q) :
    (Measure.pi fun _ : Fin L => Measure.pi fun _ : Fin k => seed).real
        {s | query (andHash hash k) far s T P q = none} ≤
      (1 - p₁ ^ k) ^ L + L * P.length * p₂ ^ k / T := by
  have hk := h.measureAnd (hp₂.trans hp.le) k
  exact measureReal_query_eq_none_le _ _ L hT hx₀ (h.not_far hp hnear)
    (fun x hx => measurableSet_andHash_eq hash k (hmeas x hx))
    (hk.le_of_near x₀ q hnear) (pow_nonneg hp₂ k) fun x _ hx => hk.le_of_far x q hx

/-- **The `(c, r)`-near-neighbour guarantee with explicit parameters** for probability-measure
seeds: with `k = numHashes |P| p₂`, `L = numTables |P| p₁ p₂`, and stop limit `T = 3 * L`, the
query fails with probability at most `exp (-1) + 1 / 3`. -/
theorem measureReal_query_numTables_eq_none_le {near far : X → X → Prop} [DecidableRel far]
    {seed : Measure ι} [IsProbabilityMeasure seed] {hash : ι → X → Y} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂) (hp₂ : 0 < p₂)
    (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P)
    (hmeas : ∀ x ∈ P, MeasurableSet {i | hash i x = hash i q}) (hnear : near x₀ q) :
    (Measure.pi fun _ : Fin (numTables P.length p₁ p₂) =>
        Measure.pi fun _ : Fin (numHashes P.length p₂) => seed).real
        {s | query (andHash hash (numHashes P.length p₂)) far s (3 * numTables P.length p₁ p₂)
          P q = none} ≤ Real.exp (-1) + 1 / 3 := by
  have hn : 0 < P.length := List.length_pos_of_mem hx₀
  obtain ⟨hL, hnum⟩ := numTables_failure_bound_le hn hp₂ hp₂₁ hp₁
  have hbound := measureReal_query_andHash_eq_none_le h hp₂.le hp₂₁ (numHashes P.length p₂)
    (numTables P.length p₁ p₂) (by omega : 0 < 3 * numTables P.length p₁ p₂) hx₀ hmeas hnear
  exact hbound.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnum)

/-- `R` independent repetitions of a probability-measure query structure all fail with probability
the `R`-th power of a single structure's failure probability. -/
theorem measureReal_queryRepeat_eq_none {far : X → X → Prop} [DecidableRel far]
    (ν : Measure ι) [IsProbabilityMeasure ν] (g : ι → X → Y) (R L T : ℕ) (P : List X) (q : X) :
    (Measure.pi fun _ : Fin R => Measure.pi fun _ : Fin L => ν).real
        {s | queryRepeat g far s T P q = none} =
      ((Measure.pi fun _ : Fin L => ν).real {s | query g far s T P q = none}) ^ R := by
  have hset : {s : Fin R → Fin L → ι | queryRepeat g far s T P q = none} =
      Set.pi Set.univ fun _ : Fin R => {t | query g far t T P q = none} := by
    ext s
    simp only [Set.mem_ofPred_eq, queryRepeat_eq_none_iff, Set.mem_pi, Set.mem_univ, true_implies]
  rw [measureReal_def, hset, Measure.pi_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow, ← measureReal_def]

/-- **Amplification by repetition for probability-measure seeds**: `R` independent structures fail
with probability at most `(e⁻¹ + 1 / 3) ^ R`. -/
theorem measureReal_queryRepeat_numTables_eq_none_le {near far : X → X → Prop} [DecidableRel far]
    {seed : Measure ι} [IsProbabilityMeasure seed] {hash : ι → X → Y} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (measureCollisionProb seed hash) near far p₁ p₂) (hp₂ : 0 < p₂)
    (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) (R : ℕ) {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P)
    (hmeas : ∀ x ∈ P, MeasurableSet {i | hash i x = hash i q}) (hnear : near x₀ q) :
    (Measure.pi fun _ : Fin R => Measure.pi fun _ : Fin (numTables P.length p₁ p₂) =>
        Measure.pi fun _ : Fin (numHashes P.length p₂) => seed).real
        {s | queryRepeat (andHash hash (numHashes P.length p₂)) far s
          (3 * numTables P.length p₁ p₂) P q = none} ≤
      (Real.exp (-1) + 1 / 3) ^ R := by
  rw [measureReal_queryRepeat_eq_none]
  exact pow_le_pow_left₀ measureReal_nonneg
    (measureReal_query_numTables_eq_none_le h hp₂ hp₂₁ hp₁ hx₀ hmeas hnear) R

end Cslib.DataStructure.NearNeighbor
