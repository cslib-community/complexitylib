/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.LocalitySensitiveHash
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Probability.EventCount
import CslibFrontier.Probability.IID.Event
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Markov

/-!
# Approximate near neighbours by locality-sensitive hashing

The `(c, r)`-approximate near-neighbour problem asks for a data structure over a finite point set
`P`. Given a query `q` with some point of `P` within distance `r`, it must return a point of `P`
within distance `c r`. Indyk and Motwani solve it with locality-sensitive hashing
[IndykMotwani1998]; [HarPeledIndykMotwani2012], Theorem 3.4. Only the static structure is
formalized here; insertions and deletions are not modelled. The structure stores `L` hash tables,
each keyed by a hash `g (s j)` drawn independently from a seed law `ν`. In the source, `g` is the
AND of `k` hashes of an `(r, c r, p₁, p₂)`-sensitive family (`Cslib.Probability.andHash`).

**The structure.** `Cslib.DataStructure.NearNeighbor.candidates` lists, table by table, the points
of `P` that collide with `q`. The query (`Cslib.DataStructure.NearNeighbor.query`) scans the first
`T` candidates and returns the first one that is not far from `q`. Its answers are always correct
(`query_eq_some`). A run fails only by returning `none`. If a point `x₀ ∈ P` is not far from `q`,
then either `x₀` collides with `q` in no table, or the first `T` candidates are all far
(`le_countP_candidates`).

**The failure bound.** Let near pairs collide under `g` with probability at least `P₁` and far
pairs with probability at most `P₂`. The tables are drawn independently, so `x₀` misses all of them
with probability at most `(1 - P₁) ^ L`. The far candidates number at most `L |P| P₂` on average,
and Markov's inequality gives `Pr[fail] ≤ (1 - P₁) ^ L + L |P| P₂ / T`
(`toOuterMeasure_query_eq_none_le`).
The bound uses only the marginal law of each table, never independence across far points.

**Parameters.** For a `(p₁, p₂)`-sensitive family with `0 < p₂ < p₁ ≤ 1` and `n = |P|`, let
`ρ = log (1 / p₁) / log (1 / p₂)` (`Cslib.DataStructure.NearNeighbor.rho`). Take
`k = ⌈log n / log (1 / p₂)⌉` (`numHashes`), `L = ⌈n ^ ρ / p₁⌉` (`numTables`) and `T = 3 L`. Then
`n p₂ ^ k ≤ 1` and `L p₁ ^ k ≥ 1`, so the query fails with probability at most `e⁻¹ + 1 / 3 < 1`
(`toOuterMeasure_query_numTables_eq_none_le`). Repeating with `R` independent structures fails
with probability at most `(e⁻¹ + 1 / 3) ^ R` (`toOuterMeasure_queryRepeat_numTables_eq_none_le`).
Stopping after `3 L` candidates is the scanning rule of Indyk and Motwani [IndykMotwani1998]; see
[AndoniIndyk2008], Section 2.4 ("Strategy 1"), for an exposition.

**What is bounded, and what is not counted.** The query inspects at most `T` candidates, so it
tests `far` at most `T` times (`length_take_candidates_le`); there are at most `L |P|` candidates
in all (`length_candidates_le`). The parameters satisfy `k < log n / log (1 / p₂) + 1` and
`L < n ^ ρ / p₁ + 1` (`numHashes_lt`, `numTables_lt`), with `0 ≤ ρ < 1` (`rho_nonneg`,
`rho_lt_one`). No declaration counts operations. In a bucketed implementation a query would
evaluate `k L` base hashes and the tables would hold `n L` entries, but here a bucket is described
by filtering `P`, so `candidates` evaluates `g (s j)` on all of `P`. A dictionary keyed by hash
values, its word-RAM cost, the cost of one hash evaluation or distance test, and hence the
`n ^ ρ` query time, are not formalized.

## Main definitions

* `Cslib.DataStructure.NearNeighbor.candidates`: the points colliding with `q`, table by table.
* `Cslib.DataStructure.NearNeighbor.query`: the first of the first `T` candidates not far from `q`.
* `Cslib.DataStructure.NearNeighbor.queryRepeat`: the first answer of `R` independent structures.
* `Cslib.DataStructure.NearNeighbor.rho`, `numHashes`, `numTables`: the exponent `ρ` and the
  parameters `k` and `L`.

## Main results

* `Cslib.DataStructure.NearNeighbor.query_eq_some`: every answer is a point of `P` not far from
  `q`.
* `Cslib.DataStructure.NearNeighbor.toOuterMeasure_query_eq_none_le`: the failure bound
  `(1 - P₁) ^ L + L |P| P₂ / T`.
* `Cslib.DataStructure.NearNeighbor.toOuterMeasure_query_andHash_eq_none_le`: the failure bound
  `(1 - p₁ ^ k) ^ L + L |P| p₂ ^ k / T` for AND tables.
* `Cslib.DataStructure.NearNeighbor.toOuterMeasure_query_numTables_eq_none_le`: with the
  parameters `k`, `L`, `3 L`, failure at most `e⁻¹ + 1 / 3`.
* `Cslib.DataStructure.NearNeighbor.toOuterMeasure_queryRepeat_numTables_eq_none_le`: `R`
  repetitions fail with probability at most `(e⁻¹ + 1 / 3) ^ R`.
* `Cslib.DataStructure.NearNeighbor.length_take_candidates_le`, `length_candidates_le`: at most
  `min T (L |P|)` candidates are inspected.
* `Cslib.DataStructure.NearNeighbor.rho_lt_one`, `numHashes_lt`, `numTables_lt`: `ρ < 1` and the
  size of the parameters.

## References

* [P. Indyk, R. Motwani, *Approximate Nearest Neighbors: Towards Removing the Curse of
  Dimensionality*][IndykMotwani1998]
* [S. Har-Peled, P. Indyk, R. Motwani, *Approximate Nearest Neighbor: Towards Removing the Curse
  of Dimensionality*][HarPeledIndykMotwani2012], Section 3.
* [A. Andoni, P. Indyk, *Near-Optimal Hashing Algorithms for Approximate Nearest Neighbor in High
  Dimensions*][AndoniIndyk2008]
-/

public section

namespace Cslib.DataStructure.NearNeighbor

open Cslib.Probability
open scoped ENNReal

variable {ι X Y : Type*}

/-! ### The structure -/

section Structure

variable [DecidableEq Y]

/-- The points of `P` that collide with `q` under the table hashes `g (s 0), …, g (s (L - 1))`,
listed table by table, with repetitions. -/
@[expose] def candidates (g : ι → X → Y) {L : ℕ} (s : Fin L → ι) (P : List X) (q : X) : List X :=
  (List.finRange L).flatMap fun j => P.filter fun x => g (s j) x = g (s j) q

/-- The LSH query: scan the first `T` candidates and return the first one that is not far from
`q`. -/
@[expose] def query (g : ι → X → Y) (far : X → X → Prop) [DecidableRel far] {L : ℕ}
    (s : Fin L → ι) (T : ℕ) (P : List X) (q : X) : Option X :=
  ((candidates g s P q).take T).find? fun x => !decide (far x q)

theorem mem_candidates {g : ι → X → Y} {L : ℕ} {s : Fin L → ι} {P : List X} {q x : X} :
    x ∈ candidates g s P q ↔ x ∈ P ∧ ∃ j, g (s j) x = g (s j) q := by
  simp only [candidates, List.mem_flatMap, List.mem_finRange, true_and, List.mem_filter,
    decide_eq_true_eq]
  exact ⟨fun ⟨j, hx, hj⟩ => ⟨hx, j, hj⟩, fun ⟨hx, j, hj⟩ => ⟨j, hx, hj⟩⟩

variable {far : X → X → Prop} [DecidableRel far]

/-- **Soundness**: every answer of the query is a point of `P` that is not far from `q`. -/
theorem query_eq_some {g : ι → X → Y} {L : ℕ} {s : Fin L → ι} {T : ℕ} {P : List X} {q x : X}
    (h : query g far s T P q = some x) : x ∈ P ∧ ¬ far x q := by
  have hfar := List.find?_some h
  have hmem := List.mem_of_find?_eq_some h
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hfar
  exact ⟨(mem_candidates.1 (List.mem_of_mem_take hmem)).1, hfar⟩

/-- The far candidates, counted with multiplicity, are the far points of `P` colliding with `q`,
summed over the tables. -/
theorem countP_candidates (g : ι → X → Y) {L : ℕ} (s : Fin L → ι) (P : List X) (q : X) :
    (candidates g s P q).countP (fun x => decide (far x q)) =
      ∑ j : Fin L, P.countP fun x => decide (g (s j) x = g (s j) q ∧ far x q) := by
  rw [candidates, List.countP_flatMap, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  rw [Function.comp_apply, List.countP_filter]
  congr 1 with x : 1
  simp only [Bool.decide_and, Bool.and_comm]

/-- **The failure event.** If a point `x` that is not far from `q` collides with `q` in some table
and the query still returns `none`, then at least `T` far candidates were seen. -/
theorem le_countP_candidates {g : ι → X → Y} {L : ℕ} {s : Fin L → ι} {T : ℕ} {P : List X}
    {q x : X} (hx : x ∈ P) (hnf : ¬ far x q) (hj : ∃ j, g (s j) x = g (s j) q)
    (h : query g far s T P q = none) :
    T ≤ (candidates g s P q).countP fun y => decide (far y q) := by
  set C := candidates g s P q
  have hall : ∀ y ∈ C.take T, far y q := by
    intro y hy
    have := List.find?_eq_none.1 h y hy
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] using this
  have hxC : x ∈ C := mem_candidates.2 ⟨hx, hj⟩
  have hT : T ≤ C.length := by
    by_contra hlt
    exact hnf (hall x (by rw [List.take_of_length_le (by omega)]; exact hxC))
  calc T = (C.take T).length := by rw [List.length_take]; omega
    _ = (C.take T).countP fun y => decide (far y q) :=
        (List.countP_eq_length.2 fun y hy => decide_eq_true (hall y hy)).symm
    _ ≤ C.countP fun y => decide (far y q) := (List.take_sublist T C).countP_le

/-- Each of the `L` tables contributes at most `|P|` candidates. -/
theorem length_candidates_le (g : ι → X → Y) {L : ℕ} (s : Fin L → ι) (P : List X) (q : X) :
    (candidates g s P q).length ≤ L * P.length := by
  rw [candidates, List.length_flatMap]
  calc ((List.finRange L).map fun j => (P.filter fun x => g (s j) x = g (s j) q).length).sum
      ≤ ((List.finRange L).map fun _ => P.length).sum :=
        List.sum_le_sum fun j _ => List.length_filter_le _ _
    _ = L * P.length := by
        rw [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul]

/-- **The query inspects few candidates**: the scanned prefix has length at most `min T (L |P|)`,
so the query tests `far` at most `T` times. -/
theorem length_take_candidates_le (g : ι → X → Y) {L : ℕ} (s : Fin L → ι) (T : ℕ) (P : List X)
    (q : X) : ((candidates g s P q).take T).length ≤ min T (L * P.length) := by
  rw [List.length_take]
  exact min_le_min le_rfl (length_candidates_le g s P q)

end Structure

/-! ### The failure bound -/

/-- **The far candidates are few on average.** If far pairs collide under `g` with probability at
most `P₂`, the expected number of far candidates over `L` independent tables is at most
`L |P| P₂`. -/
theorem tsum_iid_mul_countP_candidates_le [DecidableEq Y] {far : X → X → Prop} [DecidableRel far]
    (ν : PMF ι) (g : ι → X → Y) (L : ℕ) (P : List X) (q : X) {P₂ : ℝ}
    (hfar : ∀ x ∈ P, far x q → collisionProb ν g x q ≤ P₂) :
    ∑' s, PMF.iid ν L s * (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞) ≤
      L * (P.length * ENNReal.ofReal P₂) := by
  simp only [countP_candidates, Nat.cast_sum, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => CompleteLattice.summable)]
  calc ∑ j : Fin L, ∑' s, PMF.iid ν L s *
        ((P.countP fun x => decide (g (s j) x = g (s j) q ∧ far x q) : ℕ) : ℝ≥0∞)
      ≤ ∑ _j : Fin L, (P.length * ENNReal.ofReal P₂) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine PMF.tsum_mul_countP_le (PMF.iid ν L)
          (fun s x => g (s j) x = g (s j) q ∧ far x q) _ P ?_
        intro x hx
        by_cases hxf : far x q
        · have hset : {s : Fin L → ι | g (s j) x = g (s j) q ∧ far x q} =
              {s | s j ∈ {i | g i x = g i q}} := by
            ext s
            simp only [Set.mem_ofPred_eq, hxf, and_true]
          rw [hset, PMF.toOuterMeasure_iid_eval]
          rw [← ENNReal.ofReal_toReal (PMF.toOuterMeasure_ne_top _ _)]
          exact ENNReal.ofReal_le_ofReal (hfar x hx hxf)
        · have hset : {s : Fin L → ι | g (s j) x = g (s j) q ∧ far x q} = ∅ := by
            ext s
            simp only [Set.mem_ofPred_eq, hxf, and_false, Set.mem_empty_iff_false]
          rw [hset, MeasureTheory.measure_empty]
          exact bot_le
    _ = L * (P.length * ENNReal.ofReal P₂) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The LSH failure bound.** Let `x₀ ∈ P` be not far from `q` and collide with `q` under `g` with
probability at least `P₁`, and let every far point of `P` collide with `q` with probability at most
`P₂`. With `L` independent tables and the stop rule after `T > 0` candidates, the query returns
`none` with probability at most `(1 - P₁) ^ L + L |P| P₂ / T`. -/
theorem toOuterMeasure_query_eq_none_le [DecidableEq Y] {far : X → X → Prop} [DecidableRel far]
    (ν : PMF ι) (g : ι → X → Y) (L : ℕ) {T : ℕ} (hT : 0 < T) {P : List X} {q x₀ : X}
    (hx₀ : x₀ ∈ P) (hnf : ¬ far x₀ q) {P₁ P₂ : ℝ} (hP₁ : P₁ ≤ collisionProb ν g x₀ q)
    (hP₂ : 0 ≤ P₂) (hfar : ∀ x ∈ P, far x q → collisionProb ν g x q ≤ P₂) :
    ((PMF.iid ν L).toOuterMeasure {s | query g far s T P q = none}).toReal ≤
      (1 - P₁) ^ L + L * P.length * P₂ / T := by
  set μ := PMF.iid ν L
  set A : Set (Fin L → ι) := {s | ∀ j, s j ∈ {i | g i x₀ = g i q}ᶜ}
  set B : Set (Fin L → ι) :=
    {s | (T : ℝ≥0∞) ≤ (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞)}
  have hsub : {s | query g far s T P q = none} ⊆ A ∪ B := by
    intro s hs
    by_cases hj : ∃ j, g (s j) x₀ = g (s j) q
    · exact Or.inr (show (T : ℝ≥0∞) ≤
        (((candidates g s P q).countP fun y => decide (far y q) : ℕ) : ℝ≥0∞) from
        Nat.cast_le.2 (le_countP_candidates hx₀ hnf hj hs))
    · exact Or.inl fun j hj' => hj ⟨j, hj'⟩
  have hA : μ.toOuterMeasure A = ν.toOuterMeasure {i | g i x₀ = g i q}ᶜ ^ L :=
    PMF.toOuterMeasure_iid_forall ν _ L
  have hB : μ.toOuterMeasure B ≤ L * (P.length * ENNReal.ofReal P₂) / T := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hT.ne'))
      (Or.inl (ENNReal.natCast_ne_top T)), mul_comm]
    exact (Cslib.Probability.PMF.mul_toOuterMeasure_le_tsum μ _ _).trans
      (tsum_iid_mul_countP_candidates_le ν g L P q hfar)
  have hcompl : (ν.toOuterMeasure {i | g i x₀ = g i q}ᶜ).toReal = 1 - collisionProb ν g x₀ q := by
    have h := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl ν {i | g i x₀ = g i q}
    rw [collisionProb]
    linarith
  have hBfin : L * (P.length * ENNReal.ofReal P₂) / (T : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top L)
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top))
      (by exact_mod_cast hT.ne')
  have hle : μ.toOuterMeasure {s | query g far s T P q = none} ≤
      ν.toOuterMeasure {i | g i x₀ = g i q}ᶜ ^ L + L * (P.length * ENNReal.ofReal P₂) / T :=
    (MeasureTheory.measure_mono hsub).trans
      ((MeasureTheory.measure_union_le A B).trans (by rw [hA]; exact add_le_add le_rfl hB))
  refine (ENNReal.toReal_le_add hle (ENNReal.pow_ne_top (PMF.toOuterMeasure_ne_top _ _))
    hBfin).trans ?_
  rw [ENNReal.toReal_pow, hcompl, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hP₂, ← mul_assoc]
  have h1 : 0 ≤ 1 - collisionProb ν g x₀ q := sub_nonneg.2 (collisionProb_le_one _ _ _ _)
  gcongr

/-! ### Amplified sensitive families -/

/-- **The failure bound for AND tables.** Each of `L` tables concatenates `k` hashes of a
`(p₁, p₂)`-sensitive family with `p₂ < p₁`. If some point of `P` is near `q`, the query with stop
rule `T > 0` fails with probability at most `(1 - p₁ ^ k) ^ L + L |P| p₂ ^ k / T`. -/
theorem toOuterMeasure_query_andHash_eq_none_le [DecidableEq Y] {near far : X → X → Prop}
    [DecidableRel far] {seed : PMF ι} {hash : ι → X → Y} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂) (hp₂ : 0 ≤ p₂)
    (hp : p₂ < p₁) (k L : ℕ) {T : ℕ} (hT : 0 < T) {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P)
    (hnear : near x₀ q) :
    ((PMF.iid (PMF.iid seed k) L).toOuterMeasure
        {s | query (andHash hash k) far s T P q = none}).toReal ≤
      (1 - p₁ ^ k) ^ L + L * P.length * p₂ ^ k / T := by
  have hk := h.and (hp₂.trans hp.le) k
  exact toOuterMeasure_query_eq_none_le _ _ L hT hx₀ (h.not_far hp hnear)
    (hk.le_of_near x₀ q hnear) (pow_nonneg hp₂ k) fun x _ hx => hk.le_of_far x q hx

/-! ### Parameters -/

/-- The LSH exponent `ρ = log (1 / p₁) / log (1 / p₂)`. -/
@[expose] noncomputable def rho (p₁ p₂ : ℝ) : ℝ :=
  Real.log (1 / p₁) / Real.log (1 / p₂)

/-- The number of hashes per table, `k = ⌈log n / log (1 / p₂)⌉`. -/
@[expose] noncomputable def numHashes (n : ℕ) (p₂ : ℝ) : ℕ :=
  ⌈Real.log n / Real.log (1 / p₂)⌉₊

/-- The number of tables, `L = ⌈n ^ ρ / p₁⌉`. -/
noncomputable def numTables (n : ℕ) (p₁ p₂ : ℝ) : ℕ :=
  ⌈(n : ℝ) ^ rho p₁ p₂ / p₁⌉₊

theorem rho_nonneg {p₁ p₂ : ℝ} (hp₂ : 0 < p₂) (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) :
    0 ≤ rho p₁ p₂ :=
  div_nonneg (Real.log_nonneg (one_le_one_div (hp₂.trans hp₂₁) hp₁))
    (Real.log_nonneg (one_le_one_div hp₂ (hp₂₁.le.trans hp₁)))

/-- The exponent is below one, so the query cost `n ^ ρ` is sublinear. -/
theorem rho_lt_one {p₁ p₂ : ℝ} (hp₂ : 0 < p₂) (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) :
    rho p₁ p₂ < 1 := by
  have ha : 0 < Real.log (1 / p₂) :=
    Real.log_pos (one_lt_one_div hp₂ (hp₂₁.trans_le hp₁))
  rw [rho, div_lt_one ha]
  exact Real.log_lt_log (one_div_pos.2 (hp₂.trans hp₂₁)) (one_div_lt_one_div_of_lt hp₂ hp₂₁)

/-- With `k = numHashes n p₂`, far points are rare: `n p₂ ^ k ≤ 1`. -/
theorem mul_pow_numHashes_le {n : ℕ} (hn : 0 < n) {p₂ : ℝ} (hp₂ : 0 < p₂) (hp₂₁ : p₂ < 1) :
    n * p₂ ^ numHashes n p₂ ≤ 1 := by
  set k := numHashes n p₂
  have ha : 0 < Real.log (1 / p₂) := Real.log_pos (one_lt_one_div hp₂ hp₂₁)
  have hk : Real.log n / Real.log (1 / p₂) ≤ k := Nat.le_ceil _
  have hlog : Real.log n ≤ Real.log ((1 / p₂) ^ k) := by
    rw [Real.log_pow]
    rwa [div_le_iff₀ ha] at hk
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : (n : ℝ) ≤ (1 / p₂) ^ k :=
    (Real.log_le_log_iff hn' (pow_pos (one_div_pos.2 hp₂) k)).1 hlog
  calc (n : ℝ) * p₂ ^ k ≤ (1 / p₂) ^ k * p₂ ^ k :=
        mul_le_mul_of_nonneg_right hle (pow_nonneg hp₂.le k)
    _ = 1 := by rw [← mul_pow, one_div, inv_mul_cancel₀ hp₂.ne', one_pow]

/-- With `k = numHashes n p₂` and `L = numTables n p₁ p₂`, near points are found:
`L p₁ ^ k ≥ 1`. -/
theorem one_le_numTables_mul_pow {n : ℕ} (hn : 0 < n) {p₁ p₂ : ℝ} (hp₂ : 0 < p₂)
    (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) :
    1 ≤ numTables n p₁ p₂ * p₁ ^ numHashes n p₂ := by
  set k := numHashes n p₂
  have hp₁0 : 0 < p₁ := hp₂.trans hp₂₁
  have ha : 0 < Real.log (1 / p₂) := Real.log_pos (one_lt_one_div hp₂ (hp₂₁.trans_le hp₁))
  have hb : 0 ≤ Real.log (1 / p₁) := Real.log_nonneg (one_le_one_div hp₁0 hp₁)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (k : ℝ) < Real.log n / Real.log (1 / p₂) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.log_natCast_nonneg n) ha.le)
  -- `(k - 1) log (1 / p₁) ≤ ρ log n`
  have hkb : ((k : ℝ) - 1) * Real.log (1 / p₁) ≤ rho p₁ p₂ * Real.log n := by
    have h1 : (k : ℝ) - 1 ≤ Real.log n / Real.log (1 / p₂) := by linarith
    calc ((k : ℝ) - 1) * Real.log (1 / p₁) ≤ Real.log n / Real.log (1 / p₂) * Real.log (1 / p₁) :=
          mul_le_mul_of_nonneg_right h1 hb
      _ = rho p₁ p₂ * Real.log n := by rw [rho]; ring
  have hpos : 0 < (n : ℝ) ^ rho p₁ p₂ / p₁ * p₁ ^ k :=
    mul_pos (div_pos (Real.rpow_pos_of_pos hn' _) hp₁0) (pow_pos hp₁0 k)
  have hone : 1 ≤ (n : ℝ) ^ rho p₁ p₂ / p₁ * p₁ ^ k := by
    rw [← Real.log_nonneg_iff hpos, Real.log_mul (div_pos (Real.rpow_pos_of_pos hn' _) hp₁0).ne'
      (pow_pos hp₁0 k).ne', Real.log_div (Real.rpow_pos_of_pos hn' _).ne' hp₁0.ne',
      Real.log_rpow hn', Real.log_pow]
    rw [one_div, Real.log_inv] at hkb
    linarith
  calc (1 : ℝ) ≤ (n : ℝ) ^ rho p₁ p₂ / p₁ * p₁ ^ k := hone
    _ ≤ numTables n p₁ p₂ * p₁ ^ k :=
        mul_le_mul_of_nonneg_right (Nat.le_ceil _) (pow_nonneg hp₁0.le k)

theorem numHashes_lt (n : ℕ) {p₂ : ℝ} (hp₂ : 0 < p₂) (hp₂₁ : p₂ < 1) :
    (numHashes n p₂ : ℝ) < Real.log n / Real.log (1 / p₂) + 1 :=
  Nat.ceil_lt_add_one (div_nonneg (Real.log_natCast_nonneg n)
    (Real.log_nonneg (one_le_one_div hp₂ hp₂₁.le)))

theorem numTables_lt (n : ℕ) {p₁ p₂ : ℝ} (hp₁ : 0 < p₁) :
    (numTables n p₁ p₂ : ℝ) < (n : ℝ) ^ rho p₁ p₂ / p₁ + 1 :=
  Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hp₁.le)

/-- For `(p₁, p₂)`-sensitive parameters `0 < p₂ < p₁ ≤ 1` and `n > 0`, the explicit choices
`k = numHashes n p₂` and `L = numTables n p₁ p₂` satisfy `0 < L` and
`(1 - p₁ ^ k) ^ L + L * n * p₂ ^ k / (3 * L) ≤ exp (-1) + 1 / 3`. -/
theorem numTables_failure_bound_le {n : ℕ} (hn : 0 < n) {p₁ p₂ : ℝ} (hp₂ : 0 < p₂)
    (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) :
    0 < numTables n p₁ p₂ ∧
      (1 - p₁ ^ numHashes n p₂) ^ numTables n p₁ p₂ +
        numTables n p₁ p₂ * n * p₂ ^ numHashes n p₂ / (3 * numTables n p₁ p₂) ≤
          Real.exp (-1) + 1 / 3 := by
  set k := numHashes n p₂
  set L := numTables n p₁ p₂
  have hp₁0 : 0 < p₁ := hp₂.trans hp₂₁
  have hLp : 1 ≤ (L : ℝ) * p₁ ^ k := one_le_numTables_mul_pow hn hp₂ hp₂₁ hp₁
  have hnp : (n : ℝ) * p₂ ^ k ≤ 1 := mul_pow_numHashes_le hn hp₂ (hp₂₁.trans_le hp₁)
  have hpk0 : 0 ≤ p₁ ^ k := pow_nonneg hp₁0.le k
  have hpk1 : p₁ ^ k ≤ 1 := pow_le_one₀ hp₁0.le hp₁
  have hL : 0 < L := by
    by_contra h0
    rw [show L = 0 by omega, Nat.cast_zero, zero_mul] at hLp
    linarith
  refine ⟨hL, add_le_add ?_ ?_⟩
  · calc (1 - p₁ ^ k) ^ L ≤ Real.exp (-p₁ ^ k) ^ L := by
          refine pow_le_pow_left₀ (by linarith) ?_ L
          linarith [Real.add_one_le_exp (-p₁ ^ k)]
      _ = Real.exp (-(L * p₁ ^ k)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  · have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- **The `(c, r)`-near-neighbour guarantee with explicit parameters**, for the static structure
([HarPeledIndykMotwani2012], Theorem 3.4, which also covers updates). The scanning rule is that of
[IndykMotwani1998]; see [AndoniIndyk2008], Section 2.4. Let `hash` be `(p₁, p₂)`-sensitive with
`0 < p₂ < p₁ ≤ 1`. Use `L = numTables n p₁ p₂` tables of `k = numHashes n p₂` hashes each, with
`n = |P|`, and stop after `3 L` candidates. If some point of `P` is near `q`, the query fails with
probability at most `e⁻¹ + 1 / 3`. -/
theorem toOuterMeasure_query_numTables_eq_none_le [DecidableEq Y] {near far : X → X → Prop}
    [DecidableRel far] {seed : PMF ι} {hash : ι → X → Y} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂) (hp₂ : 0 < p₂)
    (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P)
    (hnear : near x₀ q) :
    ((PMF.iid (PMF.iid seed (numHashes P.length p₂)) (numTables P.length p₁ p₂)).toOuterMeasure
        {s | query (andHash hash (numHashes P.length p₂)) far s (3 * numTables P.length p₁ p₂)
          P q = none}).toReal ≤ Real.exp (-1) + 1 / 3 := by
  have hn : 0 < P.length := List.length_pos_of_mem hx₀
  obtain ⟨hL, hnum⟩ := numTables_failure_bound_le hn hp₂ hp₂₁ hp₁
  have hbound := toOuterMeasure_query_andHash_eq_none_le h hp₂.le hp₂₁ (numHashes P.length p₂)
    (numTables P.length p₁ p₂) (by omega : 0 < 3 * numTables P.length p₁ p₂) hx₀ hnear
  exact hbound.trans (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnum)

/-! ### Repetition -/

section Repetition

variable [DecidableEq Y] {far : X → X → Prop} [DecidableRel far]

/-- Query `R` independently built structures in turn and return the first answer. -/
@[expose] def queryRepeat (g : ι → X → Y) (far : X → X → Prop) [DecidableRel far] {R L : ℕ}
    (s : Fin R → Fin L → ι) (T : ℕ) (P : List X) (q : X) : Option X :=
  (List.finRange R).findSome? fun r => query g far (s r) T P q

theorem queryRepeat_eq_none_iff {g : ι → X → Y} {R L : ℕ} {s : Fin R → Fin L → ι} {T : ℕ}
    {P : List X} {q : X} :
    queryRepeat g far s T P q = none ↔ ∀ r, query g far (s r) T P q = none := by
  simp only [queryRepeat, List.findSome?_eq_none_iff, List.mem_finRange, true_implies]

/-- Every answer of the repeated query is a point of `P` that is not far from `q`. -/
theorem queryRepeat_eq_some {g : ι → X → Y} {R L : ℕ} {s : Fin R → Fin L → ι} {T : ℕ}
    {P : List X} {q x : X} (h : queryRepeat g far s T P q = some x) : x ∈ P ∧ ¬ far x q := by
  obtain ⟨r, -, hr⟩ := List.exists_of_findSome?_eq_some h
  exact query_eq_some hr

/-- `R` independent structures all fail with the `R`-th power of the failure probability of one. -/
theorem toOuterMeasure_queryRepeat_eq_none (ν : PMF ι) (g : ι → X → Y) (R L T : ℕ) (P : List X)
    (q : X) :
    (PMF.iid (PMF.iid ν L) R).toOuterMeasure {s | queryRepeat g far s T P q = none} =
      (PMF.iid ν L).toOuterMeasure {s | query g far s T P q = none} ^ R := by
  have hset : {s : Fin R → Fin L → ι | queryRepeat g far s T P q = none} =
      {s | ∀ r, s r ∈ {t | query g far t T P q = none}} := by
    ext s
    simp only [Set.mem_ofPred_eq, queryRepeat_eq_none_iff]
  rw [hset, PMF.toOuterMeasure_iid_forall]

/-- **Amplification by repetition.** With the parameters of
`toOuterMeasure_query_numTables_eq_none_le`, `R` independent structures all fail with probability at
most `(e⁻¹ + 1 / 3) ^ R`. -/
theorem toOuterMeasure_queryRepeat_numTables_eq_none_le {near : X → X → Prop} {seed : PMF ι}
    {hash : ι → X → Y} {p₁ p₂ : ℝ}
    (h : IsLocalitySensitive (collisionProb seed hash) near far p₁ p₂) (hp₂ : 0 < p₂)
    (hp₂₁ : p₂ < p₁) (hp₁ : p₁ ≤ 1) (R : ℕ) {P : List X} {q x₀ : X} (hx₀ : x₀ ∈ P)
    (hnear : near x₀ q) :
    ((PMF.iid (PMF.iid (PMF.iid seed (numHashes P.length p₂)) (numTables P.length p₁ p₂)) R
        ).toOuterMeasure {s | queryRepeat (andHash hash (numHashes P.length p₂)) far s
          (3 * numTables P.length p₁ p₂) P q = none}).toReal ≤ (Real.exp (-1) + 1 / 3) ^ R := by
  rw [toOuterMeasure_queryRepeat_eq_none, ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg
    (toOuterMeasure_query_numTables_eq_none_le h hp₂ hp₂₁ hp₁ hx₀ hnear) R

end Repetition

end Cslib.DataStructure.NearNeighbor
