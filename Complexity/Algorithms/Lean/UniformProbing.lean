/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Dictionary
public import Complexity.Languages.Probabilistic.RandomOracle
public import Complexity.Probability.PMF.Expect
public import Complexity.Probability.PMF.Uniform
public import Complexity.Probability.Product
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Uniform Probing in Open-Addressed Hash Tables

This file formalizes the classical uniform-probing model of open-addressed hashing from
[Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms*, third edition (MIT Press,
2009), Section 11.4 ("Open addressing", pp. 270–277)][CLRS2009], realizing the bounded-capacity
insert-only dictionary specification `Cslib.Algorithms.Lean.Dictionary.spec` over `m` table slots
(`2 * n_max ≤ m`).

In the textbook uniform-probing ("uniform hashing") model, each key `u : Fin U` is assigned an
independent uniform random permutation `π u : Equiv.Perm (Fin m)`
(`PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))`), which may equivalently be sampled lazily on
demand via `Cslib.RandomOracle.uniform_interpret_eq_lazy`
(`Complexity/Languages/Probabilistic/RandomOracle.lean`).

## Source statements and notation mapping

In [CLRS2009], third edition, Section 11.4:
* An open-address table has `m` slots (`Fin m`) and holds `n` stored elements (`O.card` or
  `(Dictionary.dom s).card`, bounded by `n_max` with `2 * n_max ≤ m`), giving load factor
  `α = n / m < 1` (`α ≤ 1 / 2` when `2 * n ≤ m`).
* Under uniform hashing (p. 271), each key's probe sequence `h(k, 0), h(k, 1), …, h(k, m - 1)` is
  equally likely to be any of the `m!` permutations of `{0, 1, …, m - 1}` (`Equiv.Perm (Fin m)`).
  Every search or insertion counts all inspected slots along the probe sequence up to and including
  the stopping slot (`unsuccessfulProbes O σ = missedProbes O σ + 1` and
  `probeCount T u σ = unsuccessfulProbes (otherOccupiedSlots T u) σ`).
* **Theorem 11.6 (pp. 274–275)** states that in an open-address hash table with load factor
  `α = n / m < 1`, the expected number of probes in an unsuccessful search is at most
  `1 / (1 - α) = m / (m - n)` under uniform hashing; its proof establishes the exact occupancy tail
  product `Pr{X ≥ i} = ∏_{j = 0}^{i - 2} ((n - j) / (m - j)) ≤ α ^ (i - 1)`.
* **Corollary 11.7 (p. 276)** states that inserting an element into an open-address hash table with
  load factor `α < 1` requires at most `1 / (1 - α) = m / (m - n)` probes on average.
* **Theorem 11.8 (p. 276)** states that when each key in the table is equally likely to be searched
  for, the expected number of probes in a successful search is at most `(1 / α) ln(1 / (1 - α))`.
  Its proof first establishes for a fixed stored key `u` that searching for `u` follows the exact
  same probe sequence as when `u` was inserted (`probeCount_runTable_eq_firstInsert`), so if `u` was
  first inserted after a prefix `ops₁` reaching state `s₁` with `i = (Dictionary.dom s₁).card` keys,
  the expected number of probes for `u` is at most `1 / (1 - i / m) = m / (m - i)`
  (`expect_probeCount_of_mem_dom_le`, and `≤ 2` when `2 * n_max ≤ m` via
  `expect_probeCount_of_mem_dom_le_two`). The uniform-key-averaged logarithmic endpoint
  `(1 / α) ln(1 / (1 - α))` is not formalized here.

## Main definitions

* `Cslib.Algorithms.Lean.UniformProbing.allOccupied`,
  `Cslib.Algorithms.Lean.UniformProbing.missedProbesFrom`,
  `Cslib.Algorithms.Lean.UniformProbing.missedProbes`,
  `Cslib.Algorithms.Lean.UniformProbing.unsuccessfulProbes`,
  `Cslib.Algorithms.Lean.UniformProbing.probeSlotIndex`: slot-probe predicates, probe counts, and
  first-available slot index along a probe permutation `σ : Equiv.Perm (Fin m)`.
* `Cslib.Algorithms.Lean.UniformProbing.Table`,
  `Cslib.Algorithms.Lean.UniformProbing.emptyTable`,
  `Cslib.Algorithms.Lean.UniformProbing.occupiedSlots`,
  `Cslib.Algorithms.Lean.UniformProbing.otherOccupiedSlots`,
  `Cslib.Algorithms.Lean.UniformProbing.probeCount`: pure open-addressed table of `m` slots and
  per-key probe count.
* `Cslib.Algorithms.Lean.UniformProbing.tableGet`,
  `Cslib.Algorithms.Lean.UniformProbing.tableInsert`,
  `Cslib.Algorithms.Lean.UniformProbing.tableStep`,
  `Cslib.Algorithms.Lean.UniformProbing.runTable`,
  `Cslib.Algorithms.Lean.UniformProbing.TableRep`: open-addressed `get`/`insert` operations and
  representation invariant linking `Table U m` to `Dictionary.State U`.

## Main results

* `Cslib.Algorithms.Lean.UniformProbing.toOuterMeasure_allOccupied_eq_prod`,
  `Cslib.Algorithms.Lean.UniformProbing.toOuterMeasure_allOccupied_le_pow`: on a table with
  `n = O.card ≤ m` occupied slots, the probability over
  `σ ← PMF.uniformOfFintype (Equiv.Perm (Fin m))`
  that the first `k ≤ m` probes all hit `O` (`k < unsuccessfulProbes O σ`) is
  `∏ i ∈ Finset.range k, ((n - i : ℝ≥0∞) / (m - i : ℝ≥0∞)) ≤ ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k`
  ([CLRS2009], third edition, proof of Theorem 11.6, pp. 274–275).
* `Cslib.Algorithms.Lean.UniformProbing.expect_unsuccessfulProbes_le`,
  `Cslib.Algorithms.Lean.UniformProbing.expect_unsuccessfulProbes_le_two`,
  `Cslib.Algorithms.Lean.UniformProbing.expect_probeCount_of_eq_none_le`,
  `Cslib.Algorithms.Lean.UniformProbing.expect_probeCount_of_eq_none_le_two`: Theorem 11.6
  (pp. 274–275) and Corollary 11.7 (p. 276) of [CLRS2009], third edition — an unsuccessful lookup or
  fresh-key insertion into a table holding `n < m` keys makes at most `m / (m - n)` probes in
  expectation (`≤ 2` when `2 * n ≤ m`).
* `Cslib.Algorithms.Lean.UniformProbing.TableRep.probeCount_tableInsert_of_isSome`,
  `Cslib.Algorithms.Lean.UniformProbing.probeCount_runTable_eq_firstInsert`,
  `Cslib.Algorithms.Lean.UniformProbing.expect_probeCount_of_mem_dom_le`,
  `Cslib.Algorithms.Lean.UniformProbing.expect_probeCount_of_mem_dom_le_two`: pathwise
  insertion-cost identity and per-key intermediate bound from the proof of Theorem 11.8 (p. 276) of
  [CLRS2009], third edition — a successful lookup of a fixed present key `u ∈ dom s` makes the
  exact same number of probes as the operation that first inserted `u` after prefix `ops₁`
  (reaching state `s₁`), which is at most `m / (m - (Dictionary.dom s₁).card) ≤ 2` in expectation
  when `2 * n_max ≤ m` (the uniform-key-averaged `(1 / α) ln(1 / (1 - α))` endpoint of Theorem 11.8
  is not formalized here).
* `Cslib.Algorithms.Lean.UniformProbing.uniform_interpret_eq_lazy_perm`: eager sampling of the
  independent permutation family `Fin U → Equiv.Perm (Fin m)` agrees in distribution with lazy
  on-demand oracle evaluation (`RandomOracle.uniform_interpret_eq_lazy`).

## Representation space note

Storing an explicit table of independent permutations in `(Equiv.Perm (Fin m)) ^ U` requires
`U * log₂ (m!)` bits (`Ω(U)` machine words when `U = poly(n_max) ≫ n_max`). To achieve an
`O(n_max)`-word self-contained Word-RAM dictionary,
`Complexity/Algorithms/WordRAM/Dictionary/UniformProbing.lean` pairs a 2-universal multiply-shift
primary hash `h₁(u) ∈ Fin (2 ^ M)` with a tabulated odd stride `h₂(u) ∈ Fin (2 ^ M)`
([CLRS2009], third edition, Section 11.4, "Double hashing", pp. 272–274), reusing the
open-addressed table invariants proved here.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 270–277][CLRS2009]
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017]
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.UniformProbing

open Cslib.Algorithms.Lean
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ## Section 1: Permutation probe counts and stopping indices -/

/-- Event that the first `k` slots `σ ⟨0, _⟩, ..., σ ⟨k - 1, _⟩` of permutation `σ` all belong to
the occupied slot set `O`. -/
def allOccupied {m : ℕ} (O : Finset (Fin m)) (k : ℕ) (σ : Equiv.Perm (Fin m)) : Prop :=
  ∀ i : Fin m, i.val < k → σ i ∈ O

instance instDecidableAllOccupied {m : ℕ} (O : Finset (Fin m)) (k : ℕ)
    (σ : Equiv.Perm (Fin m)) : Decidable (allOccupied O k σ) := by
  unfold allOccupied
  infer_instance

@[simp]
theorem allOccupied_zero {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    allOccupied O 0 σ := by
  intro i hi
  omega

theorem allOccupied_succ_iff {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k < m)
    (σ : Equiv.Perm (Fin m)) :
    allOccupied O (k + 1) σ ↔ allOccupied O k σ ∧ σ ⟨k, hk⟩ ∈ O := by
  constructor
  · intro h
    refine ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h, hk_mem⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact h i hlt
    · have : i = ⟨k, hk⟩ := Fin.ext heq
      rwa [this]

theorem allOccupied_mono {m : ℕ} {O : Finset (Fin m)} {j k : ℕ} (hjk : j ≤ k)
    {σ : Equiv.Perm (Fin m)} (h : allOccupied O k σ) : allOccupied O j σ :=
  fun i hi => h i (lt_of_lt_of_le hi hjk)

/-- Count how many consecutive slots `σ ⟨idx, _⟩, σ ⟨idx + 1, _⟩, ...` belong to `O`, for up to
`rem` steps starting at `idx`. -/
def missedProbesFrom {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    ℕ → ℕ → ℕ
  | 0, _ => 0
  | rem + 1, idx =>
    if h : idx < m then
      if σ ⟨idx, h⟩ ∈ O then 1 + missedProbesFrom O σ rem (idx + 1) else 0
    else 0

/-- Number of consecutive probes `σ 0, σ 1, ...` that hit `O` before the first slot outside `O`. -/
def missedProbes {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : ℕ :=
  missedProbesFrom O σ m 0

/-- Total number of slot probes `1 + missedProbes O σ` made by an unsuccessful search (or fresh-key
insertion) against occupied slot set `O` along permutation `σ`. -/
def unsuccessfulProbes {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) : ℕ :=
  1 + missedProbes O σ

theorem missedProbesFrom_le {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (rem idx : ℕ) : missedProbesFrom O σ rem idx ≤ rem := by
  induction rem generalizing idx with
  | zero => simp [missedProbesFrom]
  | succ rem ih =>
    simp only [missedProbesFrom]
    split_ifs
    · have := ih (idx + 1)
      omega
    · omega
    · omega

theorem missedProbes_le {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    missedProbes O σ ≤ m :=
  missedProbesFrom_le O σ m 0

theorem mem_of_lt_missedProbesFrom {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    {rem idx t : ℕ} (hrem : idx + rem ≤ m) (ht : t < missedProbesFrom O σ rem idx) :
    ∃ h : idx + t < m, σ ⟨idx + t, h⟩ ∈ O := by
  induction rem generalizing idx t with
  | zero =>
    simp [missedProbesFrom] at ht
  | succ rem ih =>
    have hidx : idx < m := by omega
    simp only [missedProbesFrom, hidx, ↓reduceDIte] at ht
    split_ifs at ht with hmem
    · cases t with
      | zero =>
        exact ⟨hidx, by simpa using hmem⟩
      | succ t =>
        have ht' : t < missedProbesFrom O σ rem (idx + 1) := by omega
        obtain ⟨h', hmem'⟩ := ih (idx := idx + 1) (by omega) ht'
        refine ⟨by omega, ?_⟩
        have heq : (⟨idx + (t + 1), by omega⟩ : Fin m) = ⟨idx + 1 + t, h'⟩ :=
          Fin.ext (show idx + (t + 1) = idx + 1 + t by omega)
        rwa [heq]
    · omega

theorem notMem_at_missedProbesFrom {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    {rem idx : ℕ} (hrem : idx + rem ≤ m) (hlt : missedProbesFrom O σ rem idx < rem) :
    ∃ h : idx + missedProbesFrom O σ rem idx < m,
      σ ⟨idx + missedProbesFrom O σ rem idx, h⟩ ∉ O := by
  induction rem generalizing idx with
  | zero => omega
  | succ rem ih =>
    have hidx : idx < m := by omega
    simp only [missedProbesFrom, hidx, ↓reduceDIte] at hlt ⊢
    split_ifs with hmem
    · simp only [hmem, ↓reduceIte] at hlt
      have hlt' : missedProbesFrom O σ rem (idx + 1) < rem := by omega
      obtain ⟨h', hnot⟩ := ih (idx := idx + 1) (by omega) hlt'
      refine ⟨by omega, ?_⟩
      have heq :
          (⟨idx + (1 + missedProbesFrom O σ rem (idx + 1)), by omega⟩ : Fin m) =
            ⟨idx + 1 + missedProbesFrom O σ rem (idx + 1), h'⟩ :=
        Fin.ext (show idx + (1 + missedProbesFrom O σ rem (idx + 1)) =
          idx + 1 + missedProbesFrom O σ rem (idx + 1) by omega)
      rwa [heq]
    · exact ⟨hidx, by simpa using hmem⟩

/-- For any `k ≤ m`, at least `k` probes miss (`k ≤ missedProbes O σ`) if and only if the first `k`
slots of `σ` all belong to `O`. -/
theorem le_missedProbes_iff_allOccupied {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k ≤ m)
    (σ : Equiv.Perm (Fin m)) :
    k ≤ missedProbes O σ ↔ allOccupied O k σ := by
  constructor
  · intro hle i hi
    have hit : i.val < missedProbesFrom O σ m 0 := lt_of_lt_of_le hi hle
    obtain ⟨_, hmem⟩ := mem_of_lt_missedProbesFrom (by omega) hit
    simpa using hmem
  · intro hall
    by_contra hnot
    have hlt : missedProbesFrom O σ m 0 < k := not_le.mp hnot
    obtain ⟨hidx, hnotMem⟩ := notMem_at_missedProbesFrom (by omega) (lt_of_lt_of_le hlt hk)
    have hidx' : missedProbesFrom O σ m 0 < m := by omega
    have hnotMem' : σ ⟨missedProbesFrom O σ m 0, hidx'⟩ ∉ O := by
      convert hnotMem using 2
      ext
      simp
    exact hnotMem' (hall ⟨missedProbesFrom O σ m 0, hidx'⟩ hlt)

/-- For any `k ≤ m`, an unsuccessful search inspects more than `k` slots
(`k < unsuccessfulProbes O σ`) if and only if the first `k` slots of `σ` all belong to `O`. -/
theorem lt_unsuccessfulProbes_iff_allOccupied {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k ≤ m)
    (σ : Equiv.Perm (Fin m)) :
    k < unsuccessfulProbes O σ ↔ allOccupied O k σ := by
  rw [unsuccessfulProbes, ← le_missedProbes_iff_allOccupied hk]
  omega

/-- When `O.card < m`, not all `m` slots of `σ` can belong to `O`. -/
theorem not_allOccupied_self_of_card_lt {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m)
    (σ : Equiv.Perm (Fin m)) : ¬ allOccupied O m σ := by
  intro hall
  have hsub : Finset.univ.map σ.toEmbedding ⊆ O := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    exact hall i i.isLt
  have hcard := Finset.card_le_card hsub
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- When `O.card < m`, `missedProbes O σ < m` for every permutation `σ`. -/
theorem missedProbes_lt_of_card_lt {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m)
    (σ : Equiv.Perm (Fin m)) : missedProbes O σ < m := by
  have hle := missedProbes_le O σ
  have hne : missedProbes O σ ≠ m := by
    intro heq
    exact not_allOccupied_self_of_card_lt hO σ
      ((le_missedProbes_iff_allOccupied le_rfl σ).mp (by omega))
  omega

/-- The probe index `⟨missedProbes O σ, _⟩ : Fin m` of the first slot along `σ` outside `O` when
`O.card < m`. -/
def probeSlotIndex {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (hO : O.card < m) : Fin m :=
  ⟨missedProbes O σ, missedProbes_lt_of_card_lt hO σ⟩

@[simp]
theorem val_probeSlotIndex {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m))
    (hO : O.card < m) : (probeSlotIndex O σ hO).val = missedProbes O σ :=
  rfl

theorem mem_of_lt_probeSlotIndex {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hO : O.card < m) {i : Fin m} (hi : i.val < (probeSlotIndex O σ hO).val) :
    σ i ∈ O :=
  (le_missedProbes_iff_allOccupied (le_of_lt (missedProbes_lt_of_card_lt hO σ)) σ).mp le_rfl i hi

theorem notMem_apply_probeSlotIndex {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hO : O.card < m) : σ (probeSlotIndex O σ hO) ∉ O := by
  obtain ⟨_, hnot⟩ := notMem_at_missedProbesFrom (O := O) (σ := σ) (by omega)
    (missedProbes_lt_of_card_lt hO σ)
  simpa [probeSlotIndex, missedProbes] using hnot

/-- Exact characterization of `missedProbes O σ`: for any `i₀ : Fin m`, `missedProbes O σ = i₀.val`
if and only if all earlier probes `i < i₀` lie in `O` and `σ i₀ ∉ O`. -/
theorem missedProbes_eq_iff {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)} (i₀ : Fin m) :
    missedProbes O σ = i₀.val ↔ allOccupied O i₀.val σ ∧ σ i₀ ∉ O := by
  constructor
  · intro heq
    have hlt : missedProbes O σ < m := heq ▸ i₀.isLt
    have hall : allOccupied O i₀.val σ :=
      (le_missedProbes_iff_allOccupied (le_of_lt i₀.isLt) σ).mp (by omega)
    obtain ⟨hidx, hnot⟩ := notMem_at_missedProbesFrom (O := O) (σ := σ) (by omega) hlt
    have hi₀ : (⟨0 + missedProbesFrom O σ m 0, hidx⟩ : Fin m) = i₀ := by
      ext
      simpa [missedProbes] using heq
    rw [hi₀] at hnot
    exact ⟨hall, hnot⟩
  · rintro ⟨hall, hnot⟩
    have hge : i₀.val ≤ missedProbes O σ :=
      (le_missedProbes_iff_allOccupied (le_of_lt i₀.isLt) σ).mpr hall
    have hnot_succ : ¬ (i₀.val + 1 ≤ missedProbes O σ) := by
      intro hle
      have hall' := (le_missedProbes_iff_allOccupied i₀.isLt σ).mp hle
      exact hnot (hall' i₀ (by omega))
    omega

theorem probeSlotIndex_eq_iff {m : ℕ} {O : Finset (Fin m)} {σ : Equiv.Perm (Fin m)}
    (hO : O.card < m) (i₀ : Fin m) :
    probeSlotIndex O σ hO = i₀ ↔ allOccupied O i₀.val σ ∧ σ i₀ ∉ O := by
  rw [Fin.ext_iff, val_probeSlotIndex, missedProbes_eq_iff]

/-- Tail-sum identity on `Fin m`: when `O.card < m`, the total number of probes
`unsuccessfulProbes O σ` equals the number of `k ∈ Finset.range m` for which `allOccupied O k σ`
holds. -/
theorem unsuccessfulProbes_eq_sum_boole {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m)
    (σ : Equiv.Perm (Fin m)) :
    unsuccessfulProbes O σ =
      ∑ k ∈ Finset.range m, if allOccupied O k σ then 1 else 0 := by
  have hlt : missedProbes O σ < m := missedProbes_lt_of_card_lt hO σ
  have hcongr : ∀ k ∈ Finset.range m,
      (if allOccupied O k σ then 1 else 0) =
        (if k ∈ Finset.range (missedProbes O σ + 1) then 1 else 0) := by
    intro k hk
    have hk_le : k ≤ m := le_of_lt (Finset.mem_range.mp hk)
    simp only [Finset.mem_range, Nat.lt_succ_iff, le_missedProbes_iff_allOccupied hk_le]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr (by
      intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega),
    Finset.sum_const, smul_eq_mul, mul_one, Finset.card_range, unsuccessfulProbes, Nat.add_comm]

/-! ## Section 2: Textbook Uniform-Probing Expected-Probe Bounds ([CLRS2009], Theorem 11.6) -/

/-- Set of permutations `σ : Equiv.Perm (Fin m)` whose first `k` probes all belong to `O`. -/
def occPermSet {m : ℕ} (O : Finset (Fin m)) (k : ℕ) : Finset (Equiv.Perm (Fin m)) :=
  Finset.univ.filter fun σ => allOccupied O k σ

@[simp]
theorem mem_occPermSet {m : ℕ} {O : Finset (Fin m)} {k : ℕ} {σ : Equiv.Perm (Fin m)} :
    σ ∈ occPermSet O k ↔ allOccupied O k σ := by
  simp [occPermSet]

@[simp]
theorem occPermSet_zero {m : ℕ} (O : Finset (Fin m)) :
    occPermSet O 0 = Finset.univ := by
  ext σ
  simp [occPermSet]

/-- Right-multiplying `σ` by `Equiv.swap ⟨k, hk⟩ j` (for `k ≤ j.val`) preserves `allOccupied O k`.
-/
private theorem allOccupied_mul_swap_iff {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k < m)
    {j : Fin m} (hj : k ≤ j.val) (σ : Equiv.Perm (Fin m)) :
    allOccupied O k (σ * Equiv.swap ⟨k, hk⟩ j) ↔ allOccupied O k σ := by
  have hfix : ∀ i : Fin m, i.val < k → (Equiv.swap ⟨k, hk⟩ j) i = i := by
    intro i hi
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      have : i.val = k := congrArg Fin.val h
      omega
    · intro h
      have : i.val = j.val := congrArg Fin.val h
      omega
  refine ⟨fun h i hi => ?_, fun h i hi => ?_⟩
  · have := h i hi
    rwa [Equiv.Perm.mul_apply, hfix i hi] at this
  · rw [Equiv.Perm.mul_apply, hfix i hi]
    exact h i hi

/-- By transposition symmetry `σ ↦ σ * Equiv.swap ⟨k, hk⟩ j`, for every `j : Fin m` with
`k ≤ j.val`, the number of permutations in `occPermSet O k` with `σ j ∈ O` equals
`(occPermSet O (k + 1)).card`. -/
private theorem card_filter_occPermSet_eq_succ {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k < m)
    {j : Fin m} (hj : k ≤ j.val) :
    ((occPermSet O k).filter fun σ => σ j ∈ O).card = (occPermSet O (k + 1)).card := by
  classical
  let τ : Equiv.Perm (Fin m) := Equiv.swap ⟨k, hk⟩ j
  refine Finset.card_bij (fun σ _ => σ * τ) ?_ ?_ ?_
  · intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨hσ_occ, hσj⟩
    rw [mem_occPermSet] at hσ_occ ⊢
    rw [allOccupied_succ_iff hk]
    refine ⟨(allOccupied_mul_swap_iff hk hj σ).mpr hσ_occ, ?_⟩
    simpa [τ] using hσj
  · intro σ₁ _ σ₂ _ heq
    exact mul_right_cancel heq
  · intro σ hσ
    rw [mem_occPermSet, allOccupied_succ_iff hk] at hσ
    refine ⟨σ * τ, ?_, ?_⟩
    · rw [Finset.mem_filter, mem_occPermSet]
      refine ⟨(allOccupied_mul_swap_iff hk hj σ).mpr hσ.1, ?_⟩
      simpa [τ] using hσ.2
    · ext x
      simp [τ]

/-- For any permutation `σ : Equiv.Perm (Fin m)`, the number of indices `i : Fin m` with `σ i ∈ O`
equals `O.card`. -/
private theorem card_filter_apply_mem_eq {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    (Finset.univ.filter fun i : Fin m => σ i ∈ O).card = O.card := by
  refine Finset.card_bij (fun i _ => σ i) ?_ ?_ ?_
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · intro i₁ _ i₂ _ h
    exact σ.injective h
  · intro y hy
    exact ⟨σ.symm y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hy]⟩, by simp⟩

/-- Partition of a `Finset` into elements satisfying `p` and `¬ p`. -/
private theorem card_filter_add_card_filter_neg {α : Type*} (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter fun x => ¬ p x).card = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    by_cases hp : p a <;> simp [Finset.filter_insert, hp, ha] <;> omega

/-- Cardinality of `{i : Fin m | i.val < k}` when `k ≤ m`. -/
private theorem card_filter_val_lt {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun i : Fin m => i.val < k).card = k := by
  refine (Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_).trans (Finset.card_range k)
  · intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  · intro i₁ _ i₂ _ h
    exact Fin.ext h
  · intro j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    exact ⟨⟨j, lt_of_lt_of_le hj_lt hk⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_lt⟩, rfl⟩

/-- Cardinality of `{i : Fin m | k ≤ i.val}` when `k ≤ m`. -/
private theorem card_filter_val_ge {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun i : Fin m => k ≤ i.val).card = m - k := by
  have hpart := card_filter_add_card_filter_neg
    (Finset.univ : Finset (Fin m)) (fun i : Fin m => i.val < k)
  have hneg : (Finset.univ.filter fun i : Fin m => ¬ i.val < k) =
      Finset.univ.filter fun i : Fin m => k ≤ i.val := by
    ext i
    simp
  rw [hneg, card_filter_val_lt hk, Finset.card_univ, Fintype.card_fin] at hpart
  omega

/-- For any `σ ∈ occPermSet O k` with `k ≤ m`, the number of remaining indices `j ≥ k` satisfying
`σ j ∈ O` is `O.card - k` (and `k ≤ O.card`). -/
private theorem card_filter_ge_and_mem {m : ℕ} {O : Finset (Fin m)} {k : ℕ} (hk : k ≤ m)
    {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ occPermSet O k) :
    ((Finset.univ.filter fun j : Fin m => k ≤ j.val).filter fun j => σ j ∈ O).card =
      O.card - k := by
  rw [mem_occPermSet] at hσ
  set S := Finset.univ.filter fun j : Fin m => σ j ∈ O
  have hpart := card_filter_add_card_filter_neg S (fun j : Fin m => j.val < k)
  have hlt_eq : S.filter (fun j : Fin m => j.val < k) =
      Finset.univ.filter fun j : Fin m => j.val < k := by
    ext j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨hσ j h, h⟩⟩
  have hge_eq : S.filter (fun j : Fin m => ¬ j.val < k) =
      (Finset.univ.filter fun j : Fin m => k ≤ j.val).filter fun j => σ j ∈ O := by
    ext j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
    exact and_comm
  rw [hlt_eq, hge_eq, card_filter_val_lt hk, card_filter_apply_mem_eq O σ] at hpart
  omega

/-- **Exact step recurrence for `occPermSet`**: for any `k < m`,
`(m - k) * (occPermSet O (k + 1)).card = (O.card - k) * (occPermSet O k).card`. -/
theorem mul_card_occPermSet_succ {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k < m) :
    (m - k) * (occPermSet O (k + 1)).card = (O.card - k) * (occPermSet O k).card := by
  classical
  set J_ge := Finset.univ.filter fun j : Fin m => k ≤ j.val
  have hsum_j :
      ∑ j ∈ J_ge, ((occPermSet O k).filter fun σ => σ j ∈ O).card =
        (m - k) * (occPermSet O (k + 1)).card := by
    have hcongr : ∀ j ∈ J_ge,
        ((occPermSet O k).filter fun σ => σ j ∈ O).card = (occPermSet O (k + 1)).card := by
      intro j hj
      exact card_filter_occPermSet_eq_succ O hk (Finset.mem_filter.mp hj).2
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul,
      card_filter_val_ge (le_of_lt hk)]
  have hsum_σ :
      ∑ j ∈ J_ge, ((occPermSet O k).filter fun σ => σ j ∈ O).card =
        (O.card - k) * (occPermSet O k).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    have hcongr : ∀ σ ∈ occPermSet O k,
        (∑ j ∈ J_ge, if σ j ∈ O then 1 else 0) = O.card - k := by
      intro σ hσ
      rw [← Finset.card_filter]
      exact card_filter_ge_and_mem (le_of_lt hk) hσ
    rw [Finset.sum_congr rfl hcongr, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  omega

/-- **Exact textbook product formula ([CLRS2009], Proof of Theorem 11.6)**:
for any occupied slot set `O : Finset (Fin m)` and `k ≤ m`, the probability over a uniform random
permutation `σ ← PMF.uniformOfFintype (Equiv.Perm (Fin m))` that the first `k` probes all hit `O`
(`k < unsuccessfulProbes O σ`) is `∏ i ∈ Finset.range k, ((O.card - i : ℝ≥0∞) / (m - i : ℝ≥0∞))`.
-/
theorem toOuterMeasure_allOccupied_eq_prod {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k ≤ m) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure {σ | allOccupied O k σ} =
      ∏ i ∈ Finset.range k, (((O.card - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞)) := by
  induction k with
  | zero =>
    rw [PMF.toOuterMeasure_uniformOfFintype]
    change ((occPermSet O 0).card : ℝ≥0∞) * (Fintype.card (Equiv.Perm (Fin m)) : ℝ≥0∞)⁻¹ = _
    rw [occPermSet_zero, Finset.card_univ, Finset.prod_range_zero]
    have hcard_pos : 0 < Fintype.card (Equiv.Perm (Fin m)) := Fintype.card_pos_iff.mpr ⟨1⟩
    exact ENNReal.mul_inv_cancel (by exact_mod_cast hcard_pos.ne') (ENNReal.natCast_ne_top _)
  | succ k ih =>
    have hk_lt : k < m := hk
    rw [Finset.prod_range_succ, ← ih (le_of_lt hk_lt)]
    rw [PMF.toOuterMeasure_uniformOfFintype, PMF.toOuterMeasure_uniformOfFintype]
    change ((occPermSet O (k + 1)).card : ℝ≥0∞) * (Fintype.card (Equiv.Perm (Fin m)) : ℝ≥0∞)⁻¹ =
      ((occPermSet O k).card : ℝ≥0∞) * (Fintype.card (Equiv.Perm (Fin m)) : ℝ≥0∞)⁻¹ *
        (((O.card - k : ℕ) : ℝ≥0∞) / ((m - k : ℕ) : ℝ≥0∞))
    have hrec : (((m - k : ℕ) : ℝ≥0∞) * ((occPermSet O (k + 1)).card : ℝ≥0∞)) =
        ((O.card - k : ℕ) : ℝ≥0∞) * ((occPermSet O k).card : ℝ≥0∞) := by
      exact_mod_cast mul_card_occPermSet_succ O hk_lt
    have hmk_ne0 : ((m - k : ℕ) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (by omega : m - k ≠ 0)
    have hmk_top : ((m - k : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    have hcard_eq : ((occPermSet O (k + 1)).card : ℝ≥0∞) =
        ((occPermSet O k).card : ℝ≥0∞) * (((O.card - k : ℕ) : ℝ≥0∞) / ((m - k : ℕ) : ℝ≥0∞)) := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm ((occPermSet O k).card : ℝ≥0∞), ← hrec,
        mul_comm ((m - k : ℕ) : ℝ≥0∞), mul_assoc, ENNReal.mul_inv_cancel hmk_ne0 hmk_top, mul_one]
    rw [hcard_eq]
    ring

/-- Each factor `(n - i) / (m - i)` for `i < m` and `n ≤ m` is at most `n / m`. -/
theorem sub_div_sub_le_div {n m i : ℕ} (hnm : n ≤ m) (hi : i < m) :
    (((n - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞)) ≤ (n : ℝ≥0∞) / (m : ℝ≥0∞) := by
  have hm_ne0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm_top : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hmi_ne0 : ((m - i : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m - i ≠ 0)
  have hmi_top : ((m - i : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (m - i)
  have hnat : (n - i) * m ≤ n * (m - i) := by
    rw [Nat.sub_mul, Nat.mul_sub, Nat.mul_comm n i]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_left i hnm) (n * m)
  have hcast : ((n - i : ℕ) : ℝ≥0∞) * (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) * ((m - i : ℕ) : ℝ≥0∞) := by
    exact_mod_cast hnat
  calc
    (((n - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞))
      = (((n - i : ℕ) : ℝ≥0∞) * (m : ℝ≥0∞)) * ((m : ℝ≥0∞)⁻¹ * ((m - i : ℕ) : ℝ≥0∞)⁻¹) := by
          rw [div_eq_mul_inv, mul_assoc, ← mul_assoc (m : ℝ≥0∞),
            ENNReal.mul_inv_cancel hm_ne0 hm_top, one_mul]
    _ ≤ ((n : ℝ≥0∞) * ((m - i : ℕ) : ℝ≥0∞)) * ((m : ℝ≥0∞)⁻¹ * ((m - i : ℕ) : ℝ≥0∞)⁻¹) := by
          gcongr
    _ = (n : ℝ≥0∞) / (m : ℝ≥0∞) := by
          rw [div_eq_mul_inv, mul_assoc, mul_left_comm ((m - i : ℕ) : ℝ≥0∞),
            ENNReal.mul_inv_cancel hmi_ne0 hmi_top, mul_one]

/-- **Upper bound `(n / m) ^ k` on the `k`-probe tail probability ([CLRS2009], Proof of Theorem
11.6)**: for any occupied slot set `O : Finset (Fin m)` and `k ≤ m`, the probability over a uniform
random permutation `σ` that the first `k` probes all hit `O` is at most
`((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k`. -/
theorem toOuterMeasure_allOccupied_le_pow {m : ℕ} (O : Finset (Fin m)) {k : ℕ} (hk : k ≤ m) :
    (PMF.uniformOfFintype (Equiv.Perm (Fin m))).toOuterMeasure {σ | allOccupied O k σ} ≤
      ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k := by
  have hO_le : O.card ≤ m := by
    simpa using Finset.card_le_univ O
  rw [toOuterMeasure_allOccupied_eq_prod O hk]
  calc
    (∏ i ∈ Finset.range k, (((O.card - i : ℕ) : ℝ≥0∞) / ((m - i : ℕ) : ℝ≥0∞)))
      ≤ ∏ _i ∈ Finset.range k, ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) :=
        Finset.prod_le_prod fun i hi =>
          sub_div_sub_le_div hO_le (lt_of_lt_of_le (Finset.mem_range.mp hi) hk)
    _ = ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k := by
        simp [Finset.prod_const]

/-- Finite geometric sum identity in `ℝ≥0∞` without subtraction: for `n < m`,
`∑ k ∈ Finset.range j, (n / m) ^ k + (m / (m - n)) * (n / m) ^ j = m / (m - n)`. -/
theorem sum_div_pow_add_tail {n m : ℕ} (hnm : n < m) (j : ℕ) :
    (∑ k ∈ Finset.range j, ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k) +
      ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j =
        (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
  have hm_ne0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm_top : (m : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top m
  have hmn_ne0 : ((m - n : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m - n ≠ 0)
  have hmn_top : ((m - n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (m - n)
  have hstep : 1 + ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) =
      (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
    have hmul : ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) =
        (n : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
        mul_comm (n : ℝ≥0∞), ← mul_assoc, mul_right_comm (m : ℝ≥0∞),
        ENNReal.mul_inv_cancel hm_ne0 hm_top, one_mul, mul_comm]
    rw [hmul, ← ENNReal.div_self hmn_ne0 hmn_top, ← ENNReal.add_div]
    congr 1
    exact_mod_cast Nat.sub_add_cancel (le_of_lt hnm)
  induction j with
  | zero => simp
  | succ j ih =>
    have htail : ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j +
        ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ (j + 1) =
          ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) * ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j := by
      rw [pow_succ, ← mul_assoc,
        mul_comm ((m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞)) (((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j),
        mul_assoc]
      nth_rw 1 [← mul_one (((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ j)]
      rw [← mul_add, hstep, mul_comm]
    rw [Finset.sum_range_succ, add_assoc, htail, ih]

/-- For `n < m`, any partial geometric sum `∑ k ∈ Finset.range j, (n / m) ^ k` is at most
`m / (m - n)`. -/
theorem sum_div_pow_le {n m : ℕ} (hnm : n < m) (j : ℕ) :
    (∑ k ∈ Finset.range j, ((n : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k) ≤
      (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) := by
  rw [← sum_div_pow_add_tail hnm j]
  exact le_self_add

/-- When `2 * n ≤ m` and `0 < m`, `m / (m - n) ≤ 2` (`1 / (1 - α) ≤ 2` for load factor `α ≤ 1 / 2`).
-/
theorem div_sub_le_two {n m : ℕ} (hm : 0 < m) (h2n : 2 * n ≤ m) :
    (m : ℝ≥0∞) / ((m - n : ℕ) : ℝ≥0∞) ≤ 2 := by
  have hmn_ne0 : ((m - n : ℕ) : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : m - n ≠ 0)
  have hmn_top : ((m - n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top (m - n)
  rw [ENNReal.div_le_iff_le_mul (Or.inl hmn_ne0) (Or.inl hmn_top)]
  exact_mod_cast (by omega : m ≤ 2 * (m - n))

/-- **Theorem 11.6 of [CLRS2009] (Expected probes in an unsuccessful search)**:
for any occupied slot set `O : Finset (Fin m)` with `O.card < m`, the expected number of probes
`unsuccessfulProbes O σ` over a uniform random permutation
`σ ← PMF.uniformOfFintype (Equiv.Perm (Fin m))` is at most `m / (m - O.card)`. -/
theorem expect_unsuccessfulProbes_le {m : ℕ} {O : Finset (Fin m)} (hO : O.card < m) :
    (∑' σ : Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Equiv.Perm (Fin m)) σ * (unsuccessfulProbes O σ : ℝ≥0∞)) ≤
        (m : ℝ≥0∞) / ((m - O.card : ℕ) : ℝ≥0∞) := by
  classical
  let μ := PMF.uniformOfFintype (Equiv.Perm (Fin m))
  have hdecomp : ∀ σ : Equiv.Perm (Fin m),
      μ σ * (unsuccessfulProbes O σ : ℝ≥0∞) =
        ∑ k ∈ Finset.range m, μ σ * (if allOccupied O k σ then 1 else 0) := by
    intro σ
    rw [← Finset.mul_sum]
    congr 1
    exact_mod_cast unsuccessfulProbes_eq_sum_boole hO σ
  change (∑' σ : Equiv.Perm (Fin m), μ σ * (unsuccessfulProbes O σ : ℝ≥0∞)) ≤ _
  simp_rw [hdecomp]
  rw [tsum_fintype, Finset.sum_comm]
  have hterm : ∀ k ∈ Finset.range m,
      (∑ σ : Equiv.Perm (Fin m), μ σ * (if allOccupied O k σ then (1 : ℝ≥0∞) else 0)) =
        μ.toOuterMeasure {σ | allOccupied O k σ} := by
    intro k _
    rw [PMF.toOuterMeasure_apply, tsum_fintype]
    refine Finset.sum_congr rfl fun σ _ => ?_
    unfold Set.indicator
    by_cases h : allOccupied O k σ
    · have hmem : σ ∈ {σ | allOccupied O k σ} := h
      simp [h, hmem]
    · have hmem : σ ∉ {σ | allOccupied O k σ} := h
      simp [h, hmem]
  rw [Finset.sum_congr rfl hterm]
  calc
    (∑ k ∈ Finset.range m, μ.toOuterMeasure {σ | allOccupied O k σ})
      ≤ ∑ k ∈ Finset.range m, ((O.card : ℝ≥0∞) / (m : ℝ≥0∞)) ^ k :=
        Finset.sum_le_sum fun k hk =>
          toOuterMeasure_allOccupied_le_pow O (le_of_lt (Finset.mem_range.mp hk))
    _ ≤ (m : ℝ≥0∞) / ((m - O.card : ℕ) : ℝ≥0∞) := sum_div_pow_le hO m

/-- **Half-load corollary of Theorem 11.6 ([CLRS2009], Section 11.4)**:
when `0 < m` and `2 * O.card ≤ m` (load factor `α = O.card / m ≤ 1 / 2`), the expected number of
probes in an unsuccessful search is at most `2`. -/
theorem expect_unsuccessfulProbes_le_two {m : ℕ} {O : Finset (Fin m)}
    (hm : 0 < m) (h2n : 2 * O.card ≤ m) :
    (∑' σ : Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Equiv.Perm (Fin m)) σ * (unsuccessfulProbes O σ : ℝ≥0∞)) ≤ 2 :=
  (expect_unsuccessfulProbes_le (by omega)).trans (div_sub_le_two hm h2n)


/-! ## Section 3: Open-Addressed Table Model ([CLRS2009], Section 11.4, pp. 270–276) -/

/-- Pure open-addressed hash table of `m` slots over key universe `Fin U`, where each slot holds
`none` (empty) or `some (u, v)` (occupied by key `u` with value `v`). -/
abbrev Table (U m : ℕ) := Fin m → Option (Fin U × ℕ)

/-- The initially empty table of `m` slots. -/
def emptyTable (U m : ℕ) : Table U m := fun _ => none

/-- The finite set of currently occupied slot indices in table `T`. -/
def occupiedSlots {U m : ℕ} (T : Table U m) : Finset (Fin m) :=
  Finset.univ.filter fun j => (T j).isSome

/-- The finite set of slot indices in `T` occupied by keys distinct from `u`. -/
def otherOccupiedSlots {U m : ℕ} (T : Table U m) (u : Fin U) : Finset (Fin m) :=
  Finset.univ.filter fun j => (T j).isSome ∧ (T j).map Prod.fst ≠ some u

/-- Total number of slot probes `1 + missedProbes (otherOccupiedSlots T u) σ` made when probing
table `T` for key `u` along permutation `σ`. -/
def probeCount {U m : ℕ} (T : Table U m) (u : Fin U) (σ : Equiv.Perm (Fin m)) : ℕ :=
  unsuccessfulProbes (otherOccupiedSlots T u) σ

@[simp]
theorem occupiedSlots_emptyTable (U m : ℕ) :
    occupiedSlots (emptyTable U m) = ∅ := by
  ext j
  simp [occupiedSlots, emptyTable]

@[simp]
theorem otherOccupiedSlots_emptyTable (U m : ℕ) (u : Fin U) :
    otherOccupiedSlots (emptyTable U m) u = ∅ := by
  ext j
  simp [otherOccupiedSlots, emptyTable]

theorem mem_otherOccupiedSlots_iff {U m : ℕ} {T : Table U m} {u : Fin U} {j : Fin m} :
    j ∈ otherOccupiedSlots T u ↔ ∃ u' v', T j = some (u', v') ∧ u' ≠ u := by
  simp only [otherOccupiedSlots, Finset.mem_filter, Finset.mem_univ, true_and]
  cases h : T j with
  | none => simp
  | some p =>
    rcases p with ⟨u', v'⟩
    simp

theorem otherOccupiedSlots_subset_occupiedSlots {U m : ℕ} (T : Table U m) (u : Fin U) :
    otherOccupiedSlots T u ⊆ occupiedSlots T := by
  intro j hj
  rcases mem_otherOccupiedSlots_iff.mp hj with ⟨u', v', hTj, -⟩
  simp [occupiedSlots, hTj]

/-- Open-addressed table representation invariant linking concrete slot array `T : Table U m` to
abstract dictionary state `s : Dictionary.State U` under permutation family
`π : Fin U → Equiv.Perm (Fin m)`. -/
structure TableRep {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) (s : Dictionary.State U)
    (T : Table U m) : Prop where
  /-- Every occupied slot `j` holds `(u, v)` with `s u = some v` at key `u`'s stopping probe index.
  -/
  slot_spec : ∀ j u v, T j = some (u, v) →
    s u = some v ∧ ∃ h : missedProbes (otherOccupiedSlots T u) (π u) < m,
      j = π u ⟨missedProbes (otherOccupiedSlots T u) (π u), h⟩
  /-- Every present key `u` with `s u = some v` is stored at its stopping probe index. -/
  key_spec : ∀ u v, s u = some v →
    ∃ h : missedProbes (otherOccupiedSlots T u) (π u) < m,
      T (π u ⟨missedProbes (otherOccupiedSlots T u) (π u), h⟩) = some (u, v)

/-- The empty table represents `Dictionary.empty U` under any permutation family `π`. -/
theorem tableRep_empty {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) :
    TableRep π (Dictionary.empty U) (emptyTable U m) where
  slot_spec j _ _ h := by simp [emptyTable] at h
  key_spec u _ h := by simp [Dictionary.empty] at h

/-- Under `TableRep π s T`, each key `u` occupies at most one slot in `T`. -/
theorem TableRep.slot_eq_of_same_key {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {j₁ j₂ : Fin m} {u : Fin U} {v₁ v₂ : ℕ}
    (h₁ : T j₁ = some (u, v₁)) (h₂ : T j₂ = some (u, v₂)) : j₁ = j₂ := by
  obtain ⟨-, hlt₁, rfl⟩ := hrep.slot_spec j₁ u v₁ h₁
  obtain ⟨-, _, rfl⟩ := hrep.slot_spec j₂ u v₂ h₂
  rfl

/-- Under `TableRep π s T`, the number of occupied slots in `T` equals `(Dictionary.dom s).card`. -/
theorem TableRep.card_occupiedSlots {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) :
    (occupiedSlots T).card = (Dictionary.dom s).card := by
  refine Finset.card_bij
    (fun j hj => ((T j).get (by simpa [occupiedSlots] using hj)).1) ?_ ?_ ?_
  · intro j hj
    have his : (T j).isSome := by simpa [occupiedSlots] using hj
    obtain ⟨⟨u, v⟩, hTj⟩ := Option.isSome_iff_exists.mp his
    have hsu := (hrep.slot_spec j u v hTj).1
    simp [Dictionary.dom, hTj, hsu]
  · intro j₁ hj₁ j₂ hj₂ heq
    obtain ⟨⟨u₁, v₁⟩, h₁⟩ := Option.isSome_iff_exists.mp (by simpa [occupiedSlots] using hj₁)
    obtain ⟨⟨u₂, v₂⟩, h₂⟩ := Option.isSome_iff_exists.mp (by simpa [occupiedSlots] using hj₂)
    have hu : u₁ = u₂ := by simpa [h₁, h₂] using heq
    subst hu
    exact hrep.slot_eq_of_same_key h₁ h₂
  · intro u hu
    obtain ⟨v, hsu⟩ := Dictionary.mem_dom_iff.mp hu
    obtain ⟨hlt, hTj⟩ := hrep.key_spec u v hsu
    refine ⟨π u ⟨missedProbes (otherOccupiedSlots T u) (π u), hlt⟩, ?_, ?_⟩
    · simp [occupiedSlots, hTj]
    · simp [hTj]

/-- Under `TableRep π s T`, `(otherOccupiedSlots T u).card = ((Dictionary.dom s).erase u).card`. -/
theorem TableRep.card_otherOccupiedSlots {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) :
    (otherOccupiedSlots T u).card = ((Dictionary.dom s).erase u).card := by
  refine Finset.card_bij
    (fun j hj => ((T j).get (by
      exact (Finset.mem_filter.mp hj).2.1)).1) ?_ ?_ ?_
  · intro j hj
    rcases mem_otherOccupiedSlots_iff.mp hj with ⟨u', v', hTj, hne⟩
    have hsu' := (hrep.slot_spec j u' v' hTj).1
    simp [Dictionary.dom, hTj, hsu', hne]
  · intro j₁ hj₁ j₂ hj₂ heq
    rcases mem_otherOccupiedSlots_iff.mp hj₁ with ⟨u₁, v₁, h₁, -⟩
    rcases mem_otherOccupiedSlots_iff.mp hj₂ with ⟨u₂, v₂, h₂, -⟩
    have hu : u₁ = u₂ := by simpa [h₁, h₂] using heq
    subst hu
    exact hrep.slot_eq_of_same_key h₁ h₂
  · intro u' hu'
    rcases Finset.mem_erase.mp hu' with ⟨hne, hu'_dom⟩
    obtain ⟨v', hsu'⟩ := Dictionary.mem_dom_iff.mp hu'_dom
    obtain ⟨hlt, hTj⟩ := hrep.key_spec u' v' hsu'
    refine ⟨π u' ⟨missedProbes (otherOccupiedSlots T u') (π u'), hlt⟩, ?_, ?_⟩
    · exact mem_otherOccupiedSlots_iff.mpr ⟨u', v', hTj, hne⟩
    · simp [hTj]

/-- Under `TableRep π s T`, `(otherOccupiedSlots T u).card ≤ (Dictionary.dom s).card`. -/
theorem TableRep.card_otherOccupiedSlots_le {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) :
    (otherOccupiedSlots T u).card ≤ (Dictionary.dom s).card := by
  rw [hrep.card_otherOccupiedSlots u]
  exact Finset.card_erase_le

/-- When `s u = none`, no slot in `T` holds key `u`, so `otherOccupiedSlots T u = occupiedSlots T`.
-/
theorem TableRep.otherOccupiedSlots_eq_occupiedSlots_of_eq_none {U m : ℕ}
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {u : Fin U} (hu : s u = none) :
    otherOccupiedSlots T u = occupiedSlots T := by
  ext j
  refine ⟨fun hj => otherOccupiedSlots_subset_occupiedSlots T u hj, fun hj => ?_⟩
  simp only [occupiedSlots, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨⟨u', v'⟩, hTj⟩ := Option.isSome_iff_exists.mp hj
  have hsu' := (hrep.slot_spec j u' v' hTj).1
  have hne : u' ≠ u := by
    rintro rfl
    rw [hu] at hsu'
    cases hsu'
  exact mem_otherOccupiedSlots_iff.mpr ⟨u', v', hTj, hne⟩

/-- When `TableRep π s T` and `(Dictionary.dom s).card < m`, the stopping index for any key `u`
satisfies `missedProbes (otherOccupiedSlots T u) (π u) < m`. -/
theorem TableRep.missedProbes_lt {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (hcard : (Dictionary.dom s).card < m) (u : Fin U) :
    missedProbes (otherOccupiedSlots T u) (π u) < m :=
  missedProbes_lt_of_card_lt (lt_of_le_of_lt (hrep.card_otherOccupiedSlots_le u) hcard) (π u)

/-- Target slot `π u ⟨missedProbes (otherOccupiedSlots T u) (π u), _⟩` where key `u` is found or
inserted when `(otherOccupiedSlots T u).card < m`. -/
def targetSlot {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < m) : Fin m :=
  π u (probeSlotIndex (otherOccupiedSlots T u) (π u) hO)

/-- Under `TableRep π s T` and `hO : (otherOccupiedSlots T u).card < m`, `T (targetSlot π T u hO)`
equals `(s u).map (fun v => (u, v))`. -/
theorem TableRep.apply_targetSlot {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < m) :
    T (targetSlot π T u hO) = (s u).map (fun v => (u, v)) := by
  cases hsu : s u with
  | none =>
    simp only [Option.map_none]
    have hnot : targetSlot π T u hO ∉ otherOccupiedSlots T u :=
      notMem_apply_probeSlotIndex hO
    cases hTj : T (targetSlot π T u hO) with
    | none => rfl
    | some p =>
      rcases p with ⟨u', v'⟩
      by_cases hne : u' = u
      · subst hne
        have hsu' := (hrep.slot_spec _ u' v' hTj).1
        rw [hsu] at hsu'
        cases hsu'
      · exact False.elim (hnot (mem_otherOccupiedSlots_iff.mpr ⟨u', v', hTj, hne⟩))
  | some v =>
    simp only [Option.map_some]
    obtain ⟨_, hTj⟩ := hrep.key_spec u v hsu
    exact hTj

/-- Pure open-addressed lookup `tableGet hm π T u` when `0 < m`: inspects slot
`π u ⟨min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1), _⟩` and returns `some v` if it
contains `(u, v)`, else `none`. -/
def tableGet {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m)
    (u : Fin U) : Option ℕ :=
  let idx := min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1)
  match T (π u ⟨idx, by omega⟩) with
  | some (u', v) => if u' = u then some v else none
  | none => none

/-- Pure open-addressed insertion `tableInsert hm π T u v`: writes `some (u, v)` at slot
`π u ⟨min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1), _⟩`. -/
def tableInsert {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m)
    (u : Fin U) (v : ℕ) : Table U m :=
  let idx := min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1)
  Function.update T (π u ⟨idx, by omega⟩) (some (u, v))

theorem tableInsert_eq_update_targetSlot {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (T : Table U m) (u : Fin U) (v : ℕ) (hO : (otherOccupiedSlots T u).card < m) :
    tableInsert hm π T u v = Function.update T (targetSlot π T u hO) (some (u, v)) := by
  have hlt : missedProbes (otherOccupiedSlots T u) (π u) < m :=
    missedProbes_lt_of_card_lt hO (π u)
  have hmin : min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1) =
      missedProbes (otherOccupiedSlots T u) (π u) := Nat.min_eq_left (by omega)
  have hslot : (⟨min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1), by omega⟩ : Fin m) =
      probeSlotIndex (otherOccupiedSlots T u) (π u) hO := Fin.ext hmin
  dsimp only [tableInsert, targetSlot]
  rw [hslot]

/-- Under `TableRep π s T` and `(otherOccupiedSlots T u).card < m`, `tableGet hm π T u = s u`. -/
theorem TableRep.tableGet_eq {U m : ℕ} (hm : 0 < m) {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U)
    (hO : (otherOccupiedSlots T u).card < m) :
    tableGet hm π T u = s u := by
  have hlt : missedProbes (otherOccupiedSlots T u) (π u) < m :=
    missedProbes_lt_of_card_lt hO (π u)
  have hmin : min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1) =
      missedProbes (otherOccupiedSlots T u) (π u) := Nat.min_eq_left (by omega)
  dsimp only [tableGet]
  have hslot : (⟨min (missedProbes (otherOccupiedSlots T u) (π u)) (m - 1), by omega⟩ : Fin m) =
      probeSlotIndex (otherOccupiedSlots T u) (π u) hO := Fin.ext hmin
  rw [hslot]
  have htarget := hrep.apply_targetSlot u hO
  dsimp only [targetSlot] at htarget
  rw [htarget]
  cases s u <;> simp

/-- Inserting `(u, v)` leaves `otherOccupiedSlots` for `u` itself unchanged. -/
theorem otherOccupiedSlots_tableInsert_self {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (_hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    otherOccupiedSlots (tableInsert hm π T u v) u = otherOccupiedSlots T u := by
  rw [tableInsert_eq_update_targetSlot hm π T u v hO]
  ext j
  by_cases hj : j = targetSlot π T u hO
  · subst hj
    have hnot : targetSlot π T u hO ∉ otherOccupiedSlots T u :=
      notMem_apply_probeSlotIndex hO
    simp [mem_otherOccupiedSlots_iff, hnot]
  · simp [mem_otherOccupiedSlots_iff, Function.update_of_ne hj]

/-- Inserting `(u, v)` preserves the stopping index `missedProbes (otherOccupiedSlots · w) (π w)`
for every key `w` already present in `s` (`(s w).isSome`). -/
theorem TableRep.missedProbes_tableInsert_of_isSome {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m)
    {w : Fin U} (hw : (s w).isSome) :
    missedProbes (otherOccupiedSlots (tableInsert hm π T u v) w) (π w) =
      missedProbes (otherOccupiedSlots T w) (π w) := by
  by_cases hwu : w = u
  · subst hwu
    rw [otherOccupiedSlots_tableInsert_self hm hrep w v hO]
  · obtain ⟨vw, hsw⟩ := Option.isSome_iff_exists.mp hw
    obtain ⟨hlt_w, hTw⟩ := hrep.key_spec w vw hsw
    set iw : Fin m := ⟨missedProbes (otherOccupiedSlots T w) (π w), hlt_w⟩
    have hiw_spec := (missedProbes_eq_iff (O := otherOccupiedSlots T w) (σ := π w) iw).mp rfl
    have htarget_u := hrep.apply_targetSlot u hO
    have hne_slot : π w iw ≠ targetSlot π T u hO := by
      intro heq
      rw [← heq, hTw] at htarget_u
      cases hsu : s u with
      | none => simp [hsu] at htarget_u
      | some vu =>
        simp only [hsu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at htarget_u
        exact hwu htarget_u.1
    rw [tableInsert_eq_update_targetSlot hm π T u v hO]
    apply (missedProbes_eq_iff iw).mpr
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi_mem : π w i ∈ otherOccupiedSlots T w := hiw_spec.1 i hi
      rcases mem_otherOccupiedSlots_iff.mp hi_mem with ⟨u', v', hTi, hne'⟩
      rw [mem_otherOccupiedSlots_iff]
      by_cases h_eq : π w i = targetSlot π T u hO
      · refine ⟨u, v, ?_, Ne.symm hwu⟩
        simp [h_eq]
      · refine ⟨u', v', ?_, hne'⟩
        simp [Function.update_of_ne h_eq, hTi]
    · rw [mem_otherOccupiedSlots_iff]
      rintro ⟨u', v', hTiw, hne'⟩
      simp only [Function.update_of_ne hne_slot] at hTiw
      rw [hTw] at hTiw
      injection hTiw with hpair
      injection hpair with hu' _
      exact hne' hu'.symm

/-- **Preservation of `TableRep` under `tableInsert`**: if `TableRep π s T` and
`(otherOccupiedSlots T u).card < m`, then `tableInsert hm π T u v` satisfies
`TableRep π (Function.update s u (some v))`. -/
theorem TableRep.tableInsert {U m : ℕ} (hm : 0 < m) {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    TableRep π (Function.update s u (some v)) (tableInsert hm π T u v) := by
  have hlt_u : missedProbes (otherOccupiedSlots T u) (π u) < m :=
    missedProbes_lt_of_card_lt hO (π u)
  have hself_mp :
      missedProbes (otherOccupiedSlots (UniformProbing.tableInsert hm π T u v) u) (π u) =
        missedProbes (otherOccupiedSlots T u) (π u) := by
    rw [otherOccupiedSlots_tableInsert_self hm hrep u v hO]
  have hupd := tableInsert_eq_update_targetSlot hm π T u v hO
  refine ⟨?_, ?_⟩
  · intro j w vw hj
    by_cases hju : j = targetSlot π T u hO
    · subst hju
      rw [hupd] at hj
      simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq] at hj
      rcases hj with ⟨rfl, rfl⟩
      refine ⟨by simp, ⟨by omega, ?_⟩⟩
      ext
      simp [targetSlot, probeSlotIndex, hself_mp]
    · rw [hupd, Function.update_of_ne hju] at hj
      obtain ⟨hsw, hlt_w, hj_eq⟩ := hrep.slot_spec j w vw hj
      have hwu : w ≠ u := by
        rintro rfl
        have ⟨_, hTu⟩ := hrep.key_spec w vw hsw
        have h_same := hrep.slot_eq_of_same_key hj hTu
        exact hju h_same
      have hw_mp := hrep.missedProbes_tableInsert_of_isSome hm u v hO (by rw [hsw]; rfl)
      refine ⟨by simp [Function.update_of_ne hwu, hsw], ⟨by omega, ?_⟩⟩
      ext
      simpa [hw_mp] using congrArg Fin.val hj_eq
  · intro w vw hsw'
    by_cases hwu : w = u
    · subst hwu
      simp only [Function.update_self, Option.some.injEq] at hsw'
      subst hsw'
      refine ⟨by omega, ?_⟩
      have hidx_eq :
          (⟨missedProbes (otherOccupiedSlots (UniformProbing.tableInsert hm π T w v) w) (π w),
            by omega⟩ : Fin m) = probeSlotIndex (otherOccupiedSlots T w) (π w) hO := by
        ext
        simp [probeSlotIndex, hself_mp]
      rw [hidx_eq, hupd]
      simp [targetSlot]
    · simp only [Function.update_of_ne hwu] at hsw'
      obtain ⟨hlt_w, hTw⟩ := hrep.key_spec w vw hsw'
      have hw_mp := hrep.missedProbes_tableInsert_of_isSome hm u v hO (by rw [hsw']; rfl)
      refine ⟨by omega, ?_⟩
      have hidx_eq :
          (⟨missedProbes (otherOccupiedSlots (UniformProbing.tableInsert hm π T u v) w) (π w),
            by omega⟩ : Fin m) = ⟨missedProbes (otherOccupiedSlots T w) (π w), hlt_w⟩ := by
        ext
        exact hw_mp
      rw [hidx_eq, hupd]
      have hne_slot :
          π w ⟨missedProbes (otherOccupiedSlots T w) (π w), hlt_w⟩ ≠ targetSlot π T u hO := by
        intro heq
        have htarget_u := hrep.apply_targetSlot u hO
        rw [← heq, hTw] at htarget_u
        cases hsu : s u with
        | none => simp [hsu] at htarget_u
        | some vu =>
          simp only [hsu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at htarget_u
          exact hwu htarget_u.1
      simp [Function.update_of_ne hne_slot, hTw]

/-- Inserting `(u, v)` leaves `probeCount · u (π u)` unchanged. -/
theorem TableRep.probeCount_tableInsert_self {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    probeCount (UniformProbing.tableInsert hm π T u v) u (π u) = probeCount T u (π u) := by
  simp [probeCount, unsuccessfulProbes, otherOccupiedSlots_tableInsert_self hm hrep u v hO]

/-- **Probe invariance for present keys ([CLRS2009], Section 11.4, p. 275)**:
once a key `w` is present in `s` (`(s w).isSome`), inserting or updating any key `(u, v)` leaves
the number of probes `probeCount · w (π w)` made when searching for `w` unchanged. -/
theorem TableRep.probeCount_tableInsert_of_isSome {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m)
    {w : Fin U} (hw : (s w).isSome) :
    probeCount (UniformProbing.tableInsert hm π T u v) w (π w) = probeCount T w (π w) := by
  simp [probeCount, unsuccessfulProbes, hrep.missedProbes_tableInsert_of_isSome hm u v hO hw]

/-- Execute a single `Dictionary.Op U` on open-addressed table `T`. -/
def tableStep {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) (T : Table U m)
    (o : Dictionary.Op U) : Table U m × (Dictionary.spec U 0 0).Result o :=
  match o with
  | .get u => (T, tableGet hm π T u)
  | .insert u v => (tableInsert hm π T u v, ())

/-- Execute a sequence of `Dictionary.Op U` operations on `T` under permutation family `π`. -/
def runTableFrom {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m)) :
    Table U m → List (Dictionary.Op U) → Table U m
  | T, [] => T
  | T, o :: os => runTableFrom hm π (tableStep hm π T o).1 os

/-- Table produced by running `ops` starting from `emptyTable U m`. -/
def runTable {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (ops : List (Dictionary.Op U)) : Table U m :=
  runTableFrom hm π (emptyTable U m) ops

/-- Under any admissible operation `(Dictionary.spec U V n_max).valid s o` with `n_max ≤ m` and
`TableRep π s T`, `(otherOccupiedSlots T u).card < m` holds for the operated key `u`. -/
theorem TableRep.card_otherOccupiedSlots_lt_of_valid {U V n_max m : ℕ} (_hm : 0 < m)
    (hcap : n_max ≤ m) {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {u : Fin U} {v : ℕ} (hval : (Dictionary.spec U V n_max).valid s (.insert u v)) :
    (otherOccupiedSlots T u).card < m := by
  rcases hval.1 with hlt | hisSome
  · have hle := hrep.card_otherOccupiedSlots_le u
    omega
  · rw [hrep.card_otherOccupiedSlots u]
    have hmem : u ∈ Dictionary.dom s := Dictionary.mem_dom_iff_isSome.mpr hisSome
    have herase := Finset.card_erase_lt_of_mem hmem
    omega

/-- Any valid operation history preserves `TableRep`. -/
theorem tableRep_runTableFrom {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {ops : List (Dictionary.Op U)} (hvh : (Dictionary.spec U V n_max).ValidHistory s ops) :
    TableRep π ((Dictionary.spec U V n_max).run s ops).1 (runTableFrom hm π T ops) := by
  induction ops generalizing s T with
  | nil => exact hrep
  | cons o os ih =>
    have hs' : (Dictionary.dom ((Dictionary.spec U V n_max).step s o).1).card ≤ n_max :=
      Dictionary.card_dom_step_le_of_valid hs hvh.1
    cases o with
    | get u =>
      exact ih hrep hs' hvh.2
    | insert u v =>
      have hO : (otherOccupiedSlots T u).card < m :=
        hrep.card_otherOccupiedSlots_lt_of_valid hm hcap hs hvh.1
      exact ih (hrep.tableInsert hm u v hO) hs' hvh.2

/-- Running any valid operation history from `emptyTable U m` produces a table satisfying
`TableRep`. -/
theorem tableRep_runTable {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    TableRep π ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1
      (runTable hm π ops) :=
  tableRep_runTableFrom hm hcap π (tableRep_empty π) (by simp) hvh

/-- If key `w` is already present in `s`, then running any valid continuation `ops` from `(s, T)`
preserves `probeCount · w (π w)`. -/
theorem probeCount_runTableFrom_of_isSome {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {w : Fin U} (hw : (s w).isSome)
    {ops : List (Dictionary.Op U)} (hvh : (Dictionary.spec U V n_max).ValidHistory s ops) :
    probeCount (runTableFrom hm π T ops) w (π w) = probeCount T w (π w) := by
  induction ops generalizing s T with
  | nil => rfl
  | cons o os ih =>
    have hs' : (Dictionary.dom ((Dictionary.spec U V n_max).step s o).1).card ≤ n_max :=
      Dictionary.card_dom_step_le_of_valid hs hvh.1
    cases o with
    | get u =>
      exact ih hrep hs' hw hvh.2
    | insert u v =>
      have hO : (otherOccupiedSlots T u).card < m :=
        hrep.card_otherOccupiedSlots_lt_of_valid hm hcap hs hvh.1
      have hw' : ((Function.update s u (some v)) w).isSome := by
        by_cases hwu : w = u
        · subst hwu; simp
        · simpa [Function.update_of_ne hwu] using hw
      rw [runTableFrom, tableStep, ih (hrep.tableInsert hm u v hO) hs' hw' hvh.2]
      exact hrep.probeCount_tableInsert_of_isSome hm u v hO hw

/-- Prefix + suffix decomposition for `ValidHistory` and `runTableFrom`. -/
theorem validHistory_and_runTableFrom_append {U V n_max m : ℕ} (hm : 0 < m)
    (π : Fin U → Equiv.Perm (Fin m)) :
    ∀ {l₁ l₂ : List (Dictionary.Op U)} {s : Dictionary.State U} (T : Table U m),
      (Dictionary.spec U V n_max).ValidHistory s (l₁ ++ l₂) →
      (Dictionary.spec U V n_max).ValidHistory s l₁ ∧
      (Dictionary.spec U V n_max).ValidHistory ((Dictionary.spec U V n_max).run s l₁).1 l₂ ∧
      runTableFrom hm π T (l₁ ++ l₂) = runTableFrom hm π (runTableFrom hm π T l₁) l₂
  | [], _, _, _, h => ⟨trivial, h, rfl⟩
  | o :: l₁, l₂, s, T, h => by
    obtain ⟨h₁, h₂, hrun⟩ :=
      validHistory_and_runTableFrom_append hm π
        (s := ((Dictionary.spec U V n_max).step s o).1) (tableStep hm π T o).1 h.2
    exact ⟨⟨h.1, h₁⟩, h₂, hrun⟩

/-- **Pathwise insertion-cost identity from the proof of Theorem 11.8 of [CLRS2009], third edition,
p. 276 (`probeCount_runTable_eq_firstInsert`)**:
if `ops = ops₁ ++ (.insert u v₀ :: ops₂)` is a valid operation history where `ops₁` is the prefix
before `u` is inserted (`((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1 u = none`),
then the number of probes made when searching for `u` after the entire history `ops` equals the
number of probes made when `u` was first inserted after `ops₁`. -/
theorem probeCount_runTable_eq_firstInsert {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m))
    {ops₁ ops₂ : List (Dictionary.Op U)} {u : Fin U} {v₀ : ℕ}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops₁ ++ (.insert u v₀ :: ops₂))) :
    probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) =
      probeCount (runTable hm π ops₁) u (π u) := by
  obtain ⟨hvh₁, hvh_rest, hrun_eq⟩ :=
    validHistory_and_runTableFrom_append hm π (emptyTable U m) hvh
  set s₁ : Dictionary.State U := ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1
  set T₁ := runTable hm π ops₁
  have hrep₁ : TableRep π s₁ T₁ := tableRep_runTable hm hcap π hvh₁
  have hs₁ : (Dictionary.dom s₁).card ≤ n_max := Dictionary.card_dom_run_empty_le hvh₁
  have hO₁ : (otherOccupiedSlots T₁ u).card < m :=
    hrep₁.card_otherOccupiedSlots_lt_of_valid hm hcap hs₁ hvh_rest.1
  have hrep_ins : TableRep π (Function.update s₁ u (some v₀)) (tableInsert hm π T₁ u v₀) :=
    hrep₁.tableInsert hm u v₀ hO₁
  have hs_ins : (Dictionary.dom (Function.update s₁ u (some v₀))).card ≤ n_max :=
    Dictionary.card_dom_step_le_of_valid hs₁ hvh_rest.1
  change probeCount (runTableFrom hm π (emptyTable U m) (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) =
    probeCount T₁ u (π u)
  rw [hrun_eq]
  change probeCount (runTableFrom hm π (tableInsert hm π T₁ u v₀) ops₂) u (π u) =
    probeCount T₁ u (π u)
  rw [probeCount_runTableFrom_of_isSome hm hcap π hrep_ins hs_ins
    (by rw [Function.update_self]; rfl) hvh_rest.2]
  exact hrep₁.probeCount_tableInsert_self hm u v₀ hO₁

/-- If key `u` is never inserted during `ops` (`∀ v, .insert u v ∉ ops`), then `runTableFrom` is
independent of `π u`: updating `π` at `u` leaves the resulting table unchanged. -/
theorem runTableFrom_update_eq {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (u : Fin U) (σ : Equiv.Perm (Fin m)) (T : Table U m) :
    ∀ {ops : List (Dictionary.Op U)},
      (∀ v, Dictionary.Op.insert u v ∉ ops) →
      runTableFrom hm (Function.update π u σ) T ops = runTableFrom hm π T ops
  | [], _ => rfl
  | .get _ :: _, hno => by
    dsimp only [runTableFrom, tableStep]
    exact runTableFrom_update_eq hm π u σ T fun v hv => hno v (List.mem_cons_of_mem _ hv)
  | .insert w v :: _, hno => by
    have hwu : w ≠ u := by
      rintro rfl
      exact hno v List.mem_cons_self
    have hins : tableInsert hm (Function.update π u σ) T w v = tableInsert hm π T w v := by
      simp [tableInsert, Function.update_of_ne hwu]
    dsimp only [runTableFrom, tableStep]
    rw [hins]
    exact runTableFrom_update_eq hm π u σ (tableInsert hm π T w v)
      fun v' hv' => hno v' (List.mem_cons_of_mem _ hv')

/-- Once `(s₀ u).isSome`, running any list of operations `l` preserves `isSome` at `u`. -/
private theorem isSome_run_of_isSome {U V n_max : ℕ} {u : Fin U} :
    ∀ (l : List (Dictionary.Op U)) {s₀ : Dictionary.State U},
      (s₀ u).isSome → (((Dictionary.spec U V n_max).run s₀ l).1 u).isSome
  | [], _, h => h
  | .get _ :: l, _, h => isSome_run_of_isSome l h
  | .insert w _ :: l, s₀, h => by
    apply isSome_run_of_isSome l (s₀ := ((Dictionary.spec U V n_max).step s₀ (.insert w _)).1)
    dsimp only [Dictionary.spec]
    by_cases hwu : u = w
    · subst hwu; simp
    · simpa [Function.update_of_ne hwu] using h

/-- If `((Dictionary.spec U V n_max).run s ops).1 u = none`, then no `.insert u v` appears in `ops`.
-/
theorem not_mem_insert_of_run_eq_none {U V n_max : ℕ} {u : Fin U} :
    ∀ {ops : List (Dictionary.Op U)} {s : Dictionary.State U},
      ((Dictionary.spec U V n_max).run s ops).1 u = none →
      ∀ v, Dictionary.Op.insert u v ∉ ops
  | [], _, _, _ => by simp
  | o :: os, s, hnone, v => by
    intro hmem
    rcases List.mem_cons.mp hmem with rfl | htail
    · have his :
          (((Dictionary.spec U V n_max).run
            (((Dictionary.spec U V n_max).step s (.insert u v)).1) os).1 u).isSome :=
        isSome_run_of_isSome (V := V) (n_max := n_max) os
          (by dsimp [Dictionary.spec]; rw [Function.update_self]; rfl)
      have hnone' :
          (((Dictionary.spec U V n_max).run
            (((Dictionary.spec U V n_max).step s (.insert u v)).1) os).1 u) = none := hnone
      rw [hnone'] at his
      cases his
    · exact not_mem_insert_of_run_eq_none
        (s := ((Dictionary.spec U V n_max).step s o).1) hnone v htail

/-- **Theorem 11.6 (pp. 274–275) & Corollary 11.7 (p. 276) of [CLRS2009], third edition, over
`PMF.uniformOfFintype`**:
for any valid operation history `ops` reaching state `s` with `(Dictionary.dom s).card < m` and any
absent key `u` (`s u = none`), the expected number of probes made by an unsuccessful lookup `get u`
or fresh-key insertion `insert u v` on `runTable hm π ops` over
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))` is at most
`m / (m - (Dictionary.dom s).card)` (`≤ 2` when `2 * (Dictionary.dom s).card ≤ m`). -/
theorem expect_probeCount_of_eq_none_le {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops)
    {u : Fin U} (hu : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 u = none)
    (hcard :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1).card < m) :
    let s := ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞)) ≤
      (m : ℝ≥0∞) / ((m - (Dictionary.dom s).card : ℕ) : ℝ≥0∞) := by
  intro s
  have hcard_s : (Dictionary.dom s).card < m := hcard
  have : Nonempty (Equiv.Perm (Fin m)) := ⟨1⟩
  let μ_all := PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))
  let μ_one := PMF.uniformOfFintype (Equiv.Perm (Fin m))
  have hno : ∀ v, Dictionary.Op.insert u v ∉ ops := not_mem_insert_of_run_eq_none hu
  have hupd : μ_all = μ_one.bind (fun σ => μ_all.map (fun π => Function.update π u σ)) :=
    (PMF.uniformOfFintype_update (ι := Fin U) (γ := Equiv.Perm (Fin m)) u).symm
  calc
    (∑' π, μ_all π * (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞))
      = ∑' π, (μ_one.bind (fun σ => μ_all.map (fun π₀ => Function.update π₀ u σ))) π *
          (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞) := by
          rw [← hupd]
    _ = ∑' σ, μ_one σ * ∑' π₀, μ_all π₀ *
          (probeCount (runTable hm (Function.update π₀ u σ) ops) u
            ((Function.update π₀ u σ) u) : ℝ≥0∞) := by
          rw [PMF.tsum_bind_mul]
          refine tsum_congr fun σ => congrArg (μ_one σ * ·) ?_
          exact PMF.tsum_map_mul μ_all (fun π₀ => Function.update π₀ u σ)
            (fun π => (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞))
    _ = ∑' π₀, μ_all π₀ * ∑' σ, μ_one σ *
          (unsuccessfulProbes (occupiedSlots (runTable hm π₀ ops)) σ : ℝ≥0∞) := by
          simp_rw [← ENNReal.tsum_mul_left]
          rw [tsum_comm]
          refine tsum_congr fun π₀ => tsum_congr fun σ => ?_
          have hrep : TableRep π₀ s (runTable hm π₀ ops) := tableRep_runTable hm hcap π₀ hvh
          have htbl : runTable hm (Function.update π₀ u σ) ops = runTable hm π₀ ops :=
            runTableFrom_update_eq hm π₀ u σ (emptyTable U m) hno
          rw [htbl, Function.update_self, probeCount,
            hrep.otherOccupiedSlots_eq_occupiedSlots_of_eq_none hu]
          ring
    _ ≤ ∑' π₀, μ_all π₀ * ((m : ℝ≥0∞) / ((m - (Dictionary.dom s).card : ℕ) : ℝ≥0∞)) := by
          refine tsum_le_tsum fun π₀ => ?_
          gcongr
          have hrep : TableRep π₀ s (runTable hm π₀ ops) := tableRep_runTable hm hcap π₀ hvh
          have hcard_occ : (occupiedSlots (runTable hm π₀ ops)).card = (Dictionary.dom s).card :=
            hrep.card_occupiedSlots
          rw [← hcard_occ]
          exact expect_unsuccessfulProbes_le (by omega)
    _ = (m : ℝ≥0∞) / ((m - (Dictionary.dom s).card : ℕ) : ℝ≥0∞) := by
          rw [ENNReal.tsum_mul_right, μ_all.tsum_coe, one_mul]

/-- **Half-load corollary of Theorem 11.6 & Corollary 11.7 ([CLRS2009], third edition, Section 11.4,
pp. 274–276)**:
when `2 * n_max ≤ m`, any unsuccessful lookup or fresh-key insertion after a valid history `ops`
makes at most `2` probes in expectation over
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))`. -/
theorem expect_probeCount_of_eq_none_le_two {U V n_max m : ℕ} (hm : 0 < m) (h2cap : 2 * n_max ≤ m)
    {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops)
    {u : Fin U} (hu : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 u = none) :
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π ops) u (π u) : ℝ≥0∞)) ≤ 2 := by
  have hdom_le :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1).card ≤ n_max :=
    Dictionary.card_dom_run_empty_le hvh
  refine (expect_probeCount_of_eq_none_le hm (by omega) hvh hu (by omega)).trans ?_
  exact div_sub_le_two hm (by omega)

/-- **Per-key successful-search bound from the proof of Theorem 11.8 of [CLRS2009], third edition,
p. 276**:
if `ops = ops₁ ++ (.insert u v₀ :: ops₂)` is a valid operation history where `ops₁` is the prefix
before `u` is first inserted (`s₁ u = none`), then the expected number of probes made when
searching for the fixed key `u` after `ops` equals the expected number of probes when `u` was first
inserted after `ops₁`, and is at most `m / (m - (Dictionary.dom s₁).card)` (this formalizes the
per-key intermediate bound `1 / (1 - i / m) = m / (m - i)` for `i = (Dictionary.dom s₁).card` from
the proof of Theorem 11.8; the uniform-key-averaged `(1 / α) ln(1 / (1 - α))` endpoint of Theorem
11.8 is not formalized here). -/
theorem expect_probeCount_of_mem_dom_le {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    {ops₁ ops₂ : List (Dictionary.Op U)} {u : Fin U} {v₀ : ℕ}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops₁ ++ (.insert u v₀ :: ops₂)))
    (hu₁ : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1 u = none)
    (hcard₁ :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1).card < m) :
    let s₁ := ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) : ℝ≥0∞)) ≤
      (m : ℝ≥0∞) / ((m - (Dictionary.dom s₁).card : ℕ) : ℝ≥0∞) := by
  intro s₁
  have hvh₁ : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops₁ :=
    (validHistory_and_runTableFrom_append hm (fun _ => 1) (emptyTable U m) hvh).1
  have hcongr : ∀ π : Fin U → Equiv.Perm (Fin m),
      probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) =
        probeCount (runTable hm π ops₁) u (π u) :=
    fun π => probeCount_runTable_eq_firstInsert hm hcap π hvh
  simp_rw [hcongr]
  exact expect_probeCount_of_eq_none_le hm hcap hvh₁ hu₁ hcard₁

/-- **Half-load per-key successful-search bound from the proof of Theorem 11.8 ([CLRS2009], third
edition, Section 11.4, p. 276)**:
when `2 * n_max ≤ m`, any successful lookup of a fixed present key `u` (first inserted after prefix
`ops₁`) makes at most `2` probes in expectation over
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))`. -/
theorem expect_probeCount_of_mem_dom_le_two {U V n_max m : ℕ} (hm : 0 < m) (h2cap : 2 * n_max ≤ m)
    {ops₁ ops₂ : List (Dictionary.Op U)} {u : Fin U} {v₀ : ℕ}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U)
      (ops₁ ++ (.insert u v₀ :: ops₂)))
    (hu₁ : ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1 u = none) :
    (∑' π : Fin U → Equiv.Perm (Fin m),
      PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m)) π *
        (probeCount (runTable hm π (ops₁ ++ (.insert u v₀ :: ops₂))) u (π u) : ℝ≥0∞)) ≤ 2 := by
  have hvh₁ : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops₁ :=
    (validHistory_and_runTableFrom_append hm (fun _ => 1) (emptyTable U m) hvh).1
  have hdom₁_le :
      (Dictionary.dom ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops₁).1).card ≤ n_max :=
    Dictionary.card_dom_run_empty_le hvh₁
  refine (expect_probeCount_of_mem_dom_le hm (by omega) hvh hu₁ (by omega)).trans ?_
  exact div_sub_le_two hm (by omega)

/-! ## Section 4: Lazy Random-Oracle Equivalence (`RandomOracle.uniform_interpret_eq_lazy`) -/

/-- Any adaptive oracle program querying per-key permutations `u ↦ π u : Equiv.Perm (Fin m)` has the
exact same output distribution whether the permutation table
`π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))` is sampled eagerly upfront or lazily on
first query via `Cslib.RandomOracle.answer`. -/
theorem uniform_interpret_eq_lazy_perm {U m : ℕ} {α : Type}
    (program : OracleComp (fun _ : Fin U => Equiv.Perm (Fin m)) α) :
    (do
      let π ← PMF.uniformOfFintype (Fin U → Equiv.Perm (Fin m))
      OracleComp.interpret (fun u => PMF.pure (π u)) program) =
        ((OracleComp.interpret
          (Cslib.RandomOracle.answer (fun _ : Fin U => PMF.uniformOfFintype (Equiv.Perm (Fin m))))
          program).run (fun _ => none)).map Prod.fst :=
  Cslib.RandomOracle.uniform_interpret_eq_lazy program

end Cslib.Algorithms.Lean.UniformProbing
