/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.UniformProbing
public import Complexity.Foundations.Data.Nat.OddMulMod
public import Complexity.Probability.KWiseIndependent.DoubleTabulation
import Complexity.Foundations.Data.Nat.Power
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

/-!
# Odd-Stride Double Hashing under Limited Independence and Double Tabulation

This module proves $O(1)$ expected probes for power-of-two odd-stride double hashing
`oddStridePerm h₁ h₂ u i = (h₁(u) + i * (2 * h₂(u) + 1)) mod 2 ^ M` ([CLRS2009], Section 11.4,
pp. 272–274) over open-addressed tables `Cslib.Algorithms.Lean.UniformProbing.Table U (2 ^ M)`
with key universe size `U`, table bit-width `M` (`m = 2 ^ M` slots), and maximum stored key count
`n_max`. The bound holds both under $(2 L + 1)$-wise independence for probe cutoff
`L = maxProbeCutoff n_max = Nat.clog 2 (max n_max 4) + 4` and under Mikkel Thorup's Double
Tabulation (`[Thorup2013]`, Theorem 1(a) and Lemma 2) with `c` characters of `b` bits
(`U ≤ 2 ^ (c * b)`) or polynomial universe exponent `c_exp` (`U ≤ max n_max 4 ^ c_exp`).

## Source statements and notation mapping

* **J. P. Schmidt and A. Siegel ([SchmidtSiegel1990], STOC 1990, pp. 224–234; extended NYU Courant
  Technical Report `TR1995-687`, May 1995, pp. 1–2, 4–7, 37–39)**:
  - **Definition 1 (`TR1995-687`, p. 2)**: Sequential closed-hashing insertion of a key set $D$
    into a table of size $n$ (`[0..n - 1]`) over universe $[0..m - 1]$ along $1$-indexed per-key
    probe sequences $p(x, 1), p(x, 2), \dots$ and affine double hashing. Here we map table size to
    $m = 2^M$ (`Fin (2 ^ M)`), universe to `Fin U`, and probe sequences to $0$-indexed permutations
    `π u i`.
  - **Definition 2 (`Models UH, DH, and DH_ψ`, `TR1995-687`, pp. 4–5)**: Formulates two-probe slot
    uniformity (Condition 1, p. 4) and $\psi$-wise cross-key probe independence for
    $\psi = c \log n$ (Condition 2, p. 5).
  - **Definition 3 and Equation (1) (`[SchmidtSiegel1990]`, Theorem 1; `TR1995-687`, pp. 6–7)**:
    Defines the dependency set $\mathrm{dep}(x, D)$, dependency DAG $G(x, D)$, and partial
    dependency DAG $G_r(x, D)$ (vertices reachable from $x$ starting along the first $r$ probes of
    $x$). At bounded load factor $\alpha \le 1 / 32$, the trivial vacancy overestimator
    $q(i) \equiv 1$ yields $O(1)$ expected probes by bounding the probability of size-$w$ partial
    dependency witnesses without the vacancy inclusion-exclusion machinery needed for
    $\alpha \to 1$.
  - **Appendix A, Lemma A (`TR1995-687`, pp. 37–39)**: Bounds the probability that a $w$-vertex
    subset hashes into a dependency tree (Part 1, pp. 37–38) or into a non-tree dependency DAG with
    spanning tree $Tr$ (Part 2, pp. 38–39) by charging one non-tree collision per vertex with a
    diamond edge.
* **M. Thorup ([Thorup2013], FOCS 2013, pp. 90–99; arXiv:1311.3121v2, 16 October 2018, Section 1.1
  Theorem 1(a) and Lemma 2, and Section 3, pp. 4–5, 11–13)**:
  Conditioned on $k$-uniqueness (`IsKUnique k (simpleTabTuple T₁)`), `doubleTabHash` is $k$-wise
  independent (`isKWiseIndependentHash_doubleTabHash_of_isKUnique`), and the fraction of
  non-$k$-unique top seeds is at most $2 (\mathrm{doubleTabCodeBound}\ c\ (8c)\ 4\ k)^2 / 2^{6b}$
  (`card_not_isKUnique_eight_mul_le`).
* **Original elementary adaptations**:
  1. **Breadth-first search (`BFS`) spanning-tree ordering**: We order the vertices of a closed
     partial dependency set $W = \mathrm{partialDepSet}(x_0, r)$ by a flat BFS queue. Every
     non-tree probe of $x_b$ then hits a slot in the set $F_{< b}$ of slots already enqueued before
     $x_b$'s expansion, while the $h_{b+1}$ new tree-child slots of $x_b$ are the first $h_{b+1}$
     slots of $[\pi(x_b, 0), \dots, \pi(x_b, w - 1)]$ outside $F_{< b}$ independently of the
     landing index $k_b$.
  2. **Power-of-two quotient fiber bound (`Nat.card_odd_mul_mod_eq_le`)**: On $m = 2^M$, an even
     probe-index difference $\Delta = k_b - j_1 \in [1, w]$ is not invertible mod $2^M$, but the
     Euclidean quotient map $s \mapsto \lfloor \Delta(2s + 1)/2^M \rfloor \in \mathrm{Fin}\ \Delta$
     bounds the stride fiber by $\Delta \le w$.
  3. **Deterministic pigeonhole bound & high-probability conditioning bridge**: Every odd stride
     $2 h_2(u) + 1$ is coprime to $2^M$, so `oddStridePerm` is a full-cycle permutation on *every*
     seed and `probeCount ≤ n_max + 1` holds deterministically (`probeCount_le_add_one`). This
     bounds both the bad-top-seed tail for $n_{\max} \ge \mathrm{doubleTabThreshold}\ c_{\exp}$ and
     the entire small-capacity regime $n_{\max} < \mathrm{doubleTabThreshold}\ c_{\exp}$.

## Main definitions

* `Cslib.Algorithms.Lean.DoubleHashing.OrderedTableRep`: open-addressed representation invariant
  extending `UniformProbing.TableRep` with an acyclic insertion-order rank.
* `Cslib.Algorithms.Lean.DoubleHashing.oddStrideSeq`,
  `Cslib.Algorithms.Lean.DoubleHashing.oddStridePerm`,
  `Cslib.Algorithms.Lean.DoubleHashing.twoStageOddStridePerm`: full-cycle odd-stride double-hashing
  probe sequence and permutation families on `Fin (2 ^ M)`.
* `Cslib.Algorithms.Lean.DoubleHashing.maxProbeCutoff`,
  `Cslib.Algorithms.Lean.DoubleHashing.DoubleTabOddStrideSeed`,
  `Cslib.Algorithms.Lean.DoubleHashing.doubleTabOddStridePerm`,
  `Cslib.Algorithms.Lean.DoubleHashing.DoubleHashSeed`,
  `Cslib.Algorithms.Lean.DoubleHashing.doubleHashOddStridePerm`: cutoff parameter and Double
  Tabulation seed types and permutation families.

## Main results

* `Cslib.Algorithms.Lean.DoubleHashing.probeCount_le_card_otherOccupied_add_one`,
  `Cslib.Algorithms.Lean.DoubleHashing.probeCount_le_add_one`: deterministic pigeonhole
  bound `probeCount T u (π u) ≤ n_max + 1`.
* `Cslib.Algorithms.Lean.DoubleHashing.OrderedTableRep.empty`,
  `Cslib.Algorithms.Lean.DoubleHashing.OrderedTableRep.tableInsert`,
  `Cslib.Algorithms.Lean.DoubleHashing.orderedTableRep_runTable`: preservation of `OrderedTableRep`.
* `Cslib.Algorithms.Lean.DoubleHashing.sum_probeCount_oddStride_le_of_kWiseIndependent`,
  `Cslib.Algorithms.Lean.DoubleHashing.expect_probeCount_oddStride_of_kWiseIndependent`: expected
  probe count $\le 2$ under $(2 L + 1)$-wise independent $(h_1, h_2)$.
* `Cslib.Algorithms.Lean.DoubleHashing.sum_probeCount_oddStride_of_whp_kWiseIndependent`,
  `Cslib.Algorithms.Lean.DoubleHashing.expect_probeCount_oddStride_of_whp_kWiseIndependent`:
  expected probe count $\le 3$ under high-probability $(2 L + 1)$-wise independence.
* `Cslib.Algorithms.Lean.DoubleHashing.sum_probeCount_oddStride_doubleTab_le`,
  `Cslib.Algorithms.Lean.DoubleHashing.expect_probeCount_oddStride_doubleTab_le`,
  `Cslib.Algorithms.Lean.DoubleHashing.expect_probeCount_oddStride_unconditional_le`: expected probe
  count $\le 3$ under Double Tabulation for $n_{\max} \ge \mathrm{doubleTabThreshold}\ c_{\exp}$,
  and $\le \max(\mathrm{doubleTabThreshold}\ c_{\exp}, 3)$ unconditionally across all $n_{\max}$.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*, third edition (MIT Press, 2009), Section 11.4,
  pp. 269–277][CLRS2009]
* [J. P. Schmidt and A. Siegel, *The Analysis of Closed Hashing under Limited
  Randomness*][SchmidtSiegel1990]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence*][Thorup2013]
-/

public section

namespace Cslib.Algorithms.Lean.DoubleHashing

open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.UniformProbing
open Cslib.Probability
open scoped BigOperators ENNReal

/-! ## Section 1: Deterministic Pigeonhole Bound and Acyclic Insertion-Order Invariant -/

/-- For any occupied slot set `O : Finset (Fin m)` and permutation `σ : Equiv.Perm (Fin m)`, the
number of consecutive missed probes `missedProbes O σ` is at most `O.card` by injectivity of `σ`. -/
theorem missedProbes_le_card {m : ℕ} (O : Finset (Fin m)) (σ : Equiv.Perm (Fin m)) :
    missedProbes O σ ≤ O.card := by
  have hle_m : missedProbes O σ ≤ m := missedProbes_le O σ
  have hall : allOccupied O (missedProbes O σ) σ :=
    (le_missedProbes_iff_allOccupied hle_m σ).mp le_rfl
  let f : Fin (missedProbes O σ) → Fin m := fun i => σ ⟨i.val, lt_of_lt_of_le i.isLt hle_m⟩
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin (missedProbes O σ))), f i ∈ O :=
    fun i _ => hall ⟨i.val, lt_of_lt_of_le i.isLt hle_m⟩ i.isLt
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin (missedProbes O σ))) := by
    intro i _ j _ hij
    have hfin := σ.injective hij
    exact Fin.ext (Fin.mk.inj hfin)
  simpa using Finset.card_le_card_of_injOn f hmaps hinj

/-- **Deterministic Pigeonhole Probe Bound**: for any table `T : Table U m`, key `u : Fin U`, and
probe permutation `σ : Equiv.Perm (Fin m)`, `probeCount T u σ ≤ (otherOccupiedSlots T u).card + 1`.
-/
theorem probeCount_le_card_otherOccupied_add_one {U m : ℕ} (T : Table U m) (u : Fin U)
    (σ : Equiv.Perm (Fin m)) :
    probeCount T u σ ≤ (otherOccupiedSlots T u).card + 1 := by
  rw [probeCount, unsuccessfulProbes, Nat.add_comm]
  exact Nat.add_le_add_right (missedProbes_le_card (otherOccupiedSlots T u) σ) 1

/-- Under `TableRep π s T`, `probeCount T u (π u) ≤ (Dictionary.dom s).card + 1` holds
deterministically for every key `u : Fin U`. -/
theorem probeCount_le_dom_card_add_one {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T) (u : Fin U) :
    probeCount T u (π u) ≤ (Dictionary.dom s).card + 1 :=
  (probeCount_le_card_otherOccupied_add_one T u (π u)).trans
    (Nat.add_le_add_right (hrep.card_otherOccupiedSlots_le u) 1)

/-- Under `TableRep π s T` and `(Dictionary.dom s).card ≤ n_max`,
`probeCount T u (π u) ≤ n_max + 1` holds deterministically for every key `u : Fin U`. -/
theorem probeCount_le_add_one {U m n_max : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    probeCount T u (π u) ≤ n_max + 1 :=
  (probeCount_le_dom_card_add_one hrep u).trans (Nat.add_le_add_right hdom 1)

/-- Open-addressed table representation invariant extending `TableRep π s T` with an acyclic
insertion-order witness `rank : Fin U → ℕ`: for every stored key `w ∈ Dictionary.dom s` and every
failed probe index `i : Fin m` with `i.val < missedProbes (otherOccupiedSlots T w) (π w)`, the slot
`π w i` holds a distinct key `y ∈ (Dictionary.dom s).erase w` with `rank y < rank w`. -/
structure OrderedTableRep {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) (s : Dictionary.State U)
    (T : Table U m) : Prop extends TableRep π s T where
  /-- Existence of an insertion-order ranking under which every failed probe of a stored key `w`
  is blocked by a strictly lower-ranked key `y ∈ (Dictionary.dom s).erase w`. -/
  exists_rank : ∃ rank : Fin U → ℕ,
    ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w

/-- The empty table satisfies `OrderedTableRep` under any permutation family `π`. -/
theorem OrderedTableRep.empty {U m : ℕ} (π : Fin U → Equiv.Perm (Fin m)) :
    OrderedTableRep π (Dictionary.empty U) (emptyTable U m) where
  toTableRep := tableRep_empty π
  exists_rank := ⟨fun _ => 0, fun w hw => by simp [Dictionary.empty, Dictionary.dom] at hw⟩

/-- **Preservation of `OrderedTableRep` under `tableInsert`**: if `OrderedTableRep π s T` and
`(otherOccupiedSlots T u).card < m`, then `tableInsert hm π T u v` satisfies
`OrderedTableRep π (Function.update s u (some v))`. -/
theorem OrderedTableRep.tableInsert {U m : ℕ} (hm : 0 < m) {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : OrderedTableRep π s T) (u : Fin U) (v : ℕ)
    (hO : (otherOccupiedSlots T u).card < m) :
    OrderedTableRep π (Function.update s u (some v))
      (UniformProbing.tableInsert hm π T u v) where
  toTableRep := hrep.toTableRep.tableInsert hm u v hO
  exists_rank := by
    classical
    obtain ⟨rank, hrank⟩ := hrep.exists_rank
    have hupd := tableInsert_eq_update_targetSlot hm π T u v hO
    have htarget := hrep.toTableRep.apply_targetSlot u hO
    cases hsu : s u with
    | some v₀ =>
      have hu_dom : u ∈ Dictionary.dom s := Dictionary.mem_dom_iff.mpr ⟨v₀, hsu⟩
      have hdom_eq : Dictionary.dom (Function.update s u (some v)) = Dictionary.dom s :=
        Dictionary.dom_insert_of_mem hu_dom v
      refine ⟨rank, fun w hw i hi => ?_⟩
      rw [hdom_eq] at hw ⊢
      have hw_some : (s w).isSome := Dictionary.mem_dom_iff_isSome.mp hw
      rw [hrep.toTableRep.missedProbes_tableInsert_of_isSome hm u v hO hw_some] at hi
      obtain ⟨y, hy_erase, vy, hTwi, hlt_rank⟩ := hrank w hw i hi
      rw [hupd]
      by_cases hslot : π w i = targetSlot π T u hO
      · have hTu : T (π w i) = some (u, v₀) := by simpa [hslot, hsu] using htarget
        rw [hTwi] at hTu
        injection hTu with hpair
        injection hpair with hyu _
        subst hyu
        exact ⟨y, hy_erase, v, by simp [hslot], hlt_rank⟩
      · exact ⟨y, hy_erase, vy, by simp [Function.update_of_ne hslot, hTwi], hlt_rank⟩
    | none =>
      have hu_not_dom : u ∉ Dictionary.dom s := Dictionary.notMem_dom_iff.mpr hsu
      let rank' : Fin U → ℕ := Function.update rank u ((Dictionary.dom s).sup rank + 1)
      have hrank'_mem : ∀ {y : Fin U}, y ∈ Dictionary.dom s → rank' y = rank y := by
        intro y hy
        have hyu : y ≠ u := fun h => hu_not_dom (h ▸ hy)
        exact Function.update_of_ne hyu _ _
      have hrank'_lt_u : ∀ {y : Fin U}, y ∈ Dictionary.dom s → rank' y < rank' u := by
        intro y hy
        rw [hrank'_mem hy]
        have hle : rank y ≤ (Dictionary.dom s).sup rank := Finset.le_sup hy
        have hru : rank' u = (Dictionary.dom s).sup rank + 1 := Function.update_self u _ rank
        omega
      refine ⟨rank', fun w hw i hi => ?_⟩
      rw [Dictionary.dom_insert] at hw ⊢
      rcases Finset.mem_insert.mp hw with rfl | hw_dom
      · rw [otherOccupiedSlots_tableInsert_self hm hrep.toTableRep w v hO] at hi
        have hmp_lt : missedProbes (otherOccupiedSlots T w) (π w) < m :=
          missedProbes_lt_of_card_lt hO (π w)
        have hi_mem : π w i ∈ otherOccupiedSlots T w :=
          (le_missedProbes_iff_allOccupied (le_of_lt hmp_lt) (π w)).mp le_rfl i hi
        rcases mem_otherOccupiedSlots_iff.mp hi_mem with ⟨y, vy, hTwi, hyw⟩
        have hy_dom : y ∈ Dictionary.dom s :=
          Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.toTableRep.slot_spec _ y vy hTwi).1⟩
        have hslot : π w i ≠ targetSlot π T w hO := by
          intro heq
          have hTnone : T (targetSlot π T w hO) = none := by simpa [hsu] using htarget
          rw [← heq, hTwi] at hTnone
          cases hTnone
        refine ⟨y, Finset.mem_erase.mpr ⟨hyw, Finset.mem_insert_of_mem hy_dom⟩, vy, ?_,
          hrank'_lt_u hy_dom⟩
        rw [hupd, Function.update_of_ne hslot]
        exact hTwi
      · have hw_some : (s w).isSome := Dictionary.mem_dom_iff_isSome.mp hw_dom
        rw [hrep.toTableRep.missedProbes_tableInsert_of_isSome hm u v hO hw_some] at hi
        obtain ⟨y, hy_erase, vy, hTwi, hlt_rank⟩ := hrank w hw_dom i hi
        rcases Finset.mem_erase.mp hy_erase with ⟨hyw, hy_dom⟩
        have hslot : π w i ≠ targetSlot π T u hO := by
          intro heq
          have hTnone : T (targetSlot π T u hO) = none := by simpa [hsu] using htarget
          rw [← heq, hTwi] at hTnone
          cases hTnone
        refine ⟨y, Finset.mem_erase.mpr ⟨hyw, Finset.mem_insert_of_mem hy_dom⟩, vy, ?_, ?_⟩
        · rw [hupd, Function.update_of_ne hslot]
          exact hTwi
        · rw [hrank'_mem hy_dom, hrank'_mem hw_dom]
          exact hlt_rank

/-- Convenience wrapper for `OrderedTableRep.tableInsert` when `(Dictionary.dom s).card < m`. -/
theorem OrderedTableRep.tableInsert_of_card_lt {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : OrderedTableRep π s T)
    (hcard : (Dictionary.dom s).card < m) (u : Fin U) (v : ℕ) :
    OrderedTableRep π (Function.update s u (some v))
      (UniformProbing.tableInsert (Nat.pos_of_ne_zero (by omega)) π T u v) :=
  hrep.tableInsert (Nat.pos_of_ne_zero (by omega)) u v
    (lt_of_le_of_lt (hrep.toTableRep.card_otherOccupiedSlots_le u) hcard)

/-- Any valid operation history preserves `OrderedTableRep`. -/
theorem orderedTableRep_runTableFrom {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {s : Dictionary.State U} {T : Table U m}
    (hrep : OrderedTableRep π s T) (hs : (Dictionary.dom s).card ≤ n_max)
    {ops : List (Dictionary.Op U)} (hvh : (Dictionary.spec U V n_max).ValidHistory s ops) :
    OrderedTableRep π ((Dictionary.spec U V n_max).run s ops).1 (runTableFrom hm π T ops) := by
  induction ops generalizing s T with
  | nil => exact hrep
  | cons o os ih =>
    have hs' : (Dictionary.dom ((Dictionary.spec U V n_max).stepFn s o).1).card ≤ n_max :=
      Dictionary.card_dom_step_le_of_valid hs hvh.1
    cases o with
    | get u =>
      exact ih hrep hs' hvh.2
    | insert u v =>
      have hO : (otherOccupiedSlots T u).card < m :=
        hrep.toTableRep.card_otherOccupiedSlots_lt_of_valid hm hcap hs hvh.1
      exact ih (hrep.tableInsert hm u v hO) hs' hvh.2

/-- Running any valid operation history from `emptyTable U m` produces a table satisfying
`OrderedTableRep`. -/
theorem orderedTableRep_runTable {U V n_max m : ℕ} (hm : 0 < m) (hcap : n_max ≤ m)
    (π : Fin U → Equiv.Perm (Fin m)) {ops : List (Dictionary.Op U)}
    (hvh : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    OrderedTableRep π ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1
      (runTable hm π ops) :=
  orderedTableRep_runTableFrom hm hcap π (OrderedTableRep.empty π) (by simp) hvh

/-! ## Section 2: Odd-Stride Double-Hashing Probe Permutation on `Fin (2 ^ M)` -/

/-- Power-of-two odd-stride double-hashing probe sequence
`oddStrideSeq M p s i = (p + i * (2 * s + 1)) mod 2 ^ M` on `Fin (2 ^ M)` ([CLRS2009], Section 11.4,
"Double hashing", pp. 272–274). -/
@[expose] def oddStrideSeq (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1)))
    (i : Fin (2 ^ M)) : Fin (2 ^ M) :=
  ⟨(p.val + i.val * (2 * s.val + 1)) % 2 ^ M, Nat.mod_lt _ (Nat.two_pow_pos M)⟩

private theorem coprime_two_mul_add_one_two_pow (M s : ℕ) :
    Nat.Coprime (2 * s + 1) (2 ^ M) := by
  have hcop2 : Nat.Coprime 2 (2 * s + 1) := by
    rw [Nat.coprime_two_left, Nat.odd_iff]
    omega
  exact (hcop2.pow_left M).symm

/-- Because `2 * s.val + 1` is odd and therefore coprime to `2 ^ M`, `oddStrideSeq M p s` is a
bijection on `Fin (2 ^ M)` for every `p` and `s`. -/
theorem bijective_oddStrideSeq (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1))) :
    Function.Bijective (oddStrideSeq M p s) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, rfl⟩
  have hinj : ∀ i j : Fin (2 ^ M), j.val ≤ i.val →
      oddStrideSeq M p s i = oddStrideSeq M p s j → i = j := by
    intro i j hij heq
    have hmod : (p.val + j.val * (2 * s.val + 1)) ≡
        (p.val + i.val * (2 * s.val + 1)) [MOD 2 ^ M] := by
      simpa [oddStrideSeq, Fin.ext_iff, Nat.ModEq] using heq.symm
    have hmul : j.val * (2 * s.val + 1) ≡ i.val * (2 * s.val + 1) [MOD 2 ^ M] :=
      Nat.ModEq.add_left_cancel' p.val hmod
    have hsub : 0 + j.val * (2 * s.val + 1) ≡
        (i.val - j.val) * (2 * s.val + 1) + j.val * (2 * s.val + 1) [MOD 2 ^ M] := by
      simpa [Nat.zero_add, ← Nat.add_mul, Nat.sub_add_cancel hij] using hmul
    have hzero : 0 ≡ (i.val - j.val) * (2 * s.val + 1) [MOD 2 ^ M] :=
      Nat.ModEq.add_right_cancel' (j.val * (2 * s.val + 1)) hsub
    have hdvd_mul : 2 ^ M ∣ (i.val - j.val) * (2 * s.val + 1) :=
      Nat.modEq_zero_iff_dvd.mp hzero.symm
    have hdvd : 2 ^ M ∣ i.val - j.val :=
      (coprime_two_mul_add_one_two_pow M s.val).symm.dvd_of_dvd_mul_right hdvd_mul
    have hlt : i.val - j.val < 2 ^ M := by
      have := i.isLt
      omega
    have hdiff0 : i.val - j.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (by omega)
  intro i j heq
  rcases le_total j.val i.val with hij | hij
  · exact hinj i j hij heq
  · exact (hinj j i hij heq.symm).symm

/-- Noncomputable full-cycle permutation `Equiv.Perm (Fin (2 ^ M))` induced by primary hash value
`p : Fin (2 ^ M)` and stride index `s : Fin (2 ^ (M - 1))`. -/
noncomputable def oddStridePermOfPair (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1))) :
    Equiv.Perm (Fin (2 ^ M)) :=
  Equiv.ofBijective (oddStrideSeq M p s) (bijective_oddStrideSeq M p s)

@[simp]
theorem oddStridePermOfPair_apply (M : ℕ) (p : Fin (2 ^ M)) (s : Fin (2 ^ (M - 1)))
    (i : Fin (2 ^ M)) :
    oddStridePermOfPair M p s i = oddStrideSeq M p s i := by
  rfl

/-- Odd-stride double-hashing permutation family `Fin U → Equiv.Perm (Fin (2 ^ M))` constructed
from a primary hash function `h₁ : Fin U → Fin (2 ^ M)` and a half-range stride hash function
`h₂ : Fin U → Fin (2 ^ (M - 1))`. -/
noncomputable def oddStridePerm {U M : ℕ} (h₁ : Fin U → Fin (2 ^ M))
    (h₂ : Fin U → Fin (2 ^ (M - 1))) (u : Fin U) : Equiv.Perm (Fin (2 ^ M)) :=
  oddStridePermOfPair M (h₁ u) (h₂ u)

@[simp]
theorem oddStridePerm_apply {U M : ℕ} (h₁ : Fin U → Fin (2 ^ M))
    (h₂ : Fin U → Fin (2 ^ (M - 1))) (u : Fin U) (i : Fin (2 ^ M)) :
    oddStridePerm h₁ h₂ u i = oddStrideSeq M (h₁ u) (h₂ u) i := by
  rfl

theorem val_oddStridePerm {U M : ℕ} (h₁ : Fin U → Fin (2 ^ M))
    (h₂ : Fin U → Fin (2 ^ (M - 1))) (u : Fin U) (i : Fin (2 ^ M)) :
    (oddStridePerm h₁ h₂ u i).val =
      ((h₁ u).val + i.val * (2 * (h₂ u).val + 1)) % 2 ^ M := by
  rfl

/-! ## Section 3: Dependency Sets and the Minimal Overflow Dichotomy -/

/-- Maximum probe-depth cutoff `L = Nat.clog 2 (max n_max 4) + 4` for the partial dependency
dichotomy ([SchmidtSiegel1990], Theorem 1). -/
@[expose] def maxProbeCutoff (n_max : ℕ) : ℕ :=
  Nat.clog 2 (max n_max 4) + 4

/-- Extended insertion-order rank placing an absent query key `u ∉ Dictionary.dom s` strictly
above all stored keys in `Dictionary.dom s`. -/
private def extRank {U : ℕ} (s : Dictionary.State U) (rank : Fin U → ℕ) (u : Fin U) :
    Fin U → ℕ :=
  if u ∈ Dictionary.dom s then rank
  else Function.update rank u ((Dictionary.dom s).sup rank + 1)

private theorem extRank_blocker_spec {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x : Fin U} (hx : x ∈ insert u (Dictionary.dom s))
    {i : Fin m} (hi : i.val < missedProbes (otherOccupiedSlots T x) (π x)) :
    ∃ y ∈ (Dictionary.dom s).erase x, ∃ vy : ℕ,
      T (π x i) = some (y, vy) ∧ extRank s rank u y < extRank s rank u x := by
  classical
  by_cases hu : u ∈ Dictionary.dom s
  · have hx_dom : x ∈ Dictionary.dom s := by
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hu
      · exact hx'
    obtain ⟨y, hy, vy, hT, hlt⟩ := hrank x hx_dom i hi
    exact ⟨y, hy, vy, hT, by simpa [extRank, hu] using hlt⟩
  · have hmem_eq : ∀ {z : Fin U}, z ∈ Dictionary.dom s → extRank s rank u z = rank z := by
      intro z hz
      have hzu : z ≠ u := fun h => hu (h ▸ hz)
      simp [extRank, hu, Function.update_of_ne hzu]
    rcases Finset.mem_insert.mp hx with rfl | hx_dom
    · have hle_m : missedProbes (otherOccupiedSlots T x) (π x) ≤ m :=
        missedProbes_le (otherOccupiedSlots T x) (π x)
      have hmem : π x i ∈ otherOccupiedSlots T x :=
        (le_missedProbes_iff_allOccupied hle_m (π x)).mp le_rfl i hi
      rcases mem_otherOccupiedSlots_iff.mp hmem with ⟨y, vy, hT, hyx⟩
      have hy_dom : y ∈ Dictionary.dom s :=
        Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.slot_spec _ y vy hT).1⟩
      refine ⟨y, Finset.mem_erase.mpr ⟨hyx, hy_dom⟩, vy, hT, ?_⟩
      rw [hmem_eq hy_dom]
      have hle_sup : rank y ≤ (Dictionary.dom s).sup rank := Finset.le_sup hy_dom
      have hux : extRank s rank x x = (Dictionary.dom s).sup rank + 1 := by
        simp [extRank, hu]
      omega
    · obtain ⟨y, hy, vy, hT, hlt⟩ := hrank x hx_dom i hi
      have hy_dom : y ∈ Dictionary.dom s := (Finset.mem_erase.mp hy).2
      refine ⟨y, hy, vy, hT, ?_⟩
      rw [hmem_eq hy_dom, hmem_eq hx_dom]
      exact hlt

/-- Keys `y : Fin U` with `r_ext y < r_ext x` that occupy a slot `π x i` among the first
`min r (missedProbes (otherOccupiedSlots T x) (π x))` probes of `x`. -/
private def directBlockers {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) : Finset (Fin U) :=
  Finset.univ.filter fun y =>
    r_ext y < r_ext x ∧
      ∃ i : Fin m, i.val < r ∧ i.val < missedProbes (otherOccupiedSlots T x) (π x) ∧
        (T (π x i)).map Prod.fst = some y

/-- Full dependency set of key `x` (including `x` itself), defined by well-founded recursion on
`r_ext x` ([SchmidtSiegel1990], Definition 3). -/
private def depSet {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) : Finset (Fin U) :=
  insert x ((directBlockers T π r_ext x m).attach.biUnion fun ⟨y, hy⟩ =>
    have : r_ext y < r_ext x := (Finset.mem_filter.mp hy).2.1
    depSet T π r_ext y)
termination_by r_ext x

/-- Partial dependency set of key `x` along its first `r` probes (excluding `x` itself), defined as
the union of `depSet T π r_ext y` over `y ∈ directBlockers T π r_ext x r` ([SchmidtSiegel1990],
Definition 3, $G_r(x, D)$). -/
private def partialDepSet {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) : Finset (Fin U) :=
  (directBlockers T π r_ext x r).biUnion (depSet T π r_ext)

private theorem depSet_eq {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    depSet T π r_ext x = insert x (partialDepSet T π r_ext x m) := by
  rw [depSet, partialDepSet]
  ext z
  simp

private theorem self_mem_depSet {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    x ∈ depSet T π r_ext x := by
  rw [depSet_eq]
  exact Finset.mem_insert_self x _

private theorem partialDepSet_zero {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    partialDepSet T π r_ext x 0 = ∅ := by
  ext z
  simp [partialDepSet, directBlockers]

private theorem partialDepSet_eq_of_missedProbes_le {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) {r : ℕ}
    (hr : missedProbes (otherOccupiedSlots T x) (π x) ≤ r) :
    partialDepSet T π r_ext x r = partialDepSet T π r_ext x m := by
  unfold partialDepSet directBlockers
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine and_congr_right fun _ => exists_congr fun i => ?_
  have := i.isLt
  exact ⟨fun ⟨_, h2, h3⟩ => ⟨this, h2, h3⟩, fun ⟨_, h2, h3⟩ => ⟨lt_of_lt_of_le h2 hr, h2, h3⟩⟩

private theorem rank_le_and_depSet_subset_of_mem_depSet {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) :
    ∀ {z : Fin U}, z ∈ depSet T π r_ext x →
      r_ext z ≤ r_ext x ∧ depSet T π r_ext z ⊆ depSet T π r_ext x := by
  induction hx : r_ext x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro z hz
    rw [depSet_eq] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz_part
    · exact ⟨by omega, Finset.Subset.refl _⟩
    · simp only [partialDepSet, Finset.mem_biUnion] at hz_part
      rcases hz_part with ⟨y, hy_dir, hzy⟩
      have hy_lt : r_ext y < n := hx ▸ (Finset.mem_filter.mp hy_dir).2.1
      obtain ⟨hzy_le, hsub_zy⟩ := ih (r_ext y) hy_lt y rfl hzy
      refine ⟨by omega, hsub_zy.trans ?_⟩
      intro w hw
      rw [depSet_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨y, hy_dir, hw⟩)

private theorem rank_lt_and_depSet_subset_of_mem_partialDepSet {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ)
    {z : Fin U} (hz : z ∈ partialDepSet T π r_ext x r) :
    r_ext z < r_ext x ∧ depSet T π r_ext z ⊆ partialDepSet T π r_ext x r := by
  simp only [partialDepSet, Finset.mem_biUnion] at hz
  rcases hz with ⟨y, hy_dir, hzy⟩
  have hy_lt : r_ext y < r_ext x := (Finset.mem_filter.mp hy_dir).2.1
  obtain ⟨hzy_le, hsub_zy⟩ := rank_le_and_depSet_subset_of_mem_depSet T π r_ext y hzy
  refine ⟨lt_of_le_of_lt hzy_le hy_lt, hsub_zy.trans ?_⟩
  intro w hw
  exact Finset.mem_biUnion.mpr ⟨y, hy_dir, hw⟩

private theorem notMem_partialDepSet_self {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) :
    x ∉ partialDepSet T π r_ext x r := by
  intro hx
  have hlt := (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x r hx).1
  omega

private theorem card_depSet_eq {U m : ℕ} (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (r_ext : Fin U → ℕ) (x : Fin U) :
    (depSet T π r_ext x).card =
      1 + (partialDepSet T π r_ext x (missedProbes (otherOccupiedSlots T x) (π x))).card := by
  rw [depSet_eq, ← partialDepSet_eq_of_missedProbes_le T π r_ext x le_rfl,
    Finset.card_insert_of_notMem (notMem_partialDepSet_self T π r_ext x _), Nat.add_comm]

private theorem mem_dom_of_mem_depSet {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (r_ext : Fin U → ℕ) {x : Fin U} (hx : x ∈ Dictionary.dom s) :
    ∀ {z : Fin U}, z ∈ depSet T π r_ext x → z ∈ Dictionary.dom s := by
  induction hn : r_ext x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro z hz
    rw [depSet_eq] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz_part
    · exact hx
    · simp only [partialDepSet, directBlockers, Finset.mem_biUnion, Finset.mem_filter,
        Finset.mem_univ, true_and] at hz_part
      rcases hz_part with ⟨y, ⟨hy_lt, i, -, -, hTy⟩, hzy⟩
      cases hTi : T (π x i) with
      | none => simp [hTi] at hTy
      | some p =>
        rcases p with ⟨y', vy⟩
        simp only [hTi, Option.map_some, Option.some.injEq] at hTy
        subst hTy
        have hy_dom : y' ∈ Dictionary.dom s :=
          Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.slot_spec _ y' vy hTi).1⟩
        exact ih (r_ext y') (hn ▸ hy_lt) hy_dom rfl hzy

private theorem mem_dom_of_mem_partialDepSet {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    (r_ext : Fin U → ℕ) (x : Fin U) (r : ℕ) {z : Fin U}
    (hz : z ∈ partialDepSet T π r_ext x r) :
    z ∈ Dictionary.dom s := by
  simp only [partialDepSet, directBlockers, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and] at hz
  rcases hz with ⟨y, ⟨_, i, -, -, hTy⟩, hzy⟩
  cases hTi : T (π x i) with
  | none => simp [hTi] at hTy
  | some p =>
    rcases p with ⟨y', vy⟩
    simp only [hTi, Option.map_some, Option.some.injEq] at hTy
    subst hTy
    have hy_dom : y' ∈ Dictionary.dom s :=
      Dictionary.mem_dom_iff.mpr ⟨vy, (hrep.slot_spec _ y' vy hTi).1⟩
    exact mem_dom_of_mem_depSet hrep r_ext hy_dom hzy

private theorem partialDepSet_subset_erase {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {r_ext : Fin U → ℕ} {u x : Fin U} (hx_le : r_ext x ≤ r_ext u) (r : ℕ) :
    partialDepSet T π r_ext x r ⊆ ((Dictionary.dom s).erase u).erase x := by
  intro z hz
  have hlt_x : r_ext z < r_ext x :=
    (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x r hz).1
  have hz_dom : z ∈ Dictionary.dom s := mem_dom_of_mem_partialDepSet hrep r_ext x r hz
  refine Finset.mem_erase.mpr ⟨by rintro rfl; omega,
    Finset.mem_erase.mpr ⟨by rintro rfl; omega, hz_dom⟩⟩

private theorem card_partialDepSet_ge {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x : Fin U} (hx : x ∈ insert u (Dictionary.dom s)) {r : ℕ}
    (hr : r ≤ missedProbes (otherOccupiedSlots T x) (π x)) :
    r ≤ (partialDepSet T π (extRank s rank u) x r).card := by
  classical
  have hrm : r ≤ m := hr.trans (missedProbes_le (otherOccupiedSlots T x) (π x))
  have hbl : ∀ i : Fin r,
      ∃ y ∈ directBlockers T π (extRank s rank u) x r,
        ∃ vy, T (π x ⟨i.val, lt_of_lt_of_le i.isLt hrm⟩) = some (y, vy) := by
    intro i
    have hi_mp : i.val < missedProbes (otherOccupiedSlots T x) (π x) :=
      lt_of_lt_of_le i.isLt hr
    obtain ⟨y, _, vy, hT, hlt⟩ :=
      extRank_blocker_spec hrep hrank u hx (i := ⟨i.val, lt_of_lt_of_le i.isLt hrm⟩) hi_mp
    refine ⟨y, ?_, vy, hT⟩
    simp only [directBlockers, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hlt, ⟨i.val, lt_of_lt_of_le i.isLt hrm⟩, i.isLt, hi_mp, by simp [hT]⟩
  choose f hf_mem hf_T using hbl
  have hmaps : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      f i ∈ partialDepSet T π (extRank s rank u) x r := by
    intro i _
    exact Finset.mem_biUnion.mpr ⟨f i, hf_mem i, self_mem_depSet T π _ (f i)⟩
  have hinj : Set.InjOn f (Finset.univ : Finset (Fin r)) := by
    intro i₁ _ i₂ _ heq
    obtain ⟨vy₁, hT₁⟩ := hf_T i₁
    obtain ⟨vy₂, hT₂⟩ := hf_T i₂
    rw [heq] at hT₁
    have hslot := hrep.slot_eq_of_same_key hT₁ hT₂
    have hfin := (π x).injective hslot
    exact Fin.ext (Fin.mk.inj hfin)
  simpa using Finset.card_le_card_of_injOn f hmaps hinj

private theorem missedProbes_lt_card_of_mem_partialDepSet {U m : ℕ}
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u x : Fin U) (r : ℕ) {z : Fin U}
    (hz : z ∈ partialDepSet T π (extRank s rank u) x r) :
    missedProbes (otherOccupiedSlots T z) (π z) <
      (partialDepSet T π (extRank s rank u) x r).card := by
  have hsub := (rank_lt_and_depSet_subset_of_mem_partialDepSet T π (extRank s rank u) x r hz).2
  have hcard_le : (depSet T π (extRank s rank u) z).card ≤
      (partialDepSet T π (extRank s rank u) x r).card :=
    Finset.card_le_card hsub
  rw [card_depSet_eq] at hcard_le
  have hz_dom : z ∈ Dictionary.dom s :=
    mem_dom_of_mem_partialDepSet hrep (extRank s rank u) x r hz
  have hge := card_partialDepSet_ge hrep hrank u (Finset.mem_insert_of_mem hz_dom) le_rfl
  omega

private theorem partialDepSet_succ_subset_union {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x : Fin U} (hx : x ∈ insert u (Dictionary.dom s)) {r : ℕ}
    (hr : r < missedProbes (otherOccupiedSlots T x) (π x)) :
    ∃ z ∈ (Dictionary.dom s).erase x,
      extRank s rank u z < extRank s rank u x ∧
      partialDepSet T π (extRank s rank u) x (r + 1) ⊆
        partialDepSet T π (extRank s rank u) x r ∪ depSet T π (extRank s rank u) z := by
  have hrm : r < m := lt_of_lt_of_le hr (missedProbes_le (otherOccupiedSlots T x) (π x))
  obtain ⟨z, hz_erase, vz, hTz, hlt_z⟩ :=
    extRank_blocker_spec hrep hrank u hx (i := ⟨r, hrm⟩) hr
  refine ⟨z, hz_erase, hlt_z, fun w hw => ?_⟩
  simp only [partialDepSet, directBlockers, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and] at hw
  rcases hw with ⟨y, ⟨hy_lt, i, hi_lt, hi_mp, hTy⟩, hwy⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hi_r | hi_eq
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
      ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy_lt, i, hi_r, hi_mp, hTy⟩, hwy⟩)
  · have hi_fin : i = ⟨r, hrm⟩ := Fin.ext hi_eq
    rw [hi_fin, hTz] at hTy
    simp only [Option.map_some, Option.some.injEq] at hTy
    subst hTy
    exact Finset.mem_union_right _ hwy

/-- **Minimal Overflow Dichotomy ([SchmidtSiegel1990], Theorem 1 & Lemma A)**:
for any `L ≥ 1` and query key `u : Fin U`, either
1. **(Normal Regime)** `missedProbes (otherOccupiedSlots T u) (π u) < L` and
   `(partialDepSet T π (extRank s rank u) u
     (missedProbes (otherOccupiedSlots T u) (π u))).card < L`,
   or
2. **(Overflow Regime)** there exist `x₀ ∈ insert u (Dictionary.dom s)` with
   `extRank s rank u x₀ ≤ extRank s rank u u` and `r₀ : ℕ` with
   `1 ≤ r₀ ∧ r₀ ≤ min (missedProbes (otherOccupiedSlots T x₀) (π x₀)) L` such that
   `L ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card` and
   `(partialDepSet T π (extRank s rank u) x₀ r₀).card < 2 * L`. -/
private theorem dichotomy_partialDepSet {U m : ℕ} {π : Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Table U m} (hrep : TableRep π s T)
    {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {L : ℕ} (hL : 1 ≤ L) :
    (missedProbes (otherOccupiedSlots T u) (π u) < L ∧
      (partialDepSet T π (extRank s rank u) u
        (missedProbes (otherOccupiedSlots T u) (π u))).card < L) ∨
      ∃ x₀ ∈ insert u (Dictionary.dom s),
        extRank s rank u x₀ ≤ extRank s rank u u ∧
        ∃ r₀ : ℕ, 1 ≤ r₀ ∧ r₀ ≤ min (missedProbes (otherOccupiedSlots T x₀) (π x₀)) L ∧
          L ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card ∧
          (partialDepSet T π (extRank s rank u) x₀ r₀).card < 2 * L := by
  classical
  by_cases hnorm :
      (partialDepSet T π (extRank s rank u) u
        (min (missedProbes (otherOccupiedSlots T u) (π u)) L)).card < L
  · left
    have hge := card_partialDepSet_ge hrep hrank u (Finset.mem_insert_self u _)
      (Nat.min_le_left (missedProbes (otherOccupiedSlots T u) (π u)) L)
    have hku_lt : missedProbes (otherOccupiedSlots T u) (π u) < L := by omega
    have hmin_eq : min (missedProbes (otherOccupiedSlots T u) (π u)) L =
        missedProbes (otherOccupiedSlots T u) (π u) := Nat.min_eq_left (le_of_lt hku_lt)
    rw [hmin_eq] at hnorm
    exact ⟨hku_lt, hnorm⟩
  · right
    have hnorm_ge : L ≤ (partialDepSet T π (extRank s rank u) u
        (min (missedProbes (otherOccupiedSlots T u) (π u)) L)).card := not_lt.mp hnorm
    let B := (insert u (Dictionary.dom s)).filter fun x =>
      extRank s rank u x ≤ extRank s rank u u ∧
        L ≤ (partialDepSet T π (extRank s rank u) x
          (min (missedProbes (otherOccupiedSlots T x) (π x)) L)).card
    have huB : u ∈ B := Finset.mem_filter.mpr
      ⟨Finset.mem_insert_self u _, le_rfl, hnorm_ge⟩
    obtain ⟨x₀, hx₀B, hmin_x₀⟩ := B.exists_min_image (extRank s rank u) ⟨u, huB⟩
    rcases Finset.mem_filter.mp hx₀B with ⟨hx₀_ins, hx₀_le_u, hx₀_ge_L⟩
    set k₀ := min (missedProbes (otherOccupiedSlots T x₀) (π x₀)) L
    have hex_r : ∃ r ≤ k₀, L ≤ (partialDepSet T π (extRank s rank u) x₀ r).card :=
      ⟨k₀, le_rfl, hx₀_ge_L⟩
    set r₀ := Nat.find hex_r
    have hr₀_spec : r₀ ≤ k₀ ∧ L ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card :=
      Nat.find_spec hex_r
    have hr₀_pos : 1 ≤ r₀ := by
      by_contra h0
      have hr0 : r₀ = 0 := by omega
      have hcard0 : (partialDepSet T π (extRank s rank u) x₀ r₀).card = 0 := by
        rw [hr0, partialDepSet_zero, Finset.card_empty]
      omega
    have hr₀_prev_lt : (partialDepSet T π (extRank s rank u) x₀ (r₀ - 1)).card < L := by
      by_contra hge_prev
      have hnot := Nat.find_min hex_r (show r₀ - 1 < r₀ by omega)
      exact hnot ⟨by omega, not_lt.mp hge_prev⟩
    have hr₀_prev_mp : r₀ - 1 < missedProbes (otherOccupiedSlots T x₀) (π x₀) := by
      have hk₀_le : k₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀) := Nat.min_le_left _ _
      omega
    obtain ⟨z, hz_erase, hlt_z, hsub_step⟩ :=
      partialDepSet_succ_subset_union hrep hrank u hx₀_ins hr₀_prev_mp
    have hr₀_eq : r₀ - 1 + 1 = r₀ := Nat.sub_add_cancel hr₀_pos
    rw [hr₀_eq] at hsub_step
    have hz_dom : z ∈ Dictionary.dom s := (Finset.mem_erase.mp hz_erase).2
    have hz_not_B : z ∉ B := fun hzB => not_lt_of_ge (hmin_x₀ z hzB) hlt_z
    have hz_lt_L :
        (partialDepSet T π (extRank s rank u) z
          (min (missedProbes (otherOccupiedSlots T z) (π z)) L)).card < L := by
      by_contra hge_z
      exact hz_not_B (Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem hz_dom,
          le_of_lt (lt_of_lt_of_le hlt_z hx₀_le_u), not_lt.mp hge_z⟩)
    have hkz_ge := card_partialDepSet_ge hrep hrank u (Finset.mem_insert_of_mem hz_dom)
      (Nat.min_le_left (missedProbes (otherOccupiedSlots T z) (π z)) L)
    have hkz_lt : missedProbes (otherOccupiedSlots T z) (π z) < L := by omega
    have hmin_z : min (missedProbes (otherOccupiedSlots T z) (π z)) L =
        missedProbes (otherOccupiedSlots T z) (π z) := Nat.min_eq_left (le_of_lt hkz_lt)
    rw [hmin_z] at hz_lt_L
    have hdep_z_le : (depSet T π (extRank s rank u) z).card ≤ L := by
      rw [card_depSet_eq]
      omega
    have hcard_r₀_lt : (partialDepSet T π (extRank s rank u) x₀ r₀).card < 2 * L := by
      have hle_union := (Finset.card_le_card hsub_step).trans (Finset.card_union_le _ _)
      omega
    exact ⟨x₀, hx₀_ins, hx₀_le_u, r₀, hr₀_pos, hr₀_spec.1, hr₀_spec.2, hcard_r₀_lt⟩

/-! ## Section 4: BFS Spanning-Tree Witness and `(2 * L + 1)`-Wise Independent Probe Bound -/

/-- Slot at step `i : ℕ` along `σ : Equiv.Perm (Fin m)` when `0 < m`. -/
private def probeAt {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (i : ℕ) : Fin m :=
  σ ⟨i % m, Nat.mod_lt i hm⟩

/-- First `l` slots probed along `σ : Equiv.Perm (Fin m)` when `0 < m`. -/
private def probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (l : ℕ) : List (Fin m) :=
  (List.range l).map (probeAt hm σ)

private theorem probeAt_eq_of_lt {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) {i : ℕ}
    (hi : i < m) : probeAt hm σ i = σ ⟨i, hi⟩ := by
  simp [probeAt, Nat.mod_eq_of_lt hi]

private theorem length_probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) (l : ℕ) :
    (probePrefix hm σ l).length = l := by
  simp [probePrefix]

private theorem nodup_probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) {l : ℕ}
    (hl : l ≤ m) : (probePrefix hm σ l).Nodup := by
  rw [probePrefix, List.nodup_map_iff_inj_on List.nodup_range]
  intro i hi j hj heq
  rw [List.mem_range] at hi hj
  rw [probeAt_eq_of_lt hm σ (lt_of_lt_of_le hi hl),
    probeAt_eq_of_lt hm σ (lt_of_lt_of_le hj hl)] at heq
  exact Fin.mk.inj (σ.injective heq)

private theorem take_probePrefix {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m)) {k w : ℕ}
    (hkw : k ≤ w) : (probePrefix hm σ w).take k = probePrefix hm σ k := by
  rw [probePrefix, probePrefix, ← List.map_take, List.take_range, Nat.min_eq_left hkw]

/-- Landing-index-free filter identity: if `k ≤ w` and `((probePrefix hm σ k).filter p).length = d`,
then taking the first `d` elements of `(probePrefix hm σ w).filter p` recovers
`(probePrefix hm σ k).filter p` without knowing `k`. -/
private theorem take_filter_probePrefix_eq {m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin m))
    {k w d : ℕ} (hkw : k ≤ w) (p : Fin m → Bool)
    (hd : ((probePrefix hm σ k).filter p).length = d) :
    ((probePrefix hm σ w).filter p).take d = (probePrefix hm σ k).filter p := by
  have hsplit := List.take_append_drop k (probePrefix hm σ w)
  rw [take_probePrefix hm σ hkw] at hsplit
  rw [← hsplit, List.filter_append, ← hd, List.take_left]

/-- Cumulative BFS slot queue parameterized only by `(x₀, w, h, x)` and the first `w` probes of
each vertex. -/
private def bfsQueue {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (x₀ : Fin U) (w : ℕ) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U) : ℕ → List (Fin m)
  | 0 => probePrefix hm (π x₀) (h 0)
  | b + 1 =>
    let q := bfsQueue hm π x₀ w h x b
    if hb : b < w then
      q ++ ((probePrefix hm (π (x ⟨b, hb⟩)) w).filter (· ∉ q)).take
        (h ⟨b + 1, Nat.succ_lt_succ hb⟩)
    else q

private theorem sum_fin_succ_eq {w : ℕ} (h : Fin (w + 1) → ℕ) :
    h 0 + (∑ i ∈ Finset.range w, if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0) =
      ∑ a : Fin (w + 1), h a := by
  rw [Fin.sum_univ_succ]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun i => if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt, Fin.succ]

/-- Local BFS step event at vertex `x b` (`b : Fin w`) given `q = bfsQueue hm π x₀ w h x b.val`
and `slot_b = q.getD b.val ⟨0, hm⟩`. -/
private def bfsStepEvent {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (x₀ : Fin U) (w : ℕ) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U) (b : Fin w) : Prop :=
  let q := bfsQueue hm π x₀ w h x b.val
  let slot_b := q.getD b.val ⟨0, hm⟩
  let σ := π (x b)
  probeAt hm σ (h ⟨b.val + 1, Nat.succ_lt_succ b.isLt⟩) = slot_b ∨
    ∃ k_b : Fin w, ∃ j₁ : Fin w,
      j₁.val < k_b.val ∧
      probeAt hm σ j₁.val ∈ q.toFinset ∧
      probeAt hm σ k_b.val = slot_b

private instance instDecidableBfsStepEvent {U m : ℕ} (hm : 0 < m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (w : ℕ) (h : Fin (w + 1) → ℕ)
    (x : Fin w → Fin U) (b : Fin w) :
    Decidable (bfsStepEvent hm π x₀ w h x b) := by
  unfold bfsStepEvent
  infer_instance

/-- Existence of a size-`w` BFS dependency witness rooted at `x₀` over stored keys `D`
([SchmidtSiegel1990], Appendix A, Lemma A). -/
private def HasBFSWitness {U m : ℕ} (hm : 0 < m) (π : Fin U → Equiv.Perm (Fin m))
    (D : Finset (Fin U)) (x₀ : Fin U) (w : ℕ) : Prop :=
  ∃ h : Fin (w + 1) → ℕ,
    1 ≤ h 0 ∧
    (∑ a : Fin (w + 1), h a = w) ∧
    ∃ x : Fin w → Fin U,
      Function.Injective x ∧
      (∀ b : Fin w, x b ∈ D.erase x₀) ∧
      ∀ b : Fin w, bfsStepEvent hm π x₀ w h x b

/-- Landing slot `probeAt hm (π y) (missedProbes (otherOccupiedSlots T y) (π y))` of key `y`. -/
private def landingSlot {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (y : Fin U) : Fin m :=
  probeAt hm (π y) (missedProbes (otherOccupiedSlots T y) (π y))

/-- Key stored at slot `j` in `T`, defaulting to `u₀` if `T j = none`. -/
private def keyAt {U m : ℕ} (T : Table U m) (u₀ : Fin U) (j : Fin m) : Fin U :=
  match T j with
  | some (y, _) => y
  | none => u₀

private theorem apply_landingSlot_of_mem_dom {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {y : Fin U} (hy : y ∈ Dictionary.dom s) :
    ∃ vy, T (landingSlot hm T π y) = some (y, vy) := by
  obtain ⟨vy, hsy⟩ := Dictionary.mem_dom_iff.mp hy
  obtain ⟨hlt, hTy⟩ := hrep.key_spec y vy hsy
  refine ⟨vy, ?_⟩
  simpa [landingSlot, probeAt_eq_of_lt hm (π y) hlt] using hTy

private theorem keyAt_landingSlot_of_mem_dom {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) (u₀ : Fin U) {y : Fin U} (hy : y ∈ Dictionary.dom s) :
    keyAt T u₀ (landingSlot hm T π y) = y := by
  obtain ⟨vy, hTy⟩ := apply_landingSlot_of_mem_dom hm hrep hy
  simp [keyAt, hTy]

private theorem landingSlot_injOn_dom {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {y₁ y₂ : Fin U} (hy₁ : y₁ ∈ Dictionary.dom s)
    (hy₂ : y₂ ∈ Dictionary.dom s)
    (heq : landingSlot hm T π y₁ = landingSlot hm T π y₂) : y₁ = y₂ := by
  have h1 := keyAt_landingSlot_of_mem_dom hm hrep y₁ hy₁
  have h2 := keyAt_landingSlot_of_mem_dom hm hrep y₁ hy₂
  rw [heq, h2] at h1
  exact h1.symm

private theorem toFinset_probePrefix_eq_image_directBlockers {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {z : Fin U} (hz : z ∈ insert u (Dictionary.dom s)) {r : ℕ}
    (hr : r ≤ missedProbes (otherOccupiedSlots T z) (π z)) :
    (probePrefix hm (π z) r).toFinset =
      (directBlockers T π (extRank s rank u) z r).image (landingSlot hm T π) := by
  ext j
  simp only [List.mem_toFinset, probePrefix, List.mem_map, List.mem_range, Finset.mem_image,
    directBlockers, Finset.mem_filter, Finset.mem_univ, true_and]
  have hrm : r ≤ m := hr.trans (missedProbes_le (otherOccupiedSlots T z) (π z))
  constructor
  · rintro ⟨i, hi_r, rfl⟩
    have hi_m : i < m := lt_of_lt_of_le hi_r hrm
    have hi_mp : i < missedProbes (otherOccupiedSlots T z) (π z) := lt_of_lt_of_le hi_r hr
    obtain ⟨y, _, vy, hTy, hlt_y⟩ :=
      extRank_blocker_spec hrep hrank u hz (i := ⟨i, hi_m⟩) hi_mp
    obtain ⟨_, hlt_mp_y, hslot_y⟩ := hrep.slot_spec _ y vy hTy
    refine ⟨y, ⟨hlt_y, ⟨i, hi_m⟩, hi_r, hi_mp, by simp [hTy]⟩, ?_⟩
    rw [landingSlot, probeAt_eq_of_lt hm (π y) hlt_mp_y, probeAt_eq_of_lt hm (π z) hi_m, hslot_y]
  · rintro ⟨y, ⟨_, i, hi_r, _, hTy⟩, rfl⟩
    cases hTi : T (π z i) with
    | none => simp [hTi] at hTy
    | some p =>
      rcases p with ⟨y', vy⟩
      simp only [hTi, Option.map_some, Option.some.injEq] at hTy
      subst hTy
      obtain ⟨_, hlt_mp_y, hslot_y⟩ := hrep.slot_spec _ y' vy hTi
      refine ⟨i.val, hi_r, ?_⟩
      rw [probeAt_eq_of_lt hm (π z) i.isLt, landingSlot, probeAt_eq_of_lt hm (π y') hlt_mp_y,
        ← hslot_y]

private theorem depSet_subset_of_directBlockers_closed {U m : ℕ} (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (r_ext : Fin U → ℕ) {C : Finset (Fin U)}
    (hclosed : ∀ z ∈ C, directBlockers T π r_ext z m ⊆ C) {y : Fin U} (hy : y ∈ C) :
    depSet T π r_ext y ⊆ C := by
  induction hn : r_ext y using Nat.strong_induction_on generalizing y with
  | _ n ih =>
    intro w hw
    rw [depSet_eq] at hw
    rcases Finset.mem_insert.mp hw with rfl | hw_part
    · exact hy
    · simp only [partialDepSet, Finset.mem_biUnion] at hw_part
      rcases hw_part with ⟨z, hz_dir, hwz⟩
      have hz_lt : r_ext z < n := hn ▸ (Finset.mem_filter.mp hz_dir).2.1
      have hzC : z ∈ C := hclosed y hy hz_dir
      exact ih (r_ext z) hz_lt hzC rfl hwz

/-- Raw BFS slot queue constructed directly from `(T, π, x₀, r₀)`. -/
private def rawQueue {U m : ℕ} (hm : 0 < m) (T : Table U m) (π : Fin U → Equiv.Perm (Fin m))
    (x₀ : Fin U) (r₀ : ℕ) : ℕ → List (Fin m)
  | 0 => probePrefix hm (π x₀) r₀
  | b + 1 =>
    let q := rawQueue hm T π x₀ r₀ b
    let slot_b := q.getD b ⟨0, hm⟩
    let x_b := keyAt T x₀ slot_b
    let k_b := missedProbes (otherOccupiedSlots T x_b) (π x_b)
    q ++ (probePrefix hm (π x_b) k_b).filter (· ∉ q)

private theorem nodup_rawQueue {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) {r₀ : ℕ} (hr₀ : r₀ ≤ m) :
    ∀ b : ℕ, (rawQueue hm T π x₀ r₀ b).Nodup
  | 0 => nodup_probePrefix hm (π x₀) hr₀
  | b + 1 => by
    dsimp only [rawQueue]
    refine List.nodup_append.mpr ⟨nodup_rawQueue hm T π x₀ hr₀ b,
      (nodup_probePrefix hm _ (missedProbes_le _ _)).filter _, ?_⟩
    intro j₁ hj₁ j₂ hj₂ heq
    subst heq
    have hj_not := (List.mem_filter.mp hj₂).2
    simp [hj₁] at hj_not

private theorem length_rawQueue_le_of_le {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (rawQueue hm T π x₀ r₀ a).length ≤ (rawQueue hm T π x₀ r₀ b).length := by
  induction hab with
  | refl => exact le_rfl
  | @step c _ ih =>
    dsimp only [rawQueue]
    rw [List.length_append]
    omega

private theorem mem_rawQueue_of_le {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ : ℕ) {a b : ℕ} (hab : a ≤ b)
    {j : Fin m} (hj : j ∈ rawQueue hm T π x₀ r₀ a) :
    j ∈ rawQueue hm T π x₀ r₀ b := by
  induction hab with
  | refl => exact hj
  | @step c _ ih =>
    dsimp only [rawQueue]
    exact List.mem_append_left _ ih

private theorem getD_eq_getElem_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ}
    (hi : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

private theorem getD_rawQueue_eq_of_le {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ : ℕ) {a b i : ℕ}
    (hab : a ≤ b) (hi : i < (rawQueue hm T π x₀ r₀ a).length) :
    (rawQueue hm T π x₀ r₀ b).getD i ⟨0, hm⟩ =
      (rawQueue hm T π x₀ r₀ a).getD i ⟨0, hm⟩ := by
  induction hab with
  | refl => rfl
  | @step c hac ih =>
    have hic : i < (rawQueue hm T π x₀ r₀ c).length :=
      lt_of_lt_of_le hi (length_rawQueue_le_of_le hm T π x₀ r₀ hac)
    dsimp only [rawQueue]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hic]
    exact ih

private theorem mem_rawQueue_succ_of_mem_probePrefix {U m : ℕ} (hm : 0 < m) (T : Table U m)
    (π : Fin U → Equiv.Perm (Fin m)) (x₀ : Fin U) (r₀ a : ℕ) {j : Fin m}
    (hj : j ∈ probePrefix hm
      (π (keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩)))
      (missedProbes (otherOccupiedSlots T
        (keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩)))
        (π (keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩))))) :
    j ∈ rawQueue hm T π x₀ r₀ (a + 1) := by
  dsimp only [rawQueue]
  by_cases hmem : j ∈ rawQueue hm T π x₀ r₀ a
  · exact List.mem_append_left _ hmem
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨hj, by simpa using hmem⟩)

private theorem rawQueue_spec {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x₀ : Fin U} (hx₀ : x₀ ∈ insert u (Dictionary.dom s))
    (hx₀_le : extRank s rank u x₀ ≤ extRank s rank u u)
    {r₀ : ℕ} (hr₀_pos : 1 ≤ r₀) (hr₀_mp : r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀)) :
    ∀ b ≤ (partialDepSet T π (extRank s rank u) x₀ r₀).card,
      (rawQueue hm T π x₀ r₀ b).toFinset ⊆
        (partialDepSet T π (extRank s rank u) x₀ r₀).image (landingSlot hm T π) ∧
      min (b + 1) (partialDepSet T π (extRank s rank u) x₀ r₀).card ≤
        (rawQueue hm T π x₀ r₀ b).length := by
  classical
  set r_ext := extRank s rank u
  set W := partialDepSet T π r_ext x₀ r₀
  have hW_dom : W ⊆ Dictionary.dom s := fun z hz =>
    (Finset.mem_erase.mp (Finset.mem_erase.mp (partialDepSet_subset_erase hrep hx₀_le r₀ hz)).2).2
  have hcard_SW : (W.image (landingSlot hm T π)).card = W.card := by
    refine Finset.card_image_of_injOn fun y₁ hy₁ y₂ hy₂ heq =>
      landingSlot_injOn_dom hm hrep (hW_dom hy₁) (hW_dom hy₂) heq
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro hbw
    cases b with
    | zero =>
      refine ⟨?_, ?_⟩
      · dsimp only [rawQueue]
        rw [toFinset_probePrefix_eq_image_directBlockers hm hrep hrank u hx₀ hr₀_mp]
        refine Finset.image_subset_image fun y hy => ?_
        exact Finset.mem_biUnion.mpr ⟨y, hy, self_mem_depSet T π r_ext y⟩
      · dsimp only [rawQueue]
        rw [length_probePrefix]
        omega
    | succ c =>
      have hc_lt_w : c < W.card := hbw
      obtain ⟨hsub_c, hlen_c⟩ := ih c (Nat.lt_succ_self c) (le_of_lt hc_lt_w)
      have hc_len : c < (rawQueue hm T π x₀ r₀ c).length := by omega
      set q_c := rawQueue hm T π x₀ r₀ c
      set slot_c := q_c.getD c ⟨0, hm⟩
      set x_c := keyAt T x₀ slot_c
      have hslot_c_mem : slot_c ∈ q_c.toFinset := by
        rw [List.mem_toFinset]
        have hget : slot_c = q_c[c] := getD_eq_getElem_of_lt q_c ⟨0, hm⟩ hc_len
        rw [hget]
        exact List.getElem_mem hc_len
      obtain ⟨y_c, hy_c_W, hland_yc⟩ := Finset.mem_image.mp (hsub_c hslot_c_mem)
      have hxc_eq : x_c = y_c := by
        dsimp only [x_c]
        rw [← hland_yc]
        exact keyAt_landingSlot_of_mem_dom hm hrep x₀ (hW_dom hy_c_W)
      have hxc_W : x_c ∈ W := hxc_eq ▸ hy_c_W
      have hxc_dom : x_c ∈ Dictionary.dom s := hW_dom hxc_W
      have hdep_xc : depSet T π r_ext x_c ⊆ W :=
        (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x₀ r₀ hxc_W).2
      have hsub_succ : (rawQueue hm T π x₀ r₀ (c + 1)).toFinset ⊆
          W.image (landingSlot hm T π) := by
        intro j hj
        dsimp only [rawQueue] at hj
        rw [List.toFinset_append, Finset.mem_union] at hj
        rcases hj with hj_c | hj_new
        · exact hsub_c hj_c
        · rw [List.mem_toFinset] at hj_new
          have hj_pref : j ∈ (probePrefix hm (π x_c)
              (missedProbes (otherOccupiedSlots T x_c) (π x_c))).toFinset :=
            List.mem_toFinset.mpr (List.mem_of_mem_filter hj_new)
          rw [toFinset_probePrefix_eq_image_directBlockers hm hrep hrank u
            (Finset.mem_insert_of_mem hxc_dom) le_rfl] at hj_pref
          rcases Finset.mem_image.mp hj_pref with ⟨y, hy_dir, rfl⟩
          refine Finset.mem_image.mpr ⟨y, hdep_xc ?_, rfl⟩
          rw [depSet_eq]
          refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨y, ?_, self_mem_depSet _ _ _ y⟩)
          have hdir_eq : directBlockers T π r_ext x_c
              (missedProbes (otherOccupiedSlots T x_c) (π x_c)) =
              directBlockers T π r_ext x_c m := by
            ext z
            simp only [directBlockers, Finset.mem_filter, Finset.mem_univ, true_and]
            refine and_congr_right fun _ => exists_congr fun i => ?_
            exact ⟨fun ⟨_, h2, h3⟩ => ⟨i.isLt, h2, h3⟩, fun ⟨_, h2, h3⟩ => ⟨h2, h2, h3⟩⟩
          rwa [← hdir_eq]
      refine ⟨hsub_succ, ?_⟩
      by_contra hlt_succ
      have hlen_le_succ : q_c.length ≤ (rawQueue hm T π x₀ r₀ (c + 1)).length :=
        length_rawQueue_le_of_le hm T π x₀ r₀ (Nat.le_succ c)
      have hlen_eq : (rawQueue hm T π x₀ r₀ (c + 1)).length = c + 1 := by omega
      have hc1_lt_w : c + 1 < W.card := by omega
      set q' := rawQueue hm T π x₀ r₀ (c + 1)
      let C := W.filter fun y => landingSlot hm T π y ∈ q'.toFinset
      have hdir0_C : directBlockers T π r_ext x₀ r₀ ⊆ C := by
        intro y hy
        refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨y, hy, self_mem_depSet _ _ _ y⟩, ?_⟩
        have hmem0 : landingSlot hm T π y ∈ (rawQueue hm T π x₀ r₀ 0).toFinset := by
          dsimp only [rawQueue]
          rw [toFinset_probePrefix_eq_image_directBlockers hm hrep hrank u hx₀ hr₀_mp]
          exact Finset.mem_image_of_mem _ hy
        exact List.mem_toFinset.mpr
          (mem_rawQueue_of_le hm T π x₀ r₀ (Nat.zero_le (c + 1)) (List.mem_toFinset.mp hmem0))
      have hclosed_C : ∀ z ∈ C, directBlockers T π r_ext z m ⊆ C := by
        intro z hz y hy_dir
        rcases Finset.mem_filter.mp hz with ⟨hzW, hz_land⟩
        have hyW : y ∈ W := by
          refine (rank_lt_and_depSet_subset_of_mem_partialDepSet T π r_ext x₀ r₀ hzW).2 ?_
          rw [depSet_eq]
          exact Finset.mem_insert_of_mem
            (Finset.mem_biUnion.mpr ⟨y, hy_dir, self_mem_depSet _ _ _ y⟩)
        refine Finset.mem_filter.mpr ⟨hyW, ?_⟩
        obtain ⟨a, ha_lt, hqa⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hz_land)
        have ha_le_c : a ≤ c := by omega
        obtain ⟨_, hlen_a⟩ := ih a (by omega) (by omega)
        have ha_len : a < (rawQueue hm T π x₀ r₀ a).length := by omega
        have hget_a : (rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩ = landingSlot hm T π z := by
          rw [← getD_rawQueue_eq_of_le hm T π x₀ r₀ (Nat.le_succ_of_le ha_le_c) ha_len,
            getD_eq_getElem_of_lt q' ⟨0, hm⟩ ha_lt, hqa]
        have hkey_a : keyAt T x₀ ((rawQueue hm T π x₀ r₀ a).getD a ⟨0, hm⟩) = z := by
          rw [hget_a, keyAt_landingSlot_of_mem_dom hm hrep x₀ (hW_dom hzW)]
        have hy_pref : landingSlot hm T π y ∈
            probePrefix hm (π z) (missedProbes (otherOccupiedSlots T z) (π z)) := by
          rw [← List.mem_toFinset,
            toFinset_probePrefix_eq_image_directBlockers hm hrep hrank u
              (Finset.mem_insert_of_mem (hW_dom hzW)) le_rfl]
          refine Finset.mem_image.mpr ⟨y, ?_, rfl⟩
          rcases Finset.mem_filter.mp hy_dir with ⟨_, hlt_yz, i, _, hi_mp, hTi⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt_yz, i, hi_mp, hi_mp, hTi⟩
        have hy_a1 : landingSlot hm T π y ∈ rawQueue hm T π x₀ r₀ (a + 1) := by
          apply mem_rawQueue_succ_of_mem_probePrefix hm T π x₀ r₀ a
          rwa [hkey_a]
        exact List.mem_toFinset.mpr
          (mem_rawQueue_of_le hm T π x₀ r₀ (Nat.succ_le_succ ha_le_c) hy_a1)
      have hW_sub_C : W ⊆ C := by
        intro w hw
        simp only [W, partialDepSet, Finset.mem_biUnion] at hw
        rcases hw with ⟨y, hy_dir, hwy⟩
        exact depSet_subset_of_directBlockers_closed T π r_ext hclosed_C (hdir0_C hy_dir) hwy
      have hSW_sub_q' : W.image (landingSlot hm T π) ⊆ q'.toFinset := by
        intro j hj
        rcases Finset.mem_image.mp hj with ⟨y, hyW, rfl⟩
        exact (Finset.mem_filter.mp (hW_sub_C hyW)).2
      have hcard_le1 : W.card ≤ q'.toFinset.card :=
        hcard_SW ▸ Finset.card_le_card hSW_sub_q'
      have hcard_le2 : q'.toFinset.card ≤ q'.length := List.toFinset_card_le q'
      omega

/-- **BFS Spanning-Tree Witness Extraction ([SchmidtSiegel1990], Appendix A, Lemma A)**:
any partial dependency set `W = partialDepSet T π (extRank s rank u) x₀ r₀` with
`1 ≤ r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀)` yields a size-`W.card` BFS witness
`HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ W.card`. -/
private theorem hasBFSWitness_of_partialDepSet {U m : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : TableRep π s T) {rank : Fin U → ℕ}
    (hrank : ∀ w ∈ Dictionary.dom s, ∀ i : Fin m,
      i.val < missedProbes (otherOccupiedSlots T w) (π w) →
        ∃ y ∈ (Dictionary.dom s).erase w, ∃ vy : ℕ,
          T (π w i) = some (y, vy) ∧ rank y < rank w)
    (u : Fin U) {x₀ : Fin U} (hx₀ : x₀ ∈ insert u (Dictionary.dom s))
    (hx₀_le : extRank s rank u x₀ ≤ extRank s rank u u)
    {r₀ : ℕ} (hr₀_pos : 1 ≤ r₀) (hr₀_mp : r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀)) :
    HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀
      (partialDepSet T π (extRank s rank u) x₀ r₀).card := by
  classical
  have hspec := rawQueue_spec hm hrep hrank u hx₀ hx₀_le hr₀_pos hr₀_mp
  set r_ext := extRank s rank u
  set W := partialDepSet T π r_ext x₀ r₀
  set w := W.card
  change ∀ b ≤ w,
      (rawQueue hm T π x₀ r₀ b).toFinset ⊆ W.image (landingSlot hm T π) ∧
      min (b + 1) w ≤ (rawQueue hm T π x₀ r₀ b).length at hspec
  have hW_erase : W ⊆ ((Dictionary.dom s).erase u).erase x₀ :=
    partialDepSet_subset_erase hrep hx₀_le r₀
  have hW_dom : W ⊆ Dictionary.dom s := fun z hz =>
    (Finset.mem_erase.mp (Finset.mem_erase.mp (hW_erase hz)).2).2
  have hcard_SW : (W.image (landingSlot hm T π)).card = w :=
    Finset.card_image_of_injOn fun y₁ hy₁ y₂ hy₂ heq =>
      landingSlot_injOn_dom hm hrep (hW_dom hy₁) (hW_dom hy₂) heq
  let x : Fin w → Fin U := fun b =>
    keyAt T x₀ ((rawQueue hm T π x₀ r₀ b.val).getD b.val ⟨0, hm⟩)
  let h : Fin (w + 1) → ℕ := Fin.cases r₀ fun b : Fin w =>
    ((probePrefix hm (π (x b))
      (missedProbes (otherOccupiedSlots T (x b)) (π (x b)))).filter
        (· ∉ rawQueue hm T π x₀ r₀ b.val)).length
  have hxb_spec : ∀ b : Fin w,
      x b ∈ W ∧
      landingSlot hm T π (x b) = (rawQueue hm T π x₀ r₀ b.val).getD b.val ⟨0, hm⟩ ∧
      missedProbes (otherOccupiedSlots T (x b)) (π (x b)) < w := by
    intro b
    obtain ⟨hsub_b, hlen_b⟩ := hspec b.val (le_of_lt b.isLt)
    have hb_len : b.val < (rawQueue hm T π x₀ r₀ b.val).length := by
      have := b.isLt
      omega
    have hslot_mem : (rawQueue hm T π x₀ r₀ b.val).getD b.val ⟨0, hm⟩ ∈
        (rawQueue hm T π x₀ r₀ b.val).toFinset := by
      rw [List.mem_toFinset, getD_eq_getElem_of_lt _ _ hb_len]
      exact List.getElem_mem hb_len
    obtain ⟨y, hyW, hland_y⟩ := Finset.mem_image.mp (hsub_b hslot_mem)
    have hxb_eq : x b = y := by
      dsimp only [x]
      rw [← hland_y]
      exact keyAt_landingSlot_of_mem_dom hm hrep x₀ (hW_dom hyW)
    have hxb_W : x b ∈ W := hxb_eq ▸ hyW
    refine ⟨hxb_W, by rw [hxb_eq, hland_y],
      missedProbes_lt_card_of_mem_partialDepSet hrep hrank u x₀ r₀ hxb_W⟩
  have hqueue_eq : ∀ b ≤ w,
      bfsQueue hm π x₀ w h x b = rawQueue hm T π x₀ r₀ b ∧
      (rawQueue hm T π x₀ r₀ b).length =
        h 0 + ∑ i ∈ Finset.range b,
          if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0 := by
    intro b hbw
    induction b with
    | zero =>
      simp [bfsQueue, rawQueue, h, length_probePrefix]
    | succ b ih =>
      have hb_lt : b < w := Nat.lt_of_succ_le hbw
      obtain ⟨ih_q, ih_len⟩ := ih (le_of_lt hb_lt)
      let b' : Fin w := ⟨b, hb_lt⟩
      have hkb_lt : missedProbes (otherOccupiedSlots T (x b')) (π (x b')) < w :=
        (hxb_spec b').2.2
      have hhb_eq : h ⟨b + 1, Nat.succ_lt_succ hb_lt⟩ =
          ((probePrefix hm (π (x b'))
            (missedProbes (otherOccupiedSlots T (x b')) (π (x b')))).filter
              (· ∉ rawQueue hm T π x₀ r₀ b)).length :=
        rfl
      have htake := take_filter_probePrefix_eq hm (π (x b')) (le_of_lt hkb_lt)
        (· ∉ rawQueue hm T π x₀ r₀ b) hhb_eq.symm
      refine ⟨?_, ?_⟩
      · simp only [bfsQueue, hb_lt, ↓reduceDIte, ih_q]
        dsimp only [rawQueue]
        rw [htake]
      · dsimp only [rawQueue]
        rw [List.length_append, Finset.sum_range_succ, ih_len]
        simp only [hb_lt, ↓reduceDIte, hhb_eq]
        dsimp only [x, b']
        rw [Nat.add_assoc]
  have hlen_w : (rawQueue hm T π x₀ r₀ w).length = w := by
    obtain ⟨hsub_w, hlen_w_ge⟩ := hspec w le_rfl
    have hr₀_m : r₀ ≤ m := hr₀_mp.trans (missedProbes_le _ _)
    have hnodup_w : (rawQueue hm T π x₀ r₀ w).Nodup := nodup_rawQueue hm T π x₀ hr₀_m w
    have hcard_eq : (rawQueue hm T π x₀ r₀ w).toFinset.card =
        (rawQueue hm T π x₀ r₀ w).length := List.toFinset_card_of_nodup hnodup_w
    have hle_SW : (rawQueue hm T π x₀ r₀ w).toFinset.card ≤ w :=
      (Finset.card_le_card hsub_w).trans_eq hcard_SW
    omega
  have hsum_h : ∑ a : Fin (w + 1), h a = w := by
    rw [← sum_fin_succ_eq h, ← (hqueue_eq w le_rfl).2, hlen_w]
  refine ⟨h, hr₀_pos, hsum_h, x, ?_, fun b => hW_erase (hxb_spec b).1, fun b => ?_⟩
  · intro b₁ b₂ heq
    have hland : landingSlot hm T π (x b₁) = landingSlot hm T π (x b₂) := congrArg _ heq
    rw [(hxb_spec b₁).2.1, (hxb_spec b₂).2.1] at hland
    obtain ⟨_, hlen_b1⟩ := hspec b₁.val (le_of_lt b₁.isLt)
    obtain ⟨_, hlen_b2⟩ := hspec b₂.val (le_of_lt b₂.isLt)
    have hb1_len : b₁.val < (rawQueue hm T π x₀ r₀ b₁.val).length := by
      have := b₁.isLt; omega
    have hb2_len : b₂.val < (rawQueue hm T π x₀ r₀ b₂.val).length := by
      have := b₂.isLt; omega
    rw [← getD_rawQueue_eq_of_le hm T π x₀ r₀ (le_of_lt b₁.isLt) hb1_len,
      ← getD_rawQueue_eq_of_le hm T π x₀ r₀ (le_of_lt b₂.isLt) hb2_len] at hland
    have hb1_w : b₁.val < (rawQueue hm T π x₀ r₀ w).length := hlen_w.symm ▸ b₁.isLt
    have hb2_w : b₂.val < (rawQueue hm T π x₀ r₀ w).length := hlen_w.symm ▸ b₂.isLt
    rw [getD_eq_getElem_of_lt _ _ hb1_w, getD_eq_getElem_of_lt _ _ hb2_w] at hland
    have hr₀_m : r₀ ≤ m := hr₀_mp.trans (missedProbes_le _ _)
    have hnodup_w := nodup_rawQueue hm T π x₀ hr₀_m w
    exact Fin.ext (hnodup_w.getElem_inj_iff.mp hland)
  · dsimp only [bfsStepEvent]
    rw [(hqueue_eq b.val (le_of_lt b.isLt)).1]
    set q := rawQueue hm T π x₀ r₀ b.val
    set k_b := missedProbes (otherOccupiedSlots T (x b)) (π (x b))
    have hkb_lt : k_b < w := (hxb_spec b).2.2
    have hslot_eq : probeAt hm (π (x b)) k_b = q.getD b.val ⟨0, hm⟩ :=
      (hxb_spec b).2.1
    have hhb_eq : h ⟨b.val + 1, Nat.succ_lt_succ b.isLt⟩ =
        ((probePrefix hm (π (x b)) k_b).filter (· ∉ q)).length :=
      rfl
    have hhb_le : h ⟨b.val + 1, Nat.succ_lt_succ b.isLt⟩ ≤ k_b := by
      rw [hhb_eq]
      exact (List.length_filter_le _ _).trans (by simp [length_probePrefix])
    rcases eq_or_lt_of_le hhb_le with hhb_eq_kb | hhb_lt_kb
    · left
      rw [hhb_eq_kb, hslot_eq]
    · right
      have hlen_lt : ((probePrefix hm (π (x b)) k_b).filter (· ∉ q)).length <
          (probePrefix hm (π (x b)) k_b).length := by
        rw [← hhb_eq, length_probePrefix]
        exact hhb_lt_kb
      have hnot_all : ¬ ∀ j ∈ probePrefix hm (π (x b)) k_b, decide (j ∉ q) = true := by
        intro hall
        rw [List.filter_eq_self.mpr hall] at hlen_lt
        exact lt_irrefl _ hlen_lt
      push Not at hnot_all
      rcases hnot_all with ⟨j, hj_pref, hj_q⟩
      have hj_mem_q : j ∈ q := by simpa using hj_q
      simp only [probePrefix, List.mem_map, List.mem_range] at hj_pref
      rcases hj_pref with ⟨j₁, hj₁_lt, rfl⟩
      exact ⟨⟨k_b, hkb_lt⟩, ⟨j₁, lt_trans hj₁_lt hkb_lt⟩, hj₁_lt,
        List.mem_toFinset.mpr hj_mem_q, hslot_eq⟩

open scoped Classical in
/-- **Pointwise Probe-Count Decomposition via Minimal Overflow Dichotomy and BFS Witnesses**:
for any `OrderedTableRep π s T` with `(Dictionary.dom s).card ≤ n_max`, query key `u : Fin U`,
and cutoff `L ≥ 1`, `probeCount T u (π u)` is bounded by `1` plus the normal-regime witness sum
over `w ∈ [1, L)` plus `n_max` times the overflow-regime witness sum over
`x₀ ∈ insert u (Dictionary.dom s)` and `w ∈ [L, 2 * L)`. -/
private theorem probeCount_le_sum_hasBFSWitness {U m n_max : ℕ} (hm : 0 < m)
    {π : Fin U → Equiv.Perm (Fin m)} {s : Dictionary.State U} {T : Table U m}
    (hrep : OrderedTableRep π s T) (hdom : (Dictionary.dom s).card ≤ n_max)
    (u : Fin U) {L : ℕ} (hL : 1 ≤ L) :
    probeCount T u (π u) ≤
      1 +
      (∑ w ∈ Finset.Ico 1 L,
        if HasBFSWitness hm π ((Dictionary.dom s).erase u) u w then w else 0) +
      n_max *
        (∑ x₀ ∈ insert u (Dictionary.dom s),
          ∑ w ∈ Finset.Ico L (2 * L),
            if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ w then 1 else 0) := by
  have hpc_eq : probeCount T u (π u) = 1 + missedProbes (otherOccupiedSlots T u) (π u) := rfl
  set k_u := missedProbes (otherOccupiedSlots T u) (π u)
  rcases Nat.eq_zero_or_pos k_u with hk0 | hk_pos
  · rw [hpc_eq, hk0]
    omega
  · obtain ⟨rank, hrank⟩ := hrep.exists_rank
    rcases dichotomy_partialDepSet hrep.toTableRep hrank u hL with ⟨hku_lt, hcard_lt⟩ | hov
    · set w := (partialDepSet T π (extRank s rank u) u k_u).card
      have hku_le_w : k_u ≤ w :=
        card_partialDepSet_ge hrep.toTableRep hrank u (Finset.mem_insert_self u _) le_rfl
      have hw_mem : w ∈ Finset.Ico 1 L := Finset.mem_Ico.mpr ⟨by omega, hcard_lt⟩
      have hwit : HasBFSWitness hm π ((Dictionary.dom s).erase u) u w :=
        hasBFSWitness_of_partialDepSet hm hrep.toTableRep hrank u
          (Finset.mem_insert_self u _) le_rfl hk_pos le_rfl
      have hle_sum : w ≤ ∑ w' ∈ Finset.Ico 1 L,
          if HasBFSWitness hm π ((Dictionary.dom s).erase u) u w' then w' else 0 := by
        have hsingle := Finset.single_le_sum
          (f := fun w' => if HasBFSWitness hm π ((Dictionary.dom s).erase u) u w' then w' else 0)
          (fun _ _ => Nat.zero_le _) hw_mem
        simpa [hwit] using hsingle
      rw [hpc_eq]
      omega
    · rcases hov with ⟨x₀, hx₀_ins, hx₀_le, r₀, hr₀_pos, hr₀_le_min, hw_ge_L, hw_lt_2L⟩
      have hr₀_mp : r₀ ≤ missedProbes (otherOccupiedSlots T x₀) (π x₀) :=
        hr₀_le_min.trans (Nat.min_le_left _ _)
      set w := (partialDepSet T π (extRank s rank u) x₀ r₀).card
      have hw_mem : w ∈ Finset.Ico L (2 * L) := Finset.mem_Ico.mpr ⟨hw_ge_L, hw_lt_2L⟩
      have hwit : HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ w :=
        hasBFSWitness_of_partialDepSet hm hrep.toTableRep hrank u hx₀_ins hx₀_le hr₀_pos hr₀_mp
      have hle_inner : 1 ≤ ∑ w' ∈ Finset.Ico L (2 * L),
          if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ w' then 1 else 0 := by
        have hsingle := Finset.single_le_sum
          (f := fun w' => if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀ w' then 1 else 0)
          (fun _ _ => Nat.zero_le _) hw_mem
        simpa [hwit] using hsingle
      have hle_outer : 1 ≤ ∑ x₀' ∈ insert u (Dictionary.dom s),
          ∑ w' ∈ Finset.Ico L (2 * L),
            if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀' w' then 1 else 0 := by
        refine hle_inner.trans (Finset.single_le_sum
          (f := fun x₀' => ∑ w' ∈ Finset.Ico L (2 * L),
            if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀' w' then 1 else 0)
          (fun _ _ => Nat.zero_le _) hx₀_ins)
      have hmul : n_max ≤ n_max * ∑ x₀' ∈ insert u (Dictionary.dom s),
          ∑ w' ∈ Finset.Ico L (2 * L),
            if HasBFSWitness hm π ((Dictionary.dom s).erase u) x₀' w' then 1 else 0 := by
        simpa using Nat.mul_le_mul_left n_max hle_outer
      have hpc_le := probeCount_le_add_one hrep.toTableRep hdom u
      omega

/-- Single-step fiber of hash pairs `(p, s) ∈ Fin (2 ^ M) × Fin (2 ^ (M - 1))` satisfying the
BFS step constraint at `slot_b` with degree `d` against queue `q`. -/
private noncomputable def stepFiber (M w : ℕ) (q : List (Fin (2 ^ M)))
    (slot_b : Fin (2 ^ M)) (d : ℕ) :
    Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
  Finset.univ.filter fun ps =>
    let σ := oddStridePermOfPair M ps.1 ps.2
    let hm := Nat.two_pow_pos M
    probeAt hm σ d = slot_b ∨
      ∃ k_b : Fin w, ∃ j₁ : Fin w,
        j₁.val < k_b.val ∧
        probeAt hm σ j₁.val ∈ q.toFinset ∧
        probeAt hm σ k_b.val = slot_b

private theorem card_filter_probeAt_eq_le_one (M : ℕ) (s : Fin (2 ^ (M - 1)))
    (idx : ℕ) (target : Fin (2 ^ M)) :
    (Finset.univ.filter fun p : Fin (2 ^ M) =>
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M p s) idx = target).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun p₁ hp₁ p₂ hp₂ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, probeAt, oddStridePermOfPair_apply,
    oddStrideSeq, Fin.ext_iff] at hp₁ hp₂
  have hmod : p₁.val + idx % 2 ^ M * (2 * s.val + 1) ≡
      p₂.val + idx % 2 ^ M * (2 * s.val + 1) [MOD 2 ^ M] :=
    hp₁.trans hp₂.symm
  have hp_mod : p₁.val ≡ p₂.val [MOD 2 ^ M] :=
    Nat.ModEq.add_right_cancel' (idx % 2 ^ M * (2 * s.val + 1)) hmod
  rw [Nat.ModEq, Nat.mod_eq_of_lt p₁.isLt, Nat.mod_eq_of_lt p₂.isLt] at hp_mod
  exact Fin.ext hp_mod

private theorem card_filter_two_probes_eq_le (M : ℕ) {j₁ k_b : ℕ} (hjk : j₁ < k_b)
    (hkb : k_b < 2 ^ M) (slot₁ slot₂ : Fin (2 ^ M)) :
    (Finset.univ.filter fun ps : Fin (2 ^ M) × Fin (2 ^ (M - 1)) =>
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) j₁ = slot₁ ∧
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) k_b = slot₂).card ≤
        k_b - j₁ := by
  set Δ := k_b - j₁
  set r := (slot₂.val + 2 ^ M - slot₁.val) % 2 ^ M
  let S_stride := (Finset.univ : Finset (Fin (2 ^ (M - 1)))).filter fun s =>
    (Δ * (2 * s.val + 1)) % 2 ^ M = r
  have hsub : (Finset.univ.filter fun ps : Fin (2 ^ M) × Fin (2 ^ (M - 1)) =>
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) j₁ = slot₁ ∧
      probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M ps.1 ps.2) k_b = slot₂) ⊆
      S_stride.biUnion (fun s =>
        (Finset.univ.filter fun p : Fin (2 ^ M) =>
          probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M p s) k_b = slot₂).map
            ⟨fun p => (p, s), fun _ _ h => (Prod.mk.inj h).1⟩) := by
    intro ⟨p, s⟩ hps
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hps
    have hj₁_lt : j₁ < 2 ^ M := lt_trans hjk hkb
    have h1 : (p.val + j₁ * (2 * s.val + 1)) % 2 ^ M = slot₁.val := by
      simpa [probeAt_eq_of_lt (Nat.two_pow_pos M) _ hj₁_lt, oddStrideSeq, Fin.ext_iff] using hps.1
    have h2 : (p.val + k_b * (2 * s.val + 1)) % 2 ^ M = slot₂.val := by
      simpa [probeAt_eq_of_lt (Nat.two_pow_pos M) _ hkb, oddStrideSeq, Fin.ext_iff] using hps.2
    have hsum_eq : p.val + k_b * (2 * s.val + 1) =
        (p.val + j₁ * (2 * s.val + 1)) + Δ * (2 * s.val + 1) := by
      have : k_b = j₁ + Δ := by omega
      rw [this, Nat.add_mul, Nat.add_assoc]
    have hmod_slot₂ : (slot₁.val + Δ * (2 * s.val + 1)) % 2 ^ M = slot₂.val := by
      rw [← h1, Nat.mod_add_mod, ← hsum_eq, h2]
    have hmod_r : (Δ * (2 * s.val + 1)) % 2 ^ M = r := by
      have hcongr : ((slot₁.val + Δ * (2 * s.val + 1)) + (2 ^ M - slot₁.val)) % 2 ^ M =
          (slot₂.val + (2 ^ M - slot₁.val)) % 2 ^ M := by
        rw [← Nat.mod_add_mod, hmod_slot₂]
      have h1_lt : slot₁.val ≤ 2 ^ M := le_of_lt slot₁.isLt
      have hlhs : (slot₁.val + Δ * (2 * s.val + 1)) + (2 ^ M - slot₁.val) =
          Δ * (2 * s.val + 1) + 2 ^ M := by omega
      have hrhs : slot₂.val + (2 ^ M - slot₁.val) = slot₂.val + 2 ^ M - slot₁.val := by omega
      rw [hlhs, hrhs, Nat.add_mod_right] at hcongr
      exact hcongr
    refine Finset.mem_biUnion.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hmod_r⟩, ?_⟩
    exact Finset.mem_map.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hps.2⟩, rfl⟩
  calc
    _ ≤ (S_stride.biUnion _).card := Finset.card_le_card hsub
    _ ≤ ∑ s ∈ S_stride,
          ((Finset.univ.filter fun p : Fin (2 ^ M) =>
            probeAt (Nat.two_pow_pos M) (oddStridePermOfPair M p s) k_b = slot₂).map _).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _s ∈ S_stride, 1 := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [Finset.card_map]
        exact card_filter_probeAt_eq_le_one M s k_b slot₂
    _ = S_stride.card := by simp
    _ ≤ Δ := Nat.card_odd_mul_mod_eq_le M Δ r (by omega)

/-- **Single-Step Fiber Bound**: for any queue `q` with `q.toFinset.card ≤ w` and `w ≤ 2 ^ M`,
`(stepFiber M w q slot_b d).card ≤ 2 ^ (M - 1) + w ^ 4`. -/
private theorem card_stepFiber_le (M : ℕ) {w : ℕ} (hw : w ≤ 2 ^ M) (q : List (Fin (2 ^ M)))
    (hq : q.toFinset.card ≤ w) (slot_b : Fin (2 ^ M)) (d : ℕ) :
    (stepFiber M w q slot_b d).card ≤ 2 ^ (M - 1) + w ^ 4 := by
  classical
  let hm := Nat.two_pow_pos M
  let F₁ : Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
    Finset.univ.filter fun ps =>
      probeAt hm (oddStridePermOfPair M ps.1 ps.2) d = slot_b
  let F₂ : Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
    Finset.univ.filter fun ps =>
      ∃ k_b : Fin w, ∃ j₁ : Fin w,
        j₁.val < k_b.val ∧
        probeAt hm (oddStridePermOfPair M ps.1 ps.2) j₁.val ∈ q.toFinset ∧
        probeAt hm (oddStridePermOfPair M ps.1 ps.2) k_b.val = slot_b
  have hsub_u : stepFiber M w q slot_b d ⊆ F₁ ∪ F₂ := by
    intro ps hps
    simp only [stepFiber, F₁, F₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and] at hps ⊢
    exact hps
  have hF₁ : F₁.card ≤ 2 ^ (M - 1) := by
    have hsub₁ : F₁ ⊆ (Finset.univ : Finset (Fin (2 ^ (M - 1)))).biUnion fun s =>
        (Finset.univ.filter fun p : Fin (2 ^ M) =>
          probeAt hm (oddStridePermOfPair M p s) d = slot_b).map
            ⟨fun p => (p, s), fun _ _ h => (Prod.mk.inj h).1⟩ := by
      intro ⟨p, s⟩ hps
      simp only [F₁, Finset.mem_filter, Finset.mem_univ, true_and] at hps
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ s,
        Finset.mem_map.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hps⟩, rfl⟩⟩
    calc
      F₁.card ≤ _ := Finset.card_le_card hsub₁
      _ ≤ ∑ s : Fin (2 ^ (M - 1)),
            ((Finset.univ.filter fun p : Fin (2 ^ M) =>
              probeAt hm (oddStridePermOfPair M p s) d = slot_b).map _).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _s : Fin (2 ^ (M - 1)), 1 := by
          refine Finset.sum_le_sum fun s _ => ?_
          rw [Finset.card_map]
          exact card_filter_probeAt_eq_le_one M s d slot_b
      _ = 2 ^ (M - 1) := by simp
  have hF₂ : F₂.card ≤ w ^ 4 := by
    let P (k_b j₁ : Fin w) (slot₁ : Fin (2 ^ M)) :
        Finset (Fin (2 ^ M) × Fin (2 ^ (M - 1))) :=
      if j₁.val < k_b.val then
        Finset.univ.filter fun ps =>
          probeAt hm (oddStridePermOfPair M ps.1 ps.2) j₁.val = slot₁ ∧
          probeAt hm (oddStridePermOfPair M ps.1 ps.2) k_b.val = slot_b
      else ∅
    have hsub₂ : F₂ ⊆ (Finset.univ : Finset (Fin w)).biUnion fun k_b =>
        (Finset.univ : Finset (Fin w)).biUnion fun j₁ =>
          q.toFinset.biUnion fun slot₁ => P k_b j₁ slot₁ := by
      intro ps hps
      simp only [F₂, Finset.mem_filter, Finset.mem_univ, true_and] at hps
      rcases hps with ⟨k_b, j₁, hlt, hmem_q, heq_b⟩
      refine Finset.mem_biUnion.mpr ⟨k_b, Finset.mem_univ k_b,
        Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ j₁,
          Finset.mem_biUnion.mpr ⟨_, hmem_q, ?_⟩⟩⟩
      simp [P, Fin.lt_def.mpr hlt, heq_b]
    have hP_le : ∀ (k_b j₁ : Fin w) (slot₁ : Fin (2 ^ M)), (P k_b j₁ slot₁).card ≤ w := by
      intro k_b j₁ slot₁
      dsimp only [P]
      split_ifs with hlt
      · refine (card_filter_two_probes_eq_le M hlt (lt_of_lt_of_le k_b.isLt hw)
          slot₁ slot_b).trans ?_
        have := k_b.isLt
        omega
      · simp
    calc
      F₂.card ≤ _ := Finset.card_le_card hsub₂
      _ ≤ ∑ k_b : Fin w, ∑ j₁ : Fin w, ∑ slot₁ ∈ q.toFinset, (P k_b j₁ slot₁).card := by
          refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun k_b _ => ?_)
          exact Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j₁ _ => Finset.card_biUnion_le)
      _ ≤ ∑ _k_b : Fin w, ∑ _j₁ : Fin w, ∑ _slot₁ ∈ q.toFinset, w := by
          refine Finset.sum_le_sum fun k_b _ =>
            Finset.sum_le_sum fun j₁ _ =>
              Finset.sum_le_sum fun slot₁ _ => hP_le k_b j₁ slot₁
      _ = w * (w * (q.toFinset.card * w)) := by simp
      _ ≤ w * (w * (w * w)) := by gcongr
      _ = w ^ 4 := by ring
  calc
    (stepFiber M w q slot_b d).card ≤ (F₁ ∪ F₂).card := Finset.card_le_card hsub_u
    _ ≤ F₁.card + F₂.card := Finset.card_union_le F₁ F₂
    _ ≤ 2 ^ (M - 1) + w ^ 4 := Nat.add_le_add hF₁ hF₂

/-- Queue of discovered slots at step `b` for a prefix tuple
`ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))`. -/
private noncomputable def tupleQueue (M w : ℕ) (h : Fin (w + 1) → ℕ) :
    (b : ℕ) → b ≤ w → (Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) → List (Fin (2 ^ M))
  | 0, _, ps =>
      let hm := Nat.two_pow_pos M
      let σ₀ := oddStridePermOfPair M (ps 0).1 (ps 0).2
      probePrefix hm σ₀ (h 0)
  | b + 1, hb, ps =>
      let hm := Nat.two_pow_pos M
      let q := tupleQueue M w h b (Nat.le_of_succ_le hb) (Fin.init ps)
      let p_last := ps (Fin.last (b + 1))
      let σ := oddStridePermOfPair M p_last.1 p_last.2
      q ++ ((probePrefix hm σ w).filter (· ∉ q)).take
        (h ⟨b + 1, Nat.succ_lt_succ hb⟩)

private theorem length_tupleQueue_le (M w : ℕ) (h : Fin (w + 1) → ℕ) :
    ∀ (b : ℕ) (hb : b ≤ w) (ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))),
      (tupleQueue M w h b hb ps).length ≤
        h 0 + ∑ i ∈ Finset.range b,
          if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0
  | 0, _, ps => by simp [tupleQueue, length_probePrefix]
  | b + 1, hbw, ps => by
      have hb : b < w := Nat.lt_of_succ_le hbw
      have ih := length_tupleQueue_le M w h b (le_of_lt hb) (Fin.init ps)
      simp only [tupleQueue, List.length_append, Finset.sum_range_succ, hb, ↓reduceDIte]
      have htake := List.length_take_le (h ⟨b + 1, Nat.succ_lt_succ hb⟩)
        ((probePrefix (Nat.two_pow_pos M)
          (oddStridePermOfPair M (ps (Fin.last (b + 1))).1 (ps (Fin.last (b + 1))).2) w).filter
            (· ∉ tupleQueue M w h b (le_of_lt hb) (Fin.init ps)))
      omega

private theorem card_toFinset_tupleQueue_le (M w : ℕ) (h : Fin (w + 1) → ℕ)
    (hsum : ∑ a : Fin (w + 1), h a = w) {b : ℕ} (hb : b ≤ w)
    (ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) :
    (tupleQueue M w h b hb ps).toFinset.card ≤ w := by
  have h1 := List.toFinset_card_le (tupleQueue M w h b hb ps)
  have h2 := length_tupleQueue_le M w h b hb ps
  have hsub : ∑ i ∈ Finset.range b,
      (if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0) ≤
      ∑ i ∈ Finset.range w,
        (if hi : i < w then h ⟨i + 1, Nat.succ_lt_succ hi⟩ else 0) :=
    Finset.sum_le_sum_of_subset (Finset.range_mono hb)
  have h3 := sum_fin_succ_eq h
  omega

/-- Prefix tuples `ps : Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))` satisfying the first `b`
BFS step constraints. -/
private noncomputable def validTuples (M w : ℕ) (h : Fin (w + 1) → ℕ) :
    (b : ℕ) → b ≤ w → Finset (Fin (b + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)))
  | 0, _ => Finset.univ
  | b + 1, hb =>
      (validTuples M w h b (Nat.le_of_succ_le hb)).biUnion fun ps =>
        let q := tupleQueue M w h b (Nat.le_of_succ_le hb) ps
        let slot_b := q.getD b ⟨0, Nat.two_pow_pos M⟩
        let d_b := h ⟨b + 1, Nat.succ_lt_succ hb⟩
        (stepFiber M w q slot_b d_b).map
          ⟨fun p_last => Fin.snoc ps p_last, fun p₁ p₂ hp => by
            have := congrFun hp (Fin.last (b + 1))
            simpa [Fin.snoc_last] using this⟩

private theorem card_validTuples_le (M : ℕ) {w : ℕ} (hw : w ≤ 2 ^ M)
    (h : Fin (w + 1) → ℕ) (hsum : (∑ a : Fin (w + 1), h a) = w) :
    ∀ (b : ℕ) (hb : b ≤ w),
      (validTuples M w h b hb).card ≤
        (2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ b
  | 0, _ => by
      simp [validTuples, Fintype.card_pi]
  | b + 1, hb => by
      have ih := card_validTuples_le M hw h hsum b (Nat.le_of_succ_le hb)
      have hbi : (validTuples M w h (b + 1) hb).card ≤
          ∑ ps ∈ validTuples M w h b (Nat.le_of_succ_le hb),
            (2 ^ (M - 1) + w ^ 4) := by
        dsimp only [validTuples]
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ps _ => ?_)
        rw [Finset.card_map]
        exact card_stepFiber_le M hw _
          (card_toFinset_tupleQueue_le M w h hsum (Nat.le_of_succ_le hb) ps) _ _
      calc
        (validTuples M w h (b + 1) hb).card ≤
            (validTuples M w h b (Nat.le_of_succ_le hb)).card * (2 ^ (M - 1) + w ^ 4) := by
          simpa using hbi
        _ ≤ ((2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ b) * (2 ^ (M - 1) + w ^ 4) :=
          Nat.mul_le_mul_right _ ih
        _ = (2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ (b + 1) := by
          ring

private def restrictTuple {α : Type*} {w : ℕ} (f : Fin (w + 1) → α) (b : ℕ) (hb : b ≤ w) :
    Fin (b + 1) → α :=
  fun i => f ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hb)⟩

private theorem init_restrictTuple {α : Type*} {w : ℕ} (f : Fin (w + 1) → α) (b : ℕ)
    (hb : b + 1 ≤ w) :
    Fin.init (restrictTuple f (b + 1) hb) = restrictTuple f b (Nat.le_of_succ_le hb) :=
  rfl

private theorem snoc_restrictTuple {α : Type*} {w : ℕ} (f : Fin (w + 1) → α) (b : ℕ)
    (hb : b + 1 ≤ w) :
    Fin.snoc (restrictTuple f b (Nat.le_of_succ_le hb))
      (f ⟨b + 1, Nat.succ_lt_succ hb⟩) = restrictTuple f (b + 1) hb := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    rfl
  · simp [Fin.snoc_castSucc, restrictTuple]

private theorem tupleQueue_restrictTuple_eq_bfsQueue {U M w : ℕ}
    (x₀ : Fin U) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U)
    (p : Fin U → Fin (2 ^ M)) (s : Fin U → Fin (2 ^ (M - 1))) :
    let xExt : Fin (w + 1) → Fin U := Fin.cases x₀ x
    let f : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)) := fun a => (p (xExt a), s (xExt a))
    let π : Fin U → Equiv.Perm (Fin (2 ^ M)) := fun u => oddStridePermOfPair M (p u) (s u)
    ∀ (b : ℕ) (hb : b ≤ w),
      tupleQueue M w h b hb (restrictTuple f b hb) =
        bfsQueue (Nat.two_pow_pos M) π x₀ w h x b := by
  intro xExt f π b hb
  induction b with
  | zero =>
      rfl
  | succ b ih =>
      have hbw : b < w := Nat.lt_of_succ_le hb
      have ih' := ih (le_of_lt hbw)
      have hlast : restrictTuple f (b + 1) hb (Fin.last (b + 1)) =
          (p (x ⟨b, hbw⟩), s (x ⟨b, hbw⟩)) := rfl
      simp only [tupleQueue, init_restrictTuple, ih', hlast, bfsQueue, hbw, ↓reduceDIte]
      rfl

private theorem mem_validTuples_of_bfsStepEvent {U M w : ℕ}
    (x₀ : Fin U) (h : Fin (w + 1) → ℕ) (x : Fin w → Fin U)
    (p : Fin U → Fin (2 ^ M)) (s : Fin U → Fin (2 ^ (M - 1)))
    (hev : ∀ b : Fin w,
      bfsStepEvent (Nat.two_pow_pos M) (fun u => oddStridePermOfPair M (p u) (s u)) x₀ w h x b) :
    let xExt : Fin (w + 1) → Fin U := Fin.cases x₀ x
    let f : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)) := fun a => (p (xExt a), s (xExt a))
    ∀ (b : ℕ) (hb : b ≤ w),
      restrictTuple f b hb ∈ validTuples M w h b hb := by
  intro xExt f b hb
  induction b with
  | zero =>
      exact Finset.mem_univ _
  | succ b ih =>
      have hbw : b < w := Nat.lt_of_succ_le hb
      dsimp only [validTuples]
      refine Finset.mem_biUnion.mpr ⟨restrictTuple f b (le_of_lt hbw),
        ih (le_of_lt hbw), ?_⟩
      refine Finset.mem_map.mpr ⟨f ⟨b + 1, Nat.succ_lt_succ hbw⟩, ?_,
        snoc_restrictTuple f b hb⟩
      have hq_eq := tupleQueue_restrictTuple_eq_bfsQueue x₀ h x p s b (le_of_lt hbw)
      have hev_b := hev ⟨b, hbw⟩
      dsimp only [bfsStepEvent] at hev_b
      rw [← hq_eq] at hev_b
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev_b⟩

private theorem injective_fin_cases {α : Type*} {w : ℕ} {x₀ : α} {x : Fin w → α}
    (hx : Function.Injective x) (hne : ∀ b : Fin w, x b ≠ x₀) :
    Function.Injective (Fin.cases x₀ x : Fin (w + 1) → α) := by
  intro i j
  refine Fin.cases ?_ (fun i' => ?_) i <;> refine Fin.cases ?_ (fun j' => ?_) j <;> intro hij
  · rfl
  · exact False.elim (hne j' hij.symm)
  · exact False.elim (hne i' hij)
  · exact congrArg Fin.succ (hx hij)

private theorem card_filter_eq_mul_pow_of_isKWiseIndependentHash
    {Θ Y : Type*} [Fintype Θ] [Fintype Y] [DecidableEq Y] [Nonempty Y]
    {k w : ℕ} {h : Θ → Fin (w + 1) → Y}
    (hh : Cslib.Probability.IsKWiseIndependentHash k h) (hw : w + 1 ≤ k)
    (y : Fin (w + 1) → Y) :
    (Finset.univ.filter fun θ : Θ => h θ = y).card * Fintype.card Y ^ (w + 1) =
      Fintype.card Θ := by
  have : Nonempty Θ := hh.nonempty
  have hY_pos : 0 < Fintype.card Y := Fintype.card_pos
  have hΘ_pos : 0 < Fintype.card Θ := Fintype.card_pos
  let T : Finset (Fin (w + 1)) := Finset.univ
  have hT : T.card ≤ k := by simpa [T] using hw
  have hdens := hh.dens_filter_restrict_eq hT (fun a => y a.1)
  have hset : (Finset.univ.filter fun θ : Θ => T.restrict (h θ) = fun a => y a.1) =
      Finset.univ.filter fun θ : Θ => h θ = y := by
    ext θ
    simp [T, funext_iff, Finset.restrict]
  rw [hset, Finset.dens_eq_card_div_card] at hdens
  have hT_card : T.card = w + 1 := by simp [T]
  rw [hT_card] at hdens
  have hY_ne : ((Fintype.card Y : ℚ≥0) ^ (w + 1)) ≠ 0 := by positivity
  have hΘ_ne : (Fintype.card Θ : ℚ≥0) ≠ 0 := by positivity
  have hq : ((Finset.univ.filter fun θ : Θ => h θ = y).card : ℚ≥0) *
      (Fintype.card Y : ℚ≥0) ^ (w + 1) = (Fintype.card Θ : ℚ≥0) := by
    rw [div_eq_iff hΘ_ne] at hdens
    calc
      ((Finset.univ.filter fun θ : Θ => h θ = y).card : ℚ≥0) *
          (Fintype.card Y : ℚ≥0) ^ (w + 1)
        = (((Fintype.card Y : ℚ≥0) ^ (w + 1))⁻¹ * (Fintype.card Θ : ℚ≥0)) *
            (Fintype.card Y : ℚ≥0) ^ (w + 1) := by rw [hdens]
      _ = (Fintype.card Θ : ℚ≥0) *
            (((Fintype.card Y : ℚ≥0) ^ (w + 1))⁻¹ * (Fintype.card Y : ℚ≥0) ^ (w + 1)) := by ring
      _ = (Fintype.card Θ : ℚ≥0) := by rw [inv_mul_cancel₀ hY_ne, mul_one]
  exact_mod_cast hq

open scoped Classical in
/-- **Fixed-Tuple BFS Event Bound under `k`-Wise Independence**:
for any `(w + 1)`-wise independent hash pair `(h₁, h₂)`, injective vertex sequence `x₀, x`,
and degree sequence `h` summing to `w ≤ 2 ^ M`, the number of seeds `θ : Θ₁ × Θ₂` satisfying all
`w` BFS step constraints is at most `(2 ^ (M - 1) + w ^ 4) ^ w / (2 ^ M * 2 ^ (M - 1)) ^ w` of
`Fintype.card (Θ₁ × Θ₂)`. -/
private theorem card_filter_bfsStepEvent_le
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] {U M k w : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash k h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash k h₂)
    (hwk : w + 1 ≤ k) (hwM : w ≤ 2 ^ M)
    (x₀ : Fin U) (h : Fin (w + 1) → ℕ) (hsum : ∑ a : Fin (w + 1), h a = w)
    (x : Fin w → Fin U) (hx : Function.Injective x) (hne : ∀ b : Fin w, x b ≠ x₀) :
    (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      ∀ b : Fin w,
        bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
      (2 ^ M * 2 ^ (M - 1)) ^ w ≤
      (2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂) := by
  let xExt : Fin (w + 1) → Fin U := Fin.cases x₀ x
  have hxExt : Function.Injective xExt := injective_fin_cases hx hne
  have hh₁' := hh₁.comp hxExt
  have hh₂' := hh₂.comp hxExt
  have : Nonempty (Fin (2 ^ M)) := ⟨⟨0, Nat.two_pow_pos M⟩⟩
  have : Nonempty (Fin (2 ^ (M - 1))) := ⟨⟨0, Nat.two_pow_pos (M - 1)⟩⟩
  let V := validTuples M w h w le_rfl
  let evalSeed (θ : Θ₁ × Θ₂) : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1)) :=
    fun a => (h₁ θ.1 (xExt a), h₂ θ.2 (xExt a))
  let F (ps : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter fun θ => evalSeed θ = ps
  have hsub : (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      ∀ b : Fin w,
        bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b) ⊆
      V.biUnion F := by
    intro θ hθ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
    have hmem := mem_validTuples_of_bfsStepEvent x₀ h x (h₁ θ.1) (h₂ θ.2) hθ w le_rfl
    have hrest : restrictTuple (evalSeed θ) w le_rfl = evalSeed θ :=
      funext fun _ => rfl
    rw [hrest] at hmem
    exact Finset.mem_biUnion.mpr ⟨evalSeed θ, hmem, Finset.mem_filter.mpr ⟨Finset.mem_univ θ, rfl⟩⟩
  have hF_eq (ps : Fin (w + 1) → Fin (2 ^ M) × Fin (2 ^ (M - 1))) :
      (F ps).card * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) = Fintype.card (Θ₁ × Θ₂) := by
    let F₁ := Finset.univ.filter fun θ₁ : Θ₁ => (fun a => h₁ θ₁ (xExt a)) = fun a => (ps a).1
    let F₂ := Finset.univ.filter fun θ₂ : Θ₂ => (fun a => h₂ θ₂ (xExt a)) = fun a => (ps a).2
    have hprod : F ps = F₁ ×ˢ F₂ := by
      ext ⟨θ₁, θ₂⟩
      simp [F, F₁, F₂, evalSeed, funext_iff, Prod.ext_iff, forall_and]
    have h1 := card_filter_eq_mul_pow_of_isKWiseIndependentHash hh₁' hwk (fun a => (ps a).1)
    have h2 := card_filter_eq_mul_pow_of_isKWiseIndependentHash hh₂' hwk (fun a => (ps a).2)
    simp only [Fintype.card_fin] at h1 h2
    calc
      (F ps).card * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1)
        = (F₁.card * F₂.card) * ((2 ^ M) ^ (w + 1) * (2 ^ (M - 1)) ^ (w + 1)) := by
          rw [hprod, Finset.card_product, mul_pow]
      _ = (F₁.card * (2 ^ M) ^ (w + 1)) * (F₂.card * (2 ^ (M - 1)) ^ (w + 1)) := by ring
      _ = Fintype.card Θ₁ * Fintype.card Θ₂ := by rw [h1, h2]
      _ = Fintype.card (Θ₁ × Θ₂) := (Fintype.card_prod Θ₁ Θ₂).symm
  have hmul : (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      ∀ b : Fin w,
        bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
      (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) ≤
      ((2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ w) * Fintype.card (Θ₁ × Θ₂) := by
    calc
      (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
          ∀ b : Fin w,
            bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
          (2 ^ M * 2 ^ (M - 1)) ^ (w + 1)
        ≤ (V.biUnion F).card * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ ≤ (∑ ps ∈ V, (F ps).card) * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) :=
          Nat.mul_le_mul_right _ Finset.card_biUnion_le
      _ = ∑ ps ∈ V, (F ps).card * (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) :=
          Finset.sum_mul _ _ _
      _ = ∑ _ps ∈ V, Fintype.card (Θ₁ × Θ₂) :=
          Finset.sum_congr rfl fun ps _ => hF_eq ps
      _ = V.card * Fintype.card (Θ₁ × Θ₂) := by simp
      _ ≤ ((2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ w) * Fintype.card (Θ₁ × Θ₂) :=
          Nat.mul_le_mul_right _ (card_validTuples_le M hwM h hsum w le_rfl)
  have hpos : 0 < 2 ^ M * 2 ^ (M - 1) := Nat.mul_pos (Nat.two_pow_pos M) (Nat.two_pow_pos (M - 1))
  have hmul' : (2 ^ M * 2 ^ (M - 1)) *
      ((Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
        ∀ b : Fin w,
          bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
        (2 ^ M * 2 ^ (M - 1)) ^ w) ≤
      (2 ^ M * 2 ^ (M - 1)) * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂)) := by
    calc
      (2 ^ M * 2 ^ (M - 1)) *
          ((Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
            ∀ b : Fin w,
              bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
            (2 ^ M * 2 ^ (M - 1)) ^ w)
        = (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
            ∀ b : Fin w,
              bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) x₀ w h x b).card *
          (2 ^ M * 2 ^ (M - 1)) ^ (w + 1) := by ring
      _ ≤ ((2 ^ M * 2 ^ (M - 1)) * (2 ^ (M - 1) + w ^ 4) ^ w) * Fintype.card (Θ₁ × Θ₂) := hmul
      _ = (2 ^ M * 2 ^ (M - 1)) * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂)) := by ring
  exact Nat.le_of_mul_le_mul_left hmul' hpos

private theorem strictMono_eq_of_image_eq {w N : ℕ} {g₁ g₂ : Fin w → Fin N}
    (hg₁ : StrictMono g₁) (hg₂ : StrictMono g₂)
    (himg : Finset.univ.image g₁ = Finset.univ.image g₂) : g₁ = g₂ := by
  funext b
  induction b using WellFoundedLT.induction with
  | ind b ih =>
    rcases lt_trichotomy (g₁ b) (g₂ b) with hlt | heq | hgt
    · have hmem : g₁ b ∈ Finset.univ.image g₂ :=
        himg ▸ Finset.mem_image_of_mem g₁ (Finset.mem_univ b)
      rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
      have hcb : c < b := hg₂.lt_iff_lt.mp (hc.symm ▸ hlt)
      have h1 : g₁ c = g₁ b := (ih c hcb).trans hc
      exact False.elim (ne_of_lt hcb (hg₁.injective h1))
    · exact heq
    · have hmem : g₂ b ∈ Finset.univ.image g₁ :=
        himg.symm ▸ Finset.mem_image_of_mem g₂ (Finset.mem_univ b)
      rcases Finset.mem_image.mp hmem with ⟨c, _, hc⟩
      have hcb : c < b := hg₁.lt_iff_lt.mp (hc.symm ▸ hgt)
      have h1 : g₂ c = g₂ b := (ih c hcb).symm.trans hc
      exact False.elim (ne_of_lt hcb (hg₂.injective h1))

private def degSeqFinset (w : ℕ) : Finset (Fin (w + 1) → Fin (w + 1)) :=
  Finset.univ.filter fun f => ∑ a : Fin (w + 1), (f a).val = w

private def degPrefSum (w : ℕ) (f : Fin (w + 1) → Fin (w + 1)) (b : ℕ) : ℕ :=
  b + ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b), (f a).val

private def degPrefImage (w : ℕ) (f : Fin (w + 1) → Fin (w + 1)) : Finset (Fin (2 * w)) :=
  (Finset.univ : Finset (Fin w)).image fun b =>
    if h : degPrefSum w f b.val < 2 * w then ⟨degPrefSum w f b.val, h⟩
    else ⟨0, by have := b.isLt; omega⟩

private theorem card_degSeqFinset_le_four_pow (w : ℕ) :
    (degSeqFinset w).card ≤ 4 ^ w := by
  have hinj : Set.InjOn (degPrefImage w) (degSeqFinset w) := by
    intro f₁ hf₁ f₂ hf₂ himg
    have hsum₁ : ∑ a : Fin (w + 1), (f₁ a).val = w := (Finset.mem_filter.mp hf₁).2
    have hsum₂ : ∑ a : Fin (w + 1), (f₂ a).val = w := (Finset.mem_filter.mp hf₂).2
    have hlt (f : Fin (w + 1) → Fin (w + 1)) (hsum : ∑ a : Fin (w + 1), (f a).val = w)
        (b : Fin w) : degPrefSum w f b.val < 2 * w := by
      have hle : ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b.val), (f a).val ≤ w :=
        (Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _).trans hsum.le
      have := b.isLt
      dsimp only [degPrefSum]
      omega
    let g₁ (b : Fin w) : Fin (2 * w) := ⟨degPrefSum w f₁ b.val, hlt f₁ hsum₁ b⟩
    let g₂ (b : Fin w) : Fin (2 * w) := ⟨degPrefSum w f₂ b.val, hlt f₂ hsum₂ b⟩
    have hg_mono (f : Fin (w + 1) → Fin (w + 1)) (hsum : ∑ a : Fin (w + 1), (f a).val = w) :
        StrictMono (fun b : Fin w => (⟨degPrefSum w f b.val, hlt f hsum b⟩ : Fin (2 * w))) := by
      intro b₁ b₂ hb
      rw [Fin.lt_def] at hb ⊢
      have hsub : Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b₁.val) ⊆
          Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b₂.val) := by
        intro a ha
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        omega
      have hsum_le := Finset.sum_le_sum_of_subset (f := fun a : Fin (w + 1) => (f a).val) hsub
      dsimp only [degPrefSum]
      omega
    have himg' : Finset.univ.image g₁ = Finset.univ.image g₂ := by
      have h1 : degPrefImage w f₁ = Finset.univ.image g₁ := by
        dsimp only [degPrefImage, g₁]
        refine Finset.image_congr fun b _ => ?_
        simp [hlt f₁ hsum₁ b]
      have h2 : degPrefImage w f₂ = Finset.univ.image g₂ := by
        dsimp only [degPrefImage, g₂]
        refine Finset.image_congr fun b _ => ?_
        simp [hlt f₂ hsum₂ b]
      rwa [← h1, ← h2]
    have hg_eq : g₁ = g₂ := strictMono_eq_of_image_eq (hg_mono f₁ hsum₁) (hg_mono f₂ hsum₂) himg'
    have hpref_eq (b : ℕ) (hb : b ≤ w) :
        ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b), (f₁ a).val =
          ∑ a ∈ Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ b), (f₂ a).val := by
      rcases eq_or_lt_of_le hb with hbw_eq | hlt_b
      · rw [hbw_eq]
        have hfilter_univ :
            Finset.univ.filter (fun a : Fin (w + 1) => a.val ≤ w) = Finset.univ := by
          ext a
          simp [Nat.le_of_lt_succ a.isLt]
        rw [hfilter_univ, hsum₁, hsum₂]
      · have hval := congrArg Fin.val (congrFun hg_eq ⟨b, hlt_b⟩)
        dsimp only [g₁, g₂, degPrefSum] at hval
        omega
    ext a
    rcases a with ⟨a_val, ha_lt⟩
    cases a_val with
    | zero =>
      have h0 := hpref_eq 0 (Nat.zero_le w)
      have hfilter0 : Finset.univ.filter (fun c : Fin (w + 1) => c.val ≤ 0) = {0} := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
          Fin.val_zero]
        omega
      rw [hfilter0, Finset.sum_singleton, Finset.sum_singleton] at h0
      exact h0
    | succ b =>
      have hbw : b < w := Nat.lt_of_succ_lt_succ ha_lt
      have hb1 := hpref_eq (b + 1) hbw
      have hb0 := hpref_eq b (le_of_lt hbw)
      let S_prev := Finset.univ.filter (fun c : Fin (w + 1) => c.val ≤ b)
      let a_next : Fin (w + 1) := ⟨b + 1, ha_lt⟩
      have ha_notMem : a_next ∉ S_prev := by simp [S_prev, a_next]
      have hS_eq : Finset.univ.filter (fun c : Fin (w + 1) => c.val ≤ b + 1) =
          insert a_next S_prev := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, S_prev,
          a_next, Fin.ext_iff]
        omega
      rw [hS_eq, Finset.sum_insert ha_notMem, Finset.sum_insert ha_notMem] at hb1
      dsimp only [S_prev, a_next] at hb1
      omega
  have hmaps : Set.MapsTo (degPrefImage w) (degSeqFinset w)
      (Finset.univ : Finset (Fin (2 * w))).powerset := by
    intro f _
    simp
  calc
    (degSeqFinset w).card ≤ (Finset.univ : Finset (Fin (2 * w))).powerset.card :=
      Finset.card_le_card_of_injOn (degPrefImage w) hmaps hinj
    _ = 2 ^ (2 * w) := by simp
    _ = 4 ^ w := by rw [pow_mul]; rfl

open scoped Classical in
/-- **Union Bound over BFS Witnesses of Size `w`**:
under `(w + 1)`-wise independence of `h₁` and `h₂`, `1 ≤ M`, `32 * n_max ≤ 2 ^ M`, and
`2 * w ^ 4 ≤ 2 ^ M`, the fraction of seeds `θ : Θ₁ × Θ₂` admitting a size-`w` BFS dependency
witness over `D` (with `D.card ≤ n_max`) rooted at `x₀` is at most `4 ^ (-w)`. -/
private theorem four_pow_mul_card_hasBFSWitness_le
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] {U M n_max k w : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash k h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash k h₂)
    (hM : 1 ≤ M) (hload : 32 * n_max ≤ 2 ^ M) (hw4 : 2 * w ^ 4 ≤ 2 ^ M)
    (hwk : w + 1 ≤ k) {D : Finset (Fin U)} (hD : D.card ≤ n_max) (x₀ : Fin U) :
    4 ^ w * (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card ≤
      Fintype.card (Θ₁ × Θ₂) := by
  have hwM : w ≤ 2 ^ M := by
    rcases Nat.eq_zero_or_pos w with rfl | hw_pos
    · exact Nat.zero_le _
    · have hw_le_w4 : w ≤ w ^ 4 := Nat.le_self_pow (by omega) w
      omega
  let X_set : Finset (Fin w → Fin U) :=
    (Fintype.piFinset fun _ : Fin w => D.erase x₀).filter Function.Injective
  have hX_card : X_set.card ≤ n_max ^ w := by
    calc
      X_set.card ≤ (Fintype.piFinset fun _ : Fin w => D.erase x₀).card :=
        Finset.card_filter_le _ _
      _ = (D.erase x₀).card ^ w := by simp [Fintype.card_piFinset]
      _ ≤ n_max ^ w := Nat.pow_le_pow_left ((Finset.card_erase_le).trans hD) w
  let E (f : Fin (w + 1) → Fin (w + 1)) (x : Fin w → Fin U) : Finset (Θ₁ × Θ₂) :=
    Finset.univ.filter fun θ =>
      ∀ b : Fin w,
        bfsStepEvent (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2))
          x₀ w (fun a => (f a).val) x b
  have hsub : (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w) ⊆
      (degSeqFinset w).biUnion fun f => X_set.biUnion fun x => E f x := by
    intro θ hθ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
    rcases hθ with ⟨h, _, hsum, x, hx_inj, hx_mem, hev⟩
    have hle_w (a : Fin (w + 1)) : h a ≤ w :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans hsum.le
    let f : Fin (w + 1) → Fin (w + 1) := fun a => ⟨h a, Nat.lt_succ_of_le (hle_w a)⟩
    have hf_mem : f ∈ degSeqFinset w := Finset.mem_filter.mpr ⟨Finset.mem_univ f, hsum⟩
    have hx_set : x ∈ X_set := Finset.mem_filter.mpr
      ⟨Fintype.mem_piFinset.mpr hx_mem, hx_inj⟩
    exact Finset.mem_biUnion.mpr ⟨f, hf_mem,
      Finset.mem_biUnion.mpr ⟨x, hx_set, Finset.mem_filter.mpr ⟨Finset.mem_univ θ, hev⟩⟩⟩
  let P_base := 2 ^ M * 2 ^ (M - 1)
  have hE_le (f : Fin (w + 1) → Fin (w + 1)) (hf : f ∈ degSeqFinset w)
      (x : Fin w → Fin U) (hx : x ∈ X_set) :
      (E f x).card * P_base ^ w ≤ (2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂) := by
    have hsum : ∑ a : Fin (w + 1), (f a).val = w := (Finset.mem_filter.mp hf).2
    have hx_pair := Finset.mem_filter.mp hx
    have hx_mem := Fintype.mem_piFinset.mp hx_pair.1
    have hne : ∀ b : Fin w, x b ≠ x₀ := fun b => (Finset.mem_erase.mp (hx_mem b)).1
    exact card_filter_bfsStepEvent_le hh₁ hh₂ hwk hwM x₀ (fun a => (f a).val) hsum x hx_pair.2 hne
  have hsum_bi : (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card *
      P_base ^ w ≤
      4 ^ w * (n_max ^ w * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂))) := by
    calc
      (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
          HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card *
          P_base ^ w
        ≤ ((degSeqFinset w).biUnion fun f => X_set.biUnion fun x => E f x).card * P_base ^ w :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ ≤ (∑ f ∈ degSeqFinset w, ∑ x ∈ X_set, (E f x).card) * P_base ^ w := by
          refine Nat.mul_le_mul_right _ (Finset.card_biUnion_le.trans ?_)
          exact Finset.sum_le_sum fun f _ => Finset.card_biUnion_le
      _ = ∑ f ∈ degSeqFinset w, ∑ x ∈ X_set, (E f x).card * P_base ^ w := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun f _ => Finset.sum_mul _ _ _
      _ ≤ ∑ _f ∈ degSeqFinset w, ∑ _x ∈ X_set,
            (2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂) :=
          Finset.sum_le_sum fun f hf => Finset.sum_le_sum fun x hx => hE_le f hf x hx
      _ = (degSeqFinset w).card *
            (X_set.card * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂))) := by
          simp
      _ ≤ 4 ^ w * (n_max ^ w * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂))) :=
          Nat.mul_le_mul (card_degSeqFinset_le_four_pow w)
            (Nat.mul_le_mul_right _ hX_card)
  have h2M_eq : 2 ^ M = 2 * 2 ^ (M - 1) := by
    cases M with
    | zero => omega
    | succ M' => simp [pow_succ']
  have hstep_base : 16 * n_max * (2 ^ (M - 1) + w ^ 4) ≤ P_base := by
    dsimp only [P_base]
    have h16 : 16 * n_max ≤ 2 ^ (M - 1) := by omega
    have hw4' : w ^ 4 ≤ 2 ^ (M - 1) := by omega
    calc
      16 * n_max * (2 ^ (M - 1) + w ^ 4)
        ≤ 2 ^ (M - 1) * (2 ^ (M - 1) + 2 ^ (M - 1)) :=
          Nat.mul_le_mul h16 (Nat.add_le_add_left hw4' _)
      _ = 2 ^ M * 2 ^ (M - 1) := by rw [h2M_eq]; ring
  have hpow_le : (16 * n_max * (2 ^ (M - 1) + w ^ 4)) ^ w ≤ P_base ^ w :=
    Nat.pow_le_pow_left hstep_base w
  have hP_pos : 0 < P_base ^ w :=
    Nat.pow_pos (Nat.mul_pos (Nat.two_pow_pos M) (Nat.two_pow_pos (M - 1)))
  have hmul_final :
      (4 ^ w * (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
        HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card) *
        P_base ^ w ≤
      Fintype.card (Θ₁ × Θ₂) * P_base ^ w := by
    calc
      (4 ^ w * (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
          HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card) *
          P_base ^ w
        = 4 ^ w * ((Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
            HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card *
            P_base ^ w) := by ring
      _ ≤ 4 ^ w * (4 ^ w * (n_max ^ w * ((2 ^ (M - 1) + w ^ 4) ^ w * Fintype.card (Θ₁ × Θ₂)))) :=
          Nat.mul_le_mul_left _ hsum_bi
      _ = (4 * (4 * (n_max * (2 ^ (M - 1) + w ^ 4)))) ^ w * Fintype.card (Θ₁ × Θ₂) := by
          rw [mul_pow, mul_pow, mul_pow]
          ring
      _ = (16 * n_max * (2 ^ (M - 1) + w ^ 4)) ^ w * Fintype.card (Θ₁ × Θ₂) := by ring
      _ ≤ P_base ^ w * Fintype.card (Θ₁ × Θ₂) := Nat.mul_le_mul_right _ hpow_le
      _ = Fintype.card (Θ₁ × Θ₂) * P_base ^ w := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hmul_final hP_pos

private theorem mul_two_pow_succ_le_four_pow : ∀ w : ℕ, w * 2 ^ (w + 1) ≤ 4 ^ w
  | 0 => by simp
  | 1 => by decide
  | w + 2 => by
      have ih := mul_two_pow_succ_le_four_pow (w + 1)
      have h2 : 2 * (w + 2) ≤ 4 * (w + 1) := by omega
      calc
        (w + 2) * 2 ^ (w + 2 + 1) = (2 * (w + 2)) * 2 ^ (w + 1 + 1) := by ring
        _ ≤ (4 * (w + 1)) * 2 ^ (w + 1 + 1) := Nat.mul_le_mul_right _ h2
        _ = 4 * ((w + 1) * 2 ^ (w + 1 + 1)) := by ring
        _ ≤ 4 * 4 ^ (w + 1) := Nat.mul_le_mul_left 4 ih
        _ = 4 ^ (w + 2) := by ring

private theorem sum_two_pow_sub_eq (a : ℕ) :
    ∀ n : ℕ, (∑ w ∈ Finset.Ico a (a + n), 2 ^ (a + n - 1 - w)) + 1 = 2 ^ n
  | 0 => by simp
  | n + 1 => by
      have hsplit : Finset.Ico a (a + (n + 1)) =
          insert (a + n) (Finset.Ico a (a + n)) := by
        ext w
        simp only [Finset.mem_Ico, Finset.mem_insert]
        omega
      have hnotMem : a + n ∉ Finset.Ico a (a + n) := by simp
      rw [hsplit, Finset.sum_insert hnotMem]
      have hlast : a + (n + 1) - 1 - (a + n) = 0 := by omega
      rw [hlast, pow_zero]
      have hrest : ∑ w ∈ Finset.Ico a (a + n), 2 ^ (a + (n + 1) - 1 - w) =
          2 * ∑ w ∈ Finset.Ico a (a + n), 2 ^ (a + n - 1 - w) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w hw => ?_
        have hw_lt : w < a + n := (Finset.mem_Ico.mp hw).2
        have hexp : a + (n + 1) - 1 - w = (a + n - 1 - w) + 1 := by omega
        rw [hexp, pow_succ']
      have ih := sum_two_pow_sub_eq a n
      rw [hrest, pow_succ']
      omega

private theorem four_mul_n_max_sq_le_four_pow_maxProbeCutoff (n_max : ℕ) :
    4 * n_max * (n_max + 1) ≤ 4 ^ maxProbeCutoff n_max := by
  let N := max n_max 4
  have hN_ge : n_max ≤ N := le_max_left n_max 4
  have hN_4 : 4 ≤ N := le_max_right n_max 4
  have hclog : N ≤ 2 ^ Nat.clog 2 N := Nat.le_pow_clog (by decide) N
  have h2L : 16 * N ≤ 2 ^ maxProbeCutoff n_max := by
    dsimp only [maxProbeCutoff]
    rw [pow_add]
    have h16 : (2 : ℕ) ^ 4 = 16 := by decide
    calc
      16 * N ≤ 16 * 2 ^ Nat.clog 2 N := Nat.mul_le_mul_left 16 hclog
      _ = 2 ^ Nat.clog 2 N * 2 ^ 4 := by rw [h16, Nat.mul_comm]
  have hquad : 4 * n_max * (n_max + 1) ≤ (16 * N) * (16 * N) := by
    have h1 : 4 * n_max ≤ 16 * N := by omega
    have h2 : n_max + 1 ≤ 16 * N := by omega
    exact Nat.mul_le_mul h1 h2
  calc
    4 * n_max * (n_max + 1) ≤ (16 * N) * (16 * N) := hquad
    _ ≤ 2 ^ maxProbeCutoff n_max * 2 ^ maxProbeCutoff n_max := Nat.mul_le_mul h2L h2L
    _ = (2 * 2) ^ maxProbeCutoff n_max := (mul_pow 2 2 (maxProbeCutoff n_max)).symm
    _ = 4 ^ maxProbeCutoff n_max := rfl

open scoped Classical in
/-- **Seed-Sum Probe-Count Bound under `(2 * L + 1)`-Wise Independence**:
for `1 ≤ M`, `32 * max n_max 4 ≤ 2 ^ M`, `2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M`, and
any `(2 * maxProbeCutoff n_max + 1)`-wise independent hash families `h₁` and `h₂`, the sum of
`probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u)` over all `θ : Θ₁ × Θ₂` is at most
`2 * Fintype.card (Θ₁ × Θ₂)`. -/
theorem sum_probeCount_oddStride_le_of_kWiseIndependent
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] {U M n_max : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U} {T : Θ₁ × Θ₂ → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (oddStridePerm (h₁ θ.1) (h₂ θ.2)) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : Θ₁ × Θ₂, probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u)) ≤
      2 * Fintype.card (Θ₁ × Θ₂) := by
  let L := maxProbeCutoff n_max
  have hL_ge4 : 4 ≤ L := by dsimp only [L, maxProbeCutoff]; omega
  have hL_pos : 1 ≤ L := by omega
  let D := (Dictionary.dom s).erase u
  have hD_le : D.card ≤ n_max := Finset.card_erase_le.trans hdom
  have hload' : 32 * n_max ≤ 2 ^ M :=
    (Nat.mul_le_mul_left 32 (le_max_left n_max 4)).trans hload
  let C (x₀ : Fin U) (w : ℕ) : ℕ :=
    (Finset.univ.filter fun θ : Θ₁ × Θ₂ =>
      HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w).card
  have hC_bound (x₀ : Fin U) {w : ℕ} (hw : w < 2 * L) :
      4 ^ w * C x₀ w ≤ Fintype.card (Θ₁ × Θ₂) := by
    have hw4' : 2 * w ^ 4 ≤ 2 ^ M :=
      (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (le_of_lt hw) 4)).trans hw4
    exact four_pow_mul_card_hasBFSWitness_le hh₁ hh₂ hM hload' hw4' (by omega) hD_le x₀
  have hC_sum_eq (x₀ : Fin U) (w : ℕ) :
      (∑ θ : Θ₁ × Θ₂,
        if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w then 1
        else 0) = C x₀ w := by
    simp [C]
  have hC_w_sum_eq (x₀ : Fin U) (w : ℕ) :
      (∑ θ : Θ₁ × Θ₂,
        if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w then w
        else 0) = w * C x₀ w := by
    have : (fun θ : Θ₁ × Θ₂ =>
        if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w then w
        else 0) =
        fun θ => w * if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w
          then 1 else 0 := by
      ext θ
      split_ifs <;> simp
    rw [this, ← Finset.mul_sum, hC_sum_eq]
  have hnorm_two :
      2 * (∑ w ∈ Finset.Ico 1 L, w * C u w) ≤ Fintype.card (Θ₁ × Θ₂) := by
    have hterm (w : ℕ) (hw : w ∈ Finset.Ico 1 L) :
        2 ^ L * (w * C u w) ≤ 2 ^ (L - 1 - w) * Fintype.card (Θ₁ × Θ₂) := by
      have hw_lt : w < L := (Finset.mem_Ico.mp hw).2
      have hpow_L : 2 ^ L = 2 ^ (L - 1 - w) * 2 ^ (w + 1) := by
        rw [← pow_add]
        congr 1
        omega
      calc
        2 ^ L * (w * C u w)
          = 2 ^ (L - 1 - w) * ((w * 2 ^ (w + 1)) * C u w) := by
            rw [hpow_L]
            ring
        _ ≤ 2 ^ (L - 1 - w) * (4 ^ w * C u w) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (mul_two_pow_succ_le_four_pow w))
        _ ≤ 2 ^ (L - 1 - w) * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_left _ (hC_bound u (by omega))
    have hIco_eq : Finset.Ico 1 L = Finset.Ico 1 (1 + (L - 1)) := by
      congr 1
      omega
    have hsum_geom : (∑ w ∈ Finset.Ico 1 L, 2 ^ (L - 1 - w)) ≤ 2 ^ (L - 1) := by
      have hgeom := sum_two_pow_sub_eq 1 (L - 1)
      have h1L : 1 + (L - 1) - 1 = L - 1 := by omega
      rw [← hIco_eq, h1L] at hgeom
      omega
    have hmul_L : 2 ^ (L - 1) * (2 * ∑ w ∈ Finset.Ico 1 L, w * C u w) ≤
        2 ^ (L - 1) * Fintype.card (Θ₁ × Θ₂) := by
      have h2L_split : 2 ^ (L - 1) * 2 = 2 ^ L := by
        rw [← pow_succ, Nat.sub_add_cancel hL_pos]
      calc
        2 ^ (L - 1) * (2 * ∑ w ∈ Finset.Ico 1 L, w * C u w)
          = 2 ^ L * ∑ w ∈ Finset.Ico 1 L, w * C u w := by rw [← Nat.mul_assoc, h2L_split]
        _ = ∑ w ∈ Finset.Ico 1 L, 2 ^ L * (w * C u w) := Finset.mul_sum _ _ _
        _ ≤ ∑ w ∈ Finset.Ico 1 L, 2 ^ (L - 1 - w) * Fintype.card (Θ₁ × Θ₂) :=
            Finset.sum_le_sum hterm
        _ = (∑ w ∈ Finset.Ico 1 L, 2 ^ (L - 1 - w)) * Fintype.card (Θ₁ × Θ₂) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ 2 ^ (L - 1) * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_right _ hsum_geom
    exact Nat.le_of_mul_le_mul_left hmul_L (Nat.two_pow_pos (L - 1))
  have hov_x₀ (x₀ : Fin U) :
      4 ^ L * (∑ w ∈ Finset.Ico L (2 * L), C x₀ w) ≤ 2 * Fintype.card (Θ₁ × Θ₂) := by
    have hterm (w : ℕ) (hw : w ∈ Finset.Ico L (2 * L)) :
        (2 ^ (L - 1) * 4 ^ L) * C x₀ w ≤ 2 ^ (2 * L - 1 - w) * Fintype.card (Θ₁ × Θ₂) := by
      have hw_ge : L ≤ w := (Finset.mem_Ico.mp hw).1
      have hw_lt : w < 2 * L := (Finset.mem_Ico.mp hw).2
      have hpow_L1 : 2 ^ (L - 1) = 2 ^ (2 * L - 1 - w) * 2 ^ (w - L) := by
        rw [← pow_add]
        congr 1
        omega
      have hpow_4w : 4 ^ (w - L) * 4 ^ L = 4 ^ w := by
        rw [← pow_add]
        congr 1
        omega
      have hpow24 : 2 ^ (w - L) ≤ 4 ^ (w - L) := Nat.pow_le_pow_left (by decide) (w - L)
      calc
        (2 ^ (L - 1) * 4 ^ L) * C x₀ w
          = 2 ^ (2 * L - 1 - w) * ((2 ^ (w - L) * 4 ^ L) * C x₀ w) := by
            rw [hpow_L1]
            ring
        _ ≤ 2 ^ (2 * L - 1 - w) * ((4 ^ (w - L) * 4 ^ L) * C x₀ w) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hpow24))
        _ = 2 ^ (2 * L - 1 - w) * (4 ^ w * C x₀ w) := by rw [hpow_4w]
        _ ≤ 2 ^ (2 * L - 1 - w) * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_left _ (hC_bound x₀ hw_lt)
    have hIco_eq : Finset.Ico L (2 * L) = Finset.Ico L (L + L) := by
      congr 1
      omega
    have hsum_geom : (∑ w ∈ Finset.Ico L (2 * L), 2 ^ (2 * L - 1 - w)) ≤ 2 ^ L := by
      have hgeom := sum_two_pow_sub_eq L L
      have hLL : L + L - 1 = 2 * L - 1 := by omega
      rw [← hIco_eq, hLL] at hgeom
      omega
    have hmul_L : 2 ^ (L - 1) * (4 ^ L * ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) ≤
        2 ^ (L - 1) * (2 * Fintype.card (Θ₁ × Θ₂)) := by
      have h2L_split : 2 ^ L = 2 ^ (L - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hL_pos]
      calc
        2 ^ (L - 1) * (4 ^ L * ∑ w ∈ Finset.Ico L (2 * L), C x₀ w)
          = ∑ w ∈ Finset.Ico L (2 * L), (2 ^ (L - 1) * 4 ^ L) * C x₀ w := by
            rw [← Nat.mul_assoc, Finset.mul_sum]
        _ ≤ ∑ w ∈ Finset.Ico L (2 * L), 2 ^ (2 * L - 1 - w) * Fintype.card (Θ₁ × Θ₂) :=
            Finset.sum_le_sum hterm
        _ = (∑ w ∈ Finset.Ico L (2 * L), 2 ^ (2 * L - 1 - w)) * Fintype.card (Θ₁ × Θ₂) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ 2 ^ L * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_right _ hsum_geom
        _ = 2 ^ (L - 1) * (2 * Fintype.card (Θ₁ × Θ₂)) := by rw [h2L_split, Nat.mul_assoc]
    exact Nat.le_of_mul_le_mul_left hmul_L (Nat.two_pow_pos (L - 1))
  have hov_two :
      2 * (n_max * ∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) ≤
        Fintype.card (Θ₁ × Θ₂) := by
    have hcard_ins : (insert u (Dictionary.dom s)).card ≤ n_max + 1 :=
      (Finset.card_insert_le u (Dictionary.dom s)).trans (Nat.add_le_add_right hdom 1)
    have hsum_4L :
        4 ^ L * (∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) ≤
          (n_max + 1) * (2 * Fintype.card (Θ₁ × Θ₂)) := by
      calc
        4 ^ L * (∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w)
          = ∑ x₀ ∈ insert u (Dictionary.dom s), 4 ^ L * ∑ w ∈ Finset.Ico L (2 * L), C x₀ w :=
            Finset.mul_sum _ _ _
        _ ≤ ∑ _x₀ ∈ insert u (Dictionary.dom s), 2 * Fintype.card (Θ₁ × Θ₂) :=
            Finset.sum_le_sum fun x₀ _ => hov_x₀ x₀
        _ = (insert u (Dictionary.dom s)).card * (2 * Fintype.card (Θ₁ × Θ₂)) := by simp
        _ ≤ (n_max + 1) * (2 * Fintype.card (Θ₁ × Θ₂)) :=
            Nat.mul_le_mul_right _ hcard_ins
    have h4L_ge := four_mul_n_max_sq_le_four_pow_maxProbeCutoff n_max
    have hmul_4L :
        (2 * 4 ^ L) *
          (2 * (n_max * ∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w)) ≤
          (2 * 4 ^ L) * Fintype.card (Θ₁ × Θ₂) := by
      calc
        (2 * 4 ^ L) *
            (2 * (n_max * ∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w))
          = 4 * n_max *
              (4 ^ L * ∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) := by
            ring
        _ ≤ 4 * n_max * ((n_max + 1) * (2 * Fintype.card (Θ₁ × Θ₂))) :=
            Nat.mul_le_mul_left _ hsum_4L
        _ = 2 * (4 * n_max * (n_max + 1)) * Fintype.card (Θ₁ × Θ₂) := by ring
        _ ≤ (2 * 4 ^ L) * Fintype.card (Θ₁ × Θ₂) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 h4L_ge)
    have hpos_4L : 0 < 2 * 4 ^ L := Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
    exact Nat.le_of_mul_le_mul_left hmul_4L hpos_4L
  have hpt :
      (∑ θ : Θ₁ × Θ₂, probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u)) ≤
        Fintype.card (Θ₁ × Θ₂) +
        (∑ w ∈ Finset.Ico 1 L, w * C u w) +
        n_max * (∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) := by
    calc
      (∑ θ : Θ₁ × Θ₂, probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u))
        ≤ ∑ θ : Θ₁ × Θ₂,
            (1 +
            (∑ w ∈ Finset.Ico 1 L,
              if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D u w
              then w else 0) +
            n_max *
              (∑ x₀ ∈ insert u (Dictionary.dom s),
                ∑ w ∈ Finset.Ico L (2 * L),
                  if HasBFSWitness (Nat.two_pow_pos M) (oddStridePerm (h₁ θ.1) (h₂ θ.2)) D x₀ w
                  then 1 else 0)) :=
          Finset.sum_le_sum fun θ _ =>
            probeCount_le_sum_hasBFSWitness (Nat.two_pow_pos M) (hrep θ) hdom u hL_pos
      _ = Fintype.card (Θ₁ × Θ₂) +
          (∑ w ∈ Finset.Ico 1 L, w * C u w) +
          n_max * (∑ x₀ ∈ insert u (Dictionary.dom s), ∑ w ∈ Finset.Ico L (2 * L), C x₀ w) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, ← Finset.mul_sum]
          congr 2
          · rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun w _ => hC_w_sum_eq u w
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun x₀ _ => ?_
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun w _ => hC_sum_eq x₀ w
  omega

private theorem tsum_uniformOfFintype_le_of_sum_le
    {Θ : Type*} [Fintype Θ] [Nonempty Θ] {f : Θ → ℕ} {C : ℕ}
    (hsum : (∑ θ : Θ, f θ) ≤ C * Fintype.card Θ) :
    (∑' θ : Θ, PMF.uniformOfFintype Θ θ * (f θ : ℝ≥0∞)) ≤ C := by
  rw [tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, ← Finset.mul_sum, ← Nat.cast_sum]
  have hcard_pos : 0 < Fintype.card Θ := Fintype.card_pos
  have hcard_ne : (Fintype.card Θ : ℝ≥0∞) ≠ 0 := by positivity
  have hsum_cast : ((∑ θ : Θ, f θ : ℕ) : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (Fintype.card Θ : ℝ≥0∞) := by
    exact_mod_cast hsum
  calc
    (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((∑ θ : Θ, f θ : ℕ) : ℝ≥0∞)
      ≤ (Fintype.card Θ : ℝ≥0∞)⁻¹ * ((C : ℝ≥0∞) * (Fintype.card Θ : ℝ≥0∞)) := by gcongr
    _ = (C : ℝ≥0∞) * ((Fintype.card Θ : ℝ≥0∞)⁻¹ * (Fintype.card Θ : ℝ≥0∞)) := by ring
    _ = C := by rw [ENNReal.inv_mul_cancel hcard_ne (ENNReal.natCast_ne_top _), mul_one]

/-- **Expected Probe-Count Bound under `(2 * L + 1)`-Wise Independence**:
under the hypotheses of `sum_probeCount_oddStride_le_of_kWiseIndependent`, the expected probe count
of `u` under `PMF.uniformOfFintype (Θ₁ × Θ₂)` is at most `2` ([SchmidtSiegel1990], Theorem 1). -/
theorem expect_probeCount_oddStride_of_kWiseIndependent
    {Θ₁ Θ₂ : Type*} [Fintype Θ₁] [Fintype Θ₂] [Nonempty Θ₁] [Nonempty Θ₂] {U M n_max : ℕ}
    {h₁ : Θ₁ → Fin U → Fin (2 ^ M)} {h₂ : Θ₂ → Fin U → Fin (2 ^ (M - 1))}
    (hh₁ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₁)
    (hh₂ : Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) h₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U} {T : Θ₁ × Θ₂ → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (oddStridePerm (h₁ θ.1) (h₂ θ.2)) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : Θ₁ × Θ₂,
      PMF.uniformOfFintype (Θ₁ × Θ₂) θ *
        (probeCount (T θ) u (oddStridePerm (h₁ θ.1) (h₂ θ.2) u) : ℝ≥0∞)) ≤ 2 :=
  tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_le_of_kWiseIndependent hh₁ hh₂ hM hload hw4 hrep hdom u)

/-! ## Section 5: High-Probability Conditioning Bridge & Double Tabulation Instantiation -/

open Cslib.Probability

/-- Odd-stride double-hashing permutation family on a two-stage seed pair
`((top₁, bottom₁), (top₂, bottom₂)) : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)`. -/
noncomputable def twoStageOddStridePerm {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*} {U M : ℕ}
    (H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M))
    (H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))) :
    (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂) → Fin U → Equiv.Perm (Fin (2 ^ M))
  | ((top₁, bottom₁), (top₂, bottom₂)) => oddStridePerm (H₁ top₁ bottom₁) (H₂ top₂ bottom₂)

/-- **High-Probability Conditioning Bridge for Odd-Stride Double Hashing**:
if `H₁ top₁` and `H₂ top₂` are `(2 * maxProbeCutoff n_max + 1)`-wise independent whenever
`Good₁ top₁` and `Good₂ top₂` hold, and the bad top-seed sets `Finset.univ.filter (¬ Goodᵢ ·)`
each have density at most `1 / (2 * (n_max + 1))`, then the sum of `probeCount` over all seeds
`θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)` is at most `3` times the total number of seeds. -/
theorem sum_probeCount_oddStride_of_whp_kWiseIndependent
    {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*}
    [Fintype Θ_top₁] [Fintype Θ_bot₁] [Fintype Θ_top₂] [Fintype Θ_bot₂]
    {U M n_max : ℕ}
    {H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M)}
    {H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))}
    (Good₁ : Θ_top₁ → Prop) (Good₂ : Θ_top₂ → Prop)
    [DecidablePred Good₁] [DecidablePred Good₂]
    (hk₁ : ∀ top₁, Good₁ top₁ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₁ top₁))
    (hk₂ : ∀ top₂, Good₂ top₂ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₂ top₂))
    (hbad₁ : 2 * (Finset.univ.filter (fun top₁ : Θ_top₁ => ¬ Good₁ top₁)).card * (n_max + 1) ≤
      Fintype.card Θ_top₁)
    (hbad₂ : 2 * (Finset.univ.filter (fun top₂ : Θ_top₂ => ¬ Good₂ top₂)).card * (n_max + 1) ≤
      Fintype.card Θ_top₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂) → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (twoStageOddStridePerm H₁ H₂ θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
      probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u)) ≤
      3 * Fintype.card ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)) := by
  let B_card := Fintype.card (Θ_bot₁ × Θ_bot₂)
  let b₁ (top₁ : Θ_top₁) : ℕ := (n_max + 1) * if ¬ Good₁ top₁ then 1 else 0
  let b₂ (top₂ : Θ_top₂) : ℕ := (n_max + 1) * if ¬ Good₂ top₂ then 1 else 0
  have hinner (top₁ : Θ_top₁) (top₂ : Θ_top₂) :
      (∑ bot : Θ_bot₁ × Θ_bot₂,
        probeCount (T ((top₁, bot.1), (top₂, bot.2))) u
          (oddStridePerm (H₁ top₁ bot.1) (H₂ top₂ bot.2) u)) ≤
        (2 + b₁ top₁ + b₂ top₂) * B_card := by
    by_cases h1 : Good₁ top₁
    · by_cases h2 : Good₂ top₂
      · have hgood := sum_probeCount_oddStride_le_of_kWiseIndependent
          (hk₁ top₁ h1) (hk₂ top₂ h2) hM hload hw4
          (T := fun bot : Θ_bot₁ × Θ_bot₂ => T ((top₁, bot.1), (top₂, bot.2)))
          (fun bot => hrep ((top₁, bot.1), (top₂, bot.2))) hdom u
        simpa [b₁, b₂, h1, h2, B_card] using hgood
      · have hdet :
            (∑ bot : Θ_bot₁ × Θ_bot₂,
              probeCount (T ((top₁, bot.1), (top₂, bot.2))) u
                (oddStridePerm (H₁ top₁ bot.1) (H₂ top₂ bot.2) u)) ≤
              (n_max + 1) * B_card := by
          calc
            _ ≤ ∑ _bot : Θ_bot₁ × Θ_bot₂, (n_max + 1) :=
                Finset.sum_le_sum fun bot _ =>
                  probeCount_le_add_one (hrep ((top₁, bot.1), (top₂, bot.2))).toTableRep hdom u
            _ = (n_max + 1) * B_card := by simp [B_card, Nat.mul_comm]
        refine hdet.trans (Nat.mul_le_mul_right B_card ?_)
        simp [b₁, b₂, h1, h2]
    · have hdet :
          (∑ bot : Θ_bot₁ × Θ_bot₂,
            probeCount (T ((top₁, bot.1), (top₂, bot.2))) u
              (oddStridePerm (H₁ top₁ bot.1) (H₂ top₂ bot.2) u)) ≤
            (n_max + 1) * B_card := by
        calc
          _ ≤ ∑ _bot : Θ_bot₁ × Θ_bot₂, (n_max + 1) :=
              Finset.sum_le_sum fun bot _ =>
                probeCount_le_add_one (hrep ((top₁, bot.1), (top₂, bot.2))).toTableRep hdom u
          _ = (n_max + 1) * B_card := by simp [B_card, Nat.mul_comm]
      refine hdet.trans (Nat.mul_le_mul_right B_card ?_)
      simp only [b₁, b₂, h1, not_false_eq_true, ↓reduceIte, mul_one]
      omega
  have hrearrange :
      (∑ θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
        probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u)) =
      ∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, ∑ bot : Θ_bot₁ × Θ_bot₂,
        probeCount (T ((top₁, bot.1), (top₂, bot.2))) u
          (oddStridePerm (H₁ top₁ bot.1) (H₂ top₂ bot.2) u) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, twoStageOddStridePerm]
    refine Finset.sum_congr rfl fun top₁ _ => ?_
    rw [Finset.sum_comm]
  have hsum_top₁ :
      (∑ top₁ : Θ_top₁, b₁ top₁) =
        (Finset.univ.filter (fun top₁ : Θ_top₁ => ¬ Good₁ top₁)).card * (n_max + 1) := by
    dsimp only [b₁]
    rw [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id, Nat.mul_comm]
  have hsum_top₂ :
      (∑ top₂ : Θ_top₂, b₂ top₂) =
        (Finset.univ.filter (fun top₂ : Θ_top₂ => ¬ Good₂ top₂)).card * (n_max + 1) := by
    dsimp only [b₂]
    rw [← Finset.mul_sum, Finset.sum_boole, Nat.cast_id, Nat.mul_comm]
  have hsum_total :
      (∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, (2 + b₁ top₁ + b₂ top₂)) =
      2 * Fintype.card Θ_top₁ * Fintype.card Θ_top₂ +
      ((Finset.univ.filter (fun top₁ : Θ_top₁ => ¬ Good₁ top₁)).card * (n_max + 1)) *
        Fintype.card Θ_top₂ +
      Fintype.card Θ_top₁ *
        ((Finset.univ.filter (fun top₂ : Θ_top₂ => ¬ Good₂ top₂)).card * (n_max + 1)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Finset.mul_sum, hsum_top₁, hsum_top₂]
    ring
  have h2_top :
      2 * (∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, (2 + b₁ top₁ + b₂ top₂)) ≤
      2 * (3 * (Fintype.card Θ_top₁ * Fintype.card Θ_top₂)) := by
    have h1 := Nat.mul_le_mul_right (Fintype.card Θ_top₂) hbad₁
    have h2 := Nat.mul_le_mul_left (Fintype.card Θ_top₁) hbad₂
    rw [hsum_total]
    nlinarith
  have htop_le :
      (∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, (2 + b₁ top₁ + b₂ top₂)) ≤
      3 * (Fintype.card Θ_top₁ * Fintype.card Θ_top₂) :=
    Nat.le_of_mul_le_mul_left h2_top (by decide)
  calc
    (∑ θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
        probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u))
      ≤ ∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, (2 + b₁ top₁ + b₂ top₂) * B_card := by
        rw [hrearrange]
        exact Finset.sum_le_sum fun top₁ _ => Finset.sum_le_sum fun top₂ _ => hinner top₁ top₂
    _ = (∑ top₁ : Θ_top₁, ∑ top₂ : Θ_top₂, (2 + b₁ top₁ + b₂ top₂)) * B_card := by
        simp_rw [← Finset.sum_mul]
    _ ≤ (3 * (Fintype.card Θ_top₁ * Fintype.card Θ_top₂)) * B_card :=
        Nat.mul_le_mul_right B_card htop_le
    _ = 3 * Fintype.card ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)) := by
        dsimp only [B_card]
        simp only [Fintype.card_prod]
        ring

/-- **Expected Probe-Count Bound under High-Probability `(2 * L + 1)`-Wise Independence**:
under the hypotheses of `sum_probeCount_oddStride_of_whp_kWiseIndependent`, the expected probe count
of `u` under `PMF.uniformOfFintype ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂))` is at most `3`. -/
theorem expect_probeCount_oddStride_of_whp_kWiseIndependent
    {Θ_top₁ Θ_bot₁ Θ_top₂ Θ_bot₂ : Type*}
    [Fintype Θ_top₁] [Fintype Θ_bot₁] [Fintype Θ_top₂] [Fintype Θ_bot₂]
    [Nonempty Θ_top₁] [Nonempty Θ_bot₁] [Nonempty Θ_top₂] [Nonempty Θ_bot₂]
    {U M n_max : ℕ}
    {H₁ : Θ_top₁ → Θ_bot₁ → Fin U → Fin (2 ^ M)}
    {H₂ : Θ_top₂ → Θ_bot₂ → Fin U → Fin (2 ^ (M - 1))}
    (Good₁ : Θ_top₁ → Prop) (Good₂ : Θ_top₂ → Prop)
    [DecidablePred Good₁] [DecidablePred Good₂]
    (hk₁ : ∀ top₁, Good₁ top₁ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₁ top₁))
    (hk₂ : ∀ top₂, Good₂ top₂ →
      Cslib.Probability.IsKWiseIndependentHash (2 * maxProbeCutoff n_max + 1) (H₂ top₂))
    (hbad₁ : 2 * (Finset.univ.filter (fun top₁ : Θ_top₁ => ¬ Good₁ top₁)).card * (n_max + 1) ≤
      Fintype.card Θ_top₁)
    (hbad₂ : 2 * (Finset.univ.filter (fun top₂ : Θ_top₂ => ¬ Good₂ top₂)).card * (n_max + 1) ≤
      Fintype.card Θ_top₂)
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂) → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (twoStageOddStridePerm H₁ H₂ θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : (Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂),
      PMF.uniformOfFintype ((Θ_top₁ × Θ_bot₁) × (Θ_top₂ × Θ_bot₂)) θ *
        (probeCount (T θ) u (twoStageOddStridePerm H₁ H₂ θ u) : ℝ≥0∞)) ≤ 3 :=
  tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_of_whp_kWiseIndependent
      Good₁ Good₂ hk₁ hk₂ hbad₁ hbad₂ hM hload hw4 hrep hdom u)

/-- Seed space for odd-stride double hashing instantiated with two independent copies of Mikkel
Thorup's Double Tabulation (`[Thorup2013]`, Theorem 1(a)), into `Fin (2 ^ M)` and
`Fin (2 ^ (M - 1))`. -/
abbrev DoubleTabOddStrideSeed (c b M : ℕ) : Type :=
  (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b M) ×
    (DoubleTabTopSeed c (8 * c) b × DoubleTabBotSeed (8 * c) b (M - 1))

/-- Odd-stride double-hashing permutation family driven by two independent `doubleTabHash`
instances (`[Thorup2013]`, Theorem 1(a)). -/
@[expose] noncomputable def doubleTabOddStridePerm (c b U M : ℕ) :
    DoubleTabOddStrideSeed c b M → Fin U → Equiv.Perm (Fin (2 ^ M)) :=
  twoStageOddStridePerm (doubleTabHash c (8 * c) b U M) (doubleTabHash c (8 * c) b U (M - 1))

/-- **Double Tabulation Summed Probe-Count Bound under Explicit Code Bound (`[Thorup2013]`,
Theorem 1(a) & `[SchmidtSiegel1990]`, Theorem 1)**:
when `1 ≤ c`, `U ≤ 2 ^ (c * b)`, `1 ≤ M`, `32 * max n_max 4 ≤ 2 ^ M`,
`2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M`, and
`2 * (n_max + 1) * doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b)`,
the sum of `probeCount` over all seeds in `DoubleTabOddStrideSeed c b M` is at most `3` times the
total number of seeds. -/
theorem sum_probeCount_oddStride_doubleTab_of_codeBound_le
    {c b U M n_max : ℕ}
    (hc : 1 ≤ c) (hU : U ≤ 2 ^ (c * b))
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    (hbound : 2 * (n_max + 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b))
    {s : Dictionary.State U}
    {T : DoubleTabOddStrideSeed c b M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleTabOddStridePerm c b U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : DoubleTabOddStrideSeed c b M,
      probeCount (T θ) u (doubleTabOddStridePerm c b U M θ u)) ≤
      3 * Fintype.card (DoubleTabOddStrideSeed c b M) := by
  let k := 2 * maxProbeCutoff n_max + 1
  let Good (T₁ : DoubleTabTopSeed c (8 * c) b) : Prop := IsKUnique k (simpleTabTuple T₁)
  let BadTop := Finset.univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b => ¬ Good T₁
  let B := n_max + 1
  let Code := doubleTabCodeBound c (8 * c) 4 k
  let N_top := Fintype.card (DoubleTabTopSeed c (8 * c) b)
  have hB_ge : 1 ≤ B := by omega
  have hbound_code : 2 * Code ≤ 2 ^ (3 * b) := by
    calc 2 * Code = 2 * 1 * Code := by ring
      _ ≤ 2 * B * Code := Nat.mul_le_mul_right Code (Nat.mul_le_mul_left 2 hB_ge)
      _ ≤ 2 ^ (3 * b) := hbound
  have hbad_le : 2 ^ (6 * b) * BadTop.card ≤ 2 * Code ^ 2 * N_top :=
    card_not_isKUnique_eight_mul_le (b := b) hc hbound_code
  have hwhp : 2 * BadTop.card * (n_max + 1) ≤ N_top := by
    have hmul : 2 ^ (6 * b) * (2 * BadTop.card * B) ≤ 2 ^ (6 * b) * N_top := by
      calc 2 ^ (6 * b) * (2 * BadTop.card * B)
          = (2 * B) * (2 ^ (6 * b) * BadTop.card) := by ring
        _ ≤ (2 * B) * (2 * Code ^ 2 * N_top) := Nat.mul_le_mul_left _ hbad_le
        _ = (2 * B * (2 * Code ^ 2)) * N_top := by ring
        _ ≤ (2 * B * Code) ^ 2 * N_top := by
          refine Nat.mul_le_mul_right N_top ?_
          have hB_sq : B ≤ B * B := Nat.le_mul_of_pos_left B hB_ge
          nlinarith
        _ ≤ (2 ^ (3 * b)) ^ 2 * N_top :=
          Nat.mul_le_mul_right N_top (Nat.pow_le_pow_left hbound 2)
        _ = 2 ^ (6 * b) * N_top := by
          rw [← Nat.pow_mul]
          congr 2
          ring
    exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos (6 * b))
  exact sum_probeCount_oddStride_of_whp_kWiseIndependent Good Good
    (fun _ hT₁ => isKWiseIndependentHash_doubleTabHash_of_isKUnique hU hT₁)
    (fun _ hT₂ => isKWiseIndependentHash_doubleTabHash_of_isKUnique hU hT₂)
    hwhp hwhp hM hload hw4 hrep hdom u

/-- **Expected Probe-Count Bound for Double Tabulation Odd-Stride Double Hashing under Explicit Code
Bound**: under the hypotheses of `sum_probeCount_oddStride_doubleTab_of_codeBound_le`, the expected
probe count of `u` under `PMF.uniformOfFintype (DoubleTabOddStrideSeed c b M)` is at most `3`. -/
theorem expect_probeCount_oddStride_doubleTab_of_codeBound_le
    {c b U M n_max : ℕ}
    (hc : 1 ≤ c) (hU : U ≤ 2 ^ (c * b))
    (hM : 1 ≤ M) (hload : 32 * max n_max 4 ≤ 2 ^ M)
    (hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M)
    (hbound : 2 * (n_max + 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b))
    {s : Dictionary.State U}
    {T : DoubleTabOddStrideSeed c b M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleTabOddStridePerm c b U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : DoubleTabOddStrideSeed c b M,
      PMF.uniformOfFintype (DoubleTabOddStrideSeed c b M) θ *
        (probeCount (T θ) u (doubleTabOddStridePerm c b U M θ u) : ℝ≥0∞)) ≤ 3 :=
  tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_doubleTab_of_codeBound_le hc hU hM hload hw4 hbound hrep hdom u)

/-- Canonical Double Tabulation seed space for odd-stride double hashing at polynomial universe
exponent `c_exp`, capacity `n_max`, and table bit-width `M`. -/
abbrev DoubleHashSeed (c_exp n_max M : ℕ) : Type :=
  DoubleTabOddStrideSeed (2 * max c_exp 1) ((1 + Nat.clog 2 (max n_max 4)) / 2) M

/-- Canonical Double Tabulation odd-stride permutation family at polynomial universe exponent
`c_exp`, capacity `n_max`, universe size `U`, and table bit-width `M`. -/
@[expose] noncomputable def doubleHashOddStridePerm (c_exp n_max U M : ℕ) :
    DoubleHashSeed c_exp n_max M → Fin U → Equiv.Perm (Fin (2 ^ M)) :=
  doubleTabOddStridePerm (2 * max c_exp 1) ((1 + Nat.clog 2 (max n_max 4)) / 2) U M

/-- **Summed Probe-Count Bound for Double Tabulation Odd-Stride Double Hashing above
`doubleTabThreshold c_exp` (`[Thorup2013]`, Theorem 1(a) & `[SchmidtSiegel1990]`, Theorem 1)**:
whenever `doubleTabThreshold c_exp ≤ n_max`, `U ≤ max n_max 4 ^ c_exp`, and
`32 * max n_max 4 ≤ 2 ^ M`, the sum of `probeCount` over all seeds in
`DoubleHashSeed c_exp n_max M` is at most `3` times the total number of seeds. -/
theorem sum_probeCount_oddStride_doubleTab_le
    {c_exp n_max U M : ℕ}
    (hge : doubleTabThreshold c_exp ≤ n_max)
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : DoubleHashSeed c_exp n_max M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleHashOddStridePerm c_exp n_max U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑ θ : DoubleHashSeed c_exp n_max M,
      probeCount (T θ) u (doubleHashOddStridePerm c_exp n_max U M θ u)) ≤
      3 * Fintype.card (DoubleHashSeed c_exp n_max M) := by
  let c := 2 * max c_exp 1
  let b := (1 + Nat.clog 2 (max n_max 4)) / 2
  have hc1 : 1 ≤ c := by omega
  have hM : 1 ≤ M := by
    by_contra h
    have : M = 0 := by omega
    subst this
    omega
  have hclog_le : Nat.clog 2 (max n_max 4) ≤ 2 * b := by omega
  have hmax_le_2b : max n_max 4 ≤ 2 ^ (2 * b) :=
    (Nat.le_pow_clog (by decide) (max n_max 4)).trans
      (Nat.pow_le_pow_right (by decide) hclog_le)
  have hU_cb : U ≤ 2 ^ (c * b) := by
    calc U ≤ max n_max 4 ^ c_exp := hU
      _ ≤ max n_max 4 ^ max c_exp 1 :=
        Nat.pow_le_pow_right (by omega) (le_max_left c_exp 1)
      _ ≤ (2 ^ (2 * b)) ^ max c_exp 1 :=
        Nat.pow_le_pow_left hmax_le_2b (max c_exp 1)
      _ = 2 ^ (c * b) := by
        rw [← Nat.pow_mul]
        congr 1
        dsimp only [c]
        ring
  have hb_ge : doubleTabMinB c_exp ≤ b := by
    have hpow_le : 2 ^ (2 * doubleTabMinB c_exp) ≤ 2 ^ Nat.clog 2 (max n_max 4) := by
      rw [← doubleTabThreshold_eq]
      exact (hge.trans (le_max_left n_max 4)).trans (Nat.le_pow_clog (by decide) (max n_max 4))
    have hclog_ge : 2 * doubleTabMinB c_exp ≤ Nat.clog 2 (max n_max 4) :=
      (Nat.pow_le_pow_iff_right (by decide)).mp hpow_le
    omega
  have hb_min_def : doubleTabMinB c_exp = 4 * (24 * c + 8) ^ 2 := doubleTabMinB_eq c_exp
  have hb_8c : 8 * c ≤ b := by nlinarith
  have hb_64 : 64 ≤ b := by nlinarith
  have hcut_le : maxProbeCutoff n_max ≤ 2 * b + 4 := by
    unfold maxProbeCutoff
    omega
  have h2cut_sq : 2 * maxProbeCutoff n_max + 1 ≤ b ^ 2 := by nlinarith
  have hck_cube : c * (2 * maxProbeCutoff n_max + 1) ≤ b ^ 3 := by
    calc c * (2 * maxProbeCutoff n_max + 1)
        ≤ b * (b ^ 2) := Nat.mul_le_mul (by omega) h2cut_sq
      _ = b ^ 3 := by ring
  have hcode_pow : doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤
      b ^ (24 * c + 5) := by
    unfold doubleTabCodeBound
    calc c * ((c * (2 * maxProbeCutoff n_max + 1)) ^ (2 * c) * (8 * c)) ^ 4
        ≤ b * (((b ^ 3) ^ (2 * c) * b) ^ 4) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left
            (Nat.mul_le_mul (Nat.pow_le_pow_left hck_cube (2 * c)) hb_8c) 4)
      _ = b ^ (24 * c + 5) := by
        rw [← Nat.pow_mul, ← pow_succ, ← Nat.pow_mul, ← pow_succ']
        congr 1
        ring
  have h2n_le : 2 * (n_max + 1) ≤ 2 ^ (2 * b) * b ^ 2 := by
    have hn_le : n_max + 1 ≤ 2 * max n_max 4 := by omega
    have h4_le : 4 ≤ b ^ 2 := by nlinarith
    calc 2 * (n_max + 1)
        ≤ 4 * max n_max 4 := by omega
      _ = max n_max 4 * 4 := by ring
      _ ≤ 2 ^ (2 * b) * b ^ 2 := Nat.mul_le_mul hmax_le_2b h4_le
  have hprod_le : 2 * (n_max + 1) *
      doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1) ≤ 2 ^ (3 * b) := by
    calc 2 * (n_max + 1) *
          doubleTabCodeBound c (8 * c) 4 (2 * maxProbeCutoff n_max + 1)
        ≤ (2 ^ (2 * b) * b ^ 2) * b ^ (24 * c + 5) :=
          Nat.mul_le_mul h2n_le hcode_pow
      _ = 2 ^ (2 * b) * b ^ (24 * c + 7) := by
          rw [Nat.mul_assoc, ← Nat.pow_add]
          congr 2
          ring
      _ ≤ 2 ^ (2 * b) * b ^ (24 * c + 8) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ 2 ^ (2 * b) * 2 ^ b :=
          Nat.mul_le_mul_left _ (Nat.pow_le_two_pow (by omega) (hb_min_def ▸ hb_ge))
      _ = 2 ^ (3 * b) := by
          rw [← Nat.pow_add]
          congr 1
          ring
  have hw4 : 2 * (2 * maxProbeCutoff n_max) ^ 4 ≤ 2 ^ M := by
    have h2cut_le : 2 * maxProbeCutoff n_max ≤ b ^ 2 := by omega
    have hclog_le_M : Nat.clog 2 (max n_max 4) ≤ M :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr (by omega)
    have hb_le_M : b ≤ M := by omega
    calc 2 * (2 * maxProbeCutoff n_max) ^ 4
        ≤ b * (b ^ 2) ^ 4 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left h2cut_le 4)
      _ = b ^ 9 := by ring
      _ ≤ b ^ (24 * c + 8) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ 2 ^ b := Nat.pow_le_two_pow (by omega) (hb_min_def ▸ hb_ge)
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by decide) hb_le_M
  exact sum_probeCount_oddStride_doubleTab_of_codeBound_le
    hc1 hU_cb hM hm hw4 hprod_le hrep hdom u

/-- **`O(1)` Expected Probes (`≤ 3`) for Double Tabulation Odd-Stride Double Hashing above
`doubleTabThreshold c_exp` (`[Thorup2013]`, Theorem 1(a) & `[SchmidtSiegel1990]`, Theorem 1)**:
whenever `doubleTabThreshold c_exp ≤ n_max`, `U ≤ max n_max 4 ^ c_exp`, and
`32 * max n_max 4 ≤ 2 ^ M`, the expected probe count of `u` under
`PMF.uniformOfFintype (DoubleHashSeed c_exp n_max M)` is at most `3`. -/
theorem expect_probeCount_oddStride_doubleTab_le
    {c_exp n_max U M : ℕ}
    (hge : doubleTabThreshold c_exp ≤ n_max)
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : DoubleHashSeed c_exp n_max M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleHashOddStridePerm c_exp n_max U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : DoubleHashSeed c_exp n_max M,
      PMF.uniformOfFintype (DoubleHashSeed c_exp n_max M) θ *
        (probeCount (T θ) u (doubleHashOddStridePerm c_exp n_max U M θ u) : ℝ≥0∞)) ≤ 3 :=
  tsum_uniformOfFintype_le_of_sum_le
    (sum_probeCount_oddStride_doubleTab_le hge hU hm hrep hdom u)

/-- **Deterministic Expected Probe-Count Bound (`≤ n_max + 1`) for Any Full-Cycle Permutation
Family**: for any nonempty finite seed space `Θ` and any permutation family
`π : Θ → Fin U → Equiv.Perm (Fin m)` representing `s` in `T θ` with
`(Dictionary.dom s).card ≤ n_max`, the expected probe count of `u` under `PMF.uniformOfFintype Θ`
is at most `n_max + 1`. -/
theorem expect_probeCount_le_add_one
    {Θ : Type*} [Fintype Θ] [Nonempty Θ] {U m n_max : ℕ}
    {π : Θ → Fin U → Equiv.Perm (Fin m)}
    {s : Dictionary.State U} {T : Θ → Table U m}
    (hrep : ∀ θ, TableRep (π θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : Θ, PMF.uniformOfFintype Θ θ * (probeCount (T θ) u (π θ u) : ℝ≥0∞)) ≤
      (n_max + 1 : ℝ≥0∞) := by
  have hsum : (∑ θ : Θ, probeCount (T θ) u (π θ u)) ≤ (n_max + 1) * Fintype.card Θ := by
    calc
      (∑ θ : Θ, probeCount (T θ) u (π θ u))
        ≤ ∑ _θ : Θ, (n_max + 1) :=
          Finset.sum_le_sum fun θ _ => probeCount_le_add_one (hrep θ) hdom u
      _ = (n_max + 1) * Fintype.card Θ := by simp [Nat.mul_comm]
  exact mod_cast tsum_uniformOfFintype_le_of_sum_le hsum

/-- **Unconditional `O_{c_exp}(1)` Expected Probe-Count Bound for All Capacities `n_max : ℕ`**:
combining the deterministic full-cycle pigeonhole bound
`probeCount ≤ n_max + 1 ≤ doubleTabThreshold c_exp` for `n_max < doubleTabThreshold c_exp` with the
Double Tabulation bound `≤ 3` for `doubleTabThreshold c_exp ≤ n_max` yields expected probe count at
most `max (doubleTabThreshold c_exp : ℝ≥0∞) 3 = doubleTabThreshold c_exp` unconditionally for every
`n_max : ℕ`. -/
theorem expect_probeCount_oddStride_unconditional_le
    {c_exp n_max U M : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) (hm : 32 * max n_max 4 ≤ 2 ^ M)
    {s : Dictionary.State U}
    {T : DoubleHashSeed c_exp n_max M → Table U (2 ^ M)}
    (hrep : ∀ θ, OrderedTableRep (doubleHashOddStridePerm c_exp n_max U M θ) s (T θ))
    (hdom : (Dictionary.dom s).card ≤ n_max) (u : Fin U) :
    (∑' θ : DoubleHashSeed c_exp n_max M,
      PMF.uniformOfFintype (DoubleHashSeed c_exp n_max M) θ *
        (probeCount (T θ) u (doubleHashOddStridePerm c_exp n_max U M θ u) : ℝ≥0∞)) ≤
      max (doubleTabThreshold c_exp : ℝ≥0∞) 3 := by
  by_cases hge : doubleTabThreshold c_exp ≤ n_max
  · exact (expect_probeCount_oddStride_doubleTab_le hge hU hm hrep hdom u).trans
      (le_max_right _ 3)
  · have hdet := expect_probeCount_le_add_one (fun θ => (hrep θ).toTableRep) hdom u
    have hle : (n_max + 1 : ℝ≥0∞) ≤ (doubleTabThreshold c_exp : ℝ≥0∞) := by
      exact_mod_cast (by omega : n_max + 1 ≤ doubleTabThreshold c_exp)
    exact (hdet.trans hle).trans (le_max_left _ 3)

end Cslib.Algorithms.Lean.DoubleHashing
