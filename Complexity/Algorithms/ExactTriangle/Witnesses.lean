/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ExactTriangle.Splitting
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite witness recovery from modular lopsided answers

Correct finite answers are ordinary `Set.EqOn` premises on the actual lopsided graphs.
The recovery scans each accepted piece until it finds an exact zero. Distinct failed scans
contain distinct modular false positives. No solver, native program or time oracle is assumed.

## Main definitions

* `scanPiece`, `runScans`: finite witness search and number of scans.
* `AnswersCorrect`, `IsScanOrder`: correctness on queried pairs and a duplicate-free scan order.

## Main results

* `recovery_correct`: sound and complete recovery with at most `falsePositiveCount + 1` scans.
* `card_failedScans_le`: false-positive accounting.
* `falsePositiveCount_add_one_mul_pieceSize_le`: bound on the number of vertices scanned.

## References

Adapted from [Witnesses.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Sec3/Theorem17/Witnesses.lean) and the minimal scan definitions in
`PaperStatements.lean` at `anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
Context: [AlmanWilliams2026, Section 3]. Quoted docstring fragments reproduce comments in the pinned
formal source; other prose describes the local Lean API.
-/

@[expose] public section

namespace Cslib.Algorithms.ExactTriangle

open Cslib.Matrix

/-- A finite search result returns a zero triangle, or certifies that no zero triangle exists.
This specifies mathematical correctness only. -/
def IsSearchAnswer {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ)
    (r : Option (Fin n × Fin n × Fin n)) : Prop :=
  (∀ a b c, r = some (a, b, c) → weightSum wAB wBC wAC a b c = 0) ∧
    (r = none → ¬ HasZeroTriangle wAB wBC wAC)

/-- Proof of Theorem 17: "scan the piece C_k of its instance for a c with S(a,b,c) = 0".  The
vertices of the piece are tried in increasing order; the result is the first `c` found, or `none` if
the scan fails. -/
def scanPiece {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (D g k : ℕ) (a b : Fin n) :
    Option (Fin n) :=
  ((List.finRange n).filter fun c => c ∈ piece n D g k).find? fun c =>
    weightSum wAB wBC wAC a b c = 0

/-- Proof of Theorem 17: "For every query pair that the oracle accepts".  `ans ι` is the oracle's
answer to the instance with index `ι`.  The result is the set of all (instance, query pair of that
instance) that the oracle accepts; each of them calls for one scan. -/
def acceptedPairs {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) : Finset (InstanceIndex p × (Fin n × Fin n)) :=
  ((instanceIndices wAB D g p) ×ˢ Finset.univ).filter fun (ι, q) =>
    q ∈ (lopInstance wAB wBC wAC D g p ι).W ∧ ans ι q = true

/-- Proof of Theorem 17: the scans, one after the other, over a list of accepted pairs: "We stop as
soon as a zero triangle is found."  The result is the triangle found (or `none`) together with the
number of scans that were carried out. -/
def runScans {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (D g : ℕ) {p : ℕ} :
    List (InstanceIndex p × (Fin n × Fin n)) → Option (Fin n × Fin n × Fin n) × ℕ
  | [] => (none, 0)
  | ((_, _, k), a, b) :: rest =>
    match scanPiece wAB wBC wAC D g k a b with
    | some c => (some (a, b, c), 1)
    | none => ((runScans wAB wBC wAC D g rest).1, (runScans wAB wBC wAC D g rest).2 + 1)

/-- Proof of Theorem 17: "For every query pair that the oracle accepts, scan [...]".  The paper does
not say in which order.  `L` is an order of the scans: a list in which every accepted pair occurs
exactly once. -/
def IsScanOrder {n : ℕ} (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) (L : List (InstanceIndex p × (Fin n × Fin n))) :
    Prop :=
  L.Nodup ∧ ∀ x, x ∈ L ↔ x ∈ acceptedPairs wAB wBC wAC D g p ans


variable {n D g p : ℕ}

section Matrices

variable {wAB wBC wAC : Fin n → Fin n → ℤ}

/-! ### Scans and accepted pairs -/

/-- Proof of Theorem 17, "scan the piece C_k of its instance for a c with S(a,b,c) = 0": a `c` that
a scan returns lies in the piece and has `S(a,b,c) = 0`. -/
theorem scanPiece_eq_some {k : ℕ} {a b c : Fin n} (h : scanPiece wAB wBC wAC D g k a b = some c) :
    c ∈ piece n D g k ∧ weightSum wAB wBC wAC a b c = 0 := by
  have hmem := List.mem_of_find?_eq_some h
  rw [List.mem_filter] at hmem
  exact ⟨by simpa using hmem.2, by simpa using List.find?_some h⟩

/-- A scan fails exactly if the piece has no `c` with `S(a,b,c) = 0`. -/
theorem scanPiece_eq_none_iff {k : ℕ} {a b : Fin n} :
    scanPiece wAB wBC wAC D g k a b = none ↔
      ∀ c ∈ piece n D g k, weightSum wAB wBC wAC a b c ≠ 0 := by
  unfold scanPiece
  rw [List.find?_eq_none]
  simp [List.mem_filter]

variable (wAB wBC wAC) (D g)

/-- The scan that belongs to `x = ((ϱ, j, k), (a, b))`, a query pair `(a, b)` of the instance with
index `(ϱ, j, k)`: the piece `C_k` is scanned for the pair `(a, b)`. -/
abbrev scanOf (wAB wBC wAC : Fin n → Fin n → ℤ) (D g : ℕ)
    (x : InstanceIndex p × (Fin n × Fin n)) : Option (Fin n) :=
  scanPiece wAB wBC wAC D g x.1.2.2 x.2.1 x.2.2

/-- What the scans over a list of pairs return: a triangle that is returned is a zero triangle; if
none is returned, then every scan failed; and all the scans that are carried out, except possibly
the last one, fail. -/
private theorem runScans_spec (wAB wBC wAC : Fin n → Fin n → ℤ) (D g : ℕ)
    (l : List (InstanceIndex p × (Fin n × Fin n))) :
    (∀ a b c, (runScans wAB wBC wAC D g l).1 = some (a, b, c) → weightSum wAB wBC wAC a b c = 0) ∧
    ((runScans wAB wBC wAC D g l).1 = none → ∀ x ∈ l, scanOf wAB wBC wAC D g x = none) ∧
    (runScans wAB wBC wAC D g l).2 ≤
      (l.filter fun x => decide (scanOf wAB wBC wAC D g x = none)).length + 1 := by
  induction l with
  | nil => simp [runScans]
  | cons x rest ih =>
    obtain ⟨ihzero, ihnone, ihcount⟩ := ih
    cases hscan : scanOf wAB wBC wAC D g x with
    | some c =>
      -- The first scan finds `c`, and the scans stop.
      have hrun : runScans wAB wBC wAC D g (x :: rest) = (some (x.2.1, x.2.2, c), 1) := by
        simp only [runScans, hscan]
      rw [hrun]
      refine ⟨fun a b c' h => ?_, fun h => by simp at h, by simp⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact (scanPiece_eq_some hscan).2
    | none =>
      -- The first scan fails, and the scans go on with the rest of the list.
      have hrun : runScans wAB wBC wAC D g (x :: rest)
          = ((runScans wAB wBC wAC D g rest).1, (runScans wAB wBC wAC D g rest).2 + 1) := by
        simp only [runScans, hscan]
      rw [hrun, List.filter_cons_of_pos (by simpa using hscan), List.length_cons]
      refine ⟨ihzero, fun h y hy => ?_, by omega⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hscan
      · exact ihnone h y hy

variable (p) (ans : InstanceIndex p → Fin n × Fin n → Bool)

/-- The hypothesis on the oracle: `ans ι` is a correct answer to the instance with index `ι`, for
every instance of the reduction. -/
def AnswersCorrect (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) : Prop :=
  ∀ ι ∈ instanceIndices wAB D g p, Set.EqOn (fun q => ans ι q = true)
      (fun q => (lopInstance wAB wBC wAC D g p ι).HasCommonNeighbor q.1 q.2)
      ((lopInstance wAB wBC wAC D g p ι).W : Set _)

/-- Proof of Theorem 17: a "failed scan, of a piece C_k for a pair (a,b)": the oracle accepted the
pair in the instance, and the piece contains no `c` with `S(a,b,c) = 0`. -/
def failedScans (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) : Finset (InstanceIndex p × (Fin n × Fin n)) :=
  (acceptedPairs wAB wBC wAC D g p ans).filter fun x => scanOf wAB wBC wAC D g x = none

variable {wAB wBC wAC D g p ans}

/-- The accepted pairs: an index of an instance, a query pair of that instance, and the answer
"yes". -/
theorem mem_acceptedPairs {ι : InstanceIndex p} {q : Fin n × Fin n} :
    (ι, q) ∈ acceptedPairs wAB wBC wAC D g p ans ↔
      ι ∈ instanceIndices wAB D g p ∧ q ∈ (lopInstance wAB wBC wAC D g p ι).W ∧ ans ι q = true := by
  simp [acceptedPairs]

/-! ### The sentences of the paragraph "Witnesses" -/

/-- Proof of Theorem 17: "A zero triangle is always found, since its c lies in some piece and makes
the oracle accept its pair." -/
theorem exists_mem_acceptedPairs (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g) (hp : p ≠ 0)
    (hans : AnswersCorrect wAB wBC wAC D g p ans) {a b c : Fin n}
    (h0 : weightSum wAB wBC wAC a b c = 0) :
    ∃ ϱ j k, ((ϱ, j, k), (a, b)) ∈ acceptedPairs wAB wBC wAC D g p ans ∧ c ∈ piece n D g k := by
  -- The piece of `c`, the residue class of `(a, b)` and the chunk of `(a, b)` in it.
  obtain ⟨k, ⟨hk, hck⟩, -⟩ := existsUnique_mem_piece hD hg1 c
  obtain ⟨ϱ, hab, -⟩ := existsUnique_mem_residueClass wAB hp (a, b)
  obtain ⟨j, hj, hW⟩ := Finset.mem_biUnion.mp
    ((biUnion_chunk (residueClass wAB p ϱ) (one_le_queryCap (by omega) hDn)).symm ▸ hab)
  have hι : ((ϱ, j, k) : InstanceIndex p) ∈ instanceIndices wAB D g p :=
    (mem_instanceIndices wAB _).mpr ⟨Finset.mem_range.mp hj, hk⟩
  have hquery : (a, b) ∈ (lopInstance wAB wBC wAC D g p (ϱ, j, k)).W := hW
  refine ⟨ϱ, j, k, mem_acceptedPairs.mpr ⟨hι, hquery, ?_⟩, hck⟩
  -- The vertex `c` makes the oracle accept the pair.
  apply (Iff.of_eq (hans _ hι hquery)).mpr
  rw [hasCommonNeighbor_lopInstance_iff wAB wBC wAC hp hquery]
  exact ⟨c, hck, by rw [show weightSum wAB wBC wAC a b c = 0 from h0]⟩

/-- Proof of Theorem 17: "A failed scan, of a piece C_k for a pair (a,b), contains a c ∈ C_k with
S(a,b,c) ≡ 0 (mod p) but S(a,b,c) ≠ 0, that is, a false positive (a,b,c) of p". -/
theorem exists_isFalsePositive_of_mem_failedScans (hp : p ≠ 0)
    (hans : AnswersCorrect wAB wBC wAC D g p ans)
    {ϱ : Fin p} {j k : ℕ} {a b : Fin n}
    (hx : ((ϱ, j, k), (a, b)) ∈ failedScans wAB wBC wAC D g p ans) :
    ∃ c ∈ piece n D g k, IsFalsePositive wAB wBC wAC p (a, b, c) := by
  obtain ⟨hacc, hnone⟩ := Finset.mem_filter.mp hx
  obtain ⟨hι, hquery, htrue⟩ := mem_acceptedPairs.mp hacc
  obtain ⟨c, hc, hS⟩ := (hasCommonNeighbor_lopInstance_iff wAB wBC wAC hp hquery).mp
    ((Iff.of_eq (hans _ hι hquery)).mp htrue)
  exact ⟨c, hc, scanPiece_eq_none_iff.mp hnone c hc, Int.modEq_zero_iff_dvd.mp hS⟩

/-- Proof of Theorem 17: "distinct scans contain distinct false positives": a triple `(a,b,c)`
belongs to the scan of at most one accepted pair. -/
theorem eq_of_mem_acceptedPairs {ϱ ϱ' : Fin p} {j j' k k' : ℕ} {q : Fin n × Fin n}
    (hx : ((ϱ, j, k), q) ∈ acceptedPairs wAB wBC wAC D g p ans)
    (hy : ((ϱ', j', k'), q) ∈ acceptedPairs wAB wBC wAC D g p ans) {c : Fin n}
    (hc : c ∈ piece n D g k)
    (hc' : c ∈ piece n D g k') : (ϱ, j, k) = (ϱ', j', k') := by
  have hp : p ≠ 0 := by
    rintro rfl
    exact ϱ.elim0
  obtain ⟨hclass, hchunk⟩ := mem_lopInstance_W (mem_acceptedPairs.mp hx).2.1
  obtain ⟨hclass', hchunk'⟩ := mem_lopInstance_W (mem_acceptedPairs.mp hy).2.1
  -- The pair determines its residue class, then its chunk; the vertex `c` determines the piece.
  obtain rfl : ϱ = ϱ' := (existsUnique_mem_residueClass wAB hp q).unique hclass hclass'
  obtain rfl : j = j' := hchunk.symm.trans hchunk'
  obtain rfl : k = k' := ((mem_piece c).mp hc).symm.trans ((mem_piece c).mp hc')
  rfl

/-- Proof of Theorem 17: "distinct scans contain distinct false positives, so there are at most F(p)
failed scans", for any finite family `s` of scans and any notion "the scan `x` contains the triple
`t`".  This applies to the accepted-pair scans in `card_failedScans_le`. -/
theorem card_le_falsePositiveCount_of_distinct_scans
    (wAB wBC wAC : Fin n → Fin n → ℤ) {σ : Type*} (s : Finset σ)
    (contains : σ → Fin n × Fin n × Fin n → Prop)
    (hfalse : ∀ x ∈ s, ∃ t, contains x t ∧ IsFalsePositive wAB wBC wAC p t)
    (hdistinct : ∀ t, ∀ x ∈ s, ∀ y ∈ s, contains x t → contains y t → x = y) :
    s.card ≤ falsePositiveCount wAB wBC wAC p := by
  classical
  refine Finset.card_le_card_of_forall_subsingleton contains (fun x hx => ?_)
    fun t _ x hx y hy => hdistinct t x hx.1 y hy.1 hx.2 hy.2
  obtain ⟨t, ht, hfp⟩ := hfalse x hx
  exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfp⟩, ht⟩

/-- Proof of Theorem 17: "so there are at most F(p) failed scans". -/
theorem card_failedScans_le (hp : p ≠ 0)
    (hans : AnswersCorrect wAB wBC wAC D g p ans) :
    (failedScans wAB wBC wAC D g p ans).card ≤ falsePositiveCount wAB wBC wAC p := by
  -- The scan of the piece `C_k` for the pair `(a, b)` contains the triples `(a, b, c)`, `c ∈ C_k`.
  refine card_le_falsePositiveCount_of_distinct_scans wAB wBC wAC _
    (fun x t => x.2 = (t.1, t.2.1) ∧ t.2.2 ∈ piece n D g x.1.2.2) ?_ ?_
  · rintro ⟨⟨ϱ, j, k⟩, a, b⟩ hx
    obtain ⟨c, hc, hfalse⟩ := exists_isFalsePositive_of_mem_failedScans hp hans hx
    exact ⟨(a, b, c), ⟨rfl, hc⟩, hfalse⟩
  · rintro ⟨a, b, c⟩ ⟨⟨ϱ, j, k⟩, q⟩ hx ⟨⟨ϱ', j', k'⟩, q'⟩ hy ⟨rfl, hc⟩ ⟨rfl, hc'⟩
    rw [eq_of_mem_acceptedPairs (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hc hc']

end Matrices

/-- Proof of Theorem 17: the length of a scan, the `O(√D/g)` in "the scans cost O((F(p) + 1)√D/g)":
a piece has at most `⌈s/g⌉ ≤ 2√D/g` vertices. -/
theorem pieceSize_le_two_mul_sqrt_div (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D) :
    (pieceSize D g : ℝ) ≤ 2 * Real.sqrt D / (g : ℝ) := by
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg1
  calc (pieceSize D g : ℝ) ≤ (sOf D : ℝ) / (g : ℝ) + 1 := by
        rw [pieceSize_eq_ceil]
        exact (Nat.ceil_lt_add_one (by positivity)).le
    _ ≤ Real.sqrt D / (g : ℝ) + Real.sqrt D / (g : ℝ) :=
        add_le_add (div_le_div_of_nonneg_right (sOf_le_sqrt D) hg0.le)
          ((one_le_div hg0).mpr hg)
    _ = 2 * Real.sqrt D / (g : ℝ) := by ring

/-- For `16 ≤ D ≤ n`, `1 ≤ g ≤ sqrt D`, `κ ≥ 1` and edge weights bounded by `n^κ`, bound
`(falsePositiveCount + 1) * pieceSize` at any selected prime by
`(2 * Hashing.falsePositiveConst + 2) * κ * n^3 * log n / g`.
This arithmetic estimate counts candidate vertices rather than native instructions. -/
theorem falsePositiveCount_add_one_mul_pieceSize_le {κ : ℝ} (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D) (hκ : 1 ≤ κ)
    (hT : WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ)) (hp : IsSelectedPrime wAB wBC wAC D p) :
    ((falsePositiveCount wAB wBC wAC p : ℝ) + 1) * (pieceSize D g : ℝ)
      ≤ (2 * Hashing.falsePositiveConst + 2) * (κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)) := by
  have hsqrt : 4 ≤ Real.sqrt (D : ℝ) :=
    Real.le_sqrt_of_sq_le (by norm_num; exact_mod_cast hD)
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlog : 1 ≤ Real.log n :=
    (Real.le_log_iff_exp_le (by linarith)).2 (Real.exp_one_lt_three.le.trans (by linarith))
  set B := κ * (n : ℝ) ^ 3 * Real.log n with hB
  -- The two terms: `F(p) √D = O(B)` by the bound on `F(p)`, and `√D ≤ n ≤ n³ ≤ B`.
  have hfalse : (falsePositiveCount wAB wBC wAC p : ℝ) * Real.sqrt D ≤
      Hashing.falsePositiveConst * B := by
    have hF := Hashing.falsePositiveCount_le_const_mul hD hDn hκ wAB wBC wAC hT hp
    rwa [← mul_div_assoc, le_div_iff₀ (by linarith)] at hF
  have hone : Real.sqrt D ≤ B :=
    calc Real.sqrt D ≤ n := sqrt_le_natCast (by omega) hDn
      _ ≤ (n : ℝ) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      _ ≤ κ * (n : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity) hκ
      _ ≤ B := le_mul_of_one_le_right (by positivity) hlog
  calc ((falsePositiveCount wAB wBC wAC p : ℝ) + 1) * (pieceSize D g : ℝ)
      ≤ ((falsePositiveCount wAB wBC wAC p : ℝ) + 1) * (2 * Real.sqrt D / (g : ℝ)) := by
        gcongr
        exact pieceSize_le_two_mul_sqrt_div hg1 hg
    _ = (2 * ((falsePositiveCount wAB wBC wAC p : ℝ) * Real.sqrt D) +
        2 * Real.sqrt D) / (g : ℝ) := by ring
    _ ≤ (2 * (Hashing.falsePositiveConst * B) + 2 * B) / (g : ℝ) := by gcongr
    _ = (2 * Hashing.falsePositiveConst + 2) * (B / (g : ℝ)) := by ring

/-! ### The output of the reduction -/

/-- **Theorem 17, correctness.**  Given any correct answers of an oracle for
Lop-AE-SparseTri to the instances of the reduction, and whatever the order `L` of the scans, the
reduction's output is correct: it is a zero triangle if one exists, and `none` otherwise.  It
carries out at most `F(p) + 1` scans ("We stop as soon as a zero triangle is found"). -/
theorem recovery_correct (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (hp : IsSelectedPrime wAB wBC wAC D p)
    {ans : InstanceIndex p → Fin n × Fin n → Bool} (hans : AnswersCorrect wAB wBC wAC D g p ans)
    {L : List (InstanceIndex p × (Fin n × Fin n))} (hL : IsScanOrder wAB wBC wAC D g p ans L) :
    IsSearchAnswer wAB wBC wAC (runScans wAB wBC wAC D g L).1 ∧
      (runScans wAB wBC wAC D g L).2 ≤ falsePositiveCount wAB wBC wAC p + 1 := by
  have hp0 : p ≠ 0 := (mem_primesInRange.mp hp.1).1.ne_zero
  obtain ⟨hzero, hnone, hcount⟩ := runScans_spec wAB wBC wAC D g L
  refine ⟨⟨hzero, fun hout ⟨a, b, c, h0⟩ => ?_⟩, ?_⟩
  · -- "A zero triangle is always found": its scan cannot have failed.
    obtain ⟨ϱ, j, k, hx, hc⟩ := exists_mem_acceptedPairs hD hDn hg1 hp0 hans h0
    exact scanPiece_eq_none_iff.mp (hnone hout _ ((hL.2 _).mpr hx)) c hc h0
  · -- All the scans except possibly the last one fail, and there are at most `F(p)` failed scans.
    have hfailed : (L.filter fun x => decide (scanOf wAB wBC wAC D g x = none)).length
        ≤ (failedScans wAB wBC wAC D g p ans).card := by
      rw [← List.toFinset_card_of_nodup (hL.1.filter _)]
      refine Finset.card_le_card fun x hx => ?_
      obtain ⟨hxL, hxnone⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
      exact Finset.mem_filter.mpr ⟨(hL.2 x).mp hxL, by simpa using hxnone⟩
    have hF := card_failedScans_le hp0 hans
    omega


/-- Every finite set of accepted queries admits a duplicate-free scan order. -/
theorem exists_isScanOrder (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ)
    (ans : InstanceIndex p → Fin n × Fin n → Bool) :
    ∃ L, IsScanOrder wAB wBC wAC D g p ans L :=
  ⟨(acceptedPairs wAB wBC wAC D g p ans).toList,
    Finset.nodup_toList _, fun _ => Finset.mem_toList⟩

/-- Correct finite answer tables exist. This is a finite specification, with no solver or
complexity claim. Values outside the queried edges remain unconstrained. -/
theorem exists_answersCorrect (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ) :
    ∃ ans, AnswersCorrect wAB wBC wAC D g p ans := by
  classical
  refine ⟨fun ι q => decide ((lopInstance wAB wBC wAC D g p ι).HasCommonNeighbor q.1 q.2), ?_⟩
  intro ι _ q hq
  simp

/-- Correct finite common-neighbor counts supply the Boolean answers used by recovery.
This connects directly to the lopsided matrix/counting interface. -/
theorem answersCorrect_of_counting (wAB wBC wAC : Fin n → Fin n → ℤ) (D g p : ℕ)
    (counts : InstanceIndex p → Fin n × Fin n → ℕ)
    (hcounts : ∀ ι ∈ instanceIndices wAB D g p,
      Set.EqOn (counts ι) (fun q => (lopInstance wAB wBC wAC D g p ι).commonNeighborCount q.1 q.2)
        ((lopInstance wAB wBC wAC D g p ι).W : Set _)) :
    AnswersCorrect wAB wBC wAC D g p (fun ι q => decide (counts ι q ≠ 0)) := by
  intro ι hι q hq
  apply propext
  simp only [decide_eq_true_eq]
  exact Iff.of_eq ((lopInstance wAB wBC wAC D g p ι).detection_eqOn_of_counting
    (counts ι) (hcounts ι hι) hq)

/-- The recovery scan examines at most the uniform false-positive bound times the piece size.
This counts candidate vertices only; it is not a charged native running-time theorem. -/
theorem recovery_vertexBound {κ : ℝ} (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (hg : (g : ℝ) ≤ Real.sqrt D) (hκ : 1 ≤ κ)
    (wAB wBC wAC : Fin n → Fin n → ℤ)
    (hw : WeightsBoundedBy wAB wBC wAC ((n : ℝ) ^ κ))
    (hp : IsSelectedPrime wAB wBC wAC D p)
    {ans : InstanceIndex p → Fin n × Fin n → Bool} (hans : AnswersCorrect wAB wBC wAC D g p ans)
    {L : List (InstanceIndex p × (Fin n × Fin n))} (hL : IsScanOrder wAB wBC wAC D g p ans L) :
    IsSearchAnswer wAB wBC wAC (runScans wAB wBC wAC D g L).1 ∧
      ((runScans wAB wBC wAC D g L).2 : ℝ) * pieceSize D g ≤
        (2 * Hashing.falsePositiveConst + 2) * (κ * (n : ℝ) ^ 3 * Real.log n / (g : ℝ)) := by
  obtain ⟨hcorrect, hcount⟩ := recovery_correct hD hDn hg1 wAB wBC wAC hp hans hL
  refine ⟨hcorrect, le_trans ?_ (falsePositiveCount_add_one_mul_pieceSize_le
    wAB wBC wAC hD hDn hg1 hg hκ hw hp)⟩
  gcongr
  exact_mod_cast hcount

/-- Finite reduction equivalence: scanning all accepted queries returns `none` exactly when the
original three matrices have no zero triangle. Any duplicate-free scan order works. -/
theorem recovery_eq_none_iff (hD : 16 ≤ D) (hDn : D ≤ n) (hg1 : 1 ≤ g)
    (wAB wBC wAC : Fin n → Fin n → ℤ) (hp : IsSelectedPrime wAB wBC wAC D p)
    {ans : InstanceIndex p → Fin n × Fin n → Bool} (hans : AnswersCorrect wAB wBC wAC D g p ans)
    {L : List (InstanceIndex p × (Fin n × Fin n))} (hL : IsScanOrder wAB wBC wAC D g p ans L) :
    (runScans wAB wBC wAC D g L).1 = none ↔ ¬ HasZeroTriangle wAB wBC wAC := by
  obtain ⟨hsound, hcomplete⟩ := (recovery_correct hD hDn hg1 wAB wBC wAC hp hans hL).1
  refine ⟨hcomplete, fun hn => ?_⟩
  cases h : (runScans wAB wBC wAC D g L).1 with
  | none => rfl
  | some t =>
    obtain ⟨a, b, c⟩ := t
    exact False.elim (hn ⟨a, b, c, hsound a b c h⟩)

end Cslib.Algorithms.ExactTriangle
