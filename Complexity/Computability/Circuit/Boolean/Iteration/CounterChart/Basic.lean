/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.FunctionalGraph.Commutation
public import Mathlib.Data.BitVec
public import Mathlib.Data.FinEnum
public import Complexity.Foundations.Combinatorics.FunctionalGraph.HittingTime

/-!
# Linear intervals between edited counter edges

Cut the ordinary linear order after each edited successor, and also at its
two endpoints. There are at most `r+1` intervals. Inside each interval the
trajectory is ordinary increment, without circular wraparound. This is the
semantic chart used by the sparse live-time circuit.

## Main definitions

* `CounterIntervalChart`: intervals on which iteration is numerical translation.
* `nextBoundary`: the next interval start above `a`, or the upper endpoint `N`.

## Main results

* `exists_counterIntervalChart`: a cover with at most one more interval than edited edges.

## References

* Adapted from lean/Proofs/CounterIntervals.lean at revision `c4cfa198` of
  [S. Schlesinger, *Square-root circuit bounds for iterated functions*]
  [Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

open Cslib.FunctionalGraph

variable {n R : ℕ}

/-- A covering by ordinary intervals on which iteration is translation.
No permutation hypothesis is needed for this local trajectory certificate. -/
structure CounterIntervalChart (f : BitVec n → BitVec n) (R : ℕ) where
  /-- First natural-number index of each interval. -/
  start : Fin R → ℕ
  /-- Exclusive upper endpoint of each interval. -/
  stop : Fin R → ℕ
  /-- Each interval is nonempty. -/
  start_lt_stop : ∀ j, start j < stop j
  /-- Every interval stays within the word universe. -/
  stop_le : ∀ j, stop j ≤ 2 ^ n
  /-- Every word belongs to at least one interval. -/
  covers : ∀ x : BitVec n, ∃ j, start j ≤ x.toNat ∧ x.toNat < stop j
  /-- Inside an interval, iteration agrees with numerical increment. -/
  path : ∀ j d, d < stop j - start j →
    f^[d] (BitVec.ofNat n (start j)) = BitVec.ofNat n (start j + d)

namespace CounterIntervalChart

variable {f : BitVec n → BitVec n} (chart : CounterIntervalChart f R)

/-- Every interval start `chart.start j` is strictly below `2 ^ n`. -/
theorem start_lt (j : Fin R) : chart.start j < 2 ^ n :=
  (chart.start_lt_stop j).trans_le (chart.stop_le j)

/-- A word `x` inside interval `j` is reached from `chart.start j` after `x.toNat - chart.start j`
steps of `f`. -/
theorem point_eq (j : Fin R) (x : BitVec n)
    (hlo : chart.start j ≤ x.toNat) (hhi : x.toNat < chart.stop j) :
    f^[x.toNat - chart.start j] (BitVec.ofNat n (chart.start j)) = x := by
  rw [chart.path j _ (by lia), Nat.add_sub_of_le hlo, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

/-- A nonrepeating interval cannot be longer than its permutation cycle. -/
theorem length_le_period (hf : Function.Injective f) (j : Fin R) :
    chart.stop j - chart.start j ≤ cycleLength f (BitVec.ofNat n (chart.start j)) := by
  let x := BitVec.ofNat n (chart.start j)
  have hdepth : transientDepth f x = 0 :=
    transientDepth_eq_zero_of_mem_periodicPts f (hf.mem_periodicPts x)
  have hp : f^[cycleLength f x] x = x := by
    simpa only [hdepth, Function.iterate_zero_apply] using (isPeriodicPt_cycleLength f x).eq
  by_contra hlen
  have hlt : cycleLength f x < chart.stop j - chart.start j := by lia
  have hpath := chart.path j _ hlt
  rw [hp] at hpath
  have he := congrArg BitVec.toNat hpath
  have hfit : chart.start j + cycleLength f x < 2 ^ n := by
    have := chart.stop_le j
    lia
  simp only [x, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (chart.start_lt j),
    Nat.mod_eq_of_lt hfit] at he
  have := cycleLength_pos f x
  lia

end CounterIntervalChart

/-- Starts of the linear pieces; the last counter edge creates no additional piece. -/
private noncomputable def counterIntervalStarts (f : BitVec n → BitVec n) : Finset ℕ :=
  insert 0 (((disagreement f (fun x => x + 1)).image
    (fun x => x.toNat + 1)).filter fun a => a < 2 ^ n)

private theorem counterIntervalStarts_bound (f : BitVec n → BitVec n) :
    (counterIntervalStarts f).card ≤ (disagreement f (fun x => x + 1)).card + 1 := by
  classical
  unfold counterIntervalStarts
  exact (Finset.card_insert_le _ _).trans
    (Nat.add_le_add_right ((Finset.card_filter_le _ _).trans (Finset.card_image_le)) 1)

private theorem counterIntervalStarts_lt (f : BitVec n → BitVec n) {a : ℕ}
    (ha : a ∈ counterIntervalStarts f) : a < 2 ^ n := by
  classical
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Nat.two_pow_pos n
  · exact (Finset.mem_filter.mp ha).2

/-- The next start, or the upper endpoint of the whole universe. -/
def nextBoundary (S : Finset ℕ) (N a : ℕ) : ℕ :=
  (insert N (S.filter fun b => a < b)).min' (by simp)

private theorem nextBoundary_gt (S : Finset ℕ) {N a : ℕ} (ha : a < N) :
    a < nextBoundary S N a := by
  have h := Finset.min'_mem (insert N (S.filter fun b => a < b)) (by simp)
  rcases Finset.mem_insert.mp h with he | he
  · change nextBoundary S N a = N at he
    exact he.symm ▸ ha
  · exact (Finset.mem_filter.mp he).2

private theorem nextBoundary_le (S : Finset ℕ) (N a : ℕ) : nextBoundary S N a ≤ N :=
  Finset.min'_le _ _ (by simp)

/-- Every element `b ∈ S` strictly above `a` is an upper bound on `nextBoundary S N a`. -/
theorem nextBoundary_le_of_mem (S : Finset ℕ) (N a b : ℕ)
    (hb : b ∈ S) (hab : a < b) : nextBoundary S N a ≤ b :=
  Finset.min'_le _ _ (by simp [hb, hab])

/-- A finite set of starts containing zero covers the whole linear universe. -/
private theorem exists_covering_interval (S : Finset ℕ) {N x : ℕ}
    (hzero : 0 ∈ S) (hx : x < N) :
    ∃ a ∈ S, a ≤ x ∧ x < nextBoundary S N a := by
  let before := S.filter fun a => a ≤ x
  have hne : before.Nonempty := ⟨0, by simp [before, hzero]⟩
  let a := before.max' hne
  have ha : a ∈ before := Finset.max'_mem _ _
  have hax : a ≤ x := (Finset.mem_filter.mp ha).2
  refine ⟨a, (Finset.mem_filter.mp ha).1, hax, ?_⟩
  by_contra h
  have hend : nextBoundary S N a ≤ x := by lia
  have hm := Finset.min'_mem (insert N (S.filter fun b => a < b)) (by simp)
  rcases Finset.mem_insert.mp hm with he | he
  · change nextBoundary S N a = N at he
    lia
  · have hmem : nextBoundary S N a ∈ before :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp he).1, hend⟩
    have hle : nextBoundary S N a ≤ a := Finset.le_max' _ _ hmem
    have hgt := nextBoundary_gt S (hax.trans_lt hx)
    lia

/-- Before the next cut, the actual update agrees with numerical increment. -/
private theorem counterInterval_step (f : BitVec n → BitVec n) {a i : ℕ}
    (hai : a ≤ i) (hi : i + 1 < nextBoundary (counterIntervalStarts f) (2 ^ n) a) :
    f (BitVec.ofNat n i) = BitVec.ofNat n (i + 1) := by
  classical
  have hiN : i + 1 < 2 ^ n := hi.trans_le (nextBoundary_le _ _ _)
  have hnot : BitVec.ofNat n i ∉ disagreement f (fun x => x + 1) := by
    intro hbad
    have hstart : i + 1 ∈ counterIntervalStarts f := by
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨BitVec.ofNat n i, hbad, ?_⟩, hiN⟩
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by lia : i < 2 ^ n)]
    have := nextBoundary_le_of_mem (counterIntervalStarts f) (2 ^ n) a (i + 1)
      hstart (by lia)
    lia
  have he : f (BitVec.ofNat n i) = BitVec.ofNat n i + 1 := by
    simpa only [mem_disagreement, not_not] using hnot
  simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using he

/-- Every sparse counter modification has a chart of at most `r+1` intervals.
This existence theorem does not charge a preprocessing algorithm. -/
theorem exists_counterIntervalChart (f : BitVec n → BitVec n) :
    ∃ R ≤ (disagreement f (fun x => x + 1)).card + 1, Nonempty (CounterIntervalChart f R) := by
  classical
  let S := counterIntervalStarts f
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by simp)).symm
  let start := fun j : Fin S.card => (e j).val
  let stop := fun j => nextBoundary S (2 ^ n) (start j)
  have hs (j : Fin S.card) : start j < 2 ^ n := counterIntervalStarts_lt f (e j).property
  refine ⟨S.card, counterIntervalStarts_bound f, ⟨{
    start := start
    stop := stop
    start_lt_stop := fun j => nextBoundary_gt S (hs j)
    stop_le := fun j => nextBoundary_le S _ _
    covers := ?_
    path := ?_ }⟩⟩
  · intro x
    obtain ⟨a, ha, hlo, hhi⟩ := exists_covering_interval S
      (show 0 ∈ S by simp [S, counterIntervalStarts]) x.isLt
    refine ⟨e.symm ⟨a, ha⟩, ?_, ?_⟩
    · simpa only [start, Equiv.apply_symm_apply] using hlo
    · simpa only [stop, start, Equiv.apply_symm_apply] using hhi
  · intro j d hd
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Function.iterate_succ_apply', ih (by lia)]
      have step := counterInterval_step f (a := start j) (i := start j + d)
        (by lia) (by change start j + d + 1 < stop j; lia)
      simpa only [Nat.add_assoc] using step

end Cslib.Circuits.Boolean.Iteration
