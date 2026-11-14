/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.BallsToSlots.Spec
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.Foundations.Data.Nat.IterLog
public import CslibFrontier.Foundations.Data.Nat.LogStar
public import CslibFrontier.Init
public import CslibFrontier.Probability.KWiseIndependent
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Foundations.Probability.TwoStage
import CslibFrontier.Probability.KWiseIndependent.Concentration
import CslibFrontier.Probability.KWiseIndependent.Restriction
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The `k`-Kick Tree Balls-to-Slots Scheme (`[BenderFarachColtonKuszmaulKuszmaulLiu2022]`)

Formalizes the pure *`k`-kick tree* balls-to-slots scheme of Bender, Farach-Colton, J. Kuszmaul,
W. Kuszmaul, and Liu, *Proc. 54th ACM STOC*, pp. 1284–1297, 2022 (`arXiv:2111.00602v2`, 4 Nov 2021)
[BenderFarachColtonKuszmaulKuszmaulLiu2022] (printed p. `p` = PDF p. `p + 1`): Section 2.4 (p. 7 /
PDF p. 8) iterated-log bridge; Section 3.1 (pp. 8–10 / PDF pp. 9–11) hierarchy, priority kicks with
`switchingCost ≤ k + 1`, and kick-depth invariance; Section 5.1 (p. 27 / PDF p. 28) removal-only
deletion (vacating only the deleted ball's slot without moving other balls; Sections 3–3.1 describe
insertions only, and state still depends on insertion order so it is not history-independent); and
Lemma 1 (pp. 10–11 / PDF pp. 11–12) and Theorems 2–3 (p. 12 / PDF p. 13) 3-wise expectation bounds
and `2m`-th moment / `(1 - δ)`-w.h.p. multi-tree concentration.

Namespace `Cslib.DataStructure.BallsToSlots` (and `KickTree`) holds this Section 3 pure
balls-to-slots model, while `Cslib.DataStructure.Dictionary.KickTree` holds the quotient permutation
layers (`QuotientPerm`, `RoundSeed`, `SmallUniversePerm`) and Section 4–5 metadata and multi-tier
cubby saturation pieces (saturation, tail promotion and replacement, and tier-merge capacity
arithmetic; dynamic resizing and the full Word-RAM dictionary realization are tracked in #5186).
Adaptations: (1) XOR probe deduplication `g(x) ^^^ (idx % M)` over primary slots;
(2) dyadic schedule `capExp i = 2 * iterLog (i + 2) M` and
`binExp (i + 1) = 6 * iterLog (i + 2) M` (clamped by `effectiveDepth`), rounding the paper's
`s_d ≈ (log^(d) n)^6` and `Pr[depthCap < i + 1] ≈ (log^(i+1) n)^(-2)` to powers of two
(where `+2` aligns 0-based indexing with `Nat.iterLog` and Chebyshev's `L^4 / L^6 = 1 / L^2`
yields a geometric series); (3) `2m`-th moment insertion-set snapshot bounds in place of
full-independence Chernoff bounds.

## Main definitions
* `Cslib.DataStructure.BallsToSlots.KickTree.Params`, `State`, `Params.ValidState`,
  `effectiveDepth`, `standardParams`, `standardInsert`, `standardRun`.

## Main results
* `max_iterLog_two_le_logLogFactor`, `logLogFactor_le_two_mul_max_iterLog_two`.
* `Params.ValidState.insert`, `Params.ValidState.delete`, `Params.ValidState.run`,
  `Params.switchingCost_insert_le`, `Params.assignedDepth_insert_of_mem`,
  `State.assignedDepth_delete_of_ne`.
* `expect_ballProbeComplexity_standardInsert_le`, `expect_totalProbeComplexity_standardRun_le`,
  `depthSteps_le_binExp`, `dens_sum_totalProbeComplexity_standardRun_gt_le`,
  `dens_sum_totalProbeComplexity_standardRun_gt_le_of_whp`.

## References
* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul and M. Liu,
  *On the Optimal Time/Space Tradeoff for Hash Tables*,
  Sections 3.1 and 5.1][BenderFarachColtonKuszmaulKuszmaulLiu2022]
-/

public section
namespace Cslib.DataStructure.BallsToSlots
open Cslib.Probability Finset Fintype
open scoped BigOperators

/-- Lower bound comparing `max (Nat.iterLog 2 n) 1` with `Dictionary.Dynamic.logLogFactor n`. -/
theorem max_iterLog_two_le_logLogFactor (n : ℕ) :
    max (Nat.iterLog 2 n) 1 ≤ Dictionary.Dynamic.logLogFactor n :=
  Nat.max_iterLog_two_eq n ▸ Nat.iterLog_two_max_four_le_clog n
/-- Upper bound showing `Dictionary.Dynamic.logLogFactor n ≤ 2 * max (Nat.iterLog 2 n) 1`. -/
theorem logLogFactor_le_two_mul_max_iterLog_two (n : ℕ) :
    Dictionary.Dynamic.logLogFactor n ≤ 2 * max (Nat.iterLog 2 n) 1 := by
  rw [Nat.max_iterLog_two_eq]; exact Nat.clog_clog_max_four_le_two_mul_iterLog n

private theorem card_fin_div_two_pow_eq {m e : ℕ} (he : e ≤ m) (r₀ : Fin (2 ^ m)) :
    #{s : Fin (2 ^ m) | s.val / 2 ^ e = r₀.val / 2 ^ e} = 2 ^ e := by
  let eqv := (finCongr (show 2 ^ m = 2 ^ (e + (m - e)) by rw [Nat.add_sub_cancel' he])).trans
    (dyadicSplitEquiv e (m - e))
  refine (Finset.card_nbij' (fun s => (eqv s).1) (fun j => eqv.symm (j, (eqv r₀).2))
    (fun _ _ => Finset.mem_univ _)
    (fun j _ => by simp [eqv, Nat.add_mul_div_left j.val _ (Nat.two_pow_pos e),
      Nat.div_eq_of_lt j.isLt])
    (fun s hs => ?_) (fun _ _ => by simp)).trans (by simp)
  rw [Finset.mem_coe, Finset.mem_filter] at hs
  exact eqv.injective (Prod.ext (by simp) (Fin.ext (by simpa [eqv] using hs.2.symm)))

private theorem expect_fin_mod_two_pow_eq_zero {b e : ℕ} (he : e ≤ b) :
    𝔼 c : Fin (2 ^ b), (if c.val % 2 ^ e = 0 then (1 : ℝ) else 0) = 1 / (2 ^ e : ℝ) := by
  have : Nonempty (Fin (2 ^ (b - e))) := ⟨⟨0, by positivity⟩⟩
  let eqv := (finCongr (show 2 ^ b = 2 ^ (e + (b - e)) by rw [Nat.add_sub_cancel' he])).trans
    (dyadicSplitEquiv e (b - e))
  rw [Fintype.expect_equiv eqv _ (fun p : Fin (2 ^ e) × Fin (2 ^ (b - e)) =>
    if p.1 = ⟨0, by positivity⟩ then (1 : ℝ) else 0) (fun c => by simp [eqv, Fin.ext_iff])]
  rw [Fintype.expect_comp_fst
    (fun a : Fin (2 ^ e) => if a = ⟨0, by positivity⟩ then (1 : ℝ) else 0)]
  rw [Fintype.expect_ite_eq']
  simp

namespace KickTree
/-- Parameters for a power-of-two `depth`-kick tree over `2 ^ slotBits` slots. -/
structure Params where
  /-- Base-2 logarithm of `slotCount = 2 ^ slotBits`. -/
  slotBits : ℕ
  /-- Maximum kick depth `k` (tree depths are `0, 1, …, depth`). -/
  depth : ℕ
  /-- Bit-width of the auxiliary hash component used for depth-cap sampling. -/
  capBits : ℕ
  /-- Base-2 logarithm of the depth-`i` bin size `2 ^ binExp i`. -/
  binExp : Fin (depth + 1) → ℕ
  /-- Negative base-2 logarithm of `Pr[depthCap < i + 1] = 2 ^ (- capExp i)`. -/
  capExp : Fin depth → ℕ
  /-- Depth-`0` bin spans all `2 ^ slotBits` slots. -/
  binExp_zero : binExp ⟨0, Nat.zero_lt_succ depth⟩ = slotBits
  /-- Deeper levels have smaller or equal power-of-two bin sizes (`s_{i+1} ∣ s_i`). -/
  binExp_antitone : Antitone binExp
  /-- Deeper levels have larger or equal tail probabilities (`capExp` is antitone). -/
  capExp_antitone : Antitone capExp
  /-- Every depth-cap threshold fits within `capBits` bits. -/
  capExp_le_capBits : ∀ i : Fin depth, capExp i ≤ capBits

namespace Params
/-- Number of primary slots `M = 2 ^ P.slotBits`. -/
abbrev slotCount (P : Params) : ℕ := 2 ^ P.slotBits
/-- Total hash output bit-width `P.slotBits + P.capBits`. -/
abbrev hashBits (P : Params) : ℕ := P.slotBits + P.capBits
/-- Size `s_i = 2 ^ P.binExp i` of each depth-`i` bin. -/
abbrev binSize (P : Params) (i : Fin (P.depth + 1)) : ℕ := 2 ^ P.binExp i
theorem slotCount_pos (P : Params) : 0 < P.slotCount := by positivity
theorem binSize_pos (P : Params) (i : Fin (P.depth + 1)) : 0 < P.binSize i := by positivity
theorem binExp_le_slotBits (P : Params) (i : Fin (P.depth + 1)) : P.binExp i ≤ P.slotBits :=
  P.binExp_zero ▸ P.binExp_antitone (Fin.zero_le i)
/-- Canonical bijection splitting a `P.hashBits`-bit hash value into `(preferredSlot, capHash)`. -/
abbrev hashEquiv (P : Params) : Fin (2 ^ P.hashBits) ≃ Fin P.slotCount × Fin (2 ^ P.capBits) :=
  dyadicSplitEquiv P.slotBits P.capBits
/-- Preferred slot `g(x) ∈ Fin P.slotCount` extracted from the low `P.slotBits` hash bits. -/
@[expose] def preferredSlot (P : Params) (hx : Fin (2 ^ P.hashBits)) : Fin P.slotCount :=
  (P.hashEquiv hx).1
/-- Auxiliary depth-cap bits extracted from the high `P.capBits` hash bits. -/
@[expose] def capHash (P : Params) (hx : Fin (2 ^ P.hashBits)) : Fin (2 ^ P.capBits) :=
  (P.hashEquiv hx).2
/-- Slot `r` belongs to the depth-`i` bin `g_i(x)` determined by hash value `hx`. -/
@[expose] def InBin (P : Params) (hx : Fin (2 ^ P.hashBits)) (i : Fin (P.depth + 1))
    (r : Fin P.slotCount) : Prop := r.val / P.binSize i = (P.preferredSlot hx).val / P.binSize i
instance (P : Params) (hx : Fin (2 ^ P.hashBits)) (i : Fin (P.depth + 1)) (r : Fin P.slotCount) :
    Decidable (P.InBin hx i r) := inferInstanceAs (Decidable (_ = _))
theorem inBin_zero (P : Params) (hx : Fin (2 ^ P.hashBits)) (r : Fin P.slotCount) :
    P.InBin hx ⟨0, Nat.zero_lt_succ P.depth⟩ r := by
  have hsz : P.binSize ⟨0, Nat.zero_lt_succ P.depth⟩ = P.slotCount := by
    simp only [binSize, P.binExp_zero, slotCount]
  simp only [InBin, hsz, Nat.div_eq_of_lt r.isLt, Nat.div_eq_of_lt (P.preferredSlot hx).isLt]
theorem InBin.mono {P : Params} {hx : Fin (2 ^ P.hashBits)} {i j : Fin (P.depth + 1)}
    {r : Fin P.slotCount} (hij : i ≤ j) (h : P.InBin hx j r) : P.InBin hx i r := by
  have hs : P.binSize i = P.binSize j * 2 ^ (P.binExp i - P.binExp j) := by
    simp only [binSize, ← Nat.pow_add, Nat.add_sub_cancel' (P.binExp_antitone hij)]
  simp only [InBin, hs, ← Nat.div_div_eq_div_mul]; rw [h]
theorem inBin_iff_of_inBin {P : Params} {hx₁ hx₂ : Fin (2 ^ P.hashBits)} {i : Fin (P.depth + 1)}
    {r : Fin P.slotCount} (h₁ : P.InBin hx₁ i r) (h₂ : P.InBin hx₂ i r) (r' : Fin P.slotCount) :
    P.InBin hx₁ i r' ↔ P.InBin hx₂ i r' := by simp only [InBin] at h₁ h₂ ⊢; rw [← h₁, h₂]
/-- Deduplicated XOR probe sequence `idx ↦ g(x) ^^^ (idx % M)` over `Fin P.slotCount`. -/
@[expose] def probeSeq {α : Type*} (P : Params) (f : α → Fin (2 ^ P.hashBits)) :
    α → ℕ → Fin P.slotCount := xorProbeSeq P.slotBits fun x => P.preferredSlot (f x)
/-- Dyadic depth cap `s(x) ∈ Fin (P.depth + 1)` sampled from `P.capHash hx`. -/
@[expose] def depthCap (P : Params) (hx : Fin (2 ^ P.hashBits)) : Fin (P.depth + 1) :=
  match Fin.find? (n := P.depth) fun d => decide ((P.capHash hx).val % 2 ^ P.capExp d = 0) with
  | some d => d.castSucc | none => Fin.last P.depth
theorem depthCap_lt_succ_iff (P : Params) (hx : Fin (2 ^ P.hashBits)) (i : Fin P.depth) :
    (P.depthCap hx).val < i.val + 1 ↔ (P.capHash hx).val % 2 ^ P.capExp i = 0 := by
  unfold depthCap; cases hf :
      Fin.find? (n := P.depth) (fun d => decide ((P.capHash hx).val % 2 ^ P.capExp d = 0)) with
  | none =>
    have hnone := Fin.find?_eq_none_iff.mp hf i; simp only [decide_eq_false_iff_not] at hnone
    simp only [Fin.val_last, hnone, iff_false, not_lt]; exact i.isLt
  | some d =>
    have hmem := Fin.mem_find?_iff.mp (Option.mem_def.mpr hf)
    have hd0 := of_decide_eq_true hmem.1; simp only [Fin.val_castSucc]
    refine ⟨fun _ => Nat.mod_eq_zero_of_dvd ((Nat.pow_dvd_pow 2
      (P.capExp_antitone (Fin.le_def.mpr (by omega)))).trans (Nat.dvd_of_mod_eq_zero hd0)),
      fun hi0 => ?_⟩
    have hle : d ≤ i := not_lt.mp fun hlt => hmem.2 i hlt (decide_eq_true hi0)
    exact Nat.lt_succ_of_le (Fin.le_def.mp hle)
end Params
/-- State of a `P.depth`-kick tree over balls of type `α`. -/
@[ext] structure State (P : Params) (α : Type*) where
  /-- Injective assignment of present balls to primary slots `Fin P.slotCount`. -/
  assignment : SlotAssignment α P.slotCount
  /-- Priority depth associated with each slot (`0` by convention when free). -/
  slotDepth : Fin P.slotCount → Fin (P.depth + 1)
namespace State
/-- Empty kick-tree state with all `P.slotCount` slots free. -/
@[expose] def empty (P : Params) (α : Type*) : State P α :=
  ⟨SlotAssignment.empty α P.slotCount, fun _ => ⟨0, Nat.zero_lt_succ P.depth⟩⟩
variable {P : Params} {α : Type*} [DecidableEq α]
/-- Query the slot currently holding ball `x` (`none` if absent). -/
@[expose] def query (st : State P α) (x : α) : Option (Fin P.slotCount) := st.assignment.slotOf x
/-- Priority depth currently associated with ball `x` (`none` if `x` is absent). -/
@[expose] def assignedDepth (st : State P α) (x : α) : Option (Fin (P.depth + 1)) :=
  (st.assignment.slotOf x).map st.slotDepth
/-- Removal-only deletion ([BenderFarachColtonKuszmaulKuszmaulLiu2022], Section 5.1, printed p. 27
/ PDF p. 28): vacate `x`'s slot without moving or re-depthing any other ball (the resulting state
still depends on insertion order, so it is not history-independent). -/
@[expose] def delete (st : State P α) (x : α) : State P α :=
  ⟨st.assignment.delete x, fun r =>
    if st.assignment.occupant r = some x then ⟨0, Nat.zero_lt_succ P.depth⟩ else st.slotDepth r⟩
/-- Deleting `x` leaves the assigned depth of every other ball `z ≠ x` unchanged. -/
theorem assignedDepth_delete_of_ne (st : State P α) {x z : α} (hne : z ≠ x) :
    (st.delete x).assignedDepth z = st.assignedDepth z := by
  simp only [assignedDepth, delete, st.assignment.slotOf_delete_of_ne hne]
  cases h : st.assignment.slotOf z with | none => rfl | some r =>
    have hr := (st.assignment.slotOf_eq_some_iff z r).mp h
    simp [show st.assignment.occupant r ≠ some x by
      rw [hr]; exact fun h' => hne (Option.some.inj h')]
/-- Place ball `y` into slot `r` at priority depth `d`. -/
@[expose] def put (st : State P α) (r : Fin P.slotCount) (y : α) (d : Fin (P.depth + 1)) :
    State P α := ⟨st.assignment.put r y, Function.update st.slotDepth r d⟩
@[simp] theorem assignedDepth_put_self (st : State P α) (r : Fin P.slotCount) (y : α)
    (d : Fin (P.depth + 1)) : (st.put r y d).assignedDepth y = some d := by
  simp [assignedDepth, put]
theorem assignedDepth_put_of_ne (st : State P α) (r : Fin P.slotCount) (y : α)
    (d : Fin (P.depth + 1)) {z : α} (hzy : z ≠ y) (hrz : st.assignment.occupant r ≠ some z) :
    (st.put r y d).assignedDepth z = st.assignedDepth z := by
  simp only [assignedDepth, put, st.assignment.slotOf_put_of_ne r y hzy hrz]
  cases h : st.assignment.slotOf z with | none => rfl | some r' =>
    have hr'z := (st.assignment.slotOf_eq_some_iff z r').mp h
    simp [Function.update_of_ne (fun heq => hrz (heq ▸ hr'z) : r' ≠ r)]
end State

namespace Params
/-- Structural and depth-cap invariant of a `k`-kick tree state `st` with respect to hash `f`. -/
structure ValidState {α : Type*} (P : Params) (f : α → Fin (2 ^ P.hashBits))
    (st : State P α) : Prop where
  /-- Every ball occupies a slot inside its associated priority depth's bin. -/
  inBin_of_occupant : ∀ ⦃r : Fin P.slotCount⦄ ⦃x : α⦄,
    st.assignment.occupant r = some x → P.InBin (f x) (st.slotDepth r) r
  /-- Every ball's associated priority depth is bounded by its depth-cap hash `depthCap (f x)`. -/
  slotDepth_le_depthCap : ∀ ⦃r : Fin P.slotCount⦄ ⦃x : α⦄,
    st.assignment.occupant r = some x → st.slotDepth r ≤ P.depthCap (f x)
theorem ValidState.empty {α : Type*} (P : Params) (f : α → Fin (2 ^ P.hashBits)) :
    P.ValidState f (State.empty P α) where
  inBin_of_occupant _ _ h := by cases h
  slotDepth_le_depthCap _ _ h := by cases h
theorem ValidState.respectsProbeSeq {α : Type*} {P : Params} {f : α → Fin (2 ^ P.hashBits)}
    {st : State P α} (_ : P.ValidState f st) : RespectsProbeSeq (P.probeSeq f) st.assignment :=
  respectsProbeSeq_xorProbeSeq P.slotBits _ st.assignment
/-- Least free slot inside the depth-`d` bin of `hx`, if any. -/
@[expose] def findFree {α : Type*} (P : Params) (st : State P α) (hx : Fin (2 ^ P.hashBits))
    (d : Fin (P.depth + 1)) : Option (Fin P.slotCount) :=
  Fin.find? fun r => decide (P.InBin hx d r) && (st.assignment.occupant r).isNone
/-- Least slot inside the depth-`d` bin of `hx` holding a strictly shallower priority `< d`. -/
@[expose] def findKick {α : Type*} (P : Params) (st : State P α) (hx : Fin (2 ^ P.hashBits))
    (d : Fin (P.depth + 1)) : Option (Fin P.slotCount) :=
  Fin.find? fun r => decide (P.InBin hx d r) && decide (st.slotDepth r < d)
/-- A depth-`d` bin is saturated iff it has neither a free slot nor an occupant of depth `< d`. -/
@[expose] def binSaturated {α : Type*} (P : Params) (st : State P α) (hx : Fin (2 ^ P.hashBits))
    (d : Fin (P.depth + 1)) : Bool := (P.findFree st hx d).isNone && (P.findKick st hx d).isNone
theorem binSaturated_eq_true_iff {α : Type*} (P : Params) (st : State P α)
    (hx : Fin (2 ^ P.hashBits)) (d : Fin (P.depth + 1)) :
    P.binSaturated st hx d = true ↔ ∀ r : Fin P.slotCount, P.InBin hx d r →
      (st.assignment.occupant r).isSome ∧ d ≤ st.slotDepth r := by
  simp only [binSaturated, Bool.and_eq_true, Option.isNone_iff_eq_none, findFree, findKick,
    Fin.find?_eq_none_iff]
  refine ⟨fun ⟨hfree, hkick⟩ r hr => ?_, fun hall => ⟨fun r => ?_, fun r => ?_⟩⟩
  · have hf := hfree r; have hk := hkick r
    simp only [hr, decide_true, Bool.true_and, Bool.eq_false_iff, ne_eq, Option.isNone_iff_eq_none,
      decide_eq_true_eq, not_lt] at hf hk
    exact ⟨Option.ne_none_iff_isSome.mp hf, hk⟩
  · by_cases hr : P.InBin hx d r
    · have h1 := (hall r hr).1; cases hocc : st.assignment.occupant r <;> simp [hr, hocc] at h1 ⊢
    · simp [hr]
  · by_cases hr : P.InBin hx d r <;> simp [hr, fun h => not_lt.mpr (hall r h).2]
/-- Largest depth `j` such that `g_0(x), …, g_j(x)` are all unsaturated. -/
@[expose] def greedyUnsatDepth {α : Type*} (P : Params) (st : State P α)
    (hx : Fin (2 ^ P.hashBits)) : Fin (P.depth + 1) :=
  match Fin.find? (n := P.depth) fun d => P.binSaturated st hx d.succ with
  | some d => d.castSucc | none => Fin.last P.depth
section Decidable
variable {α : Type*} [DecidableEq α] {P : Params}
/-- Deleting any ball preserves `ValidState` without resampling `f`. -/
theorem ValidState.delete {f : α → Fin (2 ^ P.hashBits)} {st : State P α}
    (hst : P.ValidState f st) (x : α) : P.ValidState f (st.delete x) := by
  constructor <;> intro r z hz <;> simp only [State.delete, SlotAssignment.delete] at hz ⊢ <;>
    split_ifs at hz with hrx <;> simp only [hrx, ↓reduceIte]
  · exact hst.inBin_of_occupant hz
  · exact hst.slotDepth_le_depthCap hz
private theorem ValidState.put {f : α → Fin (2 ^ P.hashBits)} {st : State P α}
    (hst : P.ValidState f st) {r : Fin P.slotCount} {y : α}
    (hy : ∀ r', st.assignment.occupant r' ≠ some y) {d : Fin (P.depth + 1)}
    (hr_bin : P.InBin (f y) d r) (hd_cap : d ≤ P.depthCap (f y)) :
    P.ValidState f (st.put r y d) := by
  constructor <;> intro r' z hz <;>
    simp only [State.put, st.assignment.occupant_put_of_absent r hy] at hz ⊢ <;>
    rcases eq_or_ne r' r with rfl | hr'
  · rw [Function.update_self] at hz ⊢; cases hz; exact hr_bin
  · rw [Function.update_of_ne hr'] at hz ⊢; exact hst.inBin_of_occupant hz
  · rw [Function.update_self] at hz ⊢; cases hz; exact hd_cap
  · rw [Function.update_of_ne hr'] at hz ⊢; exact hst.slotDepth_le_depthCap hz
theorem ValidState.ballProbeComplexity_le {f : α → Fin (2 ^ P.hashBits)} {st : State P α}
    (hst : P.ValidState f st) {x : α} {d : Fin (P.depth + 1)} (hd : st.assignedDepth x = some d) :
    ballProbeComplexity (P.probeSeq f) st.assignment x ≤ 1 + P.binExp d := by
  obtain ⟨r, hr_slot, rfl⟩ := Option.map_eq_some_iff.mp hd
  rw [ballProbeComplexity_of_slotOf_eq_some _ hr_slot]
  exact slotProbeComplexity_xorProbeSeq_le_of_div_eq P.slotBits _ x
    (hst.inBin_of_occupant ((st.assignment.slotOf_eq_some_iff x r).mp hr_slot))
private theorem binSaturated_eq_false_of_le_greedyUnsatDepth (P : Params) (st : State P α)
    (hx : Fin (2 ^ P.hashBits)) (hlt : #st.assignment.present < P.slotCount)
    {i : Fin (P.depth + 1)} (hi : i ≤ P.greedyUnsatDepth st hx) :
    P.binSaturated st hx i = false := by
  refine Fin.cases (fun _ => ?_) (fun i' hi' => ?_) i hi
  · obtain ⟨r, hr⟩ := st.assignment.card_present_lt_iff_freeSlots_nonempty.mp hlt
    have hnone := (Finset.mem_filter.mp hr).2; by_contra hsat
    have hall := (P.binSaturated_eq_true_iff st hx _).mp (Bool.eq_true_of_not_eq_false hsat) r
      (P.inBin_zero hx r)
    cases hocc : st.assignment.occupant r <;> simp [hocc] at hnone hall
  · unfold greedyUnsatDepth at hi'
    cases hf : Fin.find? (n := P.depth) (fun d => P.binSaturated st hx d.succ) with
    | none => exact Fin.find?_eq_none_iff.mp hf i'
    | some d =>
      rw [hf] at hi'; by_contra hne; exact (Fin.mem_find?_iff.mp (Option.mem_def.mpr hf)).2 i'
        (Fin.lt_def.mpr (by simpa using Fin.le_def.mp hi')) (Bool.eq_true_of_not_eq_false hne)
/-- Fuel-bounded priority-kick loop placing ball `y` at depth `d`. -/
@[expose] def kickPlaceAux (P : Params) (f : α → Fin (2 ^ P.hashBits)) :
    ℕ → State P α → α → Fin (P.depth + 1) → State P α
  | 0, st, _, _ => st
  | fuel + 1, st, y, d => match P.findFree st (f y) d with
    | some r => st.put r y d
    | none => match P.findKick st (f y) d with
      | none => st
      | some r => match st.assignment.occupant r with
        | none => st.put r y d
        | some y' => P.kickPlaceAux f fuel (st.put r y d) y' (st.slotDepth r)
/-- Insert ball `x` into `st` under hash `f` via priority kicks. -/
@[expose] def insert (P : Params) (f : α → Fin (2 ^ P.hashBits)) (st : State P α) (x : α) :
    State P α := match st.assignment.slotOf x with
  | some _ => st
  | none => if #st.assignment.present < P.slotCount then
      let d₀ := min (P.greedyUnsatDepth st (f x)) (P.depthCap (f x))
      P.kickPlaceAux f (d₀.val + 1) st x d₀ else st
/-- Single-step execution of a balls-to-slots operation on a `k`-kick tree. -/
@[expose] def step (P : Params) (f : α → Fin (2 ^ P.hashBits)) (st : State P α) :
    (o : Op α) → State P α × o.Result P.slotCount
  | .insert x => (P.insert f st x, ()) | .delete x => (st.delete x, ())
  | .query x => (st, st.query x)
/-- Execute an operation sequence `ops` from `State.empty P α` under hash `f`. -/
@[expose] def run (P : Params) (f : α → Fin (2 ^ P.hashBits)) (ops : List (Op α)) : State P α :=
  ops.foldl (fun st o => (P.step f st o).1) (State.empty P α)
private theorem kickPlaceAux_spec (P : Params) (f : α → Fin (2 ^ P.hashBits)) :
    ∀ (fuel : ℕ) (st : State P α) (y : α) (d : Fin (P.depth + 1)),
      (∀ r', st.assignment.occupant r' ≠ some y) → d.val < fuel → P.ValidState f st →
      d ≤ P.depthCap (f y) → (∀ i ≤ d, P.binSaturated st (f y) i = false) →
      let res := P.kickPlaceAux f fuel st y d
      P.ValidState f res ∧ res.assignment.present = Insert.insert y st.assignment.present ∧
      res.assignedDepth y = some d ∧
      (∀ z ∈ st.assignment.present, res.assignedDepth z = st.assignedDepth z) ∧
      changedSlots st.assignment res.assignment ≤ d.val + 1 := by
  intro fuel; induction fuel with
  | zero => intro _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro st y d hy hlt hvalid hd_cap hunsat; simp only [kickPlaceAux]
    have hne_y {z} (hz : z ∈ st.assignment.present) : z ≠ y := fun heq => by
      obtain ⟨rz, hrz⟩ := (st.assignment.mem_present_iff _).mp hz; exact hy rz (heq ▸ hrz)
    cases hfree : P.findFree st (f y) d with
    | some r =>
      have hf := Fin.eq_true_of_find?_eq_some hfree
      simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isNone_iff_eq_none] at hf
      exact ⟨hvalid.put hy hf.1 hd_cap, st.assignment.present_put_of_isNone hf.2 y,
        st.assignedDepth_put_self r y d,
        fun z hz => st.assignedDepth_put_of_ne r y d (hne_y hz) (by simp [hf.2]),
        (st.assignment.changedSlots_put_le r hy).trans (by omega)⟩
    | none =>
      have hsat_d := hunsat d le_rfl
      cases hkick : P.findKick st (f y) d with
      | none => simp [binSaturated, hfree, hkick] at hsat_d
      | some r =>
        have hk := Fin.eq_true_of_find?_eq_some hkick
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
        cases hocc : st.assignment.occupant r with
        | none => have hf_none := Fin.find?_eq_none_iff.mp hfree r; simp [hk.1, hocc] at hf_none
        | some y' =>
          dsimp only; simp only [hocc]; set d' := st.slotDepth r; set mid := st.put r y d
          have hmid_unsat (i) (hi : i ≤ d') : P.binSaturated mid (f y') i = false := by
            have hid := hi.trans hk.2.le
            have hbin_eq := inBin_iff_of_inBin ((hvalid.inBin_of_occupant hocc).mono hi)
              (hk.1.mono hid)
            by_contra hne
            have hall_mid := (P.binSaturated_eq_true_iff mid (f y') i).mp
              (Bool.eq_true_of_not_eq_false hne)
            exact absurd ((P.binSaturated_eq_true_iff st (f y) i).mpr fun r' hr' => by
              rcases eq_or_ne r' r with rfl | hr'r
              · exact ⟨by simp [hocc], hi⟩
              · simpa only [mid, State.put, st.assignment.occupant_put_of_absent r hy,
                  Function.update_of_ne hr'r] using hall_mid r' ((hbin_eq r').mpr hr'))
              (by simp [hunsat i hid])
          have ⟨hres_val, hres_pres, hres_y', hres_keep, hres_chg⟩ :=
            ih mid y' d' (st.assignment.put_occupant_ne_old hy hocc)
              (by have := Fin.lt_def.mp hk.2; omega)
              (hvalid.put hy hk.1 hd_cap) (hvalid.slotDepth_le_depthCap hocc) hmid_unsat
          have hmid_pres : mid.assignment.present = _ := st.assignment.present_put_of_some hy hocc
          refine ⟨hres_val, ?_, ?_, fun z hz => ?_, ?_⟩
          · rw [hres_pres, hmid_pres, Finset.insert_comm,
              Finset.insert_erase ((st.assignment.mem_present_iff y').mpr ⟨r, hocc⟩)]
          · rw [hres_keep y (by rw [hmid_pres]; simp)]; exact st.assignedDepth_put_self r y d
          · rcases eq_or_ne z y' with rfl | hzy'
            · rw [hres_y']
              simp [State.assignedDepth, (st.assignment.slotOf_eq_some_iff z r).mpr hocc, d']
            · have hz_mid : z ∈ mid.assignment.present := by rw [hmid_pres]; simp [hzy', hz]
              rw [hres_keep z hz_mid]
              exact st.assignedDepth_put_of_ne r y d (hne_y hz)
                (by rw [hocc]; exact fun h => hzy' (Option.some.inj h).symm)
          · have := Fin.lt_def.mp hk.2
            exact (changedSlots_triangle st.assignment mid.assignment _).trans
              ((Nat.add_le_add (st.assignment.changedSlots_put_le r hy) hres_chg).trans (by omega))
private theorem insert_spec (f : α → Fin (2 ^ P.hashBits)) {st : State P α}
    (hst : P.ValidState f st) (x : α) : P.ValidState f (P.insert f st x) ∧
    st.assignment.present ⊆ (P.insert f st x).assignment.present ∧
    (∀ z ∈ st.assignment.present, (P.insert f st x).assignedDepth z = st.assignedDepth z) ∧
    changedSlots st.assignment (P.insert f st x).assignment ≤ P.depth + 1 ∧
    (ValidOp P.slotCount st.assignment.present (.insert x) →
      (P.insert f st x).assignment.present = Insert.insert x st.assignment.present) ∧
    (x ∉ st.assignment.present → #st.assignment.present < P.slotCount →
      (P.insert f st x).assignedDepth x =
        some (min (P.greedyUnsatDepth st (f x)) (P.depthCap (f x)))) := by
  unfold Params.insert; cases hslot : st.assignment.slotOf x with
  | some _ =>
    have hmem := (st.assignment.mem_present_iff_slotOf_isSome x).mpr (by simp [hslot])
    exact ⟨hst, Finset.Subset.refl _, fun _ _ => rfl, by simp,
      fun _ => (Finset.insert_eq_of_mem hmem).symm, fun hx => (hx hmem).elim⟩
  | none =>
    have hnmem : x ∉ st.assignment.present := fun hm => by
      simpa [hslot] using (st.assignment.mem_present_iff_slotOf_isSome x).mp hm
    split_ifs with hlt
    · obtain ⟨h1, h2, h3, h4, h5⟩ := P.kickPlaceAux_spec f _ st x _
        ((st.assignment.slotOf_eq_none_iff x).mp hslot) (Nat.lt_succ_self _) hst (min_le_right _ _)
        fun i hi => P.binSaturated_eq_false_of_le_greedyUnsatDepth st (f x) hlt
          (hi.trans (min_le_left _ _))
      exact ⟨h1, h2 ▸ Finset.subset_insert _ _, h4, h5.trans (by omega), fun _ => h2, fun _ _ => h3⟩
    · exact ⟨hst, Finset.Subset.refl _, fun _ _ => rfl, by simp,
        fun hv => (hlt (hv.resolve_right hnmem)).elim, fun _ h => (hlt h).elim⟩
/-- Priority-kick insertion preserves `ValidState`. -/
theorem ValidState.insert {f : α → Fin (2 ^ P.hashBits)} {st : State P α}
    (hst : P.ValidState f st) (x : α) : P.ValidState f (P.insert f st x) := (insert_spec f hst x).1
/-- **Kick-depth invariance**: inserting `x` preserves `assignedDepth` for every present ball. -/
theorem assignedDepth_insert_of_mem (P : Params) (f : α → Fin (2 ^ P.hashBits)) {st : State P α}
    (hst : P.ValidState f st) (x : α) {z : α} (hz : z ∈ st.assignment.present) :
    (P.insert f st x).assignedDepth z = st.assignedDepth z := (insert_spec f hst x).2.2.1 z hz
/-- **Deterministic worst-case switching cost `≤ P.depth + 1`** per insertion. -/
theorem switchingCost_insert_le (P : Params) (f : α → Fin (2 ^ P.hashBits)) {st : State P α}
    (hst : P.ValidState f st) (x : α) :
    switchingCost st.assignment (P.insert f st x).assignment ≤ P.depth + 1 :=
  (switchingCost_le_changedSlots_of_subset (insert_spec f hst x).2.1).trans
    (insert_spec f hst x).2.2.2.1
/-- Every insertion displaces at most `P.depth` already-present balls. -/
theorem displacedBalls_insert_le (P : Params) (f : α → Fin (2 ^ P.hashBits)) {st : State P α}
    (hst : P.ValidState f st) (x : α) :
    displacedBalls st.assignment (P.insert f st x).assignment ≤ P.depth := by
  by_cases h : x ∉ st.assignment.present ∧ #st.assignment.present < P.slotCount
  · have hnew := (insert_spec f hst x).2.2.2.2.1 (Or.inl h.2) ▸ Finset.mem_insert_self x _
    have := displacedBalls_add_one_le_switchingCost h.1 hnew
    have := P.switchingCost_insert_le f hst x; omega
  · unfold Params.insert; cases hs : st.assignment.slotOf x with
    | some _ => simp [displacedBalls]
    | none =>
      have hnlt : ¬ #st.assignment.present < P.slotCount := fun hlt => h
        ⟨fun hm => by simpa [hs] using (st.assignment.mem_present_iff_slotOf_isSome x).mp hm, hlt⟩
      simp [hnlt, displacedBalls]
theorem ValidState.step {f : α → Fin (2 ^ P.hashBits)} {st : State P α}
    (hst : P.ValidState f st) (o : Op α) : P.ValidState f (P.step f st o).1 := by
  cases o with
  | insert x => exact hst.insert x | delete x => exact hst.delete x | query _ => exact hst
private theorem foldl_step_spec (f : α → Fin (2 ^ P.hashBits)) :
    ∀ (l : List (Op α)) {st : State P α}, P.ValidState f st →
      let res := l.foldl (fun s o => (P.step f s o).1) st
      P.ValidState f res ∧
      (ValidOpSeqFrom P.slotCount st.assignment.present l →
        res.assignment.present = activeSetFrom st.assignment.present l) ∧
      (∀ x ∈ st.assignment.present, (∀ o ∈ l, o ≠ .delete x) →
        res.assignedDepth x = st.assignedDepth x) := by
  intro l; induction l with
  | nil => intro st hst; exact ⟨hst, fun _ => rfl, fun _ _ _ => rfl⟩
  | cons o l ih =>
    intro st hst; obtain ⟨h1, h2, h3⟩ := ih (hst.step o)
    refine ⟨h1, fun hv => ?_, fun x hx hl => ?_⟩
    · have hp : (P.step f st o).1.assignment.present = stepSet st.assignment.present o := by
        cases o with
        | insert w => exact (insert_spec f hst w).2.2.2.2.1 hv.1
        | delete w => exact st.assignment.present_delete w | query _ => rfl
      rw [List.foldl_cons, activeSetFrom_cons, ← hp]; exact h2 (hp.symm ▸ hv.2)
    · have hstep : x ∈ (P.step f st o).1.assignment.present ∧
          (P.step f st o).1.assignedDepth x = st.assignedDepth x := by
        cases o with
        | insert w => exact ⟨(insert_spec f hst w).2.1 hx, P.assignedDepth_insert_of_mem f hst w hx⟩
        | delete w =>
          have hxw : x ≠ w := fun h => hl (.delete w) List.mem_cons_self (h ▸ rfl)
          exact ⟨by simp [Params.step, State.delete, hxw, hx], st.assignedDepth_delete_of_ne hxw⟩
        | query _ => exact ⟨hx, rfl⟩
      rw [List.foldl_cons, h3 x hstep.1 fun o' ho' => hl o' (List.mem_cons_of_mem o ho'), hstep.2]
/-- Executing any operation sequence from `State.empty` maintains `ValidState`. -/
theorem ValidState.run (P : Params) (f : α → Fin (2 ^ P.hashBits)) (ops : List (Op α)) :
    P.ValidState f (P.run f ops) := (foldl_step_spec f ops (ValidState.empty P f)).1
theorem present_run (P : Params) (f : α → Fin (2 ^ P.hashBits)) {ops : List (Op α)}
    (hval : ValidOpSeq P.slotCount ops) : (P.run f ops).assignment.present = activeSet ops := by
  have hemp : (State.empty P α).assignment.present = ∅ := SlotAssignment.present_empty α P.slotCount
  simpa only [Params.run, activeSet, hemp] using
    (foldl_step_spec f ops (ValidState.empty P f)).2.1 (by rwa [hemp])
theorem assignedDepth_run_of_split (P : Params) (f : α → Fin (2 ^ P.hashBits))
    {ops pre suf : List (Op α)} {x : α} (heq : ops = pre ++ .insert x :: suf)
    (hpre : ValidOpSeq P.slotCount pre) (hx : x ∉ activeSet pre)
    (hlt : #(activeSet pre) < P.slotCount) (hsuf : ∀ o ∈ suf, o ≠ .delete x) :
    (P.run f ops).assignedDepth x =
      some (min (P.greedyUnsatDepth (P.run f pre) (f x)) (P.depthCap (f x))) := by
  have hst_pre := ValidState.run P f pre; have hpres_pre := P.present_run f hpre
  have hrun : P.run f ops = suf.foldl (fun s o => (P.step f s o).1) (P.insert f (P.run f pre) x) :=
    by subst heq; simp only [Params.run, List.foldl_append, List.foldl_cons]; rfl
  rw [hrun, (foldl_step_spec f suf (hst_pre.insert x)).2.2 x
    ((insert_spec f hst_pre x).2.2.2.2.1 (Or.inl (hpres_pre ▸ hlt)) ▸
      Finset.mem_insert_self _ _) hsuf]
  exact (insert_spec f hst_pre x).2.2.2.2.2 (hpres_pre ▸ hx) (hpres_pre ▸ hlt)
/-- Every admissible step of `P.step` refines `BallsToSlots.schemeSpec` with switching cost
`≤ P.depth + 1`. -/
theorem step_schemeSpec (P : Params) (f : α → Fin (2 ^ P.hashBits)) {st : State P α}
    (hst : P.ValidState f st) {o : Op α} (hval : ValidOp P.slotCount st.assignment.present o) :
    (schemeSpec α P.slotCount P.slotCount (P.depth + 1) (P.probeSeq f)).step
      st.assignment o (P.step f st o).1.assignment (P.step f st o).2 := by
  refine ⟨(hst.step o).respectsProbeSeq, ?_, ?_⟩ <;> cases o
  · exact P.switchingCost_insert_le f hst _
  · exact (st.assignment.switchingCost_delete_le _).trans (by omega)
  · simp [Params.step]
  · exact (insert_spec f hst _).2.2.2.2.1 hval
  · exact st.assignment.present_delete _
  · exact ⟨rfl, rfl⟩
end Decidable
/-- Number of balls in `S` landing in the depth-`d` bin of `hx` with depth cap `≥ d`. -/
def binLoad {α : Type*} (P : Params) (f : α → Fin (2 ^ P.hashBits)) (S : Finset α)
    (hx : Fin (2 ^ P.hashBits)) (d : Fin (P.depth + 1)) : ℕ :=
  #{y ∈ S | P.InBin (f y) d (P.preferredSlot hx) ∧ d ≤ P.depthCap (f y)}
theorem binSize_le_binLoad_of_binSaturated {α : Type*} [DecidableEq α] {P : Params}
    {f : α → Fin (2 ^ P.hashBits)} {st : State P α} (hst : P.ValidState f st) {S : Finset α}
    (hS : st.assignment.present = S) (hx : Fin (2 ^ P.hashBits)) {d : Fin (P.depth + 1)}
    (hsat : P.binSaturated st hx d = true) : P.binSize d ≤ P.binLoad f S hx d := by
  have hB : #{r : Fin P.slotCount | P.InBin hx d r} = P.binSize d :=
    card_fin_div_two_pow_eq (P.binExp_le_slotBits d) (P.preferredSlot hx)
  obtain ⟨r₀, hr₀⟩ := Finset.card_pos.mp (hB.symm ▸ P.binSize_pos d)
  have hall := (P.binSaturated_eq_true_iff st hx d).mp hsat
  obtain ⟨x₀, _⟩ := Option.isSome_iff_exists.mp (hall r₀ (Finset.mem_filter.mp hr₀).2).1
  rw [← hB]; refine Finset.card_le_card_of_injOn (fun r => (st.assignment.occupant r).getD x₀) ?_ ?_
  · intro r hr; rw [Finset.mem_coe, Finset.mem_filter] at hr ⊢
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (hall r hr.2).1
    have hd_le := (hall r hr.2).2; simp only [hy, Option.getD_some]
    exact ⟨hS ▸ (st.assignment.mem_present_iff y).mpr ⟨r, hy⟩,
      (inBin_iff_of_inBin ((hst.inBin_of_occupant hy).mono hd_le) hr.2 _).mpr rfl,
      hd_le.trans (hst.slotDepth_le_depthCap hy)⟩
  · intro r₁ hr₁ r₂ hr₂ heq; rw [Finset.mem_coe, Finset.mem_filter] at hr₁ hr₂
    obtain ⟨y₁, hy₁⟩ := Option.isSome_iff_exists.mp (hall r₁ hr₁.2).1
    obtain ⟨y₂, hy₂⟩ := Option.isSome_iff_exists.mp (hall r₂ hr₂.2).1
    simp only [hy₁, hy₂, Option.getD_some] at heq; subst heq; exact st.assignment.injective hy₁ hy₂
/-- Insertion-time active-set upper bound on `x`'s probe complexity: depends only on the hash
values on `insert x S`, independent of slot layout and of later operations not deleting `x`. -/
def snapshotProbeBound {α : Type*} (P : Params) (f : α → Fin (2 ^ P.hashBits)) (S : Finset α)
    (x : α) : ℕ :=
  min (1 + P.slotBits) (1 + P.binExp (Fin.last P.depth) + ∑ i : Fin P.depth,
    if P.binSize i.succ ≤ P.binLoad f S (f x) i.succ ∨ (P.depthCap (f x)).val < i.val + 1 then
      P.binExp i.castSucc else 0)
theorem snapshotProbeBound_le {α : Type*} (P : Params) (f : α → Fin (2 ^ P.hashBits))
    (S : Finset α) (x : α) : P.snapshotProbeBound f S x ≤ 1 + P.slotBits := min_le_left _ _
theorem snapshotProbeBound_congr {α : Type*} [DecidableEq α] (P : Params)
    {f₁ f₂ : α → Fin (2 ^ P.hashBits)} {S : Finset α} {x : α}
    (heq : ∀ a ∈ Insert.insert x S, f₁ a = f₂ a) :
    P.snapshotProbeBound f₁ S x = P.snapshotProbeBound f₂ S x := by
  have hx := heq x (Finset.mem_insert_self x S)
  have hload (d) : P.binLoad f₁ S (f₁ x) d = P.binLoad f₂ S (f₂ x) d := by
    unfold binLoad; rw [hx]; congr 1
    exact Finset.filter_congr fun y hy => by rw [heq y (Finset.mem_insert_of_mem hy)]
  unfold snapshotProbeBound; congr 2; exact Finset.sum_congr rfl fun i _ => by rw [hload, hx]
theorem ballProbeComplexity_le_snapshotProbeBound {α : Type*} [DecidableEq α] {P : Params}
    {f : α → Fin (2 ^ P.hashBits)} {st st' : State P α} (hst : P.ValidState f st)
    (hst' : P.ValidState f st') {S : Finset α} (hS : st.assignment.present = S) {x : α}
    (hd : st'.assignedDepth x = some (min (P.greedyUnsatDepth st (f x)) (P.depthCap (f x)))) :
    ballProbeComplexity (P.probeSeq f) st'.assignment x ≤ P.snapshotProbeBound f S x := by
  refine (hst'.ballProbeComplexity_le hd).trans (le_min (Nat.add_le_add_left
    (P.binExp_le_slotBits _) 1) ?_)
  set d := min (P.greedyUnsatDepth st (f x)) (P.depthCap (f x))
  by_cases hlast : d.val = P.depth
  · rw [show d = Fin.last P.depth from Fin.ext hlast]; exact Nat.le_add_right _ _
  · let i₀ : Fin P.depth := ⟨d.val, by have := d.isLt; omega⟩
    have hor : P.binSize i₀.succ ≤ P.binLoad f S (f x) i₀.succ ∨
        (P.depthCap (f x)).val < i₀.val + 1 := by
      have hm : d.val = min (P.greedyUnsatDepth st (f x)).val (P.depthCap (f x)).val := rfl
      rcases (by dsimp only [i₀]; omega :
        (P.greedyUnsatDepth st (f x)).val = i₀.val ∨ (P.depthCap (f x)).val < i₀.val + 1) with
        hg | hc
      · unfold greedyUnsatDepth at hg
        cases hf : Fin.find? (n := P.depth) (fun d => P.binSaturated st (f x) d.succ) with
        | none => rw [hf, Fin.val_last] at hg; exact absurd hg.symm (ne_of_lt i₀.isLt)
        | some _ =>
          rw [hf, Fin.val_castSucc] at hg; cases Fin.ext hg
          exact Or.inl (P.binSize_le_binLoad_of_binSaturated hst hS (f x)
            (Fin.eq_true_of_find?_eq_some (p := fun d => P.binSaturated st (f x) d.succ) hf))
      · exact Or.inr hc
    have hle := Finset.single_le_sum (f := fun i : Fin P.depth =>
      if P.binSize i.succ ≤ P.binLoad f S (f x) i.succ ∨ (P.depthCap (f x)).val < i.val + 1 then
        P.binExp i.castSucc else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i₀)
    simp only [hor, ↓reduceIte] at hle; rw [show d = i₀.castSucc from Fin.ext rfl]; omega
/-- Under `1`-wise independence, `Pr[depthCap (h θ x) < i + 1] = 1 / 2 ^ P.capExp i`. -/
theorem dens_depthCap_lt_succ {ι α : Type*} [Fintype ι] {k_indep : ℕ} {P : Params}
    {h : ι → α → Fin (2 ^ P.hashBits)} (hh : IsKWiseIndependentHash k_indep h)
    (hk : 1 ≤ k_indep) (x : α) (i : Fin P.depth) :
    (dens {θ : ι | (P.depthCap (h θ x)).val < i.val + 1} : ℝ) = 1 / (2 ^ P.capExp i : ℝ) := by
  have : Nonempty (Fin P.slotCount) := ⟨⟨0, P.slotCount_pos⟩⟩
  have h1 := (hh.mono hk).expect_prod (T := {x}) (by simp)
    (fun _ hx => if (P.depthCap hx).val < i.val + 1 then (1 : ℝ) else 0)
  simp only [Finset.prod_singleton, Fintype.expect_boole] at h1
  rw [h1, ← Fintype.expect_boole, Fintype.expect_equiv P.hashEquiv _
    (fun p : Fin P.slotCount × Fin (2 ^ P.capBits) =>
      if p.2.val % 2 ^ P.capExp i = 0 then (1 : ℝ) else 0)
    (fun hx => by simp only [P.depthCap_lt_succ_iff]; rfl), Fintype.expect_prod_type]
  simp only [Fintype.expect_const, expect_fin_mod_two_pow_eq_zero (P.capExp_le_capBits i)]
private theorem expect_inBin_and_le_depthCap (P : Params) (i : Fin P.depth) (r₀ : Fin P.slotCount) :
    𝔼 hx : Fin (2 ^ P.hashBits),
      (if P.InBin hx i.succ r₀ ∧ i.succ ≤ P.depthCap hx then (1 : ℝ) else 0) =
      ((P.binSize i.succ : ℝ) / P.slotCount) * (1 - 1 / (2 ^ P.capExp i : ℝ)) := by
  let f₁ (p₁ : Fin P.slotCount) : ℝ :=
    if p₁.val / P.binSize i.succ = r₀.val / P.binSize i.succ then 1 else 0
  let f₂ (p₂ : Fin (2 ^ P.capBits)) : ℝ := 1 - if p₂.val % 2 ^ P.capExp i = 0 then 1 else 0
  have hpt (hx : Fin (2 ^ P.hashBits)) :
      (if P.InBin hx i.succ r₀ ∧ i.succ ≤ P.depthCap hx then (1 : ℝ) else 0) =
      f₁ (P.preferredSlot hx) * f₂ (P.capHash hx) := by
    have hiff : i.succ ≤ P.depthCap hx ↔ ¬ (P.capHash hx).val % 2 ^ P.capExp i = 0 := by
      rw [← P.depthCap_lt_succ_iff, Fin.le_def, Fin.val_succ, not_lt]
    simp only [InBin, @eq_comm ℕ (r₀.val / _), hiff, f₁, f₂]
    by_cases h1 : (P.preferredSlot hx).val / P.binSize i.succ = r₀.val / P.binSize i.succ <;>
      by_cases h2 : (P.capHash hx).val % 2 ^ P.capExp i = 0 <;> simp [h1, h2]
  rw [Fintype.expect_equiv P.hashEquiv _ (fun p => f₁ p.1 * f₂ p.2) hpt, Fintype.expect_prod_type]
  have hf₂ : (𝔼 p₂, f₂ p₂) = 1 - 1 / (2 ^ P.capExp i : ℝ) := by
    dsimp only [f₂]; rw [Finset.expect_sub_distrib, Fintype.expect_const,
      expect_fin_mod_two_pow_eq_zero (P.capExp_le_capBits i)]
  simp_rw [← Finset.mul_expect, hf₂]; rw [← Finset.expect_mul]; dsimp only [f₁]
  rw [Fintype.expect_boole, Finset.dens_eq_card_div_card,
    card_fin_div_two_pow_eq (P.binExp_le_slotBits i.succ) r₀, Fintype.card_fin]; push_cast; rfl
/-- Under `(2m + 1)`-wise independence (`1 ≤ m`), `Pr[binLoad ≥ binSize]` at depth `i + 1` is at
most `2 * (3 * m * 2 ^ (2 * capExp i) / binSize (i + 1)) ^ m`. -/
theorem dens_binLoad_ge_le_pow {ι α : Type*} [Fintype ι] {m k_indep : ℕ} (hm : 1 ≤ m) {P : Params}
    {h : ι → α → Fin (2 ^ P.hashBits)} (hh : IsKWiseIndependentHash k_indep h)
    (hk : 2 * m + 1 ≤ k_indep) {S : Finset α} (hS_le : #S ≤ P.slotCount) {x : α} (hx : x ∉ S)
    (i : Fin P.depth) : (dens {θ : ι | P.binSize i.succ ≤ P.binLoad (h θ) S (h θ x) i.succ} : ℝ) ≤
      2 * (3 * (m : ℝ) * (2 ^ (2 * P.capExp i) : ℝ) / P.binSize i.succ) ^ m := by
  classical
  have : Nonempty (Fin (2 ^ P.hashBits)) := ⟨⟨0, by positivity⟩⟩
  by_cases hm_bin : 2 * (m : ℝ) ≤ 3 * (P.binSize i.succ : ℝ)
  · refine dens_le_of_hash_fiber (hh.mono hk) x _ fun v₀ _ hsub_ind => ?_
    let f_emb (y : {y : α // y ∈ S}) : {y : α // y ≠ x} := ⟨y.1, fun heq => hx (heq ▸ y.2)⟩
    let R : Finset {y : α // y ≠ x} :=
      S.attach.map ⟨f_emb, fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩
    let g (_ : {y : α // y ≠ x}) (hx' : Fin (2 ^ P.hashBits)) : ℝ :=
      if P.InBin hx' i.succ (P.preferredSlot v₀) ∧ i.succ ≤ P.depthCap hx' then 1 else 0
    have h0 : 0 ≤ ((P.binSize i.succ : ℝ) / P.slotCount) * (1 - 1 / (2 ^ P.capExp i : ℝ)) :=
      mul_nonneg (by positivity)
        (by rw [sub_nonneg, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num))
    have hmean_sub : ∑ z ∈ R, (𝔼 hx', g z hx') ≤
        (P.binSize i.succ : ℝ) - (P.binSize i.succ : ℝ) / (2 ^ P.capExp i : ℝ) := by
      simp only [show ∀ z, 𝔼 hx', g z hx' = _ from
        fun _ => P.expect_inBin_and_le_depthCap i (P.preferredSlot v₀), Finset.sum_const,
        nsmul_eq_mul]
      calc (#R : ℝ) * (((P.binSize i.succ : ℝ) / P.slotCount) * (1 - 1 / 2 ^ P.capExp i))
          ≤ P.slotCount * (((P.binSize i.succ : ℝ) / P.slotCount) * (1 - 1 / 2 ^ P.capExp i)) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (by simpa [R] using hS_le : #R ≤ _)) h0
        _ = (P.binSize i.succ : ℝ) - (P.binSize i.succ : ℝ) / 2 ^ P.capExp i := by
            rw [← mul_assoc, mul_div_cancel₀ _ (by exact_mod_cast P.slotCount_pos.ne')]; ring
    let a : ℝ := (P.binSize i.succ : ℝ) / (2 ^ P.capExp i : ℝ)
    have ha_pos : 0 < a := div_pos (Nat.cast_pos.mpr (P.binSize_pos i.succ)) (by positivity)
    have hconc := dens_abs_sum_sub_expect_le hm hsub_ind R g
      (fun _ _ _ => by dsimp [g]; split_ifs <;> constructor <;> norm_num)
      (hmean_sub.trans (by linarith [ha_pos.le])) hm_bin ha_pos
    have hsub_ev : ({θ : {θ : ι // h θ x = v₀} |
        P.binSize i.succ ≤ P.binLoad (h θ.1) S (h θ.1 x) i.succ} : Finset _) ⊆
        ({θ : {θ : ι // h θ x = v₀} |
          a ≤ |∑ z ∈ R, (g z (h θ.1 z.1) - 𝔼 hx', g z hx')|} : Finset _) := by
      intro θ hθ; rw [Finset.mem_filter] at hθ ⊢; refine ⟨Finset.mem_univ _, ?_⟩
      have hload : (P.binLoad (h θ.1) S (h θ.1 x) i.succ : ℝ) = ∑ z ∈ R, g z (h θ.1 z.1) := by
        refine (by rw [Finset.sum_boole, θ.2, binLoad] :
          (P.binLoad (h θ.1) S (h θ.1 x) i.succ : ℝ) = _).trans
          ((Finset.sum_attach S fun y => if P.InBin (h θ.1 y) i.succ (P.preferredSlot v₀) ∧
            i.succ ≤ P.depthCap (h θ.1 y) then (1 : ℝ) else 0).symm.trans ?_)
        exact (Finset.sum_map S.attach ⟨f_emb, fun _ _ h => Subtype.ext (Subtype.mk.inj h)⟩
          fun z => g z (h θ.1 z.1)).symm
      rw [Finset.sum_sub_distrib]
      exact (by linarith [show (P.binSize i.succ : ℝ) ≤ ∑ z ∈ R, g z (h θ.1 z.1) from
        hload ▸ Nat.cast_le.mpr hθ.2] : a ≤ _).trans (le_abs_self _)
    refine (show (dens _ : ℝ) ≤ dens _ by exact_mod_cast Finset.dens_le_dens hsub_ev).trans
      (hconc.trans_eq ?_)
    have hb_ne : (P.binSize i.succ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (P.binSize_pos i.succ).ne'
    congr 2; dsimp only [a]; rw [div_pow, ← pow_mul, mul_comm (P.capExp i) 2]; field_simp [hb_ne]
  · have hbase_ge : 1 ≤ 3 * (m : ℝ) * (2 ^ (2 * P.capExp i) : ℝ) / P.binSize i.succ := by
      rw [one_le_div (Nat.cast_pos.mpr (P.binSize_pos i.succ))]
      nlinarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := 2 * P.capExp i),
        (show (1 : ℝ) ≤ m by exact_mod_cast hm)]
    have : Nonempty ι := hh.nonempty; exact (show (dens _ : ℝ) ≤ 1 by
      exact_mod_cast Finset.dens_le_one).trans (by linarith [one_le_pow₀ hbase_ge (n := m)])
/-- Under `(2m + 1)`-wise independence (`1 ≤ m`), `Pr[binSaturated (st θ) (h θ x) (i + 1)]` is at
most `2 * (3 * m * 2 ^ (2 * capExp i) / binSize (i + 1)) ^ m` (giving `6 * 2 ^ (2 * capExp i) /
binSize (i + 1)` under `3`-wise independence at `m = 1`). -/
theorem dens_binSaturated_le_pow {ι α : Type*} [Fintype ι] [DecidableEq α] {m k_indep : ℕ}
    (hm : 1 ≤ m) {P : Params} {h : ι → α → Fin (2 ^ P.hashBits)}
    (hh : IsKWiseIndependentHash k_indep h) (hk : 2 * m + 1 ≤ k_indep) {st : ι → State P α}
    (hst : ∀ θ, P.ValidState (h θ) (st θ)) {S : Finset α} (hS : ∀ θ, (st θ).assignment.present = S)
    {x : α} (hx : x ∉ S) (i : Fin P.depth) :
    (dens {θ : ι | P.binSaturated (st θ) (h θ x) i.succ = true} : ℝ) ≤
      2 * (3 * (m : ℝ) * (2 ^ (2 * P.capExp i) : ℝ) / P.binSize i.succ) ^ m := by
  classical
  have : Nonempty ι := hh.nonempty; obtain ⟨θ₀⟩ := ‹Nonempty ι›
  exact (show (dens _ : ℝ) ≤ dens {θ : ι | P.binSize i.succ ≤ P.binLoad (h θ) S (h θ x) i.succ} by
    exact_mod_cast Finset.dens_le_dens fun θ hθ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      P.binSize_le_binLoad_of_binSaturated (hst θ) (hS θ) (h θ x)
        (Finset.mem_filter.mp hθ).2⟩).trans
    (P.dens_binLoad_ge_le_pow hm hh hk (hS θ₀ ▸ (st θ₀).assignment.card_present_le) hx i)
end Params
section StandardSchedule
/-- Clamped kick depth `≤ k` (`0` if `m₀ < 32`, else `min k (floorLogStar (2 ^ m₀) - 1)`). -/
@[expose] def effectiveDepth (m₀ k : ℕ) : ℕ :=
  if m₀ < 32 then 0 else min k (Nat.floorLogStar (2 ^ m₀) - 1)
theorem effectiveDepth_le (m₀ k : ℕ) : effectiveDepth m₀ k ≤ k := by
  unfold effectiveDepth; split_ifs <;> [exact Nat.zero_le k; exact min_le_left _ _]
/-- Canonical `k`-kick tree parameters ([BenderFarachColtonKuszmaulKuszmaulLiu2022], §3.1).
Rounds the paper's schedule `s_d ≈ (log^(d) n)^6` and `Pr[depthCap < i + 1] ≈ (log^(i+1) n)^(-2)`
to powers of two via `capExp i = 2 * iterLog (i + 2) (2 ^ m₀)` and
`binExp (i + 1) = 6 * iterLog (i + 2) (2 ^ m₀)` (the `+2` offset aligns 0-based `Fin` indexing with
`Nat.iterLog`, where `iterLog 1 (2 ^ m₀) = m₀`). Under 3-wise independence, the Chebyshev ratio
`L^4 / L^6 = 1 / L^2` gives a failure bound
`6 * 2 ^ (2 * capExp i) / 2 ^ (binExp (i + 1)) = 6 / 2 ^ (2 * iterLog (i + 2) (2 ^ m₀))`
that decays geometrically against `binExp i ≤ 12 * 2 ^ (iterLog (i + 2) (2 ^ m₀))`, preserving the
`O(max (Nat.iterLog (k + 1) (2 ^ m₀)) 1)` bottom-level bound up to an `O(1)` geometric series. -/
@[expose] def standardParams (m₀ k : ℕ) : Params where
  slotBits := m₀; depth := effectiveDepth m₀ k
  capBits := if effectiveDepth m₀ k = 0 then 0 else 2 * Nat.iterLog 2 (2 ^ m₀)
  binExp d := if d.val = 0 then m₀ else 6 * Nat.iterLog (d.val + 1) (2 ^ m₀)
  capExp i := 2 * Nat.iterLog (i.val + 2) (2 ^ m₀); binExp_zero := rfl
  binExp_antitone i j hij := by
    by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;> simp only [hi, hj, ↓reduceIte]
    · exact le_rfl
    · have hm₀ : 32 ≤ m₀ := by
        by_contra hlt; have : effectiveDepth m₀ k = 0 := by simp [effectiveDepth, hlt]
        have := j.isLt; omega
      exact (Nat.mul_le_mul_left 6 (Nat.iterLog_anti_left _ (by omega))).trans
        (Nat.six_mul_iterLog_two_two_pow_le hm₀)
    · have := Fin.le_def.mp hij; omega
    · exact Nat.mul_le_mul_left 6 (Nat.iterLog_anti_left _ (by have := Fin.le_def.mp hij; omega))
  capExp_antitone _ _ hij :=
    Nat.mul_le_mul_left 2 (Nat.iterLog_anti_left _ (by have := Fin.le_def.mp hij; omega))
  capExp_le_capBits i := by
    have hne : effectiveDepth m₀ k ≠ 0 := by have := i.isLt; omega
    simp only [hne, ↓reduceIte]; exact Nat.mul_le_mul_left 2 (Nat.iterLog_anti_left _ (by omega))
/-- Insert `x` under `standardParams m₀ k`. -/
@[expose] def standardInsert {α : Type*} [DecidableEq α] (m₀ k : ℕ)
    (f : α → Fin (2 ^ (standardParams m₀ k).hashBits)) (st : State (standardParams m₀ k) α)
    (x : α) : State (standardParams m₀ k) α := (standardParams m₀ k).insert f st x
/-- Execute `ops` from empty state under `standardParams m₀ k`. -/
@[expose] def standardRun {α : Type*} [DecidableEq α] (m₀ k : ℕ)
    (f : α → Fin (2 ^ (standardParams m₀ k).hashBits)) (ops : List (Op α)) :
    State (standardParams m₀ k) α := (standardParams m₀ k).run f ops
/-- Worst-case switching cost of `standardInsert m₀ k` is at most `k + 1`. -/
theorem switchingCost_standardInsert_le {α : Type*} [DecidableEq α] (m₀ k : ℕ)
    (f : α → Fin (2 ^ (standardParams m₀ k).hashBits)) {st : State (standardParams m₀ k) α}
    (hst : (standardParams m₀ k).ValidState f st) (x : α) :
    switchingCost st.assignment (standardInsert m₀ k f st x).assignment ≤ k + 1 :=
  ((standardParams m₀ k).switchingCost_insert_le f hst x).trans
    (Nat.add_le_add_right (effectiveDepth_le m₀ k) 1)
/-- Schedule inequality on `standardParams m₀ k` ([BenderFarachColtonKuszmaulKuszmaulLiu2022] §3.1,
printed p. 9 / PDF p. 10): `effectiveDepth m₀ k - d ≤ binExp d`. -/
theorem depthSteps_le_binExp (m₀ k : ℕ) (d : Fin ((standardParams m₀ k).depth + 1)) :
    effectiveDepth m₀ k - d.val ≤ (standardParams m₀ k).binExp d := by
  by_cases hD : effectiveDepth m₀ k = 0; · omega
  have hm₀ : 32 ≤ m₀ := by by_contra hlt; exact hD (by simp [effectiveDepth, hlt])
  have hlt_star : effectiveDepth m₀ k < Nat.floorLogStar (2 ^ m₀) := by
    have := Nat.four_le_floorLogStar_two_pow hm₀; have : ¬ m₀ < 32 := by omega
    unfold effectiveDepth; simp only [this, ↓reduceIte]; omega
  have hsub := Nat.sub_le_iterLog_of_lt_floorLogStar (r := d.val) hlt_star
    (by have := d.isLt; change d.val < effectiveDepth m₀ k + 1 at this; omega)
  dsimp only [standardParams]; split_ifs with hd0
  · rw [hd0] at hsub ⊢; simpa [Nat.log_pow Nat.one_lt_two] using Nat.le_of_succ_le hsub
  · omega
theorem expect_snapshotProbeBound_standardParams_le {ι α : Type*} [Fintype ι] {k_indep : ℕ}
    (m₀ k : ℕ) {h : ι → α → Fin (2 ^ (standardParams m₀ k).hashBits)}
    (hh : IsKWiseIndependentHash k_indep h) (hk : 3 ≤ k_indep) {S : Finset α}
    (hS_le : #S ≤ 2 ^ m₀) {x : α} (hx : x ∉ S) :
    𝔼 θ, ((standardParams m₀ k).snapshotProbeBound (h θ) S x : ℝ) ≤
      96 * (max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 : ℝ) := by
  classical
  have : Nonempty ι := hh.nonempty; let P := standardParams m₀ k; let D := effectiveDepth m₀ k
  by_cases hD : D = 0
  · refine ((Finset.expect_le_expect (g := fun _ => (1 + (m₀ : ℝ))) fun θ _ => by
        exact_mod_cast P.snapshotProbeBound_le (h θ) S x).trans_eq
        (Fintype.expect_const (1 + (m₀ : ℝ)))).trans ?_
    by_cases hm₀ : m₀ < 32
    · refine (by have : (m₀ : ℝ) < 32 := by exact_mod_cast hm₀
                 linarith : (1 : ℝ) + m₀ ≤ 96 * 1).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast le_max_right _ 1) (by norm_num))
    · have := Nat.four_le_floorLogStar_two_pow (Nat.not_lt.mp hm₀)
      obtain rfl : k = 0 := by
        have hD' : effectiveDepth m₀ k = 0 := hD
        unfold effectiveDepth at hD'; simp only [hm₀, ↓reduceIte] at hD'; omega
      refine (by have : (1 : ℝ) ≤ m₀ := by exact_mod_cast (by omega : 1 ≤ m₀)
                 linarith : (1 : ℝ) + m₀ ≤ 96 * m₀).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast (by simp [Nat.log_pow Nat.one_lt_two] :
          m₀ ≤ max (Nat.iterLog (0 + 1) (2 ^ m₀)) 1)) (by norm_num))
  · have hm₀ : 32 ≤ m₀ := by by_contra hlt; exact hD (by simp [D, effectiveDepth, hlt])
    have := Nat.four_le_floorLogStar_two_pow hm₀; have hnlt : ¬ m₀ < 32 := by omega
    have hdef : D = min k (Nat.floorLogStar (2 ^ m₀) - 1) := by simp [D, effectiveDepth, hnlt]
    have hlt_star : D < Nat.floorLogStar (2 ^ m₀) := by omega
    let L (r : ℕ) : ℕ := Nat.iterLog r (2 ^ m₀)
    have hLD_le : L (D + 1) ≤ max (L (k + 1)) 1 := by
      rcases le_or_gt k (Nat.floorLogStar (2 ^ m₀) - 1) with hk_le | hk_gt
      · rw [hdef, min_eq_left hk_le]; exact le_max_left _ _
      · rw [hdef, min_eq_right hk_gt.le,
          show Nat.floorLogStar (2 ^ m₀) - 1 + 1 = Nat.floorLogStar (2 ^ m₀) by omega]
        exact (Nat.iterLog_floorLogStar_le_one _).trans (le_max_right _ _)
    let E₁ (i : Fin P.depth) (θ : ι) : Prop := P.binSize i.succ ≤ P.binLoad (h θ) S (h θ x) i.succ
    let E₂ (i : Fin P.depth) (θ : ι) : Prop := (P.depthCap (h θ x)).val < i.val + 1
    let err (i : Fin P.depth) (θ : ι) : ℝ :=
      (P.binExp i.castSucc : ℝ) * ((if E₁ i θ then 1 else 0) + (if E₂ i θ then 1 else 0))
    have hpw (θ : ι) : (P.snapshotProbeBound (h θ) S x : ℝ) ≤
        (1 + 6 * (L (D + 1) : ℝ)) + ∑ i : Fin P.depth, err i θ := by
      have hmin : (P.snapshotProbeBound (h θ) S x : ℝ) ≤ (1 + (P.binExp (Fin.last P.depth) : ℝ)) +
          ∑ i : Fin P.depth, if E₁ i θ ∨ E₂ i θ then (P.binExp i.castSucc : ℝ) else 0 := by
        exact_mod_cast (min_le_right _ _ : P.snapshotProbeBound (h θ) S x ≤ _)
      have hlast_be : P.binExp (Fin.last P.depth) = 6 * L (D + 1) := by
        change (if D = 0 then m₀ else 6 * L (D + 1)) = _; simp [hD]
      have hsum_err : (∑ i : Fin P.depth, if E₁ i θ ∨ E₂ i θ then (P.binExp i.castSucc : ℝ) else 0)
          ≤ ∑ i : Fin P.depth, err i θ := Finset.sum_le_sum fun i _ => by
        dsimp only [err]; by_cases h1 : E₁ i θ <;> by_cases h2 : E₂ i θ <;>
          simp [h1, h2]; linarith [show (0 : ℝ) ≤ P.binExp i.castSucc by positivity]
      rw [hlast_be] at hmin; push_cast at hmin; linarith
    have hterm_le (i : Fin P.depth) : 𝔼 θ, err i θ ≤ 84 * ((1 : ℝ) / 2) ^ (D - i.val) := by
      have hexp_i : 𝔼 θ, err i θ =
          (P.binExp i.castSucc : ℝ) * ((dens {θ | E₁ i θ} : ℝ) + (dens {θ | E₂ i θ} : ℝ)) := by
        dsimp only [err]; rw [← Finset.mul_expect, Finset.expect_add_distrib,
          Fintype.expect_boole, Fintype.expect_boole]
      have hBi : (P.binExp i.castSucc : ℝ) ≤ 12 * (2 : ℝ) ^ L (i.val + 2) := by
        have hlt2 := Nat.lt_pow_succ_log_self Nat.one_lt_two (L (i.val + 1))
        rw [← show L (i.val + 2) = Nat.log 2 (L (i.val + 1)) by simp [L], Nat.pow_succ,
          Nat.mul_comm] at hlt2
        have hle6 : P.binExp i.castSucc ≤ 6 * L (i.val + 1) := by
          change (if i.val = 0 then m₀ else 6 * L (i.val + 1)) ≤ _; split_ifs with hi0
          · rw [hi0, show L (0 + 1) = m₀ by simp [L, Nat.log_pow Nat.one_lt_two]]; omega
          · exact le_rfl
        exact_mod_cast hle6.trans (by omega)
      have hce : P.capExp i = 2 * L (i.val + 2) := rfl
      have hsat_p : (dens {θ | E₁ i θ} : ℝ) ≤ 6 / (2 : ℝ) ^ (2 * L (i.val + 2)) := by
        refine (P.dens_binLoad_ge_le_pow (m := 1) le_rfl hh hk hS_le hx i).trans_eq ?_
        have hbs : P.binSize i.succ = 2 ^ (6 * L (i.val + 2)) := rfl; rw [hce, hbs]; push_cast
        rw [pow_one, mul_div_assoc (3 * 1 : ℝ),
          show 6 * L (i.val + 2) = 2 * (2 * L (i.val + 2)) + 2 * L (i.val + 2) by omega,
          pow_add, div_mul_eq_div_mul_one_div, div_self (by positivity), one_mul]; ring
      have hcap_p : (dens {θ | E₂ i θ} : ℝ) = 1 / (2 : ℝ) ^ (2 * L (i.val + 2)) := by
        rw [P.dens_depthCap_lt_succ hh (by omega) x i, hce]
      have hsub_L : D - i.val ≤ L (i.val + 2) := by
        simpa [L, show D + 1 - (i.val + 1) = D - i.val by omega] using
          Nat.sub_le_iterLog_of_lt_floorLogStar (r := i.val + 1) hlt_star
            (by have := i.isLt; change i.val < D at this; omega)
      rw [hexp_i]; calc
        _ ≤ (12 * (2 : ℝ) ^ L (i.val + 2)) * (7 / (2 : ℝ) ^ (2 * L (i.val + 2))) :=
          mul_le_mul hBi ((add_le_add hsat_p hcap_p.le).trans_eq (by ring))
            (by positivity) (by positivity)
        _ = 84 / (2 : ℝ) ^ L (i.val + 2) := by
          rw [show 2 * L (i.val + 2) = L (i.val + 2) + L (i.val + 2) by omega, pow_add]
          field_simp; ring
        _ ≤ 84 / (2 : ℝ) ^ (D - i.val) := div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (pow_le_pow_right₀ (by norm_num) hsub_L)
        _ = 84 * ((1 : ℝ) / 2) ^ (D - i.val) := by rw [div_eq_mul_inv, ← inv_pow, one_div]
    have hgeom (n : ℕ) : ∑ j ∈ Finset.range n, ((1 : ℝ) / 2) ^ (n - j) ≤ 1 := by
      cases n with
      | zero => simp
      | succ n =>
        have hpow (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
            ((1 : ℝ) / 2) ^ (n + 1 - j) = (1 / (2 : ℝ)) ^ (n - j + 1) := by
          congr 1; rw [Finset.mem_range] at hj; omega
        have hr : (∑ j ∈ Finset.range (n + 1), (1 / (2 : ℝ)) ^ (n - j + 1)) =
            ∑ j ∈ Finset.range (n + 1), (1 / (2 : ℝ)) ^ (j + 1) :=
          Finset.sum_range_reflect (fun k => (1 / (2 : ℝ)) ^ (k + 1)) (n + 1)
        calc ∑ j ∈ Finset.range (n + 1), ((1 : ℝ) / 2) ^ (n + 1 - j)
            = ∑ j ∈ Finset.range (n + 1), (1 / (2 : ℝ)) ^ (n - j + 1) := Finset.sum_congr rfl hpow
          _ = ∑ j ∈ Finset.range (n + 1), (1 / (2 : ℝ)) ^ (j + 1) := hr
          _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.range (n + 1), (1 / (2 : ℝ)) ^ j := by
            simp_rw [pow_succ' (1 / (2 : ℝ)), ← Finset.mul_sum]
          _ ≤ (1 / 2 : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le (n + 1)) (by norm_num)
          _ = 1 := by ring
    have hsum_le : (𝔼 θ, ∑ i : Fin P.depth, err i θ) ≤ 84 := by
      rw [Finset.expect_sum_comm]; refine (Finset.sum_le_sum fun i _ => hterm_le i).trans ?_
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => ((1 : ℝ) / 2) ^ (D - j)) P.depth]
      change 84 * ∑ j ∈ Finset.range D, ((1 : ℝ) / 2) ^ (D - j) ≤ 84; linarith [hgeom D]
    refine ((Finset.expect_le_expect fun θ _ => hpw θ).trans_eq
      (by rw [Finset.expect_add_distrib, Fintype.expect_const])).trans ?_
    have hM_ge : (1 : ℝ) ≤ max (L (k + 1) : ℝ) 1 := le_max_right _ _
    have hLD_cast : (L (D + 1) : ℝ) ≤ max (L (k + 1) : ℝ) 1 := by exact_mod_cast hLD_le
    change _ ≤ 96 * max (L (k + 1) : ℝ) 1; linarith
/-- **Lemma 1** of [BenderFarachColtonKuszmaulKuszmaulLiu2022] (Section 3.1, printed pp. 10–11 /
PDF pp. 11–12), proved under **3-wise independence**. -/
theorem expect_ballProbeComplexity_standardInsert_le {ι α : Type*} [Fintype ι] [DecidableEq α]
    {k_indep : ℕ} (m₀ k : ℕ) {h : ι → α → Fin (2 ^ (standardParams m₀ k).hashBits)}
    (hh : IsKWiseIndependentHash k_indep h) (hk : 3 ≤ k_indep)
    {st : ι → State (standardParams m₀ k) α}
    (hst : ∀ θ, (standardParams m₀ k).ValidState (h θ) (st θ)) {S : Finset α}
    (hS : ∀ θ, (st θ).assignment.present = S) {x : α} (hx : x ∉ S) (hlt : #S < 2 ^ m₀) :
    𝔼 θ, (ballProbeComplexity ((standardParams m₀ k).probeSeq (h θ))
      (standardInsert m₀ k (h θ) (st θ) x).assignment x : ℝ) ≤
      96 * (max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 : ℝ) :=
  (Finset.expect_le_expect (g := fun θ => ((standardParams m₀ k).snapshotProbeBound (h θ) S x : ℝ))
    fun θ _ => by
      exact_mod_cast (standardParams m₀ k).ballProbeComplexity_le_snapshotProbeBound (hst θ)
        ((hst θ).insert x) (hS θ) ((Params.insert_spec (h θ) (hst θ) x).2.2.2.2.2
          (hS θ ▸ hx) (hS θ ▸ hlt))).trans
    (expect_snapshotProbeBound_standardParams_le m₀ k hh hk hlt.le hx)
private theorem ballProbeComplexity_run_le_choose {α : Type*} [DecidableEq α] (P : Params)
    (f : α → Fin (2 ^ P.hashBits)) {ops : List (Op α)} (hval : ValidOpSeq P.slotCount ops)
    {x : α} (hx : x ∈ activeSet ops) :
    ballProbeComplexity (P.probeSeq f) (P.run f ops).assignment x ≤ P.snapshotProbeBound f
      (activeSet (exists_split_last_insert_of_mem_activeSet hval hx).choose) x := by
  obtain ⟨suf, heq, hpre, hx_pre, hlt_pre, hsuf⟩ :=
    (exists_split_last_insert_of_mem_activeSet hval hx).choose_spec
  exact P.ballProbeComplexity_le_snapshotProbeBound (Params.ValidState.run P f _)
    (Params.ValidState.run P f ops) (P.present_run f hpre)
    (P.assignedDepth_run_of_split f heq hpre hx_pre hlt_pre hsuf)
/-- **Theorem 2** of [BenderFarachColtonKuszmaulKuszmaulLiu2022] (Section 3.1, printed p. 12 /
PDF p. 13), proved under **3-wise independence** over arbitrary-length histories `ops`. -/
theorem expect_totalProbeComplexity_standardRun_le {ι α : Type*} [Fintype ι] [DecidableEq α]
    {k_indep : ℕ} (m₀ k : ℕ) {h : ι → α → Fin (2 ^ (standardParams m₀ k).hashBits)}
    (hh : IsKWiseIndependentHash k_indep h) (hk : 3 ≤ k_indep) {ops : List (Op α)}
    (hval : ValidOpSeq (2 ^ m₀) ops) :
    𝔼 θ, (totalProbeComplexity ((standardParams m₀ k).probeSeq (h θ))
      (standardRun m₀ k (h θ) ops).assignment : ℝ) ≤
      96 * (#(activeSet ops) : ℝ) * (max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 : ℝ) := by
  let P := standardParams m₀ k
  have hsum_eq (θ : ι) : (totalProbeComplexity ((standardParams m₀ k).probeSeq (h θ))
      (standardRun m₀ k (h θ) ops).assignment : ℝ) = ∑ x ∈ activeSet ops,
      (ballProbeComplexity (P.probeSeq (h θ)) (P.run (h θ) ops).assignment x : ℝ) := by
    unfold standardRun; change (totalProbeComplexity (P.probeSeq (h θ))
      (P.run (h θ) ops).assignment : ℝ) = _
    rw [totalProbeComplexity_eq_sum_present, P.present_run (h θ) hval]; push_cast; rfl
  simp_rw [hsum_eq]; rw [Finset.expect_sum_comm]
  refine (Finset.sum_le_sum (g := fun _ => 96 * (max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 : ℝ))
    fun x hx => ?_).trans_eq (by rw [Finset.sum_const, nsmul_eq_mul]; ring)
  obtain ⟨_, _, _, hx_pre, hlt_pre, _⟩ :=
    (exists_split_last_insert_of_mem_activeSet hval hx).choose_spec
  exact (Finset.expect_le_expect (g := fun θ => (P.snapshotProbeBound (h θ) _ x : ℝ))
    fun θ _ => by exact_mod_cast ballProbeComplexity_run_le_choose P (h θ) hval hx).trans
    (expect_snapshotProbeBound_standardParams_le m₀ k hh hk hlt_pre.le hx_pre)
/-- **`2m`-th moment concentration across partitioned `k`-kick trees** over arbitrary-length
operation histories, adapting [BenderFarachColtonKuszmaulKuszmaulLiu2022] Theorem 3 (Section 3.1,
printed p. 12 / PDF p. 13) with four explicit deviations: (a) the partition into disjoint-footprint
sub-histories `R` is assumed as an explicit hypothesis; (b) there are no special slots in this
pure primary-slot model; (c) the tail bound is polynomial (`2m`-th moment Markov) rather than an
exponential Chernoff bound; and (d) it assumes `max 3 (2 * m * 4 ^ m₀)`-wise
(`max 3 (2 * m * 2 ^ (2 * m₀))`-wise) independence rather than full independence. -/
theorem dens_sum_totalProbeComplexity_standardRun_gt_le {ι α β : Type*} [Fintype ι] [DecidableEq α]
    {m k_indep : ℕ} (hm : 1 ≤ m) (m₀ k : ℕ) {h : ι → α → Fin (2 ^ (standardParams m₀ k).hashBits)}
    (hh : IsKWiseIndependentHash k_indep h) (hk : max 3 (2 * m * 2 ^ (2 * m₀)) ≤ k_indep)
    (R : Finset β) (ops : β → List (Op α)) (hval : ∀ b ∈ R, ValidOpSeq (2 ^ m₀) (ops b))
    (hdisj : (R : Set β).Pairwise fun b₁ b₂ => Disjoint (opsBalls (ops b₁)) (opsBalls (ops b₂)))
    {μ Δ : ℝ} (hμ : 96 * (∑ b ∈ R, (#(activeSet (ops b)) : ℝ)) *
      (max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 : ℝ) ≤ μ)
    (hmμ : 2 * (m : ℝ) * (2 ^ m₀ : ℝ) * (1 + m₀) ≤ 3 * μ) (hΔ : 0 < Δ) :
    (dens {θ : ι | μ + Δ ≤ ∑ b ∈ R, (totalProbeComplexity ((standardParams m₀ k).probeSeq (h θ))
      (standardRun m₀ k (h θ) (ops b)).assignment : ℝ)} : ℝ) ≤
      2 * (3 * (m : ℝ) * (2 ^ m₀ : ℝ) * (1 + m₀) * μ / Δ ^ 2) ^ m := by
  have : Nonempty (Fin (2 ^ (standardParams m₀ k).hashBits)) := ⟨⟨0, by positivity⟩⟩
  have hk2 : 2 * m * ((standardParams m₀ k).slotCount * (standardParams m₀ k).slotCount) ≤
      k_indep := by
    change 2 * m * (2 ^ m₀ * 2 ^ m₀) ≤ _; rw [← Nat.pow_add, ← Nat.two_mul]
    exact le_of_max_le_right hk
  refine (dens_sum_totalProbeComplexity_gt_le_of_snapshotBound
    (M := (standardParams m₀ k).slotCount) (B_max := 1 + m₀) hm (standardParams m₀ k).slotCount_pos
    (by positivity) hh hk2 (standardParams m₀ k).probeSeq
    (fun f l => (standardRun m₀ k f l).assignment) (standardParams m₀ k).snapshotProbeBound
    (standardParams m₀ k).snapshotProbeBound_le
    (fun heq => (standardParams m₀ k).snapshotProbeBound_congr heq)
    (fun f _ hl => (standardParams m₀ k).present_run f hl)
    (fun f _ hl _ hx => ballProbeComplexity_run_le_choose (standardParams m₀ k) f hl hx) R ops hval
    hdisj (fun {_} hSle {_} hx => expect_snapshotProbeBound_standardParams_le m₀ k hh
      (le_of_max_le_left hk) hSle hx) (by linarith)
    (by change 2 * (m : ℝ) * ((2 ^ m₀ : ℕ) : ℝ) * ((1 + m₀ : ℕ) : ℝ) ≤ 3 * μ; push_cast; exact hmμ)
    hΔ).trans_eq ?_
  change 2 * (3 * (m : ℝ) * ((2 ^ m₀ : ℕ) : ℝ) * ((1 + m₀ : ℕ) : ℝ) * μ / Δ ^ 2) ^ m = _
  push_cast; rfl
/-- **`(1 - δ)`-w.h.p. multi-tree probe-complexity concentration** for two-stage hash families
`h : ι₁ × ι₂ → …` whose top seed `θ₁` is good outside an event of density `≤ δ`. -/
theorem dens_sum_totalProbeComplexity_standardRun_gt_le_of_whp {ι₁ ι₂ α β : Type*}
    [Fintype ι₁] [Nonempty ι₁] [Fintype ι₂] [DecidableEq α] {m k_indep : ℕ} (hm : 1 ≤ m) (m₀ k : ℕ)
    {h : ι₁ × ι₂ → α → Fin (2 ^ (standardParams m₀ k).hashBits)}
    (Good : Set ι₁) [DecidablePred (· ∈ Good)] {δ : ℝ} (hbad : (dens {θ₁ : ι₁ | θ₁ ∉ Good} : ℝ) ≤ δ)
    (hgood : ∀ θ₁ ∈ Good, IsKWiseIndependentHash k_indep (fun θ₂ x => h (θ₁, θ₂) x))
    (hk : max 3 (2 * m * 2 ^ (2 * m₀)) ≤ k_indep) (R : Finset β) (ops : β → List (Op α))
    (hval : ∀ b ∈ R, ValidOpSeq (2 ^ m₀) (ops b))
    (hdisj : (R : Set β).Pairwise fun b₁ b₂ => Disjoint (opsBalls (ops b₁)) (opsBalls (ops b₂)))
    {μ Δ : ℝ} (hμ : 96 * (∑ b ∈ R, (#(activeSet (ops b)) : ℝ)) *
      (max (Nat.iterLog (k + 1) (2 ^ m₀)) 1 : ℝ) ≤ μ)
    (hmμ : 2 * (m : ℝ) * (2 ^ m₀ : ℝ) * (1 + m₀) ≤ 3 * μ) (hΔ : 0 < Δ) :
    (dens {s : ι₁ × ι₂ | μ + Δ ≤ ∑ b ∈ R,
      (totalProbeComplexity ((standardParams m₀ k).probeSeq (h s))
        (standardRun m₀ k (h s) (ops b)).assignment : ℝ)} : ℝ) ≤
      δ + 2 * (3 * (m : ℝ) * (2 ^ m₀ : ℝ) * (1 + m₀) * μ / Δ ^ 2) ^ m := by
  have hμ0 : 0 ≤ μ := (mul_nonneg (mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)) (by positivity)).trans hμ
  exact dens_prod_le_add_of_good (· ∈ Good) _ hbad (by positivity) fun θ₁ hg =>
    dens_sum_totalProbeComplexity_standardRun_gt_le hm m₀ k (hgood θ₁ hg) hk R ops
      hval hdisj hμ hmμ hΔ
end StandardSchedule
end KickTree
end Cslib.DataStructure.BallsToSlots
