/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyJoin
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.KeyGrouping
import all Complexity.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition
import all Complexity.Computability.Machines.Turing.MultiTape.Encodings.StreamFold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import Complexity.Foundations.Data.List.Fold

/-!
# Counting cross-side occurrences in one record pass

The machine reads tagged records directly, remembering one key, two current-run
populations and the accumulated number of pairs. It never constructs a group or
a Cartesian product. Keys need not be sorted for the run-count identity; sorting
is supplied by the class producer when runs must equal whole key classes.

## Main definitions

* `run`: incremental cross-side counting of consecutive equal-key records.
* `width`: physical maximum record width plus the binary counter budget.

## Main results

* `run_eq_count`: exact equality with grouped occurrence counting, including duplicates.
* `run_computable`: uniform near-linear bit time and small callback workspace.

This is an original implementation lemma, not the global resource theorem of [WangLvShenZhang2027].
-/

public section
namespace Turing.MultiTapeTM.KeyCount

private abbrev State := Option ℕ × (ℕ × (ℕ × ℕ))
private abbrev es := encPair (encOption encNat) (encPair encNat (encPair encNat encNat))
private abbrev er := RadixPartition.recordEncoding

private def step (q : State × SortedMatch.Record) : State :=
  let ((previous, (left, (right, total))), (key, payload)) := q
  let same := previous == some key
  let l := if same then left else 0
  let r := if same then right else 0
  if payload % 2 = 0 then (some key, (l + 1, (r, total + r)))
  else (some key, (l, (r + 1, total + l)))

private def finish (s : State) : ℕ :=
  let (_, (_, (_, total))) := s
  total

/-- Count opposite-side occurrence pairs as records arrive; no growing group is retained. -/
def run (rows : List SortedMatch.Record) : ℕ :=
  finish (rows.foldl (fun s r => step (s, r)) (none, (0, (0, 0))))

private def snapshot (key : ℕ) (group : List SortedMatch.Record) (done : ℕ) : State :=
  (some key, ((KeyJoin.side false group).length,
    ((KeyJoin.side true group).length, done + KeyJoin.population group)))

private theorem snapshot_cons (key : ℕ) (row : SortedMatch.Record)
    (group : List SortedMatch.Record) (done : ℕ) :
    step (snapshot key group done, row) =
      if key = row.1 then snapshot row.1 (row :: group) done
      else snapshot row.1 [row] (done + KeyJoin.population group) := by
  have hp : row.2 % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hk : key = row.1 <;> by_cases h : row.2 % 2 = 0 <;>
    simp [step, snapshot, KeyJoin.side, KeyJoin.population, hk, h,
      show (row.2 % 2 = 1) ↔ ¬ row.2 % 2 = 0 by omega, Nat.add_mul, Nat.mul_add, Nat.add_assoc]

private theorem snapshot_perm (key : ℕ) (a b : List SortedMatch.Record) (done : ℕ)
    (h : a.Perm b) : snapshot key a done = snapshot key b done := by
  have hf := (h.filter (fun r => decide (r.2 % 2 = 0))).length_eq
  have hr := (h.filter (fun r => decide (r.2 % 2 = 1))).length_eq
  simp only [snapshot, KeyJoin.population, KeyJoin.side, Bool.false_eq_true,
    ↓reduceIte, hf, hr]

private theorem loop_count (rows : List SortedMatch.Record) (previous : SortedMatch.Record)
    (bucket : List SortedMatch.Record) (done : List (List SortedMatch.Record)) :
    finish (rows.foldl (fun s r => step (s, r))
      (snapshot previous.1 (bucket.reverse ++ [previous]) (KeyJoin.count done))) =
    KeyJoin.count (List.splitBy.loop (fun a b : SortedMatch.Record => decide (a.1 = b.1))
      rows previous bucket done) := by
  induction rows generalizing previous bucket done with
  | nil =>
    simp only [List.foldl_nil, finish, snapshot, List.splitBy.loop, KeyJoin.count,
      List.reverse_cons, List.map_append, List.map_reverse, List.sum_append, List.sum_reverse,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  | cons row rows ih =>
    rw [List.foldl_cons, snapshot_cons, List.splitBy.loop]
    by_cases hk : previous.1 = row.1
    · simp only [hk, ↓reduceIte, decide_true]
      convert ih row (previous :: bucket) done using 1
      congr 2
      apply snapshot_perm
      simpa only [List.append_nil, List.append_assoc, List.reverse_cons] using
        (List.perm_middle (a := row) (l₁ := bucket.reverse ++ [previous]) (l₂ := [])).symm
    · simp only [hk, ↓reduceIte, decide_false]
      convert ih row [] ((previous :: bucket).reverse :: done) using 1
      simp only [List.reverse_nil, List.nil_append, KeyJoin.count, List.map_cons, List.sum_cons]
      rw [List.reverse_cons]
      congr 3; omega

/-- Counting agrees with the complete grouped join, without sortedness or uniqueness premises. -/
theorem run_eq_count (rows : List SortedMatch.Record) :
    run rows = KeyJoin.count (KeyGrouping.run rows) := by
  cases rows with
  | nil => rfl
  | cons row rows =>
    rw [run, List.foldl_cons, KeyGrouping.run, List.splitBy]
    convert loop_count rows row [] [] using 1
    have hp : row.2 % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases h : row.2 % 2 = 0 <;>
      simp [step, snapshot, KeyJoin.side, KeyJoin.population, KeyJoin.count, h,
        show (row.2 % 2 = 1) ↔ ¬ row.2 % 2 = 0 by omega]

/-- Maximum record size and enough binary bits for every counter, including the total. -/
def width (rows : List SortedMatch.Record) : ℕ :=
  streamRecordLength er rows + (encNat (rows.length ^ 2 + 1)).length + 1

private theorem state_bound (rows : List SortedMatch.Record) (j : ℕ) (hj : j ≤ rows.length) :
    let s := streamState (none, (0, (0, 0))) step rows j
    (es s).length ≤ 20 * width rows + 20 := by
  have inv := List.foldl_take_invariant rows (fun s r => step (s, r))
    (none, (0, (0, 0)))
    (fun i s => s.2.1 ≤ i ∧ s.2.2.1 ≤ i ∧ s.2.2.2 ≤ i ^ 2 ∧
      (encOption encNat s.1).length ≤ streamRecordLength er rows + 1)
    (by simp)
    (fun i hi s hs => by
      have hr := le_listMax (f := fun r => (er r).length) (List.getElem_mem hi)
      change (er rows[i]).length ≤ streamRecordLength er rows at hr
      have key : (encOption encNat (some rows[i].1)).length ≤
          streamRecordLength er rows + 1 := by
        simp only [encOption_some, List.length_cons, RadixPartition.recordEncoding,
          length_encPair] at hr ⊢
        omega
      rcases s with ⟨previous, l, r, total⟩
      dsimp only at hs
      dsimp only [step]
      split <;> split <;> dsimp only <;>
        refine ⟨by omega, by omega, ?_, key⟩ <;> nlinarith only [hs.1, hs.2.1, hs.2.2.1])
  have h := inv j hj
  let s := streamState (none, (0, (0, 0))) step rows j
  change s.2.1 ≤ j ∧ s.2.2.1 ≤ j ∧ s.2.2.2 ≤ j ^ 2 ∧
    (encOption encNat s.1).length ≤ streamRecordLength er rows + 1 at h
  have hl : s.2.1 ≤ rows.length ^ 2 + 1 := by nlinarith [h.1]
  have hr : s.2.2.1 ≤ rows.length ^ 2 + 1 := by nlinarith [h.2.1]
  have ht : s.2.2.2 ≤ rows.length ^ 2 + 1 := by
    exact h.2.2.1.trans (by nlinarith)
  have wire (v : ℕ) (hv : v ≤ rows.length ^ 2 + 1) :
      (encNat v).length ≤ (encNat (rows.length ^ 2 + 1)).length := by
    simpa only [encNat_apply, Nat.size_eq_bits_len] using Nat.size_le_size hv
  have hkey := h.2.2.2
  have h₁ := wire _ hl
  have h₂ := wire _ hr
  have h₃ := wire _ ht
  change (es s).length ≤ _
  simp only [length_encPair]
  dsimp only [width]
  omega

private theorem step_polyTime : ComputableTidilyInPolyTime step
    (encPair es er) es := by
  have previous : ComputableTidilyInPolyTime (fun q : State × SortedMatch.Record => q.1.1)
      (encPair es er) (encOption encNat) := by fun_prop
  have key : ComputableTidilyInPolyTime (fun q : State × SortedMatch.Record => q.2.1)
      (encPair es er) encNat := by dsimp only [er]; fun_prop
  have same := ComputableTidilyInPolyTime.decide_eq' previous
    ((ComputableTidilyInPolyTime.optionSome encNat).comp key)
  have left : ComputableTidilyInPolyTime (fun q : State × SortedMatch.Record => q.1.2.1)
      (encPair es er) encNat := by fun_prop
  have right : ComputableTidilyInPolyTime (fun q : State × SortedMatch.Record => q.1.2.2.1)
      (encPair es er) encNat := by fun_prop
  have total : ComputableTidilyInPolyTime (fun q : State × SortedMatch.Record => q.1.2.2.2)
      (encPair es er) encNat := by fun_prop
  have l := same.cond left (.const 0)
  have r := same.cond right (.const 0)
  have parity : ComputableTidilyInPolyTime
      (fun q : State × SortedMatch.Record => decide (q.2.2 % 2 = 0)) (encPair es er) encBool := by
    apply ComputableTidilyInPolyTime.decide_eq'
    · apply ComputableTidilyInPolyTime.binary_mod' <;> dsimp only [er] <;> fun_prop
    · exact .const 0
  have value := parity.cond
    ((l.binary_add' (.const 1)).prod (r.prod (total.binary_add' r)))
    (l.prod ((r.binary_add' (.const 1)).prod (total.binary_add' l)))
  exact (((ComputableTidilyInPolyTime.optionSome encNat).comp key).prod value).of_enc_eq
    (fun q => by
      simp only [step, beq_iff_eq, decide_eq_true_eq, Function.comp_apply]
      split <;> rfl)

private theorem finish_polyTime : ComputableTidilyInPolyTime finish es encNat := by
  exact (ComputableTidilyInPolyTime.snd encNat encNat).comp
    ((ComputableTidilyInPolyTime.snd encNat (encPair encNat encNat)).comp
      (ComputableTidilyInPolyTime.snd (encOption encNat) (encPair encNat (encPair encNat encNat))))

/-- A single uniform multitape computation counts runs in near-linear record time. The
polynomial sees only a maximum record and binary counters, never a whole group. The space
profile bounds every execution prefix, including decoded input, callback tapes and readback. -/
theorem run_computable : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ComputableInO run (encList RadixPartition.recordEncoding) encNat
      (fun rows => (encList RadixPartition.recordEncoding rows).length +
        (rows.length + 1) * P (width rows))
      (fun rows => (encList RadixPartition.recordEncoding rows).length + P (width rows)) := by
  have decode : ComputableTidilyInPolyTime (id : SortedMatch.Record → _)
      (encFramed er) er := .of_linear (.of_unframe (fun _ => by simp))
  have arg := (ComputableTidilyInPolyTime.fst es (encFramed er)).prod
    (decode.comp (ComputableTidilyInPolyTime.snd es (encFramed er)))
  obtain ⟨tN, sN, htN, hsN, hN⟩ := step_polyTime.comp arg
  simp only [Function.comp_def, id_eq] at hN
  obtain ⟨c, d, bound⟩ := (htN.add hsN).exists_le
  obtain ⟨tF, sF, htF, hsF, hF⟩ := finish_polyTime
  obtain ⟨f, e, finishBound⟩ := (htF.add hsF).exists_le
  obtain ⟨cI, hI⟩ := computableInTimeAndSpace_of_const
    (encIn := encList er) (encOut := es) (none, (0, (0, 0)))
  obtain ⟨cE, hE⟩ := computableInTimeAndSpace_of_const
    (encIn := encPair es (encFramed er)) (encOut := encBits) ([] : List Bool)
  let P : ℕ → ℕ := fun B => c * (50 * B + 50) ^ d +
    f * (20 * B + 21) ^ e + 2 * cE + 50 * B + 50
  have hP : Cslib.PolynomiallyBounded P := by dsimp only [P]; fun_prop
  have hm : Monotone P := by
    intro a b hab
    have hc := Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega : 50*a+50 ≤ 50*b+50) d)
    have hf := Nat.mul_le_mul_left f (Nat.pow_le_pow_left (by omega : 20*a+21 ≤ 20*b+21) e)
    dsimp only [P]
    omega
  have rowBound (rows : List SortedMatch.Record) (j : ℕ) (hj : j < rows.length) :
      (er rows[j]).length ≤ width rows := by
    have hr := le_listMax (f := fun r => (er r).length) (List.getElem_mem hj)
    change (er rows[j]).length ≤ streamRecordLength er rows at hr
    exact hr.trans (by dsimp only [width]; omega)
  have callbacks (rows : List SortedMatch.Record) (j : ℕ) (hj : j < rows.length) :
      tN (streamState (none, (0, (0, 0))) step rows j, rows[j]) +
        sN (streamState (none, (0, (0, 0))) step rows j, rows[j]) ≤
      c * (50 * width rows + 50) ^ d := by
    have hs := state_bound rows j hj.le
    have hr := rowBound rows j hj
    apply (bound _).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp only [length_encPair, encFramed_apply, length_frame] at hs ⊢
    omega
  have finishes (rows : List SortedMatch.Record) :
      tF (streamState (none, (0, (0, 0))) step rows rows.length) +
        sF (streamState (none, (0, (0, 0))) step rows rows.length) ≤
      f * (20 * width rows + 21) ^ e := by
    apply (finishBound _).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have hs := state_bound rows rows.length le_rfl
    omega
  obtain ⟨C, hc⟩ := ComputableTidilyInTimeAndSpace.streamFold
    (g := run) (encA := encFramed er) (encS := es) (encIn := encList er) (encOut := encNat)
    (next := step) (finish := finish)
    rawFrameReader (fun row => frame (er row)) (fun _ => frame_ne_nil _)
    (fun row rest => read_rawFrameReader _ _) id (fun _ => rfl)
    hI.computableTidilyInTimeAndSpace hN hE.computableTidilyInTimeAndSpace hF
    (fun rows => by
      simp only [Function.const_apply, id_eq]
      simp only [encBits_apply, streamEmit_const_nil, List.nil_append]
      simp only [run, streamState, List.take_length])
    (tMax := fun rows => P (width rows)) (sMax := fun rows => P (width rows))
    (lMax := fun rows => 20 * width rows + 20)
    (fun rows j hj => by
      simp only [Function.const_apply, id_eq]
      have := callbacks rows j hj
      dsimp only [P]
      omega)
    (fun rows j hj => by
      simp only [Function.const_apply, id_eq]
      have := callbacks rows j hj
      dsimp only [P]
      omega)
    (fun rows j hj => state_bound rows j hj)
    (fun rows j hj => by
      have hr := rowBound rows j hj
      simp only [id_eq, encFramed_apply, length_frame]
      omega)
  simp only [Function.const_apply, id_eq] at hc
  let K := C * (2 * cI + 20) + 20
  refine ⟨P, hP, hm, ComputableInO.of_bounds hc.computableInTimeAndSpace K ?_ ?_ ?_⟩
  · intro rows
    have hf := finishes rows
    have ht : tF (streamState (none, (0, (0, 0))) step rows rows.length) ≤
        P (width rows) := by dsimp only [P]; omega
    have hp : 20 * width rows + 21 ≤ P (width rows) := by dsimp only [P]; omega
    let D := (encList er rows).length + (rows.length + 1) * P (width rows) + 1
    have hn := Nat.mul_le_mul_left rows.length hp
    have hD : 1 ≤ D := by dsimp only [D]; omega
    have hinner : 2*cI+2 + tF (streamState (none, (0, (0, 0))) step rows rows.length) +
        (encList er rows).length + rows.length * (P (width rows) + (20*width rows+20) + 1) +
          (20*width rows+20) + 1 ≤ 2*cI+2+3*D := by
      dsimp only [D]
      nlinarith only [ht, hp, hn]
    have hscale : 2*cI+2+3*D ≤ (2*cI+20)*D := by nlinarith only [hD]
    change C * _ ≤ K * D
    have hh := Nat.mul_le_mul_left C (hinner.trans hscale)
    have hk := Nat.mul_le_mul_right D (Nat.le_add_right (C * (2*cI+20)) 20)
    exact hh.trans (by simpa only [Nat.mul_assoc] using hk)
  · intro rows
    have hf := finishes rows
    have hs : sF (streamState (none, (0, (0, 0))) step rows rows.length) ≤
        P (width rows) := by dsimp only [P]; omega
    have hp : 20 * width rows + 21 ≤ P (width rows) := by dsimp only [P]; omega
    let D := (encList er rows).length + P (width rows) + 1
    have hinner : 0 + sF (streamState (none, (0, (0, 0))) step rows rows.length) +
        P (width rows) + (20 * width rows + 20) + 1 ≤ 3 * D := by
      dsimp only [D]; omega
    have hk : C * 3 ≤ K := by dsimp only [K]; nlinarith
    change C * _ ≤ K * D
    exact (Nat.mul_le_mul_left C hinner).trans (by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right D hk)
  · intro rows
    have hr := state_bound rows rows.length le_rfl
    simp only [streamState, List.take_length] at hr
    have hs : (encNat (run rows)).length ≤ 20 * width rows + 20 := by
      exact (length_le_encPair_right encNat encNat _).trans
        ((length_le_encPair_right encNat (encPair encNat encNat) _).trans
          ((length_le_encPair_right (encOption encNat) _ _).trans hr))
    have hp : 20 * width rows + 20 ≤ P (width rows) := by dsimp only [P]; omega
    have hk : 1 ≤ K := by dsimp only [K]; omega
    exact (hs.trans hp).trans ((by omega : P (width rows) ≤
      (encList er rows).length + P (width rows) + 1).trans (Nat.le_mul_of_pos_left _ hk))

end Turing.MultiTapeTM.KeyCount
