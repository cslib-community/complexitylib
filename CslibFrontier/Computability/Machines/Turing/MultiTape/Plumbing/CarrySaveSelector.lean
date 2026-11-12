/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.AppendAtCursor
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.BinaryDecrementFlag
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import CslibFrontier.Computability.Circuit.Boolean.CarrySave.IteratedQuery

/-!
# Native streamed carry-save selection

Counter decrements inspect only the borrow prefix. The address cursor remains at its right
blank. Underflow flags are collected on a separate work tape;
the returned flags determine whether the selected child exists. Underflowing moves may still extend
the address; that data is ignored when interpreting the result as an absent child.
-/

public section

namespace Turing.MultiTapeTM.CarrySaveSelector

open Cslib.BitString

/-- Finite control for a fixed number of counter decrements. -/
@[expose] def ShiftState : ℕ → Type
  | 0 => Unit
  | n + 1 => (Unit ⊕ RewindWorkState) ⊕ ShiftState n

private noncomputable def shift {k : ℕ} (i : Fin k) :
    (n : ℕ) → MultiTapeTM k Bool (ShiftState n)
  | 0 => .ofTr () fun _ _ _ => ⟨0, fun _ => (none, 0), none, none⟩
  | n + 1 => (binaryDecrement.extendTapes (tapeEmb i)).seq (shift i n)

private def flags : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, w => decide (lsbValue w = 0) :: flags n (decrement w)

private theorem length_flags (n : ℕ) (w : List Bool) : (flags n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [flags, ih]

private theorem runFrom_counter {k : ℕ} {S : Type*} {input : List Bool}
    (i : Fin k) (cfg : Cfg k Bool S input) (w : List Bool)
    (hw : cfg.workTapes i = tapeOfList w) (hi : cfg.workTapePos i = 0) :
    (binaryDecrement.extendTapes (tapeEmb i)).runFrom
      (cfg.withState (some binaryDecrement.q₀)) (2 * BinaryDecrement.zeros w + 3) =
      { cfg.withState none with
        workTapes := Function.update cfg.workTapes i (tapeOfList (decrement w))
        workTapePos := Function.update cfg.workTapePos i 0
        output := cfg.output ++ [decide (lsbValue w = 0)] } := by
  simp only [runFrom_tapeEmb, oneTapeCfg, Cfg.withState, hw, hi,
    runFrom_binaryDecrement, embed_tapeEmb, BinaryDecrement.underflow_eq]

private theorem runFrom_shift {k : ℕ} {State : Type*} {input : List Bool}
    (i : Fin k) (n : ℕ) (cfg : Cfg k Bool State input) (w : List Bool)
    (hw : cfg.workTapes i = tapeOfList w) (hi : cfg.workTapePos i = 0) :
    (shift i n).runFrom (cfg.withState (some (shift i n).q₀))
      (BinaryDecrement.totalClock n w + 1) =
      { cfg.withState none with
        workTapes := Function.update cfg.workTapes i (tapeOfList (decrement^[n] w))
        workTapePos := Function.update cfg.workTapePos i 0
        output := cfg.output ++ flags n w } := by
  induction n generalizing w cfg with
  | zero =>
    have he : Function.update cfg.workTapePos i 0 = cfg.workTapePos := by
      rw [← hi]; exact Function.update_eq_self i cfg.workTapePos
    simp [ShiftState, shift, BinaryDecrement.totalClock, runFrom_one, step_of_state, tr_ofTr,
      Action.apply, Cfg.withState, flags, ← hw, he]
  | succ n ih =>
    let mid : Cfg k Bool (Unit ⊕ RewindWorkState) input :=
      { cfg.withState none with
        workTapes := Function.update cfg.workTapes i (tapeOfList (decrement w))
        workTapePos := Function.update cfg.workTapePos i 0
        output := cfg.output ++ [decide (lsbValue w = 0)] }
    have hc : (binaryDecrement.extendTapes (tapeEmb i)).runFrom
        (cfg.withState (some binaryDecrement.q₀)) (2 * BinaryDecrement.zeros w + 3) = mid := by
      exact runFrom_counter i cfg w hw hi
    have hr := ih (mid.withState cfg.state) (decrement w)
      (by simp [mid, Cfg.withState]) (by simp [mid, Cfg.withState])
    simp only [Cfg.withState] at hr
    have hs := runFrom_seq hc rfl hr rfl
    simpa [ShiftState, shift, mid, Cfg.withState, Cfg.mapState, handOver_some, MultiTapeTM.seq,
      MultiTapeTM.combine, BinaryDecrement.totalClock, flags, List.append_assoc,
      Function.iterate_succ_apply, Nat.add_assoc] using hs

private theorem flags_contains (n : ℕ) (w : List Bool) :
    true ∈ flags n w ↔ lsbValue w < n := by
  induction n generalizing w with
  | zero => simp [flags]
  | succ n ih =>
    by_cases hw : lsbValue w = 0
    · simp [flags, hw]
    · have hd := lsbValue_decrement w (by omega)
      simp only [flags, List.mem_cons, ih, hd]
      simp [hw]
      omega

/-- Finite control for a selector with a fixed shift of at most two. -/
abbrev State (amount : Fin 3) := ((Unit ⊕ RewindWorkState) ⊕ ShiftState amount.val) ⊕ Unit

instance shiftState_fintype (n : ℕ) : Fintype (ShiftState n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype ((Unit ⊕ RewindWorkState) ⊕ ShiftState n))

noncomputable instance (amount : Fin 3) : Fintype (State amount) := by
  exact inferInstanceAs
    (Fintype (((Unit ⊕ RewindWorkState) ⊕ ShiftState amount.val) ⊕ Unit))

private noncomputable def raw {k : ℕ} (height bit path : Fin k) (side : Bool)
    (amount : Fin 3) : MultiTapeTM k Bool (State amount) :=
  ((binaryDecrement.extendTapes (tapeEmb height)).seq (shift bit amount.val)).seq
    (appendAtCursor path side)

/-- Native selector for one fixed compressor port. The height is decremented once, the bit
index at most twice, and the address is extended at its current right cursor. The last work
tape receives at most three underflow flags. The actual output remains empty. -/
noncomputable def machine {k : ℕ} (height bit path : Fin k) (side : Bool)
    (amount : Fin 3) : MultiTapeTM (k + 1) Bool (State amount) :=
  (raw height bit path side amount).outputToTape

/-- The flag word records height underflow followed by the bit-index underflows. -/
def resultFlags (height bits : List Bool) (amount : Fin 3) : List Bool :=
  decide (lsbValue height = 0) :: flags amount.val bits

/-- All underflow information occupies at most three cells. -/
theorem resultFlags_length_le (height bits : List Bool) (amount : Fin 3) :
    (resultFlags height bits amount).length ≤ 3 := by
  simp only [resultFlags, List.length_cons, length_flags]
  omega

/-- A selected child exists precisely when the height is positive and the shift fits the index. -/
theorem resultFlags_valid (height bits : List Bool) (amount : Fin 3) :
    true ∉ resultFlags height bits amount ↔
      0 < lsbValue height ∧ amount.val ≤ lsbValue bits := by
  simp only [resultFlags, List.mem_cons, flags_contains]
  by_cases h : lsbValue height = 0 <;> simp [h]; omega

/-- The status bit written by flag cleanup is true exactly for an absent child. -/
theorem resultFlags_contains_eq (height bits : List Bool) (amount : Fin 3) :
    (resultFlags height bits amount).contains true =
      decide (lsbValue height = 0 ∨ lsbValue bits < amount.val) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem, decide_eq_true_eq]
  have hv := resultFlags_valid height bits amount
  constructor
  · intro hf
    by_contra hn
    exact (hv.mpr ⟨by omega, by omega⟩) hf
  · intro hf
    by_contra hn
    have := hv.mp hn
    omega

private theorem runFrom_raw {k : ℕ} {S : Type*} {input : List Bool}
    (h i j : Fin k) (hhi : h ≠ i) (hhj : h ≠ j) (hij : i ≠ j)
    (side : Bool) (amount : Fin 3) (cfg : Cfg k Bool S input)
    (height bits path : List Bool)
    (hh : cfg.workTapes h = tapeOfList height) (hph : cfg.workTapePos h = 0)
    (hi : cfg.workTapes i = tapeOfList bits) (hpi : cfg.workTapePos i = 0)
    (hj : cfg.workTapes j = tapeOfList path) (hpj : cfg.workTapePos j = (path.length : ℤ)) :
    (raw h i j side amount).runFrom
      (cfg.withState (some (raw h i j side amount).q₀))
      (2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5) =
      { cfg.withState none with
        workTapes := Function.update (Function.update (Function.update cfg.workTapes h
          (tapeOfList (decrement height))) i (tapeOfList (decrement^[amount.val] bits))) j
          (tapeOfList (path ++ [side]))
        workTapePos := Function.update (Function.update (Function.update cfg.workTapePos h 0) i 0)
          j ((path.length : ℤ) + 1)
        output := cfg.output ++ resultFlags height bits amount } := by
  let mid : Cfg k Bool (Unit ⊕ RewindWorkState) input :=
    { cfg.withState none with
      workTapes := Function.update cfg.workTapes h (tapeOfList (decrement height))
      workTapePos := Function.update cfg.workTapePos h 0
      output := cfg.output ++ [decide (lsbValue height = 0)] }
  have hc : (binaryDecrement.extendTapes (tapeEmb h)).runFrom
      (cfg.withState (some binaryDecrement.q₀)) (2 * BinaryDecrement.zeros height + 3) = mid := by
    exact runFrom_counter h cfg height hh hph
  have hs := runFrom_shift i amount.val mid bits
    (by simp [mid, Ne.symm hhi, hi]) (by simp [mid, Ne.symm hhi, hpi])
  have hcs := runFrom_seq hc rfl hs rfl
  let mid₂ : Cfg k Bool ((Unit ⊕ RewindWorkState) ⊕ ShiftState amount.val) input :=
    { cfg.withState none with
      workTapes := Function.update mid.workTapes i (tapeOfList (decrement^[amount.val] bits))
      workTapePos := Function.update mid.workTapePos i 0
      output := mid.output ++ flags amount.val bits }
  have hcs' : ((binaryDecrement.extendTapes (tapeEmb h)).seq (shift i amount.val)).runFrom
      (cfg.withState (some ((binaryDecrement.extendTapes (tapeEmb h)).seq
        (shift i amount.val)).q₀))
      (2 * BinaryDecrement.zeros height + 3 +
        (BinaryDecrement.totalClock amount.val bits + 1)) = mid₂ := by
    simpa [mid₂, mid, Cfg.withState, Cfg.mapState, handOver_some, MultiTapeTM.seq,
      MultiTapeTM.combine] using hcs
  have ha := runFrom_appendAtCursor j side cfg.inputPos mid₂.workTapes mid₂.workTapePos
    mid₂.output path (by simp [mid₂, mid, Ne.symm hhj, Ne.symm hij, hj])
    (by simp [mid₂, mid, Ne.symm hhj, Ne.symm hij, hpj])
  have hall := runFrom_seq hcs' rfl ha rfl
  have ht : 2 * BinaryDecrement.zeros height + 3 +
      (BinaryDecrement.totalClock amount.val bits + 1) + 1 =
      2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5 := by omega
  rw [ht] at hall
  simpa [State, raw, mid₂, mid, Cfg.withState, Cfg.mapState, handOver_some, MultiTapeTM.seq,
    MultiTapeTM.combine, resultFlags, List.append_assoc] using hall

/-- Complete native selector run. No clock term depends on the length of the existing path.
Counter words use fixed-width little-endian binary; underflow wraps the affected counter and
is reported on the last work tape. Its at-most-three flags must be consumed by the caller. -/
theorem runFrom_machine {k : ℕ} {S : Type*} {input : List Bool}
    (h i j : Fin k) (hhi : h ≠ i) (hhj : h ≠ j) (hij : i ≠ j)
    (side : Bool) (amount : Fin 3) (cfg : Cfg k Bool S input)
    (height bits path : List Bool)
    (hh : cfg.workTapes h = tapeOfList height) (hph : cfg.workTapePos h = 0)
    (hi : cfg.workTapes i = tapeOfList bits) (hpi : cfg.workTapePos i = 0)
    (hj : cfg.workTapes j = tapeOfList path) (hpj : cfg.workTapePos j = (path.length : ℤ)) :
    (machine h i j side amount).runFrom
      (outCfg (cfg.withState (some (machine h i j side amount).q₀)))
      (2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5) =
      outCfg { cfg.withState none with
        workTapes := Function.update (Function.update (Function.update cfg.workTapes h
          (tapeOfList (decrement height))) i (tapeOfList (decrement^[amount.val] bits))) j
          (tapeOfList (path ++ [side]))
        workTapePos := Function.update (Function.update (Function.update cfg.workTapePos h 0) i 0)
          j ((path.length : ℤ) + 1)
        output := cfg.output ++ resultFlags height bits amount } := by
  have hx := runFrom_map (outCfgHom (raw h i j side amount))
    (cfg.withState (some (raw h i j side amount).q₀))
    (2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5)
  rw [runFrom_raw h i j hhi hhj hij side amount cfg height bits path hh hph hi hpi hj hpj] at hx
  have hq : (raw h i j side amount).outputToTape.q₀ = (raw h i j side amount).q₀ := rfl
  simpa only [machine, hq, outCfgHom_apply] using hx

/-- Erase a flag word backwards, return its cursor to zero, and overwrite the current header
cell with the disjunction of the flags. No other cursor moves. -/
@[expose] def finish {k : ℕ} (flag status : Fin k) : MultiTapeTM k Bool (Option Bool) :=
  .ofTr none fun q _ work => match q with
    | none => ⟨0, fun j => if j = flag then (none, -1) else (none, 0), none, some (some false)⟩
    | some bad => match work flag with
      | some b => ⟨0, fun j => if j = flag then (some none, -1) else (none, 0),
          none, some (some (bad || b))⟩
      | none => ⟨0, fun j => if j = flag then (none, 1)
          else if j = status then (some (some bad), 0) else (none, 0), none, none⟩

private def finished {k : ℕ} {S : Type*} {input : List Bool}
    (flag status : Fin k) (cfg : Cfg k Bool S input) (bad : Bool) :
    Cfg k Bool (Option Bool) input :=
  { cfg.withState none with
    workTapes := Function.update (Function.update cfg.workTapes flag (tapeOfList [])) status
      (Function.update (cfg.workTapes status) (cfg.workTapePos status) (some bad))
    workTapePos := Function.update cfg.workTapePos flag 0 }

private theorem runFrom_finish_scan {k : ℕ} {S : Type*} {input : List Bool}
    (flag status : Fin k) (hne : flag ≠ status) (word : List Bool) (bad : Bool)
    (cfg : Cfg k Bool S input) (ht : cfg.workTapes flag = tapeOfList word)
    (hp : cfg.workTapePos flag = (word.length : ℤ) - 1) :
    (finish flag status).runFrom (cfg.withState (some (some bad))) (word.length + 1) =
      finished flag status cfg (bad || word.contains true) := by
  induction word using List.reverseRecOn generalizing bad cfg with
  | nil =>
    simp only [finish, Cfg.withState, List.length_nil, zero_add, runFrom_one,
      Option.some.injEq, step_of_state, Action.apply, tr_ofTr, Cfg.workTapeSymbols, hp,
      Nat.cast_zero, zero_sub, Int.reduceNeg, ht, tapeOfList_nil, moveInputPos_zero,
      Option.toList_none, List.append_nil, finished, List.contains_eq_mem, List.not_mem_nil,
      decide_false, Bool.or_false, Cfg.mk.injEq, funext_iff, and_true, true_and]
    constructor
    · intro x p
      by_cases hx : x = flag <;> by_cases hy : x = status <;> simp_all
    · intro x
      by_cases hx : x = flag <;> by_cases hy : x = status <;> simp_all
  | append_singleton word b ih =>
    have herase : Function.update (tapeOfList (word ++ [b])) (word.length : ℤ) none =
        tapeOfList word := by
      rw [tapeOfList_append_single, Function.update_idem]
      exact Function.update_eq_self_iff.mpr (by simp)
    let mid : Cfg k Bool S input :=
      { cfg with workTapes := Function.update cfg.workTapes flag (tapeOfList word)
                 workTapePos := Function.update cfg.workTapePos flag ((word.length : ℤ) - 1) }
    have hs : (finish flag status).step (cfg.withState (some (some bad))) =
        mid.withState (some (some (bad || b))) := by
      have hp' : cfg.workTapePos flag = (word.length : ℤ) := by simpa using hp
      simp only [finish, Cfg.withState, Option.some.injEq, step_of_state, Action.apply,
        tr_ofTr, Cfg.workTapeSymbols, hp', ht, tapeOfList_ofNat, List.length_append,
        List.length_cons, List.length_nil, zero_add, lt_add_iff_pos_right, Order.lt_one_iff,
        getElem?_pos, Std.le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero,
        moveInputPos_zero, Option.toList_none, List.append_nil, Cfg.mk.injEq, funext_iff,
        and_true, true_and, mid]
      constructor
      · intro x p
        by_cases hx : x = flag <;> simp_all
      · intro x
        by_cases hx : x = flag <;> simp_all [sub_eq_add_neg]
    have hr := ih (bad || b) mid (by simp [mid]) (by simp [mid])
    rw [List.length_append, List.length_singleton, Nat.add_assoc, show 1 + 1 = 2 by rfl,
      show word.length + 2 = (word.length + 1) + 1 by omega,
      runFrom, Function.iterate_succ_apply, hs, ← runFrom, hr]
    simp [finished, mid, Ne.symm hne, Bool.or_assoc, Bool.or_left_comm,
      Bool.or_comm]

/-- Flag cleanup costs the flag length plus two transitions. The flag tape is blank and reusable,
its head returns to zero, and the status bit is overwritten in place. -/
theorem runFrom_finish {k : ℕ} {S : Type*} {input : List Bool}
    (flag status : Fin k) (hne : flag ≠ status) (word : List Bool)
    (cfg : Cfg k Bool S input) (ht : cfg.workTapes flag = tapeOfList word)
    (hp : cfg.workTapePos flag = (word.length : ℤ)) :
    (finish flag status).runFrom (cfg.withState (some (finish flag status).q₀))
      (word.length + 2) =
      { cfg.withState none with
        workTapes := Function.update (Function.update cfg.workTapes flag (tapeOfList [])) status
          (Function.update (cfg.workTapes status) (cfg.workTapePos status)
            (some (word.contains true)))
        workTapePos := Function.update cfg.workTapePos flag 0 } := by
  let mid : Cfg k Bool S input :=
    { cfg with workTapePos := Function.update cfg.workTapePos flag ((word.length : ℤ) - 1) }
  have hs : (finish flag status).step (cfg.withState (some (finish flag status).q₀)) =
      mid.withState (some (some false)) := by
    simp only [finish, Cfg.withState, q₀_ofTr, Option.some.injEq, step_of_state, Action.apply,
      tr_ofTr, moveInputPos_zero, Option.toList_none, List.append_nil, Cfg.mk.injEq, funext_iff,
      and_true, true_and, mid]
    constructor
    · intro x p
      by_cases hx : x = flag <;> simp [hx]
    · intro x
      by_cases hx : x = flag <;> simp_all [sub_eq_add_neg]
  have hr := runFrom_finish_scan flag status hne word false mid ht (by simp [mid])
  rw [show word.length + 2 = (word.length + 1) + 1 by omega,
    runFrom, Function.iterate_succ_apply, hs, ← runFrom, hr]
  simp [finished, mid, Ne.symm hne]

/-- One selector transition followed by flag consumption. `status` designates a header cell;
choose it separately from the height, index and path tapes to preserve those returned words.
The flag tape is erased and reset, and the header cell is overwritten without moving its head. -/
noncomputable def complete {k : ℕ} (height bit path status : Fin k) (side : Bool)
    (amount : Fin 3) :=
  (machine height bit path side amount).seq (finish (Fin.last k) status.castSucc)

/-- A complete transition includes flag cleanup in its native clock. The displayed intermediate
configuration only names the returned data; it is not an uncharged machine operation. -/
theorem runFrom_complete {k : ℕ} {S : Type*} {input : List Bool}
    (h i j status : Fin k) (hhi : h ≠ i) (hhj : h ≠ j) (hij : i ≠ j)
    (side : Bool) (amount : Fin 3) (cfg : Cfg k Bool S input) (hout : cfg.output = [])
    (height bits path : List Bool)
    (hh : cfg.workTapes h = tapeOfList height) (hph : cfg.workTapePos h = 0)
    (hi : cfg.workTapes i = tapeOfList bits) (hpi : cfg.workTapePos i = 0)
    (hj : cfg.workTapes j = tapeOfList path) (hpj : cfg.workTapePos j = (path.length : ℤ)) :
    let post : Cfg (k + 1) Bool (State amount) input := outCfg
      { cfg.withState none with
        workTapes := Function.update (Function.update (Function.update cfg.workTapes h
          (tapeOfList (decrement height))) i (tapeOfList (decrement^[amount.val] bits))) j
          (tapeOfList (path ++ [side]))
        workTapePos := Function.update (Function.update (Function.update cfg.workTapePos h 0) i 0)
          j ((path.length : ℤ) + 1)
        output := resultFlags height bits amount }
    (complete h i j status side amount).runFrom
      (outCfg (cfg.withState (some (complete h i j status side amount).q₀)))
      (2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits +
        amount.val + 8) =
      { post.withState none with
        workTapes := Function.update
          (Function.update post.workTapes (Fin.last k) (tapeOfList [])) status.castSucc
          (Function.update (post.workTapes status.castSucc) (post.workTapePos status.castSucc)
            (some ((resultFlags height bits amount).contains true)))
        workTapePos := Function.update post.workTapePos (Fin.last k) 0 } := by
  intro post
  have hm := runFrom_machine h i j hhi hhj hij side amount cfg height bits path
    hh hph hi hpi hj hpj
  simp only [hout, List.nil_append] at hm
  change (machine h i j side amount).runFrom
    (outCfg (cfg.withState (some (machine h i j side amount).q₀)))
    (2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5) = post at hm
  have hf := runFrom_finish (Fin.last k) status.castSucc
    (Ne.symm (Fin.castSucc_ne_last status)) (resultFlags height bits amount)
    post (by simp [post]) (by simp [post])
  have hs := runFrom_seq hm rfl hf rfl
  have ht : 2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5 +
      ((resultFlags height bits amount).length + 2) =
      2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits +
        amount.val + 8 := by
    simp only [resultFlags, List.length_cons, length_flags]
    omega
  rw [ht] at hs
  simpa [complete, Cfg.mapState, Cfg.withState, outCfg, handOver_some, MultiTapeTM.seq,
    MultiTapeTM.combine] using hs

open Cslib.Circuits.Boolean.CarrySaveQuery Cslib.Circuits.Boolean.CarrySaveLocal

/-- Interpret the selector's returned counter words and flags as a child query. Flagged
underflow makes the result absent; wrapped counter contents are then irrelevant. -/
def decodedResult (height bits path : List Bool) (carry : Bool) (port : Fin 7) : Option Query :=
  if true ∈ resultFlags height bits (source carry port).shift then none
  else some ⟨path ++ [childSide (source carry port).word], lsbValue (decrement height),
    childCarry (source carry port).word,
    lsbValue (decrement^[(source carry port).shift.val] bits)⟩

/-- The native counter updates, path extension, and underflow flags implement exactly the
semantic compressor descent, including the zero-height and underflow cases. -/
theorem decodedResult_eq_descend (height bits path : List Bool) (carry : Bool) (port : Fin 7) :
    decodedResult height bits path carry port =
      descend ⟨path, lsbValue height, carry, lsbValue bits⟩ port := by
  have hv := resultFlags_valid height bits (source carry port).shift
  by_cases hh : lsbValue height = 0
  · have hf : true ∈ resultFlags height bits (source carry port).shift := by
      by_contra hn
      have := hv.mp hn
      omega
    simp [decodedResult, hf, descend, hh]
  · by_cases hs : (source carry port).shift.val ≤ lsbValue bits
    · have hp : 0 < lsbValue height := by omega
      have hf := hv.mpr ⟨hp, hs⟩
      simp [decodedResult, hf, descend, hh, hs, lsbValue_decrement height hp,
        lsbValue_iterate_decrement _ bits hs]
    · have hf : true ∈ resultFlags height bits (source carry port).shift := by
        by_contra hn
        exact hs (hv.mp hn).2
      simp [decodedResult, hf, descend, hh, hs]

private theorem totalClock_add (a b : ℕ) (w : List Bool) :
    BinaryDecrement.totalClock (a + b) w = BinaryDecrement.totalClock a w +
      BinaryDecrement.totalClock b (decrement^[a] w) := by
  induction a generalizing w with
  | zero => simp [BinaryDecrement.totalClock]
  | succ a ih =>
    rw [Nat.succ_add, BinaryDecrement.totalClock, ih]
    simp [BinaryDecrement.totalClock, Function.iterate_succ_apply, Nat.add_assoc]

/-- The sum of the certified selector subroutine clocks for a sequence of shifts. It includes the
native counter scans, their rewinds, and address appends, but not the surrounding game's flag
consumption and dispatch. -/
@[expose] def clocks : List (Fin 3) → List Bool → List Bool → ℕ
  | [], _, _ => 0
  | amount :: rest, height, bits =>
    2 * BinaryDecrement.zeros height + BinaryDecrement.totalClock amount.val bits + 5 +
      clocks rest (decrement height) (decrement^[amount.val] bits)

private theorem clocks_eq (amounts : List (Fin 3)) (height bits : List Bool) :
    clocks amounts height bits = BinaryDecrement.totalClock amounts.length height +
      BinaryDecrement.totalClock (amounts.map Fin.val).sum bits + 2 * amounts.length := by
  induction amounts generalizing height bits with
  | nil => simp [clocks, BinaryDecrement.totalClock]
  | cons a rest ih =>
    simp only [clocks, ih, List.length_cons, List.map_cons, List.sum_cons]
    rw [BinaryDecrement.totalClock, totalClock_add]
    omega

private theorem sum_amounts_le (amounts : List (Fin 3)) :
    (amounts.map Fin.val).sum ≤ 2 * amounts.length := by
  induction amounts with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have := a.isLt
    omega

/-- All selector subroutine clocks are linear in the number of levels and the initial counter
widths. In particular, growing path prefixes are never recopied or rescanned. -/
theorem clocks_le (amounts : List (Fin 3)) (height bits : List Bool) :
    clocks amounts height bits ≤ 23 * amounts.length + 2 * height.length + 2 * bits.length := by
  have ha := sum_amounts_le amounts
  rw [clocks_eq]
  have hh := BinaryDecrement.totalClock_le amounts.length height
  have hb := BinaryDecrement.totalClock_le_of_le_two_mul ha bits
  omega

/-- Including flag scanning and cleanup adds at most five native transitions per level. The
header bit is overwritten in place on every call; the cleared flag tape is reused. -/
theorem completedClocks_le (amounts : List (Fin 3)) (height bits : List Bool) :
    clocks amounts height bits + (amounts.map Fin.val).sum + 3 * amounts.length ≤
      28 * amounts.length + 2 * height.length + 2 * bits.length := by
  have ha := sum_amounts_le amounts
  have hc := clocks_le amounts height bits
  omega

end Turing.MultiTapeTM.CarrySaveSelector
