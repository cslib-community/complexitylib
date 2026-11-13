/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WordMoves
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.BlockNetwork.RelativeSearch
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Native relative-distance scanning

Two bits encode each movement. A read-only source head traverses these pairs, while a second
head stores signed displacement relative to three marker cells. The controller takes two steps
per skipped candidate and one final test, preserving both tapes and appending the match flag.
Source-column extraction and positioning are separate charged operations.
-/

public section

namespace Turing.MultiTapeTM.RelativeScan

/-- The first movement bit indicates a negative move. -/
@[expose] def negative (s : SignType) : Bool := decide (s = -1)

/-- The second movement bit indicates a positive move. -/
@[expose] def positive (s : SignType) : Bool := decide (s = 1)

/-- Two cells per movement, in candidate order. -/
@[expose] def encode : List SignType → List Bool
  | [] => []
  | s :: ss => negative s :: positive s :: encode ss

/-- Every encoded movement occupies exactly two tape cells. -/
@[simp] theorem length_encode (ss : List SignType) : (encode ss).length = 2 * ss.length := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [encode, ih]; omega

/-- Concatenating movement streams concatenates their physical two-bit words. -/
@[simp] theorem encode_append (ss ts : List SignType) :
    encode (ss ++ ts) = encode ss ++ encode ts := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp [encode, ih]

/-- The consumed offset, final signed distance, and success flag of the scan. -/
structure Result where
  /-- Number of movement pairs passed before termination. -/
  consumed : ℕ
  /-- Distance at the terminal candidate. -/
  distance : ℤ
  /-- Whether a candidate in the distance window was found. -/
  found : Bool
  deriving DecidableEq

/-- Inspect a candidate before applying the movement leading to the next candidate. -/
@[expose] def evaluate : List SignType → ℤ → Result
  | [], d => ⟨0, d, false⟩
  | s :: ss, d =>
    if |d| ≤ 1 then ⟨0, d, true⟩
    else let r := evaluate ss (d + (s : ℤ)); { r with consumed := r.consumed + 1 }

/-- The source cursor never passes the end of the supplied movement stream. -/
theorem consumed_le (ss : List SignType) (d : ℤ) : (evaluate ss d).consumed ≤ ss.length := by
  induction ss generalizing d with
  | nil => simp [evaluate]
  | cons s ss ih =>
    simp only [evaluate, List.length_cons]
    split_ifs
    · simp
    · exact Nat.add_le_add_right (ih _) 1

/-- A successful result gives its offset; an exhausted stream has no candidate. -/
@[expose] def Result.index (r : Result) : Option ℕ := if r.found then some r.consumed else none

/-- The semantic suffix of one schedule column, truncated to the remaining horizon. -/
@[expose] def movements {k q : ℕ} (σ : MultiTapePTM.Schedule k q) (h : Fin k) :
    ℕ → ℕ → List SignType
  | 0, _ => []
  | fuel + 1, cursor =>
    if hc : cursor < q then σ ⟨cursor, hc⟩ (some h) :: movements σ h fuel (cursor + 1)
    else []

/-- The supplied movement word contains at most one entry per permitted candidate. -/
theorem length_movements_le {k q : ℕ} (σ : MultiTapePTM.Schedule k q) (h : Fin k)
    (fuel cursor : ℕ) : (movements σ h fuel cursor).length ≤ fuel := by
  induction fuel generalizing cursor with
  | zero => simp [movements]
  | succ fuel ih =>
    simp only [movements]
    split_ifs
    · simpa only [List.length_cons] using Nat.add_le_add_right (ih (cursor + 1)) 1
    · simp

/-- The native scan specification agrees with the existing relative-distance search. -/
theorem evaluate_movements {k q : ℕ} (σ : MultiTapePTM.Schedule k q) (h : Fin k)
    (fuel cursor : ℕ) (d : ℤ) :
    ((evaluate (movements σ h fuel cursor) d).index).map (cursor + ·) =
      MultiTapePTM.RelativeSearch.scan σ h fuel cursor d := by
  induction fuel generalizing cursor d with
  | zero => simp [movements, evaluate, Result.index, MultiTapePTM.RelativeSearch.scan]
  | succ fuel ih =>
    rw [movements, MultiTapePTM.RelativeSearch.scan]
    split_ifs with hc hd
    · simp [evaluate, hd, Result.index]
    · rw [evaluate, ite_eq_right hd, ← ih]
      cases he : evaluate (movements σ h fuel (cursor + 1))
          (d + (σ ⟨cursor, hc⟩ (some h) : ℤ)) with
      | mk consumed distance found =>
        cases found <;> simp [Result.index, add_comm, add_left_comm]
    · simp [evaluate, Result.index]

/-- Starting after an outgoing window gives exactly its next appearance. -/
theorem evaluate_next {k q : ℕ} (σ : MultiTapePTM.Schedule k q) (i : Fin q)
    (h : Fin k) (d : Fin 3) :
    ((evaluate (movements σ h (q - (i + 1)) (i + 1))
      (1 - (d : ℤ) + (σ i (some h) : ℤ))).index).map (i.val + 1 + ·) =
      (MultiTapePTM.firstAfter (MultiTapePTM.InWindow σ h
        (MultiTapePTM.portBlock σ i h d)) i).map Fin.val := by
  rw [evaluate_movements]
  exact MultiTapePTM.RelativeSearch.next_eq_firstAfter σ i h d

/-- Native read-only scanner. False control tests the next candidate; true consumes its second bit.
The marker tape has three true cells at positions zero through two. -/
@[expose] def machine : MultiTapeTM 2 Bool Bool :=
  ofTr false fun phase _ work =>
    if phase then
      ⟨0, ![(none, 1), (none, if work 0 = some true then 1 else 0)], none, some false⟩
    else match work 0 with
      | none => ⟨0, fun _ => (none, 0), some false, none⟩
      | some neg =>
        if (work 1).isSome then ⟨0, fun _ => (none, 0), some true, none⟩
        else ⟨0, ![(none, 1), (none, if neg then -1 else 0)], none, some true⟩

/-- Physical scanner storage: whole source word, its current cursor, and signed distance. -/
@[expose] def config (input w : List Bool) (cursor distance : ℤ) (out : List Bool) :
    Cfg 2 Bool Unit input :=
  tapesCfg input ![w, [true, true, true]] 0 ![cursor, distance + 1] out

private theorem marker (d : ℤ) :
    (tapeOfList [true, true, true] (d + 1)).isSome = decide (|d| ≤ 1) := by
  rw [Bool.eq_iff_iff]
  simp only [Option.isSome_iff_ne_none, ne_eq, tapeOfList_eq_none_iff,
    List.length_cons, List.length_nil, decide_eq_true_eq, abs_le]
  omega

private theorem step_halt (input w out : List Bool) (cursor d : ℤ)
    (hs : tapeOfList w cursor = none) :
    machine.step ((config input w cursor d out).withState (some false)) =
      (config input w cursor d (out ++ [false])).withState none := by
  rw [step_of_state rfl]
  apply Cfg.ext <;> simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState,
    Cfg.workTapeSymbols, Action.apply, hs]

private theorem step_found (input w out : List Bool) (cursor d : ℤ) (neg : Bool)
    (hs : tapeOfList w cursor = some neg) (hd : |d| ≤ 1) :
    machine.step ((config input w cursor d out).withState (some false)) =
      (config input w cursor d (out ++ [true])).withState none := by
  rw [step_of_state rfl]
  apply Cfg.ext <;> simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState,
    Cfg.workTapeSymbols, Action.apply, hs, marker, hd]

private theorem step_negative (input w out : List Bool) (cursor d : ℤ) (neg : Bool)
    (hs : tapeOfList w cursor = some neg) (hd : ¬ |d| ≤ 1) :
    machine.step ((config input w cursor d out).withState (some false)) =
      (config input w (cursor + 1) (d - if neg then 1 else 0) out).withState
        (some true) := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, marker, hd,
      Action.apply]
  · simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, marker, hd,
      Action.apply]
  · funext i z
    fin_cases i <;>
      simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, marker, hd,
        Action.apply]
  · funext i
    fin_cases i <;> cases neg <;>
      simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, marker, hd,
        Action.apply]
  · simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, marker, hd,
      Action.apply]

private theorem step_positive (input w out : List Bool) (cursor d : ℤ) (pos : Bool)
    (hs : tapeOfList w cursor = some pos) :
    machine.step ((config input w cursor d out).withState (some true)) =
      (config input w (cursor + 1) (d + if pos then 1 else 0) out).withState
        (some false) := by
  rw [step_of_state rfl]
  apply Cfg.ext
  · simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, Action.apply]
  · simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, Action.apply]
  · funext i z
    fin_cases i <;>
      simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs,
        Action.apply]
  · funext i
    fin_cases i <;> cases pos <;>
      simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs,
        Action.apply]
  · simp [machine, tr_ofTr, config, tapesCfg, Cfg.withState, Cfg.workTapeSymbols, hs, Action.apply]

/-- Two native steps consume one unsuccessful candidate and preserve both tape words. -/
theorem runFrom_pair (input w pre : List Bool) (s : SignType) (ss : List SignType)
    (hw : w = pre ++ encode (s :: ss)) (d : ℤ) (hd : ¬ |d| ≤ 1) (out : List Bool) :
    machine.runFrom ((config input w pre.length d out).withState (some false)) 2 =
      (config input w (pre.length + 2) (d + (s : ℤ)) out).withState (some false) := by
  have hfirst : tapeOfList w pre.length = some (negative s) := by
    simp [hw, encode, tapeOfList_ofNat]
  have hsecond : tapeOfList w ((pre.length : ℤ) + 1) = some (positive s) := by
    rw [show (pre.length : ℤ) + 1 = ((pre.length + 1 : ℕ) : ℤ) by omega,
      hw, encode, tapeOfList_ofNat, List.getElem?_append_right (by omega)]
    simp
  change machine.runFrom _ (1 + 1) = _
  simp only [runFrom_add, runFrom_one]
  rw [step_negative _ _ _ _ _ _ hfirst hd, step_positive _ _ _ _ _ _ hsecond]
  cases s <;> simp [negative, positive, add_assoc, sub_eq_add_neg]

/-- Exact native scan, including the final successful or exhausted test. -/
theorem runFrom_machine (input w pre : List Bool) (ss : List SignType)
    (hw : w = pre ++ encode ss) (d : ℤ) (out : List Bool) :
    machine.runFrom ((config input w pre.length d out).withState (some false))
        (2 * (evaluate ss d).consumed + 1) =
      (config input w (pre.length + 2 * (evaluate ss d).consumed)
        (evaluate ss d).distance (out ++ [(evaluate ss d).found])).withState none := by
  induction ss generalizing pre d with
  | nil =>
    simp only [evaluate, Nat.mul_zero, Nat.zero_add, Nat.cast_zero]
    rw [runFrom_one]
    exact step_halt input w out pre.length d (by simp [hw, encode])
  | cons s ss ih =>
    by_cases hd : |d| ≤ 1
    · simp only [evaluate, ite_eq_left hd, Nat.mul_zero, Nat.zero_add, Nat.cast_zero]
      rw [runFrom_one]
      exact step_found input w out pre.length d (negative s) (by simp [hw, encode]) hd
    · have hp : w = (pre ++ [negative s, positive s]) ++ encode ss := by
        simp [hw, encode, List.append_assoc]
      have hr := ih (pre ++ [negative s, positive s]) hp (d + (s : ℤ))
      rw [show 2 * (evaluate (s :: ss) d).consumed + 1 =
          2 + (2 * (evaluate ss (d + (s : ℤ))).consumed + 1) by simp [evaluate, hd]; omega,
        runFrom_add, runFrom_pair input w pre s ss hw d hd out]
      simpa [evaluate, hd, mul_add, add_assoc, add_comm, add_left_comm] using hr

/-- The native scanner has a linear time bound and a corresponding visited-cell bound. -/
theorem runsBetween_machine (input w pre : List Bool) (ss : List SignType)
    (hw : w = pre ++ encode ss) (d : ℤ) (out : List Bool) :
    RunsBetween machine (config input w pre.length d out)
      (config input w (pre.length + 2 * (evaluate ss d).consumed)
        (evaluate ss d).distance (out ++ [(evaluate ss d).found]))
      (2 * (evaluate ss d).consumed + 1) (4 * (evaluate ss d).consumed + 4) := by
  exact (RunsBetween.of_runFrom (runFrom_machine input w pre ss hw d out)).mono le_rfl
    (by omega)

/-- A bounded initial distance, represented by its index in `[-2, 2]`. -/
@[expose] def initialDistance (start : Fin 5) : ℤ := (start.val : ℤ) - 2

/-- Five transitions create the three marker cells and position the displacement head. -/
@[expose] def prepareMarker (start : Fin 5) : MultiTapeTM 2 Bool (Fin 5) :=
  ofTr 0 fun phase _ _ => match phase.val with
    | 0 => ⟨0, ![(none, 0), (some (some true), 1)], none, some 1⟩
    | 1 => ⟨0, ![(none, 0), (some (some true), 1)], none, some 2⟩
    | 2 => ⟨0, ![(none, 0), (some (some true), -1)], none, some 3⟩
    | 3 => ⟨0, ![(none, 0), (none, if start.val < 2 then -1 else
        if 2 < start.val then 1 else 0)], none, some 4⟩
    | _ => ⟨0, ![(none, 0), (none, if start.val = 0 then -1 else
        if start.val = 4 then 1 else 0)], none, none⟩

private theorem step_prepareMarker_write (input w marker out : List Bool) (cursor : ℤ)
    (start phase next : Fin 5) (move : SignType)
    (ha : ∀ inp work, (prepareMarker start).tr phase inp work =
      ⟨0, ![(none, 0), (some (some true), move)], none, some next⟩) :
    (prepareMarker start).step ((tapesCfg input ![w, marker] 0
      ![cursor, marker.length] out).withState (some phase)) =
      (tapesCfg input ![w, marker ++ [true]] 0
        ![cursor, marker.length + (move : ℤ)] out).withState (some next) := by
  apply step_tapesCfg (a := ⟨0, ![(none, 0), (some (some true), move)], none, some next⟩)
  · exact ha _ _
  · rfl
  · rfl
  · intro i
    fin_cases i
    · simp
    · simpa using update_shifted_append marker true 0
  · intro i
    fin_cases i <;> simp

private theorem step_prepareMarker_move (input w out : List Bool) (cursor head : ℤ)
    (start phase : Fin 5) (next : Option (Fin 5)) (move : SignType)
    (ha : ∀ inp work, (prepareMarker start).tr phase inp work =
      ⟨0, ![(none, 0), (none, move)], none, next⟩) :
    (prepareMarker start).step ((tapesCfg input ![w, [true, true, true]] 0
      ![cursor, head] out).withState (some phase)) =
      (tapesCfg input ![w, [true, true, true]] 0
        ![cursor, head + (move : ℤ)] out).withState next := by
  apply step_tapesCfg (a := ⟨0, ![(none, 0), (none, move)], none, next⟩)
  · exact ha _ _
  · rfl
  · rfl
  · intro i
    fin_cases i <;> rfl
  · intro i
    fin_cases i <;> simp

/-- Marker initialization starts on a blank tape and preserves the entire source and output. -/
theorem runFrom_prepareMarker (input w out : List Bool) (cursor : ℤ) (start : Fin 5) :
    (prepareMarker start).runFrom ((tapesCfg input ![w, []] 0 ![cursor, 0] out).withState
      (some 0)) 5 =
      (config input w cursor (initialDistance start) out).withState none := by
  have h0 := step_prepareMarker_write input w [] out cursor start 0 1 1
    (by intros; simp [prepareMarker])
  have h1 := step_prepareMarker_write input w [true] out cursor start 1 2 1
    (by intros; simp [prepareMarker])
  have h2 := step_prepareMarker_write input w [true, true] out cursor start 2 3 (-1)
    (by intros; simp [prepareMarker])
  simp only [List.length_nil, Nat.cast_zero, List.nil_append, zero_add,
    List.length_cons, Nat.cast_add, Nat.cast_one, List.cons_append,
    SignType.coe_one, SignType.coe_neg] at h0 h1 h2
  change (prepareMarker start).runFrom _ (1 + (1 + (1 + (1 + 1)))) = _
  simp only [runFrom_add, runFrom_one]
  rw [h0, h1, h2, show (1 : ℤ) + 1 + -1 = 1 by omega]
  rw [step_prepareMarker_move input w out cursor 1 start 3 (some 4)
      (if start.val < 2 then -1 else if 2 < start.val then 1 else 0)
      (by intros; simp [prepareMarker]),
    step_prepareMarker_move input w out cursor _ start 4 none
      (if start.val = 0 then -1 else if start.val = 4 then 1 else 0)
      (by intros; simp [prepareMarker])]
  fin_cases start <;> norm_num [config, initialDistance]

/-- Initialize the marker and run the native distance scan. -/
@[expose] noncomputable def initialized (start : Fin 5) :
    MultiTapeTM 2 Bool (Fin 5 ⊕ Bool) :=
  (prepareMarker start).seq machine

/-- A scan from blank marker storage costs exactly two transitions per skipped candidate,
plus six transitions for initialization and the terminal test. -/
theorem runsBetween_initialized (input w pre : List Bool) (ss : List SignType)
    (hw : w = pre ++ encode ss) (out : List Bool) (start : Fin 5) :
    RunsBetween (initialized start)
      (tapesCfg input ![w, []] 0 ![pre.length, 0] out)
      (config input w (pre.length + 2 * (evaluate ss (initialDistance start)).consumed)
        (evaluate ss (initialDistance start)).distance
        (out ++ [(evaluate ss (initialDistance start)).found]))
      (2 * (evaluate ss (initialDistance start)).consumed + 6)
      (4 * (evaluate ss (initialDistance start)).consumed + 16) := by
  have hi : RunsBetween (prepareMarker start)
      (tapesCfg input ![w, []] 0 ![pre.length, 0] out)
      (config input w pre.length (initialDistance start) out) 5 12 :=
    RunsBetween.of_runFrom (runFrom_prepareMarker input w out pre.length start)
  have hs := hi.seq (runsBetween_machine input w pre ss hw (initialDistance start) out)
  change RunsBetween ((prepareMarker start).seq machine) _ _ _ _
  convert hs using 1 <;> omega

end Turing.MultiTapeTM.RelativeScan
