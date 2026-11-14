/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RelativeScanSchedule
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleBits
import Mathlib.Tactic.FinCases

/-!
# Reading the current movement before the native endpoint scan

The source head starts on the queried interval's pair. Two native transitions read the actual
negative and positive movement bits, advance to the next pair, and select the scanner's initial
distance in finite control. The query port is one of three fixed controller variants; the
schedule and interval index are runtime tape data. An invalid or missing pair rejects.

The resulting flag and canonical binary index agree with the prepared-column endpoint theorem.
The whole column is preserved, and its head returns to zero. The two reads are charged in the
linear clock; preparing the column and positioning its initial head remain separate operations.
-/

public section

namespace Turing.MultiTapeTM.RelativeScanDispatch

/-- Finite control remembers the first bit and then the selected scanner member. -/
inductive State (S : Type) where
  | first
  | second (negative : Bool)
  | continuation (start : Fin 5) (state : S)

instance {S : Type} [Finite S] : Finite (State S) :=
  Finite.of_injective (fun q : State S => match q with
    | .first => (Sum.inl none : Option Bool ⊕ Fin 5 × S)
    | .second negative => .inl (some negative)
    | .continuation start state => .inr (start, state)) (by
      intro a b h
      cases a <;> cases b <;> simp_all)

private def readAction {S : Type} (next : Option (State S)) (out : Option Bool) :
    Action 3 Bool (State S) :=
  ⟨0, ![(none, 1), (none, 0), (none, 0)], out, next⟩

private noncomputable def dispatcher {S : Type} (d : Fin 3)
    (family : Fin 5 → MultiTapeTM 3 Bool S) : MultiTapeTM 3 Bool (State S) :=
  .ofTr .first fun state input work => match state with
    | .first => match work 0 with
      | none => readAction none (some false)
      | some negative => readAction (some (.second negative)) none
    | .second negative => match work 0 with
      | none => readAction none (some false)
      | some positive => match ScheduleBits.decodePair negative positive with
        | none => readAction none (some false)
        | some move =>
          let start := RelativeScanSchedule.start move d
          readAction (some (.continuation start (family start).q₀)) none
    | .continuation start state =>
      let action := (family start).tr state input work
      { action with state := action.state.map (.continuation start) }

/-- Read the current movement from the source and run the corresponding native endpoint scan. -/
noncomputable def machine (d : Fin 3) := dispatcher d RelativeScanIndex.machine

private theorem continuation_follows {S : Type} (d : Fin 3)
    (family : Fin 5 → MultiTapeTM 3 Bool S) (start : Fin 5) :
    (dispatcher d family).Follows (family start) (.continuation start)
      (.mapState (Option.map (.continuation start))) :=
  fun _ _ _ h => tr_iff.mp h ▸ rfl

private theorem runFrom_continuation {S : Type} {input : List Bool} (d : Fin 3)
    (family : Fin 5 → MultiTapeTM 3 Bool S) (start : Fin 5)
    (c : Cfg 3 Bool S input) (t : ℕ) :
    (dispatcher d family).runFrom (c.mapState (Option.map (.continuation start))) t =
      ((family start).runFrom c t).mapState (Option.map (.continuation start)) :=
  runFrom_map ((continuation_follows d family start).stepHom
    (Cfg.mapState (Option.map (.continuation start))) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl)) c t

private theorem runFrom_readPair (input out : List Bool) (pre ss : List SignType)
    (move : SignType) (d : Fin 3) :
    let source := RelativeScan.encode pre ++ RelativeScan.encode (move :: ss)
    let start := RelativeScanSchedule.start move d
    (machine d).runFrom
      ((RelativeScanIndex.positionedConfig input source pre.length out).withState
        (some (machine d).q₀)) 2 =
      ((RelativeScanIndex.positionedConfig input source (pre.length + 1) out).withState
        (some (RelativeScanIndex.machine start).q₀)).mapState
          (Option.map (.continuation start)) := by
  dsimp only
  let source := RelativeScan.encode pre ++ RelativeScan.encode (move :: ss)
  let mid := tapesCfg input ![source, [], []] 0 ![2 * pre.length + 1, 0, 0] out
  have hlen : ((RelativeScan.encode pre).length : ℤ) = 2 * pre.length := by
    simp
  have hfirst : tapeOfList source (2 * pre.length) = some (RelativeScan.negative move) := by
    rw [← hlen, tapeOfList_ofNat]
    simp [source, RelativeScan.encode]
  have hsecond : tapeOfList source (2 * (pre.length : ℤ) + 1) =
      some (RelativeScan.positive move) := by
    rw [← hlen,
      show ((RelativeScan.encode pre).length : ℤ) + 1 =
        (((RelativeScan.encode pre).length + 1 : ℕ) : ℤ) by omega,
      tapeOfList_ofNat, List.getElem?_append_right (by omega)]
    simp [RelativeScan.encode]
  have h₀ : (machine d).step
      ((RelativeScanIndex.positionedConfig input source pre.length out).withState
        (some (machine d).q₀)) =
      mid.withState (some (.second (RelativeScan.negative move))) := by
    apply step_tapesCfg
      (a := readAction (some (.second (RelativeScan.negative move))) none)
    · simp [machine, dispatcher, tapesCfg, hfirst]
    · rfl
    · rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [readAction]
  have h₁ : (machine d).step
      (mid.withState (some (.second (RelativeScan.negative move)))) =
      ((RelativeScanIndex.positionedConfig input source (pre.length + 1) out).withState
        (some (RelativeScanIndex.machine (RelativeScanSchedule.start move d)).q₀)).mapState
          (Option.map (.continuation (RelativeScanSchedule.start move d))) := by
    apply step_tapesCfg
      (a := readAction (some (.continuation (RelativeScanSchedule.start move d)
        (RelativeScanIndex.machine (RelativeScanSchedule.start move d)).q₀)) none)
    · simp [machine, dispatcher, tapesCfg, hsecond]
    · rfl
    · rfl
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> simp [readAction, RelativeScanIndex.positionedConfig]; omega
  change (machine d).runFrom _ (1 + 1) = _
  simp only [runFrom_add, runFrom_one]
  rw [h₀, h₁]

/-- Reading the current pair selects the correct finite scanner and returns an absolute index.
The source is the original full column; the prefix is counted by the native rewind. -/
theorem runsBetween_fromPrefix (input out : List Bool) (pre ss : List SignType)
    (move : SignType) (d : Fin 3) :
    let source := RelativeScan.encode pre ++ RelativeScan.encode (move :: ss)
    let r := RelativeScan.evaluate ss (1 - (d : ℤ) + (move : ℤ))
    RunsBetween (machine d)
      (RelativeScanIndex.positionedConfig input source pre.length out)
      (RelativeScanIndex.finalConfig input source out
        { r with consumed := pre.length + 1 + r.consumed })
      (8 * (pre.length + 1) + 10 * r.consumed + 11)
      (3 * (8 * (pre.length + 1) + 10 * r.consumed + 12)) := by
  dsimp only
  apply RunsBetween.of_runFrom
  have h := (RelativeScanIndex.runsBetween_fromPrefix input out (pre ++ [move]) ss
    (RelativeScanSchedule.start move d)).1
  have hsource : RelativeScan.encode (pre ++ [move]) ++ RelativeScan.encode ss =
      RelativeScan.encode pre ++ RelativeScan.encode (move :: ss) := by
    simp only [RelativeScan.encode_append, RelativeScan.encode, List.append_assoc,
      List.cons_append, List.nil_append]
  simp only [List.length_append, List.length_singleton, RelativeScanSchedule.initialDistance_start,
    hsource] at h
  rw [show 8 * (pre.length + 1) + 10 * (RelativeScan.evaluate ss
    (1 - (d : ℤ) + (move : ℤ))).consumed + 11 =
      2 + (8 * (pre.length + 1) + 10 * (RelativeScan.evaluate ss
        (1 - (d : ℤ) + (move : ℤ))).consumed + 9) by omega, runFrom_add,
    runFrom_readPair, machine, runFrom_continuation, h]
  rfl

/-- The finite controller reads the actual queried movement and returns the block network's
endpoint result within a linear clock. Its source head is initially at the queried pair. -/
theorem runsBetween {k q : ℕ} (input out : List Bool) (σ : MultiTapePTM.Schedule k q)
    (i : Fin q) (h : Fin k) (d : Fin 3) :
    RunsBetween (machine d)
      (RelativeScanIndex.positionedConfig input
        (RelativeScan.encode (RelativeScanSchedule.column σ h)) i.val out)
      (RelativeScanIndex.finalConfig input
        (RelativeScan.encode (RelativeScanSchedule.column σ h)) out
        (RelativeScanSchedule.result σ i h d))
      (10 * q + 11) (30 * q + 36) := by
  let column := RelativeScanSchedule.column σ h
  have hp : (column.take i.val).length = i.val := by
    rw [List.length_take, RelativeScanSchedule.length_column, min_eq_left (by omega)]
  have hd : column.drop i.val = σ i (some h) :: column.drop (i.val + 1) := by
    rw [List.drop_eq_getElem_cons (i := i.val) (by simp [column])]
    simp [column, RelativeScanSchedule.column]
  have hsource : RelativeScan.encode (column.take i.val) ++
      RelativeScan.encode (σ i (some h) :: column.drop (i.val + 1)) =
      RelativeScan.encode column := by
    rw [← hd, ← RelativeScan.encode_append, List.take_append_drop]
  have hr := runsBetween_fromPrefix input out (column.take i.val) (column.drop (i.val + 1))
    (σ i (some h)) d
  dsimp only at hr
  rw [hp, hsource] at hr
  have hc := RelativeScan.consumed_le (column.drop (i.val + 1))
    (1 - (d : ℤ) + (σ i (some h) : ℤ))
  have hlen : column.length = q := RelativeScanSchedule.length_column σ h
  simp only [List.length_drop, hlen] at hc
  exact hr.mono (by omega) (by omega)

end Turing.MultiTapeTM.RelativeScanDispatch
