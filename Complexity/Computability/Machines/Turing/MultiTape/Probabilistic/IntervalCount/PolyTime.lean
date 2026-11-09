/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.IntervalCount
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pi
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Window
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

/-!
# Interval counts in polynomial time

The interval count on plain data (`Turing.MultiTapePTM.localIntervalCount`) is computable in
polynomial time, as long as its `2 ^ b` coin strings are polynomially many in the input. This is
the machine-simulation part of the polynomial-time construction of the block-counting networks
of #1833.

**Finite storage** (`Turing.MultiTapePTM.LocalCfg`) is encoded by `Turing.MultiTapePTM.encLocalCfg`:
the control and output track by their ranks, the input position in unary, the work tapes with all
their stored cells (`Turing.MultiTapeTM.encBiTape`), and the head positions in binary
(`Turing.MultiTapeTM.encIntBin`).

* **One coin step** (`Turing.MultiTapePTM.localCoinStep`) branches on the finite key of the
  control, the read symbols and the coin (`Turing.MultiTapeTM.ComputableInPolyTime.finite_cases`);
  every branch applies a fixed action. A step adds at most a constant to the encoded length.
* **A replay** (`Turing.MultiTapePTM.localRun`) is a fold of coin steps with additive growth.
* **The interval condition** compares the state, the output track, the head coordinates and the
  window cells after the replay, all from the encoded storage.
* **The interval count** counts the coin strings of `Cslib.BitString.enumList b` satisfying it.

## Main definitions

* `Turing.MultiTapePTM.encLocalCfg`: the encoding of finite storage.
* `Turing.MultiTapePTM.IntervalData`, `Turing.MultiTapePTM.encIntervalData`,
  `Turing.MultiTapePTM.encControlData`, `Turing.MultiTapePTM.IntervalData.count`: the arguments of
  an interval count, their encoding, and their count.

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_localRun`: replays are polynomial-time.
* `Turing.MultiTapePTM.IntervalData.computableInPolyTime_mk`,
  `Turing.MultiTapePTM.ControlData.computableInPolyTime_mk`: assembling the arguments.
* `Turing.MultiTapePTM.computableInPolyTime_localIntervalCount`: interval counts are
  polynomial-time when the `2 ^ b` coin strings are polynomially many in the input.
-/

public section

namespace Turing.MultiTapePTM

open MultiTapeNTM.ChoiceTable Cslib.Turing MultiTapeTM ComputableInPolyTime

variable {k : ℕ} {State : Type}

/-! ### Encoding finite storage -/

/-- Finite storage as the tuple of its fields. -/
@[expose] def LocalCfg.equivProd :
    LocalCfg k State ≃ Option State × ℕ × (Fin k → BiTape Bool) × (Fin k → ℤ) × OutputTrack where
  toFun l := (l.state, l.inputPos, l.workTapes, l.workTapePos, l.track)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Finite State]

/-- **The encoding of finite storage**: the control and the output track by their ranks, the input
position in unary, the work tapes with all their stored cells, and the head positions in
binary. -/
noncomputable def encLocalCfg : LocalCfg k State ↪ List Bool :=
  encOfEquiv LocalCfg.equivProd (encPair (encFinite (Option State)) (encPair encUnary
    (encPair (encPi (encBiTape encBool)) (encPair (encPi encIntBin) (encFinite OutputTrack)))))

/-! ### Rules for finite storage -/

section Rules

variable {α : Type} {input : α ↪ List Bool}

/-- Assemble finite storage from its certified fields. -/
private theorem localCfg_mk {state : α → Option State} {pos : α → ℕ}
    {tapes : α → Fin k → BiTape Bool} {coords : α → Fin k → ℤ} {track : α → OutputTrack}
    (hstate : ComputableInPolyTime state input (encFinite (Option State)))
    (hpos : ComputableInPolyTime pos input encUnary)
    (htapes : ComputableInPolyTime tapes input (encPi (encBiTape encBool)))
    (hcoords : ComputableInPolyTime coords input (encPi encIntBin))
    (htrack : ComputableInPolyTime track input (encFinite OutputTrack)) :
    ComputableInPolyTime (fun a => (⟨state a, pos a, tapes a, coords a, track a⟩ :
      LocalCfg k State)) input encLocalCfg :=
  (hstate.prod (hpos.prod (htapes.prod (hcoords.prod htrack)))).of_enc_eq fun _ => rfl

private theorem localCfg_parts : ComputableInPolyTime (LocalCfg.equivProd (k := k) (State := State))
    encLocalCfg (encPair (encFinite (Option State)) (encPair encUnary
      (encPair (encPi (encBiTape encBool)) (encPair (encPi encIntBin) (encFinite OutputTrack))))) :=
  of_eq fun _ => rfl

private theorem localCfg_state :
    ComputableInPolyTime (LocalCfg.state (k := k) (State := State)) encLocalCfg
      (encFinite (Option State)) :=
  localCfg_parts.fst'

private theorem localCfg_inputPos :
    ComputableInPolyTime (LocalCfg.inputPos (k := k) (State := State)) encLocalCfg encUnary :=
  localCfg_parts.snd'.fst'

private theorem localCfg_workTapes :
    ComputableInPolyTime (LocalCfg.workTapes (k := k) (State := State)) encLocalCfg
      (encPi (encBiTape encBool)) :=
  localCfg_parts.snd'.snd'.fst'

private theorem localCfg_workTapePos :
    ComputableInPolyTime (LocalCfg.workTapePos (k := k) (State := State)) encLocalCfg
      (encPi encIntBin) :=
  localCfg_parts.snd'.snd'.snd'.fst'

private theorem localCfg_track :
    ComputableInPolyTime (LocalCfg.track (k := k) (State := State)) encLocalCfg
      (encFinite OutputTrack) :=
  localCfg_parts.snd'.snd'.snd'.snd'

/-- Adding a binary integer, by two subtractions. -/
private theorem intBin_add' {left right : α → ℤ}
    (hleft : ComputableInPolyTime left input encIntBin)
    (hright : ComputableInPolyTime right input encIntBin) :
    ComputableInPolyTime (fun a => left a + right a) input encIntBin := by
  have h := intBin_sub.comp (hleft.prod (intBin_sub.comp ((const 0).prod hright)))
  simpa only [Function.comp_def, zero_sub, sub_neg_eq_add] using h

/-- The input symbol at a stored input position. -/
private theorem inputAt_eq_getD (x : List Bool) (j : ℕ) :
    inputAt x j = (none :: x.map some).getD j none := by
  cases j with
  | zero => rfl
  | succ j =>
    cases h : x[j]? <;> simp [inputAt, List.getD_eq_getElem?_getD, h]

/-- Reading the input at a computed position. -/
private theorem inputAt' {word : α → List Bool} {pos : α → ℕ}
    (hword : ComputableInPolyTime word input encBits)
    (hpos : ComputableInPolyTime pos input encUnary) :
    ComputableInPolyTime (fun a => inputAt (word a) (pos a)) input (encFinEnum (Option Bool)) := by
  have hsome : ComputableInPolyTime (some (α := Bool)) encBool (encFinEnum (Option Bool)) :=
    of_finite _
  have hlist : ComputableInPolyTime (fun a => none :: (word a).map some) input
      (encList (encFinEnum (Option Bool))) :=
    (const none).cons' ((map hsome).comp (bitsToList.comp hword))
  simpa only [inputAt_eq_getD] using listGetDWithInput hlist hpos none

end Rules

/-! ### One coin step -/

variable (machine : MultiTapePTM k Bool State)

/-- The finite key of a coin step: the control, the read symbols and the coin. -/
private def stepKey (p : (List Bool × LocalCfg k State) × Bool) :
    Option State × Option Bool × (Fin k → Option Bool) × Bool :=
  (p.1.2.state, inputAt p.1.1 p.1.2.inputPos, fun h => (p.1.2.workTapes h).head, p.2)

/-- A fixed action applied to finite storage. -/
private def applyAction (a : Action k Bool State) (p : (List Bool × LocalCfg k State) × Bool) :
    LocalCfg k State where
  state := a.state
  inputPos := moveInputPosNat p.1.1.length p.1.2.inputPos a.inputTape
  workTapes h := (p.1.2.workTapes h).step (a.workTapes h)
  workTapePos h := p.1.2.workTapePos h + (a.workTapes h).2
  track := p.1.2.track.emit a.output

/-- Applying a fixed action is polynomial-time. -/
private theorem computableInPolyTime_applyAction (a : Action k Bool State) :
    ComputableInPolyTime (applyAction (State := State) a)
      (encPair (encPair encBits encLocalCfg) encBool) encLocalCfg := by
  have hcfg := (fst (encPair encBits (encLocalCfg (k := k) (State := State))) encBool).snd'
  have hword := (fst (encPair encBits (encLocalCfg (k := k) (State := State))) encBool).fst'
  have h1 : ComputableInPolyTime (fun p : (List Bool × LocalCfg k State) × Bool => p.1.1.length)
      (encPair (encPair encBits encLocalCfg) encBool) encUnary := length_bits.comp hword
  have h2 : ComputableInPolyTime (fun p : (List Bool × LocalCfg k State) × Bool => p.1.2.inputPos)
      (encPair (encPair encBits encLocalCfg) encBool) encUnary := localCfg_inputPos.comp hcfg
  have h3 := (MultiTapeTM.ComputableInPolyTime.moveInputPosNat a.inputTape).comp (h1.prod h2)
  have h4 : ComputableInPolyTime
      (fun p : (List Bool × LocalCfg k State) × Bool => fun h => (p.1.2.workTapes h).step
        (a.workTapes h)) (encPair (encPair encBits encLocalCfg) encBool)
        (encPi (encBiTape encBool)) :=
    pi fun h => biTape_step (a.workTapes h) ((pi_apply _ h).comp (localCfg_workTapes.comp hcfg))
  have h5 : ComputableInPolyTime
      (fun p : (List Bool × LocalCfg k State) × Bool => fun h => p.1.2.workTapePos h +
        ((a.workTapes h).2 : ℤ)) (encPair (encPair encBits encLocalCfg) encBool)
        (encPi encIntBin) :=
    pi fun h => intBin_add' ((pi_apply _ h).comp (localCfg_workTapePos.comp hcfg)) (const _)
  have h6 : ComputableInPolyTime
      (fun p : (List Bool × LocalCfg k State) × Bool => p.1.2.track.emit a.output)
      (encPair (encPair encBits encLocalCfg) encBool) (encFinite OutputTrack) :=
    (of_finite fun t : OutputTrack => t.emit a.output).comp (localCfg_track.comp hcfg)
  exact localCfg_mk (const a.state) h3 h4 h5 h6

/-- The key of a coin step is polynomial-time. -/
private theorem computableInPolyTime_stepKey :
    ComputableInPolyTime (stepKey (k := k) (State := State))
      (encPair (encPair encBits encLocalCfg) encBool) (encFinite _) := by
  have hcfg := (fst (encPair encBits (encLocalCfg (k := k) (State := State))) encBool).snd'
  have hword := (fst (encPair encBits (encLocalCfg (k := k) (State := State))) encBool).fst'
  have hbit := snd (encPair encBits (encLocalCfg (k := k) (State := State))) encBool
  have hheads : ComputableInPolyTime
      (fun p : (List Bool × LocalCfg k State) × Bool => fun h => (p.1.2.workTapes h).head)
      (encPair (encPair encBits encLocalCfg) encBool) (encPi (encOption encBool)) :=
    pi fun h => (biTape_head encBool).comp ((pi_apply _ h).comp (localCfg_workTapes.comp hcfg))
  have hheads' : ComputableInPolyTime
      (fun p : (List Bool × LocalCfg k State) × Bool => fun h => (p.1.2.workTapes h).head)
      (encPair (encPair encBits encLocalCfg) encBool) (encFinite (Fin k → Option Bool)) :=
    (of_finite id).comp hheads
  have hsym := inputAt' hword (localCfg_inputPos.comp hcfg)
  have hall := (localCfg_state.comp hcfg).prod (hsym.prod (hheads'.prod hbit))
  exact (of_finite id).comp hall

/-- **One coin step is polynomial-time.** -/
private theorem computableInPolyTime_localCoinStep :
    ComputableInPolyTime (fun p : (List Bool × LocalCfg k State) × Bool =>
      machine.localCoinStep p.1.1 p.1.2 p.2)
      (encPair (encPair encBits encLocalCfg) encBool) encLocalCfg := by
  have h := finite_cases (tagEncoding := encFinite _) (computableInPolyTime_stepKey (k := k)
    (State := State))
    (branch := fun key => applyAction (machine.coinAction key.1 key.2.1 key.2.2.1 key.2.2.2))
    fun key => computableInPolyTime_applyAction _
  exact h

/-! ### Growth of a coin step -/

section Growth

private theorem length_encOption_bool_le (o : Option Bool) : (encOption encBool o).length ≤ 2 := by
  cases o <;> simp

private theorem length_encStackTape_eq (t : StackTape Bool) :
    (encStackTape encBool t).length =
      (t.toList.map fun a => 2 * (encOption encBool a).length + 1).sum := by
  rw [encStackTape_apply, length_encList]

private theorem length_encStackTape_tail_le (t : StackTape Bool) :
    (encStackTape encBool t.tail).length ≤ (encStackTape encBool t).length := by
  rw [length_encStackTape_eq, length_encStackTape_eq, StackTape.tail_toList]
  cases t.toList with
  | nil => simp
  | cons a l => simp

private theorem length_encStackTape_cons_le (o : Option Bool) (t : StackTape Bool) :
    (encStackTape encBool (StackTape.cons o t)).length ≤ (encStackTape encBool t).length + 5 := by
  have ho := length_encOption_bool_le o
  have hcons : (StackTape.cons o t).toList = o :: t.toList ∨
      (StackTape.cons o t).toList = t.toList := by
    rcases o with _ | a
    · rcases t with ⟨_ | ⟨hd, tl⟩, ht⟩
      · exact Or.inr rfl
      · exact Or.inl rfl
    · exact Or.inl (StackTape.cons_some_toList a t)
  rw [length_encStackTape_eq, length_encStackTape_eq]
  rcases hcons with h | h <;> rw [h]
  · simp only [List.map_cons, List.sum_cons]
    omega
  · omega

/-- A tape step adds at most `14` to the encoded tape. -/
private theorem length_encBiTape_step_le (t : BiTape Bool)
    (a : Option (Option Bool) × SignType) :
    (encBiTape encBool (t.step a)).length ≤ (encBiTape encBool t).length + 14 := by
  set w := a.1.elim t t.write with hw
  have hwl : w.left = t.left := by rcases a with ⟨_ | _, _⟩ <;> rfl
  have hwr : w.right = t.right := by rcases a with ⟨_ | _, _⟩ <;> rfl
  have hstep : t.step a = match a.2 with
      | .neg => w.moveLeft
      | .zero => w
      | .pos => w.moveRight := rfl
  have h1 := length_encOption_bool_le w.head
  have h2 := length_encOption_bool_le t.head
  have h3 := length_encOption_bool_le w.left.head
  have h4 := length_encOption_bool_le w.right.head
  have h5 := length_encStackTape_tail_le w.left
  have h6 := length_encStackTape_tail_le w.right
  have h7 := length_encStackTape_cons_le w.head w.right
  have h8 := length_encStackTape_cons_le w.head w.left
  rw [hwl] at h3 h5 h8
  rw [hwr] at h4 h6 h7
  rw [hstep]
  rcases a with ⟨_, _ | _ | _⟩ <;>
  simp only [encBiTape_apply, length_encPair, BiTape.moveLeft, BiTape.moveRight, hwl, hwr] <;>
  omega

/-- A table of values that each grow by at most `c` grows by at most `2 c` per entry. -/
private theorem length_encPi_le_add {Index Value : Type} [Fintype Index]
    (enc : Value ↪ List Bool) (f g : Index → Value) (c : ℕ)
    (h : ∀ i, (enc (g i)).length ≤ (enc (f i)).length + c) :
    (encPi enc g).length ≤ (encPi enc f).length + Fintype.card Index * (2 * c) := by
  simp only [encPi_apply, length_encList, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  calc _ ≤ ∑ i : Fin (Fintype.card Index),
        ((2 * (enc (f ((Fintype.equivFin Index).symm i))).length + 1) + 2 * c) :=
        Finset.sum_le_sum fun i _ => by have := h ((Fintype.equivFin Index).symm i); omega
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul]

/-- A step of `±1` adds at most two bits to a binary integer. -/
private theorem length_encIntBin_add_sign_le (z : ℤ) (d : SignType) :
    (encIntBin (z + d)).length ≤ (encIntBin z).length + 2 := by
  rw [length_encIntBin, length_encIntBin]
  have hd : ((d : ℤ)).natAbs ≤ 1 := by cases d <;> decide
  have habs : (z + d).natAbs ≤ z.natAbs + 1 := (Int.natAbs_add_le z d).trans (by omega)
  have := (Nat.size_le_size habs).trans (Nat.size_add_le z.natAbs 1)
  have h1 : (1 : ℕ).size = 1 := by decide
  omega

/-- The constant bounding the growth of a coin step. -/
private noncomputable def stepGrowth (k : ℕ) (State : Type) : ℕ :=
  2 * Nat.card (Option State) + 64 * k + 8

/-- **A coin step adds at most a constant to the encoded storage.** -/
private theorem length_encLocalCfg_localCoinStep_le (input : List Bool) (l : LocalCfg k State)
    (bit : Bool) :
    (encLocalCfg (machine.localCoinStep input l bit)).length ≤
      (encLocalCfg l).length + stepGrowth k State := by
  set a := machine.coinAction l.state (inputAt input l.inputPos) (fun h => (l.workTapes h).head)
    bit
  have hstate := length_encFinite_lt (machine.localCoinStep input l bit).state
  have htrack := length_encFinite_lt (machine.localCoinStep input l bit).track
  have hcard : Nat.card OutputTrack = 3 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hpos : (machine.localCoinStep input l bit).inputPos ≤ l.inputPos + 1 := by
    change moveInputPosNat input.length l.inputPos a.inputTape ≤ l.inputPos + 1
    have hd : ((a.inputTape : ℤ)) ≤ 1 := by cases a.inputTape <;> decide
    simp only [moveInputPosNat]
    omega
  have htapes := length_encPi_le_add (encBiTape encBool) l.workTapes
    (machine.localCoinStep input l bit).workTapes 14
    fun h => length_encBiTape_step_le (l.workTapes h) (a.workTapes h)
  have hcoords := length_encPi_le_add encIntBin l.workTapePos
    (machine.localCoinStep input l bit).workTapePos 2
    fun h => length_encIntBin_add_sign_le (l.workTapePos h) (a.workTapes h).2
  simp only [Fintype.card_fin] at htapes hcoords
  simp only [encLocalCfg, encOfEquiv_apply, LocalCfg.equivProd, Equiv.coe_fn_mk, length_encPair,
    encUnary_apply, List.length_replicate, stepGrowth] at hstate htrack ⊢
  omega

end Growth

/-! ### Replays -/

/-- **Replays are polynomial-time**: replaying computed coins from computed finite storage, on a
computed input. -/
theorem computableInPolyTime_localRun {α : Type} {enc : α ↪ List Bool}
    {input coins : α → List Bool} {start : α → LocalCfg k State}
    (hinput : ComputableInPolyTime input enc encBits)
    (hcoins : ComputableInPolyTime coins enc encBits)
    (hstart : ComputableInPolyTime start enc encLocalCfg) :
    ComputableInPolyTime (fun a => machine.localRun (input a) (coins a) (start a)) enc
      encLocalCfg := by
  have hfst := fst (encPair enc (encLocalCfg (k := k) (State := State))) encBool
  have hg : ComputableInPolyTime (fun p : (α × LocalCfg k State) × Bool =>
      ((input p.1.1, p.1.2), p.2)) (encPair (encPair enc encLocalCfg) encBool)
      (encPair (encPair encBits encLocalCfg) encBool) :=
    ((hinput.comp hfst.fst').prod hfst.snd').prod (snd _ _)
  have hstep : ComputableInPolyTime (fun p : (α × LocalCfg k State) × Bool =>
      machine.localCoinStep (input p.1.1) p.1.2 p.2) (encPair (encPair enc encLocalCfg) encBool)
      encLocalCfg := by
    simpa only [Function.comp_def] using (computableInPolyTime_localCoinStep machine).comp hg
  have h := foldlWithInput_of_bounded_growth (encA := encBool) (encL := encBits)
    (list := coins) (step := fun a => machine.localCoinStep (input a))
    hstart ⟨hcoins, hstep, inferInstance, inferInstance⟩ (growth := fun _ => stepGrowth k State)
    ⟨.const _, fun a l bit _ => length_encLocalCfg_localCoinStep_le machine (input a) l bit⟩
  exact h

/-! ### Tapes of windows, reads and head coordinates -/

section Window

variable {α : Type} {input : α ↪ List Bool}

private theorem ofList_eq_foldl (l : List (Option Bool)) :
    StackTape.ofList l = l.reverse.foldl (fun t a => StackTape.cons a t) StackTape.nil := by
  rw [StackTape.ofList, List.foldl_reverse]

/-- Loading a computed list of cells onto a stack tape. -/
private theorem stackTape_ofList {cells : α → List (Option Bool)}
    (hcells : ComputableInPolyTime cells input (encList (encOption encBool))) :
    ComputableInPolyTime (fun a => StackTape.ofList (cells a)) input (encStackTape encBool) := by
  have hstep : ComputableInPolyTime
      (fun p : (α × StackTape Bool) × Option Bool => StackTape.cons p.2 p.1.2)
      (encPair (encPair input (encStackTape encBool)) (encOption encBool))
      (encStackTape encBool) :=
    stackTape_cons (snd _ _) (fst _ _).snd'
  have h := foldlWithInput_of_bounded_growth (encA := encOption encBool)
    (encL := encList (encOption encBool)) (list := fun a => (cells a).reverse)
    (init := fun _ => StackTape.nil) (step := fun _ t a => StackTape.cons a t)
    (const _) ⟨listReverseWithInput hcells, hstep, inferInstance, inferInstance⟩
    (growth := fun _ => 5) ⟨.const _, fun _ t a _ => length_encStackTape_cons_le a t⟩
  simpa only [ofList_eq_foldl] using h

private theorem drop_eq_map_range (cells : List (Option Bool)) (n : ℕ) :
    cells.drop n = (List.range (cells.length - n)).map fun i => cells.getD (n + i) none := by
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  simp only [List.getElem_drop, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem]

/-- The tape holding computed cells with its head on a computed cell. -/
private theorem biTape_ofCells {cells : α → List (Option Bool)} {pos : α → ℕ}
    (hcells : ComputableInPolyTime cells input (encList (encOption encBool)))
    (hpos : ComputableInPolyTime pos input encUnary) :
    ComputableInPolyTime (fun a => BiTape.ofCells (cells a) (pos a)) input (encBiTape encBool) := by
  have hcells' := hcells.comp (fst input encUnary)
  have hleft : ComputableInPolyTime
      (fun a => (List.range (pos a)).map fun i => (cells a).getD (pos a - 1 - i) none) input
      (encList (encOption encBool)) :=
    mapWithInput (unary_range' hpos) (listGetDWithInput hcells'
      (unary_sub' (unary_sub' (hpos.comp (fst input encUnary)) (const 1)) (snd _ _)) none)
  have hright : ComputableInPolyTime
      (fun a => (List.range ((cells a).length - (pos a + 1))).map fun i =>
        (cells a).getD (pos a + 1 + i) none) input (encList (encOption encBool)) :=
    mapWithInput (unary_range' (unary_sub' ((length_list _).comp hcells)
      (unary_add' hpos (const 1))))
      (listGetDWithInput hcells' (unary_add' (unary_add' (hpos.comp (fst input encUnary))
        (const 1)) (snd _ _)) none)
  have h := biTape_mk (listGetDWithInput hcells hpos none) (stackTape_ofList hleft)
    (stackTape_ofList hright)
  simpa only [BiTape.ofCells, drop_eq_map_range] using h

/-- The sign of a binary integer is its first bit. -/
private theorem intBin_isNeg' {z : α → ℤ} (hz : ComputableInPolyTime z input encIntBin) :
    ComputableInPolyTime (fun a => decide (z a < 0)) input encBool := by
  have hbits : ComputableInPolyTime (fun z : ℤ => encIntBin z) encIntBin encBits :=
    of_eq fun _ => rfl
  exact ((headD false).comp hbits).comp hz

private theorem getD_none_eq_join (l : List (Option Bool)) (n : ℕ) :
    l.getD n none = l[n]?.join := by
  rw [List.getD_eq_getElem?_getD]
  cases l[n]? <;> rfl

/-- A read at an integer displacement, by the sign of the displacement. -/
private theorem read_eq (t : BiTape Bool) (z : ℤ) :
    t.read z = if z = 0 then t.head else if z < 0 then t.left.toList.getD ((-z).toNat - 1) none
      else t.right.toList.getD (z.toNat - 1) none := by
  rcases z with (_ | n) | n
  · rfl
  · have h1 : ¬ (Int.ofNat (n + 1) = 0) := by rw [Int.ofNat_eq_natCast]; omega
    have h2 : ¬ (Int.ofNat (n + 1) < 0) := by rw [Int.ofNat_eq_natCast]; omega
    rw [ite_eq_right h1, ite_eq_right h2, getD_none_eq_join]
    simp [BiTape.read, StackTape.read_eq_getElem?]
  · have h1 : ¬ (Int.negSucc n = 0) := by omega
    have h2 : Int.negSucc n < 0 := Int.negSucc_lt_zero n
    rw [ite_eq_right h1, ite_eq_left h2, getD_none_eq_join]
    simp [BiTape.read, StackTape.read_eq_getElem?]

/-- **Reading a computed tape at a computed displacement.** -/
private theorem biTape_read {tape : α → BiTape Bool} {z : α → ℤ}
    (htape : ComputableInPolyTime tape input (encBiTape encBool))
    (hz : ComputableInPolyTime z input encIntBin) :
    ComputableInPolyTime (fun a => (tape a).read (z a)) input (encOption encBool) := by
  simp only [read_eq]
  refine ite_decide (decide_eq' hz (const 0)) ((biTape_head _).comp htape)
    (ite_decide (intBin_isNeg' hz) ?_ ?_)
  · have hneg : ComputableInPolyTime (fun a => -z a) input encIntBin := by
      simpa only [Function.comp_def, zero_sub] using intBin_sub.comp ((const 0).prod hz)
    exact listGetD_binary none ((stackTape_toList _).comp ((biTape_left _).comp htape))
      (binary_sub' (intBin_toNat.comp hneg) (const 1))
  · exact listGetD_binary none ((stackTape_toList _).comp ((biTape_right _).comp htape))
      (binary_sub' (intBin_toNat.comp hz) (const 1))

/-- The coordinate of a head of computed storage. -/
private theorem localCfg_headCoord {l : α → LocalCfg k State}
    (hl : ComputableInPolyTime l input encLocalCfg) (head : Option (Fin k)) :
    ComputableInPolyTime (fun a => (l a).headCoord head) input encIntBin := by
  cases head with
  | none =>
    exact intBin_sub.comp
      ((intBin_natCast.comp (unary_to_binary.comp (localCfg_inputPos.comp hl))).prod (const 1))
  | some h => exact (pi_apply _ h).comp (localCfg_workTapePos.comp hl)

/-- The window cells of computed storage. -/
private theorem localCfg_windowCellsAt {b : α → ℕ} {j : α → ℤ} {l : α → LocalCfg k State}
    (hb : ComputableInPolyTime b input encUnary) (hj : ComputableInPolyTime j input encIntBin)
    (hl : ComputableInPolyTime l input encLocalCfg) (h : Fin k) :
    ComputableInPolyTime (fun a => (l a).windowCellsAt (b a) (j a) h) input
      (encList (encOption encBool)) := by
  have hfst := fst input encUnary
  have hbZ : ComputableInPolyTime (fun p : α × ℕ => (b p.1 : ℤ)) (encPair input encUnary)
      encIntBin := intBin_natCast.comp (unary_to_binary.comp (hb.comp hfst))
  have hcZ : ComputableInPolyTime (fun p : α × ℕ => (p.2 : ℤ)) (encPair input encUnary)
      encIntBin := intBin_natCast.comp (unary_to_binary.comp (snd _ _))
  have hoff : ComputableInPolyTime
      (fun p : α × ℕ => (b p.1 : ℤ) * (j p.1 - 1) + (p.2 : ℤ) - (l p.1).workTapePos h)
      (encPair input encUnary) encIntBin :=
    intBin_sub.comp ((intBin_add' (intBin_mul' hbZ (intBin_sub.comp ((hj.comp hfst).prod
      (const 1)))) hcZ).prod ((pi_apply _ h).comp (localCfg_workTapePos.comp (hl.comp hfst))))
  exact mapWithInput (unary_range' (unary_mul' (const 3) hb))
    (biTape_read ((pi_apply _ h).comp (localCfg_workTapes.comp (hl.comp hfst))) hoff)

/-- The stored input position of a coordinate. -/
private theorem val_inputPosOfCoord (x : List Bool) (p : ℤ) :
    (inputPosOfCoord x p).val = if !decide (p + 1 < 0) && decide (p + 1 - (x.length + 2) < 0)
      then min (x.length + 1) (p + 1).toNat else 0 := by
  unfold inputPosOfCoord
  by_cases h : 0 ≤ p + 1 ∧ p + 1 < x.length + 2
  · rw [dite_eq_left h]
    have : (!decide (p + 1 < 0) && decide (p + 1 - (x.length + 2) < 0)) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
        decide_eq_true_eq]
      omega
    rw [ite_eq_left this]
    simp only
    omega
  · rw [dite_eq_right h]
    have : ¬ (!decide (p + 1 < 0) && decide (p + 1 - (x.length + 2) < 0)) = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lt,
        decide_eq_true_eq]
      omega
    rw [ite_eq_right this]
    rfl

/-- The stored input position of a computed coordinate. -/
private theorem inputPosOfCoord' {word : α → List Bool} {p : α → ℤ}
    (hword : ComputableInPolyTime word input encBits)
    (hp : ComputableInPolyTime p input encIntBin) :
    ComputableInPolyTime (fun a => (inputPosOfCoord (word a) (p a)).val) input encUnary := by
  simp only [val_inputPosOfCoord]
  have hp1 := intBin_add' hp (const 1)
  have hlen : ComputableInPolyTime (fun a => (word a).length) input encUnary :=
    length_bits.comp hword
  have hlenZ : ComputableInPolyTime (fun a => ((word a).length : ℤ) + 2) input encIntBin :=
    intBin_add' (intBin_natCast.comp (unary_to_binary.comp hlen)) (const 2)
  refine ite (bool_and' (bool_not.comp (intBin_isNeg' hp1))
    (intBin_isNeg' (intBin_sub.comp (hp1.prod hlenZ)))) ?_ (const 0)
  exact binary_min_unary.comp ((unary_add' hlen (const 1)).prod (intBin_toNat.comp hp1))

end Window

/-! ### The interval count -/

section Count

/-- **The arguments of an interval count** on plain data. -/
structure IntervalData (k : ℕ) (State : Type) where
  /-- The input. -/
  input : List Bool
  /-- The block length. -/
  b : ℕ
  /-- The block indices at the start of the interval. -/
  J : Option (Fin k) → ℤ
  /-- The movements of the blocks. -/
  δ : Option (Fin k) → SignType
  /-- The entering control record. -/
  cIn : ControlData k State
  /-- The entering window cells. -/
  wIn : Fin k → List (Option Bool)
  /-- The leaving control record. -/
  cOut : ControlData k State
  /-- The leaving window cells. -/
  wOut : Fin k → List (Option Bool)

/-- The arguments of an interval count as a tuple. -/
@[expose] def IntervalData.equivProd : IntervalData k State ≃
    List Bool × ℕ × (Option (Fin k) → ℤ) × (Option (Fin k) → SignType) × ControlData k State ×
      (Fin k → List (Option Bool)) × ControlData k State × (Fin k → List (Option Bool)) where
  toFun d := (d.input, d.b, d.J, d.δ, d.cIn, d.wIn, d.cOut, d.wOut)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The encoding of a control record on plain data: the state and the track by their ranks, and
the offsets in unary. -/
noncomputable def encControlData : ControlData k State ↪ List Bool :=
  encPair (encFinite (Option State)) (encPair (encPi encUnary) (encFinite OutputTrack))

/-- **The encoding of the arguments of an interval count**: the input, the block length in unary,
the block indices in binary, the movements by their ranks, and the records and window cells. -/
noncomputable def encIntervalData : IntervalData k State ↪ List Bool :=
  encOfEquiv IntervalData.equivProd (encPair encBits (encPair encUnary (encPair (encPi encIntBin)
    (encPair (encFinite (Option (Fin k) → SignType)) (encPair encControlData
      (encPair (encPi (encList (encOption encBool))) (encPair encControlData
        (encPi (encList (encOption encBool))))))))))

/-- The interval count of its arguments. -/
@[expose] def IntervalData.count [DecidableEq State] (machine : MultiTapePTM k Bool State)
    (d : IntervalData k State) : ℕ :=
  machine.localIntervalCount d.b d.input d.J d.δ d.cIn d.wIn d.cOut d.wOut

variable {α : Type} {input : α ↪ List Bool}

/-- Assemble a control record on plain data from its certified components. -/
theorem ControlData.computableInPolyTime_mk {state : α → Option State}
    {off : α → Option (Fin k) → ℕ} {track : α → OutputTrack}
    (hstate : ComputableInPolyTime state input (encFinite (Option State)))
    (hoff : ComputableInPolyTime off input (encPi encUnary))
    (htrack : ComputableInPolyTime track input (encFinite OutputTrack)) :
    ComputableInPolyTime (fun a => ((state a, off a, track a) : ControlData k State)) input
      encControlData :=
  (hstate.prod (hoff.prod htrack)).of_enc_eq fun _ => rfl

/-- Assemble the arguments of an interval count from their certified components. -/
theorem IntervalData.computableInPolyTime_mk {word : α → List Bool} {b : α → ℕ}
    {J : α → Option (Fin k) → ℤ} {δ : α → Option (Fin k) → SignType}
    {cIn cOut : α → ControlData k State} {wIn wOut : α → Fin k → List (Option Bool)}
    (hword : ComputableInPolyTime word input encBits) (hb : ComputableInPolyTime b input encUnary)
    (hJ : ComputableInPolyTime J input (encPi encIntBin))
    (hδ : ComputableInPolyTime δ input (encFinite _))
    (hcIn : ComputableInPolyTime cIn input encControlData)
    (hwIn : ComputableInPolyTime wIn input (encPi (encList (encOption encBool))))
    (hcOut : ComputableInPolyTime cOut input encControlData)
    (hwOut : ComputableInPolyTime wOut input (encPi (encList (encOption encBool)))) :
    ComputableInPolyTime (fun a => (⟨word a, b a, J a, δ a, cIn a, wIn a, cOut a, wOut a⟩ :
      IntervalData k State)) input encIntervalData :=
  (hword.prod (hb.prod (hJ.prod (hδ.prod (hcIn.prod (hwIn.prod (hcOut.prod hwOut))))))).of_enc_eq
    fun _ => rfl

private theorem intervalData_parts : ComputableInPolyTime
    (IntervalData.equivProd (k := k) (State := State)) encIntervalData
    (encPair encBits (encPair encUnary (encPair (encPi encIntBin)
      (encPair (encFinite (Option (Fin k) → SignType)) (encPair encControlData
        (encPair (encPi (encList (encOption encBool))) (encPair encControlData
          (encPi (encList (encOption encBool)))))))))) :=
  of_eq fun _ => rfl

private theorem controlData_parts : ComputableInPolyTime (fun c : ControlData k State => c)
    encControlData (encPair (encFinite (Option State)) (encPair (encPi encUnary)
      (encFinite OutputTrack))) :=
  of_eq fun _ => rfl

/-- The finite storage of the embedded window of computed arguments. -/
private theorem localStartData' {d : α → IntervalData k State}
    (hd : ComputableInPolyTime d input encIntervalData) :
    ComputableInPolyTime (fun a => localStartData (d a).b (d a).input (d a).J (d a).cIn (d a).wIn)
      input encLocalCfg := by
  have hp := intervalData_parts.comp hd
  have hword : ComputableInPolyTime (fun a => (d a).input) input encBits := hp.fst'
  have hb : ComputableInPolyTime (fun a => (d a).b) input encUnary := hp.snd'.fst'
  have hJ : ComputableInPolyTime (fun a => (d a).J) input (encPi encIntBin) := hp.snd'.snd'.fst'
  have hc := controlData_parts.comp (hp.snd'.snd'.snd'.snd'.fst' :
    ComputableInPolyTime (fun a => (d a).cIn) input encControlData)
  have hw : ComputableInPolyTime (fun a => (d a).wIn) input
      (encPi (encList (encOption encBool))) := hp.snd'.snd'.snd'.snd'.snd'.fst'
  have hbZ : ComputableInPolyTime (fun a => ((d a).b : ℤ)) input encIntBin :=
    intBin_natCast.comp (unary_to_binary.comp hb)
  have hoff (head : Option (Fin k)) : ComputableInPolyTime (fun a => (d a).cIn.2.1 head) input
      encUnary := (pi_apply _ head).comp hc.snd'.fst'
  have hcoord (head : Option (Fin k)) : ComputableInPolyTime
      (fun a => ((d a).b : ℤ) * (d a).J head + ((d a).cIn.2.1 head : ℤ)) input encIntBin :=
    intBin_add' (intBin_mul' hbZ ((pi_apply _ head).comp hJ))
      (intBin_natCast.comp (unary_to_binary.comp (hoff head)))
  exact localCfg_mk hc.fst' (inputPosOfCoord' hword (hcoord none))
    (pi fun h => biTape_ofCells ((pi_apply _ h).comp hw) (unary_add' hb (hoff (some h))))
    (pi fun h => hcoord (some h)) hc.snd'.snd'

/-- The interval condition after the replay, as a Boolean test of the arguments and the
storage. -/
private def stepTest (d : IntervalData k State) (l : LocalCfg k State) [DecidableEq State] :
    Bool :=
  decide (l.state = d.cOut.1) && decide (l.track = d.cOut.2.2) &&
    (none :: (List.finRange k).map some).all (fun head => decide (d.cOut.2.1 head < d.b) &&
      decide (l.headCoord head = d.b * (d.J head + d.δ head) + d.cOut.2.1 head)) &&
    (List.finRange k).all fun h => decide (l.windowCellsAt d.b (d.J (some h)) h = d.wOut h)

omit [Finite State] in
private theorem stepTest_eq [DecidableEq State] (machine : MultiTapePTM k Bool State)
    (d : IntervalData k State) (coins : List Bool) :
    decide (machine.LocalIntervalStepData d.b d.input d.J d.δ d.cIn d.wIn d.cOut d.wOut coins) =
      stepTest d (machine.localRun d.input coins
        (localStartData d.b d.input d.J d.cIn d.wIn)) := by
  have hall : ∀ P : Option (Fin k) → Prop, (∀ head, P head) ↔
      ∀ head ∈ none :: (List.finRange k).map some, P head := by
    intro P
    constructor
    · exact fun h head _ => h head
    · intro h head
      cases head with
      | none => exact h none (by simp)
      | some i => exact h (some i) (by simp)
  rw [Bool.eq_iff_iff]
  simp only [stepTest, LocalIntervalStepData, decide_eq_true_eq, Bool.and_eq_true,
    List.all_eq_true, List.mem_finRange, true_implies, ← hall]
  tauto

/-- **The interval condition after the replay is polynomial-time.** -/
private theorem computableInPolyTime_stepTest [DecidableEq State] :
    ComputableInPolyTime (fun p : IntervalData k State × LocalCfg k State => stepTest p.1 p.2)
      (encPair encIntervalData encLocalCfg) encBool := by
  have hd := fst (encIntervalData (k := k) (State := State)) (encLocalCfg (k := k) (State := State))
  have hl := snd (encIntervalData (k := k) (State := State)) (encLocalCfg (k := k) (State := State))
  have hp := intervalData_parts.comp hd
  have hb : ComputableInPolyTime (fun p : IntervalData k State × LocalCfg k State => p.1.b)
      (encPair encIntervalData encLocalCfg) encUnary := hp.snd'.fst'
  have hJ : ComputableInPolyTime (fun p : IntervalData k State × LocalCfg k State => p.1.J)
      (encPair encIntervalData encLocalCfg) (encPi encIntBin) := hp.snd'.snd'.fst'
  have hδ : ComputableInPolyTime (fun p : IntervalData k State × LocalCfg k State => p.1.δ)
      (encPair encIntervalData encLocalCfg) (encFinite _) := hp.snd'.snd'.snd'.fst'
  have hc := controlData_parts.comp (hp.snd'.snd'.snd'.snd'.snd'.snd'.fst' :
    ComputableInPolyTime (fun p : IntervalData k State × LocalCfg k State => p.1.cOut)
      (encPair encIntervalData encLocalCfg) encControlData)
  have hw : ComputableInPolyTime (fun p : IntervalData k State × LocalCfg k State => p.1.wOut)
      (encPair encIntervalData encLocalCfg) (encPi (encList (encOption encBool))) :=
    hp.snd'.snd'.snd'.snd'.snd'.snd'.snd'
  have hbZ : ComputableInPolyTime
      (fun p : IntervalData k State × LocalCfg k State => (p.1.b : ℤ))
      (encPair encIntervalData encLocalCfg) encIntBin :=
    intBin_natCast.comp (unary_to_binary.comp hb)
  refine bool_and' (bool_and' (bool_and' (decide_eq' (localCfg_state.comp hl) hc.fst')
    (decide_eq' (localCfg_track.comp hl) hc.snd'.snd')) ?_) ?_
  · refine allConst _ fun head _ => bool_and' (unary_lt' ((pi_apply _ head).comp hc.snd'.fst') hb)
      (decide_eq' (localCfg_headCoord hl head) ?_)
    have hδZ : ComputableInPolyTime
        (fun p : IntervalData k State × LocalCfg k State => ((p.1.δ head : SignType) : ℤ))
        (encPair encIntervalData encLocalCfg) encIntBin :=
      (of_finite fun δ : Option (Fin k) → SignType => ((δ head : SignType) : ℤ)).comp hδ
    exact intBin_add' (intBin_mul' hbZ (intBin_add' ((pi_apply _ head).comp hJ) hδZ))
      (intBin_natCast.comp (unary_to_binary.comp ((pi_apply _ head).comp hc.snd'.fst')))
  · exact allConst _ fun h _ => decide_eq'
      (localCfg_windowCellsAt hb ((pi_apply _ (some h)).comp hJ) hl h) ((pi_apply _ h).comp hw)

/-- **Interval counts are polynomial-time** in their computed arguments, provided that the `2 ^ b`
coin strings, with their encodings, are polynomially many in the input: the count enumerates them
and replays each on the finite storage of the embedded window. -/
theorem computableInPolyTime_localIntervalCount [DecidableEq State]
    (machine : MultiTapePTM k Bool State) {d : α → IntervalData k State}
    (hd : ComputableInPolyTime d input encIntervalData) {size : ℕ → ℕ}
    (hsize : Cslib.PolynomiallyBounded size)
    (hbudget : ∀ a, 2 ^ (d a).b * (2 * (d a).b + 1) ≤ size (input a).length) :
    ComputableInPolyTime (fun a => (d a).count machine) input encUnary := by
  have hb : ComputableInPolyTime (fun a => (d a).b) input encUnary :=
    (intervalData_parts.comp hd).snd'.fst'
  have hlist := bitsEnumList hb hsize hbudget
  have hfst := fst input encBits
  have hrun : ComputableInPolyTime (fun p : α × List Bool => machine.localRun (d p.1).input p.2
      (localStartData (d p.1).b (d p.1).input (d p.1).J (d p.1).cIn (d p.1).wIn))
      (encPair input encBits) encLocalCfg :=
    computableInPolyTime_localRun machine ((intervalData_parts.comp (hd.comp hfst)).fst')
      (snd _ _) (localStartData' (hd.comp hfst))
  have htest : ComputableInPolyTime (fun p : α × List Bool =>
      decide (machine.LocalIntervalStepData (d p.1).b (d p.1).input (d p.1).J (d p.1).δ
        (d p.1).cIn (d p.1).wIn (d p.1).cOut (d p.1).wOut p.2)) (encPair input encBits)
        encBool := by
    simp only [stepTest_eq]
    simpa only [Function.comp_def] using computableInPolyTime_stepTest.comp
      ((hd.comp hfst).prod hrun)
  exact countPWithInput hlist htest

end Count

end Turing.MultiTapePTM
