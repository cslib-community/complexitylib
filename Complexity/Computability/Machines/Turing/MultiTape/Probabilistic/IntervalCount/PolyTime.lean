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
* `Turing.MultiTapePTM.IntervalData`, `Turing.MultiTapePTM.encIntervalData`: the arguments of an
  interval count and their encoding.

## Main results

* `Turing.MultiTapePTM.computableInPolyTime_localRun`: replays are polynomial-time.
* `Turing.MultiTapePTM.computableInPolyTime_localIntervalCount`: interval counts are
  polynomial-time when `2 ^ b` is polynomial in the input.
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

end Turing.MultiTapePTM
