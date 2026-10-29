/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Configuration
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Tape
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Foundations.Data.StackTape
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi

/-!
# Decoding finite configurations in polynomial time

`Turing.MultiTapeTM.decodeFiniteCfg` reads a finite configuration from any word, inverting
`Turing.MultiTapeTM.encFiniteCfg`, in polynomial time; a malformed word decodes to some
configuration. The fields are read off the frames of the encoding by `unframe` and `dropFrame`,
counts are clamped into range, and the cells of a stack tape are read by a finite transducer and
folded into a canonical tape by `StackTape.cons`, last cell first.

## Main definitions

* `Turing.MultiTapeTM.decodeStackTape`, `Turing.MultiTapeTM.decodeBiTape`: decoders of tapes.
* `Turing.MultiTapeTM.decodeTapes`: the decoder of a fixed finite family of tapes.
* `Turing.MultiTapeTM.decodeFiniteCfg`: the decoder of finite configurations.

## Main results

* `Turing.MultiTapeTM.decodeFiniteCfg_encFiniteCfg`: decoding inverts the encoding.
* `Turing.MultiTapeTM.ComputableInPolyTime.decodeTapes`: decoding a fixed finite family of
  tapes is polynomial-time.
* `Turing.MultiTapeTM.ComputableInPolyTime.decodeFiniteCfg`: decoding is polynomial-time.

## Implementation notes

Only `unframe`, `dropFrame`, list folds and finite transducers from the main development are
used. The cell transducer `Turing.MultiTapeTM.cellsTransducer` splits a framed list of cells, a
special case of splitting a word into its framed words; a general splitter with list decoders,
once available, could replace it, and `Turing.MultiTapeTM.decodeState` is a decoder of a finite
encoding from its length.
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib.Turing

/-! ### Cells -/

/-- The bits of a cell: whether it is occupied, then its symbol, `false` when it is blank. -/
def cellBits (cell : Option Bool) : List Bool := [cell.isSome, cell.getD false]

/-- The bits of a framed cell, from a summary of its framed word: blank while the word is empty,
otherwise occupied, with the second bit of the word as its symbol. -/
def contentBits : Option (Option Bool) → List Bool
  | none => [false, false]
  | some none => [true, false]
  | some (some symbol) => [true, symbol]

@[simp]
theorem length_contentBits (content : Option (Option Bool)) : (contentBits content).length = 2 := by
  rcases content with _ | _ | _ <;> rfl

/-- Record a bit of a framed word in its summary: only the first two bits matter. -/
def pushContent : Option (Option Bool) → Bool → Option (Option Bool)
  | none, _ => some none
  | some none, bit => some (some bit)
  | some (some symbol), _ => some (some symbol)

/-- The transducer emitting the bits of every framed cell. Its state is the summary of the framed
word read so far, and whether a bit of that word is expected next. -/
def cellsTransducer : Transducer Bool (Option (Option Bool) × Bool) where
  q₀ := (none, false)
  step state bit :=
    if state.2 then ((pushContent state.1 bit, false), [])
    else if bit then ((state.1, true), [])
    else ((none, false), contentBits state.1)
  final state := if state = (none, false) then [] else contentBits state.1
  length_step_le state bit := by split_ifs <;> simp
  length_final_le state := by split_ifs <;> simp

/-- The transducer emits the bits of a framed cell and continues after its frame. -/
theorem cellsTransducer_run_frame (cell : Option Bool) (rest : List Bool) :
    cellsTransducer.run (none, false) (frame (encOption encBool cell) ++ rest) =
      cellBits cell ++ cellsTransducer.run (none, false) rest := by
  rcases cell with _ | _ | _ <;> rfl

/-- On an encoded list of cells, the transducer emits the bits of every cell. -/
theorem cellsTransducer_run_encList (cells : List (Option Bool)) :
    cellsTransducer.run cellsTransducer.q₀ (encList (encOption encBool) cells) =
      cells.flatMap cellBits := by
  change cellsTransducer.run (none, false) _ = _
  induction cells with
  | nil => rfl
  | cons cell cells ih => rw [encList_cons, cellsTransducer_run_frame, ih, List.flatMap_cons]

/-! ### Stack tapes -/

/-- Read the reversed bits of cells into a tape, last cell first: a symbol bit is held until the
occupancy bit before it. -/
def stackStep : Option Bool × StackTape Bool → Bool → Option Bool × StackTape Bool
  | (none, tape), symbol => (some symbol, tape)
  | (some symbol, tape), occupied =>
    (none, StackTape.cons (if occupied then some symbol else none) tape)

/-- **Decode a stack tape** from any word, inverting `encStackTape encBool`. -/
def decodeStackTape (word : List Bool) : StackTape Bool :=
  ((cellsTransducer.run cellsTransducer.q₀ word).reverse.foldl stackStep (none, .nil)).2

/-- The fold over the reversed bits of cells prepends the cells, last first. -/
theorem foldl_stackStep (cells : List (Option Bool)) (tape : StackTape Bool) :
    (cells.flatMap cellBits).reverse.foldl stackStep (none, tape) =
      (none, cells.foldr StackTape.cons tape) := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    rw [List.flatMap_cons, List.reverse_append, List.foldl_append, ih]
    rcases cell with _ | _ <;> rfl

/-- Prepending the stored cells of a stack tape to the empty tape rebuilds it. -/
theorem _root_.Cslib.Turing.StackTape.foldr_cons_toList {Symbol : Type*}
    (tape : StackTape Symbol) : tape.toList.foldr StackTape.cons .nil = tape := by
  induction h : tape.toList generalizing tape with
  | nil => exact (StackTape.ext (by rw [h]; rfl)).symm
  | cons cell cells ih =>
    have htail : tape.tail.toList = cells := by rw [StackTape.tail_toList, h]; rfl
    have hhead : tape.head = cell := by
      cases tape with | mk values _ => cases h; rfl
    rw [List.foldr_cons, ih _ htail, ← hhead, StackTape.cons_head_tail]

/-- A word encoding a list of cells decodes to the tape of the cells, without the blank cells
at its end. -/
theorem decodeStackTape_encList (cells : List (Option Bool)) :
    decodeStackTape (encList (encOption encBool) cells) = cells.foldr StackTape.cons .nil := by
  rw [decodeStackTape, cellsTransducer_run_encList, foldl_stackStep]

/-- Decoding inverts the encoding of stack tapes. -/
theorem decodeStackTape_encStackTape (tape : StackTape Bool) :
    decodeStackTape (encStackTape encBool tape) = tape := by
  rw [encStackTape_apply, decodeStackTape_encList, StackTape.foldr_cons_toList]

/-- A step of `Turing.MultiTapeTM.stackStep` lengthens the encoded state by at most four bits. -/
theorem length_stackStep_le (state : Option Bool × StackTape Bool) (bit : Bool) :
    (encPair (encOption encBool) (encStackTape encBool) (stackStep state bit)).length ≤
      (encPair (encOption encBool) (encStackTape encBool) state).length + 4 := by
  rcases state with ⟨_ | symbol, tape⟩
  · simp [stackStep, encOption_some, encBool_apply]
  · simp only [stackStep, length_encPair, encStackTape_apply, StackTape.cons_toList]
    split_ifs <;> cases bit <;>
      simp [encOption_some, encBool_apply, encList_cons] <;> omega

/-! ### Two-sided tapes and configurations -/

/-- Decode a cell encoded by `encOption encBool`. -/
def decodeCell (word : List Bool) : Option Bool :=
  if word.isEmpty then none else some (word.tail.headD false)

/-- Decoding inverts the encoding of cells. -/
@[simp]
theorem decodeCell_encOption (cell : Option Bool) : decodeCell (encOption encBool cell) = cell := by
  rcases cell with _ | _ | _ <;> rfl

/-- **Decode a two-sided tape** from any word, inverting `encBiTape encBool`. -/
def decodeBiTape (word : List Bool) : BiTape Bool :=
  ⟨decodeCell (unframe word), decodeStackTape (unframe (dropFrame word)),
    decodeStackTape (dropFrame (dropFrame word))⟩

/-- Decoding inverts the encoding of two-sided tapes. -/
theorem decodeBiTape_encBiTape (tape : BiTape Bool) :
    decodeBiTape (encBiTape encBool tape) = tape := by
  simp only [decodeBiTape, encBiTape_apply, encPair_apply, unframe_frame_append,
    dropFrame_frame_append, decodeCell_encOption, decodeStackTape_encStackTape]

/-- Dropping `n` frames from an encoded list drops its first `n` elements. -/
theorem dropFrame_iterate_encList {α : Type*} (enc : α ↪ List Bool) (values : List α) (n : ℕ) :
    dropFrame^[n] (encList enc values) = encList enc (values.drop n) := by
  induction n generalizing values with
  | zero => rfl
  | succ n ih =>
    rcases values with _ | ⟨value, values⟩
    · have hnil : dropFrame [] = [] := rfl
      simpa [hnil] using ih []
    · rw [Function.iterate_succ_apply, encList_cons, dropFrame_frame_append, ih,
        List.drop_succ_cons]

/-- Decode a family of `k` tapes from any word, inverting `encPi (encBiTape encBool)`. -/
noncomputable def decodeTapes (k : ℕ) (word : List Bool) : Fin k → BiTape Bool :=
  fun tape => decodeBiTape (unframe (dropFrame^[(Fintype.equivFin (Fin k) tape).val] word))

/-- Decoding inverts the encoding of families of tapes. -/
theorem decodeTapes_encPi {k : ℕ} (tapes : Fin k → BiTape Bool) :
    decodeTapes k (encPi (encBiTape encBool) tapes) = tapes := by
  funext tape
  have hlt : (Fintype.equivFin (Fin k) tape).val <
      (List.ofFn fun i => tapes ((Fintype.equivFin (Fin k)).symm i)).length := by
    simpa using (Fintype.equivFin (Fin k) tape).isLt
  rw [decodeTapes, encPi_apply, dropFrame_iterate_encList, List.drop_eq_getElem_cons hlt,
    encList_cons, unframe_frame_append, decodeBiTape_encBiTape]
  simp

section Configuration

variable {k : ℕ} {State : Type} [Finite State]

/-- Decode a control state from the length of its encoding by `encFinite`, clamped into range. -/
noncomputable def decodeState (n : ℕ) : Option State :=
  letI := Fintype.ofFinite (Option State)
  (Fintype.equivFin (Option State)).symm ⟨min n (Fintype.card (Option State) - 1), by
    have := Fintype.card_pos (α := Option State)
    omega⟩

/-- A decoded control state is encoded by the clamped count. -/
theorem encFinite_decodeState (n : ℕ) : encFinite (Option State) (decodeState n) =
    encUnary (min n (Nat.card (Option State) - 1)) := by
  let := Fintype.ofFinite (Option State)
  simp [decodeState, encFinite, Nat.card_eq_fintype_card]

/-- Decoding inverts the encoding of control states. -/
@[simp]
theorem decodeState_length_encFinite (state : Option State) :
    decodeState (encFinite (Option State) state).length = state := by
  let := Fintype.ofFinite (Option State)
  have hlt := (Fintype.equivFin (Option State) state).isLt
  rw [decodeState, Equiv.symm_apply_eq]
  ext
  simp only [encFinite, Function.Embedding.coeFn_mk, encUnary_apply, List.length_replicate]
  omega

/-- **Decode a finite configuration** from any word, inverting `encFiniteCfg`. -/
noncomputable def decodeFiniteCfg (word : List Bool) : FiniteCfg k Bool State where
  input := unframe word
  state := decodeState (unframe (dropFrame word)).length
  inputPos := ⟨min (unframe (dropFrame (dropFrame word))).length ((unframe word).length + 1), by
    omega⟩
  workTapes := decodeTapes k (unframe (dropFrame (dropFrame (dropFrame word))))
  output := dropFrame (dropFrame (dropFrame (dropFrame word)))

/-- **Decoding inverts the encoding of finite configurations.** -/
theorem decodeFiniteCfg_encFiniteCfg (finite : FiniteCfg k Bool State) :
    decodeFiniteCfg (encFiniteCfg finite) = finite := by
  rcases finite with ⟨input, state, inputPos, workTapes, output⟩
  have hpos := inputPos.isLt
  simp only [decodeFiniteCfg, encFiniteCfg_apply, encPair_apply, encBits_apply,
    unframe_frame_append, dropFrame_frame_append, decodeState_length_encFinite,
    decodeTapes_encPi, encUnary_apply, List.length_replicate]
  have hinput : unframe (frame input ++ (frame (encFinite (Option State) state) ++
      (frame (List.replicate inputPos true) ++ (frame (encPi (encBiTape encBool) workTapes) ++
        output)))) = input := unframe_frame_append _ _
  refine FiniteCfg.ext hinput rfl ((Fin.heq_ext_iff
    (congrArg (fun word => word.length + 2) hinput)).mpr ?_) rfl rfl
  exact Nat.min_eq_left (by omega)

end Configuration

/-! ### Decoding in polynomial time -/

namespace ComputableTidilyInPolyTime

variable {α : Type} {input : α ↪ List Bool}

/-- Emitting the bits of the framed cells is linear-time. -/
private theorem cellsTransducer_run : ComputableTidilyInPolyTime
    (cellsTransducer.run cellsTransducer.q₀) encBits encBits :=
  of_linear (cellsTransducer.computableTidilyInLinearTimeAndSpace fun _ => rfl)

private theorem stackStep_eq (state : Option Bool × StackTape Bool) (bit : Bool) :
    stackStep state bit = (match state.1, bit with
      | none, symbol => fun tape => (some symbol, tape)
      | some symbol, occupied => fun tape =>
        (none, StackTape.cons (if occupied then some symbol else none) tape)) state.2 := by
  rcases state with ⟨_ | _, _⟩ <;> rfl

/-- A step of the stack-tape fold is polynomial-time: it branches on its finite part. -/
private theorem stackStep :
    ComputableTidilyInPolyTime (fun p : (Option Bool × StackTape Bool) × Bool =>
      Turing.MultiTapeTM.stackStep p.1 p.2)
    (encPair (encPair (encOption encBool) (encStackTape encBool)) encBool)
    (encPair (encOption encBool) (encStackTape encBool)) := by
  simp only [stackStep_eq]
  have htape := (snd (encOption encBool) (encStackTape encBool)).comp
    (fst (encPair (encOption encBool) (encStackTape encBool)) encBool)
  refine finite_cases (tag := fun p : (Option Bool × StackTape Bool) × Bool => (p.1.1, p.2))
    (branch := fun tag p => (match tag.1, tag.2 with
      | none, symbol => fun tape => (some symbol, tape)
      | some symbol, occupied => fun tape =>
        (none, StackTape.cons (if occupied then some symbol else none) tape)) p.1.2)
    (tagEncoding := encPair (encOption encBool) encBool)
    (((fst _ _).comp (fst _ _)).prod (snd _ _)) fun tag => ?_
  rcases tag with ⟨_ | symbol, bit⟩
  · exact (const _).prod htape
  · exact (const _).prod (stackTape_cons (const _) htape)

/-- **Decoding a stack tape is polynomial-time.** -/
private theorem decodeStackTape :
    ComputableTidilyInPolyTime MultiTapeTM.decodeStackTape encBits (encStackTape encBool) := by
  have hbits := bitsReverse.comp cellsTransducer_run
  have hfold := foldl' (encA := encBool) (encL := encBits) hbits (const (none, StackTape.nil))
    stackStep (B := fun word => 1 + 4 * (cellsTransducer.run cellsTransducer.q₀ word).length)
    ((PolyBounded.const 1).add ((PolyBounded.const 4).mul (polyBounded_length cellsTransducer_run)))
    fun word i _ => by
      have hgrowth : ∀ (bits : List Bool) state,
          (encPair (encOption encBool) (encStackTape encBool)
            (bits.foldl Turing.MultiTapeTM.stackStep state)).length ≤
          (encPair (encOption encBool) (encStackTape encBool) state).length + 4 * bits.length := by
        intro bits
        induction bits with
        | nil => simp
        | cons bit bits ih =>
          intro state
          have := length_stackStep_le state bit
          have := ih (Turing.MultiTapeTM.stackStep state bit)
          simp only [List.foldl_cons, List.length_cons]
          omega
      have := hgrowth (((cellsTransducer.run cellsTransducer.q₀ word).reverse.take i)) (none, .nil)
      simp only [List.length_take, List.length_reverse, Function.comp_apply] at this ⊢
      have hnil : (encPair (encOption encBool) (encStackTape encBool)
          ((none : Option Bool), (StackTape.nil : StackTape Bool))).length = 1 := rfl
      have : min i (cellsTransducer.run cellsTransducer.q₀ word).length ≤
          (cellsTransducer.run cellsTransducer.q₀ word).length := min_le_right _ _
      omega
  exact (snd (encOption encBool) (encStackTape encBool)).comp hfold

/-- Decoding a cell is polynomial-time. -/
private theorem decodeCell :
    ComputableTidilyInPolyTime MultiTapeTM.decodeCell encBits (encOption encBool) := by
  unfold Turing.MultiTapeTM.decodeCell
  exact (listIsEmpty (encA := encBool)).cond (const none)
    ((optionSome encBool).comp ((headD false).comp (tail (encA := encBool))))

/-- **Decoding a two-sided tape is polynomial-time.** -/
private theorem decodeBiTape :
    ComputableTidilyInPolyTime MultiTapeTM.decodeBiTape encBits (encBiTape encBool) :=
  biTape_mk (decodeCell.comp unframe) (decodeStackTape.comp (unframe.comp dropFrame))
    (decodeStackTape.comp (dropFrame.comp dropFrame))

/-- Dropping a fixed number of frames is polynomial-time. -/
private theorem dropFrame_iterate (n : ℕ) :
    ComputableTidilyInPolyTime (MultiTapeTM.dropFrame^[n]) encBits encBits := by
  induction n with
  | zero => exact id'
  | succ n ih => simpa only [Function.iterate_succ'] using dropFrame.comp ih

/-- Decoding a family of tapes is polynomial-time. -/
private theorem decodeTapes (k : ℕ) :
    ComputableTidilyInPolyTime (MultiTapeTM.decodeTapes k) encBits
      (encPi (encBiTape encBool)) :=
  pi fun _ => decodeBiTape.comp (unframe.comp (dropFrame_iterate _))

variable {k : ℕ} {State : Type} [Finite State]

/-- **Decoding a finite configuration is polynomial-time.** -/
private theorem decodeFiniteCfg : ComputableTidilyInPolyTime
    (MultiTapeTM.decodeFiniteCfg (k := k) (State := State)) encBits encFiniteCfg := by
  have hlength := length encBool (encL := encBits)
  have hstate : ComputableTidilyInPolyTime (fun word =>
      decodeState (State := State) (MultiTapeTM.unframe (MultiTapeTM.dropFrame word)).length)
      encBits (encFinite (Option State)) :=
    (unary_min.comp ((hlength.comp (unframe.comp dropFrame)).prod (const _))).of_enc_eq
      fun _ => encFinite_decodeState _
  exact finiteCfg_mk unframe hstate
    (unary_min.comp ((hlength.comp (unframe.comp (dropFrame.comp dropFrame))).prod
      (unary_add.comp ((hlength.comp unframe).prod (const 1)))))
    ((decodeTapes k).comp (unframe.comp (dropFrame.comp (dropFrame.comp dropFrame))))
    (dropFrame.comp (dropFrame.comp (dropFrame.comp dropFrame)))

end ComputableTidilyInPolyTime

namespace ComputableInPolyTime

/-- **Decoding a stack tape is polynomial-time.** -/
theorem decodeStackTape :
    ComputableInPolyTime MultiTapeTM.decodeStackTape encBits (encStackTape encBool) :=
  ComputableTidilyInPolyTime.decodeStackTape.computableInPolyTime

/-- **Decoding a two-sided tape is polynomial-time.** -/
theorem decodeBiTape :
    ComputableInPolyTime MultiTapeTM.decodeBiTape encBits (encBiTape encBool) :=
  ComputableTidilyInPolyTime.decodeBiTape.computableInPolyTime

/-- Decoding a fixed finite family of tapes is polynomial-time. -/
theorem decodeTapes (k : ℕ) :
    ComputableInPolyTime (MultiTapeTM.decodeTapes k) encBits (encPi (encBiTape encBool)) :=
  (ComputableTidilyInPolyTime.decodeTapes k).computableInPolyTime

variable {k : ℕ} {State : Type} [Finite State]

/-- **Decoding a finite configuration is polynomial-time.** -/
theorem decodeFiniteCfg : ComputableInPolyTime
    (MultiTapeTM.decodeFiniteCfg (k := k) (State := State)) encBits encFiniteCfg :=
  ComputableTidilyInPolyTime.decodeFiniteCfg.computableInPolyTime

end ComputableInPolyTime

end Turing.MultiTapeTM
