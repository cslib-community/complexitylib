/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAccess
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryNormalization
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.ListSlice
import Mathlib.Data.List.Induction

/-!
# Native decoding of runtime-width Boolean block labels

The decoder checks the positive width and exact word length before reading the existing explicit
layout. It reads only fixed control tags by a finite table. Every runtime residue is binary,
and work windows are decoded by streaming pairs of actual input bits. A malformed short word
never allocates cells according to an untrusted binary width.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Encoding.NativeDecode

open Cslib Cslib.BitString MultiTapeTM MultiTapeTM.ComputableInSpace
open MultiTapeNTM.ChoiceTable QueryReplay

variable {k s : ℕ} {Q : Type}

/-- Read a little-endian numeric field from an explicitly stored bit word. -/
@[expose] def readNat (word : List Bool) (offset count : ℕ) : ℕ :=
  ofBits ((word.drop offset).take count)

/-- Canonical replay codes distinguish blank, written zero and written one. -/
@[expose] def cellCode (first second : Bool) : ℕ :=
  if first then if second then 2 else 1 else 0

/-- Decode adjacent bit pairs, discarding an unmatched final bit. -/
@[expose] def cells : List Bool → List ℕ
  | first :: second :: rest => cellCode first second :: cells rest
  | _ => []

/-- Decode the fixed finite control rank, treating unused ranks as halted. -/
@[expose] def state (e : Q ≃ Fin s) (rank : ℕ) : Option Q :=
  if h : rank < s + 1 then (stateIndex e).symm ⟨rank, h⟩ else none

/-- First output-track bit in the full word, including the outer FAIL bit. -/
@[expose] def trackOffset (k s b : ℕ) : ℕ := 1 + (s + 1).size + (k + 1) * b.size

/-- Decode fields without a width-dependent runtime type. Window slices are bounded by actual
input storage, even when their declared binary width is malformed. -/
@[expose] noncomputable def payload (e : Q ≃ Fin s) (b : ℕ) (word : List Bool) : RawResult k Q :=
  (state e (readNat word 1 (s + 1).size),
    fun h => readNat word (1 + (s + 1).size + ((finSuccEquiv k).symm h).val * b.size)
      b.size % b,
    if word.getD (trackOffset k s b + 1) false then .other
    else if word.getD (trackOffset k s b) false then .accept else .empty,
    fun h => cells ((word.drop (trackOffset k s b + 2 + h.val * (6 * b))).take (6 * b)))

/-- Reject zero width, malformed word length and the existing outer FAIL tag. -/
@[expose] noncomputable def parse (e : Q ≃ Fin s) (p : ℕ × List Bool) : Option (RawResult k Q) :=
  if p.1 = 0 ∨ p.2.length ≠ width k s p.1 then none
  else if p.2.headD false then some (payload e p.1 p.2) else none

/-- Successful parsing exposes the exact input shape and the decoded payload. -/
theorem parse_eq_some_iff (e : Q ≃ Fin s) (b : ℕ) (word : List Bool) (raw : RawResult k Q) :
    parse e (b, word) = some raw ↔ b ≠ 0 ∧ word.length = width k s b ∧
      word.headD false = true ∧ raw = payload e b word := by
  constructor
  · intro hp
    unfold parse at hp
    split at hp
    · contradiction
    · rename_i hbad
      have hb : b ≠ 0 := fun h => hbad (Or.inl h)
      have hw : word.length = width k s b := by
        by_contra h
        exact hbad (Or.inr h)
      split at hp
      · rename_i ht
        exact ⟨hb, hw, ht, (Option.some.inj hp).symm⟩
      · contradiction
  · rintro ⟨hb, hw, ht, rfl⟩
    simp only [parse, hb, hw, ne_eq, not_true_eq_false, or_self, ↓reduceIte, ht]


private theorem wordDrop_inSpace : ComputableInSpace
    (fun p : List Bool × ℕ => p.1.drop p.2) (encPair encBits encNat) encBits
    (fun p => (encPair encBits encNat p).length) := by
  have htail : ComputableInSpace List.tail encBits encBits (fun w => w.length) :=
    of_inO (.of_linear (ListEncoding.tail encBool))
  have h := iterate (snd encBits encNat) (fst encBits encNat) htail
    (Q := fun p => p.1.length) (B := fun p => p.1.length)
    (fun p i _ => by simp [List.tail_iterate]) (fun p i _ => by simp [List.tail_iterate])
  refine h.weaken (.of_le_linear 8 8 fun p => ?_) |>.of_enc_eq ?_
  · simp only [length_encPair, encBits_apply]
    omega
  · intro p
    rw [List.tail_iterate]

private theorem wordReverse_inSpace : ComputableInSpace List.reverse encBits encBits
    (fun w => w.length) := of_inO ComputableInDegree.bitsReverse.inO_one

private theorem wordLength_inSpace : ComputableInSpace List.length encBits encNat
    (fun w => w.length) :=
  (of_inO ComputableInO.lengthNat).weaken (.of_le_linear 1 1 fun _ => by omega)

private theorem wordTake_inSpace : ComputableInSpace
    (fun p : List Bool × ℕ => p.1.take p.2) (encPair encBits encNat) encBits
    (fun p => (encPair encBits encNat p).length) := by
  have hw := fst encBits encNat
  have hn := snd encBits encNat
  have hrev := budget_comp_linear wordReverse_inSpace hw
  have hlen := budget_comp_linear wordLength_inSpace hw
  have hdrop := budget_comp_linear wordDrop_inSpace
    (budget_prod hrev (budget_natSub hlen hn))
  refine (budget_comp_linear wordReverse_inSpace hdrop).of_enc_eq ?_
  intro p
  rw [← List.reverse_take, List.reverse_reverse]

/-- Slice a runtime bit word using binary offset and count, in linear encoded-input space. -/
theorem slice_inSpace : ComputableInSpace
    (fun p : List Bool × ℕ × ℕ => (p.1.drop p.2.1).take p.2.2)
    (encPair encBits (encPair encNat encNat)) encBits
    (fun p => (encPair encBits (encPair encNat encNat) p).length) := by
  have hw := fst encBits (encPair encNat encNat)
  have hn := snd encBits (encPair encNat encNat)
  exact budget_comp_linear wordTake_inSpace
    (budget_prod (budget_comp_linear wordDrop_inSpace (budget_prod hw hn.fst')) hn.snd')

/-- Numeric fields use the direct charged binary-word normalization machine. -/
theorem readNat_inSpace : ComputableInSpace
    (fun p : List Bool × ℕ × ℕ => readNat p.1 p.2.1 p.2.2)
    (encPair encBits (encPair encNat encNat)) encNat
    (fun p => (encPair encBits (encPair encNat encNat) p).length) :=
  budget_comp_linear (of_inO ComputableInO.bitsToNat) slice_inSpace

private theorem bit_inSpace : ComputableInSpace
    (fun p : List Bool × ℕ => p.1.getD p.2 false) (encPair encBits encNat) encBool
    (fun p => (encPair encBits encNat p).length) := by
  have hhead : ComputableInSpace (fun w : List Bool => w.headD false) encBits encBool
      (fun w => w.length) := of_inO (.of_linear (ListEncoding.headD false))
  refine (budget_comp_linear hhead wordDrop_inSpace).of_enc_eq ?_
  intro p
  rw [List.getD_eq_getElem?_getD, List.headD_eq_head?_getD, List.head?_drop]

private abbrev Scan := Bool × Bool × List ℕ
private abbrev encScan : Scan ↪ List Bool := encPair encBool (encPair encBool (encList encNat))

private def scan (q : Scan) (bit : Bool) : Scan :=
  if q.1 then (false, false, cellCode q.2.1 bit :: q.2.2) else (true, bit, q.2.2)

private theorem scan_inSpace : ComputableInSpace (fun p : Scan × Bool => scan p.1 p.2)
    (encPair encScan encBool) encScan (fun p => (encPair encScan encBool p).length) := by
  have hq := fst encScan encBool
  have hbit := snd encScan encBool
  have hfirst := hq.snd'.fst'
  have hacc := hq.snd'.snd'
  have hcode := budget_finite (encC := encNat) (fun p : Bool × Bool => cellCode p.1 p.2)
    (budget_prod hfirst hbit)
  exact budget_ite hq.fst'
    (budget_prod (budget_const false (.refl _))
      (budget_prod (budget_const false (.refl _)) (budget_cons hcode hacc)))
    (budget_prod (budget_const true (.refl _)) (budget_prod hbit hacc))

private theorem scan_length (q : Scan) (bit : Bool) :
    (encList encNat (scan q bit).2.2).length ≤ (encList encNat q.2.2).length + 5 := by
  rcases q with ⟨a, b, acc⟩
  cases a <;> cases b <;> cases bit <;>
    simp [scan, cellCode, encList_cons, show Nat.bits 2 = [false, true] from rfl]

private theorem scan_fold_length (word : List Bool) (q : Scan) :
    (encList encNat (word.foldl scan q).2.2).length ≤
      (encList encNat q.2.2).length + 5 * word.length := by
  induction word generalizing q with
  | nil => simp
  | cons bit word ih =>
    have h := ih (scan q bit)
    have hstep := scan_length q bit
    simp only [List.foldl_cons, List.length_cons]
    omega

private theorem scan_fold_cells (word : List Bool) (acc : List ℕ) :
    (word.foldl scan (false, false, acc)).2.2 = (cells word).reverse ++ acc := by
  induction word using List.twoStepInduction generalizing acc with
  | nil => rfl
  | singleton bit => rfl
  | cons_cons first second word ih _ =>
    change (word.foldl scan (false, false, cellCode first second :: acc)).2.2 =
      (cellCode first second :: cells word).reverse ++ acc
    rw [ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- Decode actual pairs of input bits in linear space, with at most one cell per two bits. -/
theorem cells_inSpace : ComputableInSpace cells encBits (encList encNat)
    (fun word => word.length) := by
  have hl : ComputableInSpace (fun word : List Bool => word) encBits encBits
      (fun word => word.length) := of_inO ComputableInDegree.id'.inO_one
  have hinit : ComputableInSpace (fun _ : List Bool => ((false, false, []) : Scan)) encBits
      encScan (fun word => word.length) := budget_const _ (.refl _)
  have hstate (word : List Bool) (i : ℕ) (hi : i ≤ word.length) :
      (encScan ((word.take i).foldl scan (false, false, []))).length ≤ 6 + 5 * word.length := by
    have h := scan_fold_length (word.take i) (false, false, [])
    simp only [encList_nil, List.length_nil, List.length_take] at h
    simp only [encScan, length_encPair, encBool_apply, List.length_singleton]
    omega
  have hspace (word : List Bool) (i : ℕ) (hi : i < word.length) :
      (encPair encScan encBool ((word.take i).foldl scan (false, false, []), word[i])).length ≤
        20 * (word.length + 1) := by
    have h := hstate word i hi.le
    rw [length_encPair]
    simp only [encBool_apply, List.length_singleton]
    omega
  have hf := ComputableInSpace.foldl hl hinit scan_inSpace hspace hstate
  have hout := budget_comp_linear (listReverse encNat) hf.snd'.snd'
  refine hout.weaken (.of_le_linear 100 100 fun _ => by
    simp only [encBits_apply]
    omega) |>.of_enc_eq ?_
  intro word
  simp only [scan_fold_cells, List.append_nil, List.reverse_reverse]

/-- Streaming bit pairs creates exactly one cell for every two input bits. -/
theorem length_cells (word : List Bool) : (cells word).length = word.length / 2 := by
  induction word using List.twoStepInduction with
  | nil => rfl
  | singleton bit => simp [cells]
  | cons_cons first second word ih _ =>
    simp only [cells, List.length_cons, ih]
    omega

/-- Every streamed cell is one of the three canonical replay codes. -/
theorem mem_cells_le (word : List Bool) : ∀ n ∈ cells word, n ≤ 2 := by
  induction word using List.twoStepInduction with
  | nil => simp [cells]
  | singleton bit => simp [cells]
  | cons_cons first second word ih _ =>
    intro n hn
    simp only [cells, List.mem_cons] at hn
    rcases hn with rfl | hn
    · cases first <;> cases second <;> decide
    · exact ih n hn

/-- A correctly sized full label yields exactly three blocks of cells on every work tape,
including unused bit words and labels whose outer tag is FAIL. -/
theorem length_payload_cells_of_length (e : Q ≃ Fin s) (b : ℕ) (word : List Bool)
    (hlen : word.length = width k s b) (h : Fin k) :
    ((payload e b word).2.2.2 h).length = 3 * b := by
  change (cells ((word.drop (trackOffset k s b + 2 + h.val * (6 * b))).take (6 * b))).length = _
  rw [length_cells]
  have hoff : trackOffset k s b + 2 + h.val * (6 * b) + 6 * b ≤ word.length := by
    have hmul := Nat.mul_le_mul_right (6 * b) (Nat.succ_le_of_lt h.isLt)
    rw [hlen, width_eq]
    unfold trackOffset
    nlinarith
  simp only [List.length_take, List.length_drop]
  rw [min_eq_left (by omega)]
  omega

/-- The explicit fixed-width Boolean representation supplies canonical-sized replay windows. -/
theorem length_payload_cells (e : Q ≃ Fin s) (b : ℕ) (bits : BitString (width k s b))
    (h : Fin k) : ((payload e b (List.ofFn bits)).2.2.2 h).length = 3 * b :=
  length_payload_cells_of_length e b (List.ofFn bits) (List.length_ofFn) h

variable [Finite Q]

private theorem state_inSpace (e : Q ≃ Fin s) : ComputableInSpace (state e) encNat
    (encFinite (Option Q)) (fun n => (encNat n).length) := by
  classical
  let tags := List.ofFn fun i : Fin (s + 1) => (stateIndex e).symm i
  have h := dispatch tags none (fun tag _ => tag)
    (fun tag => budget_const (encB := encFinite (Option Q)) tag (.refl _))
    (of_inO (ComputableInDegree.id' (enc := encNat)).inO_one)
  refine h.of_enc_eq ?_
  intro n
  by_cases hn : n < s + 1
  · simp only [state, hn, ↓reduceDIte]
    rw [List.getD_eq_getElem _ _ (by simpa only [tags, List.length_ofFn] using hn)]
    simp only [tags, List.getElem_ofFn]
  · simp only [state, hn, ↓reduceDIte]
    rw [List.getD_eq_default _ _ (by simpa only [tags, List.length_ofFn] using Nat.le_of_not_gt hn)]

/-- Runtime width and an actual stored Boolean label. -/
abbrev encArgs : (ℕ × List Bool) ↪ List Bool := encPair encNat encBits

private theorem trackOffset_inSpace : ComputableInSpace
    (fun p : ℕ × List Bool => trackOffset k s p.1) encArgs encNat
    (fun p => (encArgs p).length) := by
  have hb := fst encNat encBits
  have hsize := budget_comp_linear natSize hb
  exact budget_natAdd (budget_const (1 + (s + 1).size) (.refl _))
    (budget_natMul (budget_const (k + 1) (.refl _)) hsize)

private theorem payload_inSpace (e : Q ≃ Fin s) : ComputableInSpace
    (fun p : ℕ × List Bool => payload (k := k) e p.1 p.2) encArgs encRawResult
    (fun p => (encArgs p).length) := by
  classical
  have hb := fst encNat encBits
  have hw := snd encNat encBits
  have hsize := budget_comp_linear natSize hb
  have hstateRead := budget_comp_linear readNat_inSpace
    (budget_prod hw (budget_prod (budget_const 1 (.refl _))
      (budget_const (s + 1).size (.refl _))))
  have hstate := budget_comp_linear (state_inSpace e) hstateRead
  have hheads := pi_linear (Index := Option (Fin k)) fun i =>
    budget_natMod (budget_comp_linear readNat_inSpace
      (budget_prod hw (budget_prod
        (budget_natAdd (budget_const (1 + (s + 1).size) (.refl _))
          (budget_natMul (budget_const ((finSuccEquiv k).symm i).val (.refl _)) hsize))
        hsize))) hb
  have htrack0 := budget_comp_linear bit_inSpace
    (budget_prod hw (trackOffset_inSpace (k := k) (s := s)))
  have htrack1 := budget_comp_linear bit_inSpace
    (budget_prod hw (budget_natSucc (trackOffset_inSpace (k := k) (s := s))))
  have htrack := budget_finite (encC := encFinite OutputTrack)
    (fun q : Bool × Bool => if q.2 then .other else if q.1 then .accept else .empty)
    (budget_prod htrack0 htrack1)
  have hwindowSize := budget_natMul (budget_const (encB := encNat) 6 (.refl _)) hb
  have hcells := pi_linear (Index := Fin k) fun i =>
    budget_comp_linear cells_inSpace (budget_comp_linear slice_inSpace
      (budget_prod hw (budget_prod
        (budget_natAdd (budget_natAdd (trackOffset_inSpace (k := k) (s := s))
          (budget_const 2 (.refl _)))
          (budget_natMul (budget_const i.val (.refl _)) hwindowSize)) hwindowSize)))
  exact (budget_prod hstate (budget_prod hheads (budget_prod htrack hcells))).of_enc_eq
    fun _ => rfl

/-- Uniform native parser. Zero width, malformed length and FAIL all return `none`. -/
theorem parse_inSpace (e : Q ≃ Fin s) : ComputableInSpace (parse (k := k) e) encArgs
    (encOption encRawResult) (fun p => (encArgs p).length) := by
  have hb := fst encNat encBits
  have hw := snd encNat encBits
  have hsize := budget_comp_linear natSize hb
  have hwidth := budget_natAdd
    (budget_natAdd (budget_const (1 + (s + 1).size) (.refl _))
      (budget_natMul (budget_const (k + 1) (.refl _)) hsize))
    (budget_natAdd (budget_const 2 (.refl _))
      (budget_natMul (budget_const (6 * k) (.refl _)) hb))
  have hlength := budget_comp_linear wordLength_inSpace hw
  have hbad := budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 || !q.2)
    (budget_prod (budget_natIsZero hb) (budget_natEq hlength hwidth))
  have htag : ComputableInSpace (fun p : ℕ × List Bool => p.2.headD false) encArgs encBool
      (fun p => (encArgs p).length) :=
    budget_comp_linear (of_inO (.of_linear (ListEncoding.headD false))) hw
  have hsome := budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := encRawResult (k := k) (Q := Q))
      (enc := encOption (encRawResult (k := k) (Q := Q)))).inO_one) (payload_inSpace (k := k) e)
  have hnone : ComputableInSpace (fun _ : ℕ × List Bool =>
      (none : Option (RawResult k Q))) encArgs (encOption encRawResult)
      (fun p => (encArgs p).length) := budget_const none (.refl _)
  refine (budget_ite hbad hnone (budget_ite htag hsome hnone)).of_enc_eq ?_
  intro p
  have hwidth : 1 + (s + 1).size + (k + 1) * p.1.size + (2 + 6 * k * p.1) =
      width k s p.1 := by rw [width_eq]; omega
  simp only [parse, hwidth, Bool.or_eq_true, Bool.not_eq_true', Bool.decide_iff,
    decide_eq_false_iff_not]

private theorem cellOfCode_cellCode (first second : Bool) :
    cellOfCode (cellCode first second) = if first then some second else none := by
  cases first <;> cases second <;> rfl

private theorem cells_getD (word : List Bool) (i : ℕ) (hi : 2 * i + 1 < word.length) :
    (cells word).getD i 0 = cellCode (word.getD (2 * i) false) (word.getD (2 * i + 1) false) := by
  induction i generalizing word with
  | zero =>
    rcases word with _ | ⟨first, word⟩
    · simp at hi
    rcases word with _ | ⟨second, word⟩
    · simp at hi
    rfl
  | succ i ih =>
    rcases word with _ | ⟨first, word⟩
    · simp at hi
    rcases word with _ | ⟨second, word⟩
    · simp at hi
    have hrest : 2 * i + 1 < word.length := by simp only [List.length_cons] at hi; omega
    rw [cells, List.getD_cons_succ]
    rw [show 2 * (i + 1) + 1 = ((2 * i + 1) + 1) + 1 from by omega,
      show 2 * (i + 1) = (2 * i + 1) + 1 from by omega]
    simp only [List.getD_cons_succ]
    exact ih word hrest

private theorem slice_ofFn {n : ℕ} (bits : BitString n) (offset count : ℕ)
    (h : offset + count ≤ n) :
    ((List.ofFn bits).drop offset).take count =
      List.ofFn (fun i : Fin count => bits ⟨offset + i.val, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

private theorem ofBits_ofFn {n : ℕ} (bits : BitString n) :
    ofBits (List.ofFn bits) = (equivFin n bits).val := by
  rw [← lsbValue_ofFn]
  exact (lsbValue_eq_foldr_bit _).symm

/-- Reading an in-range numeric field agrees with the existing finite bit-string numbering. -/
theorem readNat_ofFn {n : ℕ} (bits : BitString n) (offset count : ℕ)
    (h : offset + count ≤ n) :
    readNat (List.ofFn bits) offset count =
      (equivFin count (fun i : Fin count => bits ⟨offset + i.val, by omega⟩)).val := by
  rw [readNat, slice_ofFn bits offset count h, ofBits_ofFn]

private theorem slice_getD_ofFn {n : ℕ} (bits : BitString n) (offset count : ℕ)
    (h : offset + count ≤ n) (i : ℕ) (hi : i < count) :
    (((List.ofFn bits).drop offset).take count).getD i false =
      bits ⟨offset + i, by omega⟩ := by
  rw [List.getD_eq_getElem _ _ (by
    simp only [List.length_take, List.length_drop, List.length_ofFn]; omega)]
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

private theorem readNat_field {n count : ℕ} (bits : BitString n) (field : BitString count)
    (offset : ℕ) (h : offset + count ≤ n)
    (hfield : ∀ i, bits ⟨offset + i.val, by omega⟩ = field i) :
    readNat (List.ofFn bits) offset count = (equivFin count field).val := by
  rw [readNat_ofFn bits offset count h]
  apply congrArg (fun f : BitString count => (equivFin count f).val)
  funext i
  exact hfield i

private theorem getD_ofFn {n : ℕ} (bits : BitString n) (i : ℕ) (hi : i < n) :
    (List.ofFn bits).getD i false = bits ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hi)]
  simp only [List.getElem_ofFn]

omit [Finite Q] in
/-- The untyped payload agrees field by field with the explicit semantic codec. -/
theorem toView_payload (e : Q ≃ Fin s) (b : ℕ) [NeZero b]
    (bits : BitString (width k s b)) :
    (payload e b (List.ofFn bits)).toView b = decodePayload e (Fin.tail bits) := by
  change BitString ((s + 1).size + ((k + 1) * b.size + (2 + windowBits k b)) + 1) at bits
  have hw : (s + 1).size + ((k + 1) * b.size + (2 + windowBits k b)) + 1 =
      1 + (s + 1).size + (k + 1) * b.size + 2 + 6 * k * b := by
    unfold windowBits
    ring
  have hstate : readNat (List.ofFn bits) 1 (s + 1).size =
      (equivFin (s + 1).size (fstBits (Fin.tail bits))).val := by
    apply readNat_field bits (fstBits (Fin.tail bits)) 1 (by omega)
    intro i
    simp only [fstBits_apply, Fin.tail]
    apply congrArg bits
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castAdd]
    omega
  have hheads (head : Option (Fin k)) :
      readNat (List.ofFn bits)
        (1 + (s + 1).size + ((finSuccEquiv k).symm head).val * b.size) b.size =
      (equivFin b.size
        (blocksEquiv (fstBits (sndBits (Fin.tail bits))) ((finSuccEquiv k).symm head))).val := by
    apply readNat_field bits
      (blocksEquiv (fstBits (sndBits (Fin.tail bits))) ((finSuccEquiv k).symm head))
      (1 + (s + 1).size + ((finSuccEquiv k).symm head).val * b.size)
      (by
        have hindex := Nat.mul_le_mul_right b.size
          (Nat.succ_le_of_lt ((finSuccEquiv k).symm head).isLt)
        nlinarith)
    intro i
    simp only [blocksEquiv_apply, block_apply, fstBits_apply, sndBits_apply, Fin.tail]
    apply congrArg bits
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castAdd, Fin.val_natAdd, finProdFinEquiv_apply_val]
    ring
  have htrack (i : Fin 2) :
      (List.ofFn bits).getD (trackOffset k s b + i.val) false =
      fstBits (sndBits (sndBits (Fin.tail bits))) i := by
    rw [getD_ofFn bits _ (by unfold trackOffset; have := i.isLt; omega)]
    simp only [fstBits_apply, sndBits_apply, Fin.tail]
    congr 1
    ext
    simp only [trackOffset, Fin.val_succ, Fin.val_castAdd, Fin.val_natAdd]
    omega
  apply Prod.ext
  · apply Prod.ext
    · change state e (readNat (List.ofFn bits) 1 (s + 1).size) = _
      rw [hstate]
      rfl
    · apply Prod.ext
      · funext head
        change (readNat (List.ofFn bits)
          (1 + (s + 1).size + ((finSuccEquiv k).symm head).val * b.size) b.size % b :
          ZMod b) = _
        rw [ZMod.natCast_mod, hheads]
        rfl
      · change (if (List.ofFn bits).getD (trackOffset k s b + 1) false then _ else
          if (List.ofFn bits).getD (trackOffset k s b) false then _ else _) = _
        have hzero := htrack (0 : Fin 2)
        have hone := htrack (1 : Fin 2)
        simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at hzero hone
        rw [hzero, hone]
        rfl
  · funext tape port residue
    let offset := trackOffset k s b + 2 + tape.val * (6 * b)
    let index := port.val * b + residue.val
    have hp := port.isLt
    have hr := ZMod.val_lt residue
    have ht := tape.isLt
    have hoff : offset + 6 * b ≤
        (s + 1).size + ((k + 1) * b.size + (2 + windowBits k b)) + 1 := by
      have hmul := Nat.mul_le_mul_right (6 * b) (Nat.succ_le_of_lt ht)
      dsimp [offset, trackOffset]
      nlinarith
    have hind : 2 * index + 1 < 6 * b := by
      have hmul := Nat.mul_le_mul_right b (Nat.le_of_lt_succ hp)
      dsimp [index]
      nlinarith
    change cellOfCode ((cells (((List.ofFn bits).drop offset).take (6 * b))).getD index 0) = _
    rw [cells_getD _ index (by
      simp only [List.length_take, List.length_drop, List.length_ofFn]; omega),
      slice_getD_ofFn bits offset (6 * b) hoff (2 * index) (by omega),
      slice_getD_ofFn bits offset (6 * b) hoff (2 * index + 1) hind,
      cellOfCode_cellCode]
    have hbit (i : Fin 2) : bits ⟨offset + (2 * index + i.val), by have := i.isLt; omega⟩ =
        blocksEquiv (blocksEquiv (blocksEquiv
          (sndBits (sndBits (sndBits (Fin.tail bits)))) tape) port)
          ⟨residue.val, hr⟩ i := by
      simp only [blocksEquiv_apply, block_apply, sndBits_apply]
      congr 1
      ext
      dsimp [offset, index, trackOffset, windowBits]
      simp only [finProdFinEquiv_apply_val]
      ring
    have hzero := hbit (0 : Fin 2)
    have hone := hbit (1 : Fin 2)
    simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at hzero hone
    rw [hzero, hone]
    rfl

omit [Finite Q] in
/-- Native parsing realizes the existing explicit label decoder, including FAIL and unused
control/cell/track words. Only the finite machine control is enumerated. -/
theorem parse_ofFn (e : Q ≃ Fin s) (b : ℕ) [NeZero b]
    (bits : BitString (width k s b)) :
    (parse e (b, List.ofFn bits)).map (RawResult.toView b) = decode e bits := by
  have hlen : (List.ofFn bits).length = width k s b := List.length_ofFn
  have htag : (List.ofFn bits).headD false = bits ⟨0, width_pos k s b⟩ := by
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?]
    exact getD_ofFn bits 0 (width_pos k s b)
  simp only [parse, NeZero.ne b, hlen, ne_eq, not_true_eq_false, or_self, ↓reduceIte]
  rw [htag]
  by_cases h : bits ⟨0, width_pos k s b⟩ = true
  · simp only [h, ↓reduceIte, Option.map_some, decode]
    exact congrArg some (toView_payload e b bits)
  · simp [decode, h]

end Turing.MultiTapePTM.BlockComputation.Encoding.NativeDecode
