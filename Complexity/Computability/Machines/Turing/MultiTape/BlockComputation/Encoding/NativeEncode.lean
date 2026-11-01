/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayAccess
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Bit
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.BitList
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.NatSize
import Complexity.Foundations.Data.BitString.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Pi
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Pi

/-!
# Native serialization of runtime-width block results

The finite machine and its control numbering are fixed; block width, residues and all window
cells are runtime data. The serializer uses exactly the semantic codec's FAIL bit, control
rank, input-first head ordering, track bits and row-major two-bit cells. Raw ternary symbol
codes are decoded before serialization: written one is `[true,true]`, not the binary code 2.

Both FAIL and successful results retain explicit window buffers at the input boundary.
Every tape must contain exactly three blocks before serialization is accepted. Thus even the
zero-filled FAIL word is paid by actual stored windows, with binary width metadata paying for
head padding when there are no work tapes. Allocating these buffers remains a caller operation.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Encoding.NativeEncode

open Cslib Cslib.BitString MultiTapeTM MultiTapeTM.ComputableInSpace QueryReplay
open MultiTapeNTM.ChoiceTable

variable {k s : ℕ} {Q : Type} [Finite Q]

/-- Runtime block width, success tag and explicit returned local data. FAIL also retains its
buffers, so its fixed-width serialized output has an actual encoded space charge. -/
abbrev Args (k : ℕ) (Q : Type) := ℕ × Bool × RawResult k Q

/-- Binary width and head residues, finite control tags and explicit framed cell lists. -/
@[expose] noncomputable def encArgs : Args k Q ↪ List Bool :=
  encPair encNat (encPair encBool (encRawResult (k := k) (Q := Q)))

/-- Exactly three blocks on every tape. A rejected call returns the empty word. -/
@[expose] def valid (a : Args k Q) : Bool :=
  let (b, _, (_, _, _, cells)) := a
  (List.ofFn fun tape : Fin k => decide ((cells tape).length = 3 * b)).all id

/-- Fixed-width little-endian binary word. It reads bits directly without allocating a power. -/
@[expose] def word (b n : ℕ) : List Bool :=
  List.ofFn fun j : Fin b.size => n.testBit j

/-- Raw ternary cells pass through the same semantic cell decoder as replay results. -/
@[expose] def cellWord (n : ℕ) : List Bool :=
  List.ofFn (encodeCell (cellOfCode n))

/-- Serialize one explicit local window. The list is streamed, without an index list. -/
@[expose] def windowWord (cells : List ℕ) : List Bool := cells.flatMap cellWord

/-- The payload in the semantic codec's field order. In particular, `finSuccEquiv k` places
`none` (the input head) first, followed by work heads. -/
@[expose] def payload (e : Q ≃ Fin s) (b : ℕ) (raw : RawResult k Q) : List Bool :=
  let (control, residues, track, cells) := raw
  List.ofFn (encodeState e control) ++
    (List.ofFn fun h : Fin (k + 1) => word b (residues (finSuccEquiv k h) % b)).flatten ++
    List.ofFn (encodeTrack track) ++ (List.ofFn fun tape : Fin k => windowWord (cells tape)).flatten

/-- Serialize a success or FAIL using the existing fixed layout. FAIL blanks every payload
bit by streaming the charged payload, rather than allocating an uncharged width-sized word. -/
@[expose] def serialize (e : Q ≃ Fin s) (a : Args k Q) : List Bool :=
  let (b, success, raw) := a
  if valid a then success :: (payload e b raw).map (fun bit => success && bit) else []

private theorem append_budget {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    {f g : α → List Bool}
    (hf : ComputableInSpace f enc (encList encBool) S)
    (hg : ComputableInSpace g enc (encList encBool) S) :
    ComputableInSpace (fun a => f a ++ g a) enc (encList encBool) S :=
  (hf.append hg (fun _ => encList_append _ _ _)).weaken (.add (.refl _) (.refl _))

private theorem finiteAppend {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
    (hlen : (fun a => (enc a).length) ≼ S) {n : ℕ} {f : Fin n → α → List Bool}
    (hf : ∀ i, ComputableInSpace (f i) enc (encList encBool) S) :
    ComputableInSpace (fun a => (List.ofFn fun i => f i a).flatten)
      enc (encList encBool) S := by
  induction n with
  | zero => exact (budget_const [] hlen).of_enc_eq fun _ => rfl
  | succ n ih =>
    have ht := ih (f := fun i => f i.succ) (fun i => hf i.succ)
    refine (append_budget (hf 0) ht).of_enc_eq ?_
    intro a
    simp only [List.ofFn_succ, List.flatten_cons]

private abbrev WordState := (ℕ × ℕ) × ℕ × List Bool
private abbrev encWordState : WordState ↪ List Bool :=
  encPair (encPair encNat encNat) (encPair encNat (encList encBool))

private def wordStep (q : WordState) : WordState :=
  (q.1, q.2.1 + 1, q.2.2 ++ [q.1.2.testBit q.2.1])

private theorem iterate_wordStep (b n j : ℕ) (out : List Bool) (t : ℕ) :
    wordStep^[t] ((b, n), j, out) =
      ((b, n), j + t, out ++ (List.range t).map (fun i => n.testBit (j + i))) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [wordStep, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
    congr 2

private theorem wordStep_inSpace :
    ComputableInSpace wordStep encWordState encWordState
      (fun q => (encWordState q).length) := by
  have hp := fst (encPair encNat encNat) (encPair encNat (encList encBool))
  have hrest := snd (encPair encNat encNat) (encPair encNat (encList encBool))
  have hj := fst' hrest
  have hout := snd' hrest
  have hbit := budget_comp_lin natTestBit (linear_mul 32) (budget_prod (snd' hp) hj)
  exact (budget_prod hp (budget_prod (budget_natSucc hj) (budget_snoc hout hbit))).of_enc_eq
    fun _ => rfl

/-- Binary width metadata pays the fixed-width head word, including at tape count zero. -/
theorem word_inSpace : ComputableInSpace (fun q : ℕ × ℕ => word q.1 q.2)
    (encPair encNat encNat) (encList encBool)
    (fun q => (encPair encNat encNat q).length) := by
  have hb := fst encNat encNat
  have hn := budget_comp_linear natSize hb
  have hid : ComputableInSpace (fun q : ℕ × ℕ => q) (encPair encNat encNat)
      (encPair encNat encNat) (fun q => (encPair encNat encNat q).length) :=
    of_inO ComputableInDegree.id'.inO_one
  have hinit := budget_prod hid (budget_prod (budget_const (encB := encNat) 0 (.refl _))
    (budget_const (encB := encList encBool) [] (.refl _)))
  have hstate (q : ℕ × ℕ) (i : ℕ) (hi : i ≤ q.1.size) :
      (encWordState (wordStep^[i] (q, 0, []))).length ≤
        16 * ((encPair encNat encNat q).length + 1) := by
    rcases q with ⟨b, n⟩
    rw [iterate_wordStep]
    have hc := length_encNat_le_self i
    change i ≤ b.size at hi
    rw [← length_encNat_eq_size b] at hi
    have hout : (encList encBool ((List.range i).map (fun j => n.testBit j))).length = 3 * i := by
      simp [length_encList, List.map_map, Function.comp_def, encBool_apply, Nat.mul_comm]
    simp only [encWordState, length_encPair, Nat.zero_add, List.nil_append]
    rw [hout]
    omega
  have h := ComputableInSpace.iterate hn hinit wordStep_inSpace
    (Q := fun q => 16 * ((encPair encNat encNat q).length + 1))
    (B := fun q => 16 * ((encPair encNat encNat q).length + 1)) hstate hstate
  refine (snd' (snd' h)).weaken ?_ |>.of_enc_eq ?_
  · refine .of_le_linear 128 128 fun q => ?_
    have hc := length_encNat_le_self q.1.size
    have hbsize := length_encNat_eq_size q.1
    rw [← hbsize] at hc ⊢
    simp only [length_encPair]
    omega
  · intro q
    rw [iterate_wordStep]
    apply congrArg (encList encBool)
    simp only [word, Nat.zero_add, List.nil_append]
    apply List.ext_getElem (by simp)
    intro i hi hi'
    simp

private theorem cellWord_inSpace : ComputableInSpace cellWord encNat (encList encBool)
    (fun n => (encNat n).length) := by
  have hn : ComputableInSpace (fun n : ℕ => n) encNat encNat
      (fun n => (encNat n).length) := of_inO ComputableInDegree.id'.inO_one
  have ho := budget_const (encIn := encNat) (encB := encNat) 1 (.refl _)
  have ht := budget_const (encIn := encNat) (encB := encNat) 2 (.refl _)
  refine (budget_ite (budget_natEq hn ho)
    (budget_const (encB := encList encBool) [true, false] (.refl _))
    (budget_ite (budget_natEq hn ht)
      (budget_const (encB := encList encBool) [true, true] (.refl _))
      (budget_const (encB := encList encBool) [false, false] (.refl _)))).of_enc_eq ?_
  intro n
  by_cases h1 : n = 1 <;> by_cases h2 : n = 2 <;> simp [cellWord, cellOfCode, h1, h2, encodeCell]

private theorem length_windowWord (cells : List ℕ) :
    (windowWord cells).length = 2 * cells.length := by
  simp [windowWord, cellWord, List.length_flatMap, Nat.mul_comm]

private theorem foldl_cells (cells : List ℕ) (out : List Bool) :
    cells.foldl (fun acc n => acc ++ cellWord n) out = out ++ windowWord cells := by
  induction cells generalizing out with
  | nil => simp [windowWord]
  | cons n cells ih => simp [List.foldl_cons, ih, windowWord, List.append_assoc]

/-- Cell conversion streams the supplied list, so malformed short buffers never cause padding
up to the requested block width. -/
theorem windowWord_inSpace : ComputableInSpace windowWord (encList encNat) (encList encBool)
    (fun cells => (encList encNat cells).length) := by
  have hid : ComputableInSpace (fun l : List ℕ => l) (encList encNat) (encList encNat)
      (fun l => (encList encNat l).length) := of_inO ComputableInDegree.id'.inO_one
  have hs := append_budget (fst (encList encBool) encNat)
    (budget_comp_linear cellWord_inSpace (snd (encList encBool) encNat))
  have hstate (cells : List ℕ) (i : ℕ) (hi : i ≤ cells.length) :
      (encList encBool ((cells.take i).foldl (fun acc n => acc ++ cellWord n) [])).length ≤
        6 * (encList encNat cells).length := by
    rw [foldl_cells, List.nil_append]
    have hl := length_le_length_encList encNat cells
    have hw := length_windowWord (cells.take i)
    have hbool (l : List Bool) : (encList encBool l).length = 3 * l.length := by
      simp [length_encList, encBool_apply, Nat.mul_comm]
    rw [hbool, hw]
    nlinarith [List.length_take_le i cells]
  have hspace (cells : List ℕ) (i : ℕ) (hi : i < cells.length) :
      (encPair (encList encBool) encNat
        ((cells.take i).foldl (fun acc n => acc ++ cellWord n) [], cells[i])).length ≤
          16 * ((encList encNat cells).length + 1) := by
    have h := hstate cells i hi.le
    have hv := length_le_encList_of_mem encNat (List.getElem_mem hi)
    simp only [length_encPair]
    omega
  have h := ComputableInSpace.foldl hid (budget_const [] (.refl _)) hs hspace hstate
  refine h.weaken (.of_le_linear 64 64 fun _ => by omega) |>.of_enc_eq ?_
  intro cells
  simp only [foldl_cells, List.nil_append]

private theorem valid_inSpace : ComputableInSpace (valid (k := k) (Q := Q))
    encArgs encBool (fun a => (encArgs a).length) := by
  classical
  have hb := fst encNat (encPair encBool (encRawResult (k := k) (Q := Q)))
  have hraw := snd' (snd encNat (encPair encBool (encRawResult (k := k) (Q := Q))))
  have hcells := snd' (snd' (snd' hraw))
  have hbits (i : Fin k) := budget_natEq
    (budget_length (budget_comp_linear (of_inO (ComputableInO.pi_apply (encList encNat) i)) hcells))
    (budget_natMul (budget_const (encB := encNat) 3 (.refl _)) hb)
  have htuple := pi_linear hbits
  refine (budget_finite (encC := encBool)
    (fun checks : Fin k → Bool => (List.ofFn checks).all id) htuple).of_enc_eq fun _ => rfl

/-- All data fields are serialized in native space linear in their actual encodings. -/
theorem payload_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (fun a : ℕ × RawResult k Q => payload e a.1 a.2)
      (encPair encNat (encRawResult (k := k) (Q := Q))) (encList encBool)
      (fun a => (encPair encNat (encRawResult (k := k) (Q := Q)) a).length) := by
  classical
  have hb := fst encNat (encRawResult (k := k) (Q := Q))
  have hr := snd encNat (encRawResult (k := k) (Q := Q))
  have hcontrol := fst' hr
  have hres := fst' (snd' hr)
  have htrack := fst' (snd' (snd' hr))
  have hcells := snd' (snd' (snd' hr))
  have hs := budget_finite (encC := encList encBool)
    (fun q : Option Q => List.ofFn (encodeState e q)) hcontrol
  have hh (i : Fin (k + 1)) := budget_comp_linear word_inSpace
    (budget_prod hb (budget_natMod
      (budget_comp_linear (of_inO (ComputableInO.pi_apply encNat (finSuccEquiv k i))) hres) hb))
  have ht := budget_finite (encC := encList encBool)
    (fun t : OutputTrack => List.ofFn (encodeTrack t)) htrack
  have hw (i : Fin k) := budget_comp_linear windowWord_inSpace
    (budget_comp_linear (of_inO (ComputableInO.pi_apply (encList encNat) i)) hcells)
  exact (append_budget (append_budget (append_budget hs (finiteAppend (.refl _) hh)) ht)
    (finiteAppend (.refl _) hw)).of_enc_eq fun _ => rfl

/-- Both tag branches have a native linear-space certificate. The FAIL branch streams the
retained payload; it cannot create a width-sized word from binary width metadata alone. -/
theorem serialize_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (serialize e : Args k Q → List Bool) encArgs (encList encBool)
      (fun a => (encArgs a).length) := by
  classical
  have hb := fst encNat (encPair encBool (encRawResult (k := k) (Q := Q)))
  have hrest := snd encNat (encPair encBool (encRawResult (k := k) (Q := Q)))
  have htag := fst' hrest
  have hraw := snd' hrest
  have hpayload := budget_comp_linear (payload_inSpace e) (budget_prod hb hraw)
  -- Mapping the tag over a Boolean word is a fixed Boolean operation, not a lookup on words.
  have hmap := ComputableInSpace.mapWith
    (enc := encBool) (encP := encBool) (encK := encBool)
    (budget_finite (encC := encBool) (fun p : Bool × Bool => p.1 && p.2)
      (of_inO ComputableInDegree.id'.inO_one)) htag hpayload
  have hmap' : ComputableInSpace
      (fun a : Args k Q => (payload e a.1 a.2.2).map (fun bit => a.2.1 && bit))
      encArgs (encList encBool) (fun a => (encArgs a).length) := by
    refine hmap.weaken ?_
    obtain ⟨c, hc⟩ := hpayload.length_le
    refine .of_le_linear (32 * (c + 1)) (32 * (c + 1)) fun a => ?_
    have hm : (encList encBool ((payload e a.1 a.2.2).map (fun bit => a.2.1 && bit))).length =
        (encList encBool (payload e a.1 a.2.2)).length := by
      simp [length_encList, List.map_map, Function.comp_def, encBool_apply]
    have htaglen : (encBool a.2.1).length = 1 := rfl
    simp only [hm, htaglen]
    have hmax : listMax (fun p : Bool => (encPair encBool encBool (a.2.1, p)).length)
        (payload e a.1 a.2.2) ≤ 4 := by
      apply listMax_le
      intro bit hbit
      simp [encBool_apply]
    have hc' := hc a
    dsimp only [encArgs] at ⊢
    nlinarith
  exact (budget_ite valid_inSpace (budget_cons htag hmap')
    (budget_const [] (.refl _))).of_enc_eq fun _ => rfl

/-- Raw-word output composes directly with the native parser's `encBits` input. -/
theorem serialize_bits_inSpace (e : Q ≃ Fin s) :
    ComputableInSpace (serialize e : Args k Q → List Bool) encArgs encBits
      (fun a => (encArgs a).length) :=
  (budget_comp_linear (f := serialize e) (g := fun l : List Bool => l)
    listToBits (serialize_inSpace e)).of_enc_eq fun _ => rfl

/-- Direct bit access uses the semantic codec's little-endian convention. -/
theorem word_encodeResidue {b : ℕ} [NeZero b] (n : ℕ) :
    word b (n % b) = List.ofFn (encodeResidue (n : ZMod b)) := by
  unfold word
  congr 1
  funext j
  simp only [encodeResidue, equivFin_symm_apply, ZMod.val_natCast]

private theorem windowWord_encode {b : ℕ} (cells : List ℕ)
    (hlen : cells.length = 3 * b) :
    windowWord cells = List.ofFn
      (blocksEquiv.symm fun port : Fin 3 => blocksEquiv.symm fun r : Fin b =>
        encodeCell (cellOfCode (cells.getD (port.val * b + r.val) 0))) := by
  rw [ofFn_blocksEquiv_symm]
  simp only [ofFn_blocksEquiv_symm]
  have hlist : List.ofFn (fun i : Fin (3 * b) => cells.getD i 0) = cells := by
    apply List.ext_getElem (by simp [hlen])
    intro i hi hi'
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  have hflat : windowWord cells =
      (List.ofFn fun i : Fin (3 * b) => cellWord (cells.getD i 0)).flatten := by
    have hmap := List.map_ofFn (f := fun i : Fin (3 * b) => cells.getD i 0) (g := cellWord)
    rw [hlist] at hmap
    simp only [Function.comp_def] at hmap
    rw [← hmap]
    rfl
  rw [hflat, List.ofFn_mul, List.flatten_flatten, List.map_ofFn]
  rfl

private theorem ofFn_append {m n : ℕ} (x : Fin m → Bool) (y : Fin n → Bool) :
    List.ofFn (Fin.append x y) = List.ofFn x ++ List.ofFn y := by
  rw [List.ofFn_add]
  simp

omit [Finite Q] in
/-- Canonical window buffers serialize exactly as the existing positive-width codec. Head
residues may be arbitrary naturals: runtime modular reduction agrees with `RawResult.toView`. -/
theorem payload_eq_encodePayload (e : Q ≃ Fin s) {b : ℕ} [NeZero b]
    (raw : RawResult k Q) (hvalid : valid (b, true, raw) = true) :
    payload e b raw = List.ofFn (encodePayload e (raw.toView b)) := by
  rcases raw with ⟨control, residues, track, cells⟩
  have hlen (i : Fin k) : (cells i).length = 3 * b := by
    have h := List.all_eq_true.mp hvalid _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
    exact of_decide_eq_true h
  have hh : (List.ofFn fun h : Fin (k + 1) =>
      word b (residues (finSuccEquiv k h) % b)).flatten =
      List.ofFn (encodeHeads (fun h => (residues h : ZMod b))) := by
    rw [encodeHeads, ofFn_blocksEquiv_symm]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    exact word_encodeResidue (residues (finSuccEquiv k i))
  have hw : (List.ofFn fun tape : Fin k => windowWord (cells tape)).flatten =
      List.ofFn (encodeWindows (b := b) (fun h d r =>
        cellOfCode ((cells h).getD (d.val * b + r.val) 0))) := by
    unfold windowBits
    rw [encodeWindows, ofFn_blocksEquiv_symm]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    have hmod (r : Fin b) : r.val % b = r.val := Nat.mod_eq_of_lt r.isLt
    simpa only [ZMod.val_natCast, hmod] using windowWord_encode (cells i) (hlen i)
  unfold payloadBits
  simp only [payload, RawResult.toView, encodePayload, ofFn_append, List.append_assoc]
  rw [hh, hw]

omit [Finite Q] in
/-- Successful serialization preserves the outer tag and every field of the semantic codec. -/
theorem serialize_some (e : Q ≃ Fin s) {b : ℕ} [NeZero b] (raw : RawResult k Q)
    (hvalid : valid (b, true, raw) = true) :
    serialize e (b, true, raw) = List.ofFn (encode e (some (raw.toView b))) := by
  unfold width
  simp only [serialize, hvalid, ↓reduceIte, Bool.true_and, List.map_id_fun', id_eq,
    payload_eq_encodePayload e raw hvalid, encode, List.ofFn_succ]
  rfl

omit [Finite Q] in
/-- FAIL is encoded at the same paid width; its buffers remain part of the caller's input. -/
theorem serialize_fail (e : Q ≃ Fin s) {b : ℕ} [NeZero b] (raw : RawResult k Q)
    (hvalid : valid (b, false, raw) = true) :
    serialize e (b, false, raw) = List.ofFn (encode (k := k) (b := b) e none) := by
  have hv : valid (b, true, raw) = true := hvalid
  have hp := payload_eq_encodePayload e raw hv
  unfold width
  simp only [serialize, hvalid, ↓reduceIte, Bool.false_and, hp, List.map_ofFn,
    encode, List.ofFn_succ, Function.comp_def]
  rfl

end Turing.MultiTapePTM.BlockComputation.Encoding.NativeEncode
