/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerEncoding
public import Complexity.Computability.TreeEval.Ary.Packed.RawControllerSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Cases
import Mathlib.Data.List.GetD

/-!
# Native local computation of the uniform raw controller

All counters and arithmetic parameters are binary and runtime values. The bank updates use the
streamed checked native operations. Gate points use cyclic bank slices, so zero register width
never materializes a list of fan-in-many empty registers. The executable padding guard rejects
malformed storage before requesting data or transforming the bank.

## Main results

* `need_inSpace`: construct one request in native linear space.
* `step_inSpace`: apply one returned reply and retain the runtime parameter header.
* `halted_inSpace`: test completion or reject malformed storage.
* `point_getD`, `length_point`: the cyclic slices contain exactly the designated child registers.
-/

public section

namespace Cslib.TreeEval.Ary.Packed.RawController

open Turing MultiTapeTM ComputableInSpace Reader

/-- An external node or gate-vector reply. -/
abbrev encReply : Reply ↪ List Bool := encPair encNat (encList encNat)

/-- Request tag, path, child-register point and first output chunk. -/
abbrev encNeed : Need ↪ List Bool :=
  encPair encNat (encPair (encList encNat) (encPair (encList encNat) encNat))

/-- Runtime parameters and state, together with one returned reply. -/
abbrev encStepArgs : ((Params × State) × Reply) ↪ List Bool :=
  encPair encFullState encReply

private theorem length_encList_reverse {α : Type} (enc : α ↪ List Bool) (l : List α) :
    (encList enc l.reverse).length = (encList enc l).length := by
  simp only [length_encList, List.map_reverse, List.sum_reverse]

private theorem listReverse_inSpace {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace List.reverse (encList enc) (encList enc)
      (fun l => (encList enc l).length) := by
  have hlist : ComputableInSpace (fun l : List α => l) (encList enc) (encList enc)
      (fun l => (encList enc l).length) := of_inO ComputableInDegree.id'.inO_one
  have hinit : ComputableInSpace (fun _ : List α => ([] : List α))
      (encList enc) (encList enc) (fun l => (encList enc l).length) :=
    budget_const [] (.refl _)
  have hstep : ComputableInSpace (fun q : List α × α => q.2 :: q.1)
      (encPair (encList enc) enc) (encList enc)
      (fun q => (encPair (encList enc) enc q).length) :=
    budget_cons (snd (encList enc) enc) (fst (encList enc) enc)
  have hstate (l : List α) (i : ℕ) (_hi : i ≤ l.length) :
      (encList enc ((l.take i).foldl (fun acc a => a :: acc) [])).length ≤
        (encList enc l).length := by
    rw [List.foldl_flip_cons_eq_append', List.append_nil, length_encList_reverse]
    exact length_encList_take_le enc l i
  have hspace (l : List α) (i : ℕ) (hi : i < l.length) :
      (encPair (encList enc) enc
        ((l.take i).foldl (fun acc a => a :: acc) [], l[i])).length ≤
          4 * ((encList enc l).length + 1) := by
    have ha := length_le_encList_of_mem enc (List.getElem_mem hi)
    have hs := hstate l i hi.le
    simp only [length_encPair]
    omega
  have hfold := ComputableInSpace.foldl hlist hinit hstep hspace hstate
  refine hfold.weaken (.of_le_linear 8 8 fun _ => by omega) |>.of_enc_eq ?_
  intro l
  simp only [List.foldl_flip_cons_eq_append', List.append_nil]

private theorem listDrop_inSpace {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace (fun q : List α × ℕ => q.1.drop q.2)
      (encPair (encList enc) encNat) (encList enc)
      (fun q => (encPair (encList enc) encNat q).length) := by
  have htail : ComputableInSpace List.tail (encList enc) (encList enc)
      (fun l => (encList enc l).length) :=
    of_inO (.of_linear (ListEncoding.tail (enc₁ := enc)))
  have hlen (q : List α × ℕ) (k : ℕ) :
      (encList enc (List.tail^[k] q.1)).length ≤ (encList enc q.1).length := by
    rw [List.tail_iterate]
    rw [← q.1.take_append_drop k, encList_append, List.length_append]
    simp
  have h := iterate (snd (encList enc) encNat) (fst (encList enc) encNat) htail
    (Q := fun q => (encList enc q.1).length) (B := fun q => (encList enc q.1).length)
    (fun q k _ => hlen q k) (fun q k _ => hlen q k)
  refine h.weaken (.of_le_linear 8 8 fun q => ?_) |>.of_enc_eq ?_
  · simp only [length_encPair]
    omega
  · intro q
    rw [List.tail_iterate]

private theorem listTake_inSpace {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace (fun q : List α × ℕ => q.1.take q.2)
      (encPair (encList enc) encNat) (encList enc)
      (fun q => (encPair (encList enc) encNat q).length) := by
  have hl := fst (encList enc) encNat
  have hn := snd (encList enc) encNat
  have hrev := budget_comp_linear (listReverse_inSpace enc) hl
  have hlen := budget_length hl
  have hcount := budget_natSub hlen hn
  have hdrop := budget_comp_linear (listDrop_inSpace enc) (budget_prod hrev hcount)
  refine (budget_comp_linear (listReverse_inSpace enc) hdrop).of_enc_eq ?_
  intro q
  rw [← List.reverse_take, List.reverse_reverse]

/-- The bank point is computed with binary slicing counters and linear retained output. -/
theorem point_inSpace :
    ComputableInSpace (fun q : (ℕ × ℕ × ℕ) × List ℕ =>
      point q.1.1 q.1.2.1 q.1.2.2 q.2)
      (encPair encNat3 (encList encNat)) (encList encNat)
      (fun q => (encPair encNat3 (encList encNat) q).length) := by
  have hpar := fst encNat3 (encList encNat)
  have hd := fst' hpar
  have hr := fst' (snd' hpar)
  have ht := snd' (snd' hpar)
  have hbank := snd encNat3 (encList encNat)
  have htarget := budget_natMod ht (budget_natSucc hd)
  have hdrop := budget_comp_linear (listDrop_inSpace encNat)
    (budget_prod hbank (budget_natMul (budget_natSucc htarget) hr))
  have htake := budget_comp_linear (listTake_inSpace encNat)
    (budget_prod hbank (budget_natMul htarget hr))
  refine (budget_comp_linear (of_inO (ComputableInDegree.listAppend encNat).inO_one)
    (budget_prod hdrop htake)).of_enc_eq ?_
  intro q
  rfl

private theorem path_encoding_le (st : List Frame) :
    (encList encNat (path st)).length ≤ (encList encFrame st).length := by
  induction st with
  | nil => simp [path]
  | cons fr st ih =>
    have hc : (encNat fr.2.1).length ≤ (encFrame fr).length := by
      simp only [encFrame, length_encPair]
      omega
    have hp : path (fr :: st) = path st ++ [fr.2.1] := by simp [path]
    rw [hp, encList_append, List.length_append]
    simp only [encList_cons, encList_nil, List.append_nil, List.length_append,
      length_frame] at ih ⊢
    omega

private theorem path_inSpace :
    ComputableInSpace path (encList encFrame) (encList encNat)
      (fun st => (encList encFrame st).length) := by
  have hid : ComputableInSpace (fun st : List Frame => st) (encList encFrame) (encList encFrame)
      (fun st => (encList encFrame st).length) := of_inO ComputableInDegree.id'.inO_one
  have hinit : ComputableInSpace (fun _ : List Frame => ([] : List ℕ))
      (encList encFrame) (encList encNat) (fun st => (encList encFrame st).length) :=
    budget_const [] (.refl _)
  have hstep : ComputableInSpace (fun q : List ℕ × Frame => q.2.2.1 :: q.1)
      (encPair (encList encNat) encFrame) (encList encNat)
      (fun q => (encPair (encList encNat) encFrame q).length) := by
    have hfr := snd (encList encNat) encFrame
    exact budget_cons (fst' (snd' hfr)) (fst (encList encNat) encFrame)
  have hstate (st : List Frame) (i : ℕ) (_hi : i ≤ st.length) :
      (encList encNat ((st.take i).foldl (fun acc fr => fr.2.1 :: acc) [])).length ≤
        (encList encFrame st).length := by
    have hpath := path_encoding_le (st.take i)
    simp only [List.foldl_flip_cons_eq_append, List.append_nil,
      ← List.map_reverse] at ⊢
    exact hpath.trans (length_encList_take_le encFrame st i)
  have hspace (st : List Frame) (i : ℕ) (hi : i < st.length) :
      (encPair (encList encNat) encFrame
        ((st.take i).foldl (fun acc fr => fr.2.1 :: acc) [], st[i])).length ≤
          4 * ((encList encFrame st).length + 1) := by
    have hf := length_le_encList_of_mem encFrame (List.getElem_mem hi)
    have hs := hstate st i hi.le
    simp only [encFrame, length_encPair] at hf hs ⊢
    omega
  have hfold := ComputableInSpace.foldl hid hinit hstep hspace hstate
  refine hfold.weaken (.of_le_linear 8 8 fun _ => by omega) |>.of_enc_eq ?_
  intro st
  simp [List.foldl_flip_cons_eq_append, path, List.map_reverse]

/-- The executable shape and padding guard has a uniform native certificate. -/
theorem validBank_inSpace :
    ComputableInSpace (fun q : Params × State => validBank q.1.1 q.1.2.1 q.1.2.2 q.2.1)
      encFullState encBool (fun q => (encFullState q).length) := by
  have hpar := fst encParams encState
  have hp := fst' hpar
  have hd := fst' (snd' hpar)
  have hr := snd' (snd' hpar)
  have hbank := fst' (snd encParams encState)
  have hpad := budget_comp_linear bankPadding_inSpace (budget_prod hp hbank)
  have hlength := budget_length hbank
  have hshape := budget_natEq hlength (budget_natMul (budget_natSucc hd) hr)
  have htwo := budget_const (encIn := encFullState) (encB := encNat) 2 (.refl _)
  have hpok := budget_finite (encC := encBool) Bool.not (budget_natLt hp htwo)
  have hand := budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 && q.2)
    (budget_prod hpok hshape)
  refine (budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 && q.2)
    (budget_prod hand hpad)).of_enc_eq ?_
  intro q
  by_cases h : q.1.1 < 2
  · have hnot : ¬2 ≤ q.1.1 := by omega
    simp [validBank, h, hnot]
  · have hle : 2 ≤ q.1.1 := by omega
    simp [validBank, h, hle]

private theorem optionSome_budget {α β : Type} {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool} {f : α → β} {S : α → ℕ}
    (hf : ComputableInSpace f encIn encB S) :
    ComputableInSpace (fun a => some (f a)) encIn (encOption encB) S :=
  budget_comp_linear
    (of_inO (ComputableInDegree.optionSome (enc₁ := encB) (enc := encOption encB)).inO_one) hf

private theorem optionIsSome_budget {α β : Type} {encIn : α ↪ List Bool}
    {encB : β ↪ List Bool} {f : α → Option β} {S : α → ℕ}
    (hf : ComputableInSpace f encIn (encOption encB) S) :
    ComputableInSpace (fun a => (f a).isSome) encIn encBool S :=
  budget_comp_linear (of_inO (ComputableInDegree.isSome encB).inO_one) hf

private theorem needCore_inSpace :
    ComputableInSpace (fun q : Params × State => needCore q.1.2.1 q.1.2.2 q.2)
      encFullState (encOption encNeed) (fun q => (encFullState q).length) := by
  have hpar := fst encParams encState
  have hd := fst' (snd' hpar)
  have hr := snd' (snd' hpar)
  have hstate := snd encParams encState
  have hbank := fst' hstate
  have hrest := snd' hstate
  have hstack := fst' hrest
  have hmode := snd' hrest
  have hhead := budget_headD (0, 0, false, 0, 0) hstack
  have htail := budget_tail hstack
  have hchild := fst' (snd' hhead)
  have hundo := fst' (snd' (snd' hhead))
  have htarget := snd' (snd' (snd' (snd' hhead)))
  have hpath := budget_comp_linear path_inSpace hstack
  have hparent := budget_comp_linear path_inSpace htail
  have hpoint := budget_comp_linear point_inSpace
    (budget_prod (budget_prod hd (budget_prod hr htarget)) hbank)
  have hz := budget_const (encIn := encFullState) (encB := encNat) 0 (.refl _)
  have hnode := optionSome_budget (budget_prod hz (budget_prod hpath
    (budget_prod (budget_const (encB := encList encNat) [] (.refl _)) hz)))
  have hgate := optionSome_budget (budget_prod
    (budget_const (encB := encNat) 1 (.refl _)) (budget_prod hparent (budget_prod hpoint hz)))
  have hnone := budget_const (encIn := encFullState) (encB := encOption encNeed) none (.refl _)
  have hskip := budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 || q.2)
    (budget_prod hundo (budget_natLt (budget_natSucc hchild) hd))
  refine (budget_ite (optionIsSome_budget hmode) hnode
    (budget_ite (budget_isEmpty hstack) hnone (budget_ite hskip hnone hgate))).of_enc_eq ?_
  rintro ⟨⟨p, d, r⟩, bank, stack, mode⟩
  cases mode with
  | some ct => rfl
  | none =>
    cases stack with
    | nil => rfl
    | cons fr st => rfl

/-- Requests have a native certificate linear in the actual encoded runtime state. -/
theorem need_inSpace :
    ComputableInSpace (fun q : Params × State => need q.1.1 q.1.2.1 q.1.2.2 q.2)
      encFullState (encOption encNeed) (fun q => (encFullState q).length) :=
  (budget_ite validBank_inSpace needCore_inSpace
    (budget_const none (.refl _))).of_enc_eq fun _ => rfl

private theorem reg_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {d t j : α → ℕ} (hd : ComputableInSpace d encIn encNat S)
    (ht : ComputableInSpace t encIn encNat S) (hj : ComputableInSpace j encIn encNat S) :
    ComputableInSpace (fun a => reg (d a) (t a) (j a)) encIn encNat S :=
  budget_natMod (budget_natAdd ht (budget_natSucc hj)) (budget_natSucc hd)

private theorem frame_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {round child coeff target : α → ℕ} {undo : α → Bool}
    (hr : ComputableInSpace round encIn encNat S)
    (hj : ComputableInSpace child encIn encNat S)
    (hu : ComputableInSpace undo encIn encBool S)
    (hc : ComputableInSpace coeff encIn encNat S)
    (ht : ComputableInSpace target encIn encNat S) :
    ComputableInSpace (fun a => (round a, child a, undo a, coeff a, target a)) encIn encFrame S :=
  budget_prod hr (budget_prod hj (budget_prod hu (budget_prod hc ht)))

private theorem state_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {bank : α → List ℕ} {stack : α → List Frame} {mode : α → Option (ℕ × ℕ)}
    (hb : ComputableInSpace bank encIn (encList encNat) S)
    (hs : ComputableInSpace stack encIn (encList encFrame) S)
    (hm : ComputableInSpace mode encIn (encOption (encPair encNat encNat)) S) :
    ComputableInSpace (fun a => (bank a, stack a, mode a)) encIn encState S :=
  budget_prod hb (budget_prod hs hm)

private theorem scale_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {p r t c : α → ℕ} {bank : α → List ℕ}
    (hp : ComputableInSpace p encIn encNat S) (hr : ComputableInSpace r encIn encNat S)
    (ht : ComputableInSpace t encIn encNat S) (hc : ComputableInSpace c encIn encNat S)
    (hb : ComputableInSpace bank encIn (encList encNat) S) :
    ComputableInSpace (fun a => checkedScaleBank ((p a, r a, t a, c a), bank a))
      encIn (encList encNat) S :=
  budget_comp_linear checkedScaleBank_inSpace
    (budget_prod (budget_prod hp (budget_prod hr (budget_prod ht hc))) hb)

private theorem add_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {p r t c : α → ℕ} {values bank : α → List ℕ}
    (hp : ComputableInSpace p encIn encNat S) (hr : ComputableInSpace r encIn encNat S)
    (ht : ComputableInSpace t encIn encNat S) (hc : ComputableInSpace c encIn encNat S)
    (hv : ComputableInSpace values encIn (encList encNat) S)
    (hb : ComputableInSpace bank encIn (encList encNat) S) :
    ComputableInSpace (fun a => checkedAddBank ((p a, r a, t a, c a), values a, bank a))
      encIn (encList encNat) S :=
  budget_comp_linear checkedAddBank_inSpace
    (budget_prod (budget_prod hp (budget_prod hr (budget_prod ht hc))) (budget_prod hv hb))

private theorem sub_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {p r t c : α → ℕ} {values bank : α → List ℕ}
    (hp : ComputableInSpace p encIn encNat S) (hr : ComputableInSpace r encIn encNat S)
    (ht : ComputableInSpace t encIn encNat S) (hc : ComputableInSpace c encIn encNat S)
    (hv : ComputableInSpace values encIn (encList encNat) S)
    (hb : ComputableInSpace bank encIn (encList encNat) S) :
    ComputableInSpace (fun a => checkedSubBank ((p a, r a, t a, c a), values a, bank a))
      encIn (encList encNat) S :=
  budget_comp_linear checkedSubBank_inSpace
    (budget_prod (budget_prod hp (budget_prod hr (budget_prod ht hc))) (budget_prod hv hb))

private def checkedBeginRound (p d r round c t : ℕ) (bank : List ℕ)
    (stack : List Frame) : State :=
  (checkedScaleBank ((p, r, reg d t 0, round + 1), bank),
    (round, 0, false, c, t) :: stack, some (1, reg d t 0))

private theorem beginRound_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {p d r round c t : α → ℕ} {bank : α → List ℕ} {stack : α → List Frame}
    (hp : ComputableInSpace p encIn encNat S) (hd : ComputableInSpace d encIn encNat S)
    (hr : ComputableInSpace r encIn encNat S) (hi : ComputableInSpace round encIn encNat S)
    (hc : ComputableInSpace c encIn encNat S) (ht : ComputableInSpace t encIn encNat S)
    (hb : ComputableInSpace bank encIn (encList encNat) S)
    (hs : ComputableInSpace stack encIn (encList encFrame) S)
    (hlen : (fun a => (encIn a).length) ≼ S) :
    ComputableInSpace (fun a => checkedBeginRound (p a) (d a) (r a) (round a) (c a) (t a)
      (bank a) (stack a)) encIn encState S := by
  have hz := budget_const (encB := encNat) 0 hlen
  have hone := budget_const (encB := encNat) 1 hlen
  have hreg := reg_budget hd ht hz
  exact (state_budget (scale_budget hp hr hreg (budget_natSucc hi) hb)
    (budget_cons (frame_budget hi hz (budget_const false hlen) hc ht) hs)
    (optionSome_budget (budget_prod hone hreg))).of_enc_eq fun _ => rfl

private def checkedCall (p d r : ℕ) (reply : Reply) (bank : List ℕ) (stack : List Frame)
    (ct : ℕ × ℕ) : State :=
  if reply.1 = 1 then (checkedAddBank ((p, r, ct.2, ct.1), reply.2, bank), stack, none)
  else if reply.1 = 2 then
    if p - 1 = 0 then (bank, stack, none) else checkedBeginRound p d r 0 ct.1 ct.2 bank stack
  else (bank, stack, none)

private theorem call_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {p d r c t tag : α → ℕ} {bank values : α → List ℕ} {stack : α → List Frame}
    (hp : ComputableInSpace p encIn encNat S) (hd : ComputableInSpace d encIn encNat S)
    (hr : ComputableInSpace r encIn encNat S) (hc : ComputableInSpace c encIn encNat S)
    (ht : ComputableInSpace t encIn encNat S) (htag : ComputableInSpace tag encIn encNat S)
    (hb : ComputableInSpace bank encIn (encList encNat) S)
    (hv : ComputableInSpace values encIn (encList encNat) S)
    (hs : ComputableInSpace stack encIn (encList encFrame) S)
    (hlen : (fun a => (encIn a).length) ≼ S) :
    ComputableInSpace (fun a => checkedCall (p a) (d a) (r a) (tag a, values a)
      (bank a) (stack a) (c a, t a)) encIn encState S := by
  have hz := budget_const (encB := encNat) 0 hlen
  have hone := budget_const (encB := encNat) 1 hlen
  have htwo := budget_const (encB := encNat) 2 hlen
  have hnone := budget_const (encB := encOption (encPair encNat encNat)) none hlen
  have hreturn := state_budget hb hs hnone
  have hleaf := state_budget (add_budget hp hr ht hc hv hb) hs hnone
  have hbegin := beginRound_budget hp hd hr hz hc ht hb hs hlen
  refine (budget_ite (budget_natEq htag hone) hleaf
    (budget_ite (budget_natEq htag htwo)
      (budget_ite (budget_natIsZero (budget_natPred hp)) hreturn hbegin) hreturn)).of_enc_eq ?_
  intro a
  by_cases h1 : tag a = 1 <;> by_cases h2 : tag a = 2 <;> by_cases hz : p a - 1 = 0 <;>
    simp [checkedCall, h1, h2, hz]

private def checkedReturn (p d r : ℕ) (reply : Reply) (bank : List ℕ) (fr : Frame)
    (st : List Frame) : State :=
  if fr.2.2.1 then
    let scaled := checkedScaleBank ((p, r, reg d fr.2.2.2.2 fr.2.1,
      unitInv p fr.1), bank)
    if fr.2.1 + 1 < d then
      (scaled, (fr.1, fr.2.1 + 1, true, fr.2.2.2.1, fr.2.2.2.2) :: st,
        some (p - 1, reg d fr.2.2.2.2 (fr.2.1 + 1)))
    else if fr.1 + 1 < p - 1 then
      checkedBeginRound p d r (fr.1 + 1) fr.2.2.2.1 fr.2.2.2.2 scaled st
    else (scaled, st, none)
  else
    if fr.2.1 + 1 < d then
      (checkedScaleBank ((p, r, reg d fr.2.2.2.2 (fr.2.1 + 1), fr.1 + 1), bank),
        (fr.1, fr.2.1 + 1, false, fr.2.2.2.1, fr.2.2.2.2) :: st,
        some (1, reg d fr.2.2.2.2 (fr.2.1 + 1)))
    else
      (checkedSubBank ((p, r, fr.2.2.2.2, fr.2.2.2.1), reply.2, bank),
        (fr.1, 0, true, fr.2.2.2.1, fr.2.2.2.2) :: st,
        some (p - 1, reg d fr.2.2.2.2 0))

private theorem checkedReturn_reply (p d r : ℕ) (reply : Reply) (bank : List ℕ)
    (fr : Frame) (st : List Frame) :
    checkedReturn p d r reply bank fr st = checkedReturn p d r (0, reply.2) bank fr st := rfl

private theorem return_budget {α : Type} {encIn : α ↪ List Bool} {S : α → ℕ}
    {p d r : α → ℕ} {bank values : α → List ℕ}
    {fr : α → Frame} {st : α → List Frame}
    (hp : ComputableInSpace p encIn encNat S) (hd : ComputableInSpace d encIn encNat S)
    (hr : ComputableInSpace r encIn encNat S)
    (hb : ComputableInSpace bank encIn (encList encNat) S)
    (hv : ComputableInSpace values encIn (encList encNat) S)
    (hf : ComputableInSpace fr encIn encFrame S)
    (hs : ComputableInSpace st encIn (encList encFrame) S)
    (hlen : (fun a => (encIn a).length) ≼ S) :
    ComputableInSpace (fun a => checkedReturn (p a) (d a) (r a) (0, values a)
      (bank a) (fr a) (st a)) encIn encState S := by
  have hround := fst' hf
  have hrest := snd' hf
  have hchild := fst' hrest
  have htail := snd' hrest
  have hundo := fst' htail
  have hct := snd' htail
  have hc := fst' hct
  have ht := snd' hct
  have hz := budget_const (encB := encNat) 0 hlen
  have hone := budget_const (encB := encNat) 1 hlen
  have htrue := budget_const (encB := encBool) true hlen
  have hfalse := budget_const (encB := encBool) false hlen
  have hnone := budget_const (encB := encOption (encPair encNat encNat)) none hlen
  have hnext := budget_natSucc hchild
  have hreg := reg_budget hd ht hchild
  have hregNext := reg_budget hd ht hnext
  have hregZero := reg_budget hd ht hz
  have hunitInv := budget_comp_linear unitInv_inSpace (budget_prod hp hround)
  have hscaled := scale_budget hp hr hreg hunitInv hb
  have hneg := budget_natPred hp
  have hundoNext := state_budget hscaled
    (budget_cons (frame_budget hround hnext htrue hc ht) hs)
    (optionSome_budget (budget_prod hneg hregNext))
  have hnextRound := beginRound_budget hp hd hr (budget_natSucc hround) hc ht hscaled hs hlen
  have hpop := state_budget hscaled hs hnone
  have hundoResult := budget_ite (budget_natLt hnext hd) hundoNext
    (budget_ite (budget_natLt (budget_natSucc hround) hneg) hnextRound hpop)
  have hforwardNext := state_budget
    (scale_budget hp hr hregNext (budget_natSucc hround) hb)
    (budget_cons (frame_budget hround hnext hfalse hc ht) hs)
    (optionSome_budget (budget_prod hone hregNext))
  have hforwardLast := state_budget (sub_budget hp hr ht hc hv hb)
    (budget_cons (frame_budget hround hz htrue hc ht) hs)
    (optionSome_budget (budget_prod hneg hregZero))
  refine (budget_ite hundo hundoResult
    (budget_ite (budget_natLt hnext hd) hforwardNext hforwardLast)).of_enc_eq ?_
  intro a
  by_cases hu : (fr a).2.2.1 = true <;>
    by_cases hj : (fr a).2.1 + 1 < d a <;>
    by_cases hi : (fr a).1 + 1 < p a - 1 <;> simp [checkedReturn, hu, hj, hi]

private def checkedStepCore (par : Params) (reply : Reply) (q : State) : State :=
  q.2.2.elim
    (if q.2.1.isEmpty then q else
      checkedReturn par.1 par.2.1 par.2.2 reply q.1
        (q.2.1.headD (0, 0, false, 0, 0)) q.2.1.tail)
    (fun ct => checkedCall par.1 par.2.1 par.2.2 reply q.1 q.2.1 ct)

private theorem checkedStepCore_inSpace :
    ComputableInSpace (fun a : (Params × State) × Reply => checkedStepCore a.1.1 a.2 a.1.2)
      encStepArgs encState (fun a => (encStepArgs a).length) := by
  have hfull := fst encFullState encReply
  have hpar := fst' hfull
  have hp := fst' hpar
  have hd := fst' (snd' hpar)
  have hr := snd' (snd' hpar)
  have hq := snd' hfull
  have hbank := fst' hq
  have hstack := fst' (snd' hq)
  have hmode := snd' (snd' hq)
  have hreply := snd encFullState encReply
  have hvalues := snd' hreply
  have hret := return_budget hp hd hr hbank hvalues
    (budget_headD (0, 0, false, 0, 0) hstack) (budget_tail hstack) (.refl _)
  have hstop := budget_ite (budget_isEmpty hstack) hq hret
  have hctx := fst encStepArgs (encPair encNat encNat)
  have hctxFull := budget_comp_linear hfull hctx
  have hctxPar := fst' hctxFull
  have hctxState := snd' hctxFull
  have hctxReply := budget_comp_linear hreply hctx
  have hct := snd encStepArgs (encPair encNat encNat)
  have hcall := call_budget (fst' hctxPar) (fst' (snd' hctxPar)) (snd' (snd' hctxPar))
    (fst' hct) (snd' hct) (fst' hctxReply)
    (fst' hctxState) (snd' hctxReply) (fst' (snd' hctxState)) (.refl _)
  have hid : ComputableInSpace (fun a : (Params × State) × Reply => a) encStepArgs encStepArgs
      (fun a => (encStepArgs a).length) := of_inO ComputableInDegree.id'.inO_one
  refine (budget_comp_linear (optionElimSnd hstop hcall) (budget_prod hid hmode)).of_enc_eq ?_
  intro a
  cases hm : a.1.2.2.2 with
  | none => simp [checkedStepCore, hm, checkedReturn_reply]
  | some ct => simp [checkedStepCore, hm]

private theorem checkedBeginRound_eq (p d r round c t : ℕ) (bank : List ℕ)
    (st : List Frame) (hbank : validBank p d r bank = true) :
    checkedBeginRound p d r round c t bank st = beginRound p d r round c t bank st := by
  rw [checkedBeginRound, checkedScaleBank_eq p d r _ _ bank hbank]
  rfl

private theorem checkedStepCore_eq (p d r : ℕ) (reply : Reply) (q : State)
    (hbank : validBank p d r q.1 = true) : checkedStepCore (p, d, r) reply q =
      stepCore p d r reply q := by
  rcases q with ⟨bank, stack, mode⟩
  cases mode with
  | some ct =>
    rcases ct with ⟨c, t⟩
    simp only [checkedStepCore, Option.elim_some, checkedCall, stepCore]
    split_ifs
    · rw [checkedAddBank_eq p d r _ _ _ bank hbank]
    · rfl
    · rw [checkedBeginRound_eq p d r _ _ _ bank stack hbank]
    · rfl
  | none =>
    cases stack with
    | nil => rfl
    | cons fr st =>
      rcases fr with ⟨round, child, undo, c, t⟩
      simp only [checkedStepCore, Option.elim_none, List.isEmpty_cons,
        Bool.false_eq_true, ↓reduceIte, List.headD_cons, List.tail_cons, checkedReturn, stepCore]
      cases undo with
      | true =>
        simp only [↓reduceIte]
        rw [checkedScaleBank_eq p d r _ _ bank hbank]
        have hscaled := validBank_scaleBank p d r (reg d t child) (unitInv p round) bank hbank
        by_cases hj : child + 1 < d
        · simp only [hj, ↓reduceIte]
        · by_cases hi : round + 1 < p - 1
          · simp only [hj, hi, ↓reduceIte]
            rw [checkedBeginRound_eq p d r _ _ _ _ st hscaled]
          · simp only [hj, hi, ↓reduceIte]
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        by_cases hj : child + 1 < d
        · simp only [hj, ↓reduceIte]
          rw [checkedScaleBank_eq p d r _ _ bank hbank]
        · simp only [hj, ↓reduceIte]
          rw [checkedSubBank_eq p d r _ _ _ bank hbank]

/-- One returned reply advances the actual raw controller in native linear work space. -/
theorem stepState_inSpace :
    ComputableInSpace (fun a : (Params × State) × Reply =>
      step a.1.1.1 a.1.1.2.1 a.1.1.2.2 a.2 a.1.2)
      encStepArgs encState (fun a => (encStepArgs a).length) := by
  have hfull := fst encFullState encReply
  have hq := snd' hfull
  have hguard := budget_comp_linear validBank_inSpace hfull
  refine (budget_ite hguard checkedStepCore_inSpace hq).of_enc_eq ?_
  rintro ⟨⟨⟨p, d, r⟩, bank, stack, mode⟩, reply⟩
  by_cases h : validBank p d r bank = true
  · simp only [step, h, ↓reduceIte]
    exact congrArg encState (checkedStepCore_eq p d r reply (bank, stack, mode) h).symm
  · simp only [step, h, Bool.false_eq_true, ↓reduceIte]

/-- The runtime parameter header is retained beside the updated raw state. -/
theorem step_inSpace :
    ComputableInSpace (fun a : (Params × State) × Reply =>
      (a.1.1, step a.1.1.1 a.1.1.2.1 a.1.1.2.2 a.2 a.1.2))
      encStepArgs encFullState (fun a => (encStepArgs a).length) :=
  budget_prod (fst' (fst encFullState encReply)) stepState_inSpace

/-- The caller halts at an empty-stack return, and rejects malformed storage immediately. -/
theorem halted_inSpace :
    ComputableInSpace (fun q : Params × State =>
      !validBank q.1.1 q.1.2.1 q.1.2.2 q.2.1 || (q.2.2.2.isNone && q.2.2.1.isEmpty))
      encFullState encBool (fun q => (encFullState q).length) := by
  have hstate := snd encParams encState
  have hrest := snd' hstate
  have hstack := fst' hrest
  have hmode := snd' hrest
  have hnone := budget_finite (encC := encBool) Bool.not (optionIsSome_budget hmode)
  have hret := budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 && q.2)
    (budget_prod hnone (budget_isEmpty hstack))
  have hbad := budget_finite (encC := encBool) Bool.not validBank_inSpace
  refine (budget_finite (encC := encBool) (fun q : Bool × Bool => q.1 || q.2)
    (budget_prod hbad hret)).of_enc_eq ?_
  intro q
  cases q.2.2.2 <;> rfl

/-- A valid bank request retains exactly the child registers and omits the target. -/
theorem length_point {d r : ℕ} (bank : List ℕ) (hlen : bank.length = (d + 1) * r)
    (t : Fin (d + 1)) : (point d r t bank).length = d * r := by
  have ht : t.val ≤ d := by omega
  simp only [point, Nat.mod_eq_of_lt t.isLt, List.length_append, List.length_drop,
    List.length_take, hlen]
  rw [Nat.min_eq_left (Nat.mul_le_mul_right r t.isLt.le), ← Nat.sub_mul]
  have hsub : d + 1 - (t.val + 1) = d - t.val := by omega
  rw [hsub, ← Nat.add_mul, Nat.sub_add_cancel ht]

/-- Every coordinate of a cyclic bank slice is the existing child's designated register. -/
theorem point_getD {d r : ℕ} (bank : List ℕ) (hlen : bank.length = (d + 1) * r)
    (t : Fin (d + 1)) (j : Fin d) (i : Fin r) :
    (point d r t bank).getD (index r j i) 0 =
      bank.getD (index r (reg d t j) i) 0 := by
  have ht : t.val ≤ d := by omega
  have htail : (bank.drop ((t.val + 1) * r)).length = (d - t.val) * r := by
    rw [List.length_drop, hlen, ← Nat.sub_mul]
    congr 1
    omega
  rw [point, Nat.mod_eq_of_lt t.isLt]
  by_cases hj : j.val < d - t.val
  · have hpos : index r j i < (bank.drop ((t.val + 1) * r)).length := by
      rw [htail]
      calc
        index r j i < (j.val + 1) * r := by unfold index; nlinarith [i.isLt]
        _ ≤ (d - t.val) * r := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hj)
    have hreg : reg d t j = t.val + (j.val + 1) := by
      apply Nat.mod_eq_of_lt
      omega
    have hindex : (t.val + 1) * r + index r j i = index r (reg d t j) i := by
      rw [hreg]
      unfold index
      ring
    rw [List.getD_append _ _ 0 _ hpos]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, hindex]
  · have hjge : d - t.val ≤ j.val := by omega
    have hjsmall : j.val - (d - t.val) < t.val := by omega
    have hpos : index r (j.val - (d - t.val)) i < t.val * r := by
      calc
        index r (j.val - (d - t.val)) i < (j.val - (d - t.val) + 1) * r := by
          unfold index
          nlinarith [i.isLt]
        _ ≤ t.val * r := Nat.mul_le_mul_right r (Nat.succ_le_of_lt hjsmall)
    have hindex : index r j i = (d - t.val) * r + index r (j.val - (d - t.val)) i := by
      have hsplit : j.val = (d - t.val) + (j.val - (d - t.val)) := by omega
      calc
        index r j i = i.val + r * ((d - t.val) + (j.val - (d - t.val))) := by
          rw [← hsplit]
          rfl
        _ = _ := by unfold index; ring
    have hright : (bank.drop ((t.val + 1) * r)).length ≤ index r j i := by
      rw [htail, hindex]
      omega
    have hreg : reg d t j = j.val - (d - t.val) := by
      have hsum : t.val + (j.val + 1) = (d + 1) + (j.val - (d - t.val)) := by omega
      rw [reg, hsum, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [List.getD_append_right _ _ 0 _ hright, htail, hindex, Nat.add_sub_cancel_left]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hpos, hreg]

/-- The requested raw point has exactly the field coordinates consumed by the existing gate
extension. Modulus-offset padding contributes zero in the field. -/
theorem point_toRegs {p d r : ℕ} (bank : List ℕ) (hlen : bank.length = (d + 1) * r)
    (t : Fin (d + 1)) (j : Fin d) (i : Fin r) :
    ((point d r t bank).getD (index r j i) 0 : ZMod p) =
      toRegs p d r bank (Ary.reg t j) i := by
  rw [point_getD bank hlen, reg_eq]
  rfl

end Cslib.TreeEval.Ary.Packed.RawController
