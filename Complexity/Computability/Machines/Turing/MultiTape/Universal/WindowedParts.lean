/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedBound
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.ZipFold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Lists
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts
import Complexity.Computability.Machines.Turing.MultiTape.Internal.EqualityPrimitives
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cost of cutting, pasting and stepping windows

Cutting windows (`Turing.MultiTapeTM.Universal.Windowed.extract`) and pasting them back
(`Turing.MultiTapeTM.Universal.Windowed.restore`) take time linear in the encoded windows for each
window, so time `O((K + 1) * N)` for `K` windows of total encoded length `N`; every operation on
the cells of a window is linear in their encoded length. A windowed step
(`Turing.MultiTapeTM.Universal.Windowed.wstep`) takes time cubic in the encoded description and
windows. Halving a number of steps in unary takes linear time.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.extract_inO`, `.restore_inO`: cutting and pasting.
* `Turing.MultiTapeTM.Universal.Windowed.wstep_inO`: a windowed step.
* `Turing.MultiTapeTM.Universal.Windowed.firstHalf_inO`, `.half_inO`: halving in unary.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

open ComputableInO

/-! ### Sizes -/

private lemma one_le_length_encInt (z : ℤ) : 1 ≤ (encInt z).length := by
  rw [length_encInt]; split_ifs <;> omega

private lemma length_encList_drop_le {α : Type} (enc : α ↪ List Bool) (l : List α) (i : ℕ) :
    (encList enc (l.drop i)).length ≤ (encList enc l).length :=
  ((List.drop_sublist i l).flatMap (frame ∘ enc)).length_le

/-- Cutting does not lengthen a window. -/
private lemma length_eTape_cut_le (r : ℕ) (t : Tape) :
    (eTape (cut r t)).length ≤ (eTape t).length := by
  have h₁ := one_le_length_encInt t.head
  have h₂ := length_encList_take_le eSym t.left r
  have h₃ := length_encList_take_le eSym t.right (r + 1)
  simp only [cut, eTape_apply, length_encPair, encInt_zero, List.length_singleton]
  omega

/-- Pasting gives a window no longer than the two windows together. -/
private lemma length_eTape_paste_le (r : ℕ) (o i : Tape) :
    (eTape (paste r o i)).length ≤ (eTape o).length + (eTape i).length := by
  have h₁ := one_le_length_encInt o.head
  have h₂ := length_encList_drop_le eSym o.left r
  have h₃ := length_encList_drop_le eSym o.right (r + 1)
  simp only [paste, eTape_apply, length_encPair, encInt_zero, List.length_singleton,
    encList_append, List.length_append]
  omega

/-- Mapping a function that does not lengthen elements does not lengthen the encoded list. -/
private lemma length_encList_map_le {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {f : α → β} (hf : ∀ a, (encB (f a)).length ≤ (encA a).length) (l : List α) :
    (encList encB (l.map f)).length ≤ (encList encA l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := hf a
    simp only [List.map_cons, encList_cons, List.length_append, length_frame]
    omega

/-- Zipping with a function whose values are no longer than its two arguments together. -/
private lemma length_encList_zipWith_le {α β γ : Type} {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {f : α → β → γ}
    (hf : ∀ a b, (encC (f a b)).length ≤ (encA a).length + (encB b).length) (l₁ : List α)
    (l₂ : List β) :
    (encList encC (List.zipWith f l₁ l₂)).length ≤
      (encList encA l₁).length + (encList encB l₂).length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp
    | cons b l₂ =>
      have := hf a b
      have := ih l₂
      simp only [List.zipWith_cons_cons, encList_cons, List.length_append, length_frame] at *
      omega

/-! ### Cutting and pasting a window -/

/-- Cutting a window, in linear time. -/
private lemma cut_inO : ComputableInO (fun q : ℕ × Tape => cut q.1 q.2)
    (encPair encUnary eTape) eTape (fun q => (encPair encUnary eTape q).length)
    fun q => (encPair encUnary eTape q).length := by
  unfold cut
  refine .mono (by fun_prop) 32 (fun q => ?_) fun q => ?_ <;>
  · simp only [eTape_apply, length_encPair, encUnary_apply, List.length_replicate]
    omega

/-- Pasting a window back, in linear time. -/
private lemma paste_inO : ComputableInO (fun q : ℕ × Tape × Tape => paste q.1 q.2.1 q.2.2)
    (encPair encUnary (encPair eTape eTape)) eTape
    (fun q => (encPair encUnary (encPair eTape eTape) q).length)
    fun q => (encPair encUnary (encPair eTape eTape) q).length := by
  unfold paste
  refine .mono (by fun_prop) 64 (fun q => ?_) fun q => ?_ <;>
  · have h₁ := length_encList_drop_le eSym q.2.1.left q.1
    have h₂ := length_encList_drop_le eSym q.2.1.right (q.1 + 1)
    simp only [eTape_apply, length_encPair, encUnary_apply, List.length_replicate] at *
    omega

/-! ### Cutting and pasting all windows -/

/-- **Cutting windows** of radius `r`, in time linear in the encoded windows for each window. -/
theorem extract_inO :
    ComputableInO (fun p : ℕ × Win => extract p.1 p.2) (encPair encUnary eWin) eWin
      (fun p => (p.2.2.length + 1) * ((encPair encUnary eWin p).length + 1))
      (fun p => (p.2.2.length + 1) * ((encPair encUnary eWin p).length + 1)) := by
  have hw := snd encUnary eWin
  have hmap := ComputableInO.mapWith (encP := encUnary) (enc := eTape) (encB := eTape) cut_inO
    (fst encUnary eWin) hw.snd'
  refine ((hw.fst'.prod hmap).of_enc_eq (encOut := eWin)
    (g := fun p : ℕ × Win => extract p.1 p.2) fun _ => rfl).mono 8 (fun p => ?_) fun p => ?_
  all_goals
    obtain ⟨r, s, ts⟩ := p
    have h₁ := length_encList_map_le (length_eTape_cut_le r) ts
    have h₂ : listMax (fun a => (encPair encUnary eTape (r, a)).length) ts ≤
        2 * (encUnary r).length + 1 + (encList eTape ts).length :=
      listMax_le fun a ha => by
        have := length_le_encList_of_mem eTape ha
        simp only [length_encPair]
        omega
    have hN : (encPair encUnary eWin (r, s, ts)).length =
        2 * (encUnary r).length + 1 + (2 * (eSym s).length + 1 + (encList eTape ts).length) := by
      simp only [length_encPair]
    simp only [hN] at *
    nlinarith

/-- Pasting a window back onto its outer window, if there is one. -/
private def pasteOne (r : ℕ) (t : Tape) (b : Option Tape) : Option Tape := b.map (paste r t)

private lemma zipFold_pasteOne (r : ℕ) (outer rest : List Tape) :
    zipFold pasteOne r outer rest = List.zipWith (paste r) outer rest := by
  induction outer generalizing rest with
  | nil => rfl
  | cons t outer ih => cases rest <;> simp [zipFold, pasteOne, ih]

attribute [local fun_prop] paste_inO in
private lemma pasteOne_inO : ComputableInO (fun q : ℕ × Tape × Option Tape =>
    pasteOne q.1 q.2.1 q.2.2) (encPair encUnary (encPair eTape (encOption eTape)))
    (encOption eTape) (fun q => (encPair encUnary (encPair eTape (encOption eTape)) q).length)
    fun q => (encPair encUnary (encPair eTape (encOption eTape)) q).length := by
  have e : (fun q : ℕ × Tape × Option Tape => pasteOne q.1 q.2.1 q.2.2) = fun q =>
      if q.2.2.isSome then some (paste q.1 q.2.1 (q.2.2.getD default)) else none := by
    funext ⟨r, t, b⟩
    cases b <;> rfl
  rw [e]
  refine .mono (by fun_prop) 1024 (fun q => ?_) fun q => ?_
  all_goals
    obtain ⟨r, t, _ | i⟩ := q
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, length_encPair]
      omega
    have hpaste := length_eTape_paste_le r t i
    simp only [Option.isSome_some, ↓reduceIte, Option.getD_some, length_encPair, encOption_some,
      List.length_cons] at *
    omega

/-- **Pasting windows back**, in time linear in the encoded windows for each window. -/
theorem restore_inO :
    ComputableInO (fun p : ℕ × Win × Win => restore p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair eWin eWin)) eWin
      (fun p => (p.2.1.2.length + 1) * ((encPair encUnary (encPair eWin eWin) p).length + 1))
      (fun p => (p.2.1.2.length + 1) * ((encPair encUnary (encPair eWin eWin) p).length + 1)) := by
  have hzip := ComputableInO.zipFold pasteOne_inO 2 fun q i => by
    obtain ⟨r, o, w⟩ := q
    have h₁ := length_encList_zipWith_le (length_eTape_paste_le r) (o.take i) w
    have h₂ := length_encList_take_le eTape o i
    rw [zipFold_pasteOne]
    simp only [length_encPair] at *
    omega
  have hr := fst encUnary (encPair eWin eWin)
  have ho := (snd encUnary (encPair eWin eWin)).fst'
  have hi := (snd encUnary (encPair eWin eWin)).snd'
  refine ((hi.fst'.prod (hzip.comp (hr.prod (ho.snd'.prod hi.snd')))).of_enc_eq (encOut := eWin)
    (g := fun p : ℕ × Win × Win => restore p.1 p.2.1 p.2.2) fun ⟨r, o, i⟩ => ?_).mono 16
    (fun p => ?_) fun p => ?_
  · simp only [restore, Function.comp_apply, zipFold_pasteOne]
  all_goals
    obtain ⟨r, ⟨so, o⟩, ⟨si, w⟩⟩ := p
    simp only [length_encPair] at *
    nlinarith

/-! ### Halving in unary -/

/-- The transducer emitting a symbol on every other input symbol: from the first one on if
started in `false`, from the second one on if started in `true`. -/
private def halfT (start : Bool) : Transducer Bool Bool where
  q₀ := start
  step q _ := (!q, if q then [] else [true])
  final _ := []
  length_step_le q _ := by cases q <;> simp
  length_final_le _ := by simp

private lemma run_halfT (start : Bool) (n : ℕ) :
    (halfT start).run false (List.replicate n true) = List.replicate (n - n / 2) true ∧
      (halfT start).run true (List.replicate n true) = List.replicate (n / 2) true := by
  induction n with
  | zero => simp [halfT]
  | succ n ih =>
    have h₁ : (halfT start).step false true = (true, [true]) := rfl
    have h₂ : (halfT start).step true true = (false, []) := rfl
    rw [List.replicate_succ, Transducer.run_cons, Transducer.run_cons, h₁, h₂, ih.1, ih.2]
    refine ⟨?_, ?_⟩
    · rw [List.singleton_append, ← List.replicate_succ]
      congr 1
      omega
    · rw [List.nil_append]
      congr 1
      omega

/-- The first half of a number of steps, in unary, in linear time. -/
theorem firstHalf_inO :
    ComputableInO firstHalf encUnary encUnary (fun n => (encUnary n).length)
      (fun n => (encUnary n).length) :=
  (ComputableTidilyInO.of_linear ((halfT false).computableTidilyInLinearTimeAndSpace fun n =>
    (run_halfT false n).1.symm)).computableInO

/-- Half a number of steps, rounded down, in unary, in linear time. -/
theorem half_inO :
    ComputableInO (· / 2) encUnary encUnary (fun n => (encUnary n).length)
      (fun n => (encUnary n).length) :=
  (ComputableTidilyInO.of_linear ((halfT true).computableTidilyInLinearTimeAndSpace fun n =>
    (run_halfT true n).2.symm)).computableInO

/-! ### A windowed step -/

/-! #### Coded input cells -/

private lemma inPos_eq (c : Option ℕ) : inPos c = if decide (c = some 0) then 0 else 1 := by
  simp only [inPos, decide_eq_true_eq]

private lemma inSym_eq (c : Option ℕ) : inSym c =
    if decide (c = some 0) then none else if c.isSome then some (c.getD 0 - 1) else none := by
  rcases c with _ | _ | v <;> simp [inSym]

private lemma inPos_le (c : Option ℕ) : inPos c ≤ 1 := by
  unfold inPos; split_ifs <;> omega

private lemma length_inSym_le (c : Option ℕ) : (eSym (inSym c)).length ≤ (eSym c).length := by
  rcases c with _ | _ | v <;> simp [inSym]

/-- Whether a coded input cell is the left end, in quadratic time. -/
private lemma isEnd_inO : ComputableInO (fun c : Option ℕ => decide (c = some 0)) eSym
    encBool (fun c => ((eSym c).length + 1) ^ 2) fun c => (eSym c).length := by
  refine ((ComputableInO.eq eSym).comp ((of_linear (.of_eq fun _ => rfl) :
    ComputableInO (fun c : Option ℕ => c) eSym eSym _ _).prod
      (const (some 0)))).mono 8 (fun c => ?_) fun c => ?_ <;>
  · simp only [length_encPair, encOption_some, encUnary_apply, List.length_cons,
      List.length_replicate]
    nlinarith

/-- `Turing.MultiTapeTM.Universal.Windowed.inPos`, in quadratic time. -/
private lemma inPos_inO : ComputableInO inPos eSym encNat
    (fun c => ((eSym c).length + 1) ^ 2) fun c => (eSym c).length := by
  refine ((isEnd_inO.ite (const 0) (const 1)).of_enc_eq (g := inPos)
    fun c => by rw [inPos_eq]).mono 4 (fun c => ?_) fun c => ?_ <;>
  · have : (eSym c).length ≤ ((eSym c).length + 1) ^ 2 := by nlinarith
    split_ifs <;> omega

/-- `Turing.MultiTapeTM.Universal.Windowed.inSym`, in quadratic time. -/
private lemma inSym_inO : ComputableInO inSym eSym eSym
    (fun c => ((eSym c).length + 1) ^ 2) fun c => (eSym c).length := by
  have hsome := (ComputableInDegree.optionSome (enc₁ := encUnary) (enc := eSym)).inO_one
    |>.comp_linear (ComputableInDegree.unary_pred.inO_one.comp_linear
      (ComputableInDegree.getD (enc₁ := encUnary) (enc := eSym) 0).inO_one)
  refine ((isEnd_inO.ite (const none) ((ComputableInDegree.isSome encUnary).inO_one.ite
    hsome (const none))).of_enc_eq (g := inSym) fun c => by rw [inSym_eq]; rfl).mono 4
    (fun c => ?_) fun c => ?_ <;>
  · have : (eSym c).length ≤ ((eSym c).length + 1) ^ 2 := by nlinarith
    have : (encOption encUnary c).length = (eSym c).length := rfl
    split_ifs <;> omega

/-! #### The step -/

/-- The input window, or a blank window if there is none. -/
private def wHead (x : Desc × Win) : Tape := x.2.2.headD default

/-- The context of the step on a windowed configuration with at least one window. -/
private def wCtx (x : Desc × Win) : WCtx :=
  ((x.1, ⟨x.2.1, inPos (wHead x).read, x.2.2.tail⟩), inSym (wHead x).read)

/-- The windowed configuration after a step, from the input window, its coded position and the
result of the step. -/
private def wFin (y : (Tape × ℕ) × SCfg × Option ℕ) : Win × Option ℕ :=
  ((y.2.1.state, moveIn y.1.1 y.1.2 y.2.1.inputPos :: y.2.1.workTapes), y.2.2)

private lemma wstep_eq (x : Desc × Win) : wstep x.1 x.2 = if x.2.2.isEmpty then (x.2, none) else
    wFin ((wHead x, inPos (wHead x).read), stepWith (wCtx x).1.1 (wCtx x).1.2 (wCtx x).2) := by
  obtain ⟨d, s, _ | ⟨i, ts⟩⟩ := x <;> rfl

private lemma moveIn_eq (t : Tape) (p p' : ℕ) : moveIn t p p' =
    if decide (p' = p + 1) then t.move .pos
    else if decide (p' + 1 = p) then t.move .neg else t := by
  simp only [moveIn, decide_eq_true_eq]

/-- Reassembling the windowed configuration after a step, in quadratic time. -/
private lemma wFin_inO : ComputableInO wFin
    (encPair (encPair eTape encNat) (encPair eCfg eSym)) (encPair eWin eSym)
    (fun y => ((encPair (encPair eTape encNat) (encPair eCfg eSym) y).length + 1) ^ 2)
    fun y => (encPair (encPair eTape encNat) (encPair eCfg eSym) y).length := by
  have hy₁ := fst (encPair eTape encNat) (encPair eCfg eSym)
  have hy₂ := snd (encPair eTape encNat) (encPair eCfg eSym)
  have ht := hy₁.fst'
  have hp := hy₁.snd'
  have hf := hy₂.fst'.of_enc_eq (encOut := eCfgFields)
    (g := fun y : (Tape × ℕ) × SCfg × Option ℕ => (y.2.1.state, y.2.1.inputPos, y.2.1.workTapes))
    fun _ => rfl
  have hp' := hf.snd'.fst'
  have hsucc := ComputableInO.natSucc
  have hc₁ := (ComputableInO.eq encNat).comp (hp'.prod (hsucc.comp hp))
  have hc₂ := (ComputableInO.eq encNat).comp ((hsucc.comp hp').prod hp)
  have hmv := hc₁.ite (Universal.movePos_deg.inO_one.comp_linear ht)
    (hc₂.ite (Universal.moveNeg_deg.inO_one.comp_linear ht) ht)
  have hlist := (ComputableInDegree.cons eTape).inO_one.comp_linear
    (hmv.prod hf.snd'.snd')
  refine (((hf.fst'.prod hlist).prod hy₂.snd').of_enc_eq (g := wFin) fun y => ?_).mono 64
    (fun y => ?_) fun y => ?_
  · simp only [wFin, moveIn_eq]
    rfl
  all_goals
    obtain ⟨⟨t, p⟩, ⟨s, p', ws⟩, o⟩ := y
    have h₁ := ComputableTidilyInO.length_encNat_add_le p 1
    have h₂ := ComputableTidilyInO.length_encNat_add_le p' 1
    simp only [Function.comp_apply, length_encPair, eCfg_apply] at *
    split_ifs <;> nlinarith

/-! #### Sizes -/

private lemma length_read_le (t : Tape) : (eSym t.read).length ≤ (eTape t).length := by
  have : (eSym (t.right.headD none)).length ≤ (encList eSym t.right).length := by
    cases t.right <;> simp; omega
  simp only [Tape.read, eTape_apply, length_encPair] at *
  omega

private lemma length_encList_tail_le {α : Type} (enc : α ↪ List Bool) (l : List α) :
    (encList enc l.tail).length ≤ (encList enc l).length :=
  ((List.tail_sublist l).flatMap (frame ∘ enc)).length_le

private lemma length_read_headD_le (l : List Tape) :
    (eSym (l.headD default).read).length ≤ (encList eTape l).length := by
  cases l with
  | nil => exact le_of_eq rfl
  | cons t l =>
    have := length_read_le t
    simp only [List.headD_cons, encList_cons, List.length_append, length_frame]
    omega

private lemma length_eWCtx_wCtx_le (x : Desc × Win) :
    (eWCtx (wCtx x)).length ≤ 4 * (encPair eDesc eWin x).length + 8 := by
  have h₁ := length_inSym_le (wHead x).read
  have h₂ := length_read_headD_le x.2.2
  have h₃ := length_encList_tail_le eTape x.2.2
  have h₄ : (encNat (inPos (wHead x).read)).length ≤ 1 :=
    (length_encNat_le _).trans (inPos_le _)
  simp only [wCtx, wHead, eCfg_apply, length_encPair] at *
  omega

private lemma wTime_wCtx_le (x : Desc × Win) :
    wTime (wCtx x) ≤ 32 * ((encPair eDesc eWin x).length + 1) ^ 3 := by
  have hW := length_eWCtx_wCtx_le x
  have h₁ : (wCtx x).1.2.workTapes.length ≤ (encList eTape x.2.2).length := by
    have := length_le_length_encList eTape x.2.2
    simp only [wCtx, List.length_tail]
    omega
  have h₂ : (wCtx x).1.1.table.length ≤ (eDesc x.1).length := by
    have := length_le_length_encList (encPair eKey eAct) x.1.table
    simp only [wCtx, eDesc_apply, length_encPair]
    omega
  have h₃ : (encNat (wCtx x).1.2.inputPos).length ≤ 1 :=
    (length_encNat_le _).trans (inPos_le _)
  have hN : (encList eTape x.2.2).length + (eDesc x.1).length ≤ (encPair eDesc eWin x).length := by
    simp only [length_encPair]
    omega
  have hD : (eDesc (wCtx x).1.1).length ≤ (encPair eDesc eWin x).length := by
    simp only [wCtx, length_encPair]
    omega
  unfold wTime
  generalize (encPair eDesc eWin x).length = N at *
  generalize (eWCtx (wCtx x)).length = W at *
  generalize (eDesc (wCtx x).1.1).length = D at *
  generalize (encNat (wCtx x).1.2.inputPos).length = P at *
  have hA : (wCtx x).1.2.workTapes.length + (wCtx x).1.1.table.length + 1 ≤ 2 * (N + 1) := by
    omega
  have h := Nat.mul_le_mul (Nat.mul_le_mul hA (show D + 1 ≤ N + 1 by omega))
    (show W + 1 ≤ 9 * (N + 1) by omega)
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith

/-- The arguments of the reassembly: the input window, its coded position and the result of the
step, in cubic time and linear space. -/
private lemma wArgs_inO : ComputableInO
    (fun x : Desc × Win => ((wHead x, inPos (wHead x).read),
      stepWith (wCtx x).1.1 (wCtx x).1.2 (wCtx x).2))
    (encPair eDesc eWin) (encPair (encPair eTape encNat) (encPair eCfg eSym))
    (fun x => ((encPair eDesc eWin x).length + 1) ^ 3) fun x => (encPair eDesc eWin x).length := by
  have hd := fst eDesc eWin
  have hw := snd eDesc eWin
  have hhead := (ComputableInDegree.listHeadD eTape default).inO_one.comp_linear hw.snd'
  have hread := Universal.read_deg.inO_one.comp_linear hhead
  have hpos := inPos_inO.comp hread
  have hsym := inSym_inO.comp hread
  have htail := (ComputableInDegree.listTail eTape).inO_one.comp_linear hw.snd'
  have hcfg := (hw.fst'.prod (hpos.prod htail)).of_enc_eq (encOut := eCfg)
    (g := fun x : Desc × Win => (⟨x.2.1, inPos (wHead x).read, x.2.2.tail⟩ : SCfg)) fun _ => rfl
  have hctx := ((hd.prod hcfg).prod hsym).of_enc_eq (encOut := eWCtx) (g := wCtx) fun _ => rfl
  have hstep := stepWith_inO.comp hctx
  refine (((hhead.prod hpos).prod hstep).of_enc_eq (g := fun x : Desc × Win =>
    ((wHead x, inPos (wHead x).read), stepWith (wCtx x).1.1 (wCtx x).1.2 (wCtx x).2))
    fun _ => rfl).mono 128 (fun x => ?_) fun x => ?_
  all_goals
    have h₁ := length_read_headD_le x.2.2
    have h₂ := wTime_wCtx_le x
    have h₃ := length_eWCtx_wCtx_le x
    have hL : (encList eTape x.2.2).length ≤ (encPair eDesc eWin x).length := by
      simp only [length_encPair]; omega
    simp only [Function.comp_apply] at *
    generalize (encPair eDesc eWin x).length = N at *
    generalize (eSym (x.2.2.headD default).read).length = C at *
    generalize wTime (wCtx x) = Wt at *
    generalize (eWCtx (wCtx x)).length = W at *
    have : (C + 1) ^ 2 ≤ (N + 1) ^ 3 := by
      calc (C + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have : N + 1 ≤ (N + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    omega

/-- **A windowed step**, in time cubic in the encoded description and windows. -/
theorem wstep_inO :
    ComputableInO (fun p : Desc × Win => wstep p.1 p.2) (encPair eDesc eWin) (encPair eWin eSym)
      (fun p => ((encPair eDesc eWin p).length + 1) ^ 3)
      (fun p => ((encPair eDesc eWin p).length + 1) ^ 3) := by
  obtain ⟨c, hc⟩ := wArgs_inO.length_le
  have hw := snd eDesc eWin
  have hempty := (ComputableInDegree.listIsEmpty eTape).inO_one.comp_linear hw.snd'
  refine ((hempty.ite (hw.prod (const none)) (wFin_inO.comp wArgs_inO)).of_enc_eq
    (g := fun x : Desc × Win => wstep x.1 x.2) fun x => by rw [wstep_eq]; rfl).mono
    (4 * (c + 2) ^ 2) (fun x => ?_) fun x => ?_
  all_goals
    have h := hc x
    generalize (encPair eDesc eWin x).length = N at *
    generalize (encPair (encPair eTape encNat) (encPair eCfg eSym) _).length = G at *
    have hG : G + 1 ≤ (c + 1) * (N + 1) := by nlinarith
    have hG2 := Nat.mul_le_mul hG hG
    have h₁ : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    split_ifs <;> nlinarith

end Turing.MultiTapeTM.Universal.Windowed
