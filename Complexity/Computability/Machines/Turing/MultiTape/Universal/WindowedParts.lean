/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedBound
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
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

open ComputableTidilyInO

/-! ### Linear-time list primitives -/

section Primitives

variable {α : Type}

/-- Taking the first `n` elements, with `n` in unary, in linear time. All uses of the primitive go
through this lemma. -/
private lemma takeU (enc : α ↪ List Bool) :
    ComputableTidilyInO (fun p : List α × ℕ => p.1.take p.2) (encPair (encList enc) encUnary)
      (encList enc) (fun p => (encPair (encList enc) encUnary p).length)
      fun p => (encPair (encList enc) encUnary p).length :=
  (ComputableInDegree.takeUnary enc).inO_one.tidy

/-- Dropping the first `n` elements, with `n` in unary, in linear time. All uses of the primitive
go through this lemma. -/
private lemma dropU (enc : α ↪ List Bool) :
    ComputableTidilyInO (fun p : List α × ℕ => p.1.drop p.2) (encPair (encList enc) encUnary)
      (encList enc) (fun p => (encPair (encList enc) encUnary p).length)
      fun p => (encPair (encList enc) encUnary p).length :=
  (ComputableInDegree.dropUnary enc).inO_one.tidy

end Primitives

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

private lemma tapeFields_inO : ComputableTidilyInO (fun t : Tape => (t.head, t.left, t.right))
    eTape eTapeFields (fun t => (eTape t).length) fun t => (eTape t).length :=
  of_linear (.of_eq fun _ => rfl)

/-- Cutting a window, in linear time. -/
private lemma cut_inO : ComputableTidilyInO (fun q : ℕ × Tape => cut q.1 q.2)
    (encPair encUnary eTape) eTape (fun q => (encPair encUnary eTape q).length)
    fun q => (encPair encUnary eTape q).length := by
  have hr := fst encUnary eTape
  have ht := tapeFields_inO.comp_linear (snd encUnary eTape)
  have hl := (takeU eSym).comp_linear (ht.snd'.fst'.prod hr)
  have hr' := (takeU eSym).comp_linear
    (ht.snd'.snd'.prod (ComputableTidilyInDegree.unary_succ.inO_one.comp_linear hr))
  exact (((const (encMid := encInt) (0 : ℤ)).prod (hl.prod hr')).of_enc_eq (encOut := eTape)
    (g := fun q : ℕ × Tape => cut q.1 q.2) fun _ => rfl).mono 8 (fun q => by omega)
    fun q => by omega

/-- Pasting a window back, in linear time. -/
private lemma paste_inO : ComputableTidilyInO (fun q : ℕ × Tape × Tape => paste q.1 q.2.1 q.2.2)
    (encPair encUnary (encPair eTape eTape)) eTape
    (fun q => (encPair encUnary (encPair eTape eTape) q).length)
    fun q => (encPair encUnary (encPair eTape eTape) q).length := by
  have hr := fst encUnary (encPair eTape eTape)
  have ho := tapeFields_inO.comp_linear (snd encUnary (encPair eTape eTape)).fst'
  have hi := tapeFields_inO.comp_linear (snd encUnary (encPair eTape eTape)).snd'
  have happ := (ComputableTidilyInDegree.listAppend eSym).inO_one
  have hl := happ.comp_linear (hi.snd'.fst'.prod ((dropU eSym).comp_linear (ho.snd'.fst'.prod hr)))
  have hr' := happ.comp_linear (hi.snd'.snd'.prod ((dropU eSym).comp_linear
    (ho.snd'.snd'.prod (ComputableTidilyInDegree.unary_succ.inO_one.comp_linear hr))))
  exact (((const (encMid := encInt) (0 : ℤ)).prod (hl.prod hr')).of_enc_eq (encOut := eTape)
    (g := fun q : ℕ × Tape × Tape => paste q.1 q.2.1 q.2.2) fun _ => rfl).mono 16
    (fun q => by omega) fun q => by omega

/-! ### Cutting and pasting all windows -/

/-- **Cutting windows** of radius `r`, in time linear in the encoded windows for each window. -/
theorem extract_inO :
    ComputableInO (fun p : ℕ × Win => extract p.1 p.2) (encPair encUnary eWin) eWin
      (fun p => (p.2.2.length + 1) * ((encPair encUnary eWin p).length + 1))
      (fun p => (p.2.2.length + 1) * ((encPair encUnary eWin p).length + 1)) := by
  have hw := snd encUnary eWin
  -- bridge for #862: tidy client of the plain `ComputableInO.mapWith`
  have hmap := (ComputableInO.mapWith (encP := encUnary) (enc := eTape) (encB := eTape)
    cut_inO.computableInO (fst encUnary eWin).computableInO hw.snd'.computableInO).tidy
  refine (((hw.fst'.prod hmap).of_enc_eq (encOut := eWin)
    (g := fun p : ℕ × Win => extract p.1 p.2) fun _ => rfl).mono 8 (fun p => ?_)
    fun p => ?_).computableInO
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
    generalize (encUnary r).length = R at *
    generalize (encList eTape ts).length = L at *
    generalize (eSym s).length = S at *
    nlinarith

/-- One round of pasting windows back: the remaining run windows, and the windows pasted so far. -/
private def restoreStep (r : ℕ) (s : List Tape × List Tape) (t : Tape) : List Tape × List Tape :=
  (s.1.tail, if s.1.isEmpty then s.2 else s.2 ++ [paste r t (s.1.headD default)])

private lemma foldl_restoreStep (r : ℕ) (outer rest acc : List Tape) :
    outer.foldl (restoreStep r) (rest, acc) =
      (rest.drop outer.length, acc ++ List.zipWith (paste r) outer rest) := by
  induction outer generalizing rest acc with
  | nil => simp
  | cons t outer ih =>
    rw [List.foldl_cons]
    cases rest with
    | nil => simp [restoreStep, ih]
    | cons b rest => simp [restoreStep, ih]

/-- A round of pasting windows back, in linear time. -/
private lemma restoreStep_inO : ComputableTidilyInO
    (fun q : (ℕ × List Tape × List Tape) × Tape => restoreStep q.1.1 q.1.2 q.2)
    (encPair (encPair encUnary (encPair (encList eTape) (encList eTape))) eTape)
    (encPair (encList eTape) (encList eTape))
    (fun q => (encPair (encPair encUnary (encPair (encList eTape) (encList eTape))) eTape q).length)
    fun q =>
      (encPair (encPair encUnary (encPair (encList eTape) (encList eTape))) eTape q).length := by
  have hq := fst (encPair encUnary (encPair (encList eTape) (encList eTape))) eTape
  have ht := snd (encPair encUnary (encPair (encList eTape) (encList eTape))) eTape
  have hrest := hq.snd'.fst'
  have hacc := hq.snd'.snd'
  have htail := (ComputableTidilyInDegree.listTail eTape).inO_one.comp_linear hrest
  have hempty := (ComputableTidilyInDegree.listIsEmpty eTape).inO_one.comp_linear hrest
  have hhead := (ComputableTidilyInDegree.listHeadD eTape default).inO_one.comp_linear hrest
  have hpaste := paste_inO.comp_linear (hq.fst'.prod (ht.prod hhead))
  have hsnoc := (ComputableTidilyInDegree.snoc eTape).inO_one.comp_linear (hacc.prod hpaste)
  refine ((htail.prod (hempty.ite hacc hsnoc)).of_enc_eq
    (g := fun q : (ℕ × List Tape × List Tape) × Tape => restoreStep q.1.1 q.1.2 q.2)
    fun _ => rfl).mono 16 (fun q => ?_) fun q => ?_ <;>
  · simp only [Function.comp_apply]
    split_ifs <;> omega

/-- **Pasting windows back**, in time linear in the encoded windows for each window. -/
theorem restore_inO :
    ComputableInO (fun p : ℕ × Win × Win => restore p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair eWin eWin)) eWin
      (fun p => (p.2.1.2.length + 1) * ((encPair encUnary (encPair eWin eWin) p).length + 1))
      (fun p => (p.2.1.2.length + 1) * ((encPair encUnary (encPair eWin eWin) p).length + 1)) := by
  have hr := fst encUnary (encPair eWin eWin)
  have ho := (snd encUnary (encPair eWin eWin)).fst'
  have hi := (snd encUnary (encPair eWin eWin)).snd'
  -- the states of the fold
  have hst (p : ℕ × Win × Win) (i : ℕ) :
      (encPair (encList eTape) (encList eTape) ((p.2.1.2.take i).foldl (restoreStep p.1)
        (p.2.2.2, []))).length ≤ 3 * (encPair encUnary (encPair eWin eWin) p).length := by
    obtain ⟨r, ⟨so, o⟩, ⟨si, w⟩⟩ := p
    rw [foldl_restoreStep]
    have h₁ := length_encList_drop_le eTape w (o.take i).length
    have h₂ := length_encList_zipWith_le (length_eTape_paste_le r) (o.take i) w
    have h₃ := length_encList_take_le eTape o i
    simp only [length_encPair, List.nil_append] at *
    omega
  have hfold := foldlWith (encL := encList eTape) (encB := encPair (encList eTape) (encList eTape))
    (list := fun p : ℕ × Win × Win => p.2.1.2) hr ho.snd' (hi.snd'.prod (const [])) restoreStep_inO
    (R := fun p => 16 * (encPair encUnary (encPair eWin eWin) p).length + 8)
    (Q := fun p => 16 * (encPair encUnary (encPair eWin eWin) p).length + 8)
    (B := fun p => 3 * (encPair encUnary (encPair eWin eWin) p).length)
    (fun p i hi => by
      have h₁ := hst p i
      have h₂ := length_le_encList_of_mem eTape (List.getElem_mem hi)
      obtain ⟨r, ⟨so, o⟩, ⟨si, w⟩⟩ := p
      simp only [length_encPair] at *
      omega)
    (fun p i hi => by
      have h₁ := hst p i
      have h₂ := length_le_encList_of_mem eTape (List.getElem_mem hi)
      obtain ⟨r, ⟨so, o⟩, ⟨si, w⟩⟩ := p
      simp only [length_encPair] at *
      omega)
    (fun p i _ => hst p i)
  refine (((hi.fst'.prod hfold.snd').of_enc_eq (encOut := eWin)
    (g := fun p : ℕ × Win × Win => restore p.1 p.2.1 p.2.2) fun ⟨r, o, i⟩ => ?_).mono 64
    (fun p => ?_) fun p => ?_).computableInO
  · simp only [restore, foldl_restoreStep, List.nil_append]
  all_goals
    obtain ⟨r, ⟨so, o⟩, ⟨si, w⟩⟩ := p
    have hN : (encPair encUnary (encPair eWin eWin) (r, (so, o), (si, w))).length =
        2 * (encUnary r).length + 1 + (2 * (2 * (eSym so).length + 1 +
          (encList eTape o).length) + 1 + (2 * (eSym si).length + 1 +
          (encList eTape w).length)) := by
      simp only [length_encPair]
    simp only [hN, length_encPair] at *
    generalize (encUnary r).length = R at *
    generalize (encList eTape o).length = L at *
    generalize (encList eTape w).length = M at *
    generalize (eSym so).length = S at *
    generalize (eSym si).length = S' at *
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
  (of_linear ((halfT false).computableTidilyInLinearTimeAndSpace fun n =>
    (run_halfT false n).1.symm)).computableInO

/-- Half a number of steps, rounded down, in unary, in linear time. -/
theorem half_inO :
    ComputableInO (· / 2) encUnary encUnary (fun n => (encUnary n).length)
      (fun n => (encUnary n).length) :=
  (of_linear ((halfT true).computableTidilyInLinearTimeAndSpace fun n =>
    (run_halfT true n).2.symm)).computableInO

/-! ### A windowed step -/

section TapeDegree

private lemma tapeFields_deg : ComputableTidilyInDegree (fun t : Tape => (t.head, t.left, t.right))
    eTape eTapeFields 1 1 :=
  ComputableTidilyInDegree.of_eq fun _ => rfl

@[local fun_prop]
private lemma tapeMk_deg : ComputableTidilyInDegree
    (fun p : ℤ × List (Option ℕ) × List (Option ℕ) => Tape.mk p.1 p.2.1 p.2.2) eTapeFields eTape
    1 1 :=
  ComputableTidilyInDegree.of_eq fun _ => rfl

@[local fun_prop]
private lemma tapeHead_deg : ComputableTidilyInDegree Tape.head eTape encInt 1 1 :=
  tapeFields_deg.fst'

@[local fun_prop]
private lemma tapeLeft_deg : ComputableTidilyInDegree Tape.left eTape (encList eSym) 1 1 :=
  tapeFields_deg.snd'.fst'

@[local fun_prop]
private lemma tapeRight_deg : ComputableTidilyInDegree Tape.right eTape (encList eSym) 1 1 :=
  tapeFields_deg.snd'.snd'

/-- The symbol under the head. -/
@[local fun_prop]
private lemma read_deg : ComputableTidilyInDegree Tape.read eTape eSym 1 1 := by
  unfold Tape.read
  fun_prop (disch := lia)

/-- A right move. -/
private lemma movePos_deg :
    ComputableTidilyInDegree (fun t : Tape => t.move .pos) eTape eTape 1 1 := by
  simp only [Tape.move]
  fun_prop (disch := lia)

/-- A left move. -/
private lemma moveNeg_deg :
    ComputableTidilyInDegree (fun t : Tape => t.move .neg) eTape eTape 1 1 := by
  simp only [Tape.move]
  fun_prop (disch := lia)

end TapeDegree

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
private lemma isEnd_inO : ComputableTidilyInO (fun c : Option ℕ => decide (c = some 0)) eSym
    encBool (fun c => ((eSym c).length + 1) ^ 2) fun c => (eSym c).length := by
  refine ((ComputableInO.eq eSym).tidy.comp ((of_linear (.of_eq fun _ => rfl) :
    ComputableTidilyInO (fun c : Option ℕ => c) eSym eSym _ _).prod
      (const (some 0)))).mono 8 (fun c => ?_) fun c => ?_ <;>
  · simp only [length_encPair, encOption_some, encUnary_apply, List.length_cons,
      List.length_replicate]
    nlinarith

/-- `Turing.MultiTapeTM.Universal.Windowed.inPos`, in quadratic time. -/
private lemma inPos_inO : ComputableTidilyInO inPos eSym encNat
    (fun c => ((eSym c).length + 1) ^ 2) fun c => (eSym c).length := by
  refine ((isEnd_inO.ite (const 0) (const 1)).of_enc_eq (g := inPos)
    fun c => by rw [inPos_eq]).mono 4 (fun c => ?_) fun c => ?_ <;>
  · have : (eSym c).length ≤ ((eSym c).length + 1) ^ 2 := by nlinarith
    split_ifs <;> omega

/-- `Turing.MultiTapeTM.Universal.Windowed.inSym`, in quadratic time. -/
private lemma inSym_inO : ComputableTidilyInO inSym eSym eSym
    (fun c => ((eSym c).length + 1) ^ 2) fun c => (eSym c).length := by
  have hsome := (ComputableTidilyInDegree.optionSome (enc₁ := encUnary) (enc := eSym)).inO_one
    |>.comp_linear (ComputableTidilyInDegree.unary_pred.inO_one.comp_linear
      (ComputableTidilyInDegree.getD (enc₁ := encUnary) (enc := eSym) 0).inO_one)
  refine ((isEnd_inO.ite (const none) ((ComputableTidilyInDegree.isSome encUnary).inO_one.ite
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
private lemma wFin_inO : ComputableTidilyInO wFin
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
  have hsucc := ComputableInO.natSucc.tidy
  have hc₁ := (ComputableInO.eq encNat).tidy.comp (hp'.prod (hsucc.comp hp))
  have hc₂ := (ComputableInO.eq encNat).tidy.comp ((hsucc.comp hp').prod hp)
  have hmv := hc₁.ite (movePos_deg.inO_one.comp_linear ht)
    (hc₂.ite (moveNeg_deg.inO_one.comp_linear ht) ht)
  have hlist := (ComputableTidilyInDegree.cons eTape).inO_one.comp_linear
    (hmv.prod hf.snd'.snd')
  refine (((hf.fst'.prod hlist).prod hy₂.snd').of_enc_eq (g := wFin) fun y => ?_).mono 64
    (fun y => ?_) fun y => ?_
  · simp only [wFin, moveIn_eq]
    rfl
  all_goals
    obtain ⟨⟨t, p⟩, ⟨s, p', ws⟩, o⟩ := y
    have h₁ := length_encNat_add_le p 1
    have h₂ := length_encNat_add_le p' 1
    simp only [Function.comp_apply, length_encPair, eCfg_apply] at *
    generalize (encNat (p + 1)).length = A at *
    generalize (encNat (p' + 1)).length = A' at *
    generalize (encNat p).length = P at *
    generalize (encNat p').length = P' at *
    generalize (eTape t).length = X at *
    generalize (eSym s).length = S at *
    generalize (encList eTape ws).length = L at *
    generalize (eSym o).length = O at *
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
  have hP : (P + 1) ^ 2 ≤ 4 := by nlinarith
  have h := Nat.mul_le_mul (Nat.mul_le_mul hA (show D + 1 ≤ N + 1 by omega))
    (show W + 1 ≤ 9 * (N + 1) by omega)
  have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
  nlinarith

/-- The arguments of the reassembly: the input window, its coded position and the result of the
step, in cubic time and linear space. -/
private lemma wArgs_inO : ComputableTidilyInO
    (fun x : Desc × Win => ((wHead x, inPos (wHead x).read),
      stepWith (wCtx x).1.1 (wCtx x).1.2 (wCtx x).2))
    (encPair eDesc eWin) (encPair (encPair eTape encNat) (encPair eCfg eSym))
    (fun x => ((encPair eDesc eWin x).length + 1) ^ 3) fun x => (encPair eDesc eWin x).length := by
  have hd := fst eDesc eWin
  have hw := snd eDesc eWin
  have hhead := (ComputableTidilyInDegree.listHeadD eTape default).inO_one.comp_linear hw.snd'
  have hread := read_deg.inO_one.comp_linear hhead
  have hpos := inPos_inO.comp hread
  have hsym := inSym_inO.comp hread
  have htail := (ComputableTidilyInDegree.listTail eTape).inO_one.comp_linear hw.snd'
  have hcfg := (hw.fst'.prod (hpos.prod htail)).of_enc_eq (encOut := eCfg)
    (g := fun x : Desc × Win => (⟨x.2.1, inPos (wHead x).read, x.2.2.tail⟩ : SCfg)) fun _ => rfl
  have hctx := ((hd.prod hcfg).prod hsym).of_enc_eq (encOut := eWCtx) (g := wCtx) fun _ => rfl
  -- bridge for #862: tidy client of the plain `stepWith_inO`
  have hstep := stepWith_inO.tidy.comp hctx
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
    have : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_pos _)
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
  have hempty := (ComputableTidilyInDegree.listIsEmpty eTape).inO_one.comp_linear hw.snd'
  refine (((hempty.ite (hw.prod (const none)) (wFin_inO.comp wArgs_inO)).of_enc_eq
    (g := fun x : Desc × Win => wstep x.1 x.2) fun x => by rw [wstep_eq]; rfl).mono
    (4 * (c + 2) ^ 2) (fun x => ?_) fun x => ?_).computableInO
  all_goals
    have h := hc x
    simp only [Function.comp_apply] at *
    generalize (encPair eDesc eWin x).length = N at *
    generalize (encPair (encPair eTape encNat) (encPair eCfg eSym) _).length = G at *
    have hG : G + 1 ≤ (c + 1) * (N + 1) := by nlinarith
    have hG2 := Nat.mul_le_mul hG hG
    have h₁ : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
    have h₂ : N + 1 ≤ (N + 1) ^ 3 := by nlinarith
    split_ifs <;> nlinarith

end Turing.MultiTapeTM.Universal.Windowed
