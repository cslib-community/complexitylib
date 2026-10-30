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
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryPrimitives
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
  (ComputableTidilyInDegree.dropUnaryLin enc).inO_one

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
  have hmap := mapWith (encP := encUnary) (enc := eTape) (encB := eTape) cut_inO
    (fst encUnary eWin) hw.snd'
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

end Turing.MultiTapeTM.Universal.Windowed
