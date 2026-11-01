/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Universal.WindowedBound
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Reverse
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LinearSpaceArith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cost of the initial windows

From the input of the universal function — a description `d`, an input `x` and a number of steps
`t` in binary — the first problem of the windowed simulation is the description, `t` in unary and
the windows of radius `t` of the initial configuration. It is computable in time
`O(N + (D + 1) ^ 3 + (t + 1) * (L + 1))` for the encoded input length `N`, the length `D` of the
description and the length `L` of `t` in binary: `t` is converted to unary by doubling, the input
symbols are recoded by a finite-state rewrite in linear time, and the input window is cut with a
linear-time take.

The computation goes through the intermediate value `(d, t, x')` with `t` in unary and the coded
input cells `x' = x.map fun a => some (a + 1)`:

* `t` is converted by a left fold of `u ↦ 2 * u + b` over the binary digits of `t`, most
  significant first; each round is linear in the unary state, which is at most `t`.
* In `encList encUnary x`, the element `a` is `(true true)^a false`; in the encoding of `x'` it is
  `(true true)^(a + 2) false`. The rewrite `true ↦ true`, `false ↦ true false`, applied four times,
  maps the one to the other, and every application is a finite-state transducer.
* The input window keeps the first `t + 1` coded cells; the blank work windows are built by
  `ComputableTidilyInDegree.replicate`, within time cubic in the number of work tapes.

## Main results

* `Turing.MultiTapeTM.Universal.Windowed.initProb_inO`: the first problem.
-/

public section

namespace Turing.MultiTapeTM.Universal.Windowed

open ComputableTidilyInO

/-! ### The initial windows -/

/-- The windows of radius `t` of the initial configuration. -/
private lemma extract_initWin (d : Desc) (x : List ℕ) (t : ℕ) :
    extract t (initWin d x) = (some d.q₀,
      ⟨0, [some 0].take t, (x.map fun a => some (a + 1)).take (t + 1)⟩ ::
        List.replicate d.tapes ⟨0, [], []⟩) := by
  simp [extract, initWin, cut, List.map_replicate]

/-- Taking the first `n` elements of a list, with `n` in unary, in linear time. All uses go through
this wrapper, so that only it depends on the form of the take primitive. -/
private lemma takeU {α : Type} (enc : α ↪ List Bool) :
    ComputableTidilyInO (fun p : List α × ℕ => p.1.take p.2) (encPair (encList enc) encUnary)
      (encList enc) (fun p => (encPair (encList enc) encUnary p).length)
      fun p => (encPair (encList enc) encUnary p).length :=
  (ComputableInDegree.takeUnary enc).inO_one.tidy

/-! ### From binary to unary by doubling -/

/-- A doubling round of the conversion from binary to unary: `u ↦ 2 * u + b`. -/
private def dbl (u : ℕ) (b : Bool) : ℕ := u + u + cond b 1 0

private lemma foldr_dbl_bits (n : ℕ) : n.bits.foldr (fun b u => dbl u b) 0 = n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit _ _ hn, List.foldr_cons, ih, Nat.bit_val]
    cases b <;>
      simp only [dbl, Bool.cond_true, Bool.cond_false, Bool.toNat_true, Bool.toNat_false] <;> omega

/-- Doubling over the binary digits, most significant first, gives the number. -/
private lemma foldl_dbl_bits (n : ℕ) : (encNat n).reverse.foldl dbl 0 = n := by
  rw [List.foldl_reverse, encNat_apply, foldr_dbl_bits]

private lemma le_foldl_dbl (l : List Bool) (a : ℕ) : a ≤ l.foldl dbl a := by
  induction l generalizing a with
  | nil => exact le_rfl
  | cons b l ih => exact (show a ≤ dbl a b by simp only [dbl]; omega).trans (ih _)

/-- The states of the doubling fold are at most the number. -/
private lemma foldl_dbl_take_le (n i : ℕ) : ((encNat n).reverse.take i).foldl dbl 0 ≤ n :=
  calc _ ≤ ((encNat n).reverse.drop i).foldl dbl (((encNat n).reverse.take i).foldl dbl 0) :=
        le_foldl_dbl _ _
    _ = n := by rw [← List.foldl_append, List.take_append_drop, foldl_dbl_bits]

/-- A doubling round, in linear time. -/
private lemma dbl_deg : ComputableTidilyInDegree (fun p : ℕ × Bool => dbl p.1 p.2)
    (encPair encUnary encBool) encUnary 1 1 := by
  have h₁ := ComputableTidilyInDegree.fst encUnary encBool
  have h₂ := (ComputableTidilyInDegree.of_finite (encIn := encBool) (encMid := encUnary)
    fun b : Bool => cond b 1 0).comp (ComputableTidilyInDegree.snd encUnary encBool)
  have hdouble := h₁.append h₁ (encOut := encUnary) (g := fun p : ℕ × Bool => p.1 + p.1)
    fun p => by simp only [encUnary_apply, List.replicate_add]
  exact (hdouble.append h₂ fun p => by
    simp only [dbl, encUnary_apply, List.replicate_add, Function.comp_apply]).mono

/-- **From binary to unary**, in time `O((t + 1) * (L + 1))` for `t` with `L` binary digits. -/
private lemma toUnary_inO : ComputableTidilyInO (fun t : ℕ => t) encNat encUnary
    (fun t => (t + 1) * ((encNat t).length + 1)) fun t => (t + 1) * ((encNat t).length + 1) := by
  have hrev : ComputableTidilyInO (fun t : ℕ => (encNat t).reverse) encNat encBits
      (fun t => (encNat t).length) fun t => (encNat t).length :=
    of_linear ⟨4, (computableTidilyInTimeAndSpace_reverse fun _ => rfl).mono
      (fun _ => by omega) fun _ => Nat.zero_le _⟩
  refine ((foldl (encA := encBool) (encL := encBits) (list := fun t : ℕ => (encNat t).reverse)
    (init := fun _ => 0) (step := dbl) hrev (const 0) dbl_deg.inO_one
    (R := fun t => 2 * t + 2) (Q := fun t => 2 * t + 2) (B := fun t => t)
    (fun t i _ => ?_) (fun t i _ => ?_) (fun t i _ => ?_)).mono 8 (fun t => ?_)
      fun t => ?_).of_enc_eq fun t => ?_
  · have := foldl_dbl_take_le t i
    simp only [length_encPair, encUnary_apply, encBool_apply, List.length_replicate,
      List.length_singleton]
    omega
  · have := foldl_dbl_take_le t i
    simp only [length_encPair, encUnary_apply, encBool_apply, List.length_replicate,
      List.length_singleton]
    omega
  · have := foldl_dbl_take_le t i
    simp only [encUnary_apply, List.length_replicate]
    omega
  · have := length_encNat_le_self t
    simp only [encBits_apply, List.length_reverse]
    nlinarith
  · have := length_encNat_le_self t
    simp only [encBits_apply, List.length_reverse]
    nlinarith
  · rw [foldl_dbl_bits]

/-! ### Recoding the input symbols -/

/-- The rewrite `true ↦ true`, `false ↦ true false`. -/
private def ins (w : List Bool) : List Bool :=
  w.flatMap fun b => if b then [true] else [true, false]

/-- The rewrite `ins` as a finite-state transducer. -/
private def insT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), if b then [true] else [true, false])
  final _ := []
  length_step_le _ b := by cases b <;> simp
  length_final_le _ := by simp

private lemma insT_run (w : List Bool) : insT.run () w = ins w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (if b then [true] else [true, false]) ++ insT.run () w = _
    rw [ih]
    rfl

private lemma ins_append (u v : List Bool) : ins (u ++ v) = ins u ++ ins v :=
  List.flatMap_append

private lemma ins_replicate (n : ℕ) :
    ins (List.replicate n true ++ [false]) = List.replicate (n + 1) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append]
    change [true] ++ ins _ = _
    rw [ih]
    rfl

private lemma frame_replicate_true (n : ℕ) :
    frame (List.replicate n true) = List.replicate (2 * n) true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, frame_cons, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    rfl

/-- Four rewrites turn the encoded input into the encoded coded input cells. -/
private lemma ins_four (x : List ℕ) : ins (ins (ins (ins (encList encUnary x)))) =
    encList eSym (x.map fun a => some (a + 1)) := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    have hsym : eSym (some (a + 1)) = List.replicate (a + 1 + 1) true := rfl
    rw [encList_cons, List.map_cons, encList_cons, ins_append, ins_append, ins_append, ins_append,
      ih, hsym, encUnary_apply, frame_replicate_true, frame_replicate_true, ins_replicate,
      ins_replicate, ins_replicate, ins_replicate, show 2 * (a + 1 + 1) = 2 * a + 1 + 1 + 1 + 1 by
        omega]

private lemma length_encList_recode (x : List ℕ) :
    (encList eSym (x.map fun a => some (a + 1))).length =
      (encList encUnary x).length + 4 * x.length := by
  rw [← ins_four]
  induction x with
  | nil => rfl
  | cons a x ih =>
    rw [encList_cons, ins_append, ins_append, ins_append, ins_append, List.length_append,
      List.length_append, ih, encUnary_apply, frame_replicate_true, ins_replicate, ins_replicate,
      ins_replicate, ins_replicate]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega

/-- **Recoding the input symbols**, in linear time. -/
private lemma recode_inO : ComputableTidilyInO (fun x : List ℕ => x.map fun a => some (a + 1))
    (encList encUnary) (encList eSym) (fun x => (encList encUnary x).length)
    fun x => (encList encUnary x).length := by
  have hins : ComputableTidilyInDegree ins encBits encBits 1 1 :=
    .of_linear (insT.computableTidilyInLinearTimeAndSpace fun w => (insT_run w).symm)
  have h₁ : ComputableTidilyInDegree (fun x : List ℕ => ins (encList encUnary x))
      (encList encUnary) encBits 1 1 :=
    .of_linear (insT.computableTidilyInLinearTimeAndSpace fun x => (insT_run _).symm)
  exact ((hins.comp (hins.comp (hins.comp h₁))).mono (d' := 1) (e' := 1)).inO_one.of_enc_eq
    fun x => (ins_four x).symm

/-! ### The intermediate value -/

/-- The intermediate value: the description, `t` in unary and the coded input cells. -/
private abbrev eMid : Desc × ℕ × List (Option ℕ) ↪ List Bool :=
  encPair eDesc (encPair encUnary (encList eSym))

/-- The intermediate value, in time linear in the encoded input plus `O((t + 1) * (L + 1))`. -/
private lemma mid_inO : ComputableTidilyInO
    (fun i : Desc × List ℕ × ℕ => (i.1, i.2.2, i.2.1.map fun a => some (a + 1))) eIn eMid
    (fun i => (eIn i).length + (i.2.2 + 1) * ((encNat i.2.2).length + 1))
    fun i => (eIn i).length + (i.2.2 + 1) * ((encNat i.2.2).length + 1) := by
  have hd := fst eDesc (encPair (encList encUnary) encNat)
  have hx := (snd eDesc (encPair (encList encUnary) encNat)).fst'
  have ht := (snd eDesc (encPair (encList encUnary) encNat)).snd'
  refine (hd.prod ((toUnary_inO.comp ht).prod (recode_inO.comp_linear hx))).mono 4
    (fun i => ?_) fun i => ?_
  all_goals
    have h := length_le_encPair_left (encList encUnary) encNat i.2
    simp only [length_encPair] at *
    omega

/-- The first problem from the intermediate value, in time linear in its encoding plus cubic in the
length of the description. -/
private lemma fin_inO : ComputableTidilyInO (fun m : Desc × ℕ × List (Option ℕ) =>
      ((m.1, m.2.1, (some m.1.q₀, ⟨0, [some 0].take m.2.1, m.2.2.take (m.2.1 + 1)⟩ ::
        List.replicate m.1.tapes ⟨0, [], []⟩)) : Prob))
    eMid eProb (fun m => (eMid m).length + (descLen m.1 + 1) ^ 3)
    fun m => (eMid m).length + (descLen m.1 + 1) ^ 3 := by
  have pd := fst eDesc (encPair encUnary (encList eSym))
  have pt := (snd eDesc (encPair encUnary (encList eSym))).fst'
  have pxs := (snd eDesc (encPair encUnary (encList eSym))).snd'
  have hf : ComputableTidilyInO (fun d : Desc => (d.tapes, d.q₀, d.table)) eDesc
      (encPair encUnary (encPair encUnary (encList (encPair eKey eAct))))
      (fun d => (eDesc d).length) fun d => (eDesc d).length :=
    of_linear (.of_eq fun _ => rfl)
  have hq := ((ComputableTidilyInDegree.optionSome (enc₁ := encUnary) (enc := eSym)).inO_one
    |>.comp_linear hf.snd'.fst').comp_linear pd
  have hz : ComputableTidilyInO (fun n : ℕ => decide (n = 0)) encUnary encBool
      (fun n => (encUnary n).length) fun n => (encUnary n).length :=
    of_linear (.of_isEmpty fun n => by cases n <;> rfl)
  have hl := ite (hz.comp_linear pt) (const (encIn := eMid) (encMid := encList eSym) [])
    (const [some 0])
  have hs : ComputableTidilyInO (fun n : ℕ => n + 1) encUnary encUnary
      (fun n => (encUnary n).length) fun n => (encUnary n).length :=
    of_linear (.of_cons_true fun n => by simp only [encUnary_apply, List.replicate_succ])
  have hr := (takeU eSym).comp_linear (pxs.prod (hs.comp_linear pt))
  have htape := ((const (encIn := eMid) (encMid := encInt) (0 : ℤ)).prod (hl.prod hr)).of_enc_eq
    (encOut := eTape) (g := fun m : Desc × ℕ × List (Option ℕ) =>
      (⟨0, if decide (m.2.1 = 0) then [] else [some 0], m.2.2.take (m.2.1 + 1)⟩ : Tape))
    fun m => rfl
  have hb := (ComputableTidilyInDegree.replicate eTape).inO.comp
    ((hf.fst'.comp_linear pd).prod (const (encMid := eTape) (⟨0, [], []⟩ : Tape)))
  have hw := (htape.prod hb).of_enc_eq (encOut := encList eTape)
    (g := fun m : Desc × ℕ × List (Option ℕ) =>
      (⟨0, if decide (m.2.1 = 0) then [] else [some 0], m.2.2.take (m.2.1 + 1)⟩ : Tape) ::
        List.replicate m.1.tapes ⟨0, [], []⟩)
    fun m => rfl
  refine (((pd.prod (pt.prod (hq.prod hw))).mono 512 (fun m => ?_) fun m => ?_).of_enc_eq
    fun m => ?_)
  rotate_left 2
  · obtain ⟨d, t, xs⟩ := m
    have h : [some 0].take t = if decide (t = 0) = true then [] else [some 0] := by
      cases t <;> simp
    dsimp only
    rw [h]
    rfl
  all_goals
    have htapes : m.1.tapes ≤ descLen m.1 := by
      simp only [descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hcube : ((encPair encUnary eTape (m.1.tapes, (⟨0, [], []⟩ : Tape))).length + 1) ^ 3 ≤
        216 * (descLen m.1 + 1) ^ 3 := by
      have hk : (eTape (⟨0, [], []⟩ : Tape)).length = 4 := rfl
      rw [length_encPair, hk, encUnary_apply, List.length_replicate]
      calc _ ≤ (6 * (descLen m.1 + 1)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
        _ = _ := by ring
    clear pd pt pxs hf hq hz hl hs hr htape hb hw
    have he : (eMid m).length = (encPair eDesc (encPair encUnary (encList eSym)) m).length := rfl
    simp only [Function.comp_apply]
    split_ifs <;> omega

/-- **The first problem of the windowed simulation**, in time linear in the encoded input, cubic in
the length of the description and `O((t + 1) * (L + 1))` for `t` steps written with `L` binary
digits. -/
theorem initProb_inO :
    ComputableInO (fun i : Desc × List ℕ × ℕ => ((i.1, i.2.2, extract i.2.2 (initWin i.1 i.2.1)) :
        Prob)) eIn eProb
      (fun i => (eIn i).length + (descLen i.1 + 1) ^ 3 + (i.2.2 + 1) * ((encNat i.2.2).length + 1))
      (fun i => (eIn i).length + (descLen i.1 + 1) ^ 3 +
        (i.2.2 + 1) * ((encNat i.2.2).length + 1)) := by
  refine (((fin_inO.comp mid_inO).mono 8 (fun i => ?_) fun i => ?_).of_enc_eq
    fun i => ?_).computableInO
  rotate_left 2
  · rw [extract_initWin]
    rfl
  all_goals
    have h₁ := length_encList_recode i.2.1
    have h₂ := length_le_length_encList encUnary i.2.1
    have h₃ : i.2.2 ≤ (i.2.2 + 1) * ((encNat i.2.2).length + 1) := by nlinarith
    simp only [length_encPair, encUnary_apply, List.length_replicate] at *
    omega

end Turing.MultiTapeTM.Universal.Windowed
