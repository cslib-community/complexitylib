/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists
import Complexity.Computability.Machines.Turing.MultiTape.Internal.OLoops
import Mathlib.Tactic.Linarith

/-!
# Walking along two lists

`Turing.MultiTapeTM.zipFold f p l r` walks along `l`, consuming `r` in step, and collects
`f p a b?` for each element `a` of `l` and the matching element `b?` of `r`, if any. The function
decides what happens at a missing partner and may drop an element, so that both zipping and
padding are instances.

A linear `f` gives a machine in time the length of `l` times the length of the input and in linear
space, provided that the results collected along the way are linear in the input. The machine
folds over `l`, keeping the rest of `r` and the results.

## Main definitions

* `Turing.MultiTapeTM.zipFold`: walking along two lists.

## Main results

* `Turing.MultiTapeTM.ComputableInO.zipFold`: the cost of walking along two lists.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {π α β γ : Type}

/-- Walk along `l`, consuming `r` in step, and collect `f p a b?` for each `a` in `l` and the
matching element `b?` of `r`. -/
def zipFold (f : π → α → Option β → Option γ) (p : π) : List α → List β → List γ
  | [], _ => []
  | a :: l, r => (f p a r.head?).toList ++ zipFold f p l r.tail

/-- A round of `Turing.MultiTapeTM.zipFold`: the rest of the second list and the results so far. -/
def zipFoldStep (f : π → α → Option β → Option γ) (p : π) (s : List β × List γ) (a : α) :
    List β × List γ :=
  (s.1.tail, s.2 ++ (f p a s.1.head?).toList)

theorem foldl_zipFoldStep (f : π → α → Option β → Option γ) (p : π) (l : List α) (r : List β)
    (acc : List γ) :
    l.foldl (zipFoldStep f p) (r, acc) = (r.drop l.length, acc ++ zipFold f p l r) := by
  induction l generalizing r acc with
  | nil => simp [zipFold]
  | cons a l ih =>
    simp [zipFoldStep, ih, zipFold, List.drop_tail]

namespace ComputableInO

variable {encP : π ↪ List Bool} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encC : γ ↪ List Bool} {f : π → α → Option β → Option γ}

/-- The next element of the second list. -/
private lemma head?_eq (l : List β) [Inhabited β] :
    l.head? = if l.isEmpty then none else some (l.headD default) := by
  cases l <;> rfl

/-- The results of a round, as a test on the result of `f`. -/
private lemma append_toList_eq [Inhabited γ] (o : Option γ) (acc : List γ) :
    acc ++ o.toList = if o.isSome then acc ++ [o.getD default] else acc := by
  cases o <;> simp

private lemma length_head?_le (l : List β) :
    (encOption encB l.head?).length ≤ (encList encB l).length + 1 := by
  cases l with
  | nil => simp
  | cons b l =>
    have := length_le_encList_of_mem encB (List.mem_cons_self (a := b) (l := l))
    simp only [List.head?_cons, encOption_some, List.length_cons]
    omega

private lemma length_getD_le [Inhabited γ] (o : Option γ) :
    (encC (o.getD default)).length ≤ (encOption encC o).length + (encC default).length := by
  cases o with
  | none => simp
  | some c => simp; omega

/-- The next element of the second list, in linear time. -/
private lemma head?_inO [Inhabited β] : ComputableInO (fun l : List β => l.head?) (encList encB)
    (encOption encB) (fun l => (2 * (encB default).length + 8) * ((encList encB l).length + 1))
    fun l => (2 * (encB default).length + 8) * ((encList encB l).length + 1) := by
  have hsome := (ComputableInDegree.optionSome (enc₁ := encB) (enc := encOption encB)).inO_one
  have h : ComputableInO (fun l : List β => if l.isEmpty then none else some (l.headD default))
      (encList encB) (encOption encB) _ _ :=
    (isEmpty' (hl := id')).ite (const none) (hsome.comp' (headD' default))
  refine (h.of_enc_eq fun l => by rw [head?_eq]).mono 4 (fun l => ?_) fun l => ?_
  all_goals
    have hd : (encB (l.headD default)).length ≤
        (encList encB l).length + (encB default).length := by
      cases l with
      | nil => simp
      | cons b l =>
        have := length_le_encList_of_mem encB (List.mem_cons_self (a := b) (l := l))
        simp only [List.headD_cons]
        omega
    have hmul : (encList encB l).length + (encB default).length + 1 ≤
        (2 * (encB default).length + 8) * ((encList encB l).length + 1) := by nlinarith
    split_ifs <;> omega

/-- A round of `Turing.MultiTapeTM.zipFold`, in time and space linear in the rest of the second
list, the results so far and the element, up to the constants of `f`. -/
private lemma zipFoldStep_inO [Inhabited β] [Inhabited γ]
    (hf : ComputableInO (fun q : π × α × Option β => f q.1 q.2.1 q.2.2)
      (encPair encP (encPair encA (encOption encB))) (encOption encC)
      (fun q => (encPair encP (encPair encA (encOption encB)) q).length)
      fun q => (encPair encP (encPair encA (encOption encB)) q).length) :
    ∃ K, ComputableInO (fun q : (π × List β × List γ) × α => zipFoldStep f q.1.1 q.1.2 q.2)
      (encPair (encPair encP (encPair (encList encB) (encList encC))) encA)
      (encPair (encList encB) (encList encC))
      (fun q => K * ((encPair (encPair encP (encPair (encList encB) (encList encC))) encA q).length
        + 1))
      fun q => K * ((encPair (encPair encP (encPair (encList encB) (encList encC))) encA q).length
        + 1) := by
  obtain ⟨c, hc⟩ := hf.length_le
  have hq := fst (encPair encP (encPair (encList encB) (encList encC))) encA
  have ha := snd (encPair encP (encPair (encList encB) (encList encC))) encA
  have hrest := hq.snd'.fst'
  have hacc := hq.snd'.snd'
  have ho := hf.comp' (hq.fst'.prod (ha.prod ((head?_inO (encB := encB)).comp' hrest)))
  have hsnoc := (snoc' (enc := encC)).comp' (hacc.prod (optionGetD default ho))
  have h := ((tail' (enc := encB)).comp' hrest).prod ((optionIsSome ho).ite hsnoc hacc)
  obtain ⟨d, hd⟩ : ∃ d, d = 2 * (encB default).length + 8 + (encC default).length := ⟨_, rfl⟩
  refine ⟨4096 * (d + 1) * (c + 1), (h.of_enc_eq fun q => ?_).mono 1 (fun q => ?_) fun q => ?_⟩
  · simp only [zipFoldStep, append_toList_eq]
  all_goals
    obtain ⟨⟨p, r, acc⟩, a⟩ := q
    dsimp only
    generalize hX : (encPair (encPair encP (encPair (encList encB) (encList encC))) encA
      ((p, r, acc), a)).length = X
    have hsize : 2 * (encP p).length + 2 * (encList encB r).length + (encList encC acc).length +
        (encA a).length ≤ 2 * X := by
      rw [← hX]; simp only [length_encPair]; omega
    have hhead := length_head?_le (encB := encB) r
    have htriple : (encPair encP (encPair encA (encOption encB)) (p, a, r.head?)).length + 1 ≤
        8 * (X + 1) := by
      simp only [length_encPair] at *; omega
    have hout := hc (p, a, r.head?)
    have hout' := Nat.le_trans hout (Nat.mul_le_mul_left c htriple)
    dsimp only at hout hout'
    have hget := length_getD_le (encC := encC) (f p a r.head?)
    have hscale : (2 * (encB default).length + 8) * ((encList encB r).length + 1) ≤ d * (X + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hZ₁ : X + 1 ≤ (d + 1) * (c + 1) * (X + 1) := by nlinarith [Nat.zero_le (d * c)]
    have hZ₂ : d * (X + 1) ≤ (d + 1) * (c + 1) * (X + 1) := by nlinarith [Nat.zero_le (d * c)]
    have hZ₃ : c * (8 * (X + 1)) ≤ 8 * ((d + 1) * (c + 1) * (X + 1)) := by
      nlinarith [Nat.zero_le (d * c * (X + 1)), Nat.zero_le (d * (X + 1))]
    have hZ₄ : d ≤ (d + 1) * (c + 1) * (X + 1) :=
      (Nat.le_mul_of_pos_right d (Nat.succ_pos X)).trans hZ₂
    have hK : 4096 * (d + 1) * (c + 1) * (X + 1) = 4096 * ((d + 1) * (c + 1) * (X + 1)) := by ring
    generalize (d + 1) * (c + 1) * (X + 1) = Z at *
    simp only [length_encPair, Nat.one_mul, hK] at *
    split_ifs <;> omega

/-- **Walking along two lists.** For a linear `f`, whose results collected along the way are
linear in the input, walking along two lists takes time the length of the first list times the
length of the input, and linear space. -/
theorem zipFold [Inhabited β] [Inhabited γ]
    (hf : ComputableInO (fun q : π × α × Option β => f q.1 q.2.1 q.2.2)
      (encPair encP (encPair encA (encOption encB))) (encOption encC)
      (fun q => (encPair encP (encPair encA (encOption encB)) q).length)
      fun q => (encPair encP (encPair encA (encOption encB)) q).length)
    (k : ℕ) (hout : ∀ (q : π × List α × List β) (i : ℕ),
      (encList encC (Turing.MultiTapeTM.zipFold f q.1 (q.2.1.take i) q.2.2)).length ≤
        k * ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1)) :
    ComputableInO (fun q : π × List α × List β => Turing.MultiTapeTM.zipFold f q.1 q.2.1 q.2.2)
      (encPair encP (encPair (encList encA) (encList encB))) (encList encC)
      (fun q => (q.2.1.length + 1) *
        ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1))
      fun q => (encPair encP (encPair (encList encA) (encList encB)) q).length := by
  obtain ⟨K, hstep⟩ := zipFoldStep_inO hf
  have hq := snd encP (encPair (encList encA) (encList encB))
  have hst (q : π × List α × List β) (i : ℕ) :
      (encPair (encList encB) (encList encC) ((q.2.1.take i).foldl (zipFoldStep f q.1)
        (q.2.2, []))).length ≤
        (2 + k) * ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1) := by
    obtain ⟨p, l, r⟩ := q
    have h₁ := hout (p, l, r) i
    have h₂ := (SizedListEncoding.length_drop_le (encA := encB) (encL := encList encB) r
      (l.take i).length)
    rw [foldl_zipFoldStep, List.nil_append]
    simp only [Nat.add_mul, length_encPair] at *
    omega
  have hround (q : π × List α × List β) (i : ℕ) (hi : i < q.2.1.length) :
      K * ((encPair (encPair encP (encPair (encList encB) (encList encC))) encA)
        ((q.1, (q.2.1.take i).foldl (zipFoldStep f q.1) (q.2.2, [])), q.2.1[i])).length.succ ≤
      K * ((8 + 2 * k) *
        ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1)) := by
    refine Nat.mul_le_mul_left K ?_
    have h₁ := hst q i
    have h₂ := length_le_encList_of_mem encA (List.getElem_mem hi)
    obtain ⟨p, l, r⟩ := q
    simp only [Nat.add_mul, Nat.mul_assoc, length_encPair, Nat.succ_eq_add_one] at *
    omega
  have hfold := foldlWith (encL := encList encA)
    (encB := encPair (encList encB) (encList encC)) (list := fun q : π × List α × List β => q.2.1)
    (fst encP (encPair (encList encA) (encList encB))) hq.fst'
    (hq.snd'.prod (const [])) hstep
    (R := fun q => K * ((8 + 2 * k) *
      ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1)))
    (Q := fun q => K * ((8 + 2 * k) *
      ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1)))
    (B := fun q => (2 + k) *
      ((encPair encP (encPair (encList encA) (encList encB)) q).length + 1))
    (fun q i hi => hround q i hi) (fun q i hi => hround q i hi) (fun q i _ => hst q i)
  obtain ⟨C, hC⟩ : ∃ C, C = K * (8 + 2 * k) + (2 + k) + 2 := ⟨_, rfl⟩
  refine (((snd (encList encB) (encList encC)).comp_linear hfold).mono (C + 8) (fun q => ?_)
    fun q => ?_).of_enc_eq fun q => ?_
  on_goal 3 => simp [foldl_zipFoldStep]
  all_goals
    have hparts : (encP q.1).length + (encList encA q.2.1).length ≤
        (encPair encP (encPair (encList encA) (encList encB)) q).length := by
      simp only [length_encPair]; omega
    generalize (encPair encP (encPair (encList encA) (encList encB)) q).length = X at *
    have hsplit : C * (X + 1) =
        K * ((8 + 2 * k) * (X + 1)) + (2 + k) * (X + 1) + 2 * (X + 1) := by
      rw [hC]; ring
  · have hin := Nat.mul_le_mul_left (q.2.1.length + 1)
      (show K * ((8 + 2 * k) * (X + 1)) + (2 + k) * (X + 1) + (encP q.1).length +
        (encList encA q.2.1).length ≤ C * (X + 1) by omega)
    have hcomm : (q.2.1.length + 1) * (C * (X + 1)) = C * ((q.2.1.length + 1) * (X + 1)) :=
      Nat.mul_left_comm ..
    have hU : X + 1 ≤ (q.2.1.length + 1) * (X + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    have hexp : (C + 8) * ((q.2.1.length + 1) * (X + 1) + 1) =
        C * ((q.2.1.length + 1) * (X + 1)) + 8 * ((q.2.1.length + 1) * (X + 1)) + C + 8 := by ring
    omega
  · have hexp : (C + 8) * (X + 1) = C * (X + 1) + 8 * (X + 1) := by ring
    omega

end ComputableInO

end Turing.MultiTapeTM
