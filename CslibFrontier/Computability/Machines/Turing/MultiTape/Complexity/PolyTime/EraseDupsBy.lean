/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Foundations.Data.List.EraseDupsBy

/-!
# Erasing duplicates in polynomial time

`List.eraseDupsBy r l` keeps each entry of `l` that is related by `r` to no entry kept before it.
It is a left fold that appends at most one entry at a time (`List.eraseDupsBy_eq_foldl`), so a
polynomial-time comparison, which may capture the original input, makes it polynomial-time
(`Turing.MultiTapeTM.ComputableInPolyTime.eraseDupsByWithInput`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.eraseDupsByWithInput`: erasing duplicates of a
  computed framed list with a computed comparison.
* `Turing.MultiTapeTM.ComputableInPolyTime.decide_nodup`,
  `Turing.MultiTapeTM.ComputableInPolyTime.decide_nodup_bits`: deciding `List.Nodup` on a
  computed framed list (and its `fun_prop` specialization to bit strings).
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Erase the entries of a computed framed list related by `r x` to an earlier kept entry. Each
step of the fold appends at most one entry of the list, so the accumulator stays polynomially
bounded. -/
@[fun_prop]
theorem eraseDupsByWithInput {γ α : Type} {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {list : γ → List α} {r : γ → α → α → Bool}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hr : ComputableInPolyTime (fun p : (γ × α) × α => r p.1.1 p.1.2 p.2)
      (encPair (encPair encIn encA) encA) encBool) :
    ComputableInPolyTime (fun x => (list x).eraseDupsBy (r x)) encIn (encList encA) := by
  have hstep : ComputableInPolyTime
      (fun q : (γ × List α) × α => if q.1.2.any (r q.1.1 q.2) then q.1.2 else q.1.2 ++ [q.2])
      (encPair (encPair encIn (encList encA)) encA) (encList encA) := by
    have htest : ComputableInPolyTime
        (fun q : ((γ × List α) × α) × α => r q.1.1.1 q.1.2 q.2)
        (encPair (encPair (encPair encIn (encList encA)) encA) encA) encBool :=
      hr.comp (((fst _ _).fst'.fst'.prod (fst _ _).snd').prod (snd _ _))
    exact ite (anyWithInput (fst _ _).snd' htest) (fst _ _).snd'
      (listAppend' (fst _ _).snd' (cons' (snd _ _) (const [])))
  have hfold := foldlWithInput_of_bounded_growth (encIn := encIn) (encA := encA)
    (encB := encList encA) (list := list) (init := fun _ => [])
    (step := fun x kept a => if kept.any (r x a) then kept else kept ++ [a])
    (const _) ⟨hlist, hstep, inferInstance, inferInstance⟩
    (growth := fun x => 2 * (encList encA (list x)).length + 1)
    ⟨((PolyBounded.const 2).mul hlist.polyBounded_length).add (.const 1),
      fun x kept a ha => by
        have := SizedListEncoding.length_elem_le (encA := encA) (encL := encList encA) _ a ha
        split
        · omega
        · simp only [encList_append, encList_cons, encList_nil, List.append_nil,
            List.length_append, length_frame]
          omega⟩
  simpa only [← List.eraseDupsBy_eq_foldl] using hfold

private theorem eraseDupsBy_decide_eq_self {α : Type} [DecidableEq α] {l : List α} :
    l.eraseDupsBy (fun a b => decide (a = b)) = l ↔ l.Nodup := by
  refine ⟨fun h => h ▸ List.nodup_eraseDupsBy_eq l, fun h => ?_⟩
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.nodup_cons] at h
    rw [List.eraseDupsBy_cons, List.filter_eq_self.2 (fun b hb => by
      rw [decide_eq_true_eq, decide_eq_false_iff_not]
      rintro rfl
      exact h.1 hb), ih h.2]

/-- Decide whether a computed framed list has no duplicate entries by comparing it with the result
of erasing duplicates by equality (`eraseDupsByWithInput`). -/
theorem decide_nodup {γ α : Type} [DecidableEq α] {encIn : γ ↪ List Bool} {encA : α ↪ List Bool}
    {list : γ → List α} (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => decide (list x).Nodup) encIn encBool := by
  have herase : ComputableInPolyTime
      (fun x => (list x).eraseDupsBy fun a b => decide (a = b)) encIn (encList encA) :=
    eraseDupsByWithInput hlist (decide_eq' (fst _ _).snd' (snd _ _))
  exact (herase.decide_eq' hlist).of_enc_eq fun x => by
    simp only [encBool_apply, eraseDupsBy_decide_eq_self]

/-- Decide whether a computed framed list of bit strings has no duplicate entries. Fixing the
element encoding to `encBits` avoids an ambiguous `List Bool` encoding metavariable during
`fun_prop` search. -/
@[fun_prop]
theorem decide_nodup_bits {γ : Type} {encIn : γ ↪ List Bool} {list : γ → List (List Bool)}
    (hlist : ComputableInPolyTime list encIn (encList encBits)) :
    ComputableInPolyTime (fun x => decide (list x).Nodup) encIn encBool :=
  decide_nodup hlist

end Turing.MultiTapeTM.ComputableInPolyTime
