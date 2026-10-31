/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Foundations.Data.List.EraseDupsBy

/-!
# Erasing duplicates in polynomial time

`List.eraseDupsBy r l` keeps each entry of `l` that is related by `r` to no entry kept before it.
It is a left fold that appends at most one entry at a time (`List.eraseDupsBy_eq_foldl`), so a
polynomial-time comparison, which may capture the original input, makes it polynomial-time
(`Turing.MultiTapeTM.ComputableInPolyTime.eraseDupsByWithInput`).

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.eraseDupsByWithInput`: erasing duplicates of a
  computed framed list with a computed comparison.
-/

@[expose] public section

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

end Turing.MultiTapeTM.ComputableInPolyTime
