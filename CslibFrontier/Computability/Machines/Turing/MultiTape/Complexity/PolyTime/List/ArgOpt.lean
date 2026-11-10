/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import Mathlib.Data.List.MinMax

/-!
# Polynomial-time attained extrema of an encoded list

Use Mathlib's actual first-tie `List.argmax` / `List.argmin` folds. Each intermediate
accumulator is absent or an original list member, so its complete encoded length, including
its option tag, is bounded by the input length plus one. No score or candidate bound is advice.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.argmax`: charge comparison, retained candidates
  and output.
* `Turing.MultiTapeTM.ComputableInPolyTime.argmin`: the same machine rule with the order reversed.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type} [Preorder β] [DecidableLT β]
  {encA : α ↪ List Bool} {encB : β ↪ List Bool} {score : α → β}

/-- The actual first-tie maximum scan is polynomial-time, including its optional output. -/
theorem argmax (hs : ComputableInPolyTime score encA encB)
    (hc : ComputableInPolyTime (fun p : β × β => decide (p.1 < p.2))
      (encPair encB encB) encBool) :
    ComputableInPolyTime (List.argmax score) (encList encA) (encOption encA) := by
  have hstep : ComputableInPolyTime
      (fun p : Option α × α => List.argAux (fun b c => score c < score b) p.1 p.2)
      (encPair (encOption encA) encA) (encOption encA) := by
    have he (p : Option α × α) :
        List.argAux (fun b c => score c < score b) p.1 p.2 =
          p.1.elim (some p.2) (fun c => if score c < score p.2 then some p.2 else some c) := by
      rcases p with ⟨o, a⟩
      cases o <;> rfl
    simp_rw [he]
    apply optionElimWithInput (fst _ _) ((optionSome encA).comp (snd _ _))
    apply ite_decide
    · exact hc.comp ((hs.comp (snd _ _)).prod (hs.comp ((snd _ _).comp (fst _ _))))
    · exact (optionSome encA).comp ((snd _ _).comp (fst _ _))
    · exact (optionSome encA).comp (snd _ _)
  apply foldl' id' (const none) hstep (B := fun xs => (encList encA xs).length + 1)
    (PolyBounded.self.add (.const 1))
  intro xs i _
  change (encOption encA ((xs.take i).argmax score)).length ≤ _
  cases h : (xs.take i).argmax score with
  | none => simp only [encOption_none, List.length_nil]; omega
  | some a =>
    have hm : a ∈ xs.take i := List.argmax_mem h
    have hb := SizedListEncoding.length_elem_le (encA := encA) (encL := encList encA)
      xs a (List.mem_of_mem_take hm)
    simp only [encOption_some, List.length_cons]
    omega

/-- Reversing the same encoded comparison charges the actual minimum scan and its output. -/
theorem argmin (hs : ComputableInPolyTime score encA encB)
    (hc : ComputableInPolyTime (fun p : β × β => decide (p.1 < p.2))
      (encPair encB encB) encBool) :
    ComputableInPolyTime (List.argmin score) (encList encA) (encOption encA) :=
  argmax (β := OrderDual β) hs (hc.comp ((snd _ _).prod (fst _ _)))

end Turing.MultiTapeTM.ComputableInPolyTime
