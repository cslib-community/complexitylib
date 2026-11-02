/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Quantitative
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import Mathlib.Data.List.GetD

/-!
# Native reversal and binary slicing of framed lists

Reversal and taking or dropping a binary-counted prefix use space linear in the actual encoded
list and counter. Every intermediate list is a prefix, suffix or reversal of stored input data;
large binary counts never cause a list of that length to be allocated.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.listReverse`: reverse a framed list.
* `Turing.MultiTapeTM.ComputableInSpace.listDrop`, `.listTake`: slice with a binary counter.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Reverse a framed list in native space linear in its actual encoded storage. -/
theorem listReverse {α : Type} (enc : α ↪ List Bool) :
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

/-- Drop a binary-counted prefix without allocating storage according to its numeric length. -/
theorem listDrop {α : Type} (enc : α ↪ List Bool) :
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

/-- Take a binary-counted prefix using space linear in the actual framed list and counter. -/
theorem listTake {α : Type} (enc : α ↪ List Bool) :
    ComputableInSpace (fun q : List α × ℕ => q.1.take q.2)
      (encPair (encList enc) encNat) (encList enc)
      (fun q => (encPair (encList enc) encNat q).length) := by
  have hl := fst (encList enc) encNat
  have hn := snd (encList enc) encNat
  have hrev := budget_comp_linear (listReverse enc) hl
  have hlen := budget_length hl
  have hcount := budget_natSub hlen hn
  have hdrop := budget_comp_linear (listDrop enc) (budget_prod hrev hcount)
  refine (budget_comp_linear (listReverse enc) hdrop).of_enc_eq ?_
  intro q
  rw [← List.reverse_take, List.reverse_reverse]

end Turing.MultiTapeTM.ComputableInSpace
