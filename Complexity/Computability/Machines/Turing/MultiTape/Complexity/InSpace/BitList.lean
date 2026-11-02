/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib

/-!
# Removing Boolean-list framing in native linear space

`listToBits` copies a framed list of Boolean values to a raw word without changing its contents.
The native fold keeps only an output prefix, whose length is bounded by the input list length.
This permits state-returning serializers to supply raw words to runtime codecs.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

/-- Remove list framing in work space linear in the actual framed input. -/
theorem listToBits : ComputableInSpace (fun l : List Bool => l) (encList encBool) encBits
    (fun l => (encList encBool l).length) := by
  have hid : ComputableInSpace (fun l : List Bool => l) (encList encBool) (encList encBool)
      (fun l => (encList encBool l).length) := of_inO (ComputableInO.of_eq fun _ => rfl)
  have hs : ComputableInSpace (fun p : List Bool × Bool => p.1 ++ [p.2])
      (encPair encBits encBool) encBits
      (fun p => (encPair encBits encBool p).length) := by
    have hword := fst encBits encBool
    have hbit := (snd encBits encBool).of_enc_eq
      (encC := encBits) (g := fun p : List Bool × Bool => [p.2]) (fun _ => rfl)
    exact (hword.append hbit (fun _ => rfl)).weaken (.add (.refl _) (.refl _))
  have hfold (l out : List Bool) :
      l.foldl (fun acc bit => acc ++ [bit]) out = out ++ l := by
    induction l generalizing out with
    | nil => simp
    | cons bit l ih => simp [List.foldl_cons, ih, List.append_assoc]
  have hstate (l : List Bool) (i : ℕ) (hi : i ≤ l.length) :
      (encBits ((l.take i).foldl (fun acc bit => acc ++ [bit]) [])).length ≤
        (encList encBool l).length := by
    rw [hfold, List.nil_append]
    exact (List.length_take_le i l).trans (hi.trans (length_le_length_encList encBool l))
  have hspace (l : List Bool) (i : ℕ) (hi : i < l.length) :
      (encPair encBits encBool
        ((l.take i).foldl (fun acc bit => acc ++ [bit]) [], l[i])).length ≤
          4 * ((encList encBool l).length + 1) := by
    have h := hstate l i hi.le
    simp only [length_encPair, encBool_apply, List.length_singleton]
    omega
  have h := foldl hid (budget_const [] (.refl _)) hs hspace hstate
  refine h.weaken (.of_le_linear 16 16 fun _ => by omega) |>.of_enc_eq ?_
  intro l
  rw [hfold, List.nil_append]

end Turing.MultiTapeTM.ComputableInSpace
