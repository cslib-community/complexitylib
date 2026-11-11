/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.List.Basic

/-! # Word comparison by a left fold

The original comparison state and its all-word laws, independent of resource certificates.
-/

public section
namespace Turing.MultiTapeTM

namespace EqWords

/-- One step of comparing a word with `s.1`, the part of the other word still to be matched;
`s.2` records whether the words agree so far. -/
@[expose] public def step (s : List Bool × Bool) (b : Bool) : List Bool × Bool :=
  (s.1.tail, s.2 && !s.1.isEmpty && (s.1.headD false == b))

public lemma foldl_fst (l r : List Bool) (ok : Bool) :
    (l.foldl step (r, ok)).1 = r.drop l.length := by
  induction l generalizing r ok with
  | nil => rfl
  | cons b l ih =>
    cases r <;> simp [step, ih]

public lemma foldl_result (l r : List Bool) (ok : Bool) :
    ((l.foldl step (r, ok)).2 && (l.foldl step (r, ok)).1.isEmpty) = (ok && decide (l = r)) := by
  induction l generalizing r ok with
  | nil => cases r <;> simp
  | cons b l ih =>
    rw [List.foldl_cons, ih]
    cases r <;> grind [step]

end EqWords

end Turing.MultiTapeTM
