/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PMFSwap

/-! # The tactics `pmf_swap` and `pmf_hoist` -/

namespace CslibFrontierTests.PMFSwap

variable {α β γ δ : Type}

/-! ## `pmf_swap` -/

-- Three independent samples, drawn in opposite orders.
example (p : PMF α) (q : PMF β) (r : PMF γ) (f : α → β → γ → PMF δ) :
    (p.bind fun a => q.bind fun b => r.bind fun c => f a b c) =
      r.bind fun c => q.bind fun b => p.bind fun a => f a b c := by
  pmf_swap

-- Two samples of the same distribution, swapped: the samples are matched in the order that makes
-- the two sides equal. `simp [PMF.bind_comm]` loops on this goal.
example (c : PMF α) (f : α → α → PMF β) :
    (c.bind fun a => c.bind fun b => f a b) = c.bind fun b => c.bind fun a => f a b := by
  pmf_swap

-- A final `PMF.map` is a sample like the others.
example (p : PMF α) (q : PMF β) (f : α → β → γ) :
    (p.bind fun a => q.map fun b => f a b) = q.bind fun b => p.map fun a => f a b := by
  pmf_swap

-- A goal after `have`, which annotates the target.
example (p : PMF α) (q : PMF β) (f : α → β → PMF γ) :
    (p.bind fun a => q.bind fun b => f a b) = q.bind fun b => p.bind fun a => f a b := by
  have _h : True := trivial
  pmf_swap

-- Common samples are stripped, and what remains is left as a goal, with the stripped samples
-- named by `with`.
example (p : PMF α) (q : PMF β) (f g : α → β → PMF γ) (h : ∀ a b, f a b = g a b) :
    (p.bind fun a => q.bind fun b => f a b) = q.bind fun b => p.bind fun a => g a b := by
  pmf_swap with b a
  exact h a b

-- `with x` strips exactly one sample. A sample whose distribution occurs once on each side, here
-- `r`, has only one possible partner and is stripped before the ambiguous samples of `p`.
example (p : PMF α) (r : PMF β) (t : PMF γ) (f : α → α → β → PMF δ) (g : α → β → γ → PMF δ)
    (h : ∀ x, (p.bind fun a => p.bind fun b => f a b x) = p.bind fun a => t.bind fun y => g a x y) :
    (p.bind fun a => p.bind fun b => r.bind fun x => f a b x) =
      p.bind fun a => r.bind fun x => t.bind fun y => g a x y := by
  pmf_swap with x
  exact h x

-- `with` fails when fewer samples than named can be stripped.
/--
error: pmf_swap: only 2 of the 3 named samples can be stripped; what remains is
  f a b = g a b
-/
#guard_msgs in
example (p : PMF α) (q : PMF β) (f g : α → β → PMF γ) :
    (p.bind fun a => q.bind fun b => f a b) = q.bind fun b => p.bind fun a => g a b := by
  pmf_swap with b a c

-- A goal produced by `simp only [pmf_norm]` from monad notation.
example (p : PMF α) (q : PMF β) (f : α → β → γ) :
    (do let a ← p; let b ← q; pure (f a b) : PMF γ) =
      (do let b ← q; let a ← p; pure (f a b) : PMF γ) := by
  simp only [pmf_norm]
  pmf_swap

-- Samples without a counterpart on the other side.
/--
error: pmf_swap: the two sides have no independent sample in common.
Left side samples:
  p
  p
Right side samples:
  p'
  p'
A sample can move to the front only when its distribution does not depend on earlier samples.
-/
#guard_msgs in
example (p p' : PMF α) (f : α → α → PMF β) :
    (p.bind fun a => p.bind fun b => f a b) = p'.bind fun a => p'.bind fun b => f a b := by
  pmf_swap

-- A sample that depends on an earlier sample does not move past it.
/--
error: pmf_swap: the two sides have no independent sample in common.
Left side samples:
  p
  q a (depends on an earlier sample)
Right side samples:
  q a₀
A sample can move to the front only when its distribution does not depend on earlier samples.
-/
#guard_msgs in
example (p : PMF α) (q : α → PMF β) (a₀ : α) (f : α → β → PMF γ) :
    (p.bind fun a => (q a).bind fun b => f a b) = (q a₀).bind fun b => f a₀ b := by
  pmf_swap

-- The goal must be an equation of distributions.
/--
error: pmf_swap: the goal is an equation in
  ℕ
not an equation of distributions `PMF α`
-/
#guard_msgs in
example (m n : ℕ) (h : m = n) : m = n := by
  pmf_swap

/-! ## `pmf_hoist` -/

-- A sample moves to the front inside a probability.
example (p : PMF α) (q : PMF β) (f : α → β → PMF Bool) :
    (p.bind fun a => q.bind fun b => f a b) true =
      (q.bind fun b => p.bind fun a => f a b) true := by
  pmf_hoist q

-- In a hypothesis.
example (p : PMF α) (q : PMF β) (f : α → β → PMF Bool) (x : ENNReal)
    (h : (p.bind fun a => q.bind fun b => f a b) true ≤ x) :
    (q.bind fun b => p.bind fun a => f a b) true ≤ x := by
  pmf_hoist q at h
  exact h

-- A sample already at the front does not move.
/--
error: pmf_hoist: no sample of
  q
can move toward the front of its chain
-/
#guard_msgs in
example (p : PMF α) (q : PMF β) (f : α → β → PMF Bool) :
    (q.bind fun b => p.bind fun a => f a b) true = 0 := by
  pmf_hoist q

-- When both sides draw the same samples in the same order, the goal does not say which sample to
-- strip; `pmf_hoist` chooses it.
example (p : PMF α) (q : PMF β) (f g : α → β → PMF γ)
    (h : ∀ b, (p.bind fun a => f a b) = p.bind fun a => g a b) :
    (p.bind fun a => q.bind fun b => f a b) = p.bind fun a => q.bind fun b => g a b := by
  pmf_hoist q
  congr 1 with b : 1
  exact h b

end CslibFrontierTests.PMFSwap
