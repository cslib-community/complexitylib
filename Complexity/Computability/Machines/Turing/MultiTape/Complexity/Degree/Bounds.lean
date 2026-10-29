/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Direct degree weakening and polynomial-time consequences

The original three plain rules are moved unchanged from the degree-calculus module to keep
ordinary clients independent of its legacy construction calculus.

Charged `ComputableInO` bounds also give degree certificates: a lower workspace degree bounds
encoded output at that lower degree, even when the time bound has a higher degree.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace ComputableInDegree

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {d e d' e' : ℕ}

/-- Increasing either degree retains the same realizing machine. -/
public theorem mono (h : ComputableInDegree f encIn encOut d e)
    (hd : d ≤ d' := by first | decide | omega) (he : e ≤ e' := by first | decide | omega) :
    ComputableInDegree f encIn encOut d' e' :=
  let ⟨⟨t, s, ht, hs, hf⟩, hl⟩ := h
  ⟨⟨t, s, ht.mono_deg hd, hs.mono_deg hd, hf⟩, hl.mono_deg he⟩

/-- Exact time and workspace bounds of degree `d` also bound the output length in degree `d`. -/
public theorem of_bounds {t s : α → ℕ}
    (ht : DegreeBounded (fun a => (encIn a).length) t d)
    (hs : DegreeBounded (fun a => (encIn a).length) s d)
    (hf : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInDegree f encIn encOut d d :=
  ⟨⟨t, s, ht, hs, hf⟩, ht.mono hf.length_le⟩

/-- Fixed time and workspace degrees give plain polynomial-time computability, including degree
zero. Encoded output is bounded separately and is not charged to workspace. -/
public theorem computableInPolyTime (h : ComputableInDegree f encIn encOut d e) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨⟨_, _, ht, hs, h⟩, _⟩ := h
  obtain ⟨T, hT, ht⟩ := ht.polyBounded
  obtain ⟨S, hS, hs⟩ := hs.polyBounded
  exact ⟨T, S, hT, hS, h.mono ht hs⟩

/-- The realizing machine's own clock bounds its output, independently of the supplied output
 degree. Both asymptotic resource exponents remain `d`, including zero. -/
theorem inO (h : ComputableInDegree f encIn encOut d e) :
    ComputableInO f encIn encOut (fun a => ((encIn a).length + 1) ^ d)
      (fun a => ((encIn a).length + 1) ^ d) := by
  obtain ⟨⟨_, _, ⟨ct, ht⟩, ⟨cs, hs⟩, hf⟩, _⟩ := h
  exact .of_bounds hf (ct + cs)
    (fun a => (ht a).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _)))
    (fun a => (hs a).trans (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_succ _)))
    (fun a => (hf.length_le a).trans
      ((ht a).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _))))

/-- Cost degree one gives linear charged resource bounds, without restricting the output degree. -/
theorem inO_one (h : ComputableInDegree f encIn encOut 1 e) :
    ComputableInO f encIn encOut (fun a => (encIn a).length) (fun a => (encIn a).length) :=
  h.inO.mono 1 (fun _ => by simp) (fun _ => by simp)

end ComputableInDegree

/-- Charged workspace of degree `e` bounds the encoded output at that same degree. When
`e ≤ d`, independent degree bounds on time and workspace give cost degree `d` and output
degree `e`, retaining the realizing machine and its original resource bounds. -/
theorem ComputableInO.computableInDegree
    {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {T S : α → ℕ} {d e : ℕ} (h : ComputableInO f encIn encOut T S)
    (hT : DegreeBounded (fun a => (encIn a).length) T d)
    (hS : DegreeBounded (fun a => (encIn a).length) S e) (hed : e ≤ d) :
    ComputableInDegree f encIn encOut d e := by
  obtain ⟨c, hc, hl⟩ := h
  have ht := (hT.add_const 1).smul c
  have hs := (hS.add_const 1).smul c
  exact ⟨⟨_, _, ht, hs.mono_deg hed, hc⟩, hs.mono hl⟩

end Turing.MultiTapeTM
