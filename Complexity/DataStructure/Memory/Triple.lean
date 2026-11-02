/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Memory.Field
public import Complexity.DataStructure.StateTransition.CostHoare

/-!
# Correctness-and-cost triples for memory programs

`Memory.Triple w s p c Q` says that the memory program `p`, run from the state `s` at word size
`w`, issues only admissible operations, costs at most `c` memory units (`Memory.charge`), and
ends with an answer and a state satisfying `Q`. It is `StateTransitionSpec.CostHoare` at the
single initial state `s`; `Memory.triple_iff` unfolds it along the run of `p`.

The rules evaluate a program from its first operation on. `Triple.read_bind` and
`Triple.write_bind` discharge one operation's admissibility and charge, and leave the
continuation at the next state; `Triple.bind` splits a program at a subprogram with its own
triple; `Triple.pure` ends the run. Each rule peels one unit off a cost written `c + 1`, so a
straight-line program is checked by applying the rules in order. A recursive program is checked
by induction on its recursion measure, with the induction hypothesis applied at the recursive
call.

The word RAM's initial memory is zero past the input (`zeroAbove_init`), so a structure that
needs zeroed storage can take it there with a dirty allocation, at the cost of one unit, instead
of a zeroed one, whose charge grows with its size.

## Main definitions

* `Cslib.DataStructure.Memory.Triple`: admissibility, cost and postcondition of one run.
* `Cslib.DataStructure.Memory.ZeroAbove`: every cell at or above the frontier holds `0`.

## Main results

* `Cslib.DataStructure.Memory.triple_iff`: the triple along the run of the program.
* `Cslib.DataStructure.Memory.Triple.pure`, `Cslib.DataStructure.Memory.Triple.read_bind`,
  `Cslib.DataStructure.Memory.Triple.write_bind`,
  `Cslib.DataStructure.Memory.Triple.allocBlockDirty_bind`: one step of a run.
* `Cslib.DataStructure.Memory.Triple.bind`: sequential composition.
* `Cslib.DataStructure.Memory.Triple.mono`: weaken the cost and the postcondition.
* `Cslib.DataStructure.Memory.zeroAbove_init`: the input convention is zero above the frontier.
-/

@[expose] public section

namespace Cslib.DataStructure.Memory

open Cslib.WordRAM

variable {w : ℕ} {α β : Type}

/-- Run from `s` at word size `w`, the program `p` issues only admissible operations, costs at
most `c` memory units, and ends with an answer and a state satisfying `Q`. -/
abbrev Triple (w : ℕ) (s : State) (p : Prog α) (c : ℕ) (Q : α → State → Prop) : Prop :=
  (spec w).CostHoare charge (· = s) p Q fun _ => c

/-- A triple is a statement about the one run of the program. -/
theorem triple_iff {s : State} {p : Prog α} {c : ℕ} {Q : α → State → Prop} :
    Triple w s p c Q ↔ (spec w).ValidHistory s ((spec w).clientHistory s p) ∧
      (spec w).totalCost charge s ((spec w).clientHistory s p) ≤ c ∧
      Q ((spec w).clientResult s p) ((spec w).clientState s p) := by
  rw [Triple, StateTransitionSpec.costHoare_iff_ofFn, StateTransitionSpec.hoare_iff_ofFn]
  constructor
  · rintro ⟨h, hc⟩
    obtain ⟨hv, hq⟩ := h s rfl
    exact ⟨hv, hc s rfl, hq⟩
  · rintro ⟨hv, hc, hq⟩
    exact ⟨fun _ h => h ▸ ⟨hv, hq⟩, fun _ h => h ▸ hc⟩

namespace Triple

variable {s : State} {c c' : ℕ} {Q Q' : α → State → Prop}

/-- Weaken the cost and the postcondition. -/
theorem mono {p : Prog α} (h : Triple w s p c Q) (hc : c ≤ c') (hQ : ∀ a s', Q a s' → Q' a s') :
    Triple w s p c' Q' := by
  rw [triple_iff] at h ⊢
  exact ⟨h.1, h.2.1.trans hc, hQ _ _ h.2.2⟩

/-- Returning a value costs nothing. -/
theorem pure {a : α} (h : Q a s) : Triple w s (Pure.pure a) c Q :=
  triple_iff.mpr ⟨trivial, Nat.zero_le c, h⟩

/-- Read an allocated cell, then continue with its contents. -/
theorem read_bind {a : ℕ} {k : ℕ → Prog α} (ha : a < s.frontier)
    (h : Triple w s (k (s.mem a)) c Q) : Triple w s (read a >>= k) (c + 1) Q := by
  rw [triple_iff] at h ⊢
  obtain ⟨hv, hc, hq⟩ := h
  refine ⟨⟨ha, hv⟩, ?_, hq⟩
  change 1 + (spec w).totalCost charge s ((spec w).clientHistory s (k (s.mem a))) ≤ c + 1
  omega

/-- Write a word to an allocated cell, then continue. -/
theorem write_bind {a v : ℕ} {k : Unit → Prog α} (ha : a < s.frontier) (hv : Fits w v)
    (h : Triple w ⟨Function.update s.mem a v, s.frontier⟩ (k ()) c Q) :
    Triple w s (write a v >>= k) (c + 1) Q := by
  rw [triple_iff] at h ⊢
  obtain ⟨hvh, hc, hq⟩ := h
  refine ⟨⟨⟨ha, hv⟩, hvh⟩, ?_, hq⟩
  change 1 + (spec w).totalCost charge ⟨Function.update s.mem a v, s.frontier⟩
    ((spec w).clientHistory ⟨Function.update s.mem a v, s.frontier⟩ (k ())) ≤ c + 1
  omega

/-- Allocate a field of `k` cells without clearing it, then continue with the field at the
frontier. -/
theorem allocBlockDirty_bind {k : ℕ} {next : Block → Prog α} (hk : Fits w (s.frontier + k))
    (h : Triple w ⟨s.mem, s.frontier + k⟩ (next ⟨s.frontier, k⟩) c Q) :
    Triple w s (allocBlockDirty k >>= next) (c + 1) Q := by
  rw [triple_iff] at h ⊢
  obtain ⟨hv, hc, hq⟩ := h
  refine ⟨⟨hk, hv⟩, ?_, hq⟩
  change 1 + (spec w).totalCost charge ⟨s.mem, s.frontier + k⟩
    ((spec w).clientHistory ⟨s.mem, s.frontier + k⟩ (next ⟨s.frontier, k⟩)) ≤ c + 1
  omega

/-- **Sequential composition.** Run `p` within `c₁`, and from each of its outcomes run the
continuation within `c₂`. -/
theorem bind {p : Prog α} {k : α → Prog β} {c₁ c₂ : ℕ} {Q : β → State → Prop}
    (h : Triple w s p c₁ fun a s' => Triple w s' (k a) c₂ Q) :
    Triple w s (p >>= k) (c₁ + c₂) Q := by
  rw [triple_iff] at h ⊢
  obtain ⟨hv₁, hc₁, h₂⟩ := h
  rw [triple_iff] at h₂
  obtain ⟨hv₂, hc₂, hq⟩ := h₂
  have hrun := (spec w).runClient_bind p k s
  have hhist : (spec w).clientHistory s (p >>= k) = (spec w).clientHistory s p ++
      (spec w).clientHistory ((spec w).clientState s p) (k ((spec w).clientResult s p)) := by
    simp only [StateTransitionSpec.clientHistory]
    exact congrArg (fun r => r.2.2) hrun
  have hstate : (spec w).clientState s (p >>= k) =
      (spec w).clientState ((spec w).clientState s p) (k ((spec w).clientResult s p)) := by
    simp only [StateTransitionSpec.clientState]
    exact congrArg (fun r => r.2.1) hrun
  have hres : (spec w).clientResult s (p >>= k) =
      (spec w).clientResult ((spec w).clientState s p) (k ((spec w).clientResult s p)) :=
    congrArg (fun r => r.1) hrun
  have hmid := (spec w).run_runClient p s
  refine ⟨?_, ?_, ?_⟩
  · rw [hhist, StateTransitionSpec.validHistory_append, hmid]
    exact ⟨hv₁, hv₂⟩
  · rw [hhist, StateTransitionSpec.totalCost_append, hmid]
    omega
  · rw [hres, hstate]
    exact hq

end Triple

/-! ## Memory that is zero above the frontier -/

/-- Every cell at or above the frontier holds `0`, as in the word RAM's initial memory past the
input. A dirty allocation from such a state hands out a zeroed block at the cost of one unit. -/
def ZeroAbove (s : State) : Prop := ∀ a, s.frontier ≤ a → s.mem a = 0

/-- The input convention is zero above the frontier. -/
theorem zeroAbove_init (input : List ℕ) : ZeroAbove (State.init input) := by
  intro a ha
  change (if a = 0 then input.length else input.getD (a - 1) 0) = 0
  have ha' : input.length + 1 ≤ a := ha
  rw [ite_eq_right (by omega), List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

/-- A dirty allocation keeps memory zero above the new frontier. -/
theorem ZeroAbove.allocDirty {s : State} (h : ZeroAbove s) (k : ℕ) :
    ZeroAbove ⟨s.mem, s.frontier + k⟩ := fun a ha => h a (by simp only at ha; omega)

end Cslib.DataStructure.Memory
