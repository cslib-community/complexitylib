/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Circuit/Composition.lean`)

public import CslibFrontier.Computability.Circuit.Pi

/-!
# Lines of composed circuits

Continuing a program `p` by a program `q` keeps the lines of `p`, with their wires widened to the
larger namespace (`Program.lines_append_castAdd`), and places after them the lines of `q`, with
their input wires read from the feeding wires of `p` and their gate wires shifted past the gates of
`p` (`Program.lines_append_natAdd`). Consequently every line of the side-by-side circuit
`Circuit.pi cs` is a line of some `cs j` whose wires are renamed by a map that fixes original inputs
and sends gates to gates (`Circuit.exists_lines_pi`), and its outputs are gates when those of every
`cs j` are (`Circuit.outputs_pi_eq_gate`).

## Main results

* `Cslib.Circuits.Program.lines_append_castAdd`, `Cslib.Circuits.Program.lines_append_natAdd`: the
  lines of a continued program.
* `Cslib.Circuits.Circuit.exists_lines_pi`: every line of `pi cs` is a renamed line of some `cs j`.
* `Cslib.Circuits.Circuit.outputs_pi_eq_gate`: the outputs of `pi cs` are gates when the outputs of
  the circuits `cs j` are.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {n k g₁ g₂ : ℕ}

namespace Program

/-- Reading a wire of the continuation commutes with widening it by one gate. -/
@[simp] theorem appendedWire_castSucc (feed : Fin k → Wire n g₁) (w : Wire k g₂) :
    appendedWire feed w.castSucc = (appendedWire feed w).castSucc := by
  cases w with
  | input i =>
    change (feed i).castAdd (g₂ + 1) = ((feed i).castAdd g₂).castSucc
    cases feed i <;> rfl
  | gate j => rfl

variable (p : Program σ n g₁) (feed : Fin k → Wire n g₁)

/-- Continuing `p` by `q` keeps each line of `p`, with its wires widened past the gates of `q`. -/
theorem lines_append_castAdd (q : Program σ k g₂) (j : Fin g₁) :
    (p.append feed q).lines (Fin.castAdd g₂ j) = (p.lines j).mapWires (Wire.castAdd g₂) := by
  induction q with
  | empty =>
    change p.lines j = _
    generalize p.lines j = l
    obtain ⟨op, wires⟩ := l
    simp only [Line.mapWires, Line.mk.injEq, heq_eq_eq, true_and]
    funext a
    simp only [Function.comp_apply]
    cases wires a <;> rfl
  | @gate g₂ q line ih =>
    refine (Program.lines_gate_castSucc (p.append feed q) _ (Fin.castAdd g₂ j)).trans ?_
    rw [ih]
    generalize p.lines j = l
    obtain ⟨op, wires⟩ := l
    simp only [Line.mapWires, Line.mk.injEq, heq_eq_eq, true_and]
    funext a
    simp only [Function.comp_apply, Wire.Renaming.castSucc_apply]
    cases wires a <;> rfl

/-- The lines of `q` follow those of `p` in `p.append feed q`, reading their inputs from `feed`
and their gates shifted past the gates of `p`. -/
theorem lines_append_natAdd (q : Program σ k g₂) (j : Fin g₂) :
    (p.append feed q).lines (Fin.natAdd g₁ j) = (q.lines j).mapWires (appendedWire feed) := by
  induction q with
  | empty => exact j.elim0
  | @gate g₂ q line ih =>
    induction j using Fin.lastCases with
    | last =>
      refine (Program.lines_gate_last (p.append feed q) _).trans ?_
      rw [Program.lines_gate_last]
      simp only [Line.mapWires]
      congr 1
      funext a
      simp only [Function.comp_apply, Wire.Renaming.castSucc_apply, appendedWire_castSucc]
    | cast j =>
      refine (Program.lines_gate_castSucc (p.append feed q) _ (Fin.natAdd g₁ j)).trans ?_
      rw [ih, Program.lines_gate_castSucc]
      simp only [Line.mapWires]
      congr 1
      funext a
      simp only [Function.comp_apply, Wire.Renaming.castSucc_apply, appendedWire_castSucc]

end Program

namespace Circuit

/-- Every line of `pi cs` is a line of some `cs j`, with its wires renamed by a map `f` that fixes
the original inputs and sends gates to gates. -/
theorem exists_lines_pi {m : ℕ} (cs : Fin m → Circuit σ n 1) (k : Fin (pi cs).size) :
    ∃ (j : Fin m) (k' : Fin (cs j).size) (f : Wire n (cs j).size → Wire n (pi cs).size),
      (∀ i, f (.input i) = .input i) ∧ (∀ g, ∃ g', f (.gate g) = .gate g') ∧
      (pi cs).program.lines k = ((cs j).program.lines k').mapWires f := by
  induction m with
  | zero => exact k.elim0
  | succ m ih =>
    revert k
    rw [pi]
    intro k
    induction k using Fin.addCases with
    | left k =>
      obtain ⟨j, k', f, hi, hg, hk⟩ := ih (fun i => cs i.castSucc) k
      refine ⟨j.castSucc, k', Wire.castAdd _ ∘ f, fun i => congrArg (Wire.castAdd _) (hi i),
        fun g => ?_, ?_⟩
      · obtain ⟨g', hg'⟩ := hg g
        exact ⟨Fin.castAdd _ g', congrArg (Wire.castAdd _) hg'⟩
      · exact (Program.lines_append_castAdd _ _ _ k).trans (by rw [hk]; rfl)
    | right k =>
      exact ⟨Fin.last m, k, Program.appendedWire Wire.input, fun i => rfl,
        fun g => ⟨_, rfl⟩, Program.lines_append_natAdd _ _ _ k⟩

/-- If every circuit `cs j` outputs a gate, then every output of `pi cs` is a gate. -/
theorem outputs_pi_eq_gate {m : ℕ} (cs : Fin m → Circuit σ n 1)
    (h : ∀ j, ∃ g, (cs j).outputs 0 = .gate g) (j : Fin m) :
    ∃ g, (pi cs).outputs j = .gate g := by
  induction m with
  | zero => exact j.elim0
  | succ m ih =>
    induction j using Fin.lastCases with
    | last =>
      obtain ⟨g, hg⟩ := h (Fin.last m)
      refine ⟨Fin.natAdd _ g, ?_⟩
      change ((pi fun i => cs i.castSucc).append (cs (Fin.last m))).outputs (Fin.natAdd m 0) = _
      rw [outputs_append_natAdd, hg]
      rfl
    | cast j =>
      obtain ⟨g, hg⟩ := ih (fun i => cs i.castSucc) (fun i => h i.castSucc) j
      refine ⟨Fin.castAdd _ g, ?_⟩
      change ((pi fun i => cs i.castSucc).append (cs (Fin.last m))).outputs (Fin.castAdd 1 j) = _
      rw [outputs_append_castAdd, hg]
      rfl

end Circuit

end Cslib.Circuits
