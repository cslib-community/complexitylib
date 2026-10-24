/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Boolean.Encoding
public import Complexity.Computability.Circuit.MapOp
import Mathlib.Data.List.OfFn

/-!
# Circuit encodings under maps of signatures

## Main results

* `Cslib.Circuits.Circuit.code_mapOp`: mapping the operations maps the gate list and preserves
  the output wires.
* `Cslib.Circuits.Circuit.mapOp_injective`: an injective map of operations induces an injective
  map of circuits.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ τ : Signature} (φ : σ.Hom τ) {n g m : ℕ}

/-- The code of a translated line: the translated operation on the same wires. -/
private theorem Line.code_mapOp (line : Line σ n g) :
    (line.mapOp φ).code = (φ line.op, line.code.2) := by
  simp only [Line.code, Line.mapOp_op, Line.mapOp_wires]
  congr 1
  rw [List.ofFn_congr (φ.arity_eq line.op)]
  simp

/-- The code of a translated program: the operations of its gates translated. -/
private theorem Program.code_mapOp (p : Program σ n g) :
    (p.mapOp φ).code = p.code.map fun g => (φ g.1, g.2) := by
  induction p with
  | empty => rfl
  | gate p line ih => simp [ih, Line.code_mapOp]

/-- **The code of a translated circuit**: the operations of its gates translated, the same output
wires. -/
theorem Circuit.code_mapOp (c : Circuit σ n m) :
    (c.mapOp φ).code = (c.code.1.map fun g => (φ g.1, g.2), c.code.2) := by
  simp [Circuit.code, Program.code_mapOp]

/-- Translation along an injective map of operations is injective. -/
theorem Circuit.mapOp_injective (hφ : Function.Injective φ) :
    Function.Injective (Circuit.mapOp (n := n) (m := m) φ) := by
  intro c c' h
  have hc := congrArg Circuit.code h
  rw [Circuit.code_mapOp, Circuit.code_mapOp] at hc
  obtain ⟨h₁, h₂⟩ := Prod.ext_iff.1 hc
  refine Circuit.code_injective (Prod.ext ?_ h₂)
  refine List.map_injective_iff.2 (fun g g' hg => ?_) h₁
  obtain ⟨hg₁, hg₂⟩ := Prod.ext_iff.1 hg
  exact Prod.ext (hφ hg₁) hg₂

end Cslib.Circuits
