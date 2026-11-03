/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Basic

/-!
# Selecting a uniform realization witness

These projections choose one witness of `Realizes` before any runtime argument, width, memory
or register layout. They use classical choice from a proposition: they do not claim executable
extraction from an arbitrary proof. They let adapters refer to the same emitted native code and
its proved exchange factor, without adding another realization judgment.

## Main definitions

* `Realizes.scratchSize`, `Realizes.factor`, `Realizes.code`: select the uniform witness.

## Main results

* `Realizes.code_spec`: the selected code has the complete original realization contract.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization.Realizes

open Cslib.DataStructure

variable {B : Basis} {δ α : Type} {k l : ℕ}
  {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
  {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}

/-- Number of auxiliary registers, chosen independently of every runtime value. -/
noncomputable def scratchSize (h : Realizes B p input output safe work) : ℕ := h.choose

/-- Uniform exchange factor for memory charges plus local work. -/
noncomputable def factor (h : Realizes B p input output safe work) : ℕ := h.choose_spec.choose

/-- One emitter, selected before the register layout or any runtime data. -/
noncomputable def code (h : Realizes B p input output safe work) {r : ℕ} :
    (frontier : Fin r) → (Fin k → Fin r) → (Fin (l + h.scratchSize + 1) → Fin r) → Code B r :=
  h.choose_spec.choose_spec.choose

/-- The selected witness retains width independence, literal whole-memory semantics, all result
coordinates, and the original live-register frame. -/
theorem code_spec (h : Realizes B p input output safe work) {r : ℕ}
    (frontier : Fin r) (src : Fin k → Fin r) (tmp : Fin (l + h.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier) :
    ¬(h.code frontier src tmp).ReadsWidth ∧
    ∀ (w : ℕ) (d : δ) (x : Data r), x.Bounded w → x.regs ∘ src = input d →
      safe w d (memoryState frontier x) →
      (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p d)) →
      ∃ y, ExecWithin w (h.code frontier src tmp) x y
          (h.factor * (memoryCost (p d) (memoryState frontier x) +
            work d (memoryState frontier x) + 1)) ∧
        memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (p d) ∧
        (∀ i : Fin l, y.regs (tmp (Fin.castAdd (h.scratchSize + 1) i)) =
          output ((Memory.spec w).clientResult (memoryState frontier x) (p d)) i) ∧
        ∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i :=
  h.choose_spec.choose_spec.choose_spec frontier src tmp hi hd hf hs

end Cslib.WordRAM.Realization.Realizes
