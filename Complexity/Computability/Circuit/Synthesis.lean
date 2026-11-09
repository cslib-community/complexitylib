/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Computability.Circuit.Synthesis
import Cslib.Computability.Circuit.Composition

/-!
# Building circuits from available functions

An existing circuit can be inserted into a synthesis construction by wiring its inputs to
available functions. Its outputs then become available at a cost of its number of gates, while
all previously computed functions remain available. Repeated inputs share their original wires.

`Synthesis.Builder` accumulates available wires and gate costs through `Builder.start` and
`Builder.add`. Each appended construction is charged once; selecting and reusing wires is free.
`Builder.finish` selects the outputs and checks the requested bound. These operations compose
ordinary `Synthesis` certificates; they do not search for a cheaper construction.

## Main definitions

* `Cslib.Circuits.Synthesis.Builder`: available wires and their accumulated synthesis bound.

## Main results

* `Cslib.Circuits.Synthesis.circuit`: applying a circuit costs its number of gates.
* `Cslib.Circuits.Synthesis.extend`: append a construction fed by the wires built so far.
* `Cslib.Circuits.Synthesis.Builder.finish`: select outputs within a requested gate budget.

## References

* Adapted from MassProduction/Nonuniform/FlagSelection.lean in
  [S. Schlesinger, *Boolean circuit mass production formalization*][Schlesinger2026MassProduction].
-/

@[expose] public section

namespace Cslib.Circuits

universe v u

variable {σ : Signature.{v}} {U : Type u} {I : Interpretation σ U} {n : ℕ}

/-- A circuit whose inputs are fed by available functions computes its outputs with as many
additional gates as it has. The functions feeding the inputs may repeat. -/
theorem Synthesis.circuit {s : Set ((Fin n → U) → U)} {m p : ℕ} (c : Circuit σ m p)
    (g : Fin m → (Fin n → U) → U) (hg : ∀ i, g i ∈ s) :
    Synthesis I s (Set.range fun j x => c.eval I (fun i => g i x) j) c.size := by
  intro g₁ p₁ hp
  choose wires hw using fun i => mem_available.mp (hp (hg i))
  refine ⟨g₁ + c.size, p₁.append wires c.program, le_rfl, ?_, ?_⟩
  · intro f hf
    obtain ⟨w, hw'⟩ := mem_available.mp hf
    exact mem_available.mpr ⟨w.castAdd c.size, fun x =>
      (Program.trace_append_castAdd p₁ wires I x c.program w).trans (hw' x)⟩
  · rintro _ ⟨j, rfl⟩
    refine mem_available.mpr ⟨Program.appendedWire wires (c.outputs j), fun x => ?_⟩
    rw [Program.trace_append_appendedWire]
    have : (fun i => p₁.trace I x (wires i)) = fun i => g i x := funext fun i => hw i x
    rw [this]
    rfl

namespace Synthesis

variable {s : Set ((Fin n → U) → U)}

/-- Append a construction whose inputs are among the targets built so far, keeping those targets
available. This is the certificate behind `Builder.add`. The new family `u` is explicit, so a
chain of `extend` steps accumulates the syntactic union `s ∪ t₁ ∪ ⋯ ∪ tₖ`, and membership in it
can be checked without unfolding. -/
theorem extend {t : Set ((Fin n → U) → U)} {a b : ℕ} (h : Synthesis I s t a)
    (u : Set ((Fin n → U) → U)) (h' : Synthesis I t u b) : Synthesis I s (t ∪ u) (a + b) :=
  h.comp (h'.mono Set.subset_union_right Set.Subset.rfl le_rfl)

/-- A sequence of certified constructions, including every wire available along the way. -/
structure Builder (I : Interpretation σ U) (s : Set ((Fin n → U) → U)) where
  /-- Original sources and all outputs built so far. -/
  wires : Set ((Fin n → U) → U)
  /-- Sum of the appended constructions' gate budgets. -/
  cost : ℕ
  /-- The accumulated synthesis certificate. -/
  bound : Synthesis I s wires cost

namespace Builder

/-- Begin with the source wires, without adding gates. -/
def start (I : Interpretation σ U) (s : Set ((Fin n → U) → U)) : Builder I s :=
  ⟨s, 0, .of_subset Set.Subset.rfl⟩

/-- Append a construction whose inputs are available, retaining both old and new wires. -/
def add (b : Builder I s) {t : Set ((Fin n → U) → U)} {k : ℕ}
    (h : Synthesis I b.wires t k) : Builder I s :=
  ⟨b.wires ∪ t, b.cost + k, b.bound.extend t h⟩

/-- Select outputs from the final wires and enlarge the accumulated budget. -/
theorem finish (b : Builder I s) {t : Set ((Fin n → U) → U)} {k : ℕ}
    (ht : t ⊆ b.wires) (hk : b.cost ≤ k) : Synthesis I s t k :=
  b.bound.mono Set.Subset.rfl ht hk

end Builder

end Synthesis

end Cslib.Circuits
