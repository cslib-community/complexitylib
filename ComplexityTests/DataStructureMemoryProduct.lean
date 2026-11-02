/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.DataStructure.Stack.Memory

/-!
# Three stacks in one memory

Three array stacks of capacity `2` sit side by side in one memory at word size `8`. The iterated
product `(S₀.prod S₁).prod S₂` of their framed refinements implements the product of three stack
specifications. The tests run one linked client against concrete memory, transport the
specification's answer to it with `Refinement.simulates_client`, and check that the amortized
certificates add across both products to three memory units per operation, which also gives a
worst-case `Module.ChargeBound`.
-/

@[expose] public section

namespace ComplexityTests.DataStructureMemoryProduct

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Queue

/-- A bounded stack of capacity `2` at word size `8`. -/
abbrev S : StateTransitionSpec := Stack.WordRAM.spec 8 2

/-- The layout of stack `i`: its count cell at `3 i`, its items at `3 i + 1` and `3 i + 2`. -/
def layout (i : ℕ) : Stack.Memory.Layout := ⟨⟨3 * i, 1⟩, ⟨3 * i + 1, 2⟩⟩

/-- The three layouts are well formed. -/
theorem valid (i : ℕ) (hi : i < 3) : (layout i).Valid 8 2 :=
  Stack.Memory.valid_allocLayout (f := 3 * i) (Fits.of_le (show Fits 8 9 by decide) (by omega))

/-- Nested products find their transition function by instance search, at any depth. -/
example : (product (product S S) (product S (product S S))).HasStepFn
    (productStepFn _ _ (productStepFn S S (stack ℕ).stepFn (stack ℕ).stepFn)
      (productStepFn _ _ (stack ℕ).stepFn
        (productStepFn S S (stack ℕ).stepFn (stack ℕ).stepFn))) :=
  inferInstance

/-- So do nested products of arbitrary deterministic specifications. -/
example (D E F : StateTransitionSpec)
    {fD : (s : D.State) → (o : D.Op) → D.State × D.Result o}
    {fE : (s : E.State) → (o : E.Op) → E.State × E.Result o}
    {fF : (s : F.State) → (o : F.Op) → F.State × F.Result o}
    [D.HasStepFn fD] [E.HasStepFn fE] [F.HasStepFn fF] :
    (product D (product E F)).HasStepFn (productStepFn _ _ fD (productStepFn _ _ fE fF)) :=
  inferInstance

/-- Totality and determinism of nested products of relational specifications. -/
example (D E F : StateTransitionSpec) [D.Total] [E.Total] [F.Total] [D.Deterministic]
    [E.Deterministic] [F.Deterministic] :
    (product (product D E) F).Total ∧ (product (product D E) F).Deterministic :=
  ⟨inferInstance, inferInstance⟩

/-- Stack `i`, framed by its layout. -/
abbrev stackAt (i : ℕ) (hi : i < 3) : Framed S 8 := Stack.Memory.framed (valid i hi)

/-- The three stacks in one memory. -/
abbrev triple : Framed (product (product S S) S) 8 :=
  ((stackAt 0 (by decide)).prod (stackAt 1 (by decide))).prod (stackAt 2 (by decide))

/-- Push `1` and `2` on the first stack and `3` on the third, then pop the first stack twice and
read the sizes. -/
def client : (product (product S S) S).Client (List (Option ℕ) × List ℕ) := do
  let _ ← (product (product S S) S).call (.inl (.inl (.push 1)))
  let _ ← (product (product S S) S).call (.inl (.inl (.push 2)))
  let _ ← (product (product S S) S).call (.inr (.push 3))
  let a ← (product (product S S) S).call (.inl (.inl .pop))
  let b ← (product (product S S) S).call (.inl (.inl .pop))
  let m ← (product (product S S) S).call (.inl (.inr .size))
  let n ← (product (product S S) S).call (.inr .size)
  pure ([a, b], [m, n])

/-- Nine allocated zero cells: three empty stacks. -/
def empty : State := ⟨fun _ => 0, 9⟩

/-- The linked client answers last in, first out, on each stack separately. -/
example : (spec 8).clientResult empty (link triple.methods client) =
    ([some 2, some 1], [0, 1]) := by
  decide

/-- It issues `4 · 3 + 1 + 1` memory operations, three per push and per nonempty pop, one per
size. -/
example : (spec 8).totalCost charge empty ((spec 8).clientHistory empty
    (link triple.methods client)) = 17 := by
  decide

/-- Each stack holds in the empty memory. -/
theorem inv_layout (i : ℕ) (hi : i < 3) : Stack.Memory.Inv (layout i) empty where
  count_allocated := by simp only [Block.Allocated, layout, empty]; omega
  items_allocated := by simp only [Block.Allocated, layout, empty]; omega
  count_le := by simp [layout, empty]

/-- The three stacks hold in the empty memory, with disjoint footprints. -/
theorem inv_empty : triple.inv empty :=
  ⟨⟨inv_layout 0 (by decide), inv_layout 1 (by decide), by decide⟩, inv_layout 2 (by decide),
    by decide⟩

/-- The specification's answer, transported to the memory run by the iterated product. -/
example : (spec 8).clientResult empty (link triple.methods client) =
    (product (product S S) S).clientResult (triple.abs empty) client :=
  (triple.simulates_client client inv_empty
    ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, trivial, trivial,
      trivial, trivial, trivial⟩).2.1

/-- Every operation of the three stacks costs at most three memory units, amortized with zero
potential: the stacks' certificates add across both products. -/
theorem amortized : triple.Amortized charge (fun _ _ => 3) fun _ => 0 := by
  have h₀₁ := Framed.amortized_prod (Stack.Memory.amortized (valid 0 (by decide)))
    (Stack.Memory.amortized (valid 1 (by decide))) (Framed.Local.const _ 0)
    (Framed.Local.const _ 0)
  rw [productCharge_const] at h₀₁
  have h := Framed.amortized_prod h₀₁ (Stack.Memory.amortized (valid 2 (by decide)))
    (fun _ _ _ => rfl) (Framed.Local.const _ 0)
  rwa [productCharge_const] at h

/-- With zero potential, the same certificate is a worst-case charge bound. -/
example : triple.toModule.ChargeBound charge fun _ _ => 3 :=
  amortized.chargeBound

end ComplexityTests.DataStructureMemoryProduct
