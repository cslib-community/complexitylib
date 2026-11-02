/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: candidate

import Complexity.Computability.WordRAM.Realization.Backend
import Complexity.Computability.WordRAM.Realization.Client.MemoryStack
import Complexity.Computability.WordRAM.Realization.Function

/-! The per-constructor backend on the array stack. Three tags select the bodies of
`MemoryStack.realizes_push`, `realizes_pop` and `realizes_size`. The push carries a value and
answers `()`; its result encoding has no words, so the value is not echoed. The layout is a
runtime argument of every tag. Correctness and a constant instruction bound come from
`Stack.Memory.refinement` and `Stack.Memory.amortized`. -/

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
  Cslib.WordRAM.Realization.MemoryStack Cslib.DataStructure.Queue

namespace ComplexityTests.WordRAMRealizationBackend

/-- The stack's operation constructors. -/
inductive Tag
  | push
  | pop
  | size
  deriving DecidableEq

instance : Fintype Tag := Fintype.ofList [.push, .pop, .size] fun t => by cases t <;> simp

/-- One realization per constructor. -/
noncomputable def certificates : Tag → Certificate .exact
  | .push => ⟨realizes_push⟩
  | .pop => ⟨realizes_pop⟩
  | .size => ⟨realizes_size⟩

/-- The stack on layout `L`: the push value and the layout are the only arguments. -/
noncomputable def backend (w C : ℕ) (L : Stack.Memory.Layout) :
    Backend (Stack.WordRAM.spec w C) certificates where
  tag
    | .push _ => .push
    | .pop => .pop
    | .size => .size
  arg
    | .push v => (L, v)
    | .pop => L
    | .size => L
  answer
    | .push _ => id
    | .pop => id
    | .size => id

theorem layoutWords_fits {w : ℕ} {L : Stack.Memory.Layout} {e : Memory.State}
    (hw : Memory.WellFormed w e) (hi : Stack.Memory.Inv L e) (j : Fin 4) :
    Fits w (layoutWords L j) := by
  have h₁ : L.count.base + L.count.length ≤ e.frontier := hi.count_allocated
  have h₂ : L.items.base + L.items.length ≤ e.frontier := hi.items_allocated
  refine hw.frontier_fits.of_le ?_
  fin_cases j <;> simp [layoutWords] <;> omega

theorem implements {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) :
    (backend w C L).Implements (Stack.Memory.refinement hL) where
  run o s := by cases o <;> rfl
  entry {e} o hw hi hv := by
    have hC := hL.items_length
    cases o with
    | push v =>
      obtain ⟨hlen, hv⟩ := hv
      change (Stack.Memory.abs L e).length < C at hlen
      rw [Stack.Memory.length_abs] at hlen
      exact ⟨fits_appendWords (d := L) (a := v) layoutWords
        (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (layoutWords_fits hw hi) fun _ => hv,
        hC ▸ hL, hi, (by omega : e.mem L.count.base < L.items.length)⟩
    | pop => exact ⟨layoutWords_fits hw hi, hC ▸ hL, hi⟩
    | size => exact ⟨layoutWords_fits hw hi, trivial⟩

/-- The native stack on layout `L`. -/
noncomputable def implementation {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) :
    StateTransitionImpl (Stack.WordRAM.spec w C) ((backend w C L).exec w) :=
  Backend.implementation (implements hL)

/-- One constant bounds every operation, before every width, capacity and layout. -/
theorem instruction_bound : ∃ K, ∀ {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C),
    Bound (implementation hL) id fun _ _ => K :=
  ⟨Backend.factor certificates * 23, fun hL =>
    Backend.bound (implements hL) (Stack.Memory.amortized hL) 19 fun o _ _ => by
      cases o <;> exact Nat.le_of_ble_eq_true rfl⟩

/-- Adaptive clients run one operation at a time, within `K` instructions per operation. -/
theorem run_client : ∃ K, ∀ {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {α : Type}
    (p : (Stack.WordRAM.spec w C).Client α) {vs : List ℕ}
    {x : Data (Backend.registers certificates)},
    (implementation hL).rep vs x →
    (Stack.WordRAM.spec w C).ValidHistory vs ((Stack.WordRAM.spec w C).clientHistory vs p) →
    ∃ y traces, Executes ((backend w C L).exec w) p x
        ((Stack.WordRAM.spec w C).clientResult vs p) y traces ∧
      (implementation hL).rep ((Stack.WordRAM.spec w C).clientState vs p) y ∧
      total id traces ≤ ((Stack.WordRAM.spec w C).clientHistory vs p).length * K := by
  obtain ⟨K, hK⟩ := instruction_bound
  exact ⟨K, fun hL _ p _ _ hr hv => Bound.exists_executes_const (hK hL) p hr hv⟩

-- The push value never selects code: every push runs the body of the `push` tag.
example (w C : ℕ) (L : Stack.Memory.Layout) :
    Backend.code certificates ((backend w C L).tag (.push 3)) =
      Backend.code certificates ((backend w C L).tag (.push 4)) := rfl

-- A push answers `()` through an empty result encoding; its value is not echoed.
example : (certificates .push).l = 0 := rfl

-- Every native execution from a represented stack takes the specified step, and its memory is
-- the method's final memory.
example {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {vs : List ℕ}
    {x y : Data (Backend.registers certificates)} {o : StackOp ℕ}
    {a : (Stack.WordRAM.spec w C).Result o} {n : ℕ} (hr : (implementation hL).rep vs x)
    (hv : (Stack.WordRAM.spec w C).valid vs o) (he : (backend w C L).exec w x o a y n) :
    a = ((Stack.WordRAM.spec w C).stepFn vs o).2 ∧
      memoryState (Backend.frontier certificates) y = (Memory.spec w).clientState
        (memoryState (Backend.frontier certificates) x) (Stack.Memory.methods L w C o) :=
  ⟨((implementation hL).correct_ofFn hr hv he).1,
    Backend.exec_memoryState (implements hL) hr hv he⟩

-- An empty stack of capacity two at address three, held in zero memory with the frontier at six,
-- is represented by the native data holding that memory state.
example : (implementation (Stack.Memory.valid_allocLayout (w := 4) (f := 3) (C := 2)
    (by decide))).rep [] (Backend.data certificates ⟨fun _ => 0, 6⟩) :=
  Backend.rep_data _ ⟨by decide, fun _ => fits_zero 4⟩ ⟨le_of_lt (by decide), le_rfl, by simp⟩
    (by simp [Stack.Memory.refinement, Stack.Memory.abs])

-- Two stacks with disjoint layouts: product operations select tags of `Tag ⊕ Tag`.
example {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) :
    ((backend w C L₁).sum (backend w C L₂)).Implements
      ((Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)).toRefinement :=
  (implements h₁).prod (frame₁ := Memory.Framed.prod_frame_left _ _)
    (frame₂ := Memory.Framed.prod_frame_right _ _) (implements h₂)

-- Doubling at every width of at least `2 * (log₂ n + 1)` bits, as one flat program.
example : UniformComputableInPolyTime .standard (fun n => n + n) (fun _ n => [n]) id :=
  (Realizes.addWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding 0 0).uniformComputableInPolyTime
    .exactStandard 0 (.const 3) 2 (by decide) (fun _ _ j => by fin_cases j; rfl)
    fun n w hw _ => by
      have h2 : Fits w 2 := (show Fits 2 2 by decide).mono (le_trans (by simp [logWidth]) hw)
      have hn : Fits w (n + n) := (fits_of_lt_pow (k := 2) (n := n) (by nlinarith)).mono hw
      exact ⟨le_rfl, h2, hn, trivial, rfl, le_rfl⟩

end ComplexityTests.WordRAMRealizationBackend
