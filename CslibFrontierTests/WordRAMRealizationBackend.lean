/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: candidate

import CslibFrontier.DataStructure.Stack.Native
import CslibFrontier.Computability.WordRAM.Realization.Function

/-! The per-constructor backend on the array stack, `Stack.Native`. Three tags select the bodies
of `MemoryStack.realizes_push`, `realizes_pop` and `realizes_size`. The push carries a value and
answers `()`; its result encoding has no words, so the value is not echoed. The layout is a
runtime argument of every tag. -/

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
  Cslib.DataStructure.Queue Cslib.DataStructure.Stack.Native

namespace CslibFrontierTests.WordRAMRealizationBackend

-- A full stack rejects another push, while the largest fitting word remains a valid value.
example : ¬(Stack.spec 4 2).valid [4, 7] (.push 2) ∧ (Stack.spec 4 2).valid [] (.push 15) := by
  decide

-- The push value never selects code: every push runs the body of the `push` tag.
example (w C : ℕ) (L : Stack.Memory.Layout) :
    Backend.code certificates ((backend w C L).tag (.push 3)) =
      Backend.code certificates ((backend w C L).tag (.push 4)) := rfl

-- A push answers `()` through an empty result encoding; its value is not echoed.
example : (certificates .push).l = 0 := rfl

-- Every native execution from a represented stack takes the specified step, and its memory is
-- the method's final memory, so it writes only the layout's cells.
example {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C) {vs : List ℕ}
    {x y : Data (Backend.registers certificates)} {o : StackOp ℕ}
    {a : (Stack.spec w C).Result o} {n : ℕ} (hr : (implementation hL).rep vs x)
    (hv : (Stack.spec w C).valid vs o) (he : (backend w C L).exec w x o a y n) :
    a = ((Stack.spec w C).stepFn vs o).2 ∧ Modifies L.footprint x.mem y.mem := by
  refine ⟨((implementation hL).correct_ofFn hr hv he).1, ?_⟩
  have hm : memoryState (Backend.frontier certificates) y = (Memory.spec w).clientState
      (memoryState (Backend.frontier certificates) x) (Stack.Memory.methods L w C o) :=
    Backend.exec_memoryState (implements hL) hr hv he
  rw [← ((Backend.rep_iff _ _ _).mp hr).2.1] at hv
  have hmem := (Stack.Memory.modifies_methods hL o hv).1
  rw [← hm] at hmem
  exact hmem

/-- An empty stack of capacity two at address three, held in zero memory with the frontier at
six: the native data holding that memory state represents it. -/
theorem empty_rep : (implementation (Stack.Memory.valid_allocLayout (w := 4) (f := 3) (C := 2)
    (by decide))).rep [] (Backend.data certificates ⟨fun _ => 0, 6⟩) :=
  Backend.rep_data _ ⟨by decide, fun _ => fits_zero 4⟩ ⟨le_of_lt (by decide), le_rfl, by simp⟩
    (by simp [Stack.Memory.refinement, Stack.Memory.abs])

/-- An adaptive client chooses whether to pop from the observed size. -/
def stackClient : (Stack.spec 4 2).Client (Option ℕ × ℕ) :=
  .liftBind (.push 7) fun _ =>
    .liftBind .size fun (n : ℕ) =>
      if n = 1 then
        .liftBind .pop fun v => .liftBind .size fun (m : ℕ) => .pure (v, m)
      else .pure (none, n)

-- The native stack runs the client from the empty stack, one operation at a time: it pops the
-- pushed value, ends empty, and spends at most the constant `K` on each of its four calls.
example : ∃ K, ∃ y traces,
    Executes ((backend 4 2 ⟨⟨3, 1⟩, ⟨4, 2⟩⟩).exec 4) stackClient
        (Backend.data certificates ⟨fun _ => 0, 6⟩) (some 7, 0) y traces ∧
      total id traces ≤ 4 * K := by
  obtain ⟨K, hK⟩ := instruction_bound
  obtain ⟨y, traces, he, -, hb⟩ := Bound.exists_executes_const (hK _) stackClient empty_rep (by
    change (0 < 2 ∧ Fits 4 7) ∧ True ∧ True ∧ True ∧ True
    decide)
  exact ⟨K, y, traces, he, hb⟩

-- Two stacks with disjoint layouts: product operations select tags of `Tag ⊕ Tag`.
example {w C : ℕ} {L₁ L₂ : Stack.Memory.Layout} (h₁ : L₁.Valid w C) (h₂ : L₂.Valid w C) :
    ((backend w C L₁).sum (backend w C L₂)).Implements
      ((Stack.Memory.framed h₁).prod (Stack.Memory.framed h₂)).toRefinement :=
  (implements h₁).prod (frame₁ := Memory.Framed.prod_frame_left _ _)
    (frame₂ := Memory.Framed.prod_frame_right _ _) (implements h₂)

-- Doubling at every width of at least `2 * (log₂ n + 1)` bits, as one flat program.
example : UniformComputableInPolyTime .standard (fun n => n + n) (fun _ n => [n]) id :=
  (Realizes.addWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding 0 0).uniformComputableInPolyTime
    .exactStandard 0 (.const 3) 2 (by decide) (inputAdmissible_of_widthIndependent _ _)
    (fun _ _ j => by fin_cases j; rfl)
    fun n w hw _ => by
      have h2 : Fits w 2 := (show Fits 2 2 by decide).mono (le_trans (by simp [logWidth]) hw)
      have hn : Fits w (n + n) := (fits_of_lt_pow (k := 2) (n := n) (by nlinarith)).mono hw
      exact ⟨le_rfl, h2, hn, trivial, rfl, le_rfl⟩

end CslibFrontierTests.WordRAMRealizationBackend
