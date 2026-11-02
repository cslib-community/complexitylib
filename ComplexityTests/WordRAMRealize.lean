/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.WordRAM.Realization.Client.MemoryStack
import Complexity.Computability.WordRAM.Realization.Program
import Complexity.DataStructure.Queue.Memory
import Complexity.Tactic.Realize

/-! `realize` on the memory-oracle stack and queue, matches, loops and failures.

The three stack statements are exactly those of `Realization.MemoryStack` (#2246), including
their local-work gradings; `realize` replaces the hand-assembled bind trees and leaves only the
fit and domain conditions. The queue's enqueue runs through `link` and the pair of stacks. The
failure tests pin the messages for unsupported forms. -/

namespace ComplexityTests.WordRAMRealize

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open MemoryStack

/-! ## The stack methods -/

example : Realizes .exact Stack.Memory.size layoutWords
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

example : Realizes .exact (fun d : Stack.Memory.Layout × ℕ => Stack.Memory.push d.1 d.2)
    pushWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
    (fun w d s => d.1.Valid w d.1.items.length ∧ Stack.Memory.Inv d.1 s ∧
      s.mem d.1.count.base < d.1.items.length) (fun _ _ => 10) := by
  realize
  · exact hmem.fits_of_lt_frontier (h.2.1.item_lt h.2.2)
  · exact h.1.capacity_fits.of_le (by omega)

example : Realizes .exact Stack.Memory.pop layoutWords optionWords
    (fun w L s => L.Valid w L.items.length ∧ Stack.Memory.Inv L s) (fun _ _ => 19) := by
  realize
  · omega
  · exact hmem.fits_of_lt_frontier (h.2.item_lt (by have := h.2.count_le; omega))
  · exact h.1.count_length ▸ hwords 1

/-! ## The queue's enqueue, through `link` and the pair of stacks -/

/-- Both stack layouts, front first. -/
def queueWords : Stack.Memory.Layout × Stack.Memory.Layout ↪ (Fin 8 → ℕ) :=
  (layoutWords.prodMap layoutWords).trans (Fin.appendEquiv 4 4).toEmbedding

/-- Both layouts and the enqueued value. -/
def enqueueWords : (Stack.Memory.Layout × Stack.Memory.Layout) × ℕ ↪ (Fin 9 → ℕ) :=
  (queueWords.prodMap (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans
    (Fin.appendEquiv 8 1).toEmbedding

example (w₀ C : ℕ) : Realizes .exact
    (fun d : (Stack.Memory.Layout × Stack.Memory.Layout) × ℕ =>
      (Queue.Memory.memMethods d.1.1 d.1.2 w₀ C (.enqueue d.2) : Memory.Prog Unit))
    enqueueWords (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
    (fun w d s => d.1.2.Valid w d.1.2.items.length ∧ Stack.Memory.Inv d.1.2 s ∧
      s.mem d.1.2.count.base < d.1.2.items.length) (fun _ _ => 0) := by
  realize
  · exact hmem.fits_of_lt_frontier (h.2.1.item_lt h.2.2)
  · exact h.1.capacity_fits.of_le (by omega)

/-! ## A `match` on an optional answer -/

/-- Pop and return the successor of the top, or zero for an empty stack. -/
def popSucc (L : Stack.Memory.Layout) : Memory.Prog ℕ := do
  match ← Stack.Memory.pop L with
  | none => pure 0
  | some v => pure (v + 1)

/-- The `none` branch needs nothing; the `some` branch needs the successor to fit. -/
example : Realizes .exact popSucc layoutWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (fun w L s => L.Valid w L.items.length ∧ Stack.Memory.Inv L s ∧
      ∀ a < s.mem L.count.base, Fits w (s.mem (L.items.base + a) + 1)) (fun _ _ => 0) := by
  realize
  · omega
  · exact hmem.fits_of_lt_frontier (h.2.1.item_lt (by have := h.2.1.count_le; omega))
  · exact h.1.count_length ▸ hwords 1
  · by_cases hz : s.mem d.count.base = 0
    · simp [StateTransitionSpec.clientResult, Stack.Memory.runClient_pop_of_eq_zero _ s hz] at hc
    · simpa [StateTransitionSpec.clientResult, Stack.Memory.runClient_pop_of_pos _ s hz] using
        h.2.2 _ (Nat.sub_lt (Nat.pos_of_ne_zero hz) Nat.one_pos)

/-! ## The standard basis and computed addresses -/

/-- Read the cell after a computed address, then store a product there. -/
def scaled (d : ℕ × ℕ) : Memory.Prog Unit := do
  let x ← Memory.read (d.1 + 1)
  Memory.write (d.1 + 1) (x * d.2 - d.2)

/-- Standard-basis subtraction is total, so only the fit of the sum and the product remain. -/
example : Realizes .standard scaled
    ((Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding.prodMap
      (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding |>.trans (Fin.appendEquiv 1 1).toEmbedding)
    (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
    (fun w d s => Fits w (d.1 + 1) ∧ Fits w (s.mem (d.1 + 1) * d.2)) (fun _ _ => 0) := by
  realize
  · exact h.1
  · exact h.2

/-! ## Loops -/

/-- Two words. -/
abbrev pairWords : ℕ × ℕ ↪ (Fin 2 → ℕ) :=
  ((Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding.prodMap
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding).trans (Fin.appendEquiv 1 1).toEmbedding

/-- Follow `n` pointers from `start`. -/
def chase (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate (fun x : ℕ × ℕ => Memory.read x.2) d.1 d.2 d.1

/-- The loop receives a component of the environment; its domains are trivial. -/
example : Realizes .exact chase pairWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Add the cell at `base + i` and advance. -/
def sumStep (x : ℕ × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) := do
  let v ← Memory.read (x.1 + x.2.1)
  pure (x.2.1 + 1, x.2.2 + v)

/-- Sum `n` cells from `base`, returning the final index and the sum. -/
def sumCells (d : ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := iterate sumStep d.1 d.2 (0, 0)

/-- The loop's domain is the step's fit conditions along the iterations. -/
example : Realizes .exact sumCells pairWords pairWords
    (fun w d s => iterationSafe (fun x => sumStep (x.1.1, x.2))
      (fun w x s => Fits w (x.1.1 + x.2.1) ∧ Fits w (x.2.1 + 1) ∧
        Fits w (x.2.2 + s.mem (x.1.1 + x.2.1))) w d d.2 (0, 0) s) (fun _ _ => 0) := by
  realize
  exact h

/-! ## A whole stack client, to a flat Word-RAM program

The client allocates a stack, pushes and pops. `realize` certifies it, allocation included; the
only work left is evaluating the allocation. `exists_init_program` then gives a flat program on the
native list input whose output is the encoding of `some v`, within a constant number of steps.
No instruction is stepped by hand. -/

/-- The four layout words, for a bind that returns a layout. -/
instance : WordEncoding Stack.Memory.Layout := ⟨4, layoutWords⟩

/-- Allocate a stack of capacity `c`, push `v`, and pop. -/
def roundTrip (d : ℕ × ℕ) : Memory.Prog (Option ℕ) := do
  let L ← Stack.Memory.allocLayout d.1
  Stack.Memory.push L d.2
  Stack.Memory.pop L

/-- The certificate. -/
theorem roundTrip_realizes : Realizes .exact roundTrip pairWords optionWords
    (fun w d s => Fits w (s.frontier + 1 + d.1)) (fun _ _ => 0) := by
  realize
  all_goals
    try simp only [show (Memory.spec 0).clientResult s (Stack.Memory.allocLayout d.1) =
        ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, d.1⟩⟩ from rfl,
      show (Memory.spec 0).clientState s (Stack.Memory.allocLayout d.1) =
        ⟨clear s.mem s.frontier 1, s.frontier + 1 + d.1⟩ from rfl,
      StateTransitionSpec.clientState, Stack.Memory.runClient_push,
      clear_of_owns (show (Block.mk s.frontier 1).Owns s.frontier from ⟨le_rfl, by simp⟩),
      Function.update_self] at *
  all_goals first | exact h.of_le (by omega) | omega

/-- From `State.init [c, v]`, the flat program outputs the encoding of `some v` within
`10 C + 1` steps, for one exchange factor `C`. -/
theorem roundTrip_program : ∃ n C : ℕ,
    ∃ emit : ∀ {r : ℕ}, (frontier : Fin r) → (Fin 2 → Fin r) → (Fin (2 + n + 1) → Fin r) →
      Code .exact r,
      ∀ {r : ℕ} (frontier : Fin r) (src : Fin 2 → Fin r) (tmp : Fin (2 + n + 1) → Fin r),
        Function.Injective src → Function.Injective tmp → (∀ i j, src i ≠ tmp j) →
        (∀ j, tmp j ≠ frontier) → (∀ i, src i ≠ frontier) →
        ∀ (i : Fin 2) (w c v : ℕ), 1 ≤ c → Fits w (c + 4) → Fits w v →
          ∃ t, Executes w ((Code.seq (inputPrefix frontier (tmp (Fin.last (2 + n))) src)
              (emit frontier src tmp)).program (tmp (Fin.castAdd (n + 1) i)))
            (State.init [c, v]) (optionWords (some v) i) t ∧ t ≤ C * 10 + 1 := by
  obtain ⟨n, C, emit, he⟩ := roundTrip_realizes.exists_init_program (fun d => [d.1, d.2])
    (by intro d i; fin_cases i <;> rfl)
  refine ⟨n, C, emit, fun frontier src tmp hsrc htmp hd hf hs i w c v hc1 hc hv => ?_⟩
  have h3 : Fits w 3 := hc.of_le (by omega)
  have hvalid : (Memory.spec w).ValidHistory (inputState [c, v])
      ((Memory.spec w).clientHistory (inputState [c, v]) (roundTrip (c, v))) := by
    change (Memory.spec w).ValidHistory (inputState [c, v])
      [.alloc 1, .allocDirty c, .read 3, .write 4 v, .write 3 1, .read 3, .read 4, .write 3 0]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · change Fits w (3 + 1)
      exact hc.of_le (by omega)
    · change Fits w (3 + 1 + c)
      exact hc.of_le (by omega)
    · change 3 < 3 + 1 + c
      omega
    · exact ⟨show 4 < 3 + 1 + c by omega, hv⟩
    · exact ⟨show 3 < 3 + 1 + c by omega, h3.of_le (by omega)⟩
    · change 3 < 3 + 1 + c
      omega
    · change 4 < 3 + 1 + c
      omega
    · exact ⟨show 3 < 3 + 1 + c by omega, fits_zero w⟩
  obtain ⟨t, ht, hle⟩ := he frontier src tmp hsrc htmp hd hf hs i w (c, v) le_rfl h3
    ⟨h3.of_le (by simp), fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      exacts [hc.of_le (by omega), hv]⟩
    (hc.of_le (by simp [inputState]; omega)) hvalid
  exact ⟨t, ht, hle.trans (by rfl)⟩

/-! ## Failure messages -/

/-- A power has no glue rule. -/
def square (n : ℕ) : Memory.Prog ℕ := pure (n ^ 2)

/--
error: realize: cannot compute
  d ^ 2
from the live words
  d
-/
#guard_msgs in
example : Realizes .exact square (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- A non-strict comparison is not a native test. -/
def atMost (n : ℕ) : Memory.Prog ℕ := if n ≤ 3 then pure 0 else pure 1

/--
error: realize: a branch condition must be `a = b`, `a < b` or `a > b` on words, got
  d ≤ 3
-/
#guard_msgs in
example : Realizes .exact atMost (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Recursion on a runtime value is a loop. -/
def readMany : ℕ → Memory.Prog Unit
  | 0 => pure ()
  | n + 1 => do let _ ← Memory.read 0; readMany n

/--
error: realize: unsupported client form
  readMany d
Expected `bind`, `pure`, a memory query, `if` on a word comparison,
or a `match` on an optional answer. Recursion on a runtime value is a loop
and needs a loop rule.
-/
#guard_msgs in
example : Realizes .exact readMany (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- A loop without a query has no memory charge to pay for its iterations. -/
def countUp (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate (fun x : (ℕ × ℕ) × ℕ => pure (x.2 + 1)) d d.2 0

/--
error: realize: a loop body must begin with a memory query, which pays for the iteration;
the body begins with
  PFunctor.FreeM.pure (x.2 + 1)
-/
#guard_msgs in
example : Realizes .exact countUp pairWords (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/-- Allocation is certified in the exact basis. -/
def fresh (n : ℕ) : Memory.Prog ℕ := Memory.alloc n

/--
error: realize: allocation is certified in the exact basis;
realize there and transfer with `Realizes.mapSimulates`
-/
#guard_msgs in
example : Realizes .standard fresh (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (fun _ _ _ => True) (fun _ _ => 0) := by
  realize

/--
error: realize: the goal is not a `Realizes` certificate:
  True
-/
#guard_msgs in
example : True := by
  realize

end ComplexityTests.WordRAMRealize
