/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Client.MemoryStack
public import CslibFrontier.Computability.WordRAM.Realization.Backend
public import CslibFrontier.Computability.WordRAM.Realization.Function
import CslibFrontier.Tactic.Realize

/-!
# An adaptive stack client compiled to one word-RAM program

The client pushes its input and pops it; if the answer is zero, it pushes one and pops again. It
computes `max n 1`. Over the memory oracle it is `program`: allocate a stack of capacity one, then
run the client's calls through `Stack.Memory`'s methods (`run_eq_link`). The refinement of
`Stack.Memory` transfers the abstract client's answer, admissibility and cost to `program`
(`program_spec`). `realize` certifies `program` as one uniform native emitter
(`realizes_program`), and the argument-installation prefix with a halt makes it a flat program.
No instruction is stepped by hand.

## Main definitions

* `client`: the adaptive client over the bounded stack of capacity one.
* `run`, `program`: its calls on a stack's layout, and the allocating memory program.
* `positive`: the word-valued function `max n 1`.

## Main results

* `run_eq_link`: `run` is the client linked to the stack's methods.
* `program_spec`: the answer, the admissible memory history and the memory cost.
* `realizes_program`: the native certificate.
* `positive_polytime`: one flat program computes `positive` in constant, hence polynomial, time.

## References

The stack is `Stack.Memory`. This example is a composition test, not a new stack algorithm.
-/

namespace Cslib.DataStructure.Stack.Controller

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Realization.MemoryStack
  Cslib.DataStructure.Queue

/-- Push the input and pop it; replace a zero answer by another push and pop of one. -/
public def client (w n : ℕ) : (Stack.spec w 1).Client ℕ :=
  .liftBind (.push n) fun _ => .liftBind .pop fun
    | none => .pure 0
    | some v => if v = 0 then
        .liftBind (.push 1) fun _ => .liftBind .pop fun
          | none => .pure 0
          | some u => .pure u
      else .pure v

/-- The client's calls on the stack at `L`. -/
public def run (L : Stack.Memory.Layout) (n : ℕ) : Memory.Prog ℕ := do
  Stack.Memory.push L n
  match ← Stack.Memory.pop L with
  | none => pure 0
  | some v =>
    if v = 0 then
      (do
        Stack.Memory.push L 1
        match ← Stack.Memory.pop L with
        | none => pure 0
        | some u => pure u)
    else pure v

/-- Allocate a stack of capacity one and run the client on it. -/
public def program (n : ℕ) : Memory.Prog ℕ := do
  let L ← Stack.Memory.allocLayout 1
  run L n

/-- `run` is the client linked to the stack's methods. -/
public theorem run_eq_link (L : Stack.Memory.Layout) (w n : ℕ) :
    run L n = link (Stack.Memory.methods L w 1) (client w n) := by
  refine congrArg (Stack.Memory.push L n >>= ·) (funext fun _ => ?_)
  refine congrArg (Stack.Memory.pop L >>= ·) (funext fun a => ?_)
  rcases a with _ | v
  · rfl
  · by_cases hv : v = 0
    · simp only [hv, ↓reduceIte]
      refine congrArg (Stack.Memory.push L 1 >>= ·) (funext fun _ => ?_)
      refine congrArg (Stack.Memory.pop L >>= ·) (funext fun b => ?_)
      cases b <;> rfl
    · simp only [hv, ↓reduceIte]
      rfl

/-- The word-valued function computed by the client. -/
public def positive (n : ℕ) : ℕ := max n 1

local instance : WordEncoding Stack.Memory.Layout := ⟨4, layoutWords⟩

/-- **The native certificate.** One uniform emitter, chosen before every width, input and
memory, runs `program` from any memory whose frontier leaves room for the stack. -/
public theorem realizes_program : Realizes .exact program
    (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding
    (fun w _ s => Fits w (s.frontier + 2)) (fun _ _ => 0) := by
  realize
  all_goals
    try simp only [show (Memory.spec 0).clientResult s (Stack.Memory.allocLayout 1) =
        ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, 1⟩⟩ from rfl,
      show (Memory.spec 0).clientState s (Stack.Memory.allocLayout 1) =
        ⟨clear s.mem s.frontier 1, s.frontier + 1 + 1⟩ from rfl,
      clear_of_owns (show (Block.mk s.frontier 1).Owns s.frontier from ⟨le_rfl, by simp⟩),
      StateTransitionSpec.clientState, StateTransitionSpec.clientResult,
      Stack.Memory.runClient_push, Stack.Memory.runClient_pop_of_pos, Nat.zero_add,
      Nat.add_zero, Nat.sub_self, ne_eq, Nat.one_ne_zero, not_false_eq_true,
      Function.update_self]
    first | exact le_rfl | exact h.of_le (by omega)

/-- The abstract client is admissible when its two values fit. -/
private theorem validHistory_client {w n : ℕ} (h1 : Fits w 1) (hn : Fits w n) :
    (Stack.spec w 1).ValidHistory [] ((Stack.spec w 1).clientHistory [] (client w n)) := by
  by_cases hn0 : n = 0 <;>
    simp [StateTransitionSpec.clientHistory, client, -PFunctor.FreeM.pure_eq_pure, hn0, hn, h1]

/-- The abstract client computes `positive`. -/
private theorem clientResult_client (w n : ℕ) :
    (Stack.spec w 1).clientResult [] (client w n) = positive n := by
  by_cases hn0 : n = 0
  · simp [StateTransitionSpec.clientResult, client, positive, -PFunctor.FreeM.pure_eq_pure, hn0]
  · simp [StateTransitionSpec.clientResult, client, positive, -PFunctor.FreeM.pure_eq_pure, hn0,
      max_eq_left (show 1 ≤ n by omega)]

/-- The abstract client issues at most four stack calls. -/
private theorem length_clientHistory_client (w n : ℕ) :
    ((Stack.spec w 1).clientHistory [] (client w n)).length ≤ 4 := by
  by_cases hn0 : n = 0 <;>
    simp [StateTransitionSpec.clientHistory, client, -PFunctor.FreeM.pure_eq_pure, hn0]

/-- **Correctness through the refinement.** From a memory whose frontier leaves room, `program`
returns `positive n`, its memory history is admissible, and it costs at most fifteen memory
units: two for the allocation and three for each of at most four stack calls. -/
public theorem program_spec {w n : ℕ} {s : Memory.State} (hf : Fits w (s.frontier + 2))
    (hn : Fits w n) :
    (Memory.spec w).clientResult s (program n) = positive n ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (program n)) ∧
      memoryCost (program n) s ≤ 15 := by
  let L : Stack.Memory.Layout := ⟨⟨s.frontier, 1⟩, ⟨s.frontier + 1, 1⟩⟩
  have hL : L.Valid w 1 := Stack.Memory.valid_allocLayout hf
  obtain ⟨hinv, habs⟩ := Stack.Memory.inv_allocLayout (C := 1) s
  have hv := validHistory_client hL.capacity_fits hn
  rw [← habs] at hv
  have hlink : (Stack.Memory.refinement hL).methods = Stack.Memory.methods L w 1 := rfl
  have habs' : (Stack.Memory.refinement hL).abs = Stack.Memory.abs L := rfl
  obtain ⟨hvE, hres, -, -⟩ := (Stack.Memory.refinement hL).simulates_client (client w n) hinv hv
  have hcost := (show (Stack.Memory.refinement hL).Amortized Memory.charge
    (fun _ _ => 3) (fun _ => 0) from Stack.Memory.amortized hL).client (client w n) hinv hv
  rw [hlink, ← run_eq_link] at hvE hres hcost
  rw [habs', habs] at hres hcost
  have hrun := Stack.Memory.runClient_allocLayout_bind (w := w) 1 (fun L => run L n) s
  refine ⟨?_, ?_, ?_⟩
  · simp only [StateTransitionSpec.clientResult, program] at hres ⊢
    rw [hrun, hres]
    exact clientResult_client w n
  · simp only [StateTransitionSpec.clientHistory, program] at hvE ⊢
    rw [hrun]
    exact ⟨hf.of_le (by omega), hf, hvE⟩
  · rw [StateTransitionSpec.totalCost_const] at hcost
    have hlen := length_clientHistory_client w n
    rw [memoryCost_eq_totalCost w]
    simp only [StateTransitionSpec.clientHistory, program]
    rw [hrun]
    change 2 + (1 + (Memory.spec w).totalCost Memory.charge ⟨clear s.mem s.frontier 1,
      s.frontier + 1 + 1⟩ ((Memory.spec w).clientHistory ⟨clear s.mem s.frontier 1,
        s.frontier + 1 + 1⟩ (run L n))) ≤ 15
    omega

/-- The client, compiled to one flat word-RAM program, computes `positive` in constant time at
every width of at least three bits per input bit. -/
@[fun_prop]
public theorem positive_polytime :
    UniformComputableInPolyTime .standard positive (fun _ n => [n]) id :=
  realizes_program.uniformComputableInPolyTime .exactStandard 0 (.const 15) 3 (by decide)
    (fun _ _ j => by fin_cases j; rfl) fun n w hw hin => by
      have h4 : Fits w 4 := (show Fits 3 4 by decide).mono (le_trans (by simp [logWidth]) hw)
      have hroom : Fits w ((inputState [n]).frontier + 2) := h4.of_le (by simp [inputState])
      have hp := program_spec hroom (hin.2 n (by simp))
      refine ⟨by simp, h4.of_le (by simp), hroom, hp.2.1, ?_, by have := hp.2.2; omega⟩
      simpa only [Equiv.coe_toEmbedding, Equiv.funUnique_symm_apply, uniqueElim_const] using hp.1

end Cslib.DataStructure.Stack.Controller
