/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Heap
public import Complexity.Computability.WordRAM.Realization.Client.MemoryStack
public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.StateTransition.Resource

/-!
# The array stack on the word RAM

`Stack.Memory` implements the bounded stack `Stack.spec w C` by three memory programs. Here each
program runs as native code. The uniform realizations `MemoryStack.realizes_push`,
`realizes_pop` and `realizes_size` supply one static body per operation, chosen before every
width, capacity, layout and value; no instruction is stepped by hand. The operation's
constructor selects the body, and a push value is delivered to a register beforehand, uncharged,
as in a calling convention. The client between operations stays outside the machine; a whole
client compiles to one flat program when `realize` certifies it (`Stack.Controller`).

The native data represents a stack when its registers hold the layout words and the frontier,
and its memory satisfies the invariant of `Stack.Memory` and abstracts to the stack. Correctness
is that of `Stack.Memory.refinement`, transported through the realizations' whole-memory
postcondition. Every operation runs within one constant number of instructions
(`instruction_bound`), so an adaptive client with `m` operations runs within `m` times that
constant (`run_client`). Each operation writes only the layout's cells (`modifies`, `frame`).

## Main definitions

* `registers`, `frontier`, `layoutReg`, `arg`: the register file.
* `body`, `prepare`, `result`, `exec`: the native body of each operation, argument delivery,
  the decoded answer, and the execution relation.
* `Rep`: native data representing a stack.
* `implementation`: the native stack.
* `initialLayout`, `initial`: an empty stack at a fixed address, as a calling-convention state.

## Main results

* `instruction_bound`: a constant bound on the instructions of every operation.
* `run_client`: adaptive clients, with a bound linear in the number of operations.
* `modifies`, `frame`: operations write only the layout's cells.
* `initial_rep`: the initial state represents the empty stack.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*,
  Section 10.1][CLRS2009]
-/

namespace Cslib.DataStructure.Stack.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.WordRAM.Realization.MemoryStack
  Cslib.DataStructure.Queue

private noncomputable def slots : ℕ :=
  (1 + realizes_size.scratchSize + 1) + (0 + realizes_push.scratchSize + 1) +
    (2 + realizes_pop.scratchSize + 1)

/-- One register count, selected before every width, layout, operation and value. -/
public noncomputable def registers : ℕ := slots + 6

/-- Register zero holds the allocation frontier. -/
public noncomputable def frontier : Fin registers := ⟨0, by unfold registers; omega⟩

/-- Registers one to four hold the layout words. -/
public noncomputable def layoutReg (i : Fin 4) : Fin registers :=
  ⟨i.val + 1, by unfold registers; omega⟩

/-- Register five receives a push value. -/
public noncomputable def arg : Fin registers := ⟨5, by unfold registers; omega⟩

private noncomputable def pushSrc (i : Fin 5) : Fin registers :=
  ⟨i.val + 1, by unfold registers; omega⟩

private noncomputable def tmp {n : ℕ} (hn : n ≤ slots) (i : Fin n) : Fin registers :=
  ⟨i.val + 6, by have := i.isLt; unfold registers; omega⟩

private theorem sizeSlots : 1 + realizes_size.scratchSize + 1 ≤ slots := by unfold slots; omega
private theorem pushSlots : 0 + realizes_push.scratchSize + 1 ≤ slots := by unfold slots; omega
private theorem popSlots : 2 + realizes_pop.scratchSize + 1 ≤ slots := by unfold slots; omega

private theorem layout {k n : ℕ} (src : Fin k → Fin registers)
    (hsrc : ∀ i, 1 ≤ (src i).val ∧ (src i).val < 6) (hn : n ≤ slots) :
    Function.Injective (tmp hn) ∧ (∀ i j, src i ≠ tmp hn j) ∧
      (∀ j, tmp hn j ≠ frontier) ∧ (∀ i, src i ≠ frontier) := by
  refine ⟨fun i j h => Fin.ext (by have := congrArg Fin.val h; simp only [tmp] at this; omega),
    fun i j h => ?_, fun j h => ?_, fun i h => ?_⟩
  · have := congrArg Fin.val h
    have := hsrc i
    simp only [tmp] at *
    omega
  · have := congrArg Fin.val h
    simp only [tmp, frontier] at this
    omega
  · have := congrArg Fin.val h
    have := hsrc i
    simp only [frontier] at *
    omega

/-- The static body of each operation; arguments and runtime layouts never select code. -/
public noncomputable def body : StackOp ℕ → Code .exact registers
  | .push _ => realizes_push.code frontier pushSrc (tmp pushSlots)
  | .pop => realizes_pop.code frontier layoutReg (tmp popSlots)
  | .size => realizes_size.code frontier layoutReg (tmp sizeSlots)

/-- Deliver a push value to `arg`; the other operations take no argument. -/
public noncomputable def prepare : StackOp ℕ → Data registers → Data registers
  | .push v, x => x.set arg v
  | .pop, x => x
  | .size, x => x

/-- The answer, read from the result registers: a presence tag and a payload for a pop, a word
for a size. Decoding executes no instruction. -/
public noncomputable def result : (o : StackOp ℕ) → Data registers → (stack ℕ).Result o
  | .push _, _ => ()
  | .pop, y =>
    if y.regs (tmp popSlots (Fin.castAdd (realizes_pop.scratchSize + 1) (0 : Fin 2))) = 0 then none
    else some (y.regs (tmp popSlots (Fin.castAdd (realizes_pop.scratchSize + 1) (1 : Fin 2))))
  | .size, y => y.regs (tmp sizeSlots (Fin.castAdd (realizes_size.scratchSize + 1) (0 : Fin 1)))

/-- An operation executes its body from the prepared data, in the counted number of
instructions, and returns the decoded answer. -/
public noncomputable def exec (w C : ℕ) : Execution (Stack.spec w C) (Data registers) ℕ :=
  fun x o a y n => Exec w (body o) (prepare o x) y n ∧ a = result o y

/-- Native data represents the stack `vs` on layout `L`: the layout is well formed, its words
sit in `layoutReg`, all words are bounded, and the memory with the frontier register satisfies
the invariant of `Stack.Memory` and abstracts to `vs`. -/
public structure Rep (w C : ℕ) (L : Stack.Memory.Layout) (vs : List ℕ) (x : Data registers) :
    Prop where
  /-- The layout is well formed for capacity `C`. -/
  valid : L.Valid w C
  /-- The layout words sit in their registers. -/
  layout : ∀ i, x.regs (layoutReg i) = layoutWords L i
  /-- Every register and cell holds a word. -/
  bounded : x.Bounded w
  /-- The memory satisfies the invariant. -/
  inv : Stack.Memory.Inv L (memoryState frontier x)
  /-- The memory holds `vs`. -/
  abs_eq : Stack.Memory.abs L (memoryState frontier x) = vs

private theorem step_methods {w C : ℕ} {L : Stack.Memory.Layout} (hL : L.Valid w C)
    {s : Memory.State} (hs : Stack.Memory.Inv L s) {o : StackOp ℕ}
    (hv : (Stack.spec w C).valid (Stack.Memory.abs L s) o) :
    (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (Stack.Memory.methods L w C o)) ∧
      (Stack.spec w C).stepFn (Stack.Memory.abs L s) o =
        (Stack.Memory.abs L ((Memory.spec w).clientState s (Stack.Memory.methods L w C o)),
          (Memory.spec w).clientResult s (Stack.Memory.methods L w C o)) ∧
      Stack.Memory.Inv L ((Memory.spec w).clientState s (Stack.Memory.methods L w C o)) := by
  have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
    ((Stack.Memory.refinement hL).valid o hs hv)
  obtain ⟨hstep, hinv⟩ := (Stack.Memory.refinement hL).correct o hs hv
    ((Memory.spec w).clientRun_canonical s _ hvalid)
  exact ⟨hvalid, (((Stack.spec w C).step_iff_stepFn _ _ _ _).mp hstep).symm, hinv⟩

private theorem memoryCost_methods_le (L : Stack.Memory.Layout) (w C : ℕ) (o : StackOp ℕ)
    (s : Memory.State) : memoryCost (Stack.Memory.methods L w C o) s ≤ 3 := by
  cases o with
  | push v => exact le_of_eq rfl
  | pop =>
    by_cases h : s.mem L.count.base = 0
    · simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.methods,
        Stack.Memory.runClient_pop_of_eq_zero, h, StateTransitionSpec.totalCost, Memory.charge]
    · simp [memoryCost, StateTransitionSpec.clientHistory, Stack.Memory.methods,
        Stack.Memory.runClient_pop_of_pos, h, StateTransitionSpec.totalCost, Memory.charge]
  | size => exact Nat.le_succ_of_le (Nat.le_succ_of_le le_rfl)

private noncomputable def factor : ℕ :=
  max (max realizes_size.factor realizes_push.factor) realizes_pop.factor

private theorem optionWords_decode (a : Option ℕ) :
    (if optionWords a 0 = 0 then none else some (optionWords a 1)) = a := by
  cases a <;> simp

private theorem layoutReg_ne_tmp {n : ℕ} (hn : n ≤ slots) (i : Fin 4) (j : Fin n) :
    tmp hn j ≠ layoutReg i := by
  intro h
  have := congrArg Fin.val h
  simp only [tmp, layoutReg] at this
  omega

private theorem layoutReg_ne_frontier (i : Fin 4) : layoutReg i ≠ frontier := by
  intro h
  have := congrArg Fin.val h
  simp only [layoutReg, frontier] at this
  omega

private theorem layoutReg_ne_arg (i : Fin 4) : layoutReg i ≠ arg := by
  intro h
  have := congrArg Fin.val h
  simp only [layoutReg, arg] at this
  have := i.isLt
  omega

private theorem prepare_memoryState (o : StackOp ℕ) (x : Data registers) :
    memoryState frontier (prepare o x) = memoryState frontier x := by
  cases o with
  | push v =>
    have h : arg ≠ frontier := by
      intro h
      have := congrArg Fin.val h
      simp only [arg, frontier] at this
      omega
    exact Memory.State.ext rfl (Function.update_of_ne h.symm v x.regs)
  | pop | size => rfl

private theorem prepare_layout (o : StackOp ℕ) (x : Data registers) (i : Fin 4) :
    (prepare o x).regs (layoutReg i) = x.regs (layoutReg i) := by
  cases o with
  | push v => exact Function.update_of_ne (layoutReg_ne_arg i) _ _
  | pop | size => rfl

/-- One operation's body, from represented data: its instruction count, memory, answer and
preserved layout registers. -/
private theorem exists_body {w C : ℕ} {L : Stack.Memory.Layout} {vs : List ℕ}
    {x : Data registers} (hr : Rep w C L vs x) (o : StackOp ℕ)
    (hv : (Stack.spec w C).valid vs o) :
    ∃ y n, Exec w (body o) (prepare o x) y n ∧ n ≤ factor * 23 ∧
      memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x)
        (Stack.Memory.methods L w C o) ∧
      result o y = (Memory.spec w).clientResult (memoryState frontier x)
        (Stack.Memory.methods L w C o) ∧
      y.Bounded w ∧ ∀ i, y.regs (layoutReg i) = x.regs (layoutReg i) := by
  have hL := hr.valid
  have hC := hL.items_length
  rw [← hr.abs_eq] at hv
  have hvalid := (step_methods hL hr.inv hv).1
  have hcost := memoryCost_methods_le L w C o (memoryState frontier x)
  have hregs : x.regs ∘ layoutReg = layoutWords L := funext hr.layout
  cases o with
  | push v =>
    obtain ⟨hlen, hfit⟩ := hv
    rw [Stack.Memory.length_abs] at hlen
    have hb : (prepare (.push v) x).Bounded w := hr.bounded.set hfit
    have hp := prepare_memoryState (.push v) x
    obtain ⟨hi, hd, hf, hs⟩ := layout pushSrc (fun i => by simp only [pushSrc]; omega) pushSlots
    have hin : (prepare (.push v) x).regs ∘ pushSrc = pushWords (L, v) := by
      funext i
      fin_cases i
      · exact (prepare_layout _ x 0).trans (hr.layout 0)
      · exact (prepare_layout _ x 1).trans (hr.layout 1)
      · exact (prepare_layout _ x 2).trans (hr.layout 2)
      · exact (prepare_layout _ x 3).trans (hr.layout 3)
      · exact Function.update_self arg v x.regs
    obtain ⟨y, ⟨n, hn, he⟩, hm, _, hframe⟩ :=
      (realizes_push.code_spec frontier _ _ hi hd hf hs).2 w (L, v) _ hb hin
        ⟨hC ▸ hL, hp ▸ hr.inv, by
          change (memoryState frontier (prepare (.push v) x)).mem L.count.base < L.items.length
          rw [hp]; omega⟩ (by rw [hp]; exact hvalid)
    rw [hp] at hn hm
    have hc : memoryCost (Stack.Memory.push (L, v).1 (L, v).2) (memoryState frontier x) ≤ 3 :=
      hcost
    refine ⟨y, n, he, hn.trans ?_, hm, rfl, he.bounded hb, fun i => ?_⟩
    · exact Nat.mul_le_mul (by unfold factor; omega) (by omega)
    · rw [hframe _ (layoutReg_ne_frontier i) (fun j => layoutReg_ne_tmp _ i j)]
      exact prepare_layout _ x i
  | pop =>
    obtain ⟨hi, hd, hf, hs⟩ := layout layoutReg (fun i => by simp only [layoutReg]; omega)
      popSlots
    obtain ⟨y, ⟨n, hn, he⟩, hm, hout, hframe⟩ :=
      (realizes_pop.code_spec frontier _ _ hi hd hf hs).2 w L x hr.bounded hregs
        ⟨hC ▸ hL, hr.inv⟩ hvalid
    have hc : memoryCost (Stack.Memory.pop L) (memoryState frontier x) ≤ 3 := hcost
    refine ⟨y, n, he, hn.trans ?_, hm, ?_, he.bounded hr.bounded, fun i => ?_⟩
    · exact Nat.mul_le_mul (by unfold factor; omega) (by omega)
    · simp only [result, hout]
      exact optionWords_decode _
    · exact hframe _ (layoutReg_ne_frontier i) (fun j => layoutReg_ne_tmp _ i j)
  | size =>
    obtain ⟨hi, hd, hf, hs⟩ := layout layoutReg (fun i => by simp only [layoutReg]; omega)
      sizeSlots
    obtain ⟨y, ⟨n, hn, he⟩, hm, hout, hframe⟩ :=
      (realizes_size.code_spec frontier _ _ hi hd hf hs).2 w L x hr.bounded hregs trivial
        hvalid
    have hc : memoryCost (Stack.Memory.size L) (memoryState frontier x) ≤ 3 := hcost
    refine ⟨y, n, he, hn.trans ?_, hm, hout 0, he.bounded hr.bounded, fun i => ?_⟩
    · exact Nat.mul_le_mul (by unfold factor; omega) (by omega)
    · exact hframe _ (layoutReg_ne_frontier i) (fun j => layoutReg_ne_tmp _ i j)

/-- The native stack on layout `L`. -/
public noncomputable def implementation (w C : ℕ) (L : Stack.Memory.Layout) :
    StateTransitionImpl (Stack.spec w C) (exec w C) :=
  StateTransitionImpl.ofFn (Rep w C L)
    (fun o hr hv => by
      obtain ⟨y, n, he, _⟩ := exists_body hr o hv
      exact ⟨result o y, y, n, he, rfl⟩)
    (by
      intro vs x o a y n hr hv he
      obtain ⟨z, m, hz, _, hm, hres, hb, hl⟩ := exists_body hr o hv
      obtain ⟨rfl, -⟩ := he.1.unique hz
      rw [← hr.abs_eq] at hv
      obtain ⟨-, hstep, hinv⟩ := step_methods hr.valid hr.inv hv
      rw [hr.abs_eq] at hstep
      rw [hstep, he.2, hres, ← hm]
      exact ⟨rfl, hr.valid, fun i => (hl i).trans (hr.layout i), hb, hm ▸ hinv, rfl⟩)

/-- The representation of the native stack. -/
public theorem rep_iff (w C : ℕ) (L : Stack.Memory.Layout) (vs : List ℕ) (x : Data registers) :
    (implementation w C L).rep vs x ↔ Rep w C L vs x := Iff.rfl

/-- **Constant time per operation.** One constant `K`, chosen before every width, capacity,
layout, state and operation, bounds the instructions of every admissible operation. -/
public theorem instruction_bound : ∃ K, ∀ (w C : ℕ) (L : Stack.Memory.Layout),
    Bound (implementation w C L) id fun _ _ => K := by
  refine ⟨factor * 23, fun w C L => ?_⟩
  intro vs x o a y n hr hv he
  obtain ⟨z, m, hz, hm, _⟩ := exists_body hr o hv
  obtain ⟨-, rfl⟩ := he.1.unique hz
  exact hm

/-- **Adaptive clients.** Every client whose history is admissible has a native execution, one
operation at a time, that returns the specified answer and represents the specified final stack.
Its instruction total is at most `K` per operation, for one constant `K`. The client's own
computation between operations is outside the machine. -/
public theorem run_client : ∃ K, ∀ {w C : ℕ} {L : Stack.Memory.Layout} {α : Type}
    (p : (Stack.spec w C).Client α) {vs : List ℕ} {x : Data registers}, Rep w C L vs x →
    (Stack.spec w C).ValidHistory vs ((Stack.spec w C).clientHistory vs p) →
    ∃ y traces, Executes (exec w C) p x ((Stack.spec w C).clientResult vs p) y traces ∧
      Rep w C L ((Stack.spec w C).clientState vs p) y ∧
      total id traces ≤ ((Stack.spec w C).clientHistory vs p).length * K := by
  obtain ⟨K, hK⟩ := instruction_bound
  exact ⟨K, fun p _ _ hr hv => Bound.exists_executes_const (hK _ _ _) p hr hv⟩

/-- Every operation writes only the layout's cells and keeps the frontier. -/
public theorem modifies {w C : ℕ} {L : Stack.Memory.Layout} {vs : List ℕ}
    {x y : Data registers} {o : StackOp ℕ} {a : (Stack.spec w C).Result o} {n : ℕ}
    (hr : Rep w C L vs x) (hv : (Stack.spec w C).valid vs o) (he : exec w C x o a y n) :
    Modifies L.footprint x.mem y.mem ∧ y.regs frontier = x.regs frontier := by
  obtain ⟨z, m, hz, _, hm, _⟩ := exists_body hr o hv
  obtain ⟨rfl, -⟩ := he.1.unique hz
  rw [← hr.abs_eq] at hv
  obtain ⟨hmem, hfr⟩ := Stack.Memory.modifies_methods hr.valid o hv
  rw [← hm] at hmem hfr
  exact ⟨hmem, hfr⟩

/-- Every operation preserves each heap assertion disjoint from the layout. -/
public theorem frame {w C : ℕ} {L : Stack.Memory.Layout} {vs : List ℕ}
    {x y : Data registers} {o : StackOp ℕ} {a : (Stack.spec w C).Result o} {n : ℕ}
    (hr : Rep w C L vs x) (hv : (Stack.spec w C).valid vs o) (he : exec w C x o a y n)
    {Q : HeapAssertion} (hQ : Q.holds x.mem) (hd : Disjoint Q.footprint L.footprint) :
    Q.holds y.mem :=
  HeapAssertion.frame hQ hd (modifies hr hv he).1

/-- The layout of a stack of capacity `C` at `base`: the count cell `base`, then the items. -/
public def initialLayout (base C : ℕ) : Stack.Memory.Layout := ⟨⟨base, 1⟩, ⟨base + 1, C⟩⟩

/-- An empty stack of capacity `C` at `base`, with zero memory: the layout words in their
registers, the frontier just past the items, and every other register zero. This is a
calling-convention state, not an uncharged allocation; `Stack.Memory.allocLayout` allocates. -/
public noncomputable def initial (base C : ℕ) : Data registers where
  regs i := if i = frontier then base + 1 + C
    else if h : 1 ≤ i.val ∧ i.val ≤ 4 then layoutWords (initialLayout base C) ⟨i.val - 1, by omega⟩
    else 0
  mem _ := 0

/-- The initial state represents the empty stack when the end of the items fits a word. -/
public theorem initial_rep {w base C : ℕ} (hf : Fits w (base + 1 + C)) :
    Rep w C (initialLayout base C) [] (initial base C) := by
  have hfr : (initial base C).regs frontier = base + 1 + C := by simp [initial]
  have hl (i : Fin 4) :
      (initial base C).regs (layoutReg i) = layoutWords (initialLayout base C) i := by
    have h1 : 1 ≤ (layoutReg i).val ∧ (layoutReg i).val ≤ 4 := by
      simp only [layoutReg]; omega
    simp only [initial, layoutReg_ne_frontier i, h1, ↓reduceIte]
    congr 1
  refine ⟨Stack.Memory.valid_allocLayout hf, hl, ⟨fun i => ?_, fun _ => fits_zero w⟩,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · change Fits w (ite _ _ _)
    split
    · exact hf
    · split
      · rename_i h
        refine hf.of_le ?_
        have hi : ∀ j : Fin 4, layoutWords (initialLayout base C) j ≤ base + 1 + C := by
          intro j
          fin_cases j <;> simp [layoutWords, initialLayout] <;> omega
        exact hi _
      · exact fits_zero w
  · change base + 1 ≤ (initial base C).regs frontier
    omega
  · change base + 1 + C ≤ (initial base C).regs frontier
    omega
  · exact Nat.zero_le _
  · simp [Stack.Memory.abs, memoryState, initial]

end Cslib.DataStructure.Stack.Native
