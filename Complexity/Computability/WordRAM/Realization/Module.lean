/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.StateTransition.Module
public import Complexity.DataStructure.WordRAM.StateTransition

/-!
# Local data-structure adapters for memory-client realizations

The kernel represents the entire memory function. A finite-footprint data structure instead
supplies its existing `SubroutineBase`, including initialization, register ABI and locality.
`Realizes.toStateTransitionImpl` combines those boundary conditions with a semantic `Module`
over the memory oracle. It derives the native method execution from the single realization
certificate; callers do not supply another execution proof or intermediate assertions.

The adapter keeps the semantic method footprint and the resource inequality explicit. In
particular, global whole-memory equality does not satisfy finite-block `rep_supported`.
An upper ADT must prove its own local representation and initialization obligations.

## Main definitions

* `taggedMethod`: retain the operation index in a typed method result.
* `Realizes.toStateTransitionImplWithArgs`: instantiate one global emitter at an ADT boundary.
* `Realizes.toStateTransitionImpl`: specialize to operation-indexed method families.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {δ : Type} {B : Basis} {w r k l kInit : ℕ} {D : StateTransitionSpec.{0, 0, 0}}

/-- Retaining the operation index permits one faithful result encoding for dependent observations.
This is an ordinary existing memory program, with no additional memory operation. -/
def taggedMethod (M : Module D (Memory.spec w)) (o : D.Op) : Memory.Prog D.Label := do
  let a ← M.methods o
  pure ⟨o, a⟩

/-- Tagging changes only the result; the memory state and operation history are identical. -/
theorem runClient_taggedMethod (M : Module D (Memory.spec w)) (o : D.Op) (s : Memory.State) :
    (Memory.spec w).runClient s (taggedMethod M o) =
      (⟨o, (Memory.spec w).clientResult s (M.methods o)⟩,
        (Memory.spec w).clientState s (M.methods o),
        (Memory.spec w).clientHistory s (M.methods o)) := by
  change (Memory.spec w).runClient s
    ((M.methods o).bind (fun a => .pure (⟨o, a⟩ : D.Label))) = _
  rw [StateTransitionSpec.runClient_bind]
  simp only [StateTransitionSpec.runClient_pure, List.append_nil]

namespace Realizes

/-- Derive the existing finite-footprint Word-RAM implementation at the upper ADT boundary.
The supplied base already proves initialization and representation locality. `entry` matches
the actual register ABI; `finish` re-establishes that local representation from semantic module
correctness and the kernel's register frame. `footprint` is a semantic memory property of the
method, and `pay` is a pure inequality for the already certified combined instruction currency.
The argument map instantiates an already selected global emitter; runtime layouts stay encoded
data rather than choosing new code for each object. Neither obligation introduces an extra
execution semantics or grants free native glue. -/
noncomputable def toStateTransitionImplWithArgs (M : Module D (Memory.spec w))
    {p : δ → Memory.Prog D.Label} {input : δ ↪ (Fin k → ℕ)} {output : D.Label ↪ (Fin l → ℕ)}
    {safe : ℕ → δ → Memory.State → Prop} {work : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work)
    (arguments : D.Op → δ) (source : ∀ o, p (arguments o) = taggedMethod M o)
    (frontier : Fin r) (src : Fin k → Fin r)
    (tmp : Fin (l + h.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {P : SubroutineCode B r kInit} {base : ℕ} {params : Fin kInit → ℕ} {s₀ : D.State}
    (C : SubroutineBase P D.Result D.valid w base params s₀)
    (hcode : P.code = h.code frontier src tmp)
    (entry : ∀ {s x} o, C.rep s x → D.valid s o → C.argMatch o x.regs →
      x.regs ∘ src = input (arguments o) ∧ safe w (arguments o) (memoryState frontier x) ∧
        M.rep s (memoryState frontier x))
    (decode : ∀ o a regs,
      (∀ i : Fin l, regs (tmp (Fin.castAdd (h.scratchSize + 1) i)) = output ⟨o, a⟩ i) →
        C.decode o regs = some a)
    (finish : ∀ {s s' x y} o a, C.rep s x → D.valid s o → C.argMatch o x.regs →
      D.step s o s' a → M.rep s' (memoryState frontier y) → y.Bounded w →
      (∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i) → C.rep s' y)
    (footprint : ∀ {s e} o, M.rep s e → D.valid s o →
      Modifies (Block.mk base C.space).footprint e.mem
        ((Memory.spec w).clientState e (M.methods o)).mem)
    (pay : ∀ {s s' x y} o a, C.rep s x → D.valid s o → C.argMatch o x.regs →
      D.step s o s' a → M.rep s' (memoryState frontier y) →
      memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (M.methods o) →
      (∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i) →
      h.factor * (memoryCost (p (arguments o)) (memoryState frontier x) +
        work (arguments o) (memoryState frontier x) + 1) + C.potential y ≤
          C.charge s o + C.potential x) :
    DataStructure.WordRAM.StateTransitionImpl P D w base params s₀ where
  toSubroutineBase := C
  step_exec {s x} o hr hv ha := by
    obtain ⟨hin, hsafe, hM⟩ := entry o hr hv ha
    have hvalid := ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
      (M.valid o hM hv)
    have htag : (Memory.spec w).ValidHistory (memoryState frontier x)
        ((Memory.spec w).clientHistory (memoryState frontier x) (p (arguments o))) := by
      rw [source o]
      simpa only [StateTransitionSpec.clientHistory, runClient_taggedMethod] using hvalid
    obtain ⟨y, hy, hm, hout, hframe⟩ :=
      (h.code_spec frontier src tmp hi hd hf hs).2 w (arguments o) x (C.bounded hr) hin hsafe htag
    have hm' : memoryState frontier y =
        (Memory.spec w).clientState (memoryState frontier x) (M.methods o) := by
      simpa only [source o, StateTransitionSpec.clientState, runClient_taggedMethod] using hm
    have hrun := (Memory.spec w).clientRun_canonical (memoryState frontier x) (M.methods o) hvalid
    obtain ⟨s', hstep, hM'⟩ := M.correct o hM hv hrun
    rw [← hm'] at hM'
    have hrep := finish o _ hr hv ha hstep hM' (hy.bounded (C.bounded hr)) hframe
    have hdec := decode o ((Memory.spec w).clientResult (memoryState frontier x) (M.methods o))
      y.regs (by
        simpa only [source o, StateTransitionSpec.clientResult, runClient_taggedMethod] using hout)
    have hmod : Modifies (Block.mk base C.space).footprint x.mem y.mem := by
      change Modifies (Block.mk base C.space).footprint
        (memoryState frontier x).mem (memoryState frontier y).mem
      rw [hm']
      exact footprint o hM hv
    have hpay := pay o _ hr hv ha hstep hM' hm' hframe
    obtain ⟨n, hn, he⟩ := hy
    rw [← hcode] at he
    exact ⟨y, s', _, n, he, hstep, hdec, hrep, hmod, by omega⟩

/-- Operation-indexed specialization of the global argument-map adapter. -/
noncomputable def toStateTransitionImpl (M : Module D (Memory.spec w))
    {input : D.Op ↪ (Fin k → ℕ)} {output : D.Label ↪ (Fin l → ℕ)}
    {safe : ℕ → D.Op → Memory.State → Prop} {work : D.Op → Memory.State → ℕ}
    (h : Realizes B (taggedMethod M) input output safe work)
    (frontier : Fin r) (src : Fin k → Fin r)
    (tmp : Fin (l + h.scratchSize + 1) → Fin r)
    (hi : Function.Injective tmp) (hd : ∀ i j, src i ≠ tmp j)
    (hf : ∀ j, tmp j ≠ frontier) (hs : ∀ i, src i ≠ frontier)
    {P : SubroutineCode B r kInit} {base : ℕ} {params : Fin kInit → ℕ} {s₀ : D.State}
    (C : SubroutineBase P D.Result D.valid w base params s₀)
    (hcode : P.code = h.code frontier src tmp)
    (entry : ∀ {s x} o, C.rep s x → D.valid s o → C.argMatch o x.regs →
      x.regs ∘ src = input o ∧ safe w o (memoryState frontier x) ∧
        M.rep s (memoryState frontier x))
    (decode : ∀ o a regs,
      (∀ i : Fin l, regs (tmp (Fin.castAdd (h.scratchSize + 1) i)) = output ⟨o, a⟩ i) →
        C.decode o regs = some a)
    (finish : ∀ {s s' x y} o a, C.rep s x → D.valid s o → C.argMatch o x.regs →
      D.step s o s' a → M.rep s' (memoryState frontier y) → y.Bounded w →
      (∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i) → C.rep s' y)
    (footprint : ∀ {s e} o, M.rep s e → D.valid s o →
      Modifies (Block.mk base C.space).footprint e.mem
        ((Memory.spec w).clientState e (M.methods o)).mem)
    (pay : ∀ {s s' x y} o a, C.rep s x → D.valid s o → C.argMatch o x.regs →
      D.step s o s' a → M.rep s' (memoryState frontier y) →
      memoryState frontier y = (Memory.spec w).clientState (memoryState frontier x) (M.methods o) →
      (∀ i, i ≠ frontier → (∀ j, tmp j ≠ i) → y.regs i = x.regs i) →
      h.factor * (memoryCost (taggedMethod M o) (memoryState frontier x) +
        work o (memoryState frontier x) + 1) + C.potential y ≤ C.charge s o + C.potential x) :
    DataStructure.WordRAM.StateTransitionImpl P D w base params s₀ :=
  toStateTransitionImplWithArgs M h id (fun _ => rfl) frontier src tmp hi hd hf hs C hcode
    entry decode finish footprint pay

end Realizes

end Cslib.WordRAM.Realization
