/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Backend
public import Complexity.Computability.WordRAM.Realization.Primitive

/-!
# A fixed seven-register backend for the memory interface

The four primitive witnesses are retained as data in the existing `Certificate`/`Backend`.
Their supplied scratch, factor and code determine seven registers and exchange factor four;
no resource projection chooses again from an existential proof.

`prepare` retains the existing calling convention: already delivered arguments occupy registers
one and two, with an unused second word zeroed. Installation and typed result decoding are
uncharged. `instruction_bound` counts selected body instructions only, with no halt or native
client-control claim. Full memory, frontier, admissibility and word bounds are retained.

## Main definitions

* `certificates`, `backend`: the four supplied primitive witnesses in the shared backend.
* `body`, `prepare`, `exec`, `implementation`: the existing operation-level execution interface.

## Main results

* `registers_eq`, `factor_eq`: concrete resources of the supplied family.
* `read_code`, `write_code`: literal one-instruction bodies.
* `instruction_bound`: the existing body-only charge bound.
-/

namespace Cslib.WordRAM.Realization.MemoryBackend

open Cslib.DataStructure

local notation "word" => Equiv.toEmbedding (Equiv.symm (Equiv.funUnique (Fin 1) ℕ))

/-- Supplied witnesses for read, write, zeroed allocation and dirty allocation, in that order. -/
@[expose] public def certificates : Fin 4 → Certificate .exact :=
  ![⟨Realizes.readWitness word 0⟩,
    ⟨Realizes.writeWitness (Function.Embedding.refl (Fin 2 → ℕ)) 0 1⟩,
    ⟨Realizes.allocWitness word 0⟩, ⟨Realizes.allocDirtyWitness word 0⟩]

/-- The memory operations use their original programs and typed results through one backend. -/
@[expose] public def backend (w : ℕ) : Backend (Memory.spec w) certificates where
  tag
    | .read _ => 0
    | .write _ _ => 1
    | .alloc _ => 2
    | .allocDirty _ => 3
  arg
    | .read a => a
    | .write a v => ![a, v]
    | .alloc n => n
    | .allocDirty n => n
  answer
    | .read _ => id
    | .write _ _ => id
    | .alloc _ => id
    | .allocDirty _ => id

/-- The family has two argument slots, four result/scratch slots and one frontier. -/
@[expose] public noncomputable def registers : ℕ := Backend.registers certificates

/-- Concrete register count, determined by the supplied witnesses. -/
public theorem registers_eq : registers = 7 := by decide

/-- Register zero retains the allocation frontier across calls. -/
@[expose] public noncomputable def frontier : Fin registers := Backend.frontier certificates

private def src {k : ℕ} (hk : k ≤ 2) (i : Fin k) : Fin registers :=
  ⟨i.val + 1, by rw [registers_eq]; have := i.isLt; omega⟩

private def resultReg : Fin registers := ⟨3, by rw [registers_eq]; decide⟩

/-- The four bodies are exactly the supplied bodies of the shared backend. -/
@[expose] public noncomputable def body (o : Memory.Op) : Code .exact registers :=
  Backend.code certificates ((backend 0).tag o)

/-- The supplied read is the literal load from argument register one to result register three. -/
public theorem read_code (a : ℕ) :
    body (.read a) = .op (.load ⟨3, by rw [registers_eq]; decide⟩
      ⟨1, by rw [registers_eq]; decide⟩) := rfl

/-- The supplied store is the literal store from argument register two to address register one. -/
public theorem write_code (a v : ℕ) :
    body (.write a v) = .op (.store ⟨1, by rw [registers_eq]; decide⟩
      ⟨2, by rw [registers_eq]; decide⟩) := rfl

private def first : Memory.Op → ℕ
  | .read a | .write a _ => a
  | .alloc n | .allocDirty n => n

private def second : Memory.Op → ℕ
  | .write _ v => v
  | _ => 0

/-- Deliver arguments in registers one and two; this is an uncharged calling convention. -/
public noncomputable def prepare (o : Memory.Op) (x : Data registers) : Data registers :=
  (x.set (src (k := 2) le_rfl 0) (first o)).set (src (k := 2) le_rfl 1) (second o)

/-- Argument delivery leaves the literal whole memory and frontier unchanged. -/
public theorem prepare_memoryState (o : Memory.Op) (x : Data registers) :
    memoryState frontier (prepare o x) = memoryState frontier x := by
  apply Memory.State.ext
  · rfl
  · rfl

private theorem prepare_bounded {w : ℕ} {o : Memory.Op} {x : Data registers}
    (hx : x.Bounded w) (hv : Memory.valid w (memoryState frontier x) o) :
    (prepare o x).Bounded w := by
  have hw := wellFormed_memoryState hx (frontier := frontier)
  have hfirst : Fits w (first o) := by
    cases o with
    | read a => exact hw.fits_of_lt_frontier hv
    | write a v => exact hw.fits_of_lt_frontier hv.1
    | alloc n => exact hv.of_le (Nat.le_add_left n _)
    | allocDirty n => exact hv.of_le (Nat.le_add_left n _)
  have hsecond : Fits w (second o) := by
    cases o with
    | write a v => exact hv.2
    | _ => exact fits_zero w
  exact (hx.set hfirst).set hsecond

/-- Typed observations retain the existing word/unit convention without native decoding work. -/
public noncomputable def result (o : Memory.Op) (y : Data registers) : o.Result :=
  match o with
  | .read _ => y.regs resultReg
  | .write _ _ => ()
  | .alloc _ => y.regs resultReg
  | .allocDirty _ => y.regs resultReg

/-- Existing operation-level native body traces, following uncharged argument delivery. -/
public noncomputable def exec (w : ℕ) : Execution (Memory.spec w) (Data registers) ℕ :=
  fun x o a y n => Exec w (body o) (prepare o x) y n ∧ a = result o y

/-- The execution interface records the actual body instructions and typed observation. -/
public theorem exec_iff (w : ℕ) (x y : Data registers) (o : Memory.Op) (a : o.Result) (n : ℕ) :
    exec w x o a y n ↔ Exec w (body o) (prepare o x) y n ∧ a = result o y := Iff.rfl

/-- Runtime addresses do not select new read code. -/
public theorem body_read_eq (a b : ℕ) : body (.read a) = body (.read b) := rfl

/-- Runtime addresses and values do not select new store code. -/
public theorem body_write_eq (a v b u : ℕ) : body (.write a v) = body (.write b u) := rfl

/-- Runtime counts do not select new zeroed-allocation code. -/
public theorem body_alloc_eq (a b : ℕ) : body (.alloc a) = body (.alloc b) := rfl

/-- Runtime counts do not select new dirty-allocation code. -/
public theorem body_allocDirty_eq (a b : ℕ) : body (.allocDirty a) = body (.allocDirty b) := rfl

/-- A single exchange factor for all four supplied primitive bodies. -/
@[expose] public noncomputable def factor : ℕ := Backend.factor certificates

/-- Concrete factor, retained from the supplied four primitive witnesses. -/
public theorem factor_eq : factor = 4 := by decide

private theorem prepare_inputs (o : Memory.Op) (x : Data registers) :
    (prepare o x).regs ∘ Backend.src certificates ((backend 0).tag o) =
      (certificates ((backend 0).tag o)).input ((backend 0).arg o) := by
  cases o <;> funext j <;> fin_cases j <;> rfl

private theorem exists_body {w : ℕ} {x : Data registers} (o : Memory.Op)
    (hx : x.Bounded w) (hv : Memory.valid w (memoryState frontier x) o) :
    ∃ y n, Exec w (body o) (prepare o x) y n ∧
      n ≤ factor * (Memory.charge (memoryState frontier x) o + 1) ∧
      memoryState frontier y = (Memory.step (memoryState frontier x) o).1 ∧
      result o y = (Memory.step (memoryState frontier x) o).2 := by
  have hb := prepare_bounded hx hv
  have hprepare : memoryState (Backend.frontier certificates) (prepare o x) =
      memoryState frontier x := prepare_memoryState o x
  have hs : (certificates ((backend 0).tag o)).safe w ((backend 0).arg o)
      (memoryState (Backend.frontier certificates) (prepare o x)) := by cases o <;> trivial
  have hvalid : (Memory.spec w).ValidHistory
      (memoryState (Backend.frontier certificates) (prepare o x))
      ((Memory.spec w).clientHistory
        (memoryState (Backend.frontier certificates) (prepare o x))
        ((certificates ((backend 0).tag o)).prog ((backend 0).arg o))) := by
    rw [hprepare]
    cases o <;>
      simpa [certificates, backend, StateTransitionSpec.clientHistory,
        StateTransitionSpec.runClient_lift, StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.validHistory_nil, prepare_memoryState] using hv
  obtain ⟨y, n, he, hn, hm, hout, -, -⟩ :=
    Backend.exists_exec_live certificates ((backend 0).tag o) ((backend 0).arg o) hb
      (prepare_inputs o x) hs hvalid
  rw [hprepare] at hn hm hout
  refine ⟨y, n, he, ?_, ?_, ?_⟩
  · cases o <;>
      simpa [factor, frontier, certificates, backend, memoryCost, StateTransitionSpec.clientHistory,
      StateTransitionSpec.runClient_lift, StateTransitionSpec.totalCost_cons,
      StateTransitionSpec.totalCost_nil, Nat.add_zero, prepare_memoryState] using hn
  · cases o <;> exact hm
  · cases o with
    | write _ _ => rfl
    | read _ | alloc _ | allocDirty _ =>
      have hout0 := hout ⟨0, by change 0 < 1; decide⟩
      exact hout0

/-- The memory interface implemented by four static bodies. The representation includes every
cell, the frontier and global word bounds; argument installation is semantic and uncharged. -/
public noncomputable def implementation (w : ℕ) : StateTransitionImpl (Memory.spec w) (exec w) :=
  StateTransitionImpl.ofFn
    (fun s x => memoryState frontier x = s ∧ x.Bounded w)
    (fun o hr hv => by
      obtain ⟨y, n, he, _, _, _⟩ := exists_body o hr.2 (hr.1 ▸ hv)
      exact ⟨result o y, y, n, he, rfl⟩)
    (by
      intro s x o a y n hr hv he
      obtain ⟨z, m, hz, _, hm, hout⟩ := exists_body o hr.2 (hr.1 ▸ hv)
      obtain ⟨rfl, _⟩ := he.1.unique hz
      exact ⟨he.2.trans (hout.trans (congrArg (fun t => (Memory.step t o).2) hr.1)),
        (hm.trans (congrArg (fun t => (Memory.step t o).1) hr.1)),
        he.1.bounded (prepare_bounded hr.2 (hr.1 ▸ hv))⟩)

/-- The backend represents the full global memory and frontier, with global word bounds. -/
public theorem rep_iff (w : ℕ) (s : Memory.State) (x : Data registers) :
    (implementation w).rep s x ↔ memoryState frontier x = s ∧ x.Bounded w := Iff.rfl

/-- A body-only instruction certificate. This omits argument delivery, decoding and halt, and
therefore does not assert a whole-client machine-clock bound. -/
public theorem instruction_bound (w : ℕ) :
    Bound (implementation w) id (fun s o => factor * (Memory.charge s o + 1)) := by
  intro s x o a y n hr hv he
  obtain ⟨z, m, hz, hn, _, _⟩ := exists_body o hr.2 (hr.1 ▸ hv)
  obtain ⟨_, rfl⟩ := he.1.unique hz
  simpa only [id_eq, hr.1] using hn

end Cslib.WordRAM.Realization.MemoryBackend
