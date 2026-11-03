/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Primitive
public import Complexity.Computability.WordRAM.Realization.Witness
public import Complexity.DataStructure.StateTransition.Resource

/-!
# An operation-level native backend for the memory interface

Four uniform primitive realization witnesses supply four static native bodies. The source query
constructor selects its body; its argument values never select or generate native code. This is
an operation-level implementation for `DataStructure.Module.realize`, not a single native
dispatcher for all queries. Witness selection uses classical choice from realization proofs;
no effective code extraction is asserted.

`prepare` installs already delivered arguments in two registers without changing memory or the
frontier. This is a semantic calling convention, and its installation and result decoding are
uncharged. `instruction_bound` counts only the selected body's actual `Exec` instructions; it
does not include a final halt or imply a whole-client machine-clock bound. Client-side argument
computation, glue and control require the separate graded realization rules.

The representation retains the literal global memory function and frontier, as well as global
word bounds. Every actual execution from the prepared state is correct, by determinism of the
same native code whose existence follows from its realization certificate.

## Main definitions

* `MemoryBackend.body`, `MemoryBackend.prepare`, `MemoryBackend.exec`: static operation bodies
  and their existing native execution evidence.
* `MemoryBackend.implementation`: a generic `DataStructure.StateTransitionImpl`.

## Main results

* `MemoryBackend.instruction_bound`: a uniform body-instruction bound in `Memory.charge + 1`.
-/


namespace Cslib.WordRAM.Realization.MemoryBackend

open Cslib.DataStructure

private abbrev word : ℕ ↪ (Fin 1 → ℕ) :=
  (Equiv.funUnique (Fin 1) ℕ).symm.toEmbedding

private theorem readCertificate :
    Realizes .exact (fun a : ℕ => Memory.read a) word word
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.read word 0

private theorem writeCertificate :
    Realizes .exact (fun a : Fin 2 → ℕ => Memory.write (a 0) (a 1))
      (Function.Embedding.refl _) (Equiv.ofUnique Unit (Fin 0 → ℕ)).toEmbedding
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.write (.refl _) 0 1

private theorem allocCertificate :
    Realizes .exact (fun a : ℕ => Memory.alloc a) word word
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.alloc word 0

private theorem dirtyCertificate :
    Realizes .exact (fun a : ℕ => Memory.allocDirty a) word word
      (fun _ _ _ => True) (fun _ _ => 0) := Realizes.allocDirty word 0

private noncomputable def slots : ℕ :=
  (1 + readCertificate.scratchSize + 1) + (0 + writeCertificate.scratchSize + 1) +
    (1 + allocCertificate.scratchSize + 1) + (1 + dirtyCertificate.scratchSize + 1)

/-- One register count is selected before every width, state, query and argument. -/
public noncomputable def registers : ℕ := slots + 3

/-- Register zero retains the allocation frontier across calls. -/
public noncomputable def frontier : Fin registers := ⟨0, by unfold registers; omega⟩

private noncomputable def src {k : ℕ} (hk : k ≤ 2) (i : Fin k) : Fin registers :=
  ⟨i.val + 1, by have := i.isLt; unfold registers; omega⟩

private noncomputable def tmp {n : ℕ} (hn : n ≤ slots) (i : Fin n) : Fin registers :=
  ⟨i.val + 3, by have := i.isLt; unfold registers; omega⟩

private theorem layout {k n : ℕ} (hk : k ≤ 2) (hn : n ≤ slots) :
    Function.Injective (tmp hn) ∧ (∀ i j, src hk i ≠ tmp hn j) ∧
      (∀ j, tmp hn j ≠ frontier) ∧ (∀ i, src hk i ≠ frontier) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    simp only [tmp] at this
    omega
  · intro i j h
    have := congrArg Fin.val h
    simp only [src, tmp] at this
    have := i.isLt
    omega
  · intro j h
    have := congrArg Fin.val h
    simp only [tmp, frontier] at this
    omega
  · intro i h
    have := congrArg Fin.val h
    simp only [src, frontier] at this
    omega

private theorem readSlots : 1 + readCertificate.scratchSize + 1 ≤ slots := by
  unfold slots; omega

private theorem writeSlots : 0 + writeCertificate.scratchSize + 1 ≤ slots := by
  unfold slots; omega

private theorem allocSlots : 1 + allocCertificate.scratchSize + 1 ≤ slots := by
  unfold slots; omega

private theorem dirtySlots : 1 + dirtyCertificate.scratchSize + 1 ≤ slots := by
  unfold slots; omega

/-- Four static bodies, selected only by the query constructor. All emitters were chosen before
the query's runtime arguments. There is no native operation-tag dispatcher. -/
public noncomputable def body : Memory.Op → Code .exact registers
  | .read _ => readCertificate.code frontier (src (by omega)) (tmp readSlots)
  | .write _ _ => writeCertificate.code frontier (src le_rfl) (tmp writeSlots)
  | .alloc _ => allocCertificate.code frontier (src (by omega)) (tmp allocSlots)
  | .allocDirty _ => dirtyCertificate.code frontier (src (by omega)) (tmp dirtySlots)

private def first : Memory.Op → ℕ
  | .read a | .write a _ => a
  | .alloc n | .allocDirty n => n

private def second : Memory.Op → ℕ
  | .write _ v => v
  | _ => 0

/-- Semantic installation of delivered arguments in registers one and two. Installation is
uncharged and is not asserted to execute as part of `body`. -/
public noncomputable def prepare (o : Memory.Op) (x : Data registers) : Data registers :=
  (x.set (src (k := 2) le_rfl 0) (first o)).set (src (k := 2) le_rfl 1) (second o)

/-- Argument delivery leaves the literal whole memory and frontier unchanged. -/
public theorem prepare_memoryState (o : Memory.Op) (x : Data registers) :
    memoryState frontier (prepare o x) = memoryState frontier x := by
  apply Memory.State.ext
  · rfl
  · simp [memoryState, prepare, Data.set, src, frontier]

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

private theorem prepare_unary (o : Memory.Op) (x : Data registers) :
    (prepare o x).regs ∘ src (k := 1) (by omega) = word (first o) := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  simp [prepare, src, Data.set, word]

private theorem prepare_binary (a v : ℕ) (x : Data registers) :
    (prepare (.write a v) x).regs ∘ src (k := 2) le_rfl =
      fun i => if i = 0 then a else v := by
  funext i
  fin_cases i <;> simp [prepare, src, first, second, Data.set]

/-- Typed observation of the primitive result: word answers occupy the first scratch register;
the store has the unique unit answer. Decoding performs no charged native instruction. -/
public noncomputable def result (o : Memory.Op) (y : Data registers) : o.Result :=
  match o with
  | .read _ => y.regs (tmp readSlots 0)
  | .write _ _ => ()
  | .alloc _ => y.regs (tmp allocSlots 0)
  | .allocDirty _ => y.regs (tmp dirtySlots 0)

/-- Existing native `Exec` evidence for a typed operation, following uncharged argument delivery.
Its natural-number trace counts body instructions only, with no final halt. -/
public noncomputable def exec (w : ℕ) : Execution (Memory.spec w) (Data registers) ℕ :=
  fun x o a y n => Exec w (body o) (prepare o x) y n ∧ a = result o y

/-- The execution interface records actual native body instructions and the typed observation. -/
public theorem exec_iff (w : ℕ) (x y : Data registers) (o : Memory.Op) (a : o.Result) (n : ℕ) :
    exec w x o a y n ↔ Exec w (body o) (prepare o x) y n ∧ a = result o y := Iff.rfl

/-- Changing a read's delivered address leaves its static native body unchanged. -/
public theorem body_read_eq (a b : ℕ) : body (.read a) = body (.read b) := by rfl

/-- Changing a store's delivered address or value leaves its static body unchanged. -/
public theorem body_write_eq (a v b u : ℕ) : body (.write a v) = body (.write b u) := by rfl

/-- Changing the allocation count leaves its static native body unchanged. -/
public theorem body_alloc_eq (a b : ℕ) : body (.alloc a) = body (.alloc b) := by rfl

/-- Changing the dirty-allocation count leaves its static body unchanged. -/
public theorem body_allocDirty_eq (a b : ℕ) : body (.allocDirty a) = body (.allocDirty b) := by rfl

/-- A single body-instruction exchange factor, independent of widths and arguments. -/
public noncomputable def factor : ℕ :=
  max (max readCertificate.factor writeCertificate.factor)
    (max allocCertificate.factor dirtyCertificate.factor)

private theorem exists_body {w : ℕ} {x : Data registers} (o : Memory.Op)
    (hx : x.Bounded w) (hv : Memory.valid w (memoryState frontier x) o) :
    ∃ y n, Exec w (body o) (prepare o x) y n ∧
      n ≤ factor * (Memory.charge (memoryState frontier x) o + 1) ∧
      memoryState frontier y = (Memory.step (memoryState frontier x) o).1 ∧
      result o y = (Memory.step (memoryState frontier x) o).2 := by
  have hb := prepare_bounded hx hv
  cases o with
  | read a =>
    obtain ⟨hi, hd, hf, hs⟩ := layout (k := 1) (by omega) readSlots
    have hv' : (Memory.spec w).ValidHistory (memoryState frontier (prepare (.read a) x))
        ((Memory.spec w).clientHistory (memoryState frontier (prepare (.read a) x))
          (Memory.read a)) := by
      simpa only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift,
        prepare_memoryState, StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.validHistory_nil, and_true] using hv
    obtain ⟨y, ⟨n, hn, he⟩, hm, hout, _⟩ :=
      (readCertificate.code_spec frontier _ _ hi hd hf hs).2 w a _ hb
        (prepare_unary (.read a) x) trivial hv'
    refine ⟨y, n, he, ?_, ?_, ?_⟩
    · change n ≤ readCertificate.factor * (1 + 0 + 1) at hn
      exact hn.trans (Nat.mul_le_mul_right _ (by unfold factor; omega))
    · simpa [StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift,
        prepare_memoryState] using hm
    · simpa [result, word, tmp, StateTransitionSpec.clientResult,
        StateTransitionSpec.runClient_lift, prepare_memoryState] using hout 0
  | write a v =>
    obtain ⟨hi, hd, hf, hs⟩ := layout (k := 2) le_rfl writeSlots
    have hv' : (Memory.spec w).ValidHistory (memoryState frontier (prepare (.write a v) x))
        ((Memory.spec w).clientHistory (memoryState frontier (prepare (.write a v) x))
          (Memory.write a v)) := by
      simpa only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift,
        prepare_memoryState, StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.validHistory_nil, and_true] using hv
    obtain ⟨y, ⟨n, hn, he⟩, hm, _, _⟩ :=
      (writeCertificate.code_spec frontier _ _ hi hd hf hs).2 w
        (fun i => if i = 0 then a else v) _ hb (prepare_binary a v x) trivial hv'
    refine ⟨y, n, he, ?_, ?_, rfl⟩
    · change n ≤ writeCertificate.factor * (1 + 0 + 1) at hn
      exact hn.trans (Nat.mul_le_mul_right _ (by unfold factor; omega))
    · simpa [StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift,
        prepare_memoryState] using hm
  | alloc a =>
    obtain ⟨hi, hd, hf, hs⟩ := layout (k := 1) (by omega) allocSlots
    have hv' : (Memory.spec w).ValidHistory (memoryState frontier (prepare (.alloc a) x))
        ((Memory.spec w).clientHistory (memoryState frontier (prepare (.alloc a) x))
          (Memory.alloc a)) := by
      simpa only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift,
        prepare_memoryState, StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.validHistory_nil, and_true] using hv
    obtain ⟨y, ⟨n, hn, he⟩, hm, hout, _⟩ :=
      (allocCertificate.code_spec frontier _ _ hi hd hf hs).2 w a _ hb
        (prepare_unary (.alloc a) x) trivial hv'
    refine ⟨y, n, he, ?_, ?_, ?_⟩
    · change n ≤ allocCertificate.factor * (a + 1 + 0 + 1) at hn
      exact hn.trans (Nat.mul_le_mul_right _ (by unfold factor; omega))
    · simpa [StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift,
        prepare_memoryState] using hm
    · simpa [result, word, tmp, StateTransitionSpec.clientResult,
        StateTransitionSpec.runClient_lift, prepare_memoryState] using hout 0
  | allocDirty a =>
    obtain ⟨hi, hd, hf, hs⟩ := layout (k := 1) (by omega) dirtySlots
    have hv' : (Memory.spec w).ValidHistory (memoryState frontier (prepare (.allocDirty a) x))
        ((Memory.spec w).clientHistory (memoryState frontier (prepare (.allocDirty a) x))
          (Memory.allocDirty a)) := by
      simpa only [StateTransitionSpec.clientHistory, StateTransitionSpec.runClient_lift,
        prepare_memoryState, StateTransitionSpec.validHistory_cons,
        StateTransitionSpec.validHistory_nil, and_true] using hv
    obtain ⟨y, ⟨n, hn, he⟩, hm, hout, _⟩ :=
      (dirtyCertificate.code_spec frontier _ _ hi hd hf hs).2 w a _ hb
        (prepare_unary (.allocDirty a) x) trivial hv'
    refine ⟨y, n, he, ?_, ?_, ?_⟩
    · change n ≤ dirtyCertificate.factor * (1 + 0 + 1) at hn
      exact hn.trans (Nat.mul_le_mul_right _ (by unfold factor; omega))
    · simpa [StateTransitionSpec.clientState, StateTransitionSpec.runClient_lift,
        prepare_memoryState] using hm
    · simpa [result, word, tmp, StateTransitionSpec.clientResult,
        StateTransitionSpec.runClient_lift, prepare_memoryState] using hout 0

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
