/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Queue.WordRAM.RegisterCorrectness
public import CslibFrontier.Computability.WordRAM.Realization.Backend

/-!
# One fixed queue dispatcher over realized physical-array methods

The finite method family chooses all code and register packing before any runtime count,
base, capacity, width, memory or operation. Only the tag and payload are delivered by the
external dynamic calling convention. The count words, base, capacity and frontier remain
resident. A native branch selects a body, and two actual copies commit its returned counts.

The initializer is a literal-parameterized code family, as in the original queue: base and
capacity are fixed before the arbitrary dirty entry data. It writes registers only, performs
six instructions, and reserves exactly `2*capacity` physical cells. It is not a memory-clearing
initializer or an uncharged use of `Backend.install`.

## Main definitions

* `family`, `program`: the finite body family and its fixed native dispatcher.
* `implementation`: the existing dynamic-program calling convention and typed observation.
* `Rep`, `QueueRep`, `footprint`: the original two physical arrays with resident count words.
* `initializeCode`, `initialized`: six register writes and their exact state.

## References

The queue and its algorithmic references are in `Cslib.DataStructure.Queue.Spec`.
-/

@[expose] public section

namespace Cslib.DataStructure.Queue.WordRAM

open Cslib.WordRAM Cslib.WordRAM.Realization
open RegisterMetadata
open Cslib.DataStructure.Queue

/-- One fixed family contains both method bodies. Runtime arguments select no new code. -/
noncomputable abbrev family : Bool → Certificate .standard
  | false => Certificate.ofRealizes realizes_enqueue_standard
  | true => Certificate.ofRealizes realizes_dequeue_standard

/-- One finite register file for both bodies and the dispatcher. -/
noncomputable abbrev registers := Backend.registers family

/-- The complete physical reservation, including unused array cells. -/
def footprint (base capacity : ℕ) : Finset ℕ := (Block.mk base (2 * capacity)).footprint

/-- Persistent count, layout and payload bank. Both tags have the same five-word input. -/
noncomputable def src (i : Fin 5) : Fin registers := Backend.src family false i

/-- The two counts occupy the first two words of this common result prefix. -/
noncomputable def result (i : Fin 4) : Fin registers :=
  Backend.tmp family true (Fin.castAdd ((family true).realizes.scratchSize + 1) i)

/-- Tag delivery reuses scratch word zero, which the selected body may overwrite. -/
noncomputable abbrev tag : Fin registers := result 0

/-- A paid zero constant for the native tag test, also in the shared scratch bank. -/
noncomputable abbrev zero : Fin registers := result 1

/-- Two paid copies update the resident count bank. -/
noncomputable def commit : Code .standard registers :=
  .seq (.op (.copy (src 0) (result 0))) (.op (.copy (src 1) (result 1)))

/-- The same native program executes every operation. No host-selected body is substituted. -/
noncomputable def program : Code .standard registers :=
  .seq (.op (.const zero 0))
    (.seq (.branch (.eq tag zero) (Backend.code family false) (Backend.code family true)) commit)

/-- Only the tag and payload are external inputs. The result decoder observes Unit for
enqueue and the faithful option tag/value for dequeue; enqueue need not echo its argument. -/
noncomputable def implementation (w capacity : ℕ) :
    DynamicProgram (spec w capacity) registers where
  code := program
  output := result 3
  input i := i == tag || i == src 4
  encode o i := if i = tag then
    match o with | .enqueue _ => 0 | .dequeue => 1
    else match o with | .enqueue v => v | .dequeue => 0
  decode o regs := match o with
    | .enqueue _ => some ()
    | .dequeue => some (if regs (result 2) = 0 then none else some (regs (result 3)))

/-- The existing two-array representation, with counts and layout in the shared input bank.
Unused cells and the delivered tag/payload impose no extra memory or register premise. -/
structure Rep (w base capacity : ℕ) (front back : List ℕ) (x : Data registers) : Prop where
  bounded : x.Bounded w
  base_eq : x.regs (src 2) = base
  capacity_eq : x.regs (src 3) = capacity
  frontier_eq : x.regs (Backend.frontier family) = base + 2 * capacity
  frontLen_eq : x.regs (src 0) = front.length
  backLen_eq : x.regs (src 1) = back.length
  size_le : front.length + back.length ≤ capacity
  front_contents : Block.HoldsList base front.reverse x.mem
  back_contents : Block.HoldsList (base + capacity) back.reverse x.mem

/-- The same logical FIFO projection as the original queue. -/
def QueueRep (w base capacity : ℕ) (q : List ℕ) (x : Data registers) : Prop :=
  ∃ front back, q = contents (front, back) ∧ Rep w base capacity front back x

/-- The actual resident input words, without installing the maintained metadata again. -/
theorem Rep.input_eq {w base capacity : ℕ} {front back : List ℕ} {x : Data registers}
    (hr : Rep w base capacity front back x) :
    x.regs ∘ src = ![front.length, back.length, base, capacity, x.regs (src 4)] := by
  funext i
  fin_cases i
  · exact hr.frontLen_eq
  · exact hr.backLen_eq
  · exact hr.base_eq
  · exact hr.capacity_eq
  · rfl

/-- Rear credit is scaled by the single native exchange factor. This definition does not
assert the still separate dispatcher clock or the final per-call amortized inequality. -/
noncomputable def potential (x : Data registers) : ℕ :=
  2 * Backend.factor family * x.regs (src 1)

/-- Exact initialized data: only the frontier, counts, layout and zero scratch word change. -/
noncomputable def initialized (base capacity : ℕ) (x : Data registers) : Data registers :=
  (((((x.set (Backend.frontier family) (base + 2 * capacity)).set (src 0) 0).set
    (src 1) 0).set (src 2) base).set (src 3) capacity).set zero 0

/-- A literal base/capacity initializer with the original uniform six-instruction cost. -/
noncomputable def initializeCode (base capacity : ℕ) : Code .standard registers :=
  .seq (.op (.const (Backend.frontier family) (base + 2 * capacity)))
    (.seq (.op (.const (src 0) 0)) (.seq (.op (.const (src 1) 0))
      (.seq (.op (.const (src 2) base))
        (.seq (.op (.const (src 3) capacity)) (.op (.const zero 0))))))

/-- Initialization starts from arbitrary bounded dirty data and keeps every memory cell.
The original `Fits w 1` premise is needed by operation tag delivery, not these zero writes. -/
theorem initialize_exec {w base capacity : ℕ} {x : Data registers} (hx : x.Bounded w)
    (hc : Fits w (base + 2 * capacity)) :
    Exec w (initializeCode base capacity) x (initialized base capacity x) 6 ∧
      (initialized base capacity x).Bounded w ∧ (initialized base capacity x).mem = x.mem := by
  have hb : Fits w base := hc.of_le (by omega)
  have hcap : Fits w capacity := hc.of_le (by omega)
  have he : Exec w (initializeCode base capacity) x (initialized base capacity x) 6 :=
    (Exec.const hc).seq ((Exec.const (fits_zero w)).seq ((Exec.const (fits_zero w)).seq
      ((Exec.const hb).seq ((Exec.const hcap).seq (Exec.const (fits_zero w))))))
  exact ⟨he, he.bounded hx, rfl⟩

end Cslib.DataStructure.Queue.WordRAM
