/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Heap

/-!
# Memory-access traces of word-RAM executions

The decorated execution relation retains the exact instruction count of `Exec` while exposing
successful reads and writes, including their addresses and word values. Branches and loop control
keep their ordinary instruction charges and produce no memory probes. A trace is an observation
of a RAM execution, not the full cell-probe model with arbitrary free computation.

## Main definitions

* `Probe`, `Op.probes`: a read or write event with address and value, and the probes of a primitive
  instruction.
* `TraceExec`: structured execution with its memory-access transcript.
* `Probe.readCount`, `Probe.writeCount`, `Probe.writes`: additive resource interpretations and the
  set of written addresses.

## Main results

* `TraceExec.exec`: forgetting the transcript recovers exact `Exec`.
* `Exec.exists_trace`: every execution has a transcript.
* `Probe.readCount_append`, `Probe.writeCount_append`: compositional probe accounting.

## References

The machine and its exact compilation costs are those of `WordRAM.Structured`.
-/

@[expose] public section

namespace Cslib.WordRAM

variable {B : Basis} {r : ℕ}

/-- An observed memory access, with the value read or written. -/
inductive Probe where
  /-- Read a word from an address. -/
  | read (address value : ℕ)
  /-- Write a word at an address. -/
  | write (address value : ℕ)
  deriving DecidableEq, Repr

/-- The memory accesses made by a data instruction in its initial state. -/
def Op.probes (o : Op B r) (x : Data r) : List Probe :=
  match o with
  | .load _ a => [.read (x.regs a) (x.mem (x.regs a))]
  | .store a s => [.write (x.regs a) (x.regs s)]
  | _ => []

/-- An exact structured execution decorated with its successful memory probes. -/
inductive TraceExec (w : ℕ) : Code B r → Data r → Data r → ℕ → List Probe → Prop where
  /-- A successful data instruction. -/
  | op {o : Op B r} {x y : Data r} :
      o.eval w x = some y → TraceExec w (.op o) x y 1 (o.probes x)
  /-- Sequential traces concatenate. -/
  | seq {c₁ c₂ : Code B r} {x y z : Data r} {m n : ℕ} {ts us : List Probe} :
      TraceExec w c₁ x y m ts → TraceExec w c₂ y z n us →
      TraceExec w (.seq c₁ c₂) x z (m + n) (ts ++ us)
  /-- The positive branch pays one control instruction. -/
  | branch_pos {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} {ts : List Probe} :
      c.Holds x → TraceExec w pos x y n ts → TraceExec w (.branch c pos neg) x y (n + 1) ts
  /-- The negative branch pays two control instructions. -/
  | branch_neg {c : Cond r} {pos neg : Code B r} {x y : Data r} {n : ℕ} {ts : List Probe} :
      ¬c.Holds x → TraceExec w neg x y n ts → TraceExec w (.branch c pos neg) x y (n + 2) ts
  /-- Loop termination pays two control instructions and has no probes. -/
  | loop_exit {c : Cond r} {body : Code B r} {x : Data r} :
      ¬c.Holds x → TraceExec w (.loop c body) x x 2 []
  /-- A loop iteration concatenates its body's trace and the remaining trace. -/
  | loop_iter {c : Cond r} {body : Code B r} {x y z : Data r} {m n : ℕ} {ts us : List Probe} :
      c.Holds x → TraceExec w body x y m ts → TraceExec w (.loop c body) y z n us →
      TraceExec w (.loop c body) x z (m + n + 2) (ts ++ us)

/-- Erasing probes leaves the original exact instruction-count theorem. -/
theorem TraceExec.exec {w n : ℕ} {c : Code B r} {x y : Data r} {ts : List Probe}
    (h : TraceExec w c x y n ts) : Exec w c x y n := by
  induction h with
  | op h => exact .op h
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | branch_pos h _ ih => exact .branch_pos h ih
  | branch_neg h _ ih => exact .branch_neg h ih
  | loop_exit h => exact .loop_exit h
  | loop_iter h _ _ ih₁ ih₂ => exact .loop_iter h ih₁ ih₂

/-- Every successful structured execution admits its exact memory transcript. -/
theorem Exec.exists_trace {w n : ℕ} {c : Code B r} {x y : Data r} (h : Exec w c x y n) :
    ∃ ts, TraceExec w c x y n ts := by
  induction h with
  | op h => exact ⟨_, .op h⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨ts, ht⟩ := ih₁
    obtain ⟨us, hu⟩ := ih₂
    exact ⟨_, .seq ht hu⟩
  | branch_pos h _ ih =>
    obtain ⟨ts, ht⟩ := ih
    exact ⟨_, .branch_pos h ht⟩
  | branch_neg h _ ih =>
    obtain ⟨ts, ht⟩ := ih
    exact ⟨_, .branch_neg h ht⟩
  | loop_exit h => exact ⟨_, .loop_exit h⟩
  | loop_iter h _ _ ih₁ ih₂ =>
    obtain ⟨ts, ht⟩ := ih₁
    obtain ⟨us, hu⟩ := ih₂
    exact ⟨_, .loop_iter h ht hu⟩

namespace Probe

/-- Number of reads in a transcript. -/
def readCount : List Probe → ℕ
  | [] => 0
  | .read _ _ :: ts => readCount ts + 1
  | .write _ _ :: ts => readCount ts

/-- Number of writes in a transcript. -/
def writeCount : List Probe → ℕ
  | [] => 0
  | .read _ _ :: ts => writeCount ts
  | .write _ _ :: ts => writeCount ts + 1

/-- Read counts add across consecutive executions. -/
theorem readCount_append (ts us : List Probe) :
    readCount (ts ++ us) = readCount ts + readCount us := by
  induction ts with
  | nil => simp [readCount]
  | cons t ts ih => cases t <;> simp [readCount, ih, Nat.add_right_comm]

/-- Write counts add across consecutive executions. -/
theorem writeCount_append (ts us : List Probe) :
    writeCount (ts ++ us) = writeCount ts + writeCount us := by
  induction ts with
  | nil => simp [writeCount]
  | cons t ts ih => cases t <;> simp [writeCount, ih, Nat.add_right_comm]

/-- Every probe is exactly one read or one write. -/
theorem readCount_add_writeCount (ts : List Probe) : readCount ts + writeCount ts = ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    cases t <;> simp [readCount, writeCount, ← ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The finite set of cells actually written by a transcript. -/
def writes : List Probe → Finset ℕ
  | [] => ∅
  | .read _ _ :: ts => writes ts
  | .write a _ :: ts => {a} ∪ writes ts

/-- Sequential write footprints combine by union, allowing repeated writes. -/
theorem writes_append (ts us : List Probe) : writes (ts ++ us) = writes ts ∪ writes us := by
  induction ts with
  | nil => simp [writes]
  | cons t ts ih => cases t <;> simp [writes, ih]

end Probe

/-- A successful primitive instruction preserves every cell absent from its write transcript. -/
private theorem Op.eval_modifies {w : ℕ} {o : Op B r} {x y : Data r} (h : o.eval w x = some y) :
    Modifies (Probe.writes (o.probes x)) x.mem y.mem := by
  cases o with
  | const =>
    obtain ⟨_, rfl⟩ := Data.put_eq_some.mp h
    exact Modifies.refl _ _
  | alu =>
    obtain ⟨_, -, -, rfl⟩ := Op.eval_alu_eq_some.mp h
    exact Modifies.refl _ _
  | copy | load => cases h; exact Modifies.refl _ _
  | store a s =>
    cases h
    simpa [Op.probes, Probe.writes] using Modifies.update x.mem (x.regs a) (x.regs s)

/-- An execution changes memory only at addresses appearing as writes in its transcript. -/
theorem TraceExec.modifies {w n : ℕ} {c : Code B r} {x y : Data r} {ts : List Probe}
    (h : TraceExec w c x y n ts) : Modifies (Probe.writes ts) x.mem y.mem := by
  induction h with
  | op h => exact Op.eval_modifies h
  | seq _ _ ih₁ ih₂ => simpa only [Probe.writes_append] using ih₁.trans ih₂
  | branch_pos _ _ ih => exact ih
  | branch_neg _ _ ih => exact ih
  | loop_exit => exact Modifies.refl _ _
  | loop_iter _ _ _ ih₁ ih₂ => simpa only [Probe.writes_append] using ih₁.trans ih₂

/-- A concrete execution preserves any assertion disjoint from its write transcript. -/
theorem TraceExec.frame {w n : ℕ} {c : Code B r} {x y : Data r} {ts : List Probe}
    (h : TraceExec w c x y n ts) {P : HeapAssertion} (hP : P.holds x.mem)
    (hdisj : Disjoint P.footprint (Probe.writes ts)) : P.holds y.mem :=
  HeapAssertion.frame hP hdisj h.modifies

/-- No instruction makes more than one memory access. -/
theorem TraceExec.length_le {w n : ℕ} {c : Code B r} {x y : Data r} {ts : List Probe}
    (h : TraceExec w c x y n ts) : ts.length ≤ n := by
  induction h with
  | @op o x y ho => cases o <;> simp [Op.probes]
  | seq _ _ ih₁ ih₂ => simpa only [List.length_append] using Nat.add_le_add ih₁ ih₂
  | branch_pos _ _ ih => exact ih.trans (Nat.le_add_right _ _)
  | branch_neg _ _ ih => exact ih.trans (Nat.le_add_right _ _)
  | loop_exit => simp
  | loop_iter _ _ _ ih₁ ih₂ =>
    simp only [List.length_append]
    exact (Nat.add_le_add ih₁ ih₂).trans (Nat.le_add_right _ _)

end Cslib.WordRAM
