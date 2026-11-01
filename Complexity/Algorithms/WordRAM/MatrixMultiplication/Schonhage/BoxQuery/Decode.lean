/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.StackMemory
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.PrefixPartition
import Complexity.Foundations.Data.Nat.Radix

/-!
# Recovering the finite frontier from actual native memory

The loop's proof measure is obtained from its actual stack words. Recovering each
prefix uses the existing bounded radix digits; no guessed frontier or execution
certificate is supplied. The measure is a proof tool, not an instruction or input word.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Decode the real depth and little-endian code of one native task. -/
@[expose] def decodePrefix (k c : ℕ) : List Term :=
  List.ofFn fun i : Fin k => Encoding.termDigits
    ⟨c / 10 ^ i.val % 10, Nat.mod_lt _ (by decide)⟩

/-- The actual fixed-length radix code recovers every original prefix term. -/
theorem decodePrefix_prefixCode (xs : List Term) :
    decodePrefix xs.length (prefixCode xs) = xs := by
  apply List.ext_getElem
  · simp [decodePrefix]
  · intro i hi hi'
    simp only [decodePrefix, List.getElem_ofFn]
    have hd := Cslib.Radix.digit_ofDigits (B := 10) (by decide)
      (xs.map fun lam => (Encoding.termDigits.symm lam).val)
      (by intro d hd; obtain ⟨lam, _, rfl⟩ := List.mem_map.mp hd
          exact (Encoding.termDigits.symm lam).isLt) i (by simpa using hi')
    rw [Cslib.Radix.digit_eq_div_pow_mod] at hd
    have hv : prefixCode xs / 10 ^ i % 10 =
        (Encoding.termDigits.symm xs[i]).val := by
      simpa only [prefixCode, List.getElem_map] using hd
    have hf : (⟨prefixCode xs / 10 ^ i % 10,
        Nat.mod_lt _ (by decide)⟩ : Fin 10) = Encoding.termDigits.symm xs[i] := Fin.ext hv
    rw [hf, Encoding.termDigits.apply_symm_apply]

/-- Decode occupied stack records in their actual top-first order. -/
@[expose] def decodeStack (F : ℕ) (μ : ℕ → ℕ) : ℕ → List (List Term)
  | 0 => []
  | n + 1 => decodePrefix (μ (F + n * 5)) (μ (F + n * 5 + 1)) :: decodeStack F μ n

/-- Actual five-word readback identifies the complete logical frontier uniquely. -/
theorem StackMemory.decode {L F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {μ : ℕ → ℕ} (h : StackMemory η F tasks μ) : decodeStack F μ tasks.length = tasks := by
  induction tasks with
  | nil => rfl
  | cons xs rest ih =>
    rw [List.length_cons, decodeStack, h.1.depth, h.1.code, decodePrefix_prefixCode,
      ih h.2]

/-- Proof-only work potential computed from the actual pending records. -/
@[expose] def workMeasure {L : ℕ} (η : OutStr L) (t F : ℕ) (x : Data registers) : ℕ :=
  ((decodeStack F x.mem (x.regs Reg.top)).map (potential η t)).sum

/-- Every native readback witness gives exactly the same loop measure. -/
theorem workMeasure_eq {L t F : ℕ} {η : OutStr L} {tasks : List (List Term)}
    {x : Data registers} (h : StackMemory η F tasks x.mem)
    (ht : x.regs Reg.top = tasks.length) :
    workMeasure η t F x = (tasks.map (potential η t)).sum := by
  rw [workMeasure, ht, h.decode]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
