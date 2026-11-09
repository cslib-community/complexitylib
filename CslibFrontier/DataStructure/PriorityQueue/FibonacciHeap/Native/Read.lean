/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Memory
import CslibFrontier.Tactic.Realize

/-!
# Native read-only methods of the indexed Fibonacci heap

The existing linked record programs are realized by uniform exact-basis emitters. Capacity,
base and handle are runtime words; address arithmetic, branches and the complete Boolean or
optional-word result are charged. Optional payloads stay unshifted, including a maximum key.
The existing memory-history premise retains allocation/admissibility, independently of the
explicit arithmetic envelope.

## Main results

* `realizes_isEmpty`: the original emptiness method from runtime `(capacity, base)`.
* `realizes_getKey`: the original optional-key method from words `[capacity, base, handle]`.

These are method certificates, not a complete priority-queue backend or a consumer migration.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization

/-- The emptiness method reads the original minimum pointer. Its full two-word Boolean result
is charged, and zero capacity does not require the literal nine to fit. -/
theorem realizes_isEmpty : Realizes .exact
    (fun d : ℕ × ℕ => DataStructure.link ((layout d.1 d.2).methods 0) isEmpty)
    (WordEncoding.encode (α := ℕ × ℕ)) boolWords
    (fun w d _ => Fits w (d.2 + (9 * d.1 + 5))) (fun _ _ => 0) := by
  have h : Realizes .exact (fun d : ℕ × ℕ => do
      let m ← Memory.read (d.2 + (d.1 + d.1 + d.1 + d.1 + d.1 + d.1 + d.1 + d.1 + d.1) + 1)
      if m = 0 then pure true else pure false)
      (WordEncoding.encode (α := ℕ × ℕ)) boolWords
      (fun w d _ => Fits w (d.2 + (9 * d.1 + 5))) (fun _ _ => 0) := by
    realize
    all_goals exact h.of_le (by omega)
  apply h.congr
  intro d
  have ha : d.2 + (d.1 + d.1 + d.1 + d.1 + d.1 + d.1 + d.1 + d.1 + d.1) + 1 =
      d.2 + 9 * d.1 + 1 := by omega
  rw [ha]
  change (Memory.read (d.2 + 9 * d.1 + 1) >>= fun m =>
      if m = 0 then pure true else pure false) =
    (Memory.read (d.2 + 9 * d.1 + 1) >>= fun m => pure (decide (m = 0)))
  congr 1
  funext m
  by_cases hm : m = 0 <;> simp [hm]

/-- The optional key method uses the original in-heap flag and key array. The raw runtime
handle lies below capacity, and `some key` keeps the key itself rather than its successor. -/
theorem realizes_getKey : Realizes .exact
    (fun d : Fin 3 → ℕ => DataStructure.link ((layout (d 0) (d 1)).methods 0) (getKey (d 2)))
    (.refl _) optionWords
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) := by
  have h : Realizes .exact (fun d : Fin 3 → ℕ => do
      let b ← Memory.read (d 1 + (d 0 + d 0 + d 0 + d 0 + d 0 + d 0 + d 0) + d 2)
      if b = 0 then pure none else do
        let k ← Memory.read (d 1 + d 2)
        pure (some k))
      (.refl _) optionWords
      (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) := by
    realize
    all_goals exact h.1.of_le (by have := h.2; omega)
  apply h.congr
  intro d
  have ha : d 1 + (d 0 + d 0 + d 0 + d 0 + d 0 + d 0 + d 0) + d 2 =
      d 1 + 7 * d 0 + d 2 := by omega
  rw [ha]
  simp only [DataStructure.link, getKey, PFunctor.FreeM.liftM_bind, rd, Record.read, layout]
  congr 1
  funext b
  split_ifs <;> rfl

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
