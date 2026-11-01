/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierChunkInit
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplayChunkBits
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.QueryReplaySupplierTotal

/-!
# Exact numeric answers from checked local replay

Extracting a requested chunk after replay returns the existing packed encoding of the existing
functional gate, on every assignment. This includes partial final chunks and every FAIL case;
no high-order padding is materialized by the numeric reader.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk

open MultiTapeTM Cslib.TreeEval.Ary

variable {k s : ℕ} {Q : Type}

/-- The numeric answer of a prepared local call is the packed chunk of the existing gate's
Boolean output, including all rejected-label and failed-motion cases. -/
theorem answer_runFrom_prepare {q r m : ℕ} (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ : ℕ) (i : Fin q)
    (limit counter stride : ℕ) (hb : Encoding.width k s b ≤ r * m) (chunk : Fin r)
    (hcapacity : Encoding.width k s b ≤ limit.size) :
    let words := Assignments.labels k (limit, counter, stride, Encoding.width k s b)
    let value := gate (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) i
      ((Encoding.NativeChecked.parse (k := k) e (b, words.1)).map fun raw => raw.toView b)
      (fun h δ => (Encoding.NativeChecked.parse (k := k) e (b, words.2 h δ)).map
        fun raw => raw.toView b)
    answer M e ((machine M e).runFrom w
      (prepare e ((m, chunk), (w.length, b, σ, i, limit, counter, stride))) b) =
      (Packed.packBits hb (Encoding.encode e value) chunk).val := by
  rw [prepare, runFrom_eq]
  dsimp only [answer]
  rw [Supplier.finish_prepare_eq_gate M e w b σ i limit counter stride hcapacity]
  exact readNat_ofFn_eq_packBits hb _ chunk

end Turing.MultiTapePTM.BlockComputation.QueryReplay.SupplierChunk
