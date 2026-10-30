/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Program
public import Complexity.Algorithms.WordRAM.ExactTriangle.PreparationInput

/-!
# Original signed arrays after real preparation

The producer's existing prefix frame retains every original signed input word. These internal
readback rules relate the recovery bank to those same words and to their original magnitude
bound; they do not assume intermediate signed fits or add a second input encoding.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM

/-- Each original payload word survives preparation in the unchanged caller prefix. -/
theorem original_word {n D g p q : ℕ} (values : List ℤ) (a : Data 64) (z : Data 400)
    (hout : Instances.Output n D g p (fun q => values.getD q 0)
      (.init (PreparationInput.input n D g p values)) a)
    (hmap : (z.comap productBank).comap RecordProduct.producerBank = a)
    (hq : q < 3 * (n * n)) : z.mem (5 + q) = Signed.encode (values.getD q 0) := by
  have hm : z.mem = a.mem := congrArg (fun d : Data 64 => d.mem) hmap
  rw [hm, hout.2.2.2.2.2.2.2.2.2.2.2 (5 + q) (Or.inl (by omega))]
  exact PreparationInput.input_word n D g p values q

/-- Original magnitude bounds supply every original array entry, not merely a fitting
intermediate machine state. The implicit index equation is the producer's existing layout. -/
theorem original_magnitude {n A q : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hq : q < 3 * (n * n)) : (values.getD q 0).natAbs ≤ A := by
  have hi : q < values.length := by omega
  rw [List.getD_eq_getElem _ _ hi]
  exact hv _ (List.getElem_mem hi)

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
