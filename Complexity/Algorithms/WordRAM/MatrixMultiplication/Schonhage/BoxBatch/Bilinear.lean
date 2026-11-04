/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch.Width

/-!
# Native query batches compute the original bilinear product

Canonical left and right leaf encodings identify every stored query answer with the
existing bilinear product. The same initialized execution and charged halt compute all
wanted coordinates, preserving order and repetitions. This is a one-tile result; the
wanted coordinates and encoded arrays are original inputs to this component.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- One actual initialized batch computes all original bilinear-product coordinates,
with no repeated table preparation. Canonical encoding and threshold hypotheses are explicit. -/
theorem runs_bilinear {W L m t A B : ℕ} (hmL : m ≤ L) (ht : t ≤ m)
    (qs : List (OutStr L)) (hη : ∀ η ∈ qs, (innerSetO η).card = m)
    (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (left right : Fin (10 ^ L) → ℤ)
    (hleft : ∀ τ, left (Encoding.leafIndex τ) = encodingL a τ)
    (hright : ∀ τ, right (Encoding.leafIndex τ) = encodingR b τ)
    (ha : ∀ i, (left i).natAbs ≤ A) (hb : ∀ i, (right i).natAbs ≤ B)
    (hW : admissionWidth L m t qs.length A B ≤ W) :
    InputFits W (input m t qs left right) ∧
    ∃ y n, n + 1 ≤ timeBound m t qs ∧
      Runs W (program.program Reg.output) (State.init (input m t qs left right))
        ⟨program.size, y⟩ n ∧
      Executes W (program.program Reg.output) (State.init (input m t qs left right))
        (memoryEnd L m t qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m t qs.length + i.val) =
        Signed.encode (bilinearProduct a b (qs.get i))) ∧
      (∀ p, ¬(directoryBase L qs.length ≤ p ∧ p < memoryEnd L m t qs.length) →
        y.mem p = (State.init (input m t qs left right) : State registers).data.mem p) := by
  have hl : (fun τ => left (Encoding.leafIndex τ)) = encodingL a := funext hleft
  have hr : (fun τ => right (Encoding.leafIndex τ)) = encodingR b := funext hright
  obtain ⟨hi, y, n, hn, hp, he, hy, _, hv, _, hf⟩ :=
    runs_wide hmL qs hη left right ha hb hW
  refine ⟨hi, y, n, hn, hp, he, hy, ?_, hf⟩
  intro i
  rw [hv i, hl, hr, BoxQuery.queryValue_encoding ht _ (hη _ (List.get_mem qs i))]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch
