/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Input

/-!
# Initialized flat sparse box queries

The standard compiler runs the actual constructor and native worklist from original
signed arrays. The same data witness gives the exact query answer, prefix execution,
charged halt and allocation frame at every admitted physical width.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual initialized execution and charged halt share the exact finite-query witness. -/
theorem runs_wide {W L m t A B : ℕ} (q : Fin (10 ^ L))
    (hη : (innerSetO (PrunedQuery.queryAt q)).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t A B ≤ W) :
    InputFits W (input L m t q a b) ∧
    ∃ y n, n + 1 ≤ timeBound m t (PrunedQuery.queryAt q) ∧
      Runs W (program.program Reg.answer) (State.init (input L m t q a b))
        ⟨program.size, y⟩ n ∧
      Executes W (program.program Reg.answer) (State.init (input L m t q a b))
        (Signed.encode (queryValue m t (PrunedQuery.queryAt q)
          (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)))) (n + 1) ∧
      y.Bounded W ∧
      Parameters L t q.val 5 (5 + 10 ^ L) (directoryBase L) (valueBase L m t)
        (boxes L m t).card (stackBase L m t) y ∧
      y.regs Reg.top = 0 ∧
      y.regs Reg.answer = Signed.encode (queryValue m t (PrunedQuery.queryAt q)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ))) ∧
      Readback m t (directoryBase L) (valueBase L m t) 5 (5 + 10 ^ L)
        (fun τ => a (Encoding.leafIndex τ)) (fun τ => b (Encoding.leafIndex τ)) y.mem ∧
      (∀ p, ¬(directoryBase L ≤ p ∧ p < memoryEnd L m t) →
        y.mem p = (State.init (input L m t q a b) : State registers).data.mem p) := by
  obtain ⟨_, haddr, hmag⟩ := admission_bounds hW
  have hwidth : W - 2 + 2 = W := by unfold admissionWidth at hW; omega
  obtain ⟨hi, y, ⟨n, hn, he⟩, hy, yp, yt, ya, yr, yf⟩ :=
    exec_input q hη a b ha hb (by simpa only [hwidth] using haddr) hmag
  refine ⟨by simpa only [hwidth] using hi, y, n, ?_, ?_, ?_,
    by simpa only [hwidth] using hy, yp, yt, ya, yr, yf⟩
  · have ht : 0 < timeBound m t (PrunedQuery.queryAt q) := by unfold timeBound; omega
    omega
  · simpa only [hwidth, Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := program.program Reg.answer) (Program.Contains.self _).append_left
  · simpa only [hwidth, ya, State.init] using he.executes Reg.answer

/-- All reachable initialized states have fitting physical words at the admitted width. -/
theorem bounded_reachable {W L m t A B n : ℕ} (q : Fin (10 ^ L))
    (hη : (innerSetO (PrunedQuery.queryAt q)).card = m)
    (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t A B ≤ W) {y : State registers}
    (hy : Runs W (program.program Reg.answer) (State.init (input L m t q a b)) y n) :
    y.data.Bounded W := hy.bounded_init (runs_wide q hη a b ha hb hW).1

/-- Canonical left/right encodings give the original bilinear product, with the actual
initialized prefix and charged halt tied to the same final answer state. -/
theorem runs_bilinear {W L m t A B : ℕ} (q : Fin (10 ^ L))
    (hη : (innerSetO (PrunedQuery.queryAt q)).card = m) (ht : t ≤ m)
    (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (left right : Fin (10 ^ L) → ℤ)
    (hleft : ∀ τ, left (Encoding.leafIndex τ) = encodingL a τ)
    (hright : ∀ τ, right (Encoding.leafIndex τ) = encodingR b τ)
    (ha : ∀ i, (left i).natAbs ≤ A) (hb : ∀ i, (right i).natAbs ≤ B)
    (hW : admissionWidth L m t A B ≤ W) :
    InputFits W (input L m t q left right) ∧
    ∃ y n, n + 1 ≤ timeBound m t (PrunedQuery.queryAt q) ∧
      Runs W (program.program Reg.answer) (State.init (input L m t q left right))
        ⟨program.size, y⟩ n ∧
      Executes W (program.program Reg.answer) (State.init (input L m t q left right))
        (Signed.encode (bilinearProduct a b (PrunedQuery.queryAt q))) (n + 1) ∧
      y.Bounded W ∧
      y.regs Reg.answer = Signed.encode (bilinearProduct a b (PrunedQuery.queryAt q)) ∧
      (∀ p, ¬(directoryBase L ≤ p ∧ p < memoryEnd L m t) →
        y.mem p = (State.init (input L m t q left right) : State registers).data.mem p) := by
  have hl : (fun τ => left (Encoding.leafIndex τ)) = encodingL a := funext hleft
  have hr : (fun τ => right (Encoding.leafIndex τ)) = encodingR b := funext hright
  have hvalue : queryValue m t (PrunedQuery.queryAt q)
      (fun τ => left (Encoding.leafIndex τ)) (fun τ => right (Encoding.leafIndex τ)) =
      bilinearProduct a b (PrunedQuery.queryAt q) := by
    rw [hl, hr]
    exact queryValue_encoding ht _ hη a b
  obtain ⟨hi, y, n, hn, hp, he, hy, _, _, ha, _, hf⟩ := runs_wide q hη left right ha hb hW
  exact ⟨hi, y, n, hn, hp, by simpa only [hvalue] using he,
    hy, by simpa only [hvalue] using ha, hf⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery
