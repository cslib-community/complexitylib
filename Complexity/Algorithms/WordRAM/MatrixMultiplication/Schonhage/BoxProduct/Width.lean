/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Exec
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct.Bounds
public import Complexity.Computability.WordRAM.Width
import Mathlib.Data.List.GetD

/-!
# Initialized routed box products and every wider execution prefix

The original matrices, raw coordinates and threshold initialize the actual program.
Exact original-order product values, restored input, pre-halt execution and charged halt
share one final memory. The minimum-admission run bounds every wider prefix independently
of its physical width, including all words and memory support.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual initialized execution of both original input modes, with one charged halt
and the same final state containing every matrix-product answer in request order. -/
theorem runs {w L m t N A : ℕ} (hw : 0 < w) (hm : m ≤ L) (ht : t ≤ m) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hmag : magnitudeBound L A < 2 ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget L m t N qs.length)) :
    InputFits (w + 2) (input bits L t X Y qs) ∧
    ∃ y n, n + 1 ≤ timeBound L m t qs + 1 ∧
      Runs (w + 2) ((program bits).program QueriedProduct.Reg.output)
        (State.init (input bits L t X Y qs)) ⟨(program bits).size, y⟩ n ∧
      Executes (w + 2) ((program bits).program QueriedProduct.Reg.output)
        (State.init (input bits L t X Y qs)) (QueriedProduct.outputBase L m N qs.length) (n + 1) ∧
      y.Bounded (w + 2) ∧
      (∀ i : Fin qs.length, y.mem (QueriedProduct.outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(QueriedProduct.inputEnd m N qs.length + 1 ≤ p ∧
        p < memoryEnd L m t N qs.length) →
        y.mem p = (State.init (input bits L t X Y qs) : State 160).data.mem p) := by
  have hi := input_fits hw hm bits X Y qs hX hY hmag hfit
  obtain ⟨y, he, hp, _, hv, hf⟩ := exec hw hm ht bits X Y qs
    (State.init (input bits L t X Y qs)).data
    (fun p hp hb => input_prefix bits X Y qs p hp hb)
    (input_threshold bits X Y qs) hX hY hbits hmag hfit
  have hy := he.bounded (Data.Bounded.init hi)
  obtain ⟨n, hn, he⟩ := he
  refine ⟨hi, y, n, by omega, ?_, ?_, hy, hv, hf⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := (program bits).program QueriedProduct.Reg.output) (Program.Contains.self _).append_left
  · simpa only [hp.output, State.init] using he.executes QueriedProduct.Reg.output

/-- Both native input modes run at every sufficiently wide original-input admission.
The scalar return is the first address of the complete original-order answer array. -/
theorem runs_wide {W L m t N A : ℕ} (hm : m ≤ L) (ht : t ≤ m) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hW : admissionWidth L m t N qs.length A ≤ W) :
    InputFits W (input bits L t X Y qs) ∧
    ∃ y n, n + 1 ≤ timeBound L m t qs + 1 ∧
      Runs W ((program bits).program QueriedProduct.Reg.output)
        (State.init (input bits L t X Y qs)) ⟨(program bits).size, y⟩ n ∧
      Executes W ((program bits).program QueriedProduct.Reg.output)
        (State.init (input bits L t X Y qs)) (QueriedProduct.outputBase L m N qs.length) (n + 1) ∧
      y.Bounded W ∧
      (∀ i : Fin qs.length, y.mem (QueriedProduct.outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ p, ¬(QueriedProduct.inputEnd m N qs.length + 1 ≤ p ∧
        p < memoryEnd L m t N qs.length) →
        y.mem p = (State.init (input bits L t X Y qs) : State 160).data.mem p) := by
  obtain ⟨hw, hmag, hfit⟩ := admission_bounds hW
  have htwo : W - 2 + 2 = W := by unfold admissionWidth at hW; omega
  simpa only [htwo] using
    runs hw hm ht bits X Y qs hX hY hbits hmag (by simpa only [htwo] using hfit)

/-- Original-input bounds on every successful prefix, independent of any larger admitted width. -/
theorem prefix_bounded {W L m t N A : ℕ} (hm : m ≤ L) (ht : t ≤ m) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hW : admissionWidth L m t N qs.length A ≤ W) (s : State 160) (steps : ℕ)
    (hr : Runs W ((program bits).program QueriedProduct.Reg.output)
      (State.init (input bits L t X Y qs)) s steps) :
    (∀ i, s.data.regs i < wordBound L m t N qs.length A) ∧
      (∀ p, s.data.mem p < wordBound L m t N qs.length A) ∧
      ∀ p, wordBound L m t N qs.length A ≤ p → s.data.mem p = 0 := by
  obtain ⟨hi, _, _, _, _, halt, _⟩ := runs_wide hm ht bits X Y qs hX hY hbits le_rfl
  exact hr.prefix_bounds_init
    (Code.not_readsWidth_program (not_readsWidth bits) QueriedProduct.Reg.output)
    hW hi halt (pow_admissionWidth_lt_wordBound L m t N qs.length A).le

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct
