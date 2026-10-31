/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Flat
public import Mathlib.Data.Nat.Log

/-!
# Positive original-input width admission for native queried products

## Main results

* `QueriedProduct.admissionWidth`: sufficient physical width, derived only from original scalar
  dimensions, entry magnitude and request count.
* `QueriedProduct.runs_wide`: actual initialized product execution at every sufficiently wide
  admitted width, with guaranteed input fit and no physical-width reads by the code.

The logarithm applies to the explicit original-input magnitude/address envelope. Relating it
to a polynomially bounded whole-3SUM input remains separate composition work under #1394.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- An original-input-derived sufficient physical width, including the existing two-bit
native signed-kernel margin. It is not read by the native program. -/
@[expose] public def admissionWidth (L m N Q A : ℕ) : ℕ :=
  Nat.clog 2 (magnitudeBound L A + wordBudget L m N Q + 1) + 3

/-- The physical threshold is strictly positive even for empty and zero-magnitude inputs. -/
public theorem admissionWidth_pos (L m N Q A : ℕ) : 0 < admissionWidth L m N Q A := by
  unfold admissionWidth
  omega

/-- Mathlib's ceiling logarithm supplies both numerical admission hypotheses. -/
public theorem admission_bounds {W L m N Q A : ℕ} (hW : admissionWidth L m N Q A ≤ W) :
    0 < W - 2 ∧ magnitudeBound L A < 2 ^ ((W - 2) - 1) ∧ Fits W (wordBudget L m N Q) := by
  have hl := Nat.le_pow_clog (by decide : 1 < (2 : ℕ))
    (magnitudeBound L A + wordBudget L m N Q + 1)
  have he : Nat.clog 2 (magnitudeBound L A + wordBudget L m N Q + 1) ≤ (W - 2) - 1 := by
    unfold admissionWidth at hW
    omega
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) he
  refine ⟨by unfold admissionWidth at hW; omega, by omega, ?_⟩
  change wordBudget L m N Q < 2 ^ W
  have hp' := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega :
    Nat.clog 2 (magnitudeBound L A + wordBudget L m N Q + 1) ≤ W)
  omega

/-- Both real input modes run at every sufficiently wide physical width. All product values,
the charged halt and complete restored-input/outside frame refer to the same actual run. -/
public theorem runs_wide {W L m N A : ℕ} (hm : m ≤ L) (bits : Bool)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (hX : ∀ i k, |X i k| ≤ (A : ℤ))
    (hY : ∀ k j, |Y k j| ≤ (A : ℤ))
    (hbits : bits = true → (∀ i k, 0 ≤ X i k) ∧ (∀ k j, 0 ≤ Y k j))
    (hW : admissionWidth L m N qs.length A ≤ W) :
    InputFits W (input bits L X Y qs) ∧
    ∃ y n, n ≤ timeBound hm qs ∧
      Runs W ((program bits).program Reg.output) (State.init (input bits L X Y qs))
        ⟨(program bits).size, y⟩ n ∧
      Executes W ((program bits).program Reg.output) (State.init (input bits L X Y qs))
        (outputBase L m N qs.length) (n + 1) ∧ y.Bounded W ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, ¬(inputEnd m N qs.length ≤ a ∧ a < memoryEnd L m N qs.length) →
        y.mem a = (State.init (input bits L X Y qs) : State 160).data.mem a) := by
  obtain ⟨hw, hmagnitude, haddress⟩ := admission_bounds hW
  have htwo : W - 2 + 2 = W := by unfold admissionWidth at hW; omega
  have h := runs hw hm bits X Y qs hX hY hbits hmagnitude (by simpa only [htwo] using haddress)
  simpa only [htwo] using h

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
