/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandFlat

/-!
# Thin-regime native instruction bound

## Main results

* `BandPreparation.runs_thin`: actual initialized native execution, including the halt,
  within `81920*(L+1)*N²/(4^m)^(1/18)` at `L=19m`, `N≥(4^m)^18`.
* `BandPreparation.width_exists`: original magnitude and parameter inequalities are jointly
  satisfiable for every finite input bound, including positive thin parameters.

The result concerns shared-band preparation and encoding only. Pruned queries, products and
the whole ordinary 3SUM endpoint remain separate obligations.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- All charged preparation and encoder instructions, including the final halt, satisfy
the finite thin-regime saving. Both the coefficient and polynomial exponent are fixed. -/
theorem runs_thin {w m N : ℕ} (hw : 0 < w) (hN : D m ^ 18 ≤ N)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (A : ℤ) (hA : 0 ≤ A) (hX : ∀ i k, |X i k| ≤ A) (hY : ∀ k j, |Y k j| ≤ A)
    (hmag : (7 ^ (19 * m) : ℕ) * A < (2 : ℤ) ^ (w - 1))
    (hfit : Fits (w + 2) (wordBudget (19 * m) m N)) :
    ∃ n, Executes (w + 2) (program.program catalogue)
        (State.init (input (19 * m) m N X Y)) (catalogueBase (19 * m) m N) n ∧
      (n : ℝ) ≤ 81920 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 /
        (D m : ℝ) ^ (1 / 18 : ℝ) := by
  obtain ⟨_, _, n, hn, _, he, _⟩ := runs hw (show m ≤ 19 * m by omega)
    X Y A hA hX hY hmag hfit
  refine ⟨n + 1, he, ?_⟩
  have hpos : 1 ≤ timeBound (19 * m) m N := by
    apply Nat.succ_le_of_lt
    unfold timeBound
    positivity
  have hc : n + 1 ≤ 2 * timeBound (19 * m) m N := by omega
  have hcR : ((n + 1 : ℕ) : ℝ) ≤ 2 * (timeBound (19 * m) m N : ℝ) := by
    exact_mod_cast hc
  have ht := thin_timeBound_div m N hN
  calc
    ((n + 1 : ℕ) : ℝ) ≤ 2 * (timeBound (19 * m) m N : ℝ) := hcR
    _ ≤ 2 * (40960 * ((19 * m + 1 : ℕ) : ℝ) * (N : ℝ) ^ 2 /
        (D m : ℝ) ^ (1 / 18 : ℝ)) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by ring

/-- A concrete, deliberately generous width witnesses simultaneous signed-magnitude and
unsigned-address fits. This proves nonvacuity without enumerating a thin matrix. -/
theorem width_exists (L m N : ℕ) (A : ℤ) (hA : 0 ≤ A) :
    ∃ w, 0 < w ∧ (7 ^ L : ℕ) * A < (2 : ℤ) ^ (w - 1) ∧
      Fits (w + 2) (wordBudget L m N) := by
  let q := wordBudget L m N + 7 ^ L * A.natAbs + 3
  refine ⟨q + 1, by omega, ?_, ?_⟩
  · have hnat : 7 ^ L * A.natAbs < 2 ^ q :=
      (Nat.lt_two_pow_self (n := 7 ^ L * A.natAbs)).trans_le
        (Nat.pow_le_pow_right (by decide) (by dsimp [q]; omega))
    have hz : ((7 ^ L * A.natAbs : ℕ) : ℤ) < (2 : ℤ) ^ q := by exact_mod_cast hnat
    simpa only [Nat.add_sub_cancel, Nat.cast_mul, Int.natCast_natAbs,
      abs_of_nonneg hA] using hz
  · exact (fits_self (wordBudget L m N)).mono (by dsimp [q]; omega)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
