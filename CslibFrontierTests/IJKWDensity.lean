/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Boolean.HardnessAmplification.DirectProduct.Density
import CslibFrontier.Foundations.Data.Fintype.AgreeOn
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Concrete instances of the direct-product density lemmas

The tuple count is compared with a direct computation. The headline is instantiated for a
perfect direct product of `not` on `Bool` at `ε = 1/2`, `δ = 1`, which shows that its hypotheses
are satisfiable. This file is a module, so it sees `agreeing` only through `mem_agreeing`, as a
downstream module does; an agreement count stated without `agreeing` supplies the headline's
density hypothesis.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.IJKWDensity

open Cslib.Circuits.Boolean.DirectProduct Finset

/-! ### Counting tuples -/

-- The tuples in `Fin 3 → Bool` that agree with `y` on `{0}` number `2 ^ 2`.
example : #{b : Fin 3 → Bool | ∀ i ∈ ({0} : Finset (Fin 3)), b i = ![true, false, true] i} =
    Fintype.card Bool ^ #({0} : Finset (Fin 3))ᶜ := by
  convert Fintype.card_filter_forall_mem_eq ({0} : Finset (Fin 3)) ![true, false, true]

example :
    #{b : Fin 3 → Bool | ∀ i ∈ ({0} : Finset (Fin 3)), b i = ![true, false, true] i} = 4 := by
  decide

-- Every class of `univ` on `{0}` has `4` members, so no tuple has a class smaller than `1`.
example : (#{b ∈ (univ : Finset (Fin 3 → Bool)) |
      (#{y ∈ (univ : Finset (Fin 3 → Bool)) | ∀ i ∈ ({0} : Finset (Fin 3)), y i = b i} : ℝ) < 1} :
      ℝ) ≤ Fintype.card Bool ^ #({0} : Finset (Fin 3)) * 1 :=
  card_filter_card_filter_agree_lt_le univ {0} zero_le_one

/-! ### The agreement hypothesis -/

-- A downstream module states agreement as a count of the tuples on which `C'` agrees with the
-- direct product of `f`; `mem_agreeing` turns it into the headline's hypothesis `hG`.
example {U V : Type} [Fintype U] [DecidableEq U] [DecidableEq V] {k : ℕ}
    (C' : (Fin k → U) → Fin k → V) (f : U → V) {δ : ℝ}
    (h : δ * Fintype.card U ^ k ≤ #{y : Fin k → U | ∀ i, C' y i = f (y i)}) :
    δ * Fintype.card U ^ k ≤ #(agreeing C' f) := by
  convert h using 3
  ext y
  simp

/-! ### The headline -/

/-- The perfect direct product of `not`. -/
private def notK (k : ℕ) (y : Fin k → Bool) : Fin k → Bool := fun j => !y j

private theorem log_1024_lt : Real.log 1024 < 6.9315 := by
  have h : Real.log 1024 = 10 * Real.log 2 := by
    rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

private theorem log_sixteen_lt : Real.log 16 < 2.7726 := by
  have h : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]

-- A perfect product agrees everywhere, so the hypotheses hold for `s = 888`, `k = 1776` and
-- `m = 45`: an eighth of the seeds decode `not` with error at most `1`.
example : (1 : ℝ) / 8 * (1776).choose 888 * Fintype.card Bool ^ 1776 *
      Fintype.card (Trial Bool 1776) ^ 45 ≤
    #((univ.powersetCard 888 ×ˢ
        (univ : Finset ((Fin 1776 → Bool) × (Fin 45 → Trial Bool 1776)))).filter
      fun (P, b₀, v) => (#{x | dpDecode (notK 1776) false P b₀ v x ≠ !x} : ℝ) ≤
        1 / 2 * Fintype.card Bool) := by
  have hagree : agreeing (notK 1776) (fun x => !x) = univ := by
    ext y; simp [notK]
  refine card_filter_seed_dpDecode_err_le_ge (notK 1776) (fun x => !x) false (ε := 1 / 2)
    (δ := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl ?_ (by norm_num) ?_ ?_
  · rw [hagree, card_univ, Fintype.card_fun, Fintype.card_fin, one_mul, Nat.cast_pow]
  · norm_num
    linarith [log_1024_lt]
  · norm_num
    linarith [log_sixteen_lt]

end CslibFrontierTests.IJKWDensity
