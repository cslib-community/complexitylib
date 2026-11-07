/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import Complexity.Computability.Circuit.Boolean.SymAnd.Collapse
public import Complexity.Foundations.Data.Polynomial.ModulusAmplifier

/-!
# Tests for `SYM ∘ AND` circuits and modular tower collapse

Concrete evaluations of `SymAnd` circuits and of a two-layer modular tower, numeric checks of the
general-modulus amplifier, and non-vacuity witnesses for the collapse theorems of
`Complexity.Computability.Circuit.Boolean.SymAnd.Collapse`: the tower hypotheses are met by a
concrete tower whose output slot is neither constantly true nor constantly false.
-/

@[expose] public section

namespace ComplexityTests.Computability.Circuit.Boolean.SymAnd

open Cslib Cslib.BitString Cslib.Circuits.Boolean Polynomial

/-! ### Concrete `SYM ∘ AND` circuits -/

/-- Parity of three bits: three singleton AND gates under the symmetric gate "odd count". -/
def parity3 : SymAnd (Fin 3) := ⟨{{0}, {1}, {2}}, fun z => z % 2 == 1⟩

example : parity3.eval ![true, true, false] = false := by decide
example : parity3.eval ![true, true, true] = true := by decide
example : parity3.size = 3 := by decide
example : parity3.fanIn = 1 := by decide

/-- Majority of three bits as the threshold "at least one" over the three pairwise ANDs; a gate
of fan-in two. -/
def maj3 : SymAnd (Fin 3) := ⟨{{0, 1}, {0, 2}, {1, 2}}, fun z => decide (1 ≤ z)⟩

example : maj3.eval ![true, false, true] = true := by decide
example : maj3.eval ![false, false, true] = false := by decide
example : maj3.fanIn = 2 := by decide

/-- Repeated gates count with multiplicity. -/
example : (⟨{{0}, {0}}, fun z => z == 2⟩ : SymAnd (Fin 1)).eval ![true] = true := by decide

/-- The empty AND gate is satisfied everywhere. -/
example : (⟨{∅}, fun z => z == 1⟩ : SymAnd (Fin 2)).eval ![false, false] = true := by decide

example : (SymAnd.slot (2 : Fin 3)).eval ![false, false, true] = true := by simp

/-! ### The general-modulus amplifier -/

/-- `1 - p_2(y) = 3y² - 2y³`; at `y = 3` (divisible by `3`) it is `≡ 0 (mod 9)`. -/
example : (1 - (parityAmplifier 2).eval (3 : ℤ)) % 9 = 0 := by
  rw [parityAmplifier_two]
  simp only [eval_add, eval_sub, eval_one, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

/-- At `y = 4 ≡ 1 (mod 3)` it is `≡ 1 (mod 9)`: `3 * 16 - 2 * 64 = -80 ≡ 1 (mod 9)`. -/
example : (1 - (parityAmplifier 2).eval (4 : ℤ)) % 9 = 1 := by
  rw [parityAmplifier_two]
  simp only [eval_add, eval_sub, eval_one, eval_mul, eval_pow, eval_X, eval_ofNat]
  decide

/-- The Fermat-normalized indicator at the prime `5` and precision `3`. -/
example : 1 - (parityAmplifier 3).eval ((7 : ℤ) ^ (5 - 1)) ≡ 1 [ZMOD (5 : ℤ) ^ 3] := by
  simpa using one_sub_parityAmplifier_eval_pow_modEq Nat.prime_five 3 7

/-! ### A two-layer modular tower -/

/-- Bottom layer (`MOD_2`): slot `2` becomes `x₀ ⊕ x₁`; the input slots pass through. -/
def bottom : ModPolyLayer (Fin 3) where
  p := 2
  q := fun t v => if t = 2 then bitVal ℤ (v 0) + bitVal ℤ (v 1) else bitVal ℤ (v t)

/-- Top layer (`MOD_3`): slot `2` becomes `x₀ + x₁ + 2 (x₀ ⊕ x₁) ≢ 0 (mod 3)`, which is
`x₀ ∧ x₁`; the input slots pass through. -/
def top : ModPolyLayer (Fin 3) where
  p := 3
  q := fun t v => if t = 2 then bitVal ℤ (v 0) + bitVal ℤ (v 1) + 2 * bitVal ℤ (v 2)
    else bitVal ℤ (v t)

example : ModPolyLayer.run [top, bottom] ![true, true, false] 2 = true := by decide
example : ModPolyLayer.run [top, bottom] ![true, false, false] 2 = false := by decide
example : ModPolyLayer.run [top, bottom] ![false, true, false] 2 = false := by decide
example : ModPolyLayer.run [top, bottom] ![false, false, false] 2 = false := by decide

/-- The slot polynomials of `bottom` have degree at most one. -/
theorem bottom_q_mem_lowDegree (t : Fin 3) : bottom.q t ∈ lowDegree ℤ (Fin 3) 1 := by
  by_cases ht : t = 2
  · convert Submodule.add_mem _ (bitVal_mem_lowDegree (R := ℤ) (0 : Fin 3))
      (bitVal_mem_lowDegree (R := ℤ) (1 : Fin 3)) using 1
    funext v
    simp [bottom, ht]
  · convert bitVal_mem_lowDegree (R := ℤ) t using 1
    funext v
    simp [bottom, ht]

/-- The slot polynomials of `top` have degree at most one. -/
theorem top_q_mem_lowDegree (t : Fin 3) : top.q t ∈ lowDegree ℤ (Fin 3) 1 := by
  by_cases ht : t = 2
  · convert Submodule.add_mem _ (Submodule.add_mem _ (bitVal_mem_lowDegree (R := ℤ) (0 : Fin 3))
      (bitVal_mem_lowDegree (R := ℤ) (1 : Fin 3)))
      (Submodule.smul_mem _ (2 : ℤ) (bitVal_mem_lowDegree (R := ℤ) (2 : Fin 3))) using 1
    funext v
    simp [top, ht]
  · convert bitVal_mem_lowDegree (R := ℤ) t using 1
    funext v
    simp [top, ht]

/-- The tower `[top, bottom]` meets the collapse hypotheses with `B = 3`: primes `3` and `2`, and
slot polynomials of degree at most one. -/
theorem tower_hyps : ∀ L ∈ [top, bottom],
    L.p.Prime ∧ L.p ≤ 3 ∧ ∀ t, L.q t ∈ lowDegree ℤ (Fin 3) 3 := by
  intro L hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl
  · exact ⟨Nat.prime_three, le_rfl, fun t => lowDegree_mono (by norm_num) (top_q_mem_lowDegree t)⟩
  · exact ⟨Nat.prime_two, by norm_num [bottom],
      fun t => lowDegree_mono (by norm_num) (bottom_q_mem_lowDegree t)⟩

/-- **Non-vacuity of the tower collapse.** The output slot of `[top, bottom]` is a `SYM ∘ AND`
circuit within the stated bounds, and that circuit takes both values. -/
theorem collapse_nonvacuous : ∃ C : SymAnd (Fin 3),
    (∀ v, C.eval v = ModPolyLayer.run [top, bottom] v 2) ∧
      C.fanIn ≤ (2 * 3) ^ 5 ^ [top, bottom].length ∧
      C.size ≤ 2 ^ (2 * 3) ^ 5 ^ [top, bottom].length ∧
      C.eval ![true, true, false] = true ∧ C.eval ![true, false, false] = false := by
  obtain ⟨C, hC, hf, hs⟩ :=
    SymAnd.exists_eval_eq_run_apply [top, bottom] 2 tower_hyps (by decide)
  exact ⟨C, hC, hf, hs, by rw [hC]; decide, by rw [hC]; decide⟩

/-- The single-layer collapse applies to a `SYM ∘ AND` circuit above `top` with `k = 2`. -/
example : ∃ C' : SymAnd (Fin 3), ∀ v, C'.eval v = parity3.eval (top.step v) := by
  obtain ⟨C', hC', -, -⟩ := SymAnd.exists_eval_eq_eval_step parity3 top Nat.prime_three
    top_q_mem_lowDegree (k := 2) (by decide)
  exact ⟨C', hC'⟩

end ComplexityTests.Computability.Circuit.Boolean.SymAnd
