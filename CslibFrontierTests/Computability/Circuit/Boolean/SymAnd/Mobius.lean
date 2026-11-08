/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Circuit.Boolean.SymAnd.Mobius

/-!
# Tests for the canonical `SYM ∘ AND` circuit of a low-degree function

Concrete instances of `CslibFrontier.Computability.Circuit.Boolean.SymAnd.Mobius`:

* the number of true bits of two inputs, of degree `1`, modulo `3`: the canonical gates are the two
  singletons, and the circuit evaluates to `out` of the count;
* exclusive or of two bits, `x₀ + x₁ - 2 x₀ x₁`, of degree `2`, modulo `3`: its Möbius
  coefficient `-2` at `{0, 1}` is stored as the least residue `1`, so `(true, true)` satisfies three
  gates and the circuit reads `3 mod 3 = 0`;
* truncating below the degree: without the gate `{0, 1}` the circuit no longer computes exclusive
  or.
-/

@[expose] public section

namespace CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.Mobius

open Cslib Cslib.BitString Cslib.Circuits.Boolean Finset

/-- The number of true bits among two inputs. -/
def ones (x : Fin 2 → Bool) : ℤ := bitVal ℤ (x 0) + bitVal ℤ (x 1)

theorem ones_mem_lowDegree : ones ∈ lowDegree ℤ (Fin 2) 1 :=
  Submodule.add_mem _ (bitVal_mem_lowDegree 0) (bitVal_mem_lowDegree 1)

/-- The canonical gates of `ones` are the two singletons, each once. -/
example : (SymAnd.ofLowDegree 1 3 ones fun z => decide (z = 1)).gates = {{0}, {1}} := by
  decide +kernel

/-- With `out z = (z = 1)` the canonical circuit decides "exactly one input is true". -/
example : (SymAnd.ofLowDegree 1 3 ones fun z => decide (z = 1)).eval ![true, false] = true := by
  rw [SymAnd.eval_ofLowDegree ones_mem_lowDegree (by decide)]
  decide

example : (SymAnd.ofLowDegree 1 3 ones fun z => decide (z = 1)).eval ![true, true] = false := by
  rw [SymAnd.eval_ofLowDegree ones_mem_lowDegree (by decide)]
  decide

/-- Fan-in at most `1` and at most `3 · 3 ^ 1` gates. -/
example : (SymAnd.ofLowDegree 1 3 ones fun z => decide (z = 1)).fanIn ≤ 1 ∧
    (SymAnd.ofLowDegree 1 3 ones fun z => decide (z = 1)).size ≤ 3 * (2 + 1) ^ 1 :=
  ⟨SymAnd.fanIn_ofLowDegree_le _ _ _ _, by
    simpa using SymAnd.size_ofLowDegree_le 1 (M := 3) (by decide) ones fun z => decide (z = 1)⟩

/-- Exclusive or of two bits as an integer function. -/
def xor2 (x : Fin 2 → Bool) : ℤ := bitVal ℤ (x 0 ^^ x 1)

/-- Every function on two bits has degree at most `2`. -/
theorem xor2_mem_lowDegree : xor2 ∈ lowDegree ℤ (Fin 2) 2 := by
  simpa using mem_lowDegree_self xor2

/-- The coefficient `-2` of `x₀ x₁` is stored as its least residue `1` modulo `3`. -/
example : (SymAnd.ofLowDegree 2 3 xor2 fun z => decide (z ≠ 0)).gates = {{0}, {1}, {0, 1}} := by
  decide +kernel

/-- The canonical circuit of `xor2` modulo `3`, with `out z = (z ≠ 0)`, computes exclusive or:
`(true, true)` satisfies all three gates, and `3 mod 3 = 0`. -/
example : (SymAnd.ofLowDegree 2 3 xor2 fun z => decide (z ≠ 0)).eval ![true, true] = false := by
  rw [SymAnd.eval_ofLowDegree xor2_mem_lowDegree (by decide)]
  decide

example : (SymAnd.ofLowDegree 2 3 xor2 fun z => decide (z ≠ 0)).eval ![false, true] = true := by
  rw [SymAnd.eval_ofLowDegree xor2_mem_lowDegree (by decide)]
  decide

/-- Below its degree the canonical circuit need not compute `out ∘ c`: truncating `xor2` at degree
`1` drops the gate `{0, 1}`, and the result reads `2 mod 3 ≠ 0` on `(true, true)`. -/
example : (SymAnd.ofLowDegree 1 3 xor2 fun z => decide (z ≠ 0)).eval ![true, true] = true := by
  decide +kernel

end CslibFrontierTests.Computability.Circuit.Boolean.SymAnd.Mobius
