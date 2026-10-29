/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.BravermanAbstract
import Complexity.Computability.Circuit.Pi
import Complexity.Probability.PMF.Expect

/-! # Concrete clients and non-vacuity checks for the Braverman abstract

Verifies that the circuit semantics of `BravermanAbstract` is the library's, that its
`k`-wise independence is the library's (`Cslib.BitString.IsKWiseIndependent`), that the xor sample
space on three bits is pairwise but not `3`-wise independent, and that the hypotheses of the
headline are satisfiable: the one-gate circuit `AND₃` with `q = 2` and depth `1`, under the
uniform distribution, which is `k`-wise independent for every `k`.
-/

namespace ComplexityTests.Abstracts.BravermanTests

open ComplexityAbstracts.BravermanAbstract
open Finset Cslib Cslib.BitString Cslib.Probability Cslib.Circuits Cslib.Circuits.Boolean
open scoped BigOperators

example : meaning = Unbounded.interpretation :=
  rfl

example {n k : ℕ} (X : PMF (Fin n → Bool)) : KWiseIndependent k X ↔ IsKWiseIndependent k X :=
  ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.symm

/-- The uniform distribution is `k`-wise independent for every `k`. -/
theorem kWiseIndependent_uniform {n : ℕ} (k : ℕ) :
    KWiseIndependent k (PMF.uniformOfFintype (Fin n → Bool)) :=
  ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.1
    (isKWiseIndependent_uniformOfFintype k)

/-- The xor sample space: two random bits and their sum. -/
private def xorSample : (Fin 2 → Bool) →+ Fin 3 → Bool where
  toFun s := ![s 0, s 1, s 0 + s 1]
  map_zero' := by decide
  map_add' := by decide

/-- The distribution of the xor sample. -/
private noncomputable def X : PMF (Fin 3 → Bool) :=
  (PMF.uniformOfFintype (Fin 2 → Bool)).map fun s => xorSample s

-- The xor sample is pairwise independent: any two of its bits are uniform.
example : KWiseIndependent 2 X :=
  ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.1
    (isKWiseIndependentHash_of_surjective xorSample (by decide)).isKWiseIndependent_map

-- It is not `3`-wise independent: every sample has even parity.
example : ¬KWiseIndependent 3 X := by
  intro h'
  have h := ComplexityAbstracts.BravermanBridge.isKWiseIndependent_iff_map_restrict.2 h'
  have hb : bias X univ = 1 := by
    rw [bias, X, PMF.sum_map_mul]
    simp only [chi_eq_signVal_parityOn]
    rw [← Cslib.Probability.PMF.sum_toReal (PMF.uniformOfFintype (Fin 2 → Bool))]
    refine sum_congr rfl fun s _ => ?_
    rw [show parityOn univ (xorSample s) = false by revert s; decide, signVal_false, mul_one]
  have := h univ ⟨0, mem_univ _⟩ (by simp)
  rw [hb, abs_one] at this
  norm_num at this

/-- The one-gate circuit computing `AND₃`. -/
abbrev and3 : Circuit ACBasis 3 1 := Circuit.oneGate (.and 3) id

-- The headline applies to `AND₃` with `q = 2` and depth `1` under the uniform distribution.
example (k : ℕ) (hk : 128 ^ 41 ≤ k) :
    |probabilityTrue (PMF.uniformOfFintype (Fin 3 → Bool)) and3 - fractionTrue and3| ≤
      1 / 2 ^ 2 :=
  braverman (d := 1) (q := 2) (by norm_num) and3 (by decide) (by decide)
    (Circuit.depth_oneGate _ _).le _ (kWiseIndependent_uniform k) (by norm_num at hk ⊢; exact hk)

-- `AND₃` is true on one of the eight inputs.
example : fractionTrue and3 = 1 / 8 := by
  rw [fractionTrue, show (univ.filter fun x : Fin 3 → Bool => and3.eval meaning x 0 = true).card = 1
    by decide]
  norm_num

end ComplexityTests.Abstracts.BravermanTests
