/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Circuit.Boolean.Braverman.Fooling
import Complexity.Computability.Circuit.Pi
import Complexity.Foundations.BooleanAnalysis.FourierBitVal

/-!
# Polylogarithmic independence fools AC⁰

Concrete clients of Braverman's theorem: the witness form of the one-sided argument applied to the
pairwise independent xor sample space, Fourier truncation of a single bit, and the explicit form of
Braverman's theorem applied to the one-gate circuit `AND₃` under the uniform distribution, which is
`k`-wise independent for every `k`.
-/

namespace ComplexityTests.BravermanFooling

open Finset Cslib Cslib.BitString Cslib.Probability Cslib.Circuits Cslib.Circuits.Boolean
  Cslib.Circuits.Boolean.Braverman
open scoped BigOperators

/-- The xor sample space: two random bits and their sum. -/
private def xorSample : (Fin 2 → Bool) →+ Fin 3 → Bool where
  toFun s := ![s 0, s 1, s 0 + s 1]
  map_zero' := by decide
  map_add' := by decide

/-- The distribution of the xor sample. -/
private noncomputable def X : PMF (Fin 3 → Bool) :=
  (PMF.uniformOfFintype (Fin 2 → Bool)).map fun s => xorSample s

/-- The xor sample is a pairwise independent distribution. -/
private theorem isKWiseIndependent_X : IsKWiseIndependent 2 X :=
  (isKWiseIndependentHash_of_surjective xorSample (by decide)).isKWiseIndependent_map

-- The witness form of Braverman's argument under pairwise independence, approximating the first
-- bit by itself with the empty witness: the error `4 · 0 + 2 (1 + 1)² · 0` vanishes.
example : Fools X (4 * 0 + 2 * (1 + 1) ^ 2 * 0) fun x => bitVal ℝ (x 0) :=
  isKWiseIndependent_X.fools_bitVal_of_witness (E := fun _ => false) (e := fun _ => 0)
    (D := 1) (t := 0) (bitVal_mem_lowDegree 0) (const_mem_lowDegree 0 0) le_rfl
    (fun _ _ => rfl) (fun x => by cases x 0 <;> norm_num) (by simp) (by simp) (by simp)

-- Fourier truncation of the first bit at level `0` leaves its weight above level `0`.
example : ∃ g ∈ lowDegree ℝ (Fin 3) 0, 𝔼 x : Fin 3 → Bool, (bitVal ℝ (x 0) - g x) ^ 2 =
    (∑ S with 0 < #S, fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0)) S ^ 2) / 4 :=
  exists_mem_lowDegree_expect_sq_bitVal_sub_eq (fun x => x 0) 0

/-- The one-gate circuit computing `AND₃`. -/
abbrev and3 : Circuit Unbounded.signature 3 1 := Circuit.oneGate (.and 3) id

-- Braverman's theorem for `AND₃`, with `q = 2` and depth `1`: every
-- `128 ^ 41`-wise independent distribution, such as the uniform one, `1 / 4`-fools it.
example (k : ℕ) (hk : 128 ^ 41 ≤ k) :
    Fools (PMF.uniformOfFintype (Fin 3 → Bool)) (1 / 2 ^ 2)
      fun x => bitVal ℝ (and3.eval Unbounded.interpretation x 0) :=
  fools_of_isKWiseIndependent (d := 1) (q := 2) (by norm_num) and3 (by decide) (by decide)
    (Circuit.depth_oneGate _ _).le (by norm_num at hk ⊢; exact hk)
    (isKWiseIndependent_uniformOfFintype k)

end ComplexityTests.BravermanFooling
