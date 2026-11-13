/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Parity.Complete
public import CslibFrontier.Probability.PMF.Uniform

/-!
# Uniform sampling at a prescribed parity

Sampling all but the final bit uniformly and completing the parity gives the uniform law on
that parity fiber. The existing XOR-sampling law is moved here unchanged. The fixed-parity law
also applies to binary syndrome distributions.

## Main definitions

* `Cslib.BitString.uniformParity`: the uniform distribution on words with a prescribed parity.

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_map_parityComplete`: parity completion is uniform.
* `Cslib.BitString.mem_support_uniformParity`: exactly the prescribed parity fiber is supported.
-/

public section

namespace Cslib.Probability.PMF

open BitString

/-- Completing uniform bits to parity `c` gives a uniform bit string of parity `c`. -/
theorem uniformOfFintype_map_parityComplete (c : Bool) (j : ℕ)
    (h : ({b : BitString (j + 1) | parity (j + 1) b = c} : Finset _).Nonempty) :
    (uniformOfFintype (BitString j)).map (parityComplete c) = uniformOfFinset _ h := by
  have : Nonempty {b : BitString (j + 1) // b ∈ ({b | parity (j + 1) b = c} : Finset _)} :=
    h.coe_sort
  rw [← uniformOfFintype_finset_map_val, ← uniformOfFintype_map_equiv (parityCompleteEquiv c j),
    PMF.map_comp]
  rfl

end Cslib.Probability.PMF

namespace Cslib.BitString

open Finset Probability
open scoped ENNReal

/-- The uniform law on `n`-bit words with parity `b`; positive dimension admits either bit. -/
noncomputable def uniformParity (n : ℕ) [NeZero n] (b : Bool) : PMF (BitString n) :=
  PMF.uniformOfFinset _ (parity_fiber_nonempty (Nat.pos_of_ne_zero (NeZero.ne n)) b)

/-- The support is exactly the chosen parity fiber. -/
theorem mem_support_uniformParity {n : ℕ} [NeZero n] (b : Bool) (x : BitString n) :
    x ∈ (uniformParity n b).support ↔ parity n x = b := by
  simp [uniformParity]

/-- Every word of the chosen parity has mass `1 / 2^(n-1)`, and other words have zero mass. -/
theorem uniformParity_apply {n : ℕ} [NeZero n] (b : Bool) (x : BitString n) :
    uniformParity n b x = if parity n x = b then (2 ^ (n - 1) : ℝ≥0∞)⁻¹ else 0 := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
  cases b <;> simp [uniformParity, card_filter_parity_eq_false hn,
    card_filter_parity_eq_true hn]

/-- Parity completion supplies an exact sampler for the uniform fixed-parity law. -/
theorem uniformParity_eq_map (b : Bool) (j : ℕ) :
    uniformParity (j + 1) b =
      (PMF.uniformOfFintype (BitString j)).map (parityComplete b) :=
  (PMF.uniformOfFintype_map_parityComplete b j _).symm

end Cslib.BitString
