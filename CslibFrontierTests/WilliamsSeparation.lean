/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.WilliamsSeparation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Streaming

/-!
# Clients of Williams's time–space separation corollaries

Exercises the time–space separations derived from `DTIME_subset_DSPACE_sqrt` and
`DSPACE_ssubset_DSPACE`: subquadratic real-exponent separations for linear and quadratic space,
the sharper `n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2` linear-space separation, polynomial exponent
separations, the explicit separating diagonal witness, and extensions of the square-root-space
inclusion to eventually linear and sublinear time bounds.
-/

public section

namespace CslibFrontierTests.WilliamsSeparation

open Cslib.Complexity Filter
open _root_.Turing.MultiTapeTM

/-- Odd-parity predicate on bit words, reused as a concrete linear-time client. -/
def oddOnes (word : List Bool) : Bool := word.foldl (fun b x => b ^^ x) false

private theorem oddOnes_mem_DTIME_id : {w | oddOnes w = true} ∈ DTIME encBits (fun n => n) :=
  setOf_mem_DTIME_of_computableInO
    (ComputableTidilyInO.foldl_bits_finite encBool (fun b x => b ^^ x) false).computableInO
    (fun _ => le_rfl)

/-- `oddOnes` lies in linear space via `DTIME_id_ssubset_DSPACE_id`. -/
example : {w | oddOnes w = true} ∈ DSPACE encBits (fun n => n) :=
  DTIME_id_ssubset_DSPACE_id.subset oddOnes_mem_DTIME_id

/-- Extending the square-root-space inclusion to an eventually linear time bound (zero below `10`).
-/
example : {w | oddOnes w = true} ∈
    DSPACE encBits (fun n => Nat.sqrt ((if n < 10 then 0 else n) *
      (Nat.log2 (if n < 10 then 0 else n) + 1))) :=
  DTIME_subset_DSPACE_sqrt_of_eventually_le encBits
    ((eventually_ge_atTop 10).mono fun n hn => by simp [show ¬n < 10 by omega])
    (DTIME_mono_of_eventually_le
      ((eventually_ge_atTop 10).mono fun n hn => by simp [show ¬n < 10 by omega])
      oddOnes_mem_DTIME_id)

/-- Arbitrary sublinear bound handled by `DTIME_subset_DSPACE_sqrt_max`. -/
example (A : Set (List Bool)) (hA : A ∈ DTIME encBits (fun _ => 1)) :
    A ∈ DSPACE encBits (fun n => Nat.sqrt (max n 1 * (Nat.log2 (max n 1) + 1))) :=
  DTIME_subset_DSPACE_sqrt_max encBits (fun _ => 1) hA

/-- Linear space is not contained in deterministic time `n ^ (199 / 100)`. -/
example : ¬ DSPACE encBits (fun n => n) ⊆
    DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - (1 : ℝ) / 100)⌋₊) :=
  DSPACE_id_not_subset_DTIME_rpow_sub (by norm_num)

/-- Even when `2 - ε < 0` (edge case `ε = 3`), the subquadratic separation theorem still holds. -/
example : DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - (3 : ℝ))⌋₊) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_rpow_sub_ssubset_DSPACE_id (by norm_num)

/-- Exponent-below-two client at `3 / 2`. -/
example : DTIME encBits (fun n => ⌊(n : ℝ) ^ ((3 : ℝ) / 2)⌋₊) ⊂ DSPACE encBits (fun n => n) :=
  DTIME_rpow_lt_two_ssubset_DSPACE_id (by norm_num)

/-- Sharper logarithmic-factor linear-space separation:
`DTIME (n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2) ⊂ DSPACE (n)`. -/
example :
    DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) ⊂ DSPACE encBits (fun n => n) ∧
    ¬ DSPACE encBits (fun n => n) ⊆ DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) :=
  ⟨DTIME_sq_div_log2_sq_ssubset_DSPACE_id, DSPACE_id_not_subset_DTIME_sq_div_log2_sq⟩

/-- Polynomial time–space separations: `DTIME (n ^ 3) ⊂ DSPACE (n ^ 2)`. -/
example : DTIME encBits (· ^ 3) ⊂ DSPACE encBits (· ^ 2) ∧
    ¬ DSPACE encBits (· ^ 2) ⊆ DTIME encBits (· ^ 3) :=
  ⟨DTIME_pow_ssubset_DSPACE_pow (by decide) (by decide),
    DSPACE_pow_not_subset_DTIME_pow (by decide) (by decide)⟩

/-- General constructible space `(n + 1) ^ 2`: subquadratic and log-sharpened separations. -/
example :
    DTIME encBits (fun n => ⌊(((n + 1) ^ 2 : ℕ) : ℝ) ^ (2 - (1 : ℝ) / 10)⌋₊) ⊂
      DSPACE encBits (fun n => (n + 1) ^ 2) ∧
    DTIME encBits (fun n => ((n + 1) ^ 2) ^ 2 / (Nat.log2 ((n + 1) ^ 2) + 1) ^ 2) ⊂
      DSPACE encBits (fun n => (n + 1) ^ 2) := by
  have hn : ∀ᶠ n in atTop, n ≤ (n + 1) ^ 2 :=
    Eventually.of_forall fun n => by nlinarith
  exact ⟨DTIME_rpow_sub_ssubset_DSPACE (spaceConstructible_succ_pow 2) hn (by norm_num),
    DTIME_sq_div_log2_sq_ssubset_DSPACE (spaceConstructible_succ_pow 2) hn⟩

/-- Explicit diagonal witness separating linear space from `DTIME (⌊n ^ (199/100)⌋)` and
`DTIME (n ^ 2 / (⌊log₂ n⌋ + 1) ^ 2)`. -/
example :
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∈ DSPACE encBits (fun n => n) ∧
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∉
      DTIME encBits (fun n => ⌊(n : ℝ) ^ (2 - (1 : ℝ) / 100)⌋₊) ∧
    {x | spaceDiagonal (fun n => 4 * n) x = true} ∉
      DTIME encBits (fun n => n ^ 2 / (Nat.log2 n + 1) ^ 2) :=
  ⟨setOf_spaceDiagonal_id_mem_DSPACE,
    setOf_spaceDiagonal_id_notMem_DTIME_rpow_sub (by norm_num),
    setOf_spaceDiagonal_id_notMem_DTIME_sq_div_log2_sq⟩

/-- Little-o interface instantiated directly for `DTIME (n) ⊂ DSPACE ((n + 1) ^ 2)`. -/
example : DTIME encBits (fun n => n) ⊂ DSPACE encBits (fun n => (n + 1) ^ 2) :=
  DTIME_ssubset_DSPACE_of_isLittleO (spaceConstructible_succ_pow 2)
    (Eventually.of_forall fun n => (Nat.log2_le_self n).trans (by nlinarith))
    (by
      refine Asymptotics.isLittleO_iff.mpr fun ε hε => ?_
      filter_upwards [eventually_ge_atTop (Nat.ceil (2 / ε) + 2)] with n hn
      have hn1 : 1 ≤ n := by omega
      have hlog : Nat.log2 n ≤ n := Nat.log2_le_self n
      rw [max_self, Real.norm_natCast, Real.norm_natCast]
      have hnum : ((n * (Nat.log2 n + 1) : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
        have hnat : n * (Nat.log2 n + 1) ≤ 2 * n ^ 2 := by nlinarith
        exact_mod_cast hnat
      have heps : 2 / ε ≤ n :=
        (Nat.le_ceil _).trans (by exact_mod_cast (by omega : Nat.ceil (2 / ε) ≤ n))
      have h1 : 2 ≤ ε * n := by linarith [(div_le_iff₀ hε).mp heps]
      have hcube : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 :=
        pow_le_pow_right₀ (by exact_mod_cast hn1) (by decide)
      have hpow4 : ((((n + 1) ^ 2) ^ 2 : ℕ) : ℝ) ≥ (n : ℝ) ^ 4 := by
        push_cast
        nlinarith
      calc ((n * (Nat.log2 n + 1) : ℕ) : ℝ) ≤ 2 * (n : ℝ) ^ 2 := hnum
        _ ≤ ε * (n : ℝ) * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ε * (n : ℝ) ^ 3 := by ring
        _ ≤ ε * (n : ℝ) ^ 4 := by nlinarith
        _ ≤ ε * ((((n + 1) ^ 2) ^ 2 : ℕ) : ℝ) := by gcongr)

end CslibFrontierTests.WilliamsSeparation
