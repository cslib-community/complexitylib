/-
Copyright (c) 2026 Samuel Schlesinger, Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Mayank Rathee
-/

import CslibFrontier.Crypto.Protocols.PIR.Collusion
import CslibFrontier.Crypto.Protocols.PIR.Cube
import CslibFrontier.Crypto.Protocols.PIR.Shamir
import CslibFrontier.Probability.PMF.Map
import Mathlib.Tactic.NormNum

/-!
# Tests: coalition-private (`t`-private) PIR and polynomial Shamir schemes

* Equivalence of `Scheme.IsTPrivate 1` with `Scheme.IsPrivate` and of `Scheme.IsTPrivate t` with
  `t`-tuple query independence (`Scheme.isTPrivate_iff_tuple`).
* Sharpness on `PIR.twoServer`: it is `1`-private on `Fin 2`, communicates `6` bits, yet is not
  `2`-private because both servers XOR their queries to recover `eᵢ`.
* Full-coalition lower bounds (`t ≥ k`): no zero-server scheme is correct on `Fin 1`, and no
  `3`-private `3`-server scheme on `Fin 4` communicates `3` bits.
* Linear Shamir PIR (`PIR.shamir`) over `ZMod 5`:
  - `2`-private `3`-server PIR on `Fin 4` is correct and `2`-private (`eval_coalitionQuery_shamir`
    gives exact uniformity on `{0, 1}`), but not `3`-private;
  - `1`-private `3`-server PIR on `Fin 2` is not `2`-private (`t + 1 = 2 < k = 3`), showing the
    Shamir threshold is tight strictly below full collusion;
  - matrix-balanced `(t + 1)`-server `O(√n)` PIR (`hasTPrivateScheme_of_le_mul_self`) solves
    `16`-bit databases with `3` servers, `2`-privacy, and `72` bits.
* Degree-`d` polynomial PIR (`PIR.shamirCube`, `hasTPrivateScheme_prime_of_le_pow`, and
  `rows`-balanced `hasTPrivateScheme_prime_rows_of_le_pow`):
  - `d = 2, t = 1, k = 3` over `ZMod 5` is correct and `1`-private, and not `2`-private
    (`not_isTPrivate_succ_shamirCube`);
  - unbalanced `d = 2, t = 2, k = 5` over `ZMod 7` solves `Fin 16` with `135` bits;
  - balanced `c = 3` (`d = 2`), `t = 2`, **exact `k = c * t = 6` servers** over `ZMod 7` solves
    `Fin 1000` (`10 ^ 3`) with `540 < 1000` bits (CGKS §§1.1 & 3.4), and induces
    `HasScheme (Fin 1000) 6 540` via `HasTPrivateScheme.hasScheme`, whereas full-coalition
    `6`-privacy cannot achieve `540` bits.
-/

namespace CslibFrontierTests.Crypto.PIRTPrivate

open Cslib Cslib.Crypto.Protocols.PIR Cslib.Crypto.Protocols.SecretSharing Probability

/-! ### `1`-privacy, `t`-tuples, and `twoServer` collusion break -/

example : (twoServer (Fin 3)).IsTPrivate 0 ∧ (twoServer (Fin 3)).IsTPrivate 1 :=
  ⟨(twoServer (Fin 3)).isTPrivate_zero, Scheme.isTPrivate_one_iff.mpr isPrivate_twoServer⟩

/-- Even though `twoServer (Fin 2)` communicates `6 > 2` bits (so the full-coalition communication
bound does not rule out `2`-privacy), the two servers XOR their queries to learn the target index,
so `twoServer (Fin 2)` is not `2`-private. -/
example : ¬ (twoServer (Fin 2)).IsTPrivate 2 := by
  rw [Scheme.isTPrivate_iff_tuple]
  intro htuple
  have heq := congrArg
    (PMF.map (fun (qs : Fin 2 → Fin 2 → Bool) => (qs 0 + qs 1) 0))
    (htuple ![false, true] 0 1)
  have hlaw (idx : Fin 2) :
      (ProbComp.eval ((twoServer (Fin 2)).tupleQuery ![false, true] idx)).map
          (fun (qs : Fin 2 → Fin 2 → Bool) => (qs 0 + qs 1) 0) =
        PMF.pure (decide (0 = idx)) := by
    rw [Scheme.eval_tupleQuery, PMF.map_comp]
    refine (Cslib.Probability.PMF.map_congr_on_support _ _
      (Function.const _ (decide (0 = idx))) ?_).trans (PMF.map_const _ _)
    intro ⟨r, q⟩ hrq
    change (q false + q true) 0 = decide (0 = idx)
    rw [query_add_query_twoServer hrq]
    fin_cases idx <;> decide
  rw [hlaw 0, hlaw 1] at heq
  have hsupp := congrArg PMF.support heq
  rw [PMF.support_pure, PMF.support_pure, Set.singleton_eq_singleton_iff] at hsupp
  exact absurd hsupp (by decide)

/-! ### Full-coalition lower bounds (`t ≥ k`) -/

example (P : Scheme (Fin 1) Empty Unit Unit Bool) : ¬ P.IsCorrect :=
  Scheme.not_isCorrect_of_isEmpty

example : ¬ HasTPrivateScheme (Fin 4) 3 3 3 := fun h => by
  have hle := h.card_le_of_le le_rfl
  rw [Fintype.card_fin] at hle
  omega

/-! ### Linear Shamir `t`-private PIR (`ZMod 5`) -/

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def params2_3 : Shamir.Params (ZMod 5) (Fin 3) :=
  zmodShamirParams (t := 2) (k := 3) (p := 5) (by decide) (by decide)

private def params1_3 : Shamir.Params (ZMod 5) (Fin 3) :=
  zmodShamirParams (t := 1) (k := 3) (p := 5) (by decide) (by decide)

example : (shamir (Fin 4) params2_3).IsCorrect ∧ (shamir (Fin 4) params2_3).IsTPrivate 2 :=
  ⟨isCorrect_shamir params2_3, isTPrivate_shamir params2_3⟩

example (i : Fin 4) :
    ProbComp.eval ((shamir (Fin 4) params2_3).coalitionQuery ({0, 1} : Finset (Fin 3)) i) =
      PMF.uniformOfFintype (({0, 1} : Finset (Fin 3)) → Fin 4 → ZMod 5) :=
  eval_coalitionQuery_shamir params2_3 {0, 1} (by decide) i

example : ¬ (shamir (Fin 2) params2_3).IsTPrivate 3 :=
  not_isTPrivate_succ_shamir params2_3

/-- Threshold `t = 1` with `k = 3` servers is `1`-private (`params1_3`) but NOT `2`-private, even
though `2 < 3` servers is strictly smaller than the full server set. -/
example : (shamir (Fin 2) params1_3).IsTPrivate 1 ∧ ¬ (shamir (Fin 2) params1_3).IsTPrivate 2 :=
  ⟨isTPrivate_shamir params1_3, not_isTPrivate_succ_shamir params1_3⟩

/-- Matrix-balanced `2`-private `3`-server PIR on `16` bits over `ZMod 5`:
`3 * (2 * 4 * ⌈log₂ 5⌉) = 3 * 24 = 72` bits (using `threshold_zmodShamirParams`). -/
example : HasTPrivateScheme (Fin 16) 2 3 72 := by
  have h := hasTPrivateScheme_of_le_mul_self params2_3 (n := 16) (m := 4) (by decide)
  have hclog : Nat.clog 2 5 = 3 := by decide
  simpa [params2_3, ZMod.card, hclog] using h

/-! ### Unbalanced and `rows`-balanced degree-`d` polynomial PIR (`shamirCube`) -/

example :
    (shamirCube (Fin 2) (Fin 3) params1_3).IsCorrect ∧
      (shamirCube (Fin 2) (Fin 3) params1_3).IsTPrivate 1 ∧
      ¬ (shamirCube (Fin 2) (Fin 3) params1_3).IsTPrivate 2 :=
  ⟨isCorrect_shamirCube params1_3 (by decide),
    isTPrivate_shamirCube params1_3,
    not_isTPrivate_succ_shamirCube params1_3⟩

/-- Unbalanced `d = 2, t = 2, k = 5` over `ZMod 7`:
`5 * ((2 * 4 + 1) * ⌈log₂ 7⌉) = 5 * 27 = 135` bits. -/
example : HasTPrivateScheme (Fin 16) 2 5 135 := by
  have h := hasTPrivateScheme_prime_of_le_pow
    (n := 16) (d := 2) (ℓ := 4) (t := 2) (k := 5) (p := 7)
    (by decide) (by decide) (by decide) (by decide)
  have hclog : Nat.clog 2 7 = 3 := by decide
  simpa [hclog] using h

/-- Balanced `c = 3` (`d = 2`), `t = 2`, **exact `k = c * t = 6` servers** over `ZMod 7` on a
`1000`-bit database (`10 ^ 3`): `6 * (3 * 10 * ⌈log₂ 7⌉) = 6 * 90 = 540 < 1000` bits, instantiating
CGKS §§1.1 & 3.4's exact `c · t`-server bound, downgrading via `HasTPrivateScheme.hasScheme`,
and contrasting with the `1000`-bit full-coalition lower bound at `t = 6`. -/
example :
    HasTPrivateScheme (Fin 1000) 2 6 540 ∧
      HasScheme (Fin 1000) 6 540 ∧
      ¬ HasTPrivateScheme (Fin 1000) 6 6 540 := by
  have h6 : HasTPrivateScheme (Fin 1000) 2 6 540 := by
    have h := hasTPrivateScheme_prime_rows_of_le_pow
      (n := 1000) (d := 2) (ℓ := 10) (t := 2) (k := 6) (p := 7)
      (by decide) (by decide) (by decide) (by decide)
    have hclog : Nat.clog 2 7 = 3 := by decide
    simpa [hclog] using h
  refine ⟨h6, h6.hasScheme (by decide), fun hfull => ?_⟩
  have hle := hfull.card_le_of_le le_rfl
  rw [Fintype.card_fin] at hle
  omega

end CslibFrontierTests.Crypto.PIRTPrivate
