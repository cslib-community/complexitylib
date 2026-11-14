/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Crypto.Computational.LWE.Trapdoor

/-!
Regression clients for the Micciancio–Peikert (2012) gadget trapdoor construction
(`Cslib.Crypto.LWE.Trapdoor`): concrete gadget decomposition, short kernel basis `S_w`,
iterative `g_G`-inversion (including a threshold failure at `2 ^ w / 4`), tagged parity-check
matrices with non-identity invertible tags, syndrome lifting (`f_A⁻¹`), full trapdoor LWE
inversion (`g_A⁻¹`, Algorithm 2 / Theorem 5.4), and `GenTrap` / `genTrapIdeal` laws.
-/

namespace CslibFrontierTests.Crypto.Computational.LWE.Trapdoor

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.LWE.Trapdoor
open scoped BigOperators _root_.Matrix

/-! ### 1. Primitive Gadget Matrix, Short Kernel Basis `S_w`, and `g_G`-Inversion -/

private def toySyndrome2 : Fin 2 → ZMod (2 ^ 4) := ![11, 6]
private def toyScalarError : Fin 4 → ℤ := ![1, -2, 3, -1]

-- Concrete checks for `gadgetDecomp`, `scalarBasis`, and `invertScalar` at width `w = 4`:
-- (1) `gadgetDecomp` reconstructs `![11, 6]` under `gadgetMatrix 4`;
-- (2) `scalarBasis 4` has determinant `16 = 2 ^ 4` and annihilates `gadgetVector 4`;
-- (3) `invertScalar 4` recovers `s = 13` from `s • g + e` with signed error `![1, -2, 3, -1]`
--     (`4 * 3 = 12 < 16`).
example :
    gadgetMatrix 4 *ᵥ (Int.cast ∘ gadgetDecomp 4 toySyndrome2) = toySyndrome2 ∧
      (scalarBasis 4).det = 16 ∧
      gadgetVector 4 ᵥ* (scalarBasis 4).map (Int.cast : ℤ → ZMod (2 ^ 4)) = 0 ∧
      invertScalar 4 ((13 : ZMod (2 ^ 4)) • gadgetVector 4 + (Int.cast ∘ toyScalarError)) =
        (13 : ZMod (2 ^ 4)) := by
  decide +kernel

-- Without the quarter-modulus margin `4 * |e_j| < 2 ^ w`, `invertScalar` can fail:
-- an error of `+4` in the `j = 0` coordinate crosses the quarter-modulus boundary and flips the
-- recovered MSB (`2 ^ 3 = 8`).
example :
    invertScalar 4
        ((0 : ZMod (2 ^ 4)) • gadgetVector 4 + (Int.cast ∘ (![4, 0, 0, 0] : Fin 4 → ℤ))) =
      (8 : ZMod (2 ^ 4)) := by
  decide +kernel

-- Every column of `gadgetBasis w` lies in `Λ^⊥(G)` and has squared Euclidean norm at most `5`.
example (w : ℕ) (q : Fin 2 × Fin w) :
    InKernelLattice (gadgetMatrix (ι := Fin 2) w) (fun p => gadgetBasis w p q) ∧
      ∑ p : Fin 2 × Fin w, (gadgetBasis w p q) ^ 2 ≤ 5 :=
  ⟨gadgetBasis_col_inKernelLattice w q, sum_sq_gadgetBasis_col_le_five w q⟩

/-! ### 2. Tagged Parity-Check Matrices, Syndrome Lifting (`f_A⁻¹`), and Kernel Basis `[R; I] S` -/

private def toyAbar : _root_.Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 4)) := !![3, 9; 12, 5]

private def toyR : _root_.Matrix (Fin 2) (Fin 2 × Fin 4) ℤ := fun j p =>
  if j.val = p.1.val ∧ p.2.val < 2 then 1
  else if p.2.val = 3 then -1
  else 0

private def toyH : _root_.Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 4)) := !![1, 2; 0, 1]
private def toyHinv : _root_.Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 4)) := !![1, 14; 0, 1]

private theorem toyH_mul_toyHinv : toyH * toyHinv = 1 := by
  decide +kernel

-- Concrete check of `taggedMatrix_mulVec_invertSyndrome` and `extendedGadgetBasis` with the
-- non-identity upper-triangular invertible tag `toyH`.
example (u : Fin 2 → ZMod (2 ^ 4)) :
    taggedMatrix 4 toyAbar toyR toyH *ᵥ (Int.cast ∘ invertSyndrome 4 toyHinv toyR u) = u ∧
      taggedMatrix 4 toyAbar toyR toyH *
        (extendedGadgetBasis 4 toyR).map (Int.cast : ℤ → ZMod (2 ^ 4)) = 0 ∧
      (∀ j : Fin 2, (invertSyndrome 4 toyHinv toyR u (Sum.inl j)).natAbs ≤ 8) ∧
      (∀ p : Fin 2 × Fin 4, (invertSyndrome 4 toyHinv toyR u (Sum.inr p)).natAbs ≤ 1) :=
  ⟨taggedMatrix_mulVec_invertSyndrome 4 toyAbar toyR toyH_mul_toyHinv u,
    taggedMatrix_mul_extendedGadgetBasis 4 toyAbar toyR toyH,
    fun j => by
      simpa using natAbs_invertSyndrome_inl_le 4 toyHinv toyR u j 1
        (fun p => by revert j p; decide +kernel),
    fun p => natAbs_invertSyndrome_inr_le 4 toyHinv toyR u p⟩

/-! ### 3. Trapdoor LWE Inversion (`Algorithm 2`, `Theorem 5.4`) and `GenTrap` Support -/

private def toySecret : Fin 2 → ZMod (2 ^ 4) := ![7, 13]

private def toyLWEError : Fin 2 ⊕ (Fin 2 × Fin 4) → ℤ
  | Sum.inl 0 => 1
  | Sum.inl 1 => -1
  | Sum.inr (_, 0) => 1
  | Sum.inr (_, _) => 0

-- Concrete end-to-end execution of Algorithm 2 (`invertLWE`): recovers both `toySecret = ![7, 13]`
-- and the signed error vector `toyLWEError` in the presence of a non-identity tag `toyH`.
example :
    invertLWE 4 toyAbar toyR toyH toyHinv
        (trapdoorLWE 4 (taggedMatrix 4 toyAbar toyR toyH) toySecret toyLWEError) =
      (toySecret, toyLWEError) := by
  refine invertLWE_trapdoorLWE_of_norm_bound 4 toyAbar toyR toyH_mul_toyHinv toySecret toyLWEError
    (B_R := 1) (B_e := 1)
    (fun j p => by revert j p; decide +kernel)
    (fun k => by revert k; decide +kernel)
    (by decide)

-- End-to-end correctness of `genTrap` followed by `invertLWE` for any key pair `(A, R)` in the
-- support of `genTrap n mbar w η H` whenever `4 * (1 + mbar * η) * B_e < 2 ^ w`.
example {n mbar w η B_e : ℕ}
    {H Hinv : _root_.Matrix (Fin n) (Fin n) (ZMod (2 ^ w))} (hH : H * Hinv = 1)
    (hHinv : Hinv * H = 1)
    {out : _root_.Matrix (Fin n) (Fin mbar ⊕ (Fin n × Fin w)) (ZMod (2 ^ w)) ×
      _root_.Matrix (Fin mbar) (Fin n × Fin w) ℤ}
    (hout : out ∈ (ProbComp.eval (genTrap n mbar w η H)).support)
    (s : Fin n → ZMod (2 ^ w))
    (e : Fin mbar ⊕ (Fin n × Fin w) → ℤ)
    (he : ∀ k, (e k).natAbs ≤ B_e)
    (hbound : 4 * (1 + mbar * η) * B_e < 2 ^ w) :
    IsHTagTrapdoor w out.1 out.2 H ∧
      Function.Surjective
        (fun x : Fin mbar ⊕ (Fin n × Fin w) → ℤ => out.1 *ᵥ (Int.cast ∘ x)) ∧
      ∃ Abar : _root_.Matrix (Fin n) (Fin mbar) (ZMod (2 ^ w)),
        out.1 = taggedMatrix w Abar out.2 H ∧
          invertLWE w Abar out.2 H Hinv (trapdoorLWE w out.1 s e) = (s, e) := by
  have hHunit : IsUnit H := ⟨⟨H, Hinv, hH, hHinv⟩, rfl⟩
  rcases mem_support_genTrap n mbar w η hHunit hout with ⟨htrap, hR, Abar, hA⟩
  refine ⟨htrap, htrap.surjective, Abar, hA, ?_⟩
  rw [hA]
  exact invertLWE_trapdoorLWE_of_norm_bound w Abar out.2 hH s e hR he
    (by simpa [Fintype.card_fin] using hbound)

-- Tag-independence of the idealized hybrid `genTrapIdeal`: the public matrix distribution under
-- `toyH` is identical to the one under the zero tag `H = 0` and equals
-- the uniform distribution.
example :
    ProbComp.eval (genTrapIdeal 2 2 4 toyH) = ProbComp.eval (genTrapIdeal 2 2 4 0) ∧
      ProbComp.eval (genTrapIdeal 2 2 4 toyH) =
        PMF.uniformOfFintype
          (_root_.Matrix (Fin 2) (Fin 2 ⊕ (Fin 2 × Fin 4)) (ZMod (2 ^ 4))) :=
  ⟨eval_genTrapIdeal_eq_of_tags 2 2 4 toyH 0, eval_genTrapIdeal_eq_uniform 2 2 4 toyH⟩

/-! ### 4. Axiom Hygiene Guards for Choice-Free Results -/

/--
info: 'Cslib.Crypto.LWE.Trapdoor.natAbs_scalarBasis_le_two' does not depend on any axioms
-/
#guard_msgs in
#print axioms Cslib.Crypto.LWE.Trapdoor.natAbs_scalarBasis_le_two

/--
info: 'Cslib.Crypto.LWE.Trapdoor.natAbs_gadgetBasis_le_two' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.Crypto.LWE.Trapdoor.natAbs_gadgetBasis_le_two

/--
info: 'Cslib.Crypto.LWE.Trapdoor.natAbs_gadgetDecomp_le_one' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Cslib.Crypto.LWE.Trapdoor.natAbs_gadgetDecomp_le_one

end CslibFrontierTests.Crypto.Computational.LWE.Trapdoor
