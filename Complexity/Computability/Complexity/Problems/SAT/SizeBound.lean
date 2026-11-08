/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.SAT
public import Complexity.Logics.Propositional.CNF.ModelCount.Declared
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Encoding size of declared bounded-width CNF inputs

For valid declared inputs, full unary-header/binary-index encoding length is polynomial in the
number of variables plus clauses. This transfers bit-resource certificates to the source
parameterization without assuming an input-size estimate.

## Main results

* `Cslib.Complexity.SAT.length_declaredInput_le`: a quadratic bound with width-dependent constant.
-/

public section

namespace Cslib.Complexity.SAT

open Cslib.Logic.PL Cslib.Logic.PL.CNF Turing.MultiTapeTM

/-- Framed encoding size, including declaration, clauses, signs and every binary index. -/
theorem length_declaredInput_le {k n : ℕ} {φ : CNF ℕ}
    (hv : validDeclaredInput k n φ = true) :
    (encPair encUnary encCNF (n, φ)).length + 1 ≤ (20 * k + 4) * (n + φ.length + 1) ^ 2 := by
  obtain ⟨hw, hvars⟩ := validDeclaredInput_eq_true_iff.mp hv
  let B := n + φ.length + 1
  have hB : 1 ≤ B := by dsimp only [B]; omega
  have hnB : n + 1 ≤ B := by dsimp only [B]; omega
  have hmB : φ.length ≤ B := by dsimp only [B]; omega
  have hclause : ∀ c ∈ φ, (encList (encPair encNat encBool) c).length ≤ 9 * k * B := by
    intro c hc
    have hlit : ∀ l ∈ c, (encPair encNat encBool l).length ≤ 4 * B := by
      intro l hl
      have hln : l.1 < n := Finset.mem_range.mp (hvars
        (List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩)))
      have hbits := length_encNat_le_log2 hln.le
      have hbits' : (encNat l.1).length ≤ n + 1 :=
        hbits.trans (Nat.add_le_add_right (Nat.log2_le_self n) 1)
      simp only [length_encPair, encBool_apply, List.length_singleton]
      omega
    exact (length_encList_le (encPair encNat encBool) c hlit).trans
      ((Nat.mul_le_mul (hw c hc) (by omega : 2 * (4 * B) + 1 ≤ 9 * B)).trans_eq (by ring))
  have hcnf : (encCNF φ).length ≤ (18 * k + 1) * B ^ 2 := by
    calc _ ≤ φ.length * (2 * (9 * k * B) + 1) := length_encList_le _ φ hclause
      _ ≤ B * ((18 * k + 1) * B) := Nat.mul_le_mul hmB (by nlinarith)
      _ = _ := by ring
  have hprefix : 2 * n + 2 ≤ 2 * B ^ 2 := by
    have hb2 : B ≤ B ^ 2 := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) B
    omega
  have hpair : (encPair encUnary encCNF (n, φ)).length + 1 = (2 * n + 2) + (encCNF φ).length := by
    simp only [length_encPair, encUnary_apply, List.length_replicate]
    omega
  rw [hpair]
  calc _ ≤ 2 * B ^ 2 + (18 * k + 1) * B ^ 2 := Nat.add_le_add hprefix hcnf
    _ = (18 * k + 3) * B ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega : 18 * k + 3 ≤ 20 * k + 4)

end Cslib.Complexity.SAT
