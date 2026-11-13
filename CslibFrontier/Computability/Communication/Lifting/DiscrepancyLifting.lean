/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Communication.Lifting.GeneralDiscrepancyLifting

/-!
# A concrete discrepancy lifting theorem

For an alphabet of size `B ^ 2048` and uniform gadget discrepancy at most `B ^ (-1024)`,
every deterministic communication protocol yields a correct decision tree with an explicit
query-depth bound. This is the `k = 1` specialization of the general parameter theorem;
the local density guarantees are proved from discrepancy, not assumed.
-/

public section

namespace Cslib.Communication.Lifting

open Probability

-- Avoid the exponent-warning path during dependency analysis of the alphabet type.
set_option exponentiation.threshold 2048 in
/-- A concrete polynomial-alphabet discrepancy lifting theorem for arbitrary output relations.
The conservative constants give `B ^ (31 * queryDepth) ≤ 8 ^ (2 * communicationDepth)`. -/
theorem exists_decisionTree_of_polynomial_discrepancy {n B : ℕ} [NeZero B] {O : Type*}
    (g : Fin (B ^ 2048) → Fin (B ^ 2048) → Bool)
    (hB : 2 ≤ B) (hn : 2 ≤ n) (hnB : n ≤ B)
    (hdisc : discrepancy (PMF.uniformOfFintype (Fin (B ^ 2048) × Fin (B ^ 2048))) g ≤
      ((B : ℝ) ^ 1024)⁻¹)
    (R : (Fin n → Bool) → O → Prop)
    (p : Protocol (Fin n → Fin (B ^ 2048)) (Fin n → Fin (B ^ 2048)) O)
    (hp : ∀ x y, R (fun i => g (x i) (y i)) (p.run x y)) :
    ∃ t : DecisionTree (Fin n) O, (∀ z, R z (t.eval z)) ∧
      (B : ℝ) ^ (31 * t.depth) ≤ 8 ^ (2 * p.depth) := by
  let : NeZero (B ^ 2048) := ⟨pow_ne_zero _ (NeZero.ne B)⟩
  exact exists_decisionTree_of_parameter_discrepancy g (k := 1) (B := (B : ℝ))
    (by decide) (by exact_mod_cast hB) hn (by exact_mod_cast hnB)
    (by simp only [one_pow, Nat.mul_one, Nat.cast_pow]) hdisc R p hp

end Cslib.Communication.Lifting
