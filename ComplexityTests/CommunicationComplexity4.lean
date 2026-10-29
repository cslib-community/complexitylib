/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Equality
import Complexity.Computability.Communication.Inclusion
import Complexity.Computability.Communication.InnerProductRank

/-!
Regression clients for exchanging the players and relabelling outputs, the trivial upper bounds,
equality on finite sets, intersection and inclusion, the rank bounds for relabelled outputs and
sign matrices, character orthogonality for the inner product, and the rank of the inner-product
matrix, which is a Hadamard matrix.
-/

open Cslib Cslib.Communication Finset

namespace CommunicationComplexity4Tests

/-! ### Exchanging the players and relabelling outputs -/

/-- Alice sends her bit; on `true`, Bob sends his. -/
private def small : Protocol Bool Bool (Fin 3) :=
  .alice id (.output 0) (.bob id (.output 1) (.output 2))

example : small.swapPlayers = .bob id (.output 0) (.alice id (.output 1) (.output 2)) := rfl
example : small.swapPlayers.run true false = small.run false true := rfl
example : (small.map Fin.val).run true true = 2 := rfl
example : (small.map Fin.val).leafCount = 3 := rfl

/-! ### Trivial upper bounds -/

-- Even when Alice's input is infinite (`ℕ`), exchanging the players and encoding Bob's
-- five-element input in `⌈log₂ 5⌉ = 3` bits gives a protocol sending at most `4` bits.
example (f : ℕ → Fin 5 → Bool) : Protocol.ecomplexityFun f ≤ 4 := by
  rw [← Protocol.ecomplexityFun_swap]
  have h := Protocol.ecomplexityFun_le_clog_card_succ (fun y x => f x y)
  rw [Fintype.card_fin, show Nat.clog 2 5 = 3 by decide] at h
  exact_mod_cast h

/-! ### Equality on finite sets -/

-- Equality on a five-element set costs exactly four bits: the fooling-set bound only gives three.
example : Protocol.ecomplexityFun (equality : Fin 5 → Fin 5 → Bool) = 4 := by
  rw [ecomplexityFun_equality (by decide), Fintype.card_fin, show Nat.clog 2 5 = 3 by decide]
  rfl

-- On bit strings, `⌈log₂ 2 ^ n⌉ + 1 = n + 1` recovers the bound for `n`-bit strings.
example {n : ℕ} (hn : 0 < n) :
    Protocol.ecomplexityFun (fun x y : BitString n => !equality x y) = n + 1 := by
  rw [ecomplexityFun_not_equality (by rw [BitString.card]; exact Nat.one_lt_two_pow hn.ne'),
    BitString.card, Nat.clog_pow _ _ one_lt_two]

example (p : Protocol (Fin 3) (Fin 3) Bool) (hp : p.run = equality) : 5 ≤ p.leafCount := by
  simpa using card_add_two_le_leafCount_of_run_eq_equality (by decide) hp

/-! ### Intersection and inclusion -/

-- Set intersection and pointwise inclusion on 4-bit strings both cost 5 bits, so they have the
-- same communication complexity.
example :
    Protocol.ecomplexityFun (fun x y : BitString 4 => !disjointness x y) =
      Protocol.ecomplexityFun (fun x y : BitString 4 => decide (x ≤ y)) :=
  (ecomplexityFun_not_disjointness (by decide)).trans (ecomplexityFun_decide_le (by decide)).symm

-- Inclusion of subsets of a three-element set: the diagonal fooling set has `8` pairs.
example (p : Protocol (Finset (Fin 3)) (Finset (Fin 3)) Bool)
    (hp : p.run = fun x y => decide (x ≤ y)) : 8 < 2 ^ p.depth := by
  have h := (isFoolingSet_le (univ : Finset (Finset (Fin 3)))).card_lt_two_pow hp
    ⟨univ, ∅, by decide⟩
  rwa [card_image_of_injective _ fun x y h => congrArg Prod.fst h] at h

/-! ### Rank bounds -/

-- Relabelling the outputs of `small` in `ℚ` yields a matrix of rank at most `2 ^ small.depth = 4`.
example : small.depth = 2 ∧ (Matrix.of fun x y => ((small.run x y : ℕ) : ℚ)).rank ≤ 4 :=
  ⟨rfl, small.rank_comp_le_two_pow rfl fun z => ((z : ℕ) : ℚ)⟩

-- The `8 × 8` sign matrix of the 3-bit inner product has full rank `8`, so by the sign-matrix
-- rank bound any protocol computing it satisfies `8 ≤ 2 ^ p.depth`.
example (p : Protocol (Fin 3 → Bool) (Fin 3 → Bool) Bool) (hp : p.run = fun x y => x ⬝ᵥ y) :
    8 ≤ 2 ^ p.depth := by
  have h := p.rank_signMatrix_le_two_pow (R := ℝ) hp
  rwa [rank_signMatrix_dotProduct, Fintype.card_fin] at h

-- For the 2-bit inner product, the `4 × 4` sign matrix has full rank `4` over `ℚ`, one more than
-- the rank `3` of its `0/1` communication matrix.
example :
    (communicationMatrix ℚ fun x y : Fin 2 → Bool => x ⬝ᵥ y).rank + 1 =
      (signMatrix ℚ fun x y : Fin 2 → Bool => x ⬝ᵥ y).rank := by
  rw [rank_communicationMatrix_dotProduct, rank_signMatrix_dotProduct, Fintype.card_fin]
  rfl

-- Because the sign matrix `H` of the 3-bit inner product satisfies `H * H = 8 • 1`, scaling `H`
-- by `1 / 8` over `ℚ` gives its right inverse.
example :
    signMatrix ℚ (fun x y : Fin 3 → Bool => x ⬝ᵥ y) *
      ((1 / 8 : ℚ) • signMatrix ℚ (fun x y : Fin 3 → Bool => x ⬝ᵥ y)) = 1 := by
  rw [Matrix.mul_smul, signMatrix_dotProduct_mul_self, Fintype.card_fin, smul_smul]
  norm_num

-- Character orthogonality holds over any ring, here one that is not a domain.
example (w : Fin 3 → Bool) (hw : w ≠ 0) :
    ∑ y : Fin 3 → Bool, (if w ⬝ᵥ y then (-1 : ZMod 4) else 1) = 0 := by
  rw [BitString.sum_ite_dotProduct, ite_eq_right_iff]
  exact fun h => absurd h hw

end CommunicationComplexity4Tests
