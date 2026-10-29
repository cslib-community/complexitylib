/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Communication.Functions
import Complexity.Computability.Communication.Rank

/-!
Regression clients for deterministic communication complexity: leaf rectangles, fooling sets, the
rank bound, and the `n + 1` lower bounds for equality, greater-than, inner product and
disjointness.
-/

open Cslib Cslib.Communication

namespace CommunicationComplexityTests

/-! ### Leaf rectangles -/

/-- Alice sends her bit; on `true`, Bob sends his. -/
private def small : Protocol Bool Bool (Fin 3) :=
  .alice id (.output 0) (.bob id (.output 1) (.output 2))

example : small.leafCount = 3 := rfl
example : small.depth = 2 := rfl
example : (small.leaf false true).val = 0 := rfl
example : (small.leaf true false).val = 1 := rfl
example : (small.leaf true true).val = 2 := rfl

/-- The last leaf. -/
private def last : Fin small.leafCount := ⟨2, by decide⟩

example : small.leafOutput last = 2 := rfl

-- The rectangle of the last leaf is `{true} × {true}`.
example : true ∈ small.leafAlice last ∧ true ∈ small.leafBob last :=
  Protocol.leaf_eq_iff.mp (rfl : small.leaf true true = last)

example : false ∉ small.leafBob last := fun h =>
  absurd (Protocol.leaf_eq_iff.mpr ⟨(Protocol.leaf_eq_iff.mp
    (rfl : small.leaf true true = last)).1, h⟩) (by decide)

/-! ### The trivial protocol and the boundary `n = 0` -/

-- Without any bits, equality is constant and needs no communication: `0 < n` is needed.
example : Protocol.ecomplexity (fun (x y : BitString 0) b => equality x y = b) Set.univ
    Set.univ = 0 := by
  refine le_antisymm ?_ bot_le
  have := Protocol.ecomplexity_le_depth (p := (.output true : Protocol (BitString 0) _ _))
    (R := fun (x y : BitString 0) b => equality x y = b) (A := Set.univ) (B := Set.univ)
    (fun x _ y _ => by simp [equality, Subsingleton.elim x y])
  simpa using this

/-! ### Fooling sets -/

-- A pair off the diagonal cannot be added: `{(0, 0), (0, 1)}` is not a fooling set for equality.
example : ¬ IsFoolingSet (equality : Fin 2 → Fin 2 → Bool) true {(0, 0), (0, 1)} := by
  intro h
  have := h.1 (0, 1) (by simp)
  simp [equality] at this

-- By `isFoolingSet_disjointness`, a protocol computing disjointness on `BitString 3` has at least
-- `8` leaves labelled `true`, one for each complementary pair `(x, !x)`.
example (p : Protocol (BitString 3) (BitString 3) Bool) (hp : p.run = disjointness) :
    8 ≤ (Finset.univ.filter fun i => p.leafOutput i = true).card := by
  have h := (isFoolingSet_disjointness (Finset.univ : Finset (BitString 3))).card_le hp
  rwa [Finset.card_image_of_injective _ fun x y h => congrArg Prod.fst h,
    Finset.card_univ, BitString.card] at h

/-! ### The rank bound -/

-- The communication matrix of equality is the identity, so the rank bound gives `n` bits.
example (n : ℕ) : (n : ℕ∞) ≤
    Protocol.ecomplexity (fun (x y : BitString n) b => equality x y = b) Set.univ Set.univ := by
  have h := clog_rank_le_ecomplexity ℝ (equality : BitString n → BitString n → Bool)
  have hM : communicationMatrix ℝ (equality : BitString n → BitString n → Bool) = 1 := by
    ext x y
    simp [equality, Matrix.one_apply]
  rwa [hM, Matrix.rank_one, BitString.card, Nat.clog_pow _ _ one_lt_two] at h

/-! ### Named functions -/

-- Every protocol computing greater-than on 3-bit binary numerals sends at least 4 bits.
example (p : Protocol (BitString 3) (BitString 3) Bool)
    (hp : p.Solves
      (fun x y b => greaterThan (BitString.equivFin 3 x) (BitString.equivFin 3 y) = b)
      Set.univ Set.univ) :
    4 ≤ p.depth := by
  have h := Protocol.ecomplexity_le_depth hp
  rw [ecomplexity_greaterThan (by decide)] at h
  exact_mod_cast h

-- Any protocol computing the inner product on 3-bit strings has at least 9 leaves, hence depth at
-- least 4.
example (p : Protocol (BitString 3) (BitString 3) Bool) (hp : p.run = fun x y => x ⬝ᵥ y) :
    4 ≤ p.depth := by
  have h := (two_pow_lt_leafCount_of_run_eq_dotProduct hp).trans_le p.leafCount_le_two_pow_depth
  rw [Fintype.card_fin] at h
  exact (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp h

-- Equality on a five-element set needs three bits.
example (p : Protocol (Fin 5) (Fin 5) Bool) (hp : p.run = equality) : 3 ≤ p.depth := by
  have h := card_lt_two_pow_of_run_eq_equality (by decide) hp
  rw [Fintype.card_fin] at h
  by_contra hd
  have : 2 ^ p.depth ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end CommunicationComplexityTests
