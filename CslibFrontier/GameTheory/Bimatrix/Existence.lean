/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
import CslibFrontier.GameTheory.Bimatrix.CostGame

/-!
# Nash's theorem for bimatrix games

Every bimatrix game with nonempty strategy sets has a Nash equilibrium
(`Cslib.GameTheory.BimatrixGame.exists_isNash`), with no nondegeneracy assumption. This is the
two-player case of Nash's theorem ([Nash1951], Theorem 1).

The proof applies `Cslib.GameTheory.CostGame.exists_isMixedNash` to the cost game
`Cslib.GameTheory.BimatrixGame.toCostGame`, whose mixed Nash equilibria are the Nash equilibria of
the bimatrix game (`Cslib.GameTheory.BimatrixGame.isNash_iff_isMixedNash`).

For nondegenerate games, `Cslib.GameTheory.BimatrixGame.IsNondegenerate.odd_ncard_isNash` gives
the sharper parity statement of Lemke and Howson.

## Main results

* `Cslib.GameTheory.BimatrixGame.exists_isNash`: **Nash's theorem** for bimatrix games.

## References

* [J. Nash, *Non-Cooperative Games*][Nash1951]
-/

public section

namespace Cslib.GameTheory.BimatrixGame

universe u v

variable {M : Type u} {N : Type v} [Fintype M] [Fintype N]

/-- **Nash's theorem** for bimatrix games ([Nash1951], Theorem 1): every bimatrix game with
nonempty strategy sets has a Nash equilibrium. -/
theorem exists_isNash [Nonempty M] [Nonempty N] (G : BimatrixGame M N) :
    ∃ x y, G.IsNash x y := by
  obtain ⟨p, hp⟩ := G.toCostGame.exists_isMixedNash
  rw [eq_profile p] at hp
  exact ⟨_, _, isNash_iff_isMixedNash.2 hp⟩

end Cslib.GameTheory.BimatrixGame
