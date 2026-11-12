/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.DenseRestriction
import Mathlib.Tactic

/-! The diagonal walk and Lemma 6.7 of submission 865 on small instances. -/

namespace CslibFrontierTests.CommunicationDenseRestriction
open Cslib Cslib.Communication

/-- Rejecting is valid exactly when the row values agree. -/
example (g : BitString 1 → Bool) (A : Fin 2 → BitString 1) : composeKW g A A none :=
  fun _ => rfl

/-- A differing cell is a valid answer. -/
example (g : BitString 1 → Bool) :
    composeKW (m := 1) g (fun _ _ => true) (fun _ _ => false) (some (0, 0)) := by
  simp [composeKW]

/-- Lemma 6.7 at `m = 1`: a lower bound `d > 0` on every nonempty square is a lower bound on
`U_1 ⋄ KW_g`. -/
example (g : BitString 2 → Bool) (d : ℕ) (hd : 0 < d)
    (h : ∀ X : Finset (Fin 1 → BitString 2), 2 ^ (1 * 2) ≤ 2 ^ (1 - 1) * X.card →
      (d : ℕ∞) ≤ Protocol.ecomplexity (composeKW g) (X : Set (Fin 1 → BitString 2))
        (X : Set (Fin 1 → BitString 2))) :
    ((1 - 1 + d : ℕ) : ℕ∞) ≤ Protocol.ecomplexity (composeKW (m := 1) g) Set.univ Set.univ :=
  le_ecomplexity_composeKW hd h

/-- The diagonal walk keeps at least a quarter of `Fin 8` after two steps of any protocol. -/
example (p : Protocol (Fin 8) (Fin 8) Bool) :
    ∃ X : Finset (Fin 8), 2 ≤ X.card ∧ ∃ q : Protocol (Fin 8) (Fin 8) Bool,
      (∀ x ∈ X, ∀ y ∈ X, q.run x y = p.run x y) ∧ (q.depth = 0 ∨ q.depth + 2 ≤ p.depth) := by
  obtain ⟨X, -, hX, q, hq, hd⟩ := Protocol.exists_diagonal_subprotocol 2 p Finset.univ
  exact ⟨X, by simp at hX; omega, q, hq, hd⟩

end CslibFrontierTests.CommunicationDenseRestriction
