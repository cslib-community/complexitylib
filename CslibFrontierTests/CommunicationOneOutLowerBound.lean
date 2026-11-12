/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.OneOutLowerBound
import Mathlib.Tactic

/-! Theorems 1.1 and 1.2 of submission 865 on equality of bits, and the amplification step. -/

namespace CslibFrontierTests.CommunicationOneOutLowerBound
open Cslib.Communication Protocol OneOut Cslib.Probability

/-- Equality of bits as a total relation. -/
def eqRel (a b : Bool) (z : Bool) : Prop := z = decide (a = b)

/-- A protocol computing equality, with both players sending one bit. -/
def eqProtocol : Protocol Bool Bool Bool :=
  .alice id
    (.bob id (.output true) (.output false))
    (.bob id (.output false) (.output true))

private theorem eqProtocol_solves : eqProtocol.Solves eqRel Set.univ Set.univ := by
  intro a _ b _
  cases a <;> cases b <;> rfl

/-- The amplified protocol built from the two-instance protocol solves equality on all inputs. -/
example : ∃ q : Protocol Bool Bool Bool, q.Solves eqRel Set.univ Set.univ ∧
    q.depth ≤ max 2 (Nat.clog 2 2) + 3 * levels 2 4 := by
  obtain ⟨q, hq, hd⟩ := exists_solves_depth_le (R := eqRel) (fun a b => ⟨_, rfl⟩)
    (solves_atCoordinate eqProtocol_solves (0 : Fin 2))
  exact ⟨q, hq, by simpa [eqProtocol, Protocol.depth] using hd⟩

/-- Theorem 1.1's lower bound at `k = 2`, `n = 1`: choosing one of two distinct instances of
equality saves at most `28` bits. -/
example : ecomplexityFun (fun a b : Bool => decide (a = b)) ≤
    ecomplexity (Relation (k := 2) fun (a b : Bool) z => decide (a = b) = z) Set.univ Set.univ +
      ((18 * Nat.clog 2 2 + 3 * Nat.clog 2 (1 + 1) + 7 : ℕ) : ℕ∞) :=
  ecomplexityFun_le_oneOut _ (by simp) (by simp)

/-- One majority level fixes `1/2` and pushes `3/4` up to `27/32`. -/
example : MajorityTree.amplify (1 / 2) = 1 / 2 ∧ MajorityTree.amplify (3 / 4) = 27 / 32 := by
  norm_num [MajorityTree.amplify]

end CslibFrontierTests.CommunicationOneOutLowerBound
