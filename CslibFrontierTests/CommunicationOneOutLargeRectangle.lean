/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Communication.OneOutLargeRectangle
import CslibFrontier.Computability.Communication.Announce
import Cslib.Probability.PMF
import Mathlib.Tactic

/-! Lemma 5.2 of submission 865 on actual one-out protocols: equality on two distinct bits
(a heavy-atom instance) and a light-atom instance with uniform inputs on `Fin 4`. -/

namespace CslibFrontierTests.CommunicationOneOutLargeRectangle
open Cslib.Communication Protocol OneOut
open Cslib.Probability

/-- A protocol computing equality, with both players sending one bit. -/
def eqProtocol : Protocol Bool Bool Bool :=
  .alice id
    (.bob id (.output true) (.output false))
    (.bob id (.output false) (.output true))

/-- Equality of bits as a total relation. -/
def eqRel (a b : Bool) (z : Bool) : Prop := z = decide (a = b)

private theorem eqProtocol_solves : eqProtocol.Solves eqRel Set.univ Set.univ := by
  intro a _ b _
  cases a <;> cases b <;> rfl

/-- Lemma 5.2 for the two-instance problem on distinct bits: uniform inputs have mass `1/2`, so
some rectangle solved in two bits has total mass at least `1 + 1/4`. -/
example : ∃ (A' : Set Bool) (B' : Set Bool) (q : Protocol Bool Bool Bool),
    q.depth ≤ 2 ∧ q.Solves eqRel A' B' ∧
      (5 / 4 : ℝ) ≤ ((PMF.uniformOfFintype Bool).toOuterMeasure A').toReal +
        ((PMF.uniformOfFintype Bool).toOuterMeasure B').toReal := by
  obtain ⟨A', B', q, hq, hs, hm⟩ := exists_large_solvable_rectangle
    (PMF.uniformOfFintype Bool) (PMF.uniformOfFintype Bool)
    (atCoordinate eqProtocol (0 : Fin 2)) (R := eqRel) (fun a b => ⟨_, rfl⟩)
    (solves_atCoordinate eqProtocol_solves 0)
  have hk : (1 : ℝ) + (((2 : ℕ) : ℝ) ^ 2)⁻¹ = 5 / 4 := by norm_num
  refine ⟨A', B', q, ?_, hs, hk ▸ hm⟩
  have h1 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 one_lt_two
  simpa [eqProtocol, Protocol.depth, h1] using hq

/-- The light-atom case of Lemma 5.2 with uniform inputs on `Fin 4`, at the boundary mass
`1/4 = 1/k²` for `k = 2`: some coordinate and background give a forcing rectangle of total
mass at least `1 + 1/4`. -/
example : ∃ q : Protocol (Fin 4) (Fin 4) (Fin 4),
    ∃ (i : Fin 2) (background : Set (Fin (atCoordinate q (0 : Fin 2)).leafCount)),
      (5 / 4 : ℝ) ≤
        ((PMF.uniformOfFintype (Fin 4)).toOuterMeasure (aliceSide (atCoordinate q (0 : Fin 2)) i
          background)).toReal +
        ((PMF.uniformOfFintype (Fin 4)).toOuterMeasure (bobSide (atCoordinate q (0 : Fin 2)) i
          background)).toReal := by
  -- Any single-instance protocol gives a one-out protocol; here Alice announces her input.
  obtain ⟨q, -, -⟩ := exists_run_eq_left (X := Fin 4) (Y := Fin 4) (id : Fin 4 → Fin 4)
  have hmass (a : Fin 4) :
      ((PMF.uniformOfFintype (Fin 4)) a).toReal ≤ (((2 : ℕ) : ℝ) ^ 2)⁻¹ := by
    norm_num [PMF.uniformOfFintype_apply]
  obtain ⟨i, background, h⟩ := exists_large_forcing_rectangle
    (PMF.uniformOfFintype (Fin 4)) (PMF.uniformOfFintype (Fin 4))
    (atCoordinate q (0 : Fin 2)) (by omega) hmass hmass
  have hk : (1 : ℝ) + (((2 : ℕ) : ℝ) ^ 2)⁻¹ = 5 / 4 := by norm_num
  exact ⟨q, i, background, hk ▸ h⟩

end CslibFrontierTests.CommunicationOneOutLargeRectangle
