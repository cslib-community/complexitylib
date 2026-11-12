/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Languages.Probabilistic.IdealCipher
import CslibFrontier.Crypto.Primitives.Hash.BlockCipherCompression
import CslibFrontier.Crypto.Primitives.IdealCipher.Compression
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for the Ideal Cipher Model and Davies–Meyer Collision Resistance

Exercises `CslibFrontier/Languages/Probabilistic/IdealCipher.lean`,
`CslibFrontier/Crypto/Primitives/Hash/BlockCipherCompression.lean`, and
`CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean`:
* concrete evaluation of `cipherOutput` and `daviesMeyer`;
* the inverse-query collision break `cipherOutputAdversary_wins` on `cipherOutput`;
* concrete instantiation of `abs_sub_uniformPerm_forgetful_le` on a 2-query program using both
  forward and inverse ideal-cipher queries over `Key = Fin 2` and `Block = ZMod 16`;
* concrete nonvacuous instantiations of `daviesMeyer_collisionGame_le` and
  `daviesMeyer_collisionGame_mul_le` (Katz–Lindell Theorem 7.5) with explicit `< 1` bounds;
* `#guard_msgs` axiom checks for the headline definitions and security bounds.
-/

open Cslib Cslib.OracleComp Cslib.Crypto.BlockCipherCompression Cslib.Probability
  Cslib.IdealCipher Cslib.RandomPermutation

def E1 : Fin 2 → Equiv.Perm (ZMod 2) := fun _ => Equiv.refl _
def E2 : Fin 2 → Equiv.Perm (ZMod 2) := fun k => if k = 0 then Equiv.refl _ else Equiv.swap 0 1

example : cipherOutput E1 (1, 0) = 0 := rfl
example : cipherOutput E2 (1, 1) = 0 := rfl

example : daviesMeyer E1 (1, 0) = 0 := rfl
example : daviesMeyer E2 (1, 1) = 1 := rfl

noncomputable def test_collisionGame : PMF Bool :=
  collisionGame (cipherOutput (K := Fin 2) (B := ZMod 2))
    (cipherOutputAdversary (0 : Fin 2) (1 : Fin 2) 0)

example : test_collisionGame = PMF.pure true :=
  cipherOutputAdversary_wins (k1 := (0 : Fin 2)) (k2 := (1 : Fin 2)) (by decide) (0 : ZMod 2)

/-! ### Ideal-cipher switching bound (`abs_sub_uniformPerm_forgetful_le`) -/

noncomputable def twoQueryIdealCipherProg :
    OracleComp (Spec (Fin 2) (ZMod 16)) (ZMod 16 × ZMod 16) := do
  let y ← OracleComp.query ((0 : Fin 2), PermQuery.forward (0 : ZMod 16))
  let x ← OracleComp.query ((0 : Fin 2), PermQuery.inverse y)
  return (x, y)

theorem isQueryBounded_twoQueryIdealCipherProg :
    twoQueryIdealCipherProg.IsQueryBounded 2 :=
  IsCostBounded.bind (cost := fun _ => 1) (IsCostBounded.query _) fun _ =>
    IsCostBounded.bind (IsCostBounded.query _) fun _ =>
      IsCostBounded.pure _ 0

theorem twoQueryIdealCipherProg_diff_le :
    |(((do
        let P ← PMF.pi (fun _ : Fin 2 => PMF.uniformOfFintype (Equiv.Perm (ZMod 16)))
        OracleComp.interpret (fun (q : Query (Fin 2) (ZMod 16)) =>
          PMF.pure (evalPerm (P q.1) q.2)) twoQueryIdealCipherProg).bind
        (PMF.pure (α := ZMod 16 × ZMod 16))) (0, 0)).toReal -
      (((((OracleComp.interpret IdealCipher.forgetfulAnswer twoQueryIdealCipherProg).run
        (fun _ => [])).map Prod.fst).bind
        (PMF.pure (α := ZMod 16 × ZMod 16))) (0, 0)).toReal| ≤
      (1 : ℝ) / 16 := by
  have h := abs_sub_uniformPerm_forgetful_le isQueryBounded_twoQueryIdealCipherProg
    (PMF.pure (α := ZMod 16 × ZMod 16)) (0, 0)
  have hcard : Fintype.card (ZMod 16) = 16 := ZMod.card 16
  rw [hcard] at h
  norm_num at h ⊢
  exact h

/-! ### Nonvacuous Theorem 7.5 collision bounds on `daviesMeyer` -/

noncomputable def zeroQueryDMAdversary :
    OracleComp (Spec (Fin 2) (ZMod 16)) ((Fin 2 × ZMod 16) × (Fin 2 × ZMod 16)) :=
  return (((0 : Fin 2), (0 : ZMod 16)), ((1 : Fin 2), (1 : ZMod 16)))

theorem isQueryBounded_zeroQueryDMAdversary :
    zeroQueryDMAdversary.IsQueryBounded 0 :=
  IsCostBounded.pure _ 0

example :
    ((collisionGame (daviesMeyer (K := Fin 2) (B := ZMod 16))
      zeroQueryDMAdversary) true).toReal ≤ (1 : ℝ) / 8 := by
  have h := daviesMeyer_collisionGame_le isQueryBounded_zeroQueryDMAdversary
  have hcard : Fintype.card (ZMod 16) = 16 := ZMod.card 16
  rw [hcard] at h
  norm_num at h ⊢
  exact h

noncomputable def oneQueryDMAdversary :
    OracleComp (Spec (Fin 2) (ZMod 16)) ((Fin 2 × ZMod 16) × (Fin 2 × ZMod 16)) := do
  let y ← OracleComp.query ((0 : Fin 2), PermQuery.forward (0 : ZMod 16))
  return (((0 : Fin 2), (0 : ZMod 16)), ((1 : Fin 2), y))

theorem isQueryBounded_oneQueryDMAdversary :
    oneQueryDMAdversary.IsQueryBounded 1 :=
  IsCostBounded.bind (cost := fun _ => 1) (IsCostBounded.query _) fun _ => IsCostBounded.pure _ 0

example :
    ((collisionGame (daviesMeyer (K := Fin 2) (B := ZMod 16))
      oneQueryDMAdversary) true).toReal ≤ (3 : ℝ) / 8 := by
  have h := daviesMeyer_collisionGame_mul_le isQueryBounded_oneQueryDMAdversary
  have hcard : Fintype.card (ZMod 16) = 16 := ZMod.card 16
  rw [hcard] at h
  norm_num at h ⊢
  exact h

/-! ### Axiom guards for ideal-cipher and Davies–Meyer theorems -/

/--
info: 'Cslib.IdealCipher.abs_sub_uniformPerm_forgetful_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.IdealCipher.abs_sub_uniformPerm_forgetful_le

/--
info: 'Cslib.IdealCipher.cipherOutputAdversary_wins' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.IdealCipher.cipherOutputAdversary_wins

/--
info: 'Cslib.IdealCipher.collisionGame_daviesMeyer_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.IdealCipher.collisionGame_daviesMeyer_eq

/--
info: 'Cslib.IdealCipher.daviesMeyer_collisionGame_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.IdealCipher.daviesMeyer_collisionGame_le

/--
info: 'Cslib.IdealCipher.daviesMeyer_collisionGame_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Cslib.IdealCipher.daviesMeyer_collisionGame_mul_le
