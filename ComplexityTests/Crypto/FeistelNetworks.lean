/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Crypto.Protocols.Cipher.FeistelNetworks
import Mathlib.Data.ZMod.Basic

/-!
# Tests for block cipher networks and explicit Feistel distinguishers

Exercises substitution–permutation networks (SPNs), alternating unbalanced Feistel networks and
arbitrary-length bit-string splitting, degenerate round-function periodicity (zero and identity
rounds), and the concrete 1-round CPA, 2-round CPA, 3-round repeated-key CPA, and sharper 3-round
CCA Feistel distinguisher bounds in `Complexity.Crypto.Protocols.Cipher.FeistelNetworks`.
-/

namespace ComplexityTests.Crypto.FeistelNetworks

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.SPN Cslib.Crypto.LubyRackoff
open scoped ENNReal

-- Concrete 2-sub-block SPN evaluation, inversion, and bijectivity over `ZMod 7`.
example (k₁ k₂ kFinal state : SPNState 2 (ZMod 7)) :
    let sboxes : Fin 2 → Equiv.Perm (ZMod 7) :=
      ![Equiv.addRight (1 : ZMod 7), Equiv.addRight (3 : ZMod 7)]
    let mix := spnPermuteEquiv (G := ZMod 7) (Equiv.swap (0 : Fin 2) 1)
    (spnNetworkEquiv sboxes mix [k₁, k₂] kFinal).symm
      (spnNetworkEquiv sboxes mix [k₁, k₂] kFinal state) = state ∧
    Function.Bijective (spnNetworkEquiv sboxes mix [k₁, k₂] kFinal) :=
  ⟨(spnNetworkEquiv _ _ [k₁, k₂] kFinal).symm_apply_apply state,
   bijective_spnNetworkEquiv _ _ [k₁, k₂] kFinal⟩

-- Concrete wire-level bit-permutation layer on `SPNState 2 (BitString 3)` swapping `(0, 0)` and
-- `(1, 2)`.
example (state : SPNState 2 (BitString 3)) :
    let mix := spnBitPermuteEquiv (Equiv.swap ((0 : Fin 2), (0 : Fin 3)) (1, 2))
    mix (mix state) = state := by
  dsimp; ext i j; simp

-- Concrete 4-round unbalanced Feistel network on `ZMod 5 × ZMod 7` and odd block length
-- `BitString 5`.
example (f₁ f₃ : ZMod 7 → ZMod 5) (f₂ f₄ : ZMod 5 → ZMod 7) (p : ZMod 5 × ZMod 7)
    (g₁ g₃ : BitString 3 → BitString 2) (g₂ g₄ : BitString 2 → BitString 3) (x : BitString 5) :
    (unbalancedFeistel4 f₁ f₂ f₃ f₄).symm (unbalancedFeistel4 f₁ f₂ f₃ f₄ p) = p ∧
    (unbalancedFeistel4BitString 5 g₁ g₂ g₃ g₄).symm
      (unbalancedFeistel4BitString 5 g₁ g₂ g₃ g₄ x) = x :=
  ⟨(unbalancedFeistel4 f₁ f₂ f₃ f₄).symm_apply_apply p,
   (unbalancedFeistel4BitString 5 g₁ g₂ g₃ g₄).symm_apply_apply x⟩

-- Concrete periodicity of zero Feistel rounds over `ZMod 7`: 5 rounds swap halves and 6 rounds act
-- as the identity.
example :
    feistelNetwork (List.replicate 5 (0 : ZMod 7 → ZMod 7)) (3, 5) = (5, 3) ∧
    feistelNetwork (List.replicate 6 (0 : ZMod 7 → ZMod 7)) (3, 5) = (3, 5) := by
  rw [feistelNetwork_replicate_zero 5, feistelNetwork_replicate_zero 6]; decide

-- Concrete period-3 law for identity Feistel rounds on `BitString 4`.
example (l r : BitString 4) :
    feistelNetwork (List.replicate 9 (id : BitString 4 → BitString 4)) (l, r) = (l, r) ∧
    feistelNetwork (List.replicate 11 (id : BitString 4 → BitString 4)) (l, r) = (l + r, l) := by
  have hneg : ∀ a : BitString 4, -a = a := fun a => funext fun i => BooleanRing.neg_eq (a i)
  rw [feistelNetwork_replicate_id hneg 9, feistelNetwork_replicate_id hneg 11]
  exact ⟨rfl, rfl⟩

-- Concrete 1-round CPA distinguisher advantage `6 / 7` over `ZMod 7`.
example (f : ZMod 7 → ZMod 7) :
    (Game.advantage
      (OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
        (feistel1CPAAttack (0 : ZMod 7) 1))
      (randomFunctionGame (feistel1CPAAttack (0 : ZMod 7) 1)) : ℝ) = 6 / 7 ∧
    6 / 7 ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistelRoundEquiv f p))
          (feistel1CPAAttack (0 : ZMod 7) 1))
        (idealPermGame (feistel1CPAAttack (0 : ZMod 7) 1)) : ℝ) := by
  have hrf := advantage_feistel1CPAAttack_randomFunctionGame f (0 : ZMod 7) 1
  have hprp := le_advantage_feistel1CPAAttack_idealPermGame f (0 : ZMod 7) 1
  simp only [ZMod.card 7, Nat.cast_ofNat] at hrf hprp
  exact ⟨by linarith, by linarith⟩

-- Concrete 2-round CPA distinguisher advantage `41 / 48` over `ZMod 7`.
example (f₁ f₂ : ZMod 7 → ZMod 7) :
    41 / 48 ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistelNetwork [f₁, f₂] p))
          (feistel2CPAAttack (0 : ZMod 7) 1 2))
        (idealPermGame (feistel2CPAAttack (0 : ZMod 7) 1 2)) : ℝ) := by
  have h := le_advantage_feistel2CPAAttack_idealPermGame f₁ f₂ (l₀ := (0 : ZMod 7)) (l₁ := 1) 2
    (by decide) (by decide)
  simp only [ZMod.card 7, Nat.cast_ofNat] at h; linarith

-- Concrete 3-round repeated-key (`[f, f, f]`) CPA distinguisher advantage `127 / 128` on
-- `BitString 4`.
example (f : BitString 4 → BitString 4) :
    127 / 128 ≤
      (Game.advantage
        (OracleComp.interpret (fun p => PMF.pure (feistel3 f f f p))
          (feistel3RepeatedKeyCPAAttack (0 : BitString 4)))
        (idealPermGame (feistel3RepeatedKeyCPAAttack (0 : BitString 4))) : ℝ) := by
  have hneg : ∀ a : BitString 4, -a = a := fun a => funext fun i => BooleanRing.neg_eq (a i)
  have h := le_advantage_feistel3RepeatedKeyCPAAttack_idealPermGame hneg f (0 : BitString 4)
    (by decide)
  have hcard : (Fintype.card (BitString 4) : ℝ) = 16 := by simp [Fintype.card_pi, Fintype.card_fin]
  rw [hcard] at h; linarith

-- Concrete sharper 3-round CCA distinguisher advantage `5 / 6` over `ZMod 7`.
example (f₁ f₂ f₃ : ZMod 7 → ZMod 7) :
    5 / 6 ≤
      (Game.advantage
        (OracleComp.interpret (feistelStrongOracle (feistel3 f₁ f₂ f₃))
          (feistel3CCAAttack (0 : ZMod 7) 1 2))
        (idealStrongGame (feistel3CCAAttack (0 : ZMod 7) 1 2)) : ℝ) := by
  have h := le_advantage_feistel3CCAAttack_idealStrongGame_of_two_le_card f₁ f₂ f₃
    (l₀ := (0 : ZMod 7)) (l₁ := 1) 2 (by decide) (by decide)
  simp only [ZMod.card 7, Nat.cast_ofNat] at h; linarith

end ComplexityTests.Crypto.FeistelNetworks
