/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NoCheck

/-!
# Tests for dropping the re-encryption check of `FO-notbot`

Instantiates `CslibFrontier.Crypto.Protocols.KEM.FujisakiOkamoto.NoCheck` on a perfectly correct
toy PKE whose ciphertext is the message itself, with messages `Fin 2 → Bool` and keys `Fin 8`:

1. `leakyPKE` decrypts honest ciphertexts as the toy PKE and tagged ciphertexts to constant
   messages, preserves `indCpaAdvantage`, `DeltaCorrect`, and `GammaSpread`, and makes
   `Scheme.decapsNotBot` reject tagged ciphertexts `(c, some i)` while `Scheme.decapsNoCheck`
   accepts them.
2. `leakAdv` makes no `G` queries and `3` queries to `H`.
3. Without the re-encryption check, `leakAdv` has advantage at least `1 - 3 / 8 = 5 / 8`.
-/

public section

namespace CslibFrontierTests.Crypto.FujisakiOkamotoNoCheck

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto
open Cslib.Probability
open scoped ENNReal

/-- A perfectly correct toy PKE: the ciphertext is the message. -/
@[expose] def toyPKE : ExplicitCoinPKE Unit Unit (Fin 2 → Bool) Unit (Fin 2 → Bool) where
  keyGen := pure ((), ())
  sampleCoins := pure ()
  encDet _ m _ := m
  dec _ c := some c

/-- `toyPKE` is perfectly correct (`DeltaCorrect 0`). -/
theorem toyPKE_deltaCorrect_zero : toyPKE.DeltaCorrect 0 :=
  toyPKE.deltaCorrect_zero_of_perfect fun _ _ _ _ _ _ => rfl

/-- `toyPKE` is `0`-spread (`2 ^ (-0) = 1`). -/
theorem toyPKE_gammaSpread_zero : toyPKE.GammaSpread 0 := by
  intro pk sk _ m c
  rw [neg_zero, Real.rpow_zero, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (PMF.toOuterMeasure_le_one _ _)

/-- The `FO-notbot` scheme over `leakyPKE toyPKE` with uniform messages and keys. -/
@[expose] noncomputable def toyScheme :
    Scheme Unit Unit (Fin 2 → Bool) Unit ((Fin 2 → Bool) × Option (Fin 2)) (Fin 8) :=
  ⟨leakyPKE toyPKE, ProbComp.uniform _, ProbComp.uniform _⟩

/-! ### The bit-leaking PKE and property preservation -/

example (c : Fin 2 → Bool) : (leakyPKE toyPKE).dec () (c, none) = some c := rfl

example : (leakyPKE toyPKE).dec () (![false, true], some 1) = some fun _ => true := rfl

example : (leakyPKE toyPKE).dec () (![false, true], some 0) = some fun _ => false := rfl

example (m₀ m₁ : Fin 2 → Bool)
    (A : Unit → (Fin 2 → Bool) × Option (Fin 2) → ProbComp Bool) :
    (leakyPKE toyPKE).indCpaAdvantage m₀ m₁ A =
      toyPKE.indCpaAdvantage m₀ m₁ fun pk c => A pk (c, none) :=
  leakyPKE_indCpaAdvantage toyPKE m₀ m₁ A

example : (leakyPKE toyPKE).DeltaCorrect 0 :=
  leakyPKE_deltaCorrect toyPKE toyPKE_deltaCorrect_zero

example : (leakyPKE toyPKE).GammaSpread 0 :=
  leakyPKE_gammaSpread toyPKE toyPKE_gammaSpread_zero

/-! ### Rejection with the re-encryption check vs acceptance without it -/

example (G : (Fin 2 → Bool) → Unit)
    (H : Bool × (Fin 2 → Bool) × ((Fin 2 → Bool) × Option (Fin 2)) → Fin 8)
    (dk : ImplicitSK Unit Unit (Fin 2 → Bool)) (c : Fin 2 → Bool) (i : Fin 2) :
    toyScheme.decapsNotBot G H dk (c, some i) = H (true, dk.fallback, (c, some i)) ∧
    toyScheme.decapsNoCheck H dk (c, some i) = H (false, fun _ => c i, (c, some i)) :=
  ⟨decapsNotBot_leakyPKE_some toyPKE _ _ G H dk c i,
   Scheme.decapsNoCheck_of_dec_eq_some _ H dk rfl⟩

/-! ### Query bounds -/

example : ROQueryBounds
    (leakAdv (PK := Unit) (R := Unit) (CT := Fin 2 → Bool) (K := Fin 8) (n := 2)) 0 3 :=
  roQueryBounds_leakAdv

/-! ### The attack -/

example : (5 / 8 : ℝ) ≤
    (Game.advantage (toyScheme.eagerNoCheckGame leakAdv false)
      (toyScheme.eagerNoCheckGame leakAdv true) : ℝ) := by
  have h := advantage_eagerNoCheckGame_leakAdv toyPKE (ProbComp.uniform _)
    (ProbComp.uniform (Fin 8)) (ProbComp.eval_uniform _) fun _ _ _ _ _ _ => rfl
  norm_num at h
  exact h

end CslibFrontierTests.Crypto.FujisakiOkamotoNoCheck
