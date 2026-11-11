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
   messages, and `decapsNoCheck` accepts a tagged ciphertext.
2. `leakAdv` makes no `G` queries and `3` queries to `H`.
3. Without the re-encryption check, `leakAdv` has advantage at least `1 - 3 / 8 = 5 / 8`.
-/

@[expose] public section

namespace CslibFrontierTests.Crypto.FujisakiOkamotoNoCheck

open Cslib Cslib.Crypto Cslib.Crypto.Protocols Cslib.Crypto.Protocols.FujisakiOkamoto

/-- A perfectly correct toy PKE: the ciphertext is the message. -/
def toyPKE : ExplicitCoinPKE Unit Unit (Fin 2 → Bool) Unit (Fin 2 → Bool) where
  keyGen := pure ((), ())
  sampleCoins := pure ()
  encDet _ m _ := m
  dec _ c := some c

/-- The `FO-notbot` scheme over `leakyPKE toyPKE` with uniform messages and keys. -/
noncomputable def toyScheme :
    Scheme Unit Unit (Fin 2 → Bool) Unit ((Fin 2 → Bool) × Option (Fin 2)) (Fin 8) :=
  ⟨leakyPKE toyPKE, ProbComp.uniform _, ProbComp.uniform _⟩

/-! ### The bit-leaking PKE -/

example (c : Fin 2 → Bool) : (leakyPKE toyPKE).dec () (c, none) = some c := rfl

example : (leakyPKE toyPKE).dec () (![false, true], some 1) = some fun _ => true := rfl

example : (leakyPKE toyPKE).dec () (![false, true], some 0) = some fun _ => false := rfl

example (H : Bool × (Fin 2 → Bool) × ((Fin 2 → Bool) × Option (Fin 2)) → Fin 8)
    (dk : ImplicitSK Unit Unit (Fin 2 → Bool)) (c : Fin 2 → Bool) (i : Fin 2) :
    toyScheme.decapsNoCheck H dk (c, some i) = H (false, fun _ => c i, (c, some i)) :=
  Scheme.decapsNoCheck_of_dec_eq_some _ H dk rfl

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
