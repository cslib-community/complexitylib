/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SDitH.TweakSalt

/-! Checked 128-bit clients for SDitH v3 Algorithm 5, `TweakSalt`. -/

public section

namespace SDitHTweakSaltTests

open Cslib Cslib.Crypto.SDitH

def stripedSalt : BitString 128 := fun i => decide (i.val % 2 = 1)

def tweakFive : Fin (2 ^ 24) := ⟨5, by norm_num⟩

def tweakSix : Fin (2 ^ 24) := ⟨6, by norm_num⟩

-- Little-endian 5 has low bits 1, 0, 1, overriding the striped salt.
example : tweakSalt .hashBased stripedSalt tweakFive false 0 = true := by decide +kernel

example : tweakSalt .hashBased stripedSalt tweakFive false 1 = false := by decide +kernel

example : tweakSalt .hashBased stripedSalt tweakFive false 2 = true := by decide +kernel

-- Coordinates away from the low tweak and high tags retain the original salt.
example : tweakSalt .hashBased stripedSalt tweakFive false 24 = false := by decide +kernel

example : tweakSalt .hashBased stripedSalt tweakFive false 25 = true := by decide +kernel

-- Both variant-specific high layouts override the original high salt bits.
example : tweakSalt .hashBased stripedSalt tweakFive false 127 = false := by decide +kernel

example : tweakSalt .cipherBased stripedSalt tweakFive true 126 = true := by decide +kernel

example : tweakSalt .cipherBased stripedSalt tweakFive true 127 = false := by decide +kernel

-- Distinct tweaks and tags remain observably distinct within a fixed variant.
example :
    tweakSalt .hashBased stripedSalt tweakFive false ≠
      tweakSalt .hashBased stripedSalt tweakSix false := by
  decide +kernel

example :
    tweakSalt .cipherBased stripedSalt tweakFive false ≠
      tweakSalt .cipherBased stripedSalt tweakFive true := by
  decide +kernel

example : Function.Injective fun input : Fin (2 ^ 24) × Bool =>
    tweakSalt .hashBased stripedSalt input.1 input.2 := by
  exact tweakSalt_injective .hashBased (by norm_num) stripedSalt

example : Function.Injective fun input : Fin (2 ^ 24) × Bool =>
    tweakSalt .cipherBased stripedSalt input.1 input.2 := by
  exact tweakSalt_injective .cipherBased (by norm_num) stripedSalt

end SDitHTweakSaltTests
