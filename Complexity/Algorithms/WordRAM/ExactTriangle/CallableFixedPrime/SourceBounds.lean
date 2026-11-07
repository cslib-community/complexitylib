/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Prefix
public import Complexity.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime.Width

/-!
# Initialized logarithmic admission and polynomial prefix support

The explicit positive logarithmic constant depends only on the original weight exponent.
Every wider native prefix has the same polynomial numerical/support envelope. These coarse
bounds cover the real computed modulus; the program does not allocate by clearing this envelope.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime

private theorem input_placement {n d g p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    workspaceBase n ≤ (n + 2) ^ (12332 * (κ + 9) + 5) ∧
      inputWordBound n d g p values ≤ (n + 2) ^ (12332 * (κ + 9) + 5) := by
  let B := n + 2
  have hb : 2 ≤ B := by dsimp only [B]; omega
  have hb1 : 1 ≤ B := by omega
  have hn : n ≤ B := by dsimp only [B]; omega
  have hn2 : n * n ≤ B ^ 2 := (Nat.mul_le_mul hn hn).trans_eq (by ring)
  have h2 : 1 ≤ B ^ 2 := Nat.one_le_pow _ _ hb1
  have h8 : 8 ≤ B ^ 3 :=
    (by decide : 8 ≤ (2 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hb 3)
  have hbase : workspaceBase n ≤ B ^ 5 := by
    calc
      _ ≤ 8 * B ^ 2 := by dsimp only [workspaceBase]; omega
      _ ≤ B ^ 3 * B ^ 2 := Nat.mul_le_mul_right _ h8
      _ = _ := by ring
  refine ⟨hbase.trans (Nat.pow_le_pow_right hb1 (by omega)), ?_⟩
  have hM := windowSize_le_pow values hlen hv hd hg hp hA
  have h4 : 4 ≤ B ^ 2 := (by decide : 4 ≤ (2 : ℕ) ^ 2).trans (Nat.pow_le_pow_left hb 2)
  calc
    _ ≤ B ^ 2 * B ^ (12332 * (κ + 9)) := Nat.mul_le_mul h4 hM
    _ = B ^ (12332 * (κ + 9) + 2) := by rw [← pow_add, Nat.add_comm]
    _ ≤ _ := Nat.pow_le_pow_right hb1 (by omega)

/-- All physical widths beyond a positive constant times log(n+2) admit the actual initialized
program. No weight exponent or width certificate is passed to the program. -/
theorem inputWidth_le_log {n d g p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    inputWidth n d g p values ≤
      (24664 * (κ + 9) + 19) * Nat.clog 2 (n + 2) := by
  obtain ⟨hb, hP⟩ := input_placement values hlen hv hd hg hp hA
  have h := admissionWidth_le_log values hlen hv hd hg hp hA hb hP
  simpa only [inputWidth, show 12332 * (κ + 9) + (12332 * (κ + 9) + 5) + 14 =
    24664 * (κ + 9) + 19 by omega] using h

/-- Polynomial bound on the width-independent envelope that controls every initialized prefix. -/
theorem prefixBound_le_pow {n d g p A κ : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hv : ∀ z ∈ values, z.natAbs ≤ A)
    (hd : d ≤ n) (hg : g ≤ n) (hp : p ≤ n) (hA : A ≤ (n + 2) ^ κ) :
    prefixBound n d g p values ≤ (n + 2) ^ (24664 * (κ + 9) + 20) := by
  obtain ⟨hb, hP⟩ := input_placement values hlen hv hd hg hp hA
  have h := wordBound_le_pow values hlen hv hd hg hp hA hb hP
  simpa only [prefixBound, show 12332 * (κ + 9) + (12332 * (κ + 9) + 5) + 15 =
    24664 * (κ + 9) + 20 by omega] using h

end Cslib.Algorithms.WordRAM.ExactTriangle.CallableFixedPrime
