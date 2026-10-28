/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingSnapshot
public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingLayout

/-!
# Executing the native shared traversal layout

The controller copies computed parameters, doubles the actual magnitude, divides the common
packed length into four-cell groups and computes the explicit stack reservation by instructions.

## Main results

* `setupTraversal_exec`: actual nineteen-instruction layout setup and exact native controls.

The native layout and composition proof are original.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Execute all shared traversal arguments, constants and explicit-stack reservations. -/
theorem setupTraversal_exec {κ n w : ℕ} (x : Data 128) (hs : Saved κ n x)
    (hc : x.regs (primeRegisters PrimeTable.count) =
      (Nat.primesLE (Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ))).card)
    (hfit : Fits w ((arena κ n x.mem).floor + (arena κ n x.mem).U +
      (arena κ n x.mem).N + (arena κ n x.mem).fuel + 16)) :
    ∃ y, Exec w setupTraversal x y 19 ∧ Saved κ n y ∧
      (arena κ n x.mem).Controls y ∧ y.regs Traversal.outputCount = 0 ∧
      y.regs power = 1 ∧
      y.regs remaining = Cslib.Algorithms.ThreeSum.ChanHe.fuel n + 1 ∧
      y.regs scalar = 3 ∧ y.mem = x.mem := by
  let a := arena κ n x.mem
  let F := a.fuel
  let y := x |>.set Traversal.limit a.m |>.set Traversal.digits a.Λ
    |>.set Traversal.magnitude a.U |>.set Traversal.groups a.N
    |>.set Traversal.bitmap a.primes |>.set Traversal.primeCount (Nat.primesLE a.m).card
    |>.set Traversal.stackBase (a.primes + a.m)
    |>.set Traversal.stackBase a.stack
    |>.set Traversal.stackCapacity (F + F)
    |>.set Traversal.stackCapacity (F + F + 1) |>.set scalar 7
    |>.set Traversal.stackCapacity a.capacity |>.set Traversal.outputs a.table
    |>.set Traversal.outputCount 0 |>.set Traversal.zero 0 |>.set Traversal.one 1
    |>.set power 1 |>.set remaining (F + 1) |>.set scalar 3
  have hfloor : a.primes + a.m + 1 + 7 * (2 * F + 1) ≤ a.floor := by
    dsimp only [a, F, arena]
    omega
  have fit (v : ℕ) (hv : v ≤ a.floor + a.U + a.N + F + 16) : Fits w v := hfit.of_le hv
  have hU : Fits w (2 * (n + 2) ^ κ) := fit _ (by change a.U ≤ _; omega)
  have hN : Fits w (2 * a.m ^ 2) := fit _ (by change a.N ≤ _; omega)
  have hstack₀ : Fits w (a.primes + a.m) := fit _ (by omega)
  have hstack : Fits w a.stack := fit _ (by change a.primes + a.m + 1 ≤ _; omega)
  have hF₀ : Fits w (F + F) := fit _ (by omega)
  have hF₁ : Fits w (F + F + 1) := fit _ (by omega)
  have hcap : Fits w a.capacity := fit _ (by change 7 * (2 * F + 1) ≤ _; omega)
  have htable : Fits w a.table := fit _ (by change a.primes + a.m + 1 + 7 * (2 * F + 1) ≤ _; omega)
  have hnext : Fits w (F + 1) := fit _ (by omega)
  have h1 : Fits w 1 := fit _ (by omega)
  have h3 : Fits w 3 := fit _ (by omega)
  have h7 : Fits w 7 := fit _ (by omega)
  have hdiv : 8 * a.m ^ 2 / 4 = 2 * a.m ^ 2 := by omega
  simp only [a, F, arena, ← two_mul, Nat.mul_comm, Nat.add_assoc]
    at hU hN hstack₀ hstack hF₀ hF₁ hcap htable hnext hdiv
  dsimp only [primeRegisters, PrimeTable.count] at hc
  have he : Exec w setupTraversal x y 19 := by
    ram_eval [setupTraversal, y, a, F, arena, hs.limit, hs.digits, hs.magnitude,
      hs.length, hs.endpoint, hs.fuel, hs.one, hs.four, hc, hdiv, hU, hN,
      hstack₀, hstack, hF₀, hF₁, hcap, htable, hnext, h1, h3, h7,
      Traversal.limit, Traversal.digits, Traversal.magnitude, Traversal.groups,
      Traversal.bitmap, Traversal.primeCount, Traversal.stackBase, Traversal.stackCapacity,
      Traversal.outputs, Traversal.outputCount, Traversal.zero, Traversal.one,
      candidateLimit, labels, inputMagnitude, packedLength, four, firstFree, levels,
      one, power, remaining, scalar, primeRegisters, PrimeTable.count,
      ← two_mul, Nat.mul_comm, Nat.add_assoc]
  refine ⟨y, he, hs.congr (fun i hi hj => he.within.regs_eq ?_), ?_, ?_, ?_, ?_, ?_, rfl⟩
  · have hh : ∀ i : Fin 128, 109 ≤ i.val → i ≠ power → i ≠ remaining → i ≠ scalar →
        setupTraversal.Preserves i := by decide
    exact hh i hi (by intro hh; subst i; norm_num [power] at hj)
      (by intro hh; subst i; norm_num [remaining] at hj)
      (by intro hh; subst i; norm_num [scalar] at hj)
  · constructor <;> simp +decide [y, a, F, arena, Traversal.limit, Traversal.digits,
      Traversal.magnitude, Traversal.groups, Traversal.bitmap, Traversal.primeCount,
      Traversal.outputs, Traversal.stackBase, Traversal.stackCapacity,
      Traversal.zero, Traversal.one, scalar, remaining, power]
  all_goals simp +decide [y, F, a, arena, Traversal.outputCount,
    Traversal.one, Traversal.zero, Traversal.outputs, Traversal.stackCapacity,
    power, remaining, scalar]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
