/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ThreeSum.ChanHe.PreprocessingSnapshot

/-!
# Computing the shared native prime bitmap

The forest copies its computed candidate bound and fresh frontend endpoint into the existing
native trial-division program. Its actual bitmap and count are retained for every recursion root.

## Main results

* `primes_exec`: execute argument delivery and the complete table builder, preserving the frontend.

This native composition proof is original and reuses the existing primality computation.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing

open Cslib.WordRAM

/-- Compute the actual shared bitmap from the already computed frontend and numeric parameters. -/
theorem primes_exec {κ n w : ℕ} (x : Data 128) (hs : Saved κ n x)
    (hfit : Fits w ((Frontend.layout κ n).endpoint +
      Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ) + 4)) :
    let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
    let base := (Frontend.layout κ n).endpoint
    ∃ y, ExecWithin w (.seq preparePrimes (PrimeTable.program.rename primeRegisters)) x y
        (2 + ((m + 1) * (7 * m + 15) + 8)) ∧
      Saved κ n y ∧ y.mem = PrimeTable.memory x.mem base (m + 1) ∧
      y.regs (primeRegisters PrimeTable.count) = (Nat.primesLE m).card ∧
      (∀ q ≤ m, y.mem (base + q) = if q.Prime then 1 else 0) ∧
      ∀ p < base, y.mem p = x.mem p := by
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
  let base := (Frontend.layout κ n).endpoint
  let p := (x.set (primeRegisters PrimeTable.limit) m).set (primeRegisters PrimeTable.base) base
  have hp : Exec w preparePrimes x p 2 := by
    ram_eval [preparePrimes, p, hs.limit, hs.endpoint, m, base]
  have hpi : Function.Injective primeRegisters := by
    intro i j hij
    exact Fin.ext (congrArg (fun k : Fin 128 => k.val) hij)
  obtain ⟨z, hz, hmem, hcount, _, _⟩ := PrimeTable.exec (p.comap primeRegisters)
    (hfit.of_le (by change m + 3 ≤ base + m + 4; omega))
    (hfit.of_le (by change base + (m + 1) ≤ base + m + 4; omega))
  let y := z.extend primeRegisters p
  have he : ExecWithin w (.seq preparePrimes (PrimeTable.program.rename primeRegisters)) x y
      (2 + ((m + 1) * (7 * m + 15) + 8)) := by
    simpa +decide [y, p, Data.comap, primeRegisters, PrimeTable.limit, m] using
      hp.within.seq (hz.rename hpi)
  have hmemory : y.mem = PrimeTable.memory x.mem base (m + 1) := by
    simpa +decide [y, p, Data.extend, Data.comap, primeRegisters, PrimeTable.limit,
      PrimeTable.base] using hmem
  refine ⟨y, he, hs.congr (fun i hi _ => he.regs_eq ?_), hmemory, ?_, ?_, ?_⟩
  · have hh : ∀ i : Fin 128, 109 ≤ i.val →
        (Code.seq preparePrimes (PrimeTable.program.rename primeRegisters)).Preserves i := by decide
    exact hh i hi
  · have hc := congrArg (fun d : Data 15 => d.regs PrimeTable.count)
      (Data.comap_extend hpi z p)
    exact hc.trans (by simpa +decide [p, Data.comap, primeRegisters, PrimeTable.limit] using hcount)
  · intro q hq
    change y.mem (base + q) = if q.Prime then 1 else 0
    change q ≤ m at hq
    rw [hmemory]
    simp only [PrimeTable.memory, show base ≤ base + q ∧ base + q < base + (m + 1) by omega,
      and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · intro q hq
    rw [hmemory]
    simp only [PrimeTable.memory, show ¬(base ≤ q ∧ q < base + (m + 1)) by omega, ↓reduceIte]

end Cslib.Algorithms.WordRAM.ThreeSum.ChanHe.Preprocessing
