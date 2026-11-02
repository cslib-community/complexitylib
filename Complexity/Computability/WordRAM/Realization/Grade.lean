/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.WordRAM.Realization.Loop

/-!
# Combined memory and local-work currency

`combinedCost p work s` adds the actual memory-history charge to an explicit local-work grading.
The grading is supplied by the client and matched by its `Realizes` certificate; the extensional
`Memory.Prog` term does not determine a canonical local-work cost. In particular, monad laws may
erase pure binds, whereas a chosen native realization must still pay for its control and glue.

The bind law uses the actual interpreted reply and memory state and includes one control-work
unit. The loop law reuses `iterationSum_eq`, retaining one control-work unit even on iterations
that issue no memory query. These are currency identities, not native instruction certificates.
A memory-only upper estimate requires a separate uniform bound on the supplied local work.

## Main definitions

* `combinedCost`: memory-history charge plus the explicitly supplied local-work grading.

## Main results

* `combinedCost_pure`: semantic return retains its local-work charge.
* `combinedCost_bind`: combined charges split at the actual returned value and state.
* `combinedCost_iterate`: a bounded loop sums body charges and adds its iteration count.
* `combinedCost_le_of_work_le`: a uniform local-work envelope gives a memory-only estimate.
* `scaled_potential_pay`: explicit clock, local-work and memory-potential bounds imply a scaled
  potential payment inequality.

## References

This grading API is original infrastructure for the existing memory-client realization rules.
-/

@[expose] public section

namespace Cslib.WordRAM.Realization

open Cslib.DataStructure

variable {α β δ σ : Type}

/-- The actual memory-history charge plus an explicit realization grading. This definition
alone does not certify that `work` pays for any native implementation. -/
def combinedCost (p : Memory.Prog α) (work : Memory.State → ℕ) (s : Memory.State) : ℕ :=
  memoryCost p s + work s

/-- Returning without a memory query still retains the supplied local-work grading. -/
@[simp] theorem combinedCost_pure (a : α) (work : Memory.State → ℕ) (s : Memory.State) :
    combinedCost (pure a) work s = work s := Nat.zero_add (work s)

/-- Sequential local work includes one control unit and evaluates the continuation grading at
the reply and state actually reached by the first computation. -/
theorem combinedCost_bind (p : Memory.Prog α) (q : α → Memory.Prog β)
    (first : Memory.State → ℕ) (next : α → Memory.State → ℕ) (s : Memory.State) :
    combinedCost (p.bind q)
        (fun s => first s + next ((Memory.spec 0).clientResult s p)
          ((Memory.spec 0).clientState s p) + 1) s =
      combinedCost p first s +
        combinedCost (q ((Memory.spec 0).clientResult s p))
          (next ((Memory.spec 0).clientResult s p)) ((Memory.spec 0).clientState s p) + 1 := by
  simp only [combinedCost, memoryCost_bind]
  omega

/-- Combined body charges are summed along the actual joint value/memory transition. The
additional `n` pays control work on every iteration, including query-free iterations. -/
theorem combinedCost_iterate (body : δ × σ → Memory.Prog σ)
    (work : (δ × σ) → Memory.State → ℕ) (d : δ) (n : ℕ) (a : σ) (s : Memory.State) :
    combinedCost (iterate body d n a) (iterationWork body work d n a) s =
      iterationSum (iterationStep body d)
        (fun q => combinedCost (body (d, q.1)) (work (d, q.1)) q.2) n (a, s) + n :=
  (iterationSum_eq body work d n a s).symm

/-- A memory-only estimate is available under an explicit uniform local-work envelope. The
constants precede every state. This arithmetic estimate supplies no native execution claim. -/
theorem combinedCost_le_of_work_le (p : Memory.Prog α) (work : Memory.State → ℕ)
    (a b : ℕ) (hwork : ∀ s, work s ≤ a * memoryCost p s + b) (s : Memory.State) :
    combinedCost p work s ≤ (a + 1) * memoryCost p s + b := by
  have h := hwork s
  simp only [combinedCost, Nat.add_mul, Nat.one_mul]
  omega

/-- Transfer a certified combined clock through an explicit local-work envelope and a memory
amortization inequality. Scale the memory potential by the same fixed exchange factor; the
result is pure arithmetic and does not supply an execution certificate. All constants and
charges are explicit, so a consumer must discharge the three premises for its own operation. -/
theorem scaled_potential_pay (M G n Φpre Φpost q factor a b : ℕ)
    (hn : n ≤ factor * (M + G + 1)) (hwork : G ≤ a * M + b)
    (hmem : M + Φpost ≤ q + Φpre) :
    n + factor * (a + 1) * Φpost ≤ factor * (a + 1) * q + factor * (b + 1) +
      factor * (a + 1) * Φpre := by
  have hcharge : M + G + 1 ≤ (a + 1) * M + (b + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hclock := hn.trans (Nat.mul_le_mul_left factor hcharge)
  rw [Nat.mul_add, ← Nat.mul_assoc] at hclock
  have hpotential := Nat.mul_le_mul_left (factor * (a + 1)) hmem
  rw [Nat.mul_add (factor * (a + 1)) M Φpost,
    Nat.mul_add (factor * (a + 1)) q Φpre] at hpotential
  omega

end Cslib.WordRAM.Realization
