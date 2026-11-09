/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Cost

/-!
# Charged cost transfer for an interleaved Chan–He visitor

Traversal charges every pending descriptor, including skipped entries. Solver charges depend
only on the number of emitted mathematical nodes. The fixed root and forest overheads reuse
the existing traversal budgets; the callback and packed-tail release cost the actual host bound
plus eight.

The ledger below combines proved instruction budgets, rather than asserting exact running time.
It includes initialized frontend execution, all scalar and layout setup, the value-envelope
loop, every root descriptor and stack transition, Boolean accumulation and the final halt.
Its count bound is purely the finite reduction's existing theorem and uses no completed
catalogue-producing native execution.

## Main definitions

* `callbackTime`: the actual host bound and charged callback setup/receive instructions.
* `forestCost`: every root transition and one callback charge per emitted node.
* `largeCost`: the complete fused large-input branch budget, without the outer prefix or halt.

## Main results

* `cost_ledger`: exact equality between the two symbolic charged budgets, including slack.
* `largeCost_le`, `cost_le`: the existing ordinary decision bound covers the fused visitor.
* `allNodes_cost_le`: the same transfer at the exact finite output list's node count.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor

open Cslib.WordRAM

/-- Four native argument copies, the certified host, Boolean receive and one packed-tail release. -/
@[expose] def callbackTime {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n : ℕ) : ℕ :=
  Host.callerTime (instanceLength κ n)
    (c.time (Host.sideLength (instanceLength κ n))
      (2 * (n + 2) ^ envelopeExponent κ + 1)) + 8

/-- Charge all root work and descriptor/control overhead, but callbacks only for emitted nodes. -/
@[expose] def forestCost (κ n emitted T : ℕ) : ℕ :=
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  (Frontend.layout κ n).count *
    (ChanHe.Traversal.rootTime F (n + 1) m (2 * m ^ 2) + 17) + 2 + emitted * T

/-- Native large-branch budget: frontend, snapshot, prime setup, layout, envelope and forest.
The frontend's own final halt is excluded because its code is inlined into the visitor. -/
@[expose] def largeCost {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n emitted : ℕ) : ℕ :=
  let m := Cslib.Algorithms.ThreeSum.ChanHe.mPar n (2 * (n + 2) ^ κ)
  let F := Cslib.Algorithms.ThreeSum.ChanHe.fuel n
  (Frontend.cost κ n - 1) + 13 + (2 + ((m + 1) * (7 * m + 15) + 8)) +
    19 + (4 * (F + 1) + 5) + (6 + (4 * envelopeExponent κ + 2)) +
    forestCost κ n emitted (callbackTime κ c n)

/-- The reused preprocessing budget covers exactly the same root work and shared setup. -/
theorem largeCost_eq {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n emitted : ℕ) :
    largeCost κ c n emitted + 1 =
      ChanHe.Preprocessing.cost κ n + 4 * envelopeExponent κ + 8 +
        emitted * callbackTime κ c n := by
  have hfront : 0 < Frontend.cost κ n := by
    dsimp only [Frontend.cost]
    omega
  dsimp only [largeCost, forestCost, ChanHe.Preprocessing.cost]
  omega

/-- Full initialized prefix/branch/halt costs seven. Four units per callback and eighteen
fixed units remain as slack in the old budget; no solver call is charged for a skipped entry. -/
theorem cost_ledger {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n emitted : ℕ) :
    largeCost κ c n emitted + 7 + 18 + 4 * emitted =
      ChanHe.Preprocessing.cost κ n + 4 * envelopeExponent κ + 32 +
        emitted * (Host.callerTime (instanceLength κ n)
          (c.time (Host.sideLength (instanceLength κ n))
            (2 * (n + 2) ^ envelopeExponent κ + 1)) + 12) := by
  have h := largeCost_eq κ c n emitted
  dsimp only [callbackTime] at h
  simp only [Nat.mul_add] at h ⊢
  omega

/-- Any emitted-node count within the finite reduction's bound preserves the old cost envelope. -/
theorem cost_le {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n emitted : ℕ)
    (hcount : emitted ≤ instanceBound κ n) :
    largeCost κ c n emitted + 7 ≤ Decision.cost κ c n := by
  have h := cost_ledger κ c n emitted
  have hm := Nat.mul_le_mul_right
    (Host.callerTime (instanceLength κ n)
      (c.time (Host.sideLength (instanceLength κ n))
        (2 * (n + 2) ^ envelopeExponent κ + 1)) + 12) hcount
  dsimp only [Decision.cost]
  omega

/-- The large branch leaves the existing seven-instruction outer prefix/branch/halt allowance. -/
theorem largeCost_le {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n emitted : ℕ)
    (hcount : emitted ≤ instanceBound κ n) :
    largeCost κ c n emitted ≤ Decision.cost κ c n - 7 := by
  have h := cost_le κ c n emitted hcount
  omega

/-- The exact mathematical output count is covered without running the old native producer. -/
theorem allNodes_cost_le {r : ℕ} (κ : ℕ) (c : Host.Callee r) (n : ℕ) (input : Fin n → ℤ) :
    largeCost κ c n
        (Cslib.Algorithms.ThreeSum.ChanHe.allNodes n ((n + 2) ^ κ) input).length + 7 ≤
      Decision.cost κ c n := by
  apply cost_le
  simpa only [Cslib.Algorithms.ThreeSum.ChanHe.instances, List.length_map, instanceBound]
    using Cslib.Algorithms.ThreeSum.ChanHe.length_instances_le n ((n + 2) ^ κ) input

end Cslib.Algorithms.WordRAM.ThreeSum.Decision.Visitor
