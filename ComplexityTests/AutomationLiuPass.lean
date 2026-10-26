/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Crypto.Computational.OneWay.CondEPPRG
public import Complexity.Crypto.Computational.OneWay.LiuPassConverse
public import Complexity.Computability.Complexity.AverageCase
public import Complexity.Computability.Kolmogorov.AverageCase
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Complexity.Foundations.Data.Nat.Asymptotics
import Complexity.Foundations.Data.Nat.Log
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime


/-!
# Automatic Liu–Pass threshold arithmetic

The first goal retains the original threshold expression, arbitrary constants and automatic
proof script from `OneWay/LiuPass.lean`, at its original default budget. It does not invoke the
private named threshold certificate or supply intermediate arithmetic certificates.
The separate captured-callback controls test that an arbitrary leaf needs its own certificate.
-/

@[expose] public section

namespace Cslib.Crypto.AutomationLiuPassTests

open Cslib.Complexity Probability Probability.PMF BitString Filter Kolmogorov Turing.MultiTapeTM

/-- The original threshold arithmetic, reproduced only for its automation regression. -/
def thresholdValue (γ d c n : ℕ) : ℕ :=
  let m := n + γ * Nat.log 2 n - c
  m - (2 * Nat.log 2 n + 3) - d * (Nat.log 2 m + 1)

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example (γ d c : ℕ) :
    ComputableInPolyTime (thresholdValue γ d c) encUnary encUnary := by
  unfold thresholdValue
  fun_prop

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example (γ d c : ℕ) (leaf : ℕ → ℕ)
    (hleaf : ComputableInPolyTime leaf encUnary encUnary) :
    ComputableInPolyTime (fun n =>
      let m := n + γ * leaf n - c
      m - (2 * leaf n + 3) - d * (leaf m + 1)) encUnary encUnary := by
  fun_prop

-- The complete missing-leaf control still times out under both default and 256-step
-- search; it remains open in #1155, with its failed source/logs preserved separately.

end Cslib.Crypto.AutomationLiuPassTests
