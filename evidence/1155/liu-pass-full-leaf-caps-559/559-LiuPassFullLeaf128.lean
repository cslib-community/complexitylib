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
# Matched configured full-leaf Liu–Pass diagnostic

The supplied-leaf goal is copied from AutomationLiuPass with its entire expression and telescope.
Both positive and missing-leaf control use maxSteps128 at the original200000 heartbeat budget.
This does not change the existing bare original positive or resolve default rejection parity.
-/

namespace Cslib.Crypto.AutomationLiuPassTests

open Cslib.Complexity Probability Probability.PMF BitString Filter Kolmogorov Turing.MultiTapeTM

/-- The original threshold arithmetic, reproduced only for its automation regression. -/
def thresholdValue (γ d c n : ℕ) : ℕ :=
  let m := n + γ * Nat.log 2 n - c
  m - (2 * Nat.log 2 n + 3) - d * (Nat.log 2 m + 1)

set_option maxHeartbeats 200000 in
-- Pin the original default as the regression budget; do not raise it.
example (γ d c : ℕ) (leaf : ℕ → ℕ)
    (hleaf : ComputableInPolyTime leaf encUnary encUnary) :
    ComputableInPolyTime (fun n =>
      let m := n + γ * leaf n - c
      m - (2 * leaf n + 3) - d * (leaf m + 1)) encUnary encUnary := by
  fun_prop (maxSteps := 128)

set_option maxHeartbeats 200000 in
-- Same original heartbeat budget and explicit search cap as the supplied-leaf positive.
example (_γ _d _c : ℕ) (_leaf : ℕ → ℕ) : True := by
  fail_if_success
    have : ComputableInPolyTime (fun n =>
        let m := n + _γ * _leaf n - _c
        m - (2 * _leaf n + 3) - _d * (_leaf m + 1)) encUnary encUnary := by
      fun_prop (maxSteps := 128)
  trivial

end Cslib.Crypto.AutomationLiuPassTests
