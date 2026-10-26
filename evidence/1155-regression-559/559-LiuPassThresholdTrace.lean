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

namespace Cslib.Crypto.AutomationLiuPassTests

open Cslib.Complexity Probability Probability.PMF BitString Filter Kolmogorov Turing.MultiTapeTM

private def thresholdValue (γ d c n : ℕ) : ℕ :=
  let m := n + γ * Nat.log 2 n - c
  m - (2 * Nat.log 2 n + 3) - d * (Nat.log 2 m + 1)

set_option trace.Meta.Tactic.fun_prop true in
set_option maxHeartbeats 200000 in
example (γ d c : ℕ) :
    ComputableInPolyTime (thresholdValue γ d c) encUnary encUnary := by
  unfold thresholdValue
  fun_prop

end Cslib.Crypto.AutomationLiuPassTests
