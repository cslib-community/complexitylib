/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Tactic.PolyTime
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.Toda.Counting
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-! Plain/tidy automation boundaries from #558: bounded failure, verifier rules, the SBP
binary threshold and Toda's input-dependent counting verifier. -/

namespace ComplexityTests.PolyTimeMixes

open Cslib Cslib.Complexity Turing.MultiTapeTM
variable {α : Type} {enc : α ↪ List Bool}

set_option maxHeartbeats 2000 in
-- Check that a bounded failed attempt and the explicit certificate fit a small heartbeat budget.
/-- The WPP singleton target: bound a failed tidy search before explicitly preparing the plain
hypothesis. The default search on this shape can run to its heartbeat limit. -/
example {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin) :
    ComputableTidilyInPolyTime (fun a => [f a]) enc (encList encIntBin) := by
  fail_if_success fun_prop (config := { maxSteps := 32 })
  have hf := hf.tidy
  fun_prop

/-- `polytime` prepares the same plain hypothesis without a manual conversion. -/
example {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin) :
    ComputableTidilyInPolyTime (fun a => [f a]) enc (encList encIntBin) := by polytime

/-- Before: prepare each verifier for the existing tidy rule, then convert its result. -/
example {k : α → ℕ} {V W : α × List Bool → Bool}
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) :
    ComputableInPolyTime (andVerifier k V W) (encPair enc encBits) encBool :=
  .of_tidy (computableTidilyInPolyTime_andVerifier hk.tidy hV.tidy hW.tidy)

/-- After: the plain rule lets `fun_prop` use the plain hypotheses directly. -/
example {k : α → ℕ} {V W : α × List Bool → Bool}
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) :
    ComputableInPolyTime (andVerifier k V W) (encPair enc encBits) encBool := by fun_prop

example {k : α → ℕ} {V W : α × List Bool → Bool}
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) :
    ComputableInPolyTime (orVerifier k V W) (encPair enc encBits) encBool := by fun_prop

example {V W : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool) :
    ComputableInPolyTime (selectVerifier V W) (encPair enc encBits) encBool := by fun_prop

/-- The plain rules still accept a mixture of plain and tidy verifier certificates. -/
example {V W : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableTidilyInPolyTime W (encPair enc encBits) encBool) :
    ComputableInPolyTime (selectVerifier V W) (encPair enc encBits) encBool := by fun_prop

/-- Before: convert the binary input certificate, search tidily, and convert the result back. -/
example {k : α → ℕ} (hk : ComputableInPolyTime k enc encNat) (q : Polynomial ℕ) :
    ComputableInPolyTime (fun a => 3 * (k a * 2 ^ q.eval (enc a).length)) enc encNat := by
  have hk := hk.tidy
  exact .of_tidy (by fun_prop)

/-- The SBP threshold mixes binary `k`, unary exponents, multiplication and exponentiation. -/
example {k : α → ℕ} (hk : ComputableInPolyTime k enc encNat) (q : Polynomial ℕ) :
    ComputableInPolyTime (fun a => 3 * (k a * 2 ^ q.eval (enc a).length)) enc encNat := by
  polytime

/-- Toda's `sharpTest` carries the original input through two witness arguments. -/
example {V : (α × List Bool) × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair (encPair enc encBits) encBits) encBool)
    (R Z : Polynomial ℕ) :
    ComputableInPolyTime (fun x : α × List Bool =>
      Toda.sharpTest (fun r z => V ((x.1, r), z)) (R.eval (enc x.1).length)
        (Z.eval (enc x.1).length) x.2) (encPair enc encBits) encBool := by
  polytime

end ComplexityTests.PolyTimeMixes
