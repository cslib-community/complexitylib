/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Computability.Complexity.Classes.SharpP.Combinators
import CslibFrontier.Computability.Complexity.Classes.Toda.Counting
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-! Plain/tidy automation boundaries: bounded failure, verifier rules, the SBP
binary threshold and Toda's input-dependent counting verifier. -/

namespace CslibFrontierTests.PolyTimeMixes

open Cslib Cslib.Complexity Turing.MultiTapeTM
variable {α : Type} {enc : α ↪ List Bool}

set_option maxHeartbeats 2000 in
-- Check that a bounded failed attempt and the explicit certificate fit a small heartbeat budget.
-- The certificate route takes about 34 heartbeats, so the speculative attempt needs only a small
-- step budget. `maxSteps` counts visited goals, not rules that fail to unify, so the heartbeat
-- cost per step depends on how many candidate rules each goal has: 8 steps cost about 250 here
-- and 16 about 1500.
/-- The WPP singleton target: bound a failed tidy search before explicitly preparing the plain
hypothesis. -/
example {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin) :
    ComputableTidilyInPolyTime (fun a => [f a]) enc (encList encIntBin) := by
  fail_if_success fun_prop (config := { maxSteps := 8 })
  have hf := hf.tidy
  fun_prop

/-- `polytime` prepares plain hypotheses, verifier combinators (`andVerifier`, `orVerifier`,
`selectVerifier`), the SBP threshold, and Toda's `sharpTest` without manual conversions. -/
example {f : α → ℤ} (hf : ComputableInPolyTime f enc encIntBin)
    {k : α → ℕ} {V W W' : α × List Bool → Bool}
    (hk : ComputableInPolyTime k enc encUnary)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hW : ComputableInPolyTime W (encPair enc encBits) encBool)
    (hW' : ComputableTidilyInPolyTime W' (encPair enc encBits) encBool)
    {kNat : α → ℕ} (hkNat : ComputableInPolyTime kNat enc encNat) (q : Polynomial ℕ)
    {VToda : (α × List Bool) × List Bool → Bool}
    (hVToda : ComputableInPolyTime VToda (encPair (encPair enc encBits) encBits) encBool)
    (R Z : Polynomial ℕ) :
    ComputableTidilyInPolyTime (fun a => [f a]) enc (encList encIntBin) ∧
    ComputableInPolyTime (andVerifier k V W) (encPair enc encBits) encBool ∧
    ComputableInPolyTime (orVerifier k V W) (encPair enc encBits) encBool ∧
    ComputableInPolyTime (selectVerifier V W) (encPair enc encBits) encBool ∧
    ComputableInPolyTime (selectVerifier V W') (encPair enc encBits) encBool ∧
    ComputableInPolyTime (fun a => 3 * (kNat a * 2 ^ q.eval (enc a).length)) enc encNat ∧
    ComputableInPolyTime (fun x : α × List Bool =>
      Toda.sharpTest (fun r z => VToda ((x.1, r), z)) (R.eval (enc x.1).length)
        (Z.eval (enc x.1).length) x.2) (encPair enc encBits) encBool :=
  ⟨by polytime, by fun_prop, by fun_prop, by fun_prop, by fun_prop, by polytime, by polytime⟩

end CslibFrontierTests.PolyTimeMixes
