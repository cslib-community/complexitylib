/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
public import CslibFrontier.Tactic.PolyTime

/-!
# Plain captured polynomial-time automation tests

Checks that `fun_prop` (with `maxTransitionDepth := 0`) and `polytime` discharge plain
`Turing.MultiTapeTM.ComputableInPolyTime` goals through `PolyTime.Captured`, including hidden
list-element encoding resolution via `@[program_certificate hlist]` and explicit `binary_mod'`
without making `HMod.hMod` dispatch ambiguous.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.PolyTimeCaptured

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool}

-- `cond'` works in both `fun_prop` and `polytime`, with arbitrary Boolean guard encoding.
example {encC : Bool ↪ List Bool} (c : α → Bool) (t e : α → β)
    (hc : ComputableInPolyTime c enc encC)
    (ht : ComputableInPolyTime t enc encOut)
    (he : ComputableInPolyTime e enc encOut) :
    ComputableInPolyTime (fun a => _root_.cond (c a) (t a) (e a)) enc encOut := by
  fail_if_success (clear hc; fun_prop (config := { maxTransitionDepth := 0 }))
  fun_prop (config := { maxTransitionDepth := 0 })

example (c : α → Bool) (t e : α → List Bool)
    (hc : ComputableInPolyTime c enc encBool)
    (ht : ComputableInPolyTime t enc encBits)
    (he : ComputableInPolyTime e enc encBits) :
    ComputableInPolyTime (fun a => _root_.cond (!(c a)) (t a) (e a)) enc encBits := by
  polytime

-- `listHeadDWithInput` handles computed fallbacks, constant fallbacks, and outer projections.
example (f : α → List β) (d : α → β)
    (hf : ComputableInPolyTime f enc (encList encOut))
    (hd : ComputableInPolyTime d enc encOut) :
    ComputableInPolyTime (fun a => (f a).headD (d a)) enc encOut := by
  fail_if_success (clear hf; fun_prop (config := { maxTransitionDepth := 0 }))
  fail_if_success (clear hd; fun_prop (config := { maxTransitionDepth := 0 }))
  fun_prop (config := { maxTransitionDepth := 0 })

example (f : α → List (List Bool × ℕ)) (d : α → List Bool × ℕ)
    (hf : ComputableInPolyTime f enc (encList (encPair encBits encNat)))
    (hd : ComputableInPolyTime d enc (encPair encBits encNat)) :
    ComputableInPolyTime (fun a => ((f a).headD (d a)).1) enc encBits := by
  polytime

example (f : α → List (List Bool))
    (hf : ComputableInPolyTime f enc (encList encBits)) :
    ComputableInPolyTime (fun a => (f a).headD []) enc encBits := by
  polytime

example (f : α → List (List Bool × ℕ))
    (hf : ComputableInPolyTime f enc (encList (encPair encBits encNat))) :
    ComputableInPolyTime (fun a => (f a).head?.isSome) enc encBool := by
  fun_prop (config := { maxTransitionDepth := 0 })

-- `listTakeWithInput` and `listDropWithInput` check the unary count premise.
example (f : α → List β) (k : α → ℕ)
    (hf : ComputableInPolyTime f enc (encList encOut))
    (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a => ((f a).take (k a)).drop 1) enc (encList encOut) := by
  fail_if_success (clear hk; fun_prop (config := { maxTransitionDepth := 0 }))
  fun_prop (config := { maxTransitionDepth := 0 })

example (f : α → List β) (k : α → ℕ)
    (hf : ComputableInPolyTime f enc (encList encOut))
    (hk : ComputableInPolyTime k enc encUnary) :
    ComputableInPolyTime (fun a => ((f a).drop (k a)).take (k a)) enc (encList encOut) := by
  polytime

-- `countWithInput` resolves the hidden element encoding `encNat` (absent from output `encUnary`)
-- via `@[program_certificate hlist]` in `polytime`, and via `hlist`-first order in `fun_prop`.
example (f : α → List ℕ) (x : α → ℕ)
    (hf : ComputableInPolyTime f enc (encList encNat))
    (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun a => (f a).count (x a)) enc encUnary := by
  fail_if_success (clear hf; polytime)
  fail_if_success (clear hx; polytime)
  polytime

example (f : α → List (ℕ × List Bool))
    (hf : ComputableInPolyTime f enc (encList (encPair encNat encBits))) :
    ComputableInPolyTime (fun a => (f a).count (0, [])) enc encUnary := by
  polytime

example (f : α → List ℕ) (x : α → ℕ)
    (hf : ComputableInPolyTime f enc (encList encNat))
    (hx : ComputableInPolyTime x enc encNat) :
    ComputableInPolyTime (fun a => (f a).count (x a)) enc encUnary := by
  fun_prop (config := { maxTransitionDepth := 0 })

-- `anyConst` scans a fixed list whose index type carries no encoding.
private structure UnencodedTag where
  label : ℕ → ℕ

example (tags : List UnencodedTag) (test : α → UnencodedTag → Bool)
    (htest : ∀ t ∈ tags, ComputableInPolyTime (fun a => test a t) enc encBool) :
    ComputableInPolyTime (fun a => tags.any (test a)) enc encBool := by
  fun_prop (config := { maxTransitionDepth := 0 })

example (tags : List UnencodedTag) (test : α → UnencodedTag → Bool)
    (htest : ∀ t ∈ tags, ComputableInPolyTime (fun a => test a t) enc encBool) :
    ComputableInPolyTime (fun a => tags.any (test a)) enc encBool := by
  polytime

-- `binary_mod'` is available explicitly on `encNat` without making `HMod.hMod` ambiguous on
-- `encUnary`.
example (x y : α → ℕ)
    (hx : ComputableInPolyTime x enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => x a % y a) enc encNat := by
  fail_if_success fun_prop (config := { maxTransitionDepth := 0 })
  exact ComputableInPolyTime.binary_mod' hx hy

example (x : α → ℕ) (hx : ComputableInPolyTime x enc encUnary) :
    ComputableInPolyTime (fun a => x a % 2) enc encUnary := by
  polytime

end CslibFrontierTests.PolyTimeCaptured
