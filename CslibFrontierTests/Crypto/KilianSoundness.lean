/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Kilian.NP
import CslibFrontier.Tactic.PPT

/-!
# Tests for the soundness of Kilian's protocol

Under a hash that ignores its message, every path of the right length opens every leaf, so a
cheating prover can answer two runs with different bits at one position; both runs are accepted
by a PCP verifier that accepts everything, and the binding adversary's output breaks position
binding, as `merkleBreaksBinding_kilianBindingOutput` predicts. Under a hash that returns its
message, the honest prover's two runs never conflict, and the adversary's fallback output does not
break binding. A constant prover is strict PPT, so `KilianProver.IsPPT` is not vacuous.
-/

namespace ComplexityTests.Crypto.KilianSoundness

open Cslib Cslib.Complexity Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- A hash that ignores its message. -/
def constHash (k _ : List Bool) : List Bool := k

/-- A hash that returns its message. -/
def idHash (_ x : List Bool) : List Bool := x

/-- A PCP verifier that accepts everything: one random bit chooses the address `1000` or `5`. -/
def trivialVerifier : PCPVerifier (List Bool) where
  coins _ := 1
  queries := fun (_, ρ) => [if ρ.headD false then 5 else 1000]
  verdict _ := true

/-- The statement. -/
abbrev x : List Bool := [true, false]

/-- The key. -/
abbrev key : List Bool := [false, true]

/-- Under `constHash`, the root of every tree is the key, and so is every path label. -/
abbrev root : List Bool := key

/-- Two runs on the same random string, opening its position to different bits. -/
abbrev response₁ : KilianResponse := [[(true, [key])]]
abbrev response₂ : KilianResponse := [[(false, [key])]]

-- Both runs are accepted.
example : kilianVerify constHash trivialVerifier key x root [[true]] response₁ = true := by decide
example : kilianVerify constHash trivialVerifier key x root [[true]] response₂ = true := by decide

-- The adversary finds the conflict, and its output breaks position binding.
example : kilianConflict trivialVerifier x (kilianOpenings trivialVerifier x [[true]] response₁)
    (kilianOpenings trivialVerifier x [[true]] response₂) =
      some ((5, true, [key]), (5, false, [key])) := by decide
example : merkleBreaksBinding constHash key (kilianBindingOutput trivialVerifier x root
    (kilianOpenings trivialVerifier x [[true]] response₁)
    (kilianOpenings trivialVerifier x [[true]] response₂)) = true := by decide

-- Two honest runs on different random strings under `idHash` open different positions with no
-- conflict; the fallback output does not break binding.
example : kilianConflict trivialVerifier x
    (kilianOpenings trivialVerifier x [[false]]
      (kilianRespond idHash trivialVerifier key x [true, true] [[false]]))
    (kilianOpenings trivialVerifier x [[true]]
      (kilianRespond idHash trivialVerifier key x [true, true] [[true]])) = none := by decide
example : merkleBreaksBinding idHash key (kilianBindingOutput trivialVerifier x
    (kilianCommit idHash trivialVerifier key x [true, true])
    (kilianOpenings trivialVerifier x [[false]]
      (kilianRespond idHash trivialVerifier key x [true, true] [[false]]))
    (kilianOpenings trivialVerifier x [[true]]
      (kilianRespond idHash trivialVerifier key x [true, true] [[true]]))) = false := by decide

/-- A prover that always claims `x` with the key as its root, and answers nothing. -/
def constantProver : KilianProver (List Bool) where
  commit _ k := pure ((x, k), [])
  answer _ _ ρs := pure (ρs.map fun _ => [])

-- Its two stages are strict PPT, so the hypothesis of `HashFamily.kilianSound` can be met.
example : constantProver.IsPPT encBits where
  commit := by
    unfold constantProver
    ppt
  answer := by
    unfold constantProver
    ppt

end ComplexityTests.Crypto.KilianSoundness
