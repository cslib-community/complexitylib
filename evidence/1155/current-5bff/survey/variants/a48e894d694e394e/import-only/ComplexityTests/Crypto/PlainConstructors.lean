/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.PRGToOneWay


import Diag1155.Measure
/-! Public cryptographic constructors accept ordinary deterministic certificates. -/

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

example {f : List Bool → List Bool} (hf : ComputableInPolyTime f encBits encBits)
    (hnegligible : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n)))) :
    OneWay f := OneWay.of_inversion_negligible hf hnegligible

-- The real reduction uses the PRG's existing plain field, without a public tidy conversion.
example {generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hgenerator : PseudorandomGenerator generator length) (hdouble : ∀ n, 2 * n ≤ length n) :
    OneWay generator := hgenerator.oneWay hdouble

-- Both the unary parameter and arbitrary sample word are part of the certified input.
example {X Y : ℕ → PMF (List Bool)} (h : ComputationallyIndistinguishable X Y) :
    ComputationallyIndistinguishable (fun n => (X n).map (fun word => word.take n))
      (fun n => (Y n).map (fun word => word.take n)) :=
  h.map (by polytime)
