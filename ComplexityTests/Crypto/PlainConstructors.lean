/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Crypto.Computational.PRGToOneWay

/-! Public cryptographic constructors accept ordinary deterministic certificates. -/

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

-- Public constructors expose plain polynomial-time certificates from both direct inversion
-- bounds and PRG length-doubling reductions.
example {f generator : List Bool → List Bool} {length : ℕ → ℕ}
    (hf : ComputableInPolyTime f encBits encBits)
    (hnegligible : ∀ adversary : Inverter, IsPPT encBits adversary →
      Negligible (fun n => Game.succProbability (ProbComp.eval (inversionGame f adversary n))))
    (hgenerator : PseudorandomGenerator generator length) (hdouble : ∀ n, 2 * n ≤ length n) :
    ComputableInPolyTime f encBits encBits ∧
    ComputableInPolyTime generator encBits encBits :=
  ⟨(OneWay.of_inversion_negligible hf hnegligible).polyTime,
   (hgenerator.oneWay hdouble).polyTime⟩

-- Both the unary parameter and arbitrary sample word are part of the certified input.
example {X Y : ℕ → PMF (List Bool)} (h : ComputationallyIndistinguishable X Y) :
    ComputationallyIndistinguishable (fun n => (X n).map (fun word => word.take n))
      (fun n => (Y n).map (fun word => word.take n)) :=
  h.map (by polytime)
