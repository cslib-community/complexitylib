/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Game
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
public import Complexity.Languages.Probabilistic.BitString
public import Complexity.Probability.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Complexity.Tactic.PolyTime.Init
import Complexity.Tactic.PPT

/-!
# Padding expanding generators to a common input length

Run an expander on the required seed prefix, retain the unused input bits, and truncate the
result to one bit more than the common input length. Independent uniform padding preserves
the distinguishing advantage exactly through an efficient reduction.

This is used to give the entropy guesses in the OWF-to-PRG construction a common seed length
before amplification and XOR combination.

## Main definitions

* `generate`: pad a raw expanding function to one bit of stretch at a common input length.
* `test`: reduce a padded-output test to a test of the raw output.

## Main results

* `isPolyTime_generate`, `isPPTOn_test`: certify the construction and its security reduction.
* `ideal_distribution`: uniform raw output and independent padding give uniform output.
* `length_generate`: exactly one bit of stretch for correctly sized inputs.
* `advantage_eq`: the reduction preserves distinguishing advantage exactly.

## References

Thomas Holenstein, *Pseudorandom Generators from
One-Way Functions: A Simple Construction for Any Hardness*, TCC 2006, Section 5, final proof of
Theorem 1, [Holenstein2006].

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`.
-/

@[expose] public section

namespace Cslib.Crypto.GeneratorPadding

open Probability BitString Turing.MultiTapeTM

/-- Retain the unused uniform input bits and keep exactly one bit of stretch. -/
def generate (seedBits commonBits : ℕ) (generator : List Bool → List Bool)
    (seed : List Bool) : List Bool :=
  (generator (seed.take seedBits) ++ seed.drop seedBits).take (commonBits + 1)

/-- Padding uses only the supplied generator, word slicing, and concatenation. -/
theorem isPolyTime_generate {α : Type} {input : α ↪ List Bool}
    {seedBits commonBits : α → ℕ} {generator : α → List Bool → List Bool} {seed : α → List Bool}
    (hseedBits : ComputableInPolyTime seedBits input encUnary)
    (hcommon : ComputableInPolyTime commonBits input encUnary)
    (hgenerator : ComputableInPolyTime (fun a => generator a.1 a.2)
      (encPair input encBits) encBits)
    (hseed : ComputableInPolyTime seed input encBits) :
    ComputableInPolyTime
      (fun a => generate (seedBits a) (commonBits a) (generator a) (seed a)) input encBits := by
  have htakeSeed : ComputableInPolyTime (fun a => (seed a).take (seedBits a)) input encBits :=
    ComputableInPolyTime.bitsTakeWithInput hseed hseedBits
  have hdropSeed : ComputableInPolyTime (fun a => (seed a).drop (seedBits a)) input encBits :=
    ComputableInPolyTime.bitsDropWithInput hseed hseedBits
  have hgen : ComputableInPolyTime
      (fun a => generator a ((seed a).take (seedBits a))) input encBits :=
    hgenerator.comp (ComputableInPolyTime.id'.prod htakeSeed)
  have happ : ComputableInPolyTime
      (fun a => generator a ((seed a).take (seedBits a)) ++ (seed a).drop (seedBits a))
      input encBits :=
    ComputableInPolyTime.bitsAppend hgen hdropSeed
  have hlen : ComputableInPolyTime (fun a => commonBits a + 1) input encUnary :=
    ComputableInPolyTime.unary_succ.comp hcommon
  unfold generate
  exact ComputableInPolyTime.bitsTakeWithInput happ hlen

attribute [program_certificate] isPolyTime_generate

/-- One bit of raw expansion suffices, also when no padding is needed. -/
theorem length_generate {seedBits commonBits : ℕ} {generator : List Bool → List Bool}
    (hfits : seedBits ≤ commonBits)
    (hexpands : ∀ seed, seed.length = seedBits → seedBits < (generator seed).length)
    {seed : List Bool} (hseed : seed.length = commonBits) :
    (generate seedBits commonBits generator seed).length = commonBits + 1 := by
  have h := hexpands (seed.take seedBits) (by simpa [hseed] using Nat.min_eq_left hfits)
  simp only [generate, List.length_take, List.length_append, List.length_drop, hseed]
  exact Nat.min_eq_left (by lia)

/-- The unused suffix of a uniform padded seed is fresh independent randomness. -/
theorem generate_distribution {seedBits commonBits : ℕ} (generator : List Bool → List Bool)
    (hfits : seedBits ≤ commonBits) :
    (uniformList commonBits).map (generate seedBits commonBits generator) =
      (do
        let word ← (uniformList seedBits).map generator
        (uniformList (commonBits - seedBits)).map
          (fun padding => (word ++ padding).take (commonBits + 1))) := by
  change (uniformList commonBits).bind (fun seed => PMF.pure
    ((generator (seed.take seedBits) ++ seed.drop seedBits).take (commonBits + 1))) = _
  nth_rw 1 [show commonBits = seedBits + (commonBits - seedBits) by lia]
  rw [uniformList_bind_split seedBits (commonBits - seedBits)
    (fun front padding => PMF.pure
      ((generator front ++ padding).take (commonBits + 1)))]
  simp only [PMF.monad_bind_eq_bind, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]

/-- Uniform raw output and independent padding give exactly the desired uniform output. -/
theorem ideal_distribution {seedBits outputBits commonBits : ℕ}
    (hexpands : seedBits < outputBits) :
    (do
      let word ← uniformList outputBits
      (uniformList (commonBits - seedBits)).map
        (fun padding => (word ++ padding).take (commonBits + 1))) =
      uniformList (commonBits + 1) := by
  rw [← uniformList_take (n := outputBits + (commonBits - seedBits))
    (k := commonBits + 1) (by lia), uniformList_add, PMF.map_bind]
  simp only [PMF.monad_bind_eq_bind, PMF.map_comp, Function.comp_def]

/-- A distinguisher for padded output is an ordinary randomized postprocessing of raw output. -/
noncomputable def test (seedBits commonBits : ℕ) (adversary : List Bool → ProbComp Bool)
    (word : List Bool) : ProbComp Bool := do
  let padding ← BitString.sampleList (commonBits - seedBits)
  adversary ((word ++ padding).take (commonBits + 1))

/-- The reduction charges the padding and the call to the captured adversary. -/
@[program_certificate]
theorem isPPTOn_test {α : Type} {input : α ↪ List Bool}
    {seedBits commonBits : α → ℕ} {adversary : α → List Bool → ProbComp Bool}
    {word : α → List Bool}
    (hseedBits : ComputableInPolyTime seedBits input encUnary)
    (hcommon : ComputableInPolyTime commonBits input encUnary)
    (hadversary : IsPPTOn (encPair input encBits) encBool
      (fun a => adversary a.1 a.2))
    (hword : ComputableInPolyTime word input encBits) :
    IsPPTOn input encBool
      (fun a => test (seedBits a) (commonBits a) (adversary a) (word a)) := by
  unfold test
  ppt

/-- Padding preserves the tested distinguishing advantage exactly. -/
theorem advantage_eq {seedBits outputBits commonBits : ℕ} (generator : List Bool → List Bool)
    (adversary : List Bool → ProbComp Bool) (hfits : seedBits ≤ commonBits)
    (hexpands : seedBits < outputBits) :
    Game.advantage
      (((uniformList commonBits).map (generate seedBits commonBits generator)).bind
        (fun word => ProbComp.eval (adversary word)))
      ((uniformList (commonBits + 1)).bind (fun word => ProbComp.eval (adversary word))) =
    Game.advantage
      (((uniformList seedBits).map generator).bind
        (fun word => ProbComp.eval (test seedBits commonBits adversary word)))
      ((uniformList outputBits).bind
        (fun word => ProbComp.eval (test seedBits commonBits adversary word))) := by
  rw [generate_distribution generator hfits, ← ideal_distribution hexpands]
  simp only [PMF.monad_bind_eq_bind]
  simp only [test, ProbComp.eval_bind, BitString.eval_sampleList, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]

end Cslib.Crypto.GeneratorPadding
