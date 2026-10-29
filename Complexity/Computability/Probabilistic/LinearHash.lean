/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Languages.Probabilistic.LinearHash
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Primitives
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Tactic.PPT

/-!
# Polynomial-time binary linear hashing

Matrix hashing uses the shared row parser and Boolean folds. Both certificates allow computed
input and output lengths, arbitrary input encodings, and short matrix seeds padded with zero.
The full extractor charges sampling, hashing and copying its complete public seed and digest.

## Main results

* `Cslib.BitString.LinearHash.computableInPolyTime_wordHash`: deterministic hashing.
* `Cslib.BitString.LinearHash.isPPTOn_extract`: the complete seeded sampler.

## References

Adapted from Computability/Probabilistic/LinearHash.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the tidy machine calculus.
-/

@[expose] public section

namespace Cslib.BitString.LinearHash

open Probability Turing.MultiTapeTM

/-- Hash efficiently available words, with all dimensions computed in unary. -/
@[local fun_prop]
private theorem computableTidilyInPolyTime_wordHash {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {seed input : α → List Bool}
    (hcount : ComputableTidilyInPolyTime count encode encUnary)
    (hseed : ComputableTidilyInPolyTime seed encode encBits)
    (hinput : ComputableTidilyInPolyTime input encode encBits) :
    ComputableTidilyInPolyTime (fun a => wordHash (count a) (seed a) (input a))
      encode encBits := by
  unfold wordHash
  fun_prop

/-- Hash plain polynomial-time words, retaining unary output dimensions and the full input. -/
@[fun_prop]
theorem computableInPolyTime_wordHash {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {seed input : α → List Bool}
    (hcount : ComputableInPolyTime count encode encUnary)
    (hseed : ComputableInPolyTime seed encode encBits)
    (hinput : ComputableInPolyTime input encode encBits) :
    ComputableInPolyTime (fun a => wordHash (count a) (seed a) (input a))
      encode encBits :=
  .of_tidy (computableTidilyInPolyTime_wordHash hcount.tidy hseed.tidy hinput.tidy)

/-- The complete extractor is uniformly strict PPT, including the revealed matrix seed. -/
@[program_certificate]
theorem isPPTOn_extract {α : Type} {encode : α ↪ List Bool}
    {count : α → ℕ} {input : α → List Bool}
    (hcount : ComputableInPolyTime count encode encUnary)
    (hinput : ComputableInPolyTime input encode encBits) :
    IsPPTOn encode encBits (fun a => extract (count a) (input a)) := by
  have hcount := hcount.tidy
  have hinput := hinput.tidy
  have hwidth := ComputableTidilyInPolyTime.unary_mul.comp
    (hcount.prod (ComputableTidilyInPolyTime.length_bits.comp hinput))
  have hsample := ComputableInPolyTime.sampleList (.of_tidy hwidth)
  have hc := (ComputableInPolyTime.of_tidy hcount).comp
    (ComputableInPolyTime.fst encode encBits)
  have hi := (ComputableInPolyTime.of_tidy hinput).comp
    (ComputableInPolyTime.fst encode encBits)
  have hs := ComputableInPolyTime.snd encode encBits
  have hcallback := ComputableInPolyTime.bitsAppend hs
    (computableInPolyTime_wordHash hc hs hi)
  simpa only [extract, bind_pure_comp, Function.comp_def] using hsample.map_with hcallback

end Cslib.BitString.LinearHash
