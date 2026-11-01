/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.MCSP.SuccinctNP
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# A binary NP language for succinct MCSP

The verifier for `SuccinctMCSP` extends to all binary words by decoding the raw tuple of arity,
samples and threshold. This gives an `NP` language agreeing with `SuccinctMCSP` on its canonical
encodings. On other words, the language is determined by the total raw decoder and verifier;
membership does not require recognizing the canonical order of the sample list.

## Main results

* `Cslib.SuccinctMCSP.exists_language_mem_NP`: a binary `NP` language agreeing with succinct MCSP
  under its unary-threshold encoding.
-/

public section

namespace Cslib.SuccinctMCSP

open Turing.MultiTapeTM Complexity

/-- There is a binary language in `NP` agreeing with `SuccinctMCSP` on every word encoded by
`SuccinctMCSP.enc`. Its behavior on words outside the encoding's image is unrestricted. -/
theorem exists_language_mem_NP :
    ∃ L : Language Bool, (L : Set (List Bool)) ∈ NP encBits ∧
      ∀ x, x ∈ SuccinctMCSP ↔ enc x ∈ L := by
  let encIn := encPair encUnary (encList (encPair encBits encBool))
  obtain ⟨decode, hround, d, e, hcompute⟩ : Decoder (encPair encIn encUnary) :=
    .pair (.pair .unary (.list (.pair .bits .bool))) .unary
  let V : List Bool × List Bool → Bool := fun p => rawVerifier (decode p.1, p.2)
  have hconv : ComputableInPolyTime
      (fun r : (ℕ × List (List Bool × Bool)) × ℕ => (r.1, r.2))
      (encPair encIn encUnary) (encPair encIn encNat) :=
    (ComputableInPolyTime.fst _ _).prod
      (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))
  have hdecode : ComputableInPolyTime decode encBits (encPair encIn encNat) :=
    hconv.comp hcompute.computableInPolyTime
  have hV : ComputableInPolyTime V (encPair encBits encBits) encBool :=
    computableInPolyTime_rawVerifier.comp
      ((hdecode.comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.snd _ _))
  refine ⟨{w | ∃ c : List Bool,
    c.length = MCSP.certPolynomial.eval w.length ∧ V (w, c) = true},
    ⟨MCSP.certPolynomial, V, hV, fun _ => Iff.rfl⟩, fun x => ?_⟩
  change x ∈ SuccinctMCSP ↔ ∃ c : List Bool,
    c.length = MCSP.certPolynomial.eval (enc x).length ∧
      rawVerifier (decode (enc x), c) = true
  rw [enc_apply, hround]
  exact isVerifier x

end Cslib.SuccinctMCSP
