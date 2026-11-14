/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Falcon.Verification
public import CslibFrontier.Crypto.Primitives.ByteString

/-!
# Falcon v1.2 encoded verification frontend

This module formalizes the byte-level frontend used by the NIST API of the NIST-selected Falcon
Round 3 submission, version 1.2 ([Falcon2020], Sections 3.7, 3.10 and 3.11). It parses the
two-byte big-endian signature length, 40-byte salt, message and nonce-less signature; decodes the
canonical compressed second signature polynomial; maps a supplied SHAKE-256 output prefix to a
ring point by Algorithm 3's big-endian rejection rule; and then calls the algebraic verifier in
`Cslib.Crypto.Falcon.verify`.

The pinned dependencies do not contain a SHAKE-256 implementation. Accordingly,
`verifyNistWithXof` takes a function supplying an output prefix and passes it exactly the parsed
`salt ++ message`. This exposes the interoperability boundary but does not implement or assume
the cryptographic properties of SHAKE-256. The module is sourced to Falcon v1.2 and does not
claim agreement with the still-developing FN-DSA / FIPS 206 standard.

## Main definitions

* `Cslib.Crypto.Falcon.ByteString`: bytes represented as values in `Fin 256`.
* `Cslib.Crypto.Falcon.decompressCoefficients`, `Cslib.Crypto.Falcon.decompress`: canonical
  compressed-polynomial decoding for the variable-length NIST signature.
* `Cslib.Crypto.Falcon.NistSignedMessage`,
  `Cslib.Crypto.Falcon.parseNistSignedMessage`: the NIST signed-message layout and parser.
* `Cslib.Crypto.Falcon.hashToPointCoefficients`,
  `Cslib.Crypto.Falcon.hashToPointPrefix`: Algorithm 3 applied to a finite XOF output prefix.
* `Cslib.Crypto.Falcon.verifyNistWithXof`: the encoded frontend connected to the algebraic
  verifier.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-Based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Algorithms 3, 16 and 18 and Section 3.11.6.
-/

public section

namespace Cslib.Crypto.Falcon

/-- A byte string, with each byte intrinsically restricted to the range `0,...,255`. -/
abbrev ByteString := List Cslib.Crypto.Byte

/-- Decode exactly `n` compressed Falcon coefficients from a byte string.

This is [Falcon2020], Algorithm 18, specialized to the variable-length NIST signature from
Section 3.11.6 and the submission's reference `comp_decode`: the sign and seven low magnitude
bits precede a unary high part, magnitudes above `2047` and negative zero are rejected, all unused
bits in the last byte must be zero, and a redundant whole zero byte is rejected. -/
@[expose] def decompressCoefficients (n : ℕ) (encoded : ByteString) : Option (List ℤ) := do
  let bitsToNat (bits : List Bool) : ℕ :=
    bits.foldl (fun acc b => 2 * acc + b.toNat) 0
  /- Decode the unary high magnitude, allowing at most fifteen zero bits. -/
  let rec decodeHigh : ℕ → List Bool → Option (ℕ × List Bool)
    | _, [] => none
    | _, true :: rest => some (0, rest)
    | 0, false :: _ => none
    | maxZeros + 1, false :: rest => do
        let (k, tail) ← decodeHigh maxZeros rest
        return (k + 1, tail)
  let decodeCoefficient (bits : List Bool) : Option (ℤ × List Bool) := do
    if bits.length < 8 then
      none
    else
      let sign := bits.headD false
      let low := bitsToNat ((bits.take 8).drop 1)
      let (high, tail) ← decodeHigh 15 (bits.drop 8)
      let magnitude := low + 128 * high
      if sign && magnitude = 0 then
        none
      else if sign then
        some (-(magnitude : ℤ), tail)
      else
        some ((magnitude : ℤ), tail)
  /- Decode the requested coefficient count while preserving the unused suffix. -/
  let rec decodeCoefficients : ℕ → List Bool → Option (List ℤ × List Bool)
    | 0, bits => some ([], bits)
    | count + 1, bits => do
        let (x, rest) ← decodeCoefficient bits
        let (xs, tail) ← decodeCoefficients count rest
        return (x :: xs, tail)
  let (coefficients, unused) ← decodeCoefficients n (bytesToBitsBE encoded)
  if unused.length < 8 && unused.all (fun b => !b) then
    some coefficients
  else
    none

attribute [nolint docBlame]
  decompressCoefficients.decodeHigh decompressCoefficients.decodeCoefficients

/-- Decode the compressed second signature polynomial for parameters `P`. -/
@[expose] def decompress (P : VerificationParams)
    (encoded : ByteString) : Option (IntegerPolynomial P) := do
  let coefficients ← decompressCoefficients P.n encoded
  return fun i => coefficients.getD i.val 0

/-- A successfully parsed Falcon v1.2 NIST signed message. The parser guarantees that `salt` has
40 bytes and that `second` came from the final nonce-less signature after its degree header was
checked. -/
structure NistSignedMessage (P : VerificationParams) where
  /-- The 40-byte random salt called `nonce` by the NIST API wrapper. -/
  salt : ByteString
  /-- The message bytes between the salt and the trailing signature. -/
  message : ByteString
  /-- The canonically decompressed second signature polynomial. -/
  second : IntegerPolynomial P

/-- The exact input injected into SHAKE-256 by Falcon verification: the 40-byte salt followed by
the message. -/
@[expose] def NistSignedMessage.hashInput {P : VerificationParams}
    (signed : NistSignedMessage P) : ByteString :=
  signed.salt ++ signed.message

/-- Parse [Falcon2020], Section 3.11.6's NIST API signed-message aggregate.

The first two bytes give the trailing signature length in big-endian order. They are followed by
the 40-byte salt, the message, and a signature whose header is `0010nnnn`; the low nibble is
accepted exactly when `P.n = 2^nnnn`. The remaining signature bytes are decoded canonically by
`decompress`. -/
@[expose] def parseNistSignedMessage (P : VerificationParams)
    (signedMessage : ByteString) : Option (NistSignedMessage P) :=
  match signedMessage with
  | lengthHigh :: lengthLow :: rest =>
      if rest.length < 40 then
        none
      else
        let signatureLength := 256 * lengthHigh.val + lengthLow.val
        let afterSalt := rest.drop 40
        if afterSalt.length < signatureLength then
          none
        else
          let messageLength := afterSalt.length - signatureLength
          let signature := afterSalt.drop messageLength
          match signature with
          | [] => none
          | header :: encoded =>
              if 33 ≤ header.val && header.val ≤ 42 &&
                  2 ^ (header.val - 32) = P.n then
                match decompress P encoded with
                | none => none
                | some second => some {
                    salt := rest.take 40
                    message := afterSalt.take messageLength
                    second := second
                  }
              else
                none
  | _ => none

/-- Apply [Falcon2020], Algorithm 3's rejection rule to a finite SHAKE-256 output prefix.

Success returns the first `n` accepted coefficients. Each consecutive byte pair is interpreted
big-endian as `t`; values below `⌊2^16 / q⌋ q` contribute `t mod q` and the others are discarded.
The result is `none` when `q` is outside the source range, `n = 0`, or the prefix has too few
accepted pairs. -/
@[expose] def hashToPointCoefficients (q n : ℕ) (xofOutput : ByteString) : Option (List ℕ) :=
  /- Parse consecutive byte pairs as big-endian 16-bit words. -/
  let rec xofWords : ByteString → List ℕ
    | high :: low :: rest => (256 * high.val + low.val) :: xofWords rest
    | _ => []
  if 0 < q && q ≤ 2 ^ 16 && 0 < n then
    let threshold := (2 ^ 16 / q) * q
    let accepted := (xofWords xofOutput).filter (fun t => t < threshold) |>.map (· % q)
    if n ≤ accepted.length then some (accepted.take n) else none
  else
    none

attribute [nolint docBlame] hashToPointCoefficients.xofWords

/-- Interpret enough accepted coefficients from a finite XOF output prefix as the Falcon hash
point in `ℤ_q[x]/(x^n + 1)`. -/
@[expose] def hashToPointPrefix (P : VerificationParams)
    (xofOutput : ByteString) : Option (Polynomial P) := do
  let coefficients ← hashToPointCoefficients P.q P.n xofOutput
  return Negacyclic.ofCoeffs fun i => coefficients.getD i.val 0

/-- Run the Falcon v1.2 NIST encoded verification frontend with an explicit XOF-prefix supplier.

On a successfully parsed aggregate, `xof` is called on exactly `salt ++ message`; its output is
processed by Algorithm 3 and the result and decoded `s₂` are passed to `verify`. Malformed input
or an insufficient XOF prefix is rejected. Instantiating `xof` with a correct SHAKE-256
implementation is a separate obligation. -/
@[expose] def verifyNistWithXof (P : VerificationParams) (xof : ByteString → ByteString)
    (h : Polynomial P) (signedMessage : ByteString) : Bool :=
  match parseNistSignedMessage P signedMessage with
  | none => false
  | some signed =>
      match hashToPointPrefix P (xof signed.hashInput) with
      | none => false
      | some c => verify P h c signed.second

end Cslib.Crypto.Falcon
