/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.LocallyDecodable.Basic
public import Complexity.Crypto.Protocols.PIR.Basic

/-!
# Private information retrieval from perfectly smooth codes

A non-adaptive `q`-query decoder for a code `C : (ι → Bool) → P → Γ` draws coins `r`, reads the
positions `Q i r k` for `k < q`, and outputs `output i r` of the symbols read
(`Code.nonadaptive`). Give each read its own server holding the codeword `C x`: the user sends the
position `Q i r k` to the server `k`, the server answers with the symbol `C x (Q i r k)`, and the
user runs the decoder's output function on the answers. This is `PIR.ofDecoder`
[Yekhanin, Lemma 6.2][Yekhanin2012].

* The user's output has the decoder's law on the codeword `C x` (`PIR.eval_run_ofDecoder`), so
  the scheme is perfectly correct exactly when the decoder decodes codewords with probability one
  (`PIR.isCorrect_ofDecoder_iff`).
* The server `k` sees the position `Q i r k`, so the scheme is perfectly private exactly when the
  law of each read does not depend on the index (`PIR.isPrivate_ofDecoder_iff`). This holds when
  the code is perfectly smooth, that is, each read is a uniform position
  (`PIR.isPrivate_ofDecoder`); the same hypothesis makes the decoder smooth in the sense of
  `Code.IsSmoothDecoder` (`Code.isSmoothDecoder_nonadaptive_of_uniform`).
* The scheme communicates `q (⌈log₂ N⌉ + ⌈log₂ |Γ|⌉)` bits for codewords of length `N = |P|`
  (`PIR.communication_ofDecoder`), the bound of the source.

The source states the lemma for a perfectly smooth locally decodable code; its proof uses only that
the decoder recovers `x i` from uncorrupted codewords, which is the hypothesis here. Decoding
corrupted words is not needed.

## Main definitions

* `Cslib.Crypto.Protocols.PIR.ofDecoder`: the scheme of a non-adaptive decoder.

## Main results

* `Cslib.Crypto.Protocols.PIR.isCorrect_ofDecoder_iff`,
  `Cslib.Crypto.Protocols.PIR.isPrivate_ofDecoder_iff`: correctness and privacy of the scheme.
* `Cslib.Crypto.Protocols.PIR.hasScheme_ofDecoder`: a perfectly smooth `q`-query decoder that
  decodes codewords exactly gives a `q`-server scheme with `q (⌈log₂ N⌉ + ⌈log₂ |Γ|⌉)` bits.

## References

* [S. Yekhanin, *Locally decodable codes*][Yekhanin2012], Section 6.1.1, Lemma 6.2; numbering of
  the author's draft of the monograph
-/

public section

namespace Cslib.Crypto.Protocols.PIR

open Code Probability

variable {ι P Γ R : Type} {q : ℕ}

/-- The `q`-server scheme of a non-adaptive `q`-query decoder for the code `C`
[Yekhanin, Lemma 6.2][Yekhanin2012]: the servers hold the codeword `C x`, the server `k` receives
the `k`-th position read by the decoder and answers with the symbol there, and the user runs the
decoder's output function on the answers. -/
def ofDecoder (C : (ι → Bool) → P → Γ) (coins : ι → ProbComp R) (Q : ι → R → Fin q → P)
    (output : ι → R → (Fin q → Γ) → Bool) : Scheme ι (Fin q) R P Γ where
  query i := (fun r => (r, Q i r)) <$> coins i
  answer _ x p := C x p
  reconstruct i r a := output i r a

variable (C : (ι → Bool) → P → Γ) (coins : ι → ProbComp R) (Q : ι → R → Fin q → P)
  (output : ι → R → (Fin q → Γ) → Bool)

/-- The user's output has the law of the decoder on the codeword. -/
theorem eval_run_ofDecoder (x : ι → Bool) (i : ι) :
    ProbComp.eval ((ofDecoder C coins Q output).run x i) =
      decodeLaw (nonadaptive (coins i) (Q i) (output i)) (C x) := by
  rw [Scheme.eval_run, decodeLaw_nonadaptive, ofDecoder, ProbComp.eval_map, PMF.map_comp]
  rfl

/-- The query of the server `k` is the `k`-th position read by the decoder. -/
theorem eval_serverQuery_ofDecoder (k : Fin q) (i : ι) :
    ProbComp.eval ((ofDecoder C coins Q output).serverQuery k i) =
      (ProbComp.eval (coins i)).map fun r => Q i r k := by
  rw [Scheme.eval_serverQuery, ofDecoder, ProbComp.eval_map, PMF.map_comp]
  rfl

/-- The scheme of a decoder is perfectly correct exactly when the decoder decodes every codeword
with probability one. -/
theorem isCorrect_ofDecoder_iff : (ofDecoder C coins Q output).IsCorrect ↔
    ∀ x i, decodeLaw (nonadaptive (coins i) (Q i) (output i)) (C x) = PMF.pure (x i) := by
  rw [Scheme.isCorrect_iff_eval_run]
  simp only [eval_run_ofDecoder]

/-- The scheme of a decoder is perfectly private exactly when the law of each position read does
not depend on the index. -/
theorem isPrivate_ofDecoder_iff : (ofDecoder C coins Q output).IsPrivate ↔
    ∀ k i i', (ProbComp.eval (coins i)).map (fun r => Q i r k) =
      (ProbComp.eval (coins i')).map fun r => Q i' r k := by
  rw [Scheme.isPrivate_iff]
  simp only [eval_serverQuery_ofDecoder]

/-- **The scheme of a perfectly smooth decoder is private** [Yekhanin, Lemma 6.2][Yekhanin2012]:
when each position read is uniform, each server receives a uniform position. -/
theorem isPrivate_ofDecoder [Fintype P] [Nonempty P]
    (huniform : ∀ i k, (ProbComp.eval (coins i)).map (fun r => Q i r k) =
      PMF.uniformOfFintype P) :
    (ofDecoder C coins Q output).IsPrivate :=
  (isPrivate_ofDecoder_iff C coins Q output).mpr fun k i i' => by
    rw [huniform i k, huniform i' k]

/-- The scheme of a `q`-query decoder for codewords of length `N` over `Γ` communicates
`q (⌈log₂ N⌉ + ⌈log₂ |Γ|⌉)` bits [Yekhanin, Lemma 6.2][Yekhanin2012]. -/
theorem communication_ofDecoder [Fintype P] [Fintype Γ] :
    communication (Fin q) P Γ =
      q * (Nat.clog 2 (Fintype.card P) + Nat.clog 2 (Fintype.card Γ)) := by
  rw [communication_eq, Fintype.card_fin]

/-- **Private information retrieval from a perfectly smooth code**
[Yekhanin, Lemma 6.2][Yekhanin2012]: a non-adaptive `q`-query decoder for a code of length `N`
over `Γ`, each of whose reads is a uniform position and which decodes every codeword with
probability one, gives a perfectly correct and perfectly private `q`-server scheme communicating
`q (⌈log₂ N⌉ + ⌈log₂ |Γ|⌉)` bits. -/
theorem hasScheme_ofDecoder [Fintype P] [Nonempty P] [Fintype Γ]
    (huniform : ∀ i k, (ProbComp.eval (coins i)).map (fun r => Q i r k) =
      PMF.uniformOfFintype P)
    (hcorrect : ∀ x i,
      decodeLaw (nonadaptive (coins i) (Q i) (output i)) (C x) = PMF.pure (x i)) :
    HasScheme ι q (q * (Nat.clog 2 (Fintype.card P) + Nat.clog 2 (Fintype.card Γ))) := by
  have h := ((isCorrect_ofDecoder_iff C coins Q output).mpr hcorrect).hasScheme
    (isPrivate_ofDecoder C coins Q output huniform)
  rwa [Fintype.card_fin, communication_ofDecoder] at h

end Cslib.Crypto.Protocols.PIR
