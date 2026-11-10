/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.Reduction.Isomorphism.SchroederBernstein
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Paddable languages

A language `A` is *paddable* when arbitrary bit strings `y` can be appended to an instance `a` by a
polynomial-time map `pad a y` that preserves membership in `A` and from which `y` can be recovered
in polynomial time [Berman and Hartmanis][BermanHartmanis1975]. Paddability turns any
polynomial-time many-one reduction into a one-one, length-increasing reduction with a
polynomial-time left inverse: pad the reduct with a self-delimiting copy of the original instance,
followed by enough filler to exceed its length. Together with the polynomial-time
Cantor–Schröder–Bernstein theorem
(`Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeIsomorphic`), this
shows that paddable languages that are many-one interreducible are polynomial-time isomorphic, and
in particular that any two paddable `NP`-complete languages are.

The library's languages are sets of typed instances with injective encodings, rather than sets of
strings. Inverting the padded reduction must decode a bit string back into an instance of the
source type, so the reduction theorems assume a total polynomial-time `Decoder` for the source
encoding. Every standard encoding built from bits, naturals, pairs, options and lists has one.

## Source and adaptations

The source version is the 1975 Cornell technical report
[Berman and Hartmanis][BermanHartmanis1975]. Locators in this file refer to that report; the
numbering of the 1977 journal version [Berman and Hartmanis][BermanHartmanis1977] has not been
checked. The padding lemma below corresponds to Lemmas 3 and 5 (printed pp. 10–12), which give
length growth and the two-argument padding and read-back condition, and the isomorphism results
combine them with §III, Theorem 1 (printed pp. 7–10), formalized in
`Cslib.Complexity.PolyTimeInvertibleLengthIncreasingOneOneReducible.polyTimeIsomorphic`.

The report pads strings. Here `pad : α → List Bool → α` acts on typed instances, the read-back
`unpad : α → List Bool` is total, and only `unpad (pad a y) = y` is required of it. The padded
reduction is given a total left inverse rather than the report's partial inverse on its range; as
in the Schröder–Bernstein module, the forward-image test recovers that range. The padding carries
an encoding of the source instance. Over strings that encoding is the instance itself, while here
it must be decoded back into a typed instance, which is what the `Decoder` hypothesis supplies.
For bit-string sources (`encBits`, with `Turing.MultiTapeTM.Decoder.bits`) the hypothesis is met,
and `Cslib.Complexity.Paddable.polyTimeIsomorphic_preimage_decode` shows that a paddable typed
language is `≅ᵖ` to its language of words.

## Main definitions

* `Cslib.Complexity.Paddable`: polynomial-time paddability of a language under an encoding.

## Main results

* `Cslib.Complexity.Paddable.polyTimeInvertibleLengthIncreasingOneOneReducible`: a many-one
  reduction into a paddable language upgrades to `≤₁,ᵢₗ`.
* `Cslib.Complexity.Paddable.polyTimeIsomorphic`: interreducible paddable languages are
  `≅ᵖ`.
* `Cslib.Complexity.NPComplete.polyTimeIsomorphic_of_paddable`: two paddable `NP`-complete
  languages are `≅ᵖ`.
* `Cslib.Complexity.PolyTimeIsomorphic.paddable_iff`: paddability is invariant under `≅ᵖ`.
* `Cslib.Complexity.NPComplete.polyTimeIsomorphic_iff_paddable`: for a paddable `NP`-complete
  `B`, an `NP`-complete language is `≅ᵖ` to `B` exactly when it is paddable.
* `Cslib.Complexity.Paddable.infinite`: a nonempty paddable language is infinite.
* `Cslib.Complexity.Paddable.compl`: paddability passes to the complement.
* `Cslib.Complexity.Paddable.preimage_decode`, `Cslib.Complexity.NPComplete.preimage_decode`:
  reading words through a total decoder preserves paddability and `NP`-completeness.
* `Cslib.Complexity.Paddable.polyTimeIsomorphic_preimage_decode`: a paddable typed language is
  `≅ᵖ` to its language of words.

## References

* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1975], Cornell TR75-260 (1975), §III, Theorem 1 and Lemmas 3 and 5
* [L. Berman, J. Hartmanis, *On isomorphisms and density of NP and other complete
  sets*][BermanHartmanis1977], journal version (numbering not checked)
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {A : Set α} {B : Set β}

/-- A language `A` is *paddable* under the encoding `encA` when there are a polynomial-time padding
function `pad : α → List Bool → α` and a polynomial-time decoding function
`unpad : α → List Bool` with `unpad (pad a y) = y` and `pad a y ∈ A ↔ a ∈ A`. This is the
typed form of the two-argument padding and read-back condition of
[Berman and Hartmanis][BermanHartmanis1975], Lemmas 3 and 5. Recovering the padding makes `pad a`
injective; nothing is required of `unpad` off the range of `pad`. -/
@[expose] def Paddable (encA : α ↪ List Bool) (A : Set α) : Prop :=
  ∃ pad : α → List Bool → α, ∃ unpad : α → List Bool,
    ComputableInPolyTime (fun p : α × List Bool => pad p.1 p.2) (encPair encA encBits) encA ∧
    ComputableInPolyTime unpad encA encBits ∧
    (∀ a y, unpad (pad a y) = y) ∧
    ∀ a y, pad a y ∈ A ↔ a ∈ A

namespace Paddable

/-- Paddability of `A` is paddability of its complement: the same functions work. -/
theorem compl (h : Paddable encA A) : Paddable encA Aᶜ := by
  obtain ⟨pad, unpad, hpad, hunpad, hdec, hmem⟩ := h
  exact ⟨pad, unpad, hpad, hunpad, hdec, fun a y => not_congr (hmem a y)⟩

/-- A nonempty paddable language is infinite: padding a member is injective in the padding. -/
theorem infinite (h : Paddable encA A) (hA : A.Nonempty) : A.Infinite := by
  obtain ⟨pad, unpad, -, -, hdec, hmem⟩ := h
  obtain ⟨a, ha⟩ := hA
  refine Set.infinite_of_injective_forall_mem (f := pad a) (fun y y' hy => ?_)
    fun y => (hmem a y).2 ha
  rw [← hdec a y, hy, hdec a y']

/-- **Padding lemma** ([Berman and Hartmanis][BermanHartmanis1975], Lemmas 3 and 5). A
polynomial-time many-one reduction from `B` to a paddable language `A` upgrades to a
length-increasing one-one reduction with a polynomial-time left inverse, given a total
polynomial-time decoder for the instances of `B`. The decoder hypothesis is the typed-model
addition described in the module docstring.

The new reduction pads `r b` with the framed encoding of `b`, followed by more filler than any
polynomial bound on the decoded padding allows from an encoding no longer than `encB b`. -/
theorem polyTimeInvertibleLengthIncreasingOneOneReducible (hA : Paddable encA A)
    (D : Decoder encB) (h : PolyTimeReducible encB encA B A) :
    PolyTimeInvertibleLengthIncreasingOneOneReducible encB encA B A := by
  obtain ⟨pad, unpad, hpad, hunpad, hdec, hmem⟩ := hA
  obtain ⟨r, hr, hrBA⟩ := h
  obtain ⟨c, d, hcd⟩ := hunpad.polyBounded_length.exists_le
  let k : β → ℕ := fun b => c * ((encB b).length + 1) ^ d
  let w : β → List Bool := fun b => frame (encB b) ++ List.replicate (k b) true
  have hk : ComputableInPolyTime k encB encUnary := by
    have hlen : ComputableInPolyTime (fun b => (encB b).length + 1) encB encUnary :=
      ComputableInPolyTime.unary_add' (ComputableInPolyTime.encoding_length encB)
        (ComputableInPolyTime.const 1)
    exact ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
      ((ComputableInPolyTime.unary_pow d).comp hlen)
  have hw : ComputableInPolyTime w encB encBits := by
    have hframe : ComputableInPolyTime (fun b => frame (encB b)) encB encBits :=
      ComputableInPolyTime.frame.comp
        (ComputableInPolyTime.id'.of_enc_eq (g := fun b => encB b) fun _ => rfl)
    have hrep : ComputableInPolyTime (fun b => List.replicate (k b) true) encB encBits :=
      hk.of_enc_eq fun _ => rfl
    exact ComputableInPolyTime.bitsAppend hframe hrep
  refine ⟨fun b => pad (r b) (w b), ⟨fun a => D.decode (unframe (unpad a)), ?_, ?_, ?_, ?_⟩,
    fun b => (hrBA b).trans (hmem (r b) (w b)).symm⟩
  · exact hpad.comp (hr.prod hw)
  · exact D.computableInPolyTime.comp (ComputableInPolyTime.unframe.comp hunpad)
  · intro b
    simp only [hdec, w, unframe_frame_append, D.decode_enc]
  · intro b
    refine Nat.lt_of_not_le fun hle => ?_
    change (encA (pad (r b) (w b))).length ≤ (encB b).length at hle
    have h1 : (w b).length ≤ c * ((encA (pad (r b) (w b))).length + 1) ^ d := by
      have := hcd (pad (r b) (w b))
      rwa [hdec] at this
    have h2 : (w b).length = 2 * (encB b).length + 1 + k b := by
      simp only [w, List.length_append, length_frame, List.length_replicate]
    have h3 : c * ((encA (pad (r b) (w b))).length + 1) ^ d ≤ k b :=
      Nat.mul_le_mul_left c (Nat.pow_le_pow_left (by omega) d)
    omega

/-- **Berman–Hartmanis, paddable form.** Two paddable languages that are polynomial-time many-one
interreducible are polynomial-time isomorphic, given total polynomial-time decoders for both
instance encodings: [Berman and Hartmanis][BermanHartmanis1975], §III, Theorem 1 combined with
Lemmas 3 and 5. -/
theorem polyTimeIsomorphic (hA : Paddable encA A) (hB : Paddable encB B) (DA : Decoder encA)
    (DB : Decoder encB) (hAB : PolyTimeReducible encA encB A B)
    (hBA : PolyTimeReducible encB encA B A) : PolyTimeIsomorphic encA encB A B :=
  (hB.polyTimeInvertibleLengthIncreasingOneOneReducible DA hAB).polyTimeIsomorphic
    (hA.polyTimeInvertibleLengthIncreasingOneOneReducible DB hBA)

end Paddable

/-- Paddability transfers along polynomial-time isomorphisms: conjugate the padding function. -/
theorem PolyTimeIsomorphic.paddable (h : PolyTimeIsomorphic encA encB A B)
    (hB : Paddable encB B) : Paddable encA A := by
  obtain ⟨e, ⟨he, hsymm⟩, hAB⟩ := h
  obtain ⟨pad, unpad, hpad, hunpad, hdec, hmem⟩ := hB
  refine ⟨fun a y => e.symm (pad (e a) y), fun a => unpad (e a), ?_, hunpad.comp he, ?_, ?_⟩
  · exact hsymm.comp (hpad.comp ((he.comp (ComputableInPolyTime.fst encA encBits)).prod
      (ComputableInPolyTime.snd encA encBits)))
  · intro a y
    simp only [Equiv.apply_symm_apply, hdec]
  · intro a y
    rw [hAB, Equiv.apply_symm_apply, hmem, hAB]

/-- Paddability is invariant under polynomial-time isomorphism. -/
theorem PolyTimeIsomorphic.paddable_iff (h : PolyTimeIsomorphic encA encB A B) :
    Paddable encA A ↔ Paddable encB B :=
  ⟨h.symm.paddable, h.paddable⟩

/-- **Paddable `NP`-complete languages are polynomial-time isomorphic**
([Berman and Hartmanis][BermanHartmanis1975], §III, Theorem 1 combined with Lemmas 3 and 5), for
instance types with total polynomial-time decoders. -/
theorem NPComplete.polyTimeIsomorphic_of_paddable (hA : NPComplete encA A)
    (hB : NPComplete encB B) (hpA : Paddable encA A) (hpB : Paddable encB B) (DA : Decoder encA)
    (DB : Decoder encB) : PolyTimeIsomorphic encA encB A B :=
  hpA.polyTimeIsomorphic hpB DA DB (hB.2 encA A hA.1) (hA.2 encB B hB.1)

/-- For a paddable `NP`-complete language `B`, an `NP`-complete language is polynomial-time
isomorphic to `B` exactly when it is paddable. The reverse direction is
`NPComplete.polyTimeIsomorphic_of_paddable` ([Berman and Hartmanis][BermanHartmanis1975], §III,
Theorem 1 combined with Lemmas 3 and 5); the forward direction, transport of paddability along
`≅ᵖ`, is derived here. With `B = SAT`, the Berman–Hartmanis conjecture says that every
`NP`-complete language is paddable. -/
theorem NPComplete.polyTimeIsomorphic_iff_paddable (hA : NPComplete encA A)
    (hB : NPComplete encB B) (hpB : Paddable encB B) (DA : Decoder encA) (DB : Decoder encB) :
    PolyTimeIsomorphic encA encB A B ↔ Paddable encA A :=
  ⟨fun h => h.paddable hpB, fun hpA => hA.polyTimeIsomorphic_of_paddable hB hpA hpB DA DB⟩

/-! ### Words read through a decoder -/

/-- The decoder reduces the word language to `A`. -/
private theorem polyTimeReducible_preimage_decode (D : Decoder encA) :
    PolyTimeReducible encBits encA (D.decode ⁻¹' A) A :=
  ⟨D.decode, D.computableInPolyTime, fun _ => Iff.rfl⟩

/-- The encoding reduces `A` to the word language. -/
private theorem polyTimeReducible_to_preimage_decode (D : Decoder encA) :
    PolyTimeReducible encA encBits A (D.decode ⁻¹' A) :=
  ⟨fun a => encA a, ComputableInPolyTime.id'.of_enc_eq fun _ => rfl, fun a => by
    simp only [Set.mem_preimage, D.decode_enc]⟩

/-- Reading every word through a total decoder preserves paddability: pad the decoded instance
and re-encode it. -/
theorem Paddable.preimage_decode (hA : Paddable encA A) (D : Decoder encA) :
    Paddable encBits (D.decode ⁻¹' A) := by
  obtain ⟨pad, unpad, hpad, hunpad, hdec, hmem⟩ := hA
  have henc : ComputableInPolyTime (fun a => encA a) encA encBits :=
    ComputableInPolyTime.id'.of_enc_eq fun _ => rfl
  refine ⟨fun w y => encA (pad (D.decode w) y), fun w => unpad (D.decode w), ?_,
    hunpad.comp D.computableInPolyTime, ?_, ?_⟩
  · exact henc.comp (hpad.comp ((D.computableInPolyTime.comp
      (ComputableInPolyTime.fst encBits encBits)).prod (ComputableInPolyTime.snd encBits encBits)))
  · intro w y
    simp only [D.decode_enc, hdec]
  · intro w y
    simp only [Set.mem_preimage, D.decode_enc, hmem]

/-- A paddable language of typed instances is polynomial-time isomorphic to the language of the
words that decode into it. So, for paddable languages, the typed instance model and the string
model agree up to `≅ᵖ`. -/
theorem Paddable.polyTimeIsomorphic_preimage_decode (hA : Paddable encA A) (D : Decoder encA) :
    PolyTimeIsomorphic encA encBits A (D.decode ⁻¹' A) :=
  hA.polyTimeIsomorphic (hA.preimage_decode D) D .bits (polyTimeReducible_to_preimage_decode D)
    (polyTimeReducible_preimage_decode D)

/-- Reading every word through a total decoder preserves `NP`-completeness: the decoder reduces the
word language to `A`, and the encoding reduces `A` back to it. -/
theorem NPComplete.preimage_decode (hA : NPComplete encA A) (D : Decoder encA) :
    NPComplete encBits (D.decode ⁻¹' A) :=
  ⟨(polyTimeReducible_preimage_decode D).mem_NP hA.1,
    hA.2.trans (polyTimeReducible_to_preimage_decode D)⟩

end Cslib.Complexity
