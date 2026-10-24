/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Interpretation.Rank

/-!
# Encoding order-free interpreted structures

An interpretation maps a well-formed structure instance to its interpreted structure, numbered
by increasing tuple-index rank. An instance `(n, tables)` with invalid table shapes maps to a
fixed malformed target instance, outside every target query language. This is a map between
parsed instances; no claim about decoding arbitrary bit strings is made.

## Main definitions

* `Cslib.Logic.FO.Interpretation.encodedMap`: the encoded interpreted structure.

## Main results

* `Cslib.Logic.FO.Interpretation.wellFormed_encodedMap_iff`: shape validity is preserved and
  reflected by the map.
* `Cslib.Logic.FO.Interpretation.mem_queryLanguage_encodedMap_iff`: target query membership is
  equivalent to validity of the source instance and membership of its interpreted structure.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
-/

@[expose] public section

universe u v u' v'

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic.FO.Interpretation

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  {ι : Type} {d : ℕ} (I : Interpretation L L' ι) (v : Vocabulary L) (v' : Vocabulary L')
  (e : ι ≃ Fin d)

/-- Encode the structure interpreted in a well-formed input, numbering its elements by ranks.
Malformed inputs map to a fixed malformed structure encoding. This includes empty structures,
empty interpreted domains, nullary relations, and interpretations of dimension zero. -/
noncomputable def encodedMap (a : EncodedStructure) : EncodedStructure :=
  if v.WellFormed a then
    letI := v.decode a
    v'.encode (I.Model (Fin a.1)) (rankEquiv I e a.1)
  else (0, List.replicate (v'.count + 1) [])

variable {a : EncodedStructure}

/-- On a well-formed input `a`, `I.encodedMap v v' e a` encodes `I.Model (Fin a.1)` along
`rankEquiv I e a.1`. -/
theorem encodedMap_of_wellFormed (ha : v.WellFormed a) :
    I.encodedMap v v' e a = (letI := v.decode a;
      v'.encode (I.Model (Fin a.1)) (rankEquiv I e a.1)) :=
  ite_eq_left ha

/-- On a malformed input `a`, `I.encodedMap v v' e a` returns the fixed malformed pair
`(0, List.replicate (v'.count + 1) [])`. -/
theorem encodedMap_of_not_wellFormed (ha : ¬ v.WellFormed a) :
    I.encodedMap v v' e a = (0, List.replicate (v'.count + 1) []) :=
  ite_eq_right ha

/-- A malformed source input `a` maps to a malformed target output `I.encodedMap v v' e a`. -/
theorem not_wellFormed_encodedMap (ha : ¬ v.WellFormed a) :
    ¬ v'.WellFormed (I.encodedMap v v' e a) := by
  rw [I.encodedMap_of_not_wellFormed v v' e ha]
  intro h
  have := h.1
  simp only [List.length_replicate] at this
  omega

/-- The encoded interpreted structure is well formed exactly when the input is. -/
@[simp]
theorem wellFormed_encodedMap_iff :
    v'.WellFormed (I.encodedMap v v' e a) ↔ v.WellFormed a := by
  by_cases ha : v.WellFormed a
  · rw [I.encodedMap_of_wellFormed v v' e ha]
    let _ := v.decode a
    exact iff_of_true (Vocabulary.wellFormed_encode _ _) ha
  · exact iff_of_false (I.not_wellFormed_encodedMap v v' e ha) ha

/-- For an isomorphism-closed target class, target query membership is exactly source validity
and membership of the interpreted structure in that class. -/
theorem mem_queryLanguage_encodedMap_iff {K' : Set (Bundled.{0} L'.Structure)}
    (hK' : IsoClosed K') :
    I.encodedMap v v' e a ∈ v'.queryLanguage K' ↔
      v.WellFormed a ∧ (letI := v.decode a;
        Bundled.of (c := L'.Structure) (I.Model (Fin a.1)) ∈ K') := by
  by_cases ha : v.WellFormed a
  · rw [I.encodedMap_of_wellFormed v v' e ha]
    let _ := v.decode a
    rw [v'.mem_queryLanguage_encode hK']
    exact (and_iff_right ha).symm
  · rw [Vocabulary.mem_queryLanguage]
    simp only [I.not_wellFormed_encodedMap v v' e ha, ha, false_and]

end Cslib.Logic.FO.Interpretation
