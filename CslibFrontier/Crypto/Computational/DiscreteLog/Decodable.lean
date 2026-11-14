/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiscreteLog
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Decodable prime-order group families

A `DecodablePrimeOrderGroupFamily` extends `PrimeOrderGroupFamily` with a canonical decoder
`decode : ∀ d, List Bool → Option (Carrier d)` whose domain indicator `(decode d w).isSome` is
computable in polynomial time (`computableInPolyTime_isElem`) and which inverts `encode d` on both
sides (`decode_encode` and `encode_eq_of_decode_eq_some`).

Because `encode d` is injective and `decode d` accepts only canonical encodings, the Boolean
membership test `isElem (d, w) := (decode d w).isSome` characterizes `Set.range (encode d)`, and
the encoded partial inverse `(decode d w).map (encode d)` equals `if isElem (d, w) then some w else
none`, so it is also computable in polynomial time (`computableInPolyTime_decode_map_encode`).

## Main definitions

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily`: a `PrimeOrderGroupFamily` equipped with a
  canonical decoder and a polynomial-time group-element membership test.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.isElem`: Boolean group-element membership test on
  `(d, w)`.

## Main results

* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.decode_eq_some_iff`: `decode d w = some x ↔ w =
  encode d x`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.isElem_eq_true_iff`: `isElem (d, w) = true ↔ w ∈
  Set.range (encode d)`.
* `Cslib.Crypto.DecodablePrimeOrderGroupFamily.computableInPolyTime_decode_map_encode`: the
  encoded partial decoder `(d, w) ↦ (decode d w).map (encode d)` is computable in polynomial time.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- A prime-order group family equipped with a canonical decoder whose domain membership test is
computable in polynomial time. -/
structure DecodablePrimeOrderGroupFamily extends PrimeOrderGroupFamily where
  /-- Decode a bit string as an element of `Carrier d`, returning `none` if the word is not the
  canonical encoding of any group element. -/
  decode : ∀ d : Desc, List Bool → Option (Carrier d)
  /-- Decoding the encoding of any group element recovers that element. -/
  decode_encode : ∀ (d : Desc) (x : Carrier d), decode d (encode d x) = some x
  /-- `decode` rejects non-canonical encodings. -/
  encode_eq_of_decode_eq_some :
    ∀ {d : Desc} {w : List Bool} {x : Carrier d}, decode d w = some x → w = encode d x
  /-- Testing whether a word represents a group element in `Carrier d` is computable in
  polynomial time. -/
  computableInPolyTime_isElem :
    ComputableInPolyTime (fun p : Desc × List Bool => (decode p.1 p.2).isSome)
      (encPair encDesc encBits) encBool

namespace DecodablePrimeOrderGroupFamily

variable (F : DecodablePrimeOrderGroupFamily)

instance (d : F.Desc) : Fact (F.order d).Prime := ⟨F.prime_order d⟩

instance (d : F.Desc) : NeZero (F.order d) := ⟨(F.prime_order d).ne_zero⟩

/-- Boolean group-element membership test on `(d, w)`: `true` iff `F.decode d w` succeeds. -/
@[expose] def isElem (p : F.Desc × List Bool) : Bool :=
  (F.decode p.1 p.2).isSome

@[simp] theorem isElem_encode (d : F.Desc) (x : F.Carrier d) :
    F.isElem (d, F.encode d x) = true := by
  simp [isElem, F.decode_encode]

/-- A word decodes to `x` if and only if it equals `F.encode d x`. -/
theorem decode_eq_some_iff {d : F.Desc} {w : List Bool} {x : F.Carrier d} :
    F.decode d w = some x ↔ w = F.encode d x :=
  ⟨F.encode_eq_of_decode_eq_some, fun h => h ▸ F.decode_encode d x⟩

/-- `F.isElem (d, w) = true` if and only if `w` is in `Set.range (F.encode d)`. -/
theorem isElem_eq_true_iff (d : F.Desc) (w : List Bool) :
    F.isElem (d, w) = true ↔ w ∈ Set.range (F.encode d) := by
  constructor
  · intro h
    cases hdec : F.decode d w with
    | none => simp [isElem, hdec] at h
    | some x => exact ⟨x, (F.encode_eq_of_decode_eq_some hdec).symm⟩
  · rintro ⟨x, rfl⟩
    exact F.isElem_encode d x

/-- `F.isElem (d, w) = false` if and only if `w ∉ Set.range (F.encode d)`. -/
theorem isElem_eq_false_iff (d : F.Desc) (w : List Bool) :
    F.isElem (d, w) = false ↔ w ∉ Set.range (F.encode d) := by
  rw [← Bool.not_eq_true, F.isElem_eq_true_iff]

/-- `F.decode d w = none` if and only if `w ∉ Set.range (F.encode d)`. -/
theorem decode_eq_none_iff {d : F.Desc} {w : List Bool} :
    F.decode d w = none ↔ w ∉ Set.range (F.encode d) := by
  rw [← F.isElem_eq_false_iff, isElem, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]

/-- Obtaining the decoded element whenever `F.isElem (d, w) = true`. -/
theorem exists_decode_eq_some_of_isElem {d : F.Desc} {w : List Bool}
    (h : F.isElem (d, w) = true) :
    ∃ x : F.Carrier d, F.decode d w = some x ∧ F.encode d x = w := by
  cases hdec : F.decode d w with
  | none => simp [isElem, hdec] at h
  | some x => exact ⟨x, rfl, (F.encode_eq_of_decode_eq_some hdec).symm⟩

/-- On words, decoding followed by re-encoding equals gating `w` on `F.isElem (d, w)`. -/
theorem map_encode_decode (d : F.Desc) (w : List Bool) :
    (F.decode d w).map (F.encode d) = if F.isElem (d, w) then some w else none := by
  cases hdec : F.decode d w with
  | none => simp [isElem, hdec]
  | some x =>
    have hw := F.encode_eq_of_decode_eq_some hdec
    subst hw
    simp [isElem, F.decode_encode]

/-- Decoding a word with fallback `z` and re-encoding equals returning `w` when `F.isElem (d, w)`
holds and `F.encode d z` otherwise. -/
theorem encode_decode_getD (d : F.Desc) (w : List Bool) (z : F.Carrier d) :
    F.encode d ((F.decode d w).getD z) = if F.isElem (d, w) then w else F.encode d z := by
  cases hdec : F.decode d w with
  | none => simp [isElem, hdec]
  | some x =>
    have hw := F.encode_eq_of_decode_eq_some hdec
    subst hw
    simp [isElem, F.decode_encode]

variable {F} in
/-- Group-element membership testing for computed group descriptions and candidate words is
computable in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_isElem_app {α : Type} {enc : α ↪ List Bool}
    {d : α → F.Desc} {w : α → List Bool} (hd : ComputableInPolyTime d enc F.encDesc)
    (hw : ComputableInPolyTime w enc encBits) :
    ComputableInPolyTime (fun a => F.isElem (d a, w a)) enc encBool :=
  (F.computableInPolyTime_isElem.comp (hd.prod hw)).of_enc_eq fun _ => rfl

/-- The encoded partial decoder `(d, w) ↦ (F.decode d w).map (F.encode d)` is computable in
polynomial time. -/
theorem computableInPolyTime_decode_map_encode :
    ComputableInPolyTime (fun p : F.Desc × List Bool => (F.decode p.1 p.2).map (F.encode p.1))
      (encPair F.encDesc encBits) (encOption encBits) := by
  have hsome : ComputableInPolyTime (fun p : F.Desc × List Bool => some p.2)
      (encPair F.encDesc encBits) (encOption encBits) :=
    (ComputableInPolyTime.optionSome encBits).comp (by fun_prop)
  have hnone : ComputableInPolyTime (fun _ : F.Desc × List Bool => (none : Option (List Bool)))
      (encPair F.encDesc encBits) (encOption encBits) := by fun_prop
  have hif := F.computableInPolyTime_isElem.ite hsome hnone
  exact hif.of_enc_eq fun p => congrArg (encOption encBits) (F.map_encode_decode p.1 p.2)

end DecodablePrimeOrderGroupFamily

end Cslib.Crypto
