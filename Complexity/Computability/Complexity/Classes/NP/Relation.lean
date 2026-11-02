/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP

/-!
# NP relations

An NP relation is a search problem whose solutions are checked in polynomial time: Goldreich's
class `PC` [Goldreich, Definition 2.3][Goldreich2008]. Here it is presented, like `NP` itself
(`Cslib.Complexity.NP`), by a certificate-length polynomial `p` and a verifier `V` computable in
polynomial time: `w` is a witness for `a` when `w` has length exactly `p (enc a).length` and
`V (a, w)` holds (`Cslib.Complexity.NPRelation.IsWitness`). Exact certificate lengths are the
convention of `Cslib.Complexity.IsVerifier`; Goldreich only bounds the length of a solution.

An NP relation is a problem in `NP` together with a chosen verifier: its language, the instances
that have a witness, satisfies `IsVerifier` by definition
(`Cslib.Complexity.NPRelation.isVerifier_language`), and every problem in `NP` is the language of
some NP relation (`Cslib.Complexity.mem_NP_iff_exists_npRelation`). Witness-preserving (Levin)
reductions are defined between NP relations in
`Complexity.Computability.Complexity.Reduction.Levin`.

## Main definitions

* `Cslib.Complexity.NPRelation`: a certificate-length polynomial and a polynomial-time verifier.
* `Cslib.Complexity.NPRelation.IsWitness`: the relation the verifier defines.
* `Cslib.Complexity.NPRelation.language`: the instances that have a witness.

## Main results

* `Cslib.Complexity.NPRelation.isVerifier_language`: the verifier verifies the language.
* `Cslib.Complexity.NPRelation.language_mem_NP`: the language is in `NP`.
* `Cslib.Complexity.mem_NP_iff_exists_npRelation`: the problems in `NP` are exactly the languages
  of NP relations.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008]; numbering of
  the author's online draft of 30 December 2006.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type}

/-- An **NP relation** over instances encoded by `enc`: a polynomial giving the length of
certificates as a function of the length of the encoded instance, and a verifier computable in
polynomial time on encoded instance–certificate pairs. This is Goldreich's class `PC`
[Goldreich, Definition 2.3][Goldreich2008] with certificates of exactly the prescribed length. -/
structure NPRelation (enc : α ↪ List Bool) where
  /-- The length of certificates, as a polynomial in the length of the encoded instance. -/
  certLength : Polynomial ℕ
  /-- The verifier, on an instance and a certificate. -/
  verifier : α × List Bool → Bool
  /-- The verifier is computable in polynomial time. -/
  computableInPolyTime_verifier : ComputableInPolyTime verifier (encPair enc encBits) encBool

namespace NPRelation

variable {enc : α ↪ List Bool} (R : NPRelation enc)

/-- `w` is a witness for `a`: it has the prescribed length and the verifier accepts it. -/
@[expose]
def IsWitness (a : α) (w : List Bool) : Prop :=
  w.length = R.certLength.eval (enc a).length ∧ R.verifier (a, w) = true

instance (a : α) (w : List Bool) : Decidable (R.IsWitness a w) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem isWitness_iff {a : α} {w : List Bool} :
    R.IsWitness a w ↔ w.length = R.certLength.eval (enc a).length ∧ R.verifier (a, w) = true :=
  Iff.rfl

theorem IsWitness.length_eq {R : NPRelation enc} {a : α} {w : List Bool} (h : R.IsWitness a w) :
    w.length = R.certLength.eval (enc a).length :=
  h.1

theorem IsWitness.verifier_eq_true {R : NPRelation enc} {a : α} {w : List Bool}
    (h : R.IsWitness a w) : R.verifier (a, w) = true :=
  h.2

/-- The language of an NP relation: the instances that have a witness. -/
@[expose]
def language : Set α := {a | ∃ w, R.IsWitness a w}

theorem mem_language {a : α} : a ∈ R.language ↔ ∃ w, R.IsWitness a w := Iff.rfl

/-- The verifier of an NP relation verifies its language. -/
theorem isVerifier_language : IsVerifier enc R.certLength R.verifier R.language := fun _ =>
  Iff.rfl

/-- If the verifier of an NP relation verifies `A`, then `A` is its language. -/
theorem language_eq_of_isVerifier {A : Set α}
    (h : IsVerifier enc R.certLength R.verifier A) : R.language = A :=
  Set.ext fun a => (h a).symm

/-- The language of an NP relation is in `NP`. -/
theorem language_mem_NP : R.language ∈ NP enc :=
  ⟨R.certLength, R.verifier, R.computableInPolyTime_verifier, R.isVerifier_language⟩

end NPRelation

/-- The problems in `NP` are exactly the languages of NP relations. -/
theorem mem_NP_iff_exists_npRelation {enc : α ↪ List Bool} {A : Set α} :
    A ∈ NP enc ↔ ∃ R : NPRelation enc, R.language = A :=
  ⟨fun ⟨p, V, hV, hA⟩ => ⟨⟨p, V, hV⟩, NPRelation.language_eq_of_isVerifier _ hA⟩,
    fun ⟨R, hR⟩ => hR ▸ R.language_mem_NP⟩

end Cslib.Complexity
