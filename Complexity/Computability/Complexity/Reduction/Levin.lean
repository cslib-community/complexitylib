/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.NP.Relation
public import Complexity.Computability.Complexity.Reduction

/-!
# Levin reductions

A Levin reduction of an NP relation `R` to an NP relation `S` is a polynomial-time map `f` of
instances together with two polynomial-time maps of witnesses: a forward map sending each witness
`w` for `a` to a witness for `f a`, and a backward map sending each witness for `f a` to a witness
for `a`. This is the augmented Karp reduction of [Goldreich, Exercise 2.28][Goldreich2008], which
Goldreich notes is the definition Levin used [Levin1973] (Levin's witness maps read only the
witness). Goldreich's Definition 2.12 keeps only the instance map and the backward map; the
forward map is what lets an honest prover for `S` run on the witnesses of `R`, as in
zero-knowledge proofs for all of `NP`.

Both witness maps read the instance as well as the witness. A Levin reduction is in particular a
polynomial-time many-one reduction between the languages
(`Cslib.Complexity.LevinReduction.toPolyTimeReducible`). Levin reductions compose
(`Cslib.Complexity.LevinReduction.trans`), and an NP relation is `LevinHard` when every NP
relation, over any encoded instance type, Levin-reduces to it; its language is then `NP`-hard
(`Cslib.Complexity.LevinHard.npHard`). This is Goldreich's `PC`-hardness (the
remark following [Goldreich, Definition 2.18][Goldreich2008]) for the augmented reductions.

## Main definitions

* `Cslib.Complexity.LevinReduction`: instance map with forward and backward witness maps.
* `Cslib.Complexity.LevinReduction.refl`, `Cslib.Complexity.LevinReduction.trans`: identity and
  composition.
* `Cslib.Complexity.LevinHard`: every NP relation Levin-reduces to the given one.

## Main results

* `Cslib.Complexity.LevinReduction.mem_language_iff`,
  `Cslib.Complexity.LevinReduction.toPolyTimeReducible`: the instance map is a polynomial-time
  many-one reduction of the languages.
* `Cslib.Complexity.LevinHard.trans`: hardness transfers along Levin reductions.
* `Cslib.Complexity.LevinHard.npHard`: the language of a Levin-hard relation is `NP`-hard.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008]; numbering of
  the author's online draft of 30 December 2006.
* [L. A. Levin, *Universal sequential search problems*][Levin1973]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}

/-- A **Levin reduction** of the NP relation `R` to the NP relation `S`
[Goldreich, Exercise 2.28][Goldreich2008]: a polynomial-time map `toFun` of instances, a
polynomial-time map `forwardWitness` sending a witness `w` for `a` to the witness
`forwardWitness (a, w)` for `toFun a`, and a polynomial-time map `backwardWitness` sending a
witness `w` for `toFun a` to the witness `backwardWitness (a, w)` for `a`. -/
structure LevinReduction (R : NPRelation encA) (S : NPRelation encB) where
  /-- The map of instances. -/
  toFun : α → β
  /-- The map of witnesses for an instance to witnesses for its image. -/
  forwardWitness : α × List Bool → List Bool
  /-- The map of witnesses for the image of an instance back to witnesses for the instance. -/
  backwardWitness : α × List Bool → List Bool
  /-- The map of instances is computable in polynomial time. -/
  computableInPolyTime_toFun : ComputableInPolyTime toFun encA encB
  /-- The forward witness map is computable in polynomial time. -/
  computableInPolyTime_forwardWitness :
    ComputableInPolyTime forwardWitness (encPair encA encBits) encBits
  /-- The backward witness map is computable in polynomial time. -/
  computableInPolyTime_backwardWitness :
    ComputableInPolyTime backwardWitness (encPair encA encBits) encBits
  /-- The forward map sends witnesses to witnesses. -/
  isWitness_forwardWitness :
    ∀ a w, R.IsWitness a w → S.IsWitness (toFun a) (forwardWitness (a, w))
  /-- The backward map sends witnesses to witnesses. -/
  isWitness_backwardWitness :
    ∀ a w, S.IsWitness (toFun a) w → R.IsWitness a (backwardWitness (a, w))

namespace LevinReduction

variable {R : NPRelation encA} {S : NPRelation encB} {T : NPRelation encC}

/-- The instance map of a Levin reduction preserves membership in the languages. -/
theorem mem_language_iff (r : LevinReduction R S) (a : α) :
    a ∈ R.language ↔ r.toFun a ∈ S.language :=
  ⟨fun ⟨w, hw⟩ => ⟨_, r.isWitness_forwardWitness a w hw⟩,
    fun ⟨w, hw⟩ => ⟨_, r.isWitness_backwardWitness a w hw⟩⟩

/-- A Levin reduction is a polynomial-time many-one reduction of the languages. -/
theorem toPolyTimeReducible (r : LevinReduction R S) :
    PolyTimeReducible encA encB R.language S.language :=
  ⟨r.toFun, r.computableInPolyTime_toFun, r.mem_language_iff⟩

/-- The identity Levin reduction of an NP relation to itself. -/
@[expose]
def refl (R : NPRelation encA) : LevinReduction R R where
  toFun := id
  forwardWitness := Prod.snd
  backwardWitness := Prod.snd
  computableInPolyTime_toFun := .id'
  computableInPolyTime_forwardWitness := .snd encA encBits
  computableInPolyTime_backwardWitness := .snd encA encBits
  isWitness_forwardWitness _ _ h := h
  isWitness_backwardWitness _ _ h := h

/-- **Composition of Levin reductions.** The forward maps compose along the first instance map;
the backward map first pulls a witness back to the intermediate instance. -/
@[expose]
def trans (r : LevinReduction R S) (s : LevinReduction S T) : LevinReduction R T where
  toFun := s.toFun ∘ r.toFun
  forwardWitness x := s.forwardWitness (r.toFun x.1, r.forwardWitness x)
  backwardWitness x := r.backwardWitness (x.1, s.backwardWitness (r.toFun x.1, x.2))
  computableInPolyTime_toFun := s.computableInPolyTime_toFun.comp r.computableInPolyTime_toFun
  computableInPolyTime_forwardWitness :=
    s.computableInPolyTime_forwardWitness.comp
      ((r.computableInPolyTime_toFun.comp (.fst encA encBits)).prod
        r.computableInPolyTime_forwardWitness)
  computableInPolyTime_backwardWitness :=
    r.computableInPolyTime_backwardWitness.comp
      ((ComputableInPolyTime.fst encA encBits).prod
        (s.computableInPolyTime_backwardWitness.comp
          ((r.computableInPolyTime_toFun.comp (.fst encA encBits)).prod
            (.snd encA encBits))))
  isWitness_forwardWitness a w h :=
    s.isWitness_forwardWitness _ _ (r.isWitness_forwardWitness a w h)
  isWitness_backwardWitness a w h :=
    r.isWitness_backwardWitness a _ (s.isWitness_backwardWitness _ w h)

@[simp]
theorem trans_toFun (r : LevinReduction R S) (s : LevinReduction S T) :
    (r.trans s).toFun = s.toFun ∘ r.toFun :=
  rfl

end LevinReduction

/-- The NP relation `S` is **Levin-hard**: every NP relation, over any encoded type of instances,
Levin-reduces to it. This is Goldreich's `PC`-hardness (the remark following
[Goldreich, Definition 2.18][Goldreich2008]) for reductions with both witness maps, over NP
relations with certificates of exactly the prescribed length. As in `Cslib.Complexity.HardUnder`,
the instance type is strict-implicit. -/
@[expose]
def LevinHard (S : NPRelation encB) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (R : NPRelation encA), Nonempty (LevinReduction R S)

/-- Levin-hardness transfers along a Levin reduction. -/
theorem LevinHard.trans {S : NPRelation encB} {T : NPRelation encC} (hS : LevinHard S)
    (s : LevinReduction S T) : LevinHard T := fun _ encA R =>
  let ⟨r⟩ := hS encA R
  ⟨r.trans s⟩

/-- The language of a Levin-hard NP relation is `NP`-hard. -/
theorem LevinHard.npHard {S : NPRelation encB} (hS : LevinHard S) : NPHard encB S.language :=
  fun _ encA _ hA =>
    let ⟨R, hR⟩ := mem_NP_iff_exists_npRelation.1 hA
    let ⟨r⟩ := hS encA R
    hR ▸ r.toPolyTimeReducible

end Cslib.Complexity
