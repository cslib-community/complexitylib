/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.BoundedFormula
public import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Binary
import CslibFrontier.Foundations.Computability.ComputablePred

/-!
# Trakhtenbrot's theorem for Mathlib sentences

**Trakhtenbrot's theorem** ([Trakhtenbrot1950]) in the form of [Libkin2004], Theorem 9.2 and
Corollary 9.3, for Mathlib's `L.Sentence`: for a finite relational language `L` with a binary
relation symbol, finite satisfiability of sentences is r.e. but undecidable, and finite validity is
co-r.e. but not r.e., so no effective proof system is sound and complete for truth in all finite
structures.

The statements use the raw coding of sentences,
`FirstOrder.Language.BoundedFormula.primcodableRaw`, through its scoped instance
(`open scoped FirstOrder.Language.BoundedFormula.RawCoding`). Its hypotheses are
`[L.IsRelational]`, `[Encodable (Σ l, L.Relations l)]` and `[Finite (Σ l, L.Relations l)]`; the
coding does not depend on the choice of encoding up to primitive recursive equivalence
(`FirstOrder.Language.BoundedFormula.primrec_id_primcodableRaw`).

The r.e. half follows from the raw result `Cslib.Logic.FO.RawFormula.rePred_finSat` along the
primitive recursive translation `FirstOrder.Language.BoundedFormula.toRaw`, which preserves finite
satisfiability (`FirstOrder.Language.Sentence.finSat_iff_toRaw`). The undecidability half reduces
the raw theorem `Cslib.Logic.FO.RawFormula.not_computablePred_finSat` along
`FirstOrder.Language.Sentence.binarize R`: a raw formula is reduced to a raw sentence over the one
binary symbol `encode ⟨2, R⟩` (`Cslib.Logic.FO.RawFormula.binarize`), renamed into level-named form
(`Cslib.Logic.FO.RawFormula.levels`) and decoded as an `L.Sentence`
(`FirstOrder.Language.BoundedFormula.fromRaw`).

**Scope.** The language must be relational with finitely many relation symbols, one of them
binary. Languages with function symbols, infinite vocabularies, and vocabularies whose only
non-unary symbols have arity at least three are not covered.

## Main definitions

* `FirstOrder.Language.Sentence.binarize`: the reduction from raw formulas.

## Main results

* `FirstOrder.Language.Sentence.finSat_binarize`, `FirstOrder.Language.Sentence.primrec_binarize`:
  the reduction.
* `FirstOrder.Language.Sentence.rePred_finSat`: finite satisfiability is r.e.
* `FirstOrder.Language.Sentence.not_computablePred_finSat`: **Trakhtenbrot's theorem**.
* `FirstOrder.Language.Sentence.not_rePred_finValid`,
  `FirstOrder.Language.Sentence.not_computablePred_finValid`,
  `FirstOrder.Language.Sentence.rePred_not_finValid`,
  `FirstOrder.Language.Sentence.not_rePred_not_finSat`: finite validity is co-r.e. but not r.e.
* `FirstOrder.Language.Sentence.exists_finValid_not_of_rePred`,
  `FirstOrder.Language.Sentence.exists_finValid_unprovable`: no sound and complete effective proof
  system for finite validity.

## References

* [B. A. Trakhtenbrot, *Impossibility of an algorithm for the decision problem in finite
  classes*][Trakhtenbrot1950]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace FirstOrder.Language.Sentence

open Encodable Cslib.Logic.FO BoundedFormula
open scoped BoundedFormula.RawCoding

variable {L : Language} [Encodable (Σ l, L.Relations l)]

/-- **The reduction from raw formulas to `L.Sentence`**: the sentence over the binary symbol `R`
decoded from the level-named form of `Cslib.Logic.FO.RawFormula.binarize (encode ⟨2, R⟩) ψ`. The
decoding always succeeds (`FirstOrder.Language.Sentence.toRaw_binarize`); `⊥` is a default. -/
def binarize (R : L.Relations 2) (ψ : RawFormula) : L.Sentence :=
  (fromRaw 0 (RawFormula.levels
    (RawFormula.binarize (encode (⟨2, R⟩ : Σ l, L.Relations l)) ψ))).getD ⊥

variable [L.IsRelational]

theorem toRaw_binarize (R : L.Relations 2) (ψ : RawFormula) :
    toRaw (binarize R ψ) =
      RawFormula.levels (RawFormula.binarize (encode (⟨2, R⟩ : Σ l, L.Relations l)) ψ) := by
  have hw := RawFormula.wellScoped_levels_of_isSentenceOver
    (RawFormula.isSentenceOver_binarize (encode (⟨2, R⟩ : Σ l, L.Relations l)) ψ)
  have hs : (fromRaw (L := L) (α := Empty) 0 (RawFormula.levels
      (RawFormula.binarize (encode (⟨2, R⟩ : Σ l, L.Relations l)) ψ))).isSome := by
    refine isSome_fromRaw.2 (hw.mono (fun _ h => h.elim) fun r k h => ?_)
    obtain ⟨hr, hk⟩ := Prod.ext_iff.1 (Set.mem_singleton_iff.1 h)
    exact ⟨⟨2, R⟩, hr.symm, hk.symm⟩
  obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1 hs
  rw [binarize, hφ, Option.getD_some]
  exact toRaw_of_fromRaw hφ

theorem finSat_binarize (R : L.Relations 2) (ψ : RawFormula) :
    FinSat (binarize R ψ) ↔ RawFormula.FinSat ψ := by
  rw [finSat_iff_toRaw, toRaw_binarize, RawFormula.finSat_levels, RawFormula.finSat_binarize]

variable [Finite (Σ l, L.Relations l)]

theorem primrec_binarize (R : L.Relations 2) : Primrec (binarize R) :=
  Primrec.option_getD.comp (primrec_fromRaw.comp (RawFormula.primrec_levels.comp
    (RawFormula.primrec_binarize _))) (Primrec.const ⊥)

/-- **Finite satisfiability is r.e.** ([Libkin2004], Chapter 9), for sentences of a finite
relational language. -/
theorem rePred_finSat : REPred (FinSat (L := L)) :=
  (RawFormula.rePred_finSat.comp (primrec_toRaw (L := L) (α := Empty) (n := 0)).to_comp).of_eq
    fun φ => (finSat_iff_toRaw φ).symm

/-- Finite non-validity is r.e. -/
theorem rePred_not_finValid : REPred fun φ : L.Sentence => ¬FinValid φ :=
  (rePred_finSat.comp primrec_not.to_comp).of_eq fun φ => by
    rw [finValid_iff_not_finSat_not, not_not]

/-- **Trakhtenbrot's theorem** ([Libkin2004], Theorem 9.2): for a finite relational language with
a binary relation symbol `R`, finite satisfiability of sentences is undecidable. -/
theorem not_computablePred_finSat (R : L.Relations 2) : ¬ComputablePred (FinSat (L := L)) :=
  fun h => RawFormula.not_computablePred_finSat <|
    (h.comp (primrec_binarize R).to_comp).of_eq fun ψ => finSat_binarize R ψ

/-- Finite unsatisfiability is not r.e., for a finite relational language with a binary relation
symbol `R`. -/
theorem not_rePred_not_finSat (R : L.Relations 2) : ¬REPred fun φ : L.Sentence => ¬FinSat φ :=
  fun h => RawFormula.not_rePred_not_finSat <|
    (h.comp (primrec_binarize R).to_comp).of_eq fun ψ => by rw [finSat_binarize]

/-- **Finite validity is not r.e.** ([Libkin2004], Corollary 9.3), for a finite relational language
with a binary relation symbol `R`. -/
theorem not_rePred_finValid (R : L.Relations 2) : ¬REPred (FinValid (L := L)) :=
  fun h => not_rePred_not_finSat R <| (h.comp primrec_not.to_comp).of_eq fun φ =>
    finValid_not_iff φ

/-- Finite validity is undecidable, for a finite relational language with a binary relation
symbol `R`. -/
theorem not_computablePred_finValid (R : L.Relations 2) : ¬ComputablePred (FinValid (L := L)) :=
  fun h => not_rePred_finValid R h.to_re

/-- **Incompleteness for finite validity.** For a finite relational language with a binary relation
symbol `R`, every r.e. set of finitely valid sentences misses some finitely valid sentence. -/
theorem exists_finValid_not_of_rePred (R : L.Relations 2) {S : L.Sentence → Prop} (hS : REPred S)
    (hsound : ∀ φ, S φ → FinValid φ) : ∃ φ, FinValid φ ∧ ¬S φ :=
  hS.exists_not_of_not_rePred (not_rePred_finValid R) hsound

/-- **No sound and complete proof system for finite validity.** For a finite relational language
with a binary relation symbol `R`: if `P φ π` ("`π` is a proof of `φ`") is a decidable relation and
only finitely valid sentences have proofs, then some finitely valid sentence has no proof. -/
theorem exists_finValid_unprovable (R : L.Relations 2) {β : Type*} [Primcodable β]
    {P : L.Sentence → β → Prop} (hP : ComputablePred (Function.uncurry P))
    (hsound : ∀ φ π, P φ π → FinValid φ) : ∃ φ, FinValid φ ∧ ∀ π, ¬P φ π :=
  hP.exists_forall_not_of_not_rePred (not_rePred_finValid R) hsound

end FirstOrder.Language.Sentence
