/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Raw.Graph
public import Complexity.Logics.FirstOrder.Raw.Uniformize
public import Complexity.Logics.FirstOrder.Trakhtenbrot.Undecidability
import Complexity.Foundations.Computability.ComputablePred

/-!
# Trakhtenbrot's theorem for a binary relation

**Trakhtenbrot's theorem** in the form of [Libkin2004], Theorem 9.2: for every relational
vocabulary `σ` with at least one binary relation symbol, finite satisfiability of first-order
sentences over `σ` is undecidable
(`Cslib.Logic.FO.RawFormula.not_exists_computable_finSat_of_mem`). Since finite satisfiability is
r.e. (`Cslib.Logic.FO.RawFormula.rePred_finSat`), the finitely valid sentences over `σ` do not
form an r.e. set ([Libkin2004], Corollary 9.3,
`Cslib.Logic.FO.RawFormula.not_exists_rePred_finValid_of_mem`), so no effective proof system for
sentences over `σ` is sound and complete for finite validity
(`Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_unprovable`).

The proof reduces finite satisfiability of arbitrary raw formulas, undecidable by
`Cslib.Logic.FO.RawFormula.not_computablePred_finSat`, along the primitive recursive map
`Cslib.Logic.FO.RawFormula.binarize s`, whose values are sentences over `{(s, 2)}`:

1. `uniformize` rewrites all relation symbols as the single symbol `0`, coding each symbol and
   arity in the length of a padded argument list
   (`Complexity/Logics/FirstOrder/Raw/Uniformize.lean`);
2. `toGraph` interprets the resulting structure in one binary relation by tuple gadgets
   (`Complexity/Logics/FirstOrder/Raw/Graph.lean`);
3. the existential closure turns the result into a sentence
   (`Complexity/Logics/FirstOrder/Raw/Sentence.lean`), and `rename [s]` moves the binary symbol
   `0` to `s`.

Each step preserves finite satisfiability (`Cslib.Logic.FO.RawFormula.finSat_binarize`).

**Relation to `not_computablePred_finSat`.** `Cslib.Logic.FO.RawFormula.not_computablePred_finSat`
rules out a decision procedure that is correct on all raw formulas. The theorems here only ask the
procedure to be correct on sentences over `σ`, a set that may contain a single binary relation
symbol, so they are strictly stronger statements.

**Scope.** The sentences are library-local `Cslib.Logic.FO.RawFormula`s, with equality and
relation symbols named by natural numbers; a vocabulary is a set of pairs (symbol, arity). A
computable translation from Mathlib's `L.Sentence` is not formalized (see the module documentation
of `Complexity/Logics/FirstOrder/Raw/Basic.lean`).

## Main definitions

* `Cslib.Logic.FO.RawFormula.binarize`: the reduction to a single binary relation symbol.

## Main results

* `Cslib.Logic.FO.RawFormula.finSat_binarize`, `Cslib.Logic.FO.RawFormula.isSentenceOver_binarize`,
  `Cslib.Logic.FO.RawFormula.primrec_binarize`: the reduction.
* `Cslib.Logic.FO.RawFormula.not_exists_computable_finSat_of_mem`: **Trakhtenbrot's theorem** for a
  vocabulary with a binary relation symbol.
* `Cslib.Logic.FO.RawFormula.not_exists_rePred_finValid_of_mem`: finite validity of sentences over
  such a vocabulary is not r.e.
* `Cslib.Logic.FO.RawFormula.exists_isSentenceOver_finValid_unprovable`: no sound and complete
  proof system for finite validity of sentences over such a vocabulary.

## References

* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace Cslib.Logic.FO

namespace RawFormula

/-- Renaming the binary symbol `0` to `s` preserves finite satisfiability. -/
private theorem finSat_rename_singleton {φ : RawFormula} (hφ : ∀ a ∈ φ.atoms, a = (0, 2)) (s : ℕ) :
    FinSat (rename [s] φ) ↔ FinSat φ := by
  constructor
  · rintro ⟨M, hf, hn, I, v, h⟩
    exact ⟨M, hf, hn, _, v, (realize_rename [s] I φ v).1 h⟩
  · rintro ⟨M, hf, hn, I, v, h⟩
    refine ⟨M, hf, hn, fun _ => I 0, v, (realize_rename [s] _ φ v).2 ?_⟩
    refine (realize_congr_rel φ v fun r as hr => ?_).1 h
    obtain ⟨rfl, -⟩ := Prod.mk.inj (hφ _ hr)
    exact Iff.rfl

/-- **The reduction to one binary relation symbol `s`**: a sentence over `{(s, 2)}` that is
finitely satisfiable iff `φ` is. -/
def binarize (s : ℕ) (φ : RawFormula) : RawFormula :=
  let ψ := uniformize φ.varBound φ
  rename [s] (exClosure (toGraph ψ.varBound ψ))

theorem isSentenceOver_binarize (s : ℕ) (φ : RawFormula) :
    IsSentenceOver {(s, 2)} (binarize s φ) := by
  refine ⟨by rw [binarize, IsSentence, freeVars_rename]; exact isSentence_exClosure _,
    fun a ha => ?_⟩
  rw [binarize, atoms_rename, List.mem_map, atoms_exClosure] at ha
  obtain ⟨b, hb, rfl⟩ := ha
  rw [atoms_toGraph _ _ b hb]
  rfl

theorem finSat_binarize (s : ℕ) (φ : RawFormula) : FinSat (binarize s φ) ↔ FinSat φ := by
  rw [binarize, finSat_rename_singleton (by rw [atoms_exClosure]; exact atoms_toGraph _ _),
    finSat_exClosure, finSat_toGraph (atoms_uniformize _ φ), finSat_uniformize]

open Primrec in
theorem primrec_binarize (s : ℕ) : Primrec (binarize s) := by
  have hu : Primrec fun φ => uniformize φ.varBound φ :=
    primrec₂_uniformize.comp primrec_varBound Primrec.id
  exact primrec₂_rename.comp (const [s])
    (primrec_exClosure.comp (primrec₂_toGraph.comp (primrec_varBound.comp hu) hu))

/-- **Trakhtenbrot's theorem** ([Libkin2004], Theorem 9.2): for every vocabulary `σ` with a binary
relation symbol, no computable procedure decides finite satisfiability of sentences over `σ`. -/
theorem not_exists_computable_finSat_of_mem {σ : Set (ℕ × ℕ)} {s : ℕ} (hs : (s, 2) ∈ σ) :
    ¬∃ f : RawFormula → Bool, Computable f ∧
      ∀ φ, IsSentenceOver σ φ → (f φ = true ↔ FinSat φ) := by
  rintro ⟨f, hf, hfφ⟩
  apply not_computablePred_finSat
  refine ComputablePred.computable_iff.2 ⟨fun φ => f (binarize s φ),
    hf.comp (primrec_binarize s).to_comp, funext fun φ => propext ?_⟩
  have h := isSentenceOver_binarize s φ
  rw [hfφ _ ⟨h.1, fun a ha => by rw [h.2 a ha]; exact hs⟩, finSat_binarize]

/-- **Finite validity is not r.e.** ([Libkin2004], Corollary 9.3): for every vocabulary `σ` with a
binary relation symbol, the finitely valid sentences over `σ` do not form an r.e. set. -/
theorem not_exists_rePred_finValid_of_mem {σ : Set (ℕ × ℕ)} {s : ℕ} (hs : (s, 2) ∈ σ) :
    ¬∃ S : RawFormula → Prop, REPred S ∧ ∀ φ, IsSentenceOver σ φ → (S φ ↔ FinValid φ) := by
  rintro ⟨S, hS, hSφ⟩
  apply not_rePred_finValid
  refine (hS.comp (primrec_neg ((primrec_binarize s).comp (primrec_neg Primrec.id))).to_comp).of_eq
    fun φ => ?_
  have h := isSentenceOver_binarize s (neg φ)
  have h' : IsSentenceOver σ (neg (binarize s (neg φ))) :=
    isSentenceOver_neg.2 ⟨h.1, fun a ha => by rw [h.2 a ha]; exact hs⟩
  change S (neg (binarize s (neg φ))) ↔ _
  rw [hSφ _ h', finValid_neg_iff, finSat_binarize, finValid_iff_not_finSat_neg]

/-- **Incompleteness for finite validity over a binary relation.** For every vocabulary `σ` with a
binary relation symbol, every r.e. set of finitely valid sentences misses some finitely valid
sentence over `σ`. -/
theorem exists_isSentenceOver_finValid_not_of_rePred {σ : Set (ℕ × ℕ)} {s : ℕ} (hs : (s, 2) ∈ σ)
    {S : RawFormula → Prop} (hS : REPred S) (hsound : ∀ φ, S φ → FinValid φ) :
    ∃ φ, IsSentenceOver σ φ ∧ FinValid φ ∧ ¬S φ := by
  by_contra hne
  exact not_exists_rePred_finValid_of_mem hs ⟨S, hS, fun φ hφ =>
    ⟨hsound φ, fun h => by_contra fun hS' => hne ⟨φ, hφ, h, hS'⟩⟩⟩

/-- **No sound and complete proof system for finite validity over a binary relation.** If
`P φ π` ("`π` is a proof of `φ`") is a decidable relation and only finitely valid sentences have
proofs, then for every vocabulary `σ` with a binary relation symbol some finitely valid sentence
over `σ` has no proof. -/
theorem exists_isSentenceOver_finValid_unprovable {σ : Set (ℕ × ℕ)} {s : ℕ} (hs : (s, 2) ∈ σ)
    {β : Type*} [Primcodable β] {P : RawFormula → β → Prop}
    (hP : ComputablePred (Function.uncurry P)) (hsound : ∀ φ π, P φ π → FinValid φ) :
    ∃ φ, IsSentenceOver σ φ ∧ FinValid φ ∧ ∀ π, ¬P φ π := by
  obtain ⟨φ, hσ, hφ, hS⟩ := exists_isSentenceOver_finValid_not_of_rePred hs
    (ComputablePred.rePred_exists hP) fun φ ⟨π, h⟩ => hsound φ π h
  exact ⟨φ, hσ, hφ, fun π h => hS ⟨π, h⟩⟩

end RawFormula

end Cslib.Logic.FO
