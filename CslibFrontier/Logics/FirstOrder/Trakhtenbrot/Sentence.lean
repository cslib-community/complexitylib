/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Raw.BoundedFormula
public import CslibFrontier.Logics.FirstOrder.Trakhtenbrot.Binary
public import Mathlib.SetTheory.Cardinal.NatCard
import CslibFrontier.Foundations.Computability.ComputablePred
import CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Monadic

/-!
# Trakhtenbrot's theorem and the monadic decidability dichotomy for Mathlib sentences

For a finite relational language `L`, finite satisfiability of first-order sentences is decidable
if and only if every relation symbol of `L` has arity at most `1`, and equivalently finite validity
is decidable — or even recursively enumerable — in exactly the same monadic case
(`FirstOrder.Language.Sentence.computablePred_finSat_iff`,
`FirstOrder.Language.Sentence.computablePred_finValid_iff`,
`FirstOrder.Language.Sentence.rePred_finValid_iff`).

* **Undecidable side** ([Trakhtenbrot1950]; compare [Libkin2004], Theorem 9.2 and Corollary 9.3, for
  the binary case): when `L` has a relation symbol `R` of arity `l ≥ 2`, finite satisfiability is
  r.e. but undecidable, and finite validity is co-r.e. but not r.e., so no effective proof system is
  sound and complete for truth in all finite structures. A raw formula is reduced along
  `FirstOrder.Language.Sentence.singleRel R`: turned into a raw sentence over the single symbol
  `encode ⟨l, R⟩` of arity `l` (`Cslib.Logic.FO.RawFormula.singleRel`), renamed into level-named
  form (`Cslib.Logic.FO.RawFormula.levels`) and decoded as an `L.Sentence`
  (`FirstOrder.Language.BoundedFormula.fromRaw`).
* **Decidable monadic side** ([Lowenheim1915]): when every relation symbol of `L` has arity at most
  `1` (allowing both unary and nullary symbols), a finitely satisfiable sentence `φ` of quantifier
  rank `q` has a model on `Fin (n + 1)` with `n + 1 ≤ max q 1 * 2 ^ k` for `k` unary symbols
  (`Cslib.Logic.FO.Monadic.exists_fin_realize`; the explicit bound is proved there). Combining that
  bound with the primitive recursive fixed-size evaluator `Cslib.Logic.FO.RawFormula.SatOnFin` and
  primitive recursive quantifier rank (`FirstOrder.Language.BoundedFormula.primrec_quantifierRank`)
  makes `FinSat` and `FinValid` primitive recursive and hence decidable.

The statements use the raw coding of sentences,
`FirstOrder.Language.BoundedFormula.primcodableRaw`, through its scoped instance
(`open scoped FirstOrder.Language.BoundedFormula.RawCoding`). Its hypotheses are
`[L.IsRelational]`, `[Encodable (Σ l, L.Relations l)]` and `[Finite (Σ l, L.Relations l)]`; the
coding does not depend on the choice of encoding up to primitive recursive equivalence
(`FirstOrder.Language.BoundedFormula.primrec_id_primcodableRaw`).

**Scope.** The language must be relational with finitely many relation symbols. Languages with
function symbols and infinite vocabularies are not covered here.

## Main definitions

* `FirstOrder.Language.Sentence.singleRel`: the reduction from raw formulas to sentences over a
  single relation symbol of arity at least `2`.

## Main results

* `FirstOrder.Language.Sentence.toRaw_singleRel`,
  `FirstOrder.Language.Sentence.finSat_singleRel`,
  `FirstOrder.Language.Sentence.primrec_singleRel`: the reduction.
* `FirstOrder.Language.Sentence.rePred_finSat`,
  `FirstOrder.Language.Sentence.rePred_not_finValid`: finite satisfiability and finite non-validity
  are r.e.
* `FirstOrder.Language.Sentence.not_computablePred_finSat`: **Trakhtenbrot's theorem** for arity
  `l ≥ 2`.
* `FirstOrder.Language.Sentence.not_rePred_finValid`,
  `FirstOrder.Language.Sentence.not_computablePred_finValid`,
  `FirstOrder.Language.Sentence.not_rePred_not_finSat`: finite validity is not r.e. for arity
  `l ≥ 2`.
* `FirstOrder.Language.Sentence.exists_finValid_not_of_rePred`,
  `FirstOrder.Language.Sentence.exists_finValid_unprovable`: no sound and complete effective proof
  system for finite validity when a symbol has arity `l ≥ 2`.
* `FirstOrder.Language.Sentence.finSat_iff_exists_lt_satOnFin`,
  `FirstOrder.Language.Sentence.primrecPred_finSat_of_monadic`,
  `FirstOrder.Language.Sentence.computablePred_finSat_of_monadic`,
  `FirstOrder.Language.Sentence.primrecPred_finValid_of_monadic`,
  `FirstOrder.Language.Sentence.computablePred_finValid_of_monadic`: **Löwenheim's decidability**
  for monadic finite relational languages.
* `FirstOrder.Language.Sentence.computablePred_finSat_iff`,
  `FirstOrder.Language.Sentence.computablePred_finValid_iff`,
  `FirstOrder.Language.Sentence.rePred_finValid_iff`,
  `FirstOrder.Language.Sentence.rePred_not_finSat_iff`: **the full decidability and r.e. dichotomy**
  for finite relational languages.

## References

* [B. A. Trakhtenbrot, *Impossibility of an algorithm for the decision problem in finite
  classes*][Trakhtenbrot1950]
* [L. Löwenheim, *Über Möglichkeiten im Relativkalkül*][Lowenheim1915]
* [L. Libkin, *Elements of Finite Model Theory*][Libkin2004]
-/

public section

namespace FirstOrder.Language.Sentence

open Encodable Cslib.Logic.FO BoundedFormula
open scoped BoundedFormula.RawCoding

variable {L : Language} [Encodable (Σ l, L.Relations l)]

/-- **The reduction from raw formulas to `L.Sentence`**: the sentence over the relation symbol `R`
(of arity `l ≥ 2`) decoded from the level-named form of
`Cslib.Logic.FO.RawFormula.singleRel (encode ⟨l, R⟩) l ψ`. When `2 ≤ l`, the decoding always
succeeds (`FirstOrder.Language.Sentence.toRaw_singleRel`); `⊥` is a default. -/
def singleRel {l : ℕ} (R : L.Relations l) (ψ : RawFormula) : L.Sentence :=
  (fromRaw 0 (RawFormula.levels
    (RawFormula.singleRel (encode (⟨l, R⟩ : Σ l, L.Relations l)) l ψ))).getD ⊥

variable [L.IsRelational]

theorem toRaw_singleRel {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l) (ψ : RawFormula) :
    toRaw (singleRel R ψ) =
      RawFormula.levels (RawFormula.singleRel (encode (⟨l, R⟩ : Σ l, L.Relations l)) l ψ) := by
  have hw := RawFormula.wellScoped_levels_of_isSentenceOver
    (RawFormula.isSentenceOver_singleRel (s := encode (⟨l, R⟩ : Σ l, L.Relations l)) hl ψ)
  have hs : (fromRaw (L := L) (α := Empty) 0 (RawFormula.levels
      (RawFormula.singleRel (encode (⟨l, R⟩ : Σ l, L.Relations l)) l ψ))).isSome := by
    refine isSome_fromRaw.2 (hw.mono (fun _ h => h.elim) fun r k h => ?_)
    obtain ⟨hr, hk⟩ := Prod.ext_iff.1 (Set.mem_singleton_iff.1 h)
    exact ⟨⟨l, R⟩, hr.symm, hk.symm⟩
  obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1 hs
  rw [singleRel, hφ, Option.getD_some]
  exact toRaw_of_fromRaw hφ

theorem finSat_singleRel {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l) (ψ : RawFormula) :
    FinSat (singleRel R ψ) ↔ RawFormula.FinSat ψ := by
  rw [finSat_iff_toRaw, toRaw_singleRel R hl, RawFormula.finSat_levels, RawFormula.finSat_singleRel]

/-- A sentence holds in some `L`-structure on `Fin (n + 1)` iff its raw formula satisfies
`SatOnFin n`. -/
theorem exists_structure_fin_realize_iff_satOnFin (n : ℕ) (φ : L.Sentence) :
    (∃ _ : L.Structure (Fin (n + 1)), Fin (n + 1) ⊨ φ) ↔ RawFormula.SatOnFin n φ.toRaw :=
  (exists_structure_realize_iff_toRaw (Fin (n + 1)) φ).trans RawFormula.satOnFin_iff.symm

/-- **Bounded finite-model search for monadic sentences.** In a monadic language with finitely many
unary relation symbols, a sentence `φ` is finitely satisfiable iff its raw formula is satisfiable on
`Fin (n + 1)` for some `n < max q 1 * 2 ^ k`, where `q` is the quantifier rank of `φ` and `k` the
number of unary relation symbols. The small-model bound is proved in
`Cslib.Logic.FO.Monadic.exists_fin_realize` (after [Lowenheim1915]). -/
theorem finSat_iff_exists_lt_satOnFin [Finite (L.Relations 1)]
    (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) (φ : L.Sentence) :
    FinSat φ ↔
      ∃ n < max (quantifierRank φ) 1 * 2 ^ Nat.card (L.Relations 1),
        RawFormula.SatOnFin n φ.toRaw := by
  constructor
  · rintro ⟨M, _, _, _, hM⟩
    obtain ⟨n, hn, hfin⟩ := Cslib.Logic.FO.Monadic.exists_fin_realize hmon hM
    exact ⟨n, Nat.lt_of_succ_le hn, (exists_structure_fin_realize_iff_satOnFin n φ).1 hfin⟩
  · rintro ⟨n, _, hsat⟩
    obtain ⟨hS, hφ⟩ := (exists_structure_fin_realize_iff_satOnFin n φ).2 hsat
    exact ⟨Fin (n + 1), hS, inferInstance, inferInstance, hφ⟩

variable [Finite (Σ l, L.Relations l)]

theorem primrec_singleRel {l : ℕ} (R : L.Relations l) : Primrec (singleRel R) :=
  Primrec.option_getD.comp (primrec_fromRaw.comp (RawFormula.primrec_levels.comp
    (RawFormula.primrec_singleRel _ _))) (Primrec.const ⊥)

/-- **Finite satisfiability is r.e.** ([Libkin2004], Chapter 9), for sentences of a finite
relational language. -/
theorem rePred_finSat : REPred (FinSat (L := L)) :=
  (RawFormula.rePred_finSat.comp (primrec_toRaw (L := L) (α := Empty) (n := 0)).to_comp).of_eq
    fun φ => (finSat_iff_toRaw φ).symm

/-- Finite non-validity is r.e. -/
theorem rePred_not_finValid : REPred fun φ : L.Sentence => ¬FinValid φ :=
  (rePred_finSat.comp primrec_not.to_comp).of_eq fun φ => by
    rw [finValid_iff_not_finSat_not, not_not]

/-- **Trakhtenbrot's theorem** (extending [Libkin2004], Theorem 9.2): for a finite relational
language with a relation symbol `R` of arity `l ≥ 2`, finite satisfiability of sentences is
undecidable. -/
theorem not_computablePred_finSat {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l) :
    ¬ComputablePred (FinSat (L := L)) :=
  fun h => RawFormula.not_computablePred_finSat <|
    (h.comp (primrec_singleRel R).to_comp).of_eq fun ψ => finSat_singleRel R hl ψ

/-- Finite unsatisfiability is not r.e., for a finite relational language with a relation symbol `R`
of arity `l ≥ 2`. -/
theorem not_rePred_not_finSat {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l) :
    ¬REPred fun φ : L.Sentence => ¬FinSat φ :=
  fun h => RawFormula.not_rePred_not_finSat <|
    (h.comp (primrec_singleRel R).to_comp).of_eq fun ψ => by rw [finSat_singleRel R hl]

/-- **Finite validity is not r.e.** (extending [Libkin2004], Corollary 9.3), for a finite relational
language with a relation symbol `R` of arity `l ≥ 2`. -/
theorem not_rePred_finValid {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l) :
    ¬REPred (FinValid (L := L)) :=
  fun h => not_rePred_not_finSat R hl <| (h.comp primrec_not.to_comp).of_eq fun φ =>
    finValid_not_iff φ

/-- Finite validity is undecidable, for a finite relational language with a relation symbol `R` of
arity `l ≥ 2`. -/
theorem not_computablePred_finValid {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l) :
    ¬ComputablePred (FinValid (L := L)) :=
  fun h => not_rePred_finValid R hl h.to_re

/-- **Incompleteness for finite validity.** For a finite relational language with a relation symbol
`R` of arity `l ≥ 2`, every r.e. set of finitely valid sentences misses some finitely valid
sentence. -/
theorem exists_finValid_not_of_rePred {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l)
    {S : L.Sentence → Prop} (hS : REPred S) (hsound : ∀ φ, S φ → FinValid φ) :
    ∃ φ, FinValid φ ∧ ¬S φ :=
  hS.exists_not_of_not_rePred (not_rePred_finValid R hl) hsound

/-- **No sound and complete proof system for finite validity.** For a finite relational language
with a relation symbol `R` of arity `l ≥ 2`: if `P φ π` ("`π` is a proof of `φ`") is a decidable
relation and only finitely valid sentences have proofs, then some finitely valid sentence has no
proof. -/
theorem exists_finValid_unprovable {l : ℕ} (R : L.Relations l) (hl : 2 ≤ l)
    {β : Type*} [Primcodable β] {P : L.Sentence → β → Prop}
    (hP : ComputablePred (Function.uncurry P)) (hsound : ∀ φ π, P φ π → FinValid φ) :
    ∃ φ, FinValid φ ∧ ∀ π, ¬P φ π :=
  hP.exists_forall_not_of_not_rePred (not_rePred_finValid R hl) hsound

/-! ### Monadic decidability and the Trakhtenbrot–Löwenheim dichotomy -/

/-- **Löwenheim's theorem for finite satisfiability** ([Lowenheim1915]; explicit bound proved in
`CslibFrontier.Logics.FirstOrder.EhrenfeuchtFraisse.Monadic`): for a finite relational language
whose relation symbols all have arity at most `1`, finite satisfiability of sentences is primitive
recursive. -/
theorem primrecPred_finSat_of_monadic (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) :
    PrimrecPred (FinSat (L := L)) := by
  have : Finite (L.Relations 1) :=
    .of_injective (Sigma.mk 1) fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  have hB : Primrec fun φ : L.Sentence =>
      max (quantifierRank φ) 1 * 2 ^ Nat.card (L.Relations 1) :=
    Primrec.nat_mul.comp (Primrec.nat_max.comp primrec_quantifierRank (Primrec.const 1))
      (Primrec.const _)
  exact (RawFormula.primrecRel_satOnFin.exists_mem_list.comp
    (Primrec.list_range.comp hB) primrec_toRaw).of_eq fun φ => by
      simp only [List.mem_range, finSat_iff_exists_lt_satOnFin hmon φ]

/-- **Löwenheim's theorem for finite satisfiability** [Lowenheim1915]: for a finite relational
language whose relation symbols all have arity at most `1`, finite satisfiability of sentences is
decidable. -/
theorem computablePred_finSat_of_monadic (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) :
    ComputablePred (FinSat (L := L)) :=
  (primrecPred_finSat_of_monadic hmon).computablePred

/-- For a finite relational language whose relation symbols all have arity at most `1`, finite
validity of sentences is primitive recursive. -/
theorem primrecPred_finValid_of_monadic (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) :
    PrimrecPred (FinValid (L := L)) :=
  (((primrecPred_finSat_of_monadic hmon).comp primrec_not).not).of_eq fun φ =>
    (finValid_iff_not_finSat_not φ).symm

/-- For a finite relational language whose relation symbols all have arity at most `1`, finite
validity of sentences is decidable. -/
theorem computablePred_finValid_of_monadic (hmon : ∀ l, 2 ≤ l → IsEmpty (L.Relations l)) :
    ComputablePred (FinValid (L := L)) :=
  (primrecPred_finValid_of_monadic hmon).computablePred

/-- **The Trakhtenbrot–Löwenheim dichotomy for finite satisfiability** ([Trakhtenbrot1950];
[Lowenheim1915]): for a finite relational language `L`, finite satisfiability of first-order
sentences is decidable if and only if every relation symbol of `L` has arity at most `1`. -/
theorem computablePred_finSat_iff :
    ComputablePred (FinSat (L := L)) ↔ ∀ l, 2 ≤ l → IsEmpty (L.Relations l) :=
  ⟨fun h _ hl => ⟨fun R => not_computablePred_finSat R hl h⟩, computablePred_finSat_of_monadic⟩

/-- **The Trakhtenbrot–Löwenheim dichotomy for finite validity** ([Trakhtenbrot1950];
[Lowenheim1915]): for a finite relational language `L`, finite validity of first-order sentences is
decidable if and only if every relation symbol of `L` has arity at most `1`. -/
theorem computablePred_finValid_iff :
    ComputablePred (FinValid (L := L)) ↔ ∀ l, 2 ≤ l → IsEmpty (L.Relations l) :=
  ⟨fun h _ hl => ⟨fun R => not_computablePred_finValid R hl h⟩,
    computablePred_finValid_of_monadic⟩

/-- For a finite relational language `L`, finite validity of first-order sentences is recursively
enumerable if and only if every relation symbol of `L` has arity at most `1` (in which case it is
decidable). -/
theorem rePred_finValid_iff :
    REPred (FinValid (L := L)) ↔ ∀ l, 2 ≤ l → IsEmpty (L.Relations l) :=
  ⟨fun h _ hl => ⟨fun R => not_rePred_finValid R hl h⟩,
    fun hmon => (computablePred_finValid_of_monadic hmon).to_re⟩

/-- For a finite relational language `L`, finite unsatisfiability of first-order sentences is
recursively enumerable if and only if every relation symbol of `L` has arity at most `1` (in which
case finite satisfiability is decidable). -/
theorem rePred_not_finSat_iff :
    REPred (fun φ : L.Sentence => ¬FinSat φ) ↔ ∀ l, 2 ≤ l → IsEmpty (L.Relations l) :=
  ⟨fun h _ hl => ⟨fun R => not_rePred_not_finSat R hl h⟩,
    fun hmon => (computablePred_finSat_of_monadic hmon).not.to_re⟩

end FirstOrder.Language.Sentence
