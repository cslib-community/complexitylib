/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Fagin.Converse
public import CslibFrontier.Logics.SecondOrder.Grounding

/-!
# SAT completeness under order-free first-order interpretations

The reductions in this module use order-free first-order interpretations. Input structures have
no built-in order or numeric predicates; these results are order-free variants of the standard ones.

The class `cnf.SAT` of satisfiable CNF structures has its query language in `NP`
(`Cslib.Logic.FO.cnf.queryLanguage_SAT_mem_NP`). Every isomorphism-closed class of finite
structures whose query language is in `NP` and which contains every empty structure is order-free
reducible to it (`Cslib.Logic.FO.cnf.reduces_SAT_of_queryLanguage_mem_NP`), and conversely every
class order-free reducible to SAT is in `NP`
(`Cslib.Logic.FO.cnf.queryLanguage_mem_NP_of_reduces_SAT`). So the classes containing every empty
structure that are order-free reducible to SAT are exactly the isomorphism-closed classes in `NP`
(`Cslib.Logic.FO.cnf.reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP`). Without the hypothesis
on empty structures, every isomorphism-closed class in `NP` is order-free reducible to SAT on
the nonempty finite structures
(`Cslib.Logic.FO.cnf.exists_interpretation_SAT_of_queryLanguage_mem_NP`).

This adapts the descriptive form of the Cook–Levin theorem [Immerman, Chapter 7][Immerman1999].
Immerman's structures are ordered and have at least two elements; his reductions are projections;
here the structures are unordered and the reductions are first-order interpretations, with
quantifiers. Neither statement implies the other. The hypothesis on empty structures comes from
the reduction: an interpretation of positive dimension maps every empty input to the empty CNF
structure, which is satisfiable. The proofs combine Fagin's theorem
(`Cslib.Logic.ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP`) with the grounding of
existential second-order sentences (`Cslib.Logic.ESO.Definable.reduces_SAT`). The machine-level
Cook–Levin theorem, for the encoded problem `Cslib.Complexity.SAT` under polynomial-time
reductions, is proved separately.

## Main results

* `Cslib.Logic.FO.cnf.queryLanguage_SAT_mem_NP`, `Cslib.Logic.FO.cnf.queryLanguage_ThreeSAT_mem_NP`:
  SAT and 3SAT are in `NP`.
* `Cslib.Logic.FO.cnf.reduces_SAT_of_queryLanguage_mem_NP`: SAT is NP-hard under order-free
  reductions, for classes containing every empty structure.
* `Cslib.Logic.FO.cnf.exists_interpretation_SAT_of_queryLanguage_mem_NP`: SAT is NP-hard under
  order-free reductions correct on the nonempty structures.
* `Cslib.Logic.FO.cnf.queryLanguage_mem_NP_of_reduces_SAT`: classes reducible to SAT are in `NP`.
* `Cslib.Logic.FO.cnf.reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP`: the classes containing
  every empty structure that are order-free reducible to SAT are the isomorphism-closed classes in
  `NP`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [R. Fagin, *Generalized first-order spectra and polynomial-time recognizable sets*][Fagin1974]
-/

public section

universe u v

namespace Cslib.Logic.FO.cnf

open FirstOrder Language Structure CategoryTheory Cslib.Complexity

/-- **SAT is in NP**: the encodings of the satisfiable CNF structures form a problem in `NP`. -/
theorem queryLanguage_SAT_mem_NP : vocabulary.queryLanguage SAT ∈ NP encStructure :=
  definable_SAT.queryLanguage_mem_NP vocabulary

/-- **3SAT is in NP.** -/
theorem queryLanguage_ThreeSAT_mem_NP : vocabulary.queryLanguage ThreeSAT ∈ NP encStructure :=
  definable_ThreeSAT.queryLanguage_mem_NP vocabulary

variable {L : Language.{u, v}} [L.IsRelational] (v : Vocabulary L)

/-- **SAT is NP-hard under order-free reductions, for classes containing every empty structure**:
every isomorphism-closed class of finite structures whose query language is in `NP` and which
contains every empty structure is order-free reducible to SAT. -/
theorem reduces_SAT_of_queryLanguage_mem_NP {K : Set (Bundled.{0} L.Structure)} (hK : IsoClosed K)
    (hNP : v.queryLanguage K ∈ NP encStructure)
    (hempty : ∀ M : Bundled.{0} L.Structure, IsEmpty M → M ∈ K) : Reduces K SAT :=
  (ESO.Definable.of_queryLanguage_mem_NP v hK hNP).reduces_SAT hempty

/-- **SAT is NP-hard under order-free reductions correct on the nonempty structures**: for every
isomorphism-closed class of finite structures whose query language is in `NP`, some first-order
interpretation maps every nonempty finite structure inside SAT exactly when it is in the class.
This is an order-free variant of [Immerman, Chapter 7][Immerman1999]; the structures here have
no built-in order, unlike Immerman's ordered structures of at least two elements. -/
theorem exists_interpretation_SAT_of_queryLanguage_mem_NP {K : Set (Bundled.{0} L.Structure)}
    (hK : IsoClosed K) (hNP : v.queryLanguage K ∈ NP encStructure) :
    ∃ (ι : Type) (_ : Finite ι) (I : Interpretation L cnf ι),
      ∀ (M : Bundled.{0} L.Structure) [Finite M] [Nonempty M],
        M ∈ K ↔ Bundled.of (c := cnf.Structure) (I.Model M) ∈ SAT :=
  (ESO.Definable.of_queryLanguage_mem_NP v hK hNP).exists_interpretation_SAT_of_nonempty

/-- **Classes order-free reducible to SAT are in NP.** -/
theorem queryLanguage_mem_NP_of_reduces_SAT {K : Set (Bundled.{0} L.Structure)}
    (h : Reduces K SAT) : v.queryLanguage K ∈ NP encStructure :=
  (definable_SAT.of_reduces h).queryLanguage_mem_NP v

/-- **The classes order-free reducible to SAT are the NP classes**: a class containing every empty
structure is order-free reducible to SAT exactly when it is closed under isomorphism and its
query language is in `NP`. -/
theorem reduces_SAT_iff_isoClosed_and_queryLanguage_mem_NP {K : Set (Bundled.{0} L.Structure)}
    (hempty : ∀ M : Bundled.{0} L.Structure, IsEmpty M → M ∈ K) :
    Reduces K SAT ↔ IsoClosed K ∧ v.queryLanguage K ∈ NP encStructure :=
  (ESO.definable_iff_reduces_SAT hempty).symm.trans
    (ESO.definable_iff_isoClosed_and_queryLanguage_mem_NP v)

end Cslib.Logic.FO.cnf
