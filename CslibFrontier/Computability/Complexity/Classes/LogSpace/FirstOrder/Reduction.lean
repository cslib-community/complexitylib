/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Transducer
public import CslibFrontier.Logics.FirstOrder.Interpretation.Encoding

/-!
# Order-free first-order interpretations as logarithmic-space reductions

For finite relational vocabularies, an order-free first-order interpretation induces a
logarithmic-space transducer on structure encodings. It is the domain-counting transducer of
`Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMapWith`, instantiated with the
order-free formula compiler, which reads relation atoms from the input tables and admits every
cardinality. The transducer checks the input shape, counts domain tuples to emit the unary output
cardinality, and emits each relation table by repeatedly reconstructing the tuples of the
requested ranks. Neither the output structure nor its tables are stored.

Inputs `(n, tables)` with invalid table shapes map to a fixed malformed target instance.
Raw bit strings outside the image of `encStructure` are outside the encoded-input contract.
Empty structures, empty domains,
nullary relations, and zero-dimensional interpretations are included. Isomorphism closure of
the target query makes the choice of numbering immaterial.

These are order-free interpretations, without built-in order or `BIT`. The ordered instance of
the same transducer, which computes the canonical numeric atoms, is
`Cslib.Logic.FO.Ordered.DomainInterpretation.computableInLogSpace_encodedMap`.

## Main definitions

* `Cslib.Logic.Vocabulary.ModelChecker.formulaCompiler`: the order-free formula compiler.

## Main results

* `Cslib.Logic.FO.Interpretation.encodedMap_eq_encodedMapWith`: the encoded map is the output of
  the domain-counting transducer.
* `Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMap`: the encoded map has a total
  logarithmic-space transducer.
* `Cslib.Logic.FO.Reduces.logSpaceReducible`: order-free interpretation reductions induce
  logspace many-one reductions between query languages.
* `Cslib.Logic.FO.Reduces.queryLanguage_mem_L` and
  `Cslib.Logic.FO.Reduces.queryLanguage_mem_P`: closure of encoded queries in `L` and `P`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [M. Sipser, *Introduction to the Theory of Computation*, Section 8.5][Sipser2013]
-/

@[expose] public section

universe u v u' v'

open FirstOrder Language Structure CategoryTheory Turing

namespace Cslib.Logic

/-- The order-free formula compiler: formulas over the input vocabulary itself, read from the
input tables, with every cardinality admissible. -/
def Vocabulary.ModelChecker.formulaCompiler {L : Language.{u, v}} [L.IsRelational]
    (v : Vocabulary L) : Vocabulary.ModelChecker.FormulaCompiler v L where
  minCard := 0
  expand _ s := s
  atomic := Vocabulary.ModelChecker.atomicCompiler v
  atomic_correct ha _ _ fv base val := Vocabulary.ModelChecker.atomicCompiler_correct ha fv base val

namespace FO.Interpretation

open Vocabulary.ModelChecker

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  {ι : Type} {d : ℕ} (I : Interpretation L L' ι) (v : Vocabulary L) (v' : Vocabulary L')
  (e : ι ≃ Fin d)

/-- The order-free encoded map is the domain-counting transducer's output with the order-free
formula compiler. -/
theorem encodedMap_eq_encodedMapWith :
    I.encodedMap v v' e = I.encodedMapWith (formulaCompiler v) v' e := by
  funext a
  by_cases ha : v.WellFormed a
  · rw [I.encodedMap_of_wellFormed v v' e ha,
      I.encodedMapWith_of_admissible _ v' e ha (Nat.zero_le _)]
    rfl
  · rw [I.encodedMap_of_not_wellFormed v v' e ha,
      I.encodedMapWith_of_not_admissible _ v' e fun h => ha h.1]

/-- Computing an order-free first-order interpretation on encoded finite relational structures
uses logarithmic work space. The output is streamed, including its unary cardinality frame;
malformed inputs map to malformed outputs. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v' e) encStructure encStructure := by
  rw [encodedMap_eq_encodedMapWith]
  exact I.computableInLogSpace_encodedMapWith _ v' e

end FO.Interpretation

end Cslib.Logic

namespace Cslib.Logic.FO

variable {L : Language.{u, v}} {L' : Language.{u', v'}} [L.IsRelational] [L'.IsRelational]
  (v : Vocabulary L) (v' : Vocabulary L')
  {K : Set (Bundled.{0} L.Structure)} {K' : Set (Bundled.{0} L'.Structure)}

/-- An order-free first-order interpretation reduction induces a logspace many-one reduction
between the query languages, provided the target class is closed under isomorphism. The
transducer maps malformed instances to a fixed malformed target instance outside the target query
language, and includes empty structures and empty domains. -/
theorem Reduces.logSpaceReducible (h : Reduces K K') (hK' : IsoClosed K') :
    Complexity.LogSpaceReducible encStructure encStructure (v.queryLanguage K)
      (v'.queryLanguage K') := by
  classical
  obtain ⟨ι, hι, I, hI⟩ := h
  let _ := Fintype.ofFinite ι
  let e := Fintype.equivFin ι
  refine ⟨I.encodedMap v v' e, I.computableInLogSpace_encodedMap v v' e, fun a => ?_⟩
  rw [I.mem_queryLanguage_encodedMap_iff v v' e hK', Vocabulary.mem_queryLanguage]
  have : Finite (v.decoded a) := inferInstanceAs (Finite (Fin a.1))
  exact and_congr_right fun _ => hI (v.decoded a)

/-- Query languages in `L` are closed under order-free first-order interpretation reductions
with an isomorphism-closed target class. -/
theorem Reduces.queryLanguage_mem_L (h : Reduces K K') (hK' : IsoClosed K')
    (hL : v'.queryLanguage K' ∈ Complexity.L encStructure) :
    v.queryLanguage K ∈ Complexity.L encStructure :=
  (h.logSpaceReducible v v' hK').mem_L hL

/-- Query languages in `P` are closed under order-free first-order interpretation reductions
with an isomorphism-closed target class. -/
theorem Reduces.queryLanguage_mem_P (h : Reduces K K') (hK' : IsoClosed K')
    (hP : v'.queryLanguage K' ∈ Complexity.P encStructure) :
    v.queryLanguage K ∈ Complexity.P encStructure :=
  (h.logSpaceReducible v v' hK').polyTimeReducible.mem_P hP

end Cslib.Logic.FO
