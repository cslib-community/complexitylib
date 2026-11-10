/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Transducer
public import CslibFrontier.Logics.FirstOrder.Ordered.DomainInterpretation.Encoding
public import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.DomainInterpretation
public import CslibFrontier.Logics.FirstOrder.Ordered.Reduction

/-!
# Ordered interpretations in logarithmic space

The encoded map of a fixed ordered interpretation with a domain formula is computed by the
domain-counting transducer of `Cslib.Logic.FO.Interpretation.computableInLogSpace_encodedMapWith`,
instantiated with the ordered formula compiler: canonical numeric atoms (order, `BIT`, `0`, `1`,
`max`) are computed from cardinality and indices, and no numeric tables are supplied. The
coordinates are enumerated by `Fin.revPerm`, so that tuple indices are lexicographic ranks. The
transducer checks the source shape and size before emitting output, then writes the unary count of
the domain tuples and each target relation table over their ranks.

A full-tuple interpretation is the instance with domain `⊤`, through
`FullTupleInterpretation.encodedMap_toDomainInterpretation`; it has no separate program.

## Main definitions

* `Cslib.Logic.FO.Ordered.ModelChecker.formulaCompiler`: the ordered formula compiler.

## Main results

* `Cslib.Logic.FO.Ordered.DomainInterpretation.encodedMap_eq_encodedMapWith`: the encoded image is
  the output of the domain-counting transducer.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.computableInLogSpace_encodedMap`: ordered
  interpretations with a domain formula are computed in logarithmic space.
* `Cslib.Logic.FO.Ordered.IsDomainMap.exists_computableInLogSpace`: domain maps are simulated by
  logspace maps of encodings, the hypothesis of `Cslib.Complexity.ManyOneReducibleBy.lift`.
* `Cslib.Logic.FO.Ordered.DomainInterpretation.logSpaceReducible`: admissible interpretations
  reducing one ordered query to another induce logspace reductions of their encodings.
* `Cslib.Logic.FO.Ordered.Reduces.logSpaceReducible`: **first-order reductions are logspace
  reductions**; `Reduces.encodedLanguage_mem_L` and `Reduces.encodedLanguage_mem_P` give closure of
  `L` and `P`.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.computableInLogSpace_encodedMap`: the full-domain
  instance.
* `Cslib.Logic.FO.Ordered.FullTupleInterpretation.logSpaceReducible_onSentence`: the exact map
  reduces the pulled-back ordered query to the target query.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 3.1 and Propositions 3.5/3.10.
  Capture remains open.
* The order-free interpretation writer, shared counter-program simulation and Christian
  Reitwiessner's native arithmetic are reused with their source authorship retained.
-/

@[expose] public section

open FirstOrder Language Structure Turing

namespace Cslib.Logic.FO.Ordered

open Vocabulary.ModelChecker
open FO.Interpretation (modelCard rankEquiv rankEquiv_apply_val domainRank_mono)

namespace ModelChecker

variable {L : Language} [L.IsRelational] (v : Vocabulary L)

/-- The ordered formula compiler: canonical numeric atoms are computed natively, input atoms read
from the input tables, and inputs of size below two are inadmissible. -/
def formulaCompiler : FormulaCompiler v (language L) where
  minCard := 2
  expand hn s :=
    letI := s
    letI : Fact (2 ≤ _) := ⟨hn⟩
    inferInstance
  atomic := atomicCompiler v
  atomic_correct {a} ha hn _ fv base val :=
    letI : Fact (2 ≤ a.1) := ⟨hn⟩
    atomicCompiler_correct ha fv base val

end ModelChecker

namespace DomainInterpretation

variable {L L' : Language} [L.IsRelational] [L'.IsRelational] {k : ℕ}
  (I : DomainInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

/-- The encoded image is the output of the domain-counting transducer with the ordered formula
compiler, numbering coordinates in reverse so that tuple indices are lexicographic ranks. -/
theorem encodedMap_eq_encodedMapWith :
    I.encodedMap v v' =
      I.toFOInterpretation.encodedMapWith (ModelChecker.formulaCompiler v) v' Fin.revPerm := by
  funext a
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · obtain ⟨ha, hn⟩ := h
    rw [I.encodedMap_of_admissible v v' ha hn,
      I.toFOInterpretation.encodedMapWith_of_admissible _ v' _ ha hn]
    let M := decoded v a hn
    let J := I.toFOInterpretation
    let _ := (ModelChecker.formulaCompiler v).expand hn (v.decode a)
    let g : Fin (modelCard J Fin.revPerm a.1) → Fin k → Fin M.size :=
      fun i => ((rankEquiv J Fin.revPerm a.1).symm i).1
    have hrank (i) : J.domainRank Fin.revPerm a.1 (lexRank (g i)) = i := by
      have hi := congrArg Fin.val ((rankEquiv J Fin.revPerm a.1).apply_symm_apply i)
      rw [rankEquiv_apply_val] at hi
      exact hi
    obtain ⟨hc, hu⟩ := I.unrank_eq_of_strictMono (M := M) g
      (fun i => ((rankEquiv J Fin.revPerm a.1).symm i).2)
      (fun x hx => ⟨rankEquiv J Fin.revPerm a.1 (Interpretation.Model.mk x hx), by
        simp only [g, Equiv.symm_apply_apply]
        rfl⟩)
      (fun i j hij => by
        change lexRank (g i) < lexRank (g j)
        by_contra hle
        have hmono := domainRank_mono (I := J) (e := Fin.revPerm) (n := a.1) (not_lt.mp hle)
        rw [hrank, hrank] at hmono
        have := Fin.lt_def.mp hij
        omega)
    let _ := I.inputStructure M
    refine v'.encode_congr _ _ hc fun R x => ?_
    change (I.rel R).Realize (fun p => I.unrank M (x p.1) p.2) ↔
      (I.rel R).Realize (fun p => g (Fin.cast hc (x p.1)) p.2)
    simp only [hu]
  · rw [I.encodedMap_of_not_admissible v v' h,
      I.toFOInterpretation.encodedMapWith_of_not_admissible _ v' _ h]

/-- **Ordered interpretations with a domain formula are computed in logarithmic space.** For a
fixed interpretation and fixed vocabularies, the encoded image, numbered by lexicographic rank of
the domain tuples, is computed by a native transducer whose work space is logarithmic in the full
encoded input length. The domain may have fewer than two tuples. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v') encStructure encStructure := by
  rw [encodedMap_eq_encodedMapWith]
  exact I.toFOInterpretation.computableInLogSpace_encodedMapWith _ v' _

end DomainInterpretation

variable {L L' : Language} [L.IsRelational] [L'.IsRelational] (v : Vocabulary L)
  (v' : Vocabulary L')

/-- **Domain maps are simulated in logarithmic space.** Every image map of an admissible ordered
interpretation with a domain formula is simulated, through partial decoding, by a map of encodings
computable in logarithmic space: its encoded map. -/
theorem IsDomainMap.exists_computableInLogSpace {f : Structure L → Structure L'}
    (hf : IsDomainMap f) :
    ∃ F, MultiTapeTM.ComputableInLogSpace F encStructure encStructure ∧
      ∀ a, decode? v' (F a) = (decode? v a).map f :=
  let ⟨_, I, hI, hf⟩ := hf
  ⟨I.encodedMap v v', I.computableInLogSpace_encodedMap v v', hf ▸ I.decode?_encodedMap v v' hI⟩

/-- **Ordered interpretations are logspace reductions.** An admissible ordered interpretation with
a domain formula whose image map reduces the query `K` to `K'` induces a logspace many-one
reduction between their encoded query languages. -/
theorem DomainInterpretation.logSpaceReducible {k : ℕ} (I : DomainInterpretation L L' k)
    (hI : I.Admissible) {K : Query L} {K' : Query L'} (hK : ∀ M, M ∈ K ↔ I.map hI M ∈ K') :
    Complexity.LogSpaceReducible encStructure encStructure (K.encodedLanguage v)
      (K'.encodedLanguage v') := by
  rw [K.encodedLanguage_eq, K'.encodedLanguage_eq]
  exact Complexity.logSpaceReducible_iff_manyOneReducibleBy.mpr <|
    Complexity.ManyOneReducibleBy.lift (decode? v) (decode? v')
      (fun _ hf => IsDomainMap.exists_computableInLogSpace v v' hf) ⟨_, I.isDomainMap hI, hK⟩

namespace Reduces

variable {K : Query L} {K' : Query L'}

/-- **First-order reductions are logspace reductions** [Immerman1999, Theorem 3.1 and the remark
after Definition 2.14]: a first-order reduction of the ordered query `K` to `K'` induces a
logspace many-one reduction between their encoded query languages. The numeric certificate of the
reduction is not used; the transducer computes ranks by counting. The closure of `L` and `P` under
first-order reductions, `encodedLanguage_mem_L` and `encodedLanguage_mem_P`, are the corollaries of
[Immerman1999, Proposition 3.10]. -/
theorem logSpaceReducible (h : Reduces K K') :
    Complexity.LogSpaceReducible encStructure encStructure (K.encodedLanguage v)
      (K'.encodedLanguage v') := by
  rw [K.encodedLanguage_eq, K'.encodedLanguage_eq]
  exact Complexity.logSpaceReducible_iff_manyOneReducibleBy.mpr <|
    (Complexity.ManyOneReducibleBy.mono (fun _ hf => IsFirstOrderMap.isDomainMap hf) h).lift
      (decode? v) (decode? v') fun _ hf => IsDomainMap.exists_computableInLogSpace v v' hf

/-- Encoded ordered queries in `L` are closed under first-order reductions. -/
theorem encodedLanguage_mem_L (h : Reduces K K')
    (hL : K'.encodedLanguage v' ∈ Complexity.L encStructure) :
    K.encodedLanguage v ∈ Complexity.L encStructure :=
  (h.logSpaceReducible v v').mem_L hL

/-- Encoded ordered queries in `P` are closed under first-order reductions. -/
theorem encodedLanguage_mem_P (h : Reduces K K')
    (hP : K'.encodedLanguage v' ∈ Complexity.P encStructure) :
    K.encodedLanguage v ∈ Complexity.P encStructure :=
  (h.logSpaceReducible v v').polyTimeReducible.mem_P hP

end Reduces

end Cslib.Logic.FO.Ordered

namespace Cslib.Logic.FO.Ordered.FullTupleInterpretation

variable {L L' : Language} [L.IsRelational] [L'.IsRelational] {k : ℕ}
  (I : FullTupleInterpretation L L' k) (v : Vocabulary L) (v' : Vocabulary L')

/-- The actual canonical full-tuple encoded map is computed by a native logspace transducer.
The dimension, formulas and vocabularies are fixed. Space is logarithmic in full encoded input
length; the unary target size and relation tables are streamed through the write-only output.
It is the domain-counting transducer for the full domain. -/
theorem computableInLogSpace_encodedMap :
    MultiTapeTM.ComputableInLogSpace (I.encodedMap v v') encStructure encStructure := by
  rw [← I.encodedMap_toDomainInterpretation v v']
  exact I.toDomainInterpretation.computableInLogSpace_encodedMap v v'

/-- For positive tuple dimension, the encoded map belongs to the target ordered query language if
and only if the source belongs to the pulled-back ordered query language. -/
theorem mem_queryLanguage_encodedMap_iff (hk : 0 < k) (φ : (language L').Sentence)
    {a : EncodedStructure} :
    I.encodedMap v v' a ∈ queryLanguage v' φ ↔ a ∈ queryLanguage v (I.onSentence φ) := by
  by_cases h : v.WellFormed a ∧ 2 ≤ a.1
  · obtain ⟨ha, hn⟩ := h
    let : Fact (2 ≤ a.1) := ⟨hn⟩
    let : Fact (2 ≤ (I.encodedMap v v' a).1) := ⟨I.two_le_card_encodedMap v v' hk ha hn⟩
    rw [mem_queryLanguage, mem_queryLanguage, I.wellFormed_encodedMap_iff]
    refine ⟨fun ⟨_, hφ⟩ => ⟨ha, ?_⟩, fun ⟨_, hφ⟩ => ⟨⟨ha, hn⟩, ?_⟩⟩
    · let _ := v.decode a
      let _ := I.modelStructure hk (n := a.1)
      let _ := I.inputStructure (n := a.1)
      let _ : Fact (2 ≤ a.1 ^ k) := ⟨two_le_pow (n := a.1) hk⟩
      let _ := v'.decode (I.encodedMap v v' a)
      rw [I.realize_onSentence hk φ, ← StrongHomClass.realize_sentence (I.modelEquiv hk) φ,
        StrongHomClass.realize_sentence (I.encodedModelEquiv v v' hk ha) φ]
      exact hφ
    · let _ := v.decode a
      let _ := I.modelStructure hk (n := a.1)
      let _ := I.inputStructure (n := a.1)
      let _ : Fact (2 ≤ a.1 ^ k) := ⟨two_le_pow (n := a.1) hk⟩
      let _ := v'.decode (I.encodedMap v v' a)
      rw [← StrongHomClass.realize_sentence (I.encodedModelEquiv v v' hk ha) φ,
        StrongHomClass.realize_sentence (I.modelEquiv hk) φ, ← I.realize_onSentence hk φ]
      exact hφ
  · refine iff_of_false ?_ ?_
    · intro hm
      exact h ((I.wellFormed_encodedMap_iff v v').mp hm.1)
    · rintro ⟨ha, hn, _⟩
      exact h ⟨ha, hn⟩

/-- For positive tuple dimension, the canonical full-tuple encoded map is a logspace many-one
reduction from the pulled-back ordered query language to the target ordered query language. -/
theorem logSpaceReducible_onSentence (hk : 0 < k) (φ : (language L').Sentence) :
    Complexity.LogSpaceReducible encStructure encStructure
      (queryLanguage v (I.onSentence φ)) (queryLanguage v' φ) :=
  ⟨I.encodedMap v v', I.computableInLogSpace_encodedMap v v',
    fun _ => (I.mem_queryLanguage_encodedMap_iff v v' hk φ).symm⟩

end Cslib.Logic.FO.Ordered.FullTupleInterpretation
