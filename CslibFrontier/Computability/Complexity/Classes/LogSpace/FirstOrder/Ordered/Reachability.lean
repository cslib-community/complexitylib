/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.ConfigurationGraph
public import CslibFrontier.Computability.Complexity.Problems.STCON
public import CslibFrontier.Logics.FirstOrder.Ordered.Problems.Reachability
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.Ordered.Reduction
import CslibFrontier.Computability.Complexity.Classes.LogSpace.FirstOrder.TransitiveClosure.Converse
import CslibFrontier.Computability.Complexity.Problems.STCON.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Words
import CslibFrontier.Foundations.Relation.Transport
import CslibFrontier.Logics.FirstOrder.Ordered.FullTuple.Composition

/-!
# Native NL membership and unconditional first-order NL-completeness of REACH

On canonically ordered finite directed graphs (`Fin n` with `2 ≤ n`, directed arcs and self-loops
allowed), the `0`-to-`max` reachability query `Cslib.Logic.FO.Ordered.Reach` (`REACH` of
[Immerman1999, Section 3.3 and Theorem 3.16]) belongs to native `NL` at the source-only structure
encoding `encStructure`, is complete for every ordered query in native `NL` under ordered
first-order reductions (`Cslib.Logic.FO.Ordered.Reduces`), and is interreducible in deterministic
logarithmic space with the adjacency-matrix connectivity problem `Cslib.Complexity.STCON`
(`encSTCON`).

* **Native `NL` membership** (`reach_encodedLanguage_mem_NL`, `stReach_encodedLanguage_mem_NL`):
  reuses the compiled FO(TC) model checker (`PosTCDefinable.encodedLanguage_mem_NL`) on
  `posTCDefinable_Reach` without a separate reachability program.
* **Unconditional ordered first-order `NL`-completeness** ([Immerman1999, Theorem 3.16],
  `exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL`,
  `reduces_Reach_of_encodedLanguage_mem_NL`, `reduces_Reach_iff_encodedLanguage_mem_NL`): for any
  relational language `L`, vocabulary `v`, and ordered query `K` with
  `K.encodedLanguage v ∈ NL encStructure`, the register configuration graph of a logarithmic-space
  decider is embedded into `Reach` by `configurationGraphInterpretation` (built from
  `boundedReachInterpretation`, `startFormula`, `stepFormula` and `acceptFormula`) on a polynomial
  power universe `v.orderedPowerInterpretation K' har`, and flattened to one full-tuple
  interpretation via `FullTupleInterpretation.comp`. Because `Reach` pulls back positive FO(TC)
  definability (`PosTCDefinable.of_reduces_Reach`), transitivity of `Ordered.Reduces` through
  `Reach` also closes native `NL` under arbitrary ordered first-order reductions
  (`Reduces.encodedLanguage_mem_NL`).
* **Semantic and logspace bridges to `STCON`** (`Reach.toSTCONInstance`,
  `STCONInstance.toOrderedGraph`, `reach_logSpaceReducible_STCON`, `stcon_logSpaceReducible_Reach`,
  `reach_logSpaceComplete_NL`): explicit instance translations in both directions (handling
  `I.n = 1` and `I.s = I.t`), together with bidirectional `LogSpaceReducible` reductions between
  `encStructure` and `encSTCON`, establishing `LogSpaceComplete NL encStructure` for `Reach`.

## Main definitions

* `Cslib.Complexity.ConfigurationGraph.configurationGraphInterpretation`: full-tuple interpretation
  embedding register-tuple reachability of a nondeterministic machine into `Reach`.
* `Cslib.Logic.FO.Ordered.Reach.toSTCONInstance`: view an ordered graph structure as an
  `STCONInstance` from `0` to `max`.
* `Cslib.Complexity.STCONInstance.toOrderedGraph`: embed any `STCONInstance` (including `n = 1`
  and `s = t`) into an ordered graph on `Fin (I.n + 2)` preserving reachability via `Reach`.

## Main results

* `Cslib.Logic.FO.Ordered.reach_encodedLanguage_mem_NL`,
  `Cslib.Logic.FO.Ordered.stReach_encodedLanguage_mem_NL`: native `NL` membership of `Reach` and
  `STReach` at `encStructure`.
* `Cslib.Complexity.ConfigurationGraph.mem_Reach_configurationGraphInterpretation`: exact machine
  acceptance semantics of `configurationGraphInterpretation`.
* `Cslib.Logic.FO.Ordered.exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL`: every
  ordered query in native `NL` reduces to `Reach` by a single full-tuple interpretation.
* `Cslib.Logic.FO.Ordered.reduces_Reach_of_encodedLanguage_mem_NL`,
  `Cslib.Logic.FO.Ordered.encodedLanguage_mem_NL_of_reduces_Reach`,
  `Cslib.Logic.FO.Ordered.reduces_Reach_iff_encodedLanguage_mem_NL`: unconditional ordered
  first-order `NL`-completeness of `Reach` [Immerman1999, Theorem 3.16].
* `Cslib.Logic.FO.Ordered.Reduces.encodedLanguage_mem_NL`: encoded ordered queries in native `NL`
  are closed under ordered first-order reductions.
* `Cslib.Logic.FO.Ordered.Reach.toSTCONInstance_mem_STCON`,
  `Cslib.Complexity.STCONInstance.toOrderedGraph_mem_Reach`: exact semantic `STCON` bridges.
* `Cslib.Logic.FO.Ordered.reach_logSpaceReducible_STCON`,
  `Cslib.Logic.FO.Ordered.stcon_logSpaceReducible_Reach`,
  `Cslib.Logic.FO.Ordered.reach_logSpaceHard_NL`,
  `Cslib.Logic.FO.Ordered.reach_logSpaceComplete_NL`: logspace interreducibility with `STCON` and
  logspace `NL`-completeness of `Reach`.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Section 3.3, Theorem 3.16 and
  Exercise 3.20 (pp. 64–66).
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013], Section 8.4 and
  Theorem 8.25.
-/

public section

open FirstOrder Language Turing Cslib.Turing Cslib.Logic Cslib.Logic.FO Cslib.Logic.FO.Ordered
open Turing.MultiTapeNTM.ConfigurationGraph

/-! ### Configuration graph as a full-tuple interpretation into `Reach` -/

namespace Cslib.Complexity.ConfigurationGraph

variable (L : Language) {k : ℕ} {State : Type} [Fintype State]

/-- **Configuration-graph interpretation into `Reach`**: on any universe `Fin N` (`2 ≤ N`), tuples
of dimension `Fintype.card (Register k) + 2` step from `(0, …, 0)` to `(0, max, X)` at
`startFormula`, follow `stepFormula` along interior tuples `(0, max, X)`, and step to
`(max, …, max)` at `acceptFormula`. -/
noncomputable def configurationGraphInterpretation
    (inputFormula : Option Bool → (language L).Formula (Fin 1))
    (lengthFormula : (language L).Formula (Fin 1))
    (ntm : MultiTapeNTM k Bool State) :
    FullTupleInterpretation L Language.graph (Fintype.card (Register k) + 2) :=
  boundedReachInterpretation
    (startFormula L ntm fun r => .var (Fintype.equivFin (Register k) r))
    (stepFormula L inputFormula lengthFormula ntm
      (fun r => .var (.inl (Fintype.equivFin (Register k) r)))
      (fun r => .var (.inr (Fintype.equivFin (Register k) r))))
    (acceptFormula L State fun r => .var (Fintype.equivFin (Register k) r))

variable {L}

/-- **Machine acceptance via `configurationGraphInterpretation`**: on any ordered structure `M`
whose universe `Fin M.size` exceeds `w.length` and holds every reachable register tuple of `ntm`
on `w`, the image graph belongs to `Reach` if and only if `ntm.Accepts w`. -/
theorem mem_Reach_configurationGraphInterpretation
    {inputFormula : Option Bool → (language L).Formula (Fin 1)}
    {lengthFormula : (language L).Formula (Fin 1)} {w : List Bool}
    (M : Ordered.Structure L)
    (hinput : ∀ s (a : Fin M.size), (inputFormula s).Realize ![a] ↔ inputAt w a.val = s)
    (hlen : ∀ a : Fin M.size, lengthFormula.Realize ![a] ↔ w.length = a.val)
    (hn : w.length < M.size) (ntm : MultiTapeNTM k Bool State)
    (hfit : ∀ v, Relation.ReflTransGen ntm.ViewStep (ntm.initView w) v →
      Fits M.size (registers v))
    {hI : (configurationGraphInterpretation L inputFormula lengthFormula
      ntm).toDomainInterpretation.Admissible} :
    (configurationGraphInterpretation L inputFormula lengthFormula ntm).toDomainInterpretation.map
      hI M ∈ Reach ↔ ntm.Accepts w := by
  let E : (Fin (Fintype.card (Register k)) → Fin M.size) ≃ (Register k → Fin M.size) :=
    { toFun := fun x r => x (Fintype.equivFin (Register k) r)
      invFun := fun x i => x ((Fintype.equivFin (Register k)).symm i)
      left_inv := fun x => funext fun i => by simp only [Equiv.apply_symm_apply]
      right_inv := fun x => funext fun r => by simp only [Equiv.symm_apply_apply] }
  refine (mem_Reach_boundedReachInterpretation _ _ _ M).trans ?_
  rw [accepts_iff_registerStep_fin hfit]
  have hsrc (x : Fin (Fintype.card (Register k)) → Fin M.size) :
      (startFormula L ntm fun r => Term.var (Fintype.equivFin (Register k) r)).Realize x ↔
        ∀ r, (E x r).val = startRegisters ntm r := by
    simp only [realize_startFormula, Term.realize_var, E, Equiv.coe_fn_mk]
  have hstep (a b : Fin (Fintype.card (Register k)) → Fin M.size) :
      (stepFormula L inputFormula lengthFormula ntm
        (fun r => Term.var (.inl (Fintype.equivFin (Register k) r)))
        (fun r => Term.var (.inr (Fintype.equivFin (Register k) r)))).Realize (Sum.elim a b) ↔
        RegisterStep ntm w (fun r => (E a r).val) (fun r => (E b r).val) := by
    simp only [realize_stepFormula hinput hlen hn, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
      E, Equiv.coe_fn_mk]
  have htgt (y : Fin (Fintype.card (Register k)) → Fin M.size) :
      (acceptFormula L State fun r => Term.var (Fintype.equivFin (Register k) r)).Realize y ↔
        (E y .control).val = stateCode (none : Option State) ∧ (E y .output).val = 1 := by
    simp only [realize_acceptFormula, Term.realize_var, E, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨x, y, hx, hxy, hy⟩
    obtain ⟨hc, ho⟩ := (htgt y).mp hy
    exact ⟨E x, E y, (hsrc x).mp hx,
      (Relation.reflTransGen_equiv_iff E hstep x y).mp hxy, hc, ho⟩
  · rintro ⟨x, y, hx, hxy, hc, ho⟩
    refine ⟨E.symm x, E.symm y, ?_, ?_, ?_⟩
    · exact (hsrc _).mpr (by simpa only [Equiv.apply_symm_apply] using hx)
    · exact (Relation.reflTransGen_equiv_iff E hstep (E.symm x) (E.symm y)).mpr
        (by simpa only [Equiv.apply_symm_apply] using hxy)
    · exact (htgt _).mpr (by simpa only [Equiv.apply_symm_apply] using ⟨hc, ho⟩)

end Cslib.Complexity.ConfigurationGraph

/-! ### Native `NL` membership and unconditional ordered first-order `NL`-completeness -/

namespace Cslib.Logic.FO.Ordered

open Cslib.Complexity Cslib.Complexity.ConfigurationGraph Turing.MultiTapeTM

/-- **`Reach` belongs to native `NL`** at the canonical structure encoding `encStructure`. -/
theorem reach_encodedLanguage_mem_NL :
    Reach.encodedLanguage graphVocabulary ∈ Complexity.NL encStructure :=
  posTCDefinable_Reach.encodedLanguage_mem_NL graphVocabulary

/-- **`STReach` belongs to native `NL`** at the canonical structure encoding `encStructure`. -/
theorem stReach_encodedLanguage_mem_NL :
    STReach.encodedLanguage stGraphVocabulary ∈ Complexity.NL encStructure :=
  (PosTCDefinable.of_reduces_Reach stReach_reduces_Reach).encodedLanguage_mem_NL stGraphVocabulary

private theorem mem_Reach_comp {L L' : Language} [L'.IsRelational] {k l : ℕ}
    (hk : 0 < k) (hl : 0 < l)
    (I : FullTupleInterpretation L L' k) (J : FullTupleInterpretation L' Language.graph l)
    (M : Structure L)
    {hcomp : (J.comp I).toDomainInterpretation.Admissible}
    {hJ : J.toDomainInterpretation.Admissible} :
    (J.comp I).toDomainInterpretation.map hcomp M ∈ Reach ↔
      J.toDomainInterpretation.map hJ
        ⟨M.size ^ k, FullTupleInterpretation.two_le_pow (n := M.size) hk,
          I.inputStructure (n := M.size)⟩ ∈ Reach := by
  let M' : Structure L' :=
    ⟨M.size ^ k, FullTupleInterpretation.two_le_pow (n := M.size) hk,
      I.inputStructure (n := M.size)⟩
  let _ := I.inputStructure (n := M.size)
  let _ : Fact (2 ≤ M.size ^ k) := ⟨FullTupleInterpretation.two_le_pow (n := M.size) hk⟩
  let _ := J.inputStructure (n := M.size ^ k)
  let _ : Fact (2 ≤ (M.size ^ k) ^ l) := ⟨FullTupleInterpretation.two_le_pow (n := M.size ^ k) hl⟩
  let _ := (J.comp I).inputStructure (n := M.size)
  let _ : Fact (2 ≤ M.size ^ (l * k)) :=
    ⟨FullTupleInterpretation.two_le_pow (n := M.size) (Nat.mul_pos hl hk)⟩
  let iso := J.compEquiv (n := M.size) I hk hl
  have hc₁ := J.card_toDomainInterpretation M'
  have hc₂ := (J.comp I).card_toDomainInterpretation M
  let e : J.toDomainInterpretation.map hJ M' ≃ (J.comp I).toDomainInterpretation.map hcomp M :=
    (finCongr hc₁).trans (iso.toEquiv.trans (finCongr hc₂.symm))
  have he_val (x : J.toDomainInterpretation.map hJ M') : (e x).val = x.val := rfl
  have he_zero : e 0 = 0 := Fin.ext rfl
  have he_max : e (J.toDomainInterpretation.map hJ M').maxElem =
      ((J.comp I).toDomainInterpretation.map hcomp M).maxElem := by
    apply Fin.ext
    change J.toDomainInterpretation.card M' - 1 = (J.comp I).toDomainInterpretation.card M - 1
    rw [hc₁, hc₂, ← pow_mul, Nat.mul_comm]
  have hedge (x y : J.toDomainInterpretation.map hJ M') :
      graphAdj (J.toDomainInterpretation.map hJ M') x y ↔
        graphAdj ((J.comp I).toDomainInterpretation.map hcomp M) (e x) (e y) := by
    rw [graphAdj, graphAdj, J.relMap_map_toDomainInterpretation hl,
      (J.comp I).relMap_map_toDomainInterpretation (Nat.mul_pos hl hk)]
    have hcast : Fin.cast hc₂ ∘ ![e x, e y] = iso ∘ (Fin.cast hc₁ ∘ ![x, y]) := by
      funext b
      cases b using Fin.cases with
      | zero => rfl
      | succ b' =>
        have hb' : b' = 0 := Subsingleton.elim _ _
        subst hb'
        rfl
    have hiso : (J.inputStructure (n := M.size ^ k)).RelMap Language.adj
        (Fin.cast hc₁ ∘ ![x, y]) ↔
        ((J.comp I).inputStructure (n := M.size)).RelMap Language.adj
          (iso ∘ (Fin.cast hc₁ ∘ ![x, y])) :=
      (iso.map_rel (.inl Language.adj) (Fin.cast hc₁ ∘ ![x, y])).symm
    rw [← hcast] at hiso
    exact hiso
  change Relation.ReflTransGen (graphAdj ((J.comp I).toDomainInterpretation.map hcomp M)) 0
      ((J.comp I).toDomainInterpretation.map hcomp M).maxElem ↔
    Relation.ReflTransGen (graphAdj (J.toDomainInterpretation.map hJ M')) 0
      (J.toDomainInterpretation.map hJ M').maxElem
  rw [← he_zero, ← he_max]
  exact (Relation.reflTransGen_equiv_iff e hedge 0
    (J.toDomainInterpretation.map hJ M').maxElem).symm

/-- **Explicit full-tuple reduction to `Reach` for every ordered query in native `NL`**
([Immerman1999, Theorem 3.16]): if `K.encodedLanguage v ∈ NL encStructure`, then some positive
dimension `d` and `FullTupleInterpretation L Language.graph d` reduce `K` to `Reach` on all
canonically ordered structures. -/
theorem exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL {L : Language}
    [L.IsRelational] (v : Vocabulary L) {K : Query L}
    (hNL : K.encodedLanguage v ∈ Complexity.NL encStructure) :
    ∃ (d : ℕ) (hd : 0 < d) (I : FullTupleInterpretation L Language.graph d),
      ∀ M : Structure L,
        M ∈ K ↔
          I.toDomainInterpretation.map (I.admissible_toDomainInterpretation hd) M ∈ Reach := by
  obtain ⟨k, State, _, ntm, c, hdec⟩ := hNL
  let _ := Fintype.ofFinite State
  obtain ⟨K', hK', har, hpow⟩ := v.exists_pow_fits State c
  let I := v.orderedPowerInterpretation K' har
  let J := configurationGraphInterpretation v.powerLanguage v.inputSymbol v.inputLength ntm
  have hl : 0 < Fintype.card (Register k) + 2 := Nat.zero_lt_succ _
  have hd : 0 < (Fintype.card (Register k) + 2) * K' := Nat.mul_pos hl hK'
  refine ⟨(Fintype.card (Register k) + 2) * K', hd, J.comp I, fun M => ?_⟩
  let a := encode v M
  have ha : v.WellFormed a := v.wellFormed_encode M (Equiv.refl M)
  obtain ⟨hdec_all, -⟩ := hdec
  obtain ⟨hspace, hacc⟩ := hdec_all a
  obtain ⟨hn, hfit⟩ := hpow a ha M.size_ge_two hspace
  change (encStructure a).length < M.size ^ K' at hn
  change ∀ u, _ → Fits (M.size ^ K') _ at hfit
  have hcomp := mem_Reach_comp (hcomp := (J.comp I).admissible_toDomainInterpretation hd)
    (hJ := J.admissible_toDomainInterpretation hl) hK' hl I J M
  have he : I.inputStructure (n := M.size) = v.powerStructure a (M.size ^ K') :=
    v.inputStructure_orderedPowerInterpretation K' har hK' M
  let P : Structure v.powerLanguage :=
    ⟨M.size ^ K', FullTupleInterpretation.two_le_pow (n := M.size) hK',
      v.powerStructure a (M.size ^ K')⟩
  have hM' : (⟨M.size ^ K', FullTupleInterpretation.two_le_pow (n := M.size) hK',
      I.inputStructure (n := M.size)⟩ : Structure v.powerLanguage) = P := by
    simp only [P, he]
  rw [hM'] at hcomp
  let _ : Fact (2 ≤ M.size ^ K') := ⟨FullTupleInterpretation.two_le_pow (n := M.size) hK'⟩
  let _ := v.powerStructure a (M.size ^ K')
  have hJ_reach : J.toDomainInterpretation.map (J.admissible_toDomainInterpretation hl) P ∈ Reach ↔
      ntm.Accepts (encStructure a) :=
    mem_Reach_configurationGraphInterpretation P
      (v.realize_inputSymbol ha hn) (v.realize_inputLength ha hn) hn ntm hfit
  exact (mem_encodedLanguage_encode v K M).symm.trans
    (hacc.trans (hJ_reach.symm.trans hcomp.symm))

/-- **Hardness of `Reach` for native `NL` under ordered first-order reductions**
([Immerman1999, Theorem 3.16]). -/
theorem reduces_Reach_of_encodedLanguage_mem_NL {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L}
    (hNL : K.encodedLanguage v ∈ Complexity.NL encStructure) :
    Reduces K Reach := by
  obtain ⟨d, hd, I, hI⟩ := exists_fullTupleInterpretation_Reach_of_encodedLanguage_mem_NL v hNL
  exact I.reduces hd hI

/-- Every ordered query that first-order reduces to `Reach` belongs to native `NL`. -/
theorem encodedLanguage_mem_NL_of_reduces_Reach {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} (h : Reduces K Reach) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  (PosTCDefinable.of_reduces_Reach h).encodedLanguage_mem_NL v

/-- **Unconditional ordered first-order `NL`-completeness of `Reach`**
([Immerman1999, Theorem 3.16]): for every finite relational vocabulary `v` and ordered query `K`,
`K` first-order reduces to `Reach` if and only if `K.encodedLanguage v ∈ NL encStructure`. -/
theorem reduces_Reach_iff_encodedLanguage_mem_NL {L : Language} [L.IsRelational]
    (v : Vocabulary L) {K : Query L} :
    Reduces K Reach ↔ K.encodedLanguage v ∈ Complexity.NL encStructure :=
  ⟨encodedLanguage_mem_NL_of_reduces_Reach v, reduces_Reach_of_encodedLanguage_mem_NL v⟩

/-- **Encoded ordered queries in native `NL` are closed under ordered first-order reductions**:
composing `h : Reduces K K'` with `K' ≤_fo Reach` reduces `K` to `Reach`. -/
theorem Reduces.encodedLanguage_mem_NL {L L' : Language} [L.IsRelational] [L'.IsRelational]
    (v : Vocabulary L) (v' : Vocabulary L') {K : Query L} {K' : Query L'}
    (h : Reduces K K') (hNL : K'.encodedLanguage v' ∈ Complexity.NL encStructure) :
    K.encodedLanguage v ∈ Complexity.NL encStructure :=
  encodedLanguage_mem_NL_of_reduces_Reach v
    (h.trans (reduces_Reach_of_encodedLanguage_mem_NL v' hNL))

end Cslib.Logic.FO.Ordered

/-! ### Semantic and logspace bridges between `Reach` and `STCON` -/

namespace Cslib.Logic.FO.Ordered.Reach

open Cslib.Complexity

open scoped Classical in
/-- View an ordered graph structure `M` as an `STCONInstance` on `Fin M.size` with source `0` and
target `M.maxElem`. -/
noncomputable def toSTCONInstance (M : Ordered.Structure Language.graph) : STCONInstance where
  n := M.size
  adj x y := decide (graphAdj M x y)
  s := 0
  t := M.maxElem

@[simp]
theorem toSTCONInstance_mem_STCON (M : Ordered.Structure Language.graph) :
    toSTCONInstance M ∈ STCON ↔ M ∈ Reach := by
  rw [mem_STCON, mem_Reach]
  have hadj : (toSTCONInstance M).Adj = graphAdj M := by
    ext x y
    simp only [STCONInstance.Adj, toSTCONInstance, decide_eq_true_eq]
  rw [hadj]
  rfl

end Cslib.Logic.FO.Ordered.Reach

namespace Cslib.Complexity.STCONInstance

open Cslib.Logic.FO.Ordered

/-- Embed any `STCONInstance` (including `I.n = 1` and `I.s = I.t`) into a canonically ordered
graph on `Fin (I.n + 2)`: vertex `0` steps to `I.s + 1`, interior vertices `a + 1` step along
`I.adj` to `b + 1` and from `I.t + 1` to `I.n + 1` (`max`). -/
@[expose] def toOrderedGraph (I : STCONInstance) : Ordered.Structure Language.graph where
  size := I.n + 2
  size_ge_two := by omega
  input :=
    { funMap := fun f => isEmptyElim f
      RelMap
        | .adj, x =>
          ((x 0).val = 0 ∧ (x 1).val = I.s.val + 1) ∨
            (∃ a b : Fin I.n, (x 0).val = a.val + 1 ∧ (x 1).val = b.val + 1 ∧ I.adj a b = true) ∨
            ((x 0).val = I.t.val + 1 ∧ (x 1).val = I.n + 1) }

@[simp]
theorem toOrderedGraph_mem_Reach (I : STCONInstance) :
    I.toOrderedGraph ∈ Reach ↔ I ∈ STCON := by
  let shift (a : Fin I.n) : Fin (I.n + 2) := ⟨a.val + 1, by omega⟩
  have hadj (u w : Fin (I.n + 2)) :
      graphAdj I.toOrderedGraph u w ↔
        ((u.val = 0 ∧ w.val = I.s.val + 1) ∨
          (∃ a b : Fin I.n, u.val = a.val + 1 ∧ w.val = b.val + 1 ∧ I.adj a b = true) ∨
          (u.val = I.t.val + 1 ∧ w.val = I.n + 1)) := Iff.rfl
  have hval : (I.toOrderedGraph.maxElem : Fin (I.n + 2)).val = I.n + 1 := by
    change I.n + 2 - 1 = I.n + 1
    omega
  constructor
  · intro hpath
    let Inv (w : Fin (I.n + 2)) : Prop :=
      w.val = 0 ∨
        (∃ a : Fin I.n, w = shift a ∧ Relation.ReflTransGen I.Adj I.s a) ∨
        (w.val = I.n + 1 ∧ Relation.ReflTransGen I.Adj I.s I.t)
    have hinv : ∀ {w : Fin (I.n + 2)},
        Relation.ReflTransGen (graphAdj I.toOrderedGraph) 0 w → Inv w := by
      intro w hw
      induction hw with
      | refl => exact Or.inl rfl
      | @tail u w _ huw ih =>
        have hedge := (hadj u w).mp huw
        rcases ih with hu0 | ⟨a, rfl, hsa⟩ | ⟨hu_max, -⟩
        · rcases hedge with ⟨_, hw⟩ | ⟨a, b, ha, _, _⟩ | ⟨ht, _⟩
          · exact Or.inr (Or.inl ⟨I.s, Fin.ext hw, .refl⟩)
          · omega
          · omega
        · rcases hedge with ⟨hu0, _⟩ | ⟨a', b, ha', hb, hab⟩ | ⟨ht, hw⟩
          · simp only [shift] at hu0
            omega
          · have ha_eq : a = a' := by
              apply Fin.ext
              simp only [shift] at ha'
              omega
            subst ha_eq
            exact Or.inr (Or.inl ⟨b, Fin.ext hb, hsa.tail hab⟩)
          · have ha_eq : a = I.t := by
              apply Fin.ext
              simp only [shift] at ht
              omega
            subst ha_eq
            exact Or.inr (Or.inr ⟨hw, hsa⟩)
        · rcases hedge with ⟨hu0, _⟩ | ⟨a, _, ha, _, _⟩ | ⟨ht, _⟩
          · omega
          · have := a.isLt; omega
          · have := I.t.isLt; omega
    rcases hinv hpath with h0 | ⟨a, ha, -⟩ | ⟨_, hst⟩
    · omega
    · have ha' := congrArg Fin.val ha
      rw [hval] at ha'
      simp only [shift] at ha'
      have := a.isLt
      omega
    · exact hst
  · intro hst
    have h1 : graphAdj I.toOrderedGraph 0 (shift I.s) :=
      (hadj 0 (shift I.s)).mpr (Or.inl ⟨rfl, rfl⟩)
    have h2 : Relation.ReflTransGen (graphAdj I.toOrderedGraph) (shift I.s) (shift I.t) :=
      Relation.ReflTransGen.lift shift
        (fun a b hab => (hadj (shift a) (shift b)).mpr (Or.inr (Or.inl ⟨a, b, rfl, rfl, hab⟩)))
        I.s I.t hst
    have h3 : graphAdj I.toOrderedGraph (shift I.t) I.toOrderedGraph.maxElem :=
      (hadj (shift I.t) I.toOrderedGraph.maxElem).mpr (Or.inr (Or.inr ⟨rfl, hval⟩))
    exact (Relation.ReflTransGen.head h1 h2).tail h3

end Cslib.Complexity.STCONInstance

namespace Cslib.Logic.FO.Ordered

open Cslib.Complexity Turing.MultiTapeTM

/-- **`Reach` reduces to `STCON` in deterministic logarithmic space** (`encStructure` to
`encSTCON`). -/
theorem reach_logSpaceReducible_STCON :
    LogSpaceReducible encStructure encSTCON (Reach.encodedLanguage graphVocabulary) STCON :=
  STCON.logSpaceReducible_of_mem_NL reach_encodedLanguage_mem_NL

section STCONToReach

private def takeUnaryT : Transducer Bool Bool where
  q₀ := true
  step
    | true, true => (true, [true])
    | _, _ => (false, [])
  final _ := []
  length_step_le q b := by cases q <;> cases b <;> simp
  length_final_le _ := by simp

private theorem takeUnaryT_step_true_true : takeUnaryT.step true true = (true, [true]) := rfl
private theorem takeUnaryT_step_true_false : takeUnaryT.step true false = (false, []) := rfl
private theorem takeUnaryT_step_false (b : Bool) : takeUnaryT.step false b = (false, []) := by
  cases b <;> rfl

private theorem takeUnaryT_run_false : ∀ l : List Bool, takeUnaryT.run false l = []
  | [] => rfl
  | b :: l => by
    rw [Transducer.run_cons, takeUnaryT_step_false, List.nil_append]
    exact takeUnaryT_run_false l

private theorem takeUnaryT_eq_replicate (q : Bool) (w : List Bool) :
    List.replicate (takeUnaryT.run q w).length true = takeUnaryT.run q w := by
  induction w generalizing q with
  | nil => cases q <;> rfl
  | cons b w ih =>
    cases q
    · rw [takeUnaryT_run_false]
      rfl
    · cases b
      · rw [Transducer.run_cons, takeUnaryT_step_true_false, List.nil_append, takeUnaryT_run_false]
        rfl
      · rw [Transducer.run_cons, takeUnaryT_step_true_true, List.singleton_append,
          List.length_cons, List.replicate_succ]
        exact congrArg (true :: ·) (ih true)

private theorem takeUnaryT_run_replicate :
    ∀ (m : ℕ) (l : List Bool),
      takeUnaryT.run true (List.replicate m true ++ false :: l) = List.replicate m true
  | 0, l => by
    rw [List.replicate_zero, List.nil_append, Transducer.run_cons, takeUnaryT_step_true_false,
      List.nil_append, takeUnaryT_run_false]
  | m + 1, l => by
    rw [List.replicate_succ, List.cons_append, Transducer.run_cons, takeUnaryT_step_true_true,
      List.singleton_append]
    exact congrArg (true :: ·) (takeUnaryT_run_replicate m l)

private def countUnary (w : List Bool) : ℕ :=
  (takeUnaryT.run true w).length

private theorem computableInLogSpace_countUnary :
    ComputableInLogSpace countUnary encBits encUnary :=
  takeUnaryT.computableInLogSpace fun w => takeUnaryT_eq_replicate true w

private theorem computableInLogSpace_splitUnary {γ : Type} {encIn : γ ↪ List Bool}
    {w rest : γ → List Bool} {f : γ → ℕ}
    (hw : ComputableInLogSpace w encIn encBits)
    (hsplit : ∀ a, w a = List.replicate (f a) true ++ false :: rest a) :
    ComputableInLogSpace f encIn encUnary ∧ ComputableInLogSpace rest encIn encBits := by
  have hf : ComputableInLogSpace f encIn encUnary :=
    (computableInLogSpace_countUnary.comp hw).congr_fun fun a => by
      rw [Function.comp_apply, hsplit a, countUnary, takeUnaryT_run_replicate,
        List.length_replicate]
  refine ⟨hf, (ComputableInLogSpace.bitsDrop' hw
    (ComputableInLogSpace.unaryAdd hf (.const 1))).congr_fun fun a => ?_⟩
  have hlen : f a + 1 = (List.replicate (f a) true ++ [false]).length := by simp
  have happ : List.replicate (f a) true ++ false :: rest a =
      (List.replicate (f a) true ++ [false]) ++ rest a := by simp
  rw [hsplit a, hlen, happ, List.drop_left]

private def rawOneHot (n k : ℕ) : List Bool :=
  (List.replicate k false ++ ([true] ++ List.replicate n false)).take n

private theorem length_rawOneHot (n k : ℕ) : (rawOneHot n k).length = n := by
  simp only [rawOneHot, List.length_take, List.length_append, List.length_replicate,
    List.length_singleton]
  omega

private theorem getD_rawOneHot {n k i : ℕ} (hk : k < n) (hi : i < n) :
    (rawOneHot n k).getD i false = decide (i = k) := by
  rw [rawOneHot, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  rcases lt_trichotomy i k with hik | rfl | hki
  · rw [List.getElem?_append_left (by simp only [List.length_replicate]; exact hik)]
    have hne : i ≠ k := by omega
    simp [hik, hne]
  · rw [List.getElem?_append_right (by simp only [List.length_replicate]; exact le_rfl)]
    simp
  · rw [List.getElem?_append_right (by simp only [List.length_replicate]; omega)]
    obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i - k ≠ 0)
    have hdn : d < n := by omega
    have hne : i ≠ k := by omega
    simp [hd, hdn, hne]

private def yesSTEncoded : EncodedStructure :=
  (2, [ [false, false, false, false], [true, false], [true, false] ])

private theorem yesSTEncoded_mem_STReach :
    yesSTEncoded ∈ STReach.encodedLanguage stGraphVocabulary := by
  refine ⟨⟨rfl, fun i => ?_⟩, Nat.le_refl 2, ?_⟩
  · rcases i with ⟨i, hi⟩
    match i, hi with
    | 0, _ | 1, _ | 2, _ => rfl
  · rw [mem_STReach]
    refine ⟨0, 0, ?_, ?_, .refl⟩
    · change [true, false].getD (tupleIndex (![0] : Fin 1 → Fin 2)) false = true
      decide
    · change [true, false].getD (tupleIndex (![0] : Fin 1 → Fin 2)) false = true
      decide

private def stconToSTEncoded (I : STCONInstance) : EncodedStructure :=
  if I.n ≤ 1 then yesSTEncoded
  else (I.n, [I.matrix, rawOneHot I.n I.t.val, rawOneHot I.n I.s.val])

private theorem stconToSTEncoded_mem_iff (I : STCONInstance) :
    stconToSTEncoded I ∈ STReach.encodedLanguage stGraphVocabulary ↔ I ∈ STCON := by
  by_cases hn1 : I.n ≤ 1
  · simp only [stconToSTEncoded, hn1, ↓reduceIte]
    have hI : I ∈ STCON := by
      rw [mem_STCON]
      have hsub : I.s = I.t := by
        apply Fin.ext
        have hs := I.s.isLt
        have ht := I.t.isLt
        omega
      rw [hsub]
    exact iff_of_true yesSTEncoded_mem_STReach hI
  · have hn2 : 2 ≤ I.n := by omega
    simp only [stconToSTEncoded, hn1, ↓reduceIte]
    let tables : List (List Bool) := [I.matrix, rawOneHot I.n I.t.val, rawOneHot I.n I.s.val]
    have hwf : stGraphVocabulary.WellFormed (I.n, tables) := by
      refine ⟨rfl, fun i => ?_⟩
      rcases i with ⟨idx, hidx⟩
      match idx, hidx with
      | 0, _ =>
        change I.matrix.length = I.n ^ 2
        rw [I.length_matrix, sq]
      | 1, _ =>
        change (rawOneHot I.n I.t.val).length = I.n ^ 1
        rw [length_rawOneHot, pow_one]
      | 2, _ =>
        change (rawOneHot I.n I.s.val).length = I.n ^ 1
        rw [length_rawOneHot, pow_one]
    change (stGraphVocabulary.WellFormed (I.n, tables) ∧
        ∃ hn : 2 ≤ I.n, decoded stGraphVocabulary (I.n, tables) hn ∈ STReach) ↔ I ∈ STCON
    simp only [hwf, true_and]
    let M := decoded stGraphVocabulary (I.n, tables) hn2
    have hex : (∃ hn : 2 ≤ I.n, decoded stGraphVocabulary (I.n, tables) hn ∈ STReach) ↔
        M ∈ STReach :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨hn2, h⟩⟩
    rw [hex, mem_STReach, mem_STCON]
    have htuple1 (x : Fin I.n) : tupleIndex ![x] = x.val := by
      rw [tupleIndex_apply, Fin.sum_univ_one]
      simp
    have htuple2 (x y : Fin I.n) : tupleIndex ![x, y] = y.val * I.n + x.val := by
      rw [tupleIndex_apply, Fin.sum_univ_two]
      simp [Nat.add_comm]
    have honeHot (u x : Fin I.n) :
        (rawOneHot I.n u.val).getD (tupleIndex ![x]) false = true ↔ x = u := by
      rw [htuple1, getD_rawOneHot u.isLt x.isLt, decide_eq_true_eq, Fin.ext_iff]
    have hsrc (x : Fin I.n) :
        Language.Structure.RelMap (L := stGraphLanguage) (.inr .source)
          (![x] : Fin 1 → M) ↔ x = I.t := honeHot I.t x
    have htgt (x : Fin I.n) :
        Language.Structure.RelMap (L := stGraphLanguage) (.inr .target)
          (![x] : Fin 1 → M) ↔ x = I.s := honeHot I.s x
    have hadj (x y : Fin I.n) :
        Language.Structure.RelMap (L := stGraphLanguage) (.inl .adj)
          (![x, y] : Fin 2 → M) ↔ Function.swap I.Adj x y := by
      change I.matrix.getD (tupleIndex ![x, y]) false = true ↔ I.adj y x = true
      rw [htuple2, I.getD_matrix y x]
    constructor
    · rintro ⟨s', t', hs', ht', hpath⟩
      rw [(hsrc s').mp hs', (htgt t').mp ht'] at hpath
      have hswap : Relation.ReflTransGen (Function.swap I.Adj) I.t I.s :=
        Relation.ReflTransGen.lift id (fun x y hxy => (hadj x y).mp hxy) I.t I.s hpath
      exact Relation.reflTransGen_swap.mp hswap
    · intro hst
      refine ⟨I.t, I.s, (hsrc I.t).mpr rfl, (htgt I.s).mpr rfl, ?_⟩
      have hswap : Relation.ReflTransGen (Function.swap I.Adj) I.t I.s :=
        Relation.reflTransGen_swap.mpr hst
      exact Relation.ReflTransGen.lift id (fun x y hxy => (hadj x y).mpr hxy) I.t I.s hswap

private theorem computableInLogSpace_replicate_false {γ : Type} {encIn : γ ↪ List Bool}
    {f : γ → ℕ} (hf : ComputableInLogSpace f encIn encUnary) :
    ComputableInLogSpace (fun a => List.replicate (f a) false) encIn encBits := by
  have htrue : ComputableInLogSpace (fun n : ℕ => List.replicate n true) encUnary encBits :=
    ComputableInLogSpace.of_eq fun _ => rfl
  have hmap : ComputableInLogSpace (fun n : ℕ => List.replicate n false) encUnary encBits :=
    ((ComputableInLogSpace.bitsMap fun _ => false).comp htrue).congr_fun fun n => by
      simp [Function.comp_apply]
  exact hmap.comp hf

private theorem computableInLogSpace_rawOneHot {γ : Type} {encIn : γ ↪ List Bool}
    {fn fk : γ → ℕ} (hn : ComputableInLogSpace fn encIn encUnary)
    (hk : ComputableInLogSpace fk encIn encUnary) :
    ComputableInLogSpace (fun a => rawOneHot (fn a) (fk a)) encIn encBits :=
  ComputableInLogSpace.bitsTake'
    (ComputableInLogSpace.bitsAppend (computableInLogSpace_replicate_false hk)
      (ComputableInLogSpace.bitsAppend (.const [true]) (computableInLogSpace_replicate_false hn)))
    hn

private theorem computableInLogSpace_stconToSTEncoded :
    ComputableInLogSpace stconToSTEncoded encSTCON encStructure := by
  have hraw : ComputableInLogSpace STCONInstance.encode encSTCON encBits :=
    ComputableInLogSpace.of_eq fun _ => rfl
  obtain ⟨hn, hrem₁⟩ := computableInLogSpace_splitUnary hraw fun _ => rfl
  obtain ⟨hs, hrem₂⟩ := computableInLogSpace_splitUnary hrem₁ fun _ => rfl
  obtain ⟨ht, hmat⟩ := computableInLogSpace_splitUnary hrem₂ fun _ => rfl
  have hsrc : ComputableInLogSpace (fun I : STCONInstance => rawOneHot I.n I.t.val)
      encSTCON encBits :=
    computableInLogSpace_rawOneHot hn ht
  have htgt : ComputableInLogSpace (fun I : STCONInstance => rawOneHot I.n I.s.val)
      encSTCON encBits :=
    computableInLogSpace_rawOneHot hn hs
  have htables : ComputableInLogSpace
      (fun I : STCONInstance => [I.matrix, rawOneHot I.n I.t.val, rawOneHot I.n I.s.val])
      encSTCON (encList encBits) :=
    ComputableInLogSpace.listCons hmat
      (ComputableInLogSpace.listCons hsrc (ComputableInLogSpace.listSingleton.comp htgt))
  have hmain : ComputableInLogSpace
      (fun I : STCONInstance => (I.n, [I.matrix, rawOneHot I.n I.t.val, rawOneHot I.n I.s.val]))
      encSTCON encStructure :=
    ComputableInLogSpace.pair hn htables
  exact ComputableInLogSpace.ite_decide
    (ComputableInLogSpace.unaryLeConst 1 hn) (.const yesSTEncoded) hmain

end STCONToReach

/-- **`STCON` reduces to `Reach` in deterministic logarithmic space** (`encSTCON` to
`encStructure`), composing the transpose `STCON → STReach` encoding with the ordered first-order
endpoint normalization `stReach_reduces_Reach`. -/
theorem stcon_logSpaceReducible_Reach :
    LogSpaceReducible encSTCON encStructure STCON (Reach.encodedLanguage graphVocabulary) :=
  LogSpaceReducible.trans
    ⟨stconToSTEncoded, computableInLogSpace_stconToSTEncoded,
      fun I => (stconToSTEncoded_mem_iff I).symm⟩
    (stReach_reduces_Reach.logSpaceReducible stGraphVocabulary graphVocabulary)

/-- **`Reach` is `NL`-hard** under deterministic logspace many-one reductions (`encStructure`). -/
theorem reach_logSpaceHard_NL :
    LogSpaceHard NL encStructure (Reach.encodedLanguage graphVocabulary) :=
  STCON.logSpaceHard.trans stcon_logSpaceReducible_Reach

/-- **`Reach` is `NL`-complete** under deterministic logspace many-one reductions
(`encStructure`). -/
theorem reach_logSpaceComplete_NL :
    LogSpaceComplete NL encStructure (Reach.encodedLanguage graphVocabulary) :=
  ⟨reach_encodedLanguage_mem_NL, reach_logSpaceHard_NL⟩

end Cslib.Logic.FO.Ordered
