/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Arborescences
public import CslibFrontier.Foundations.Combinatorics.Multidigraph.BEST
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Polynomial-time Eulerian-circuit counting via the BEST theorem

Polynomial-time evaluation of the exact number of Eulerian circuits starting with a given arc in a
finite multidigraph (`Cslib.Complexity.Graph`), combining the BEST theorem (`Multidigraph.BEST`),
Tutte's directed matrix-tree theorem (`Arborescences`), and
`Cslib.Circuits.Rational.detRows_polytime`.

Isolated declared vertices (`outdeg = 0`) do not affect `Multidigraph.IsEulerianCircuit`, so the
algorithm filters to `Graph.activeVertices` before applying the reduced-Laplacian formula.

## Main definitions

* `Cslib.Complexity.Graph.outdeg`, `Cslib.Complexity.Graph.indeg`: outgoing and incoming arc counts
  in `G.validArcs`.
* `Cslib.Complexity.Graph.isBalancedBool`: Boolean check that `outdeg v = indeg v` for every
  declared vertex.
* `Cslib.Complexity.Graph.activeVertices`: duplicate-free list of declared vertices with positive
  out-degree.
* `Cslib.Complexity.Graph.eulerianCircuitCount`: exact count of Eulerian circuits starting at arc
  index `eIdx` via the BEST determinant formula (`0` if `eIdx` is out of range or `G` is not
  balanced).

## Main results

* `Cslib.Complexity.Graph.eulerianCircuitCount_eq_natCard`: exact equality with
  `Nat.card {l // Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l}`.
* `Cslib.Complexity.Graph.computableInPolyTime_eulerianCircuitCount`,
  `Cslib.Complexity.Graph.computableInPolyTime_natCard_isEulerianCircuit`: polynomial-time
  computability on `encPair encGraph encNat`.
-/

public section

namespace Cslib.Complexity.Graph

open Turing MultiTapeTM

/-- Out-degree of `v` in the valid-arc multidigraph `G.validArcs`. -/
@[expose]
def outdeg (G : Graph) (v : ℕ) : ℕ :=
  G.validArcs.countP fun e => decide (e.1 = v)

/-- In-degree of `v` in the valid-arc multidigraph `G.validArcs`. -/
@[expose]
def indeg (G : Graph) (v : ℕ) : ℕ :=
  G.validArcs.countP fun e => decide (e.2 = v)

/-- Boolean check that every declared vertex of `G` has equal out-degree and in-degree in
`G.validArcs`. -/
@[expose]
def isBalancedBool (G : Graph) : Bool :=
  G.distinctVertices.all fun v => decide (G.outdeg v = G.indeg v)

/-- Duplicate-free list of declared vertices of `G` with at least one outgoing arc in
`G.validArcs`. -/
@[expose]
def activeVertices (G : Graph) : List ℕ :=
  G.distinctVertices.filter fun v => decide (G.outdeg v ≠ 0)

/-- Number of Eulerian circuits of `(G.arcSrc, G.arcTgt)` starting with arc `eIdx` (`0` if
`eIdx ≥ G.validArcs.length` or `G` is not balanced), computed via the BEST theorem. -/
@[expose]
def eulerianCircuitCount (G : Graph) (eIdx : ℕ) : ℕ :=
  if decide (eIdx < G.validArcs.length) && G.isBalancedBool then
    let r := (G.validArcs.getD eIdx (0, 0)).1
    multiLaplacianCount G.activeVertices G.validArcs r *
      (G.activeVertices.map fun v => ((G.outdeg v - 1).factorial : ℤ)).prod.toNat
  else 0

private theorem activeVertices_nodup (G : Graph) : G.activeVertices.Nodup :=
  G.nodup_distinctVertices.filter _

private theorem card_fin_filter_subtype_eq {xs : List ℕ} {ys : List (ℕ × ℕ)} (p : ℕ × ℕ → ℕ)
    (hp : ∀ e ∈ ys, p e ∈ xs) (v : {x // x ∈ xs}) :
    (Finset.univ.filter fun i : Fin ys.length =>
      (⟨p ys[i], hp _ (List.getElem_mem i.isLt)⟩ : {x // x ∈ xs}) = v).card =
      ys.countP fun e => decide (p e = v.1) := by
  rw [List.countP_eq_card_filter_getElem ys (fun e => decide (p e = v.1))]
  congr 1
  ext i
  simp [Subtype.ext_iff]

private theorem mem_activeVertices_of_validArc (G : Graph) (hbal : G.isBalancedBool = true)
    {e : ℕ × ℕ} (he : e ∈ G.validArcs) :
    e.1 ∈ G.activeVertices ∧ e.2 ∈ G.activeVertices := by
  have hv : e.1 ∈ G.1 ∧ e.2 ∈ G.1 := (mem_validArcs.1 he).2
  have h1 : 0 < G.outdeg e.1 := List.countP_pos_iff.2 ⟨e, he, decide_eq_true rfl⟩
  have h2_in : 0 < G.indeg e.2 := List.countP_pos_iff.2 ⟨e, he, decide_eq_true rfl⟩
  have h2_eq : G.outdeg e.2 = G.indeg e.2 := by
    simp only [isBalancedBool, List.all_eq_true, decide_eq_true_eq] at hbal
    exact hbal e.2 (Graph.mem_distinctVertices.2 hv.2)
  refine ⟨List.mem_filter.2 ⟨Graph.mem_distinctVertices.2 hv.1, decide_eq_true (by omega)⟩,
    List.mem_filter.2 ⟨Graph.mem_distinctVertices.2 hv.2, decide_eq_true (by omega)⟩⟩

/-- **Polynomial-time BEST theorem evaluation**: `G.eulerianCircuitCount eIdx` equals the number
of Eulerian circuits of `(G.arcSrc, G.arcTgt)` starting at arc `eIdx` (and `0` when `eIdx` is out
of range). -/
theorem eulerianCircuitCount_eq_natCard (G : Graph) (eIdx : ℕ) :
    G.eulerianCircuitCount eIdx =
      if he : eIdx < G.validArcs.length then
        Nat.card {l : List (Fin G.validArcs.length) //
          Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l}
      else 0 := by
  classical
  by_cases he : eIdx < G.validArcs.length
  · rw [dite_eq_left he]
    by_cases hbalB : G.isBalancedBool = true
    · have hcond : (decide (eIdx < G.validArcs.length) && G.isBalancedBool) = true := by
        simp [he, hbalB]
      simp only [eulerianCircuitCount, hcond, ↓reduceIte]
      have harcs : ∀ e ∈ G.validArcs, e.1 ∈ G.activeVertices ∧ e.2 ∈ G.activeVertices :=
        fun e he_mem => G.mem_activeVertices_of_validArc hbalB he_mem
      let srcAct : Fin G.validArcs.length → {v // v ∈ G.activeVertices} := fun i =>
        ⟨G.validArcs[i].1, (harcs _ (List.getElem_mem i.isLt)).1⟩
      let tgtAct : Fin G.validArcs.length → {v // v ∈ G.activeVertices} := fun i =>
        ⟨G.validArcs[i].2, (harcs _ (List.getElem_mem i.isLt)).2⟩
      have hcirc_iff : ∀ l : List (Fin G.validArcs.length),
          Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l ↔
            Multidigraph.IsEulerianCircuit srcAct tgtAct ⟨eIdx, he⟩ l := by
        intro l
        constructor <;> rintro ⟨hnd, hmem, hh, hch, hgl⟩ <;>
          refine ⟨hnd, hmem, hh, hch.imp fun a b hab => ?_, fun a ha => ?_⟩
        · simpa only [Subtype.ext_iff, arcSrc, arcTgt, srcAct, tgtAct] using hab
        · simpa only [Subtype.ext_iff, arcSrc, arcTgt, srcAct, tgtAct] using hgl a ha
        · simpa only [Subtype.ext_iff, arcSrc, arcTgt, srcAct, tgtAct] using hab
        · simpa only [Subtype.ext_iff, arcSrc, arcTgt, srcAct, tgtAct] using hgl a ha
      have hcard_eq :
          Nat.card {l : List (Fin G.validArcs.length) //
              Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l} =
            Nat.card {l : List (Fin G.validArcs.length) //
              Multidigraph.IsEulerianCircuit srcAct tgtAct ⟨eIdx, he⟩ l} :=
        Nat.card_congr (Equiv.subtypeEquivRight hcirc_iff)
      have hbal_act : ∀ v : {v // v ∈ G.activeVertices},
          (Finset.univ.filter fun e => srcAct e = v).card =
            (Finset.univ.filter fun e => tgtAct e = v).card := by
        intro v
        rw [card_fin_filter_subtype_eq Prod.fst (fun e h => (harcs e h).1) v,
          card_fin_filter_subtype_eq Prod.snd (fun e h => (harcs e h).2) v]
        simp only [isBalancedBool, List.all_eq_true, decide_eq_true_eq] at hbalB
        exact hbalB v.1 ((List.mem_filter.1 v.2).1)
      have hpos_act : ∀ v : {v // v ∈ G.activeVertices}, ∃ e, srcAct e = v := by
        intro v
        have hpos : 0 < G.outdeg v.1 := by
          have := (List.mem_filter.1 v.2).2
          simp only [decide_eq_true_eq] at this
          exact Nat.pos_of_ne_zero this
        obtain ⟨e, he_mem, he_fst⟩ := List.countP_pos_iff.1 hpos
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 he_mem
        refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
        simpa [srcAct, hget] using decide_eq_true_iff.1 he_fst
      have hbest :=
        Multidigraph.natCard_isEulerianCircuit srcAct tgtAct hbal_act hpos_act ⟨eIdx, he⟩
      have hr_def : (G.validArcs.getD eIdx (0, 0)).1 = G.validArcs[eIdx].1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he, Option.getD_some]
      have harb :
          multiLaplacianCount G.activeVertices G.validArcs G.validArcs[eIdx].1 =
            Nat.card {f : {v : {v // v ∈ G.activeVertices} // v ≠ srcAct ⟨eIdx, he⟩} →
                Fin G.validArcs.length //
              Multidigraph.IsInArborescence srcAct tgtAct (srcAct ⟨eIdx, he⟩) f} :=
        multiLaplacianCount_eq_natCard G.activeVertices_nodup (fun _ => Iff.rfl)
          G.validArcs harcs (harcs _ (List.getElem_mem he)).1
      let eAct : Fin G.activeVertices.length ≃ {v // v ∈ G.activeVertices} :=
        G.activeVertices_nodup.getEquiv G.activeVertices
      have hprod :
          (G.activeVertices.map fun v => ((G.outdeg v - 1).factorial : ℤ)).prod.toNat =
            ∏ v : {v // v ∈ G.activeVertices},
              ((Finset.univ.filter fun e => srcAct e = v).card - 1).factorial := by
        have hnat :
            (G.activeVertices.map fun v => ((G.outdeg v - 1).factorial : ℤ)).prod =
              ((∏ v : {v // v ∈ G.activeVertices},
                ((Finset.univ.filter fun e => srcAct e = v).card - 1).factorial : ℕ) : ℤ) := by
          rw [← Fin.prod_univ_fun_getElem, Nat.cast_prod, ← Equiv.prod_comp eAct]
          refine Finset.prod_congr rfl fun i _ => ?_
          have hi : (eAct i).1 = G.activeVertices[i] := rfl
          rw [card_fin_filter_subtype_eq Prod.fst (fun e h => (harcs e h).1) (eAct i), hi]
          rfl
        rw [hnat, Int.toNat_natCast]
      rw [hr_def, hcard_eq, hbest, harb, hprod]
    · have hcond : (decide (eIdx < G.validArcs.length) && G.isBalancedBool) = false := by
        simp [hbalB]
      simp only [eulerianCircuitCount, hcond, Bool.false_eq_true, ↓reduceIte]
      have hempty : IsEmpty {l : List (Fin G.validArcs.length) //
          Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l} := by
        refine ⟨fun ⟨l, hl⟩ => hbalB ?_⟩
        simp only [isBalancedBool, List.all_eq_true, decide_eq_true_eq]
        intro v hv
        unfold outdeg indeg
        let vSub : {x // x ∈ G.1} := ⟨v, Graph.mem_distinctVertices.1 hv⟩
        rw [show v = vSub.1 from rfl,
          ← card_fin_filter_subtype_eq Prod.fst (fun e h => (mem_validArcs.1 h).2.1) vSub,
          ← card_fin_filter_subtype_eq Prod.snd (fun e h => (mem_validArcs.1 h).2.2) vSub]
        exact hl.card_filter_src_eq vSub
      exact (Nat.card_of_isEmpty).symm
  · simp [eulerianCircuitCount, he]

/-! ### Polynomial-time computability -/

@[fun_prop]
theorem computableInPolyTime_outdeg {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → Graph} {v : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encGraph)
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => (g x).outdeg (v x)) encIn encUnary := by
  have harcs : ComputableInPolyTime (fun x => (g x).validArcs) encIn
      (encList (encPair encNat encNat)) :=
    computableInPolyTime_validArcs.comp hg
  refine ComputableInPolyTime.countPWithInput harcs ?_
  exact ((ComputableInPolyTime.fst encNat encNat).comp
    (ComputableInPolyTime.snd encIn (encPair encNat encNat))).decide_eq'
    (hv.comp (ComputableInPolyTime.fst encIn (encPair encNat encNat)))

@[fun_prop]
theorem computableInPolyTime_indeg {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → Graph} {v : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encGraph)
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => (g x).indeg (v x)) encIn encUnary := by
  have harcs : ComputableInPolyTime (fun x => (g x).validArcs) encIn
      (encList (encPair encNat encNat)) :=
    computableInPolyTime_validArcs.comp hg
  refine ComputableInPolyTime.countPWithInput harcs ?_
  exact ((ComputableInPolyTime.snd encNat encNat).comp
    (ComputableInPolyTime.snd encIn (encPair encNat encNat))).decide_eq'
    (hv.comp (ComputableInPolyTime.fst encIn (encPair encNat encNat)))

@[fun_prop]
theorem computableInPolyTime_isBalancedBool :
    ComputableInPolyTime isBalancedBool encGraph encBool := by
  refine ComputableInPolyTime.allWithInput computableInPolyTime_distinctVertices ?_
  have hout := computableInPolyTime_outdeg
    (ComputableInPolyTime.fst encGraph encNat) (ComputableInPolyTime.snd encGraph encNat)
  have hin := computableInPolyTime_indeg
    (ComputableInPolyTime.fst encGraph encNat) (ComputableInPolyTime.snd encGraph encNat)
  exact hout.decide_eq' hin

@[fun_prop]
theorem computableInPolyTime_activeVertices :
    ComputableInPolyTime activeVertices encGraph (encList encNat) := by
  refine ComputableInPolyTime.filterWithInput computableInPolyTime_distinctVertices ?_
  have hout := computableInPolyTime_outdeg
    (ComputableInPolyTime.fst encGraph encNat) (ComputableInPolyTime.snd encGraph encNat)
  have hzero : ComputableInPolyTime (fun p : Graph × ℕ => decide (p.1.outdeg p.2 = 0))
      (encPair encGraph encNat) encBool :=
    hout.decide_eq' (ComputableInPolyTime.const 0)
  simpa only [Function.comp_def, decide_not] using ComputableInPolyTime.bool_not.comp hzero

/-- `Graph.eulerianCircuitCount` is computable in polynomial time on `encPair encGraph encNat`. -/
@[fun_prop]
theorem computableInPolyTime_eulerianCircuitCount :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.eulerianCircuitCount p.2)
      (encPair encGraph encNat) encNat := by
  have hfst : ComputableInPolyTime (fun p : Graph × ℕ => p.1) (encPair encGraph encNat) encGraph :=
    ComputableInPolyTime.fst _ _
  have hsnd : ComputableInPolyTime (fun p : Graph × ℕ => p.2) (encPair encGraph encNat) encNat :=
    ComputableInPolyTime.snd _ _
  have harcs : ComputableInPolyTime (fun p : Graph × ℕ => p.1.validArcs)
      (encPair encGraph encNat) (encList (encPair encNat encNat)) :=
    computableInPolyTime_validArcs.comp hfst
  have hlen : ComputableInPolyTime (fun p : Graph × ℕ => p.1.validArcs.length)
      (encPair encGraph encNat) encNat := by
    have hu : ComputableInPolyTime (fun p : Graph × ℕ => p.1.validArcs.countP fun _ => true)
        (encPair encGraph encNat) encUnary :=
      ComputableInPolyTime.countPWithInput harcs (ComputableInPolyTime.const true)
    refine (ComputableInPolyTime.unary_to_binary.comp hu).of_enc_eq fun p => ?_
    simp [List.countP_true]
  have hlt : ComputableInPolyTime (fun p : Graph × ℕ => decide (p.2 < p.1.validArcs.length))
      (encPair encGraph encNat) encBool :=
    ComputableInPolyTime.binary_lt' hsnd hlen
  have hcond : ComputableInPolyTime
      (fun p : Graph × ℕ => decide (p.2 < p.1.validArcs.length) && p.1.isBalancedBool)
      (encPair encGraph encNat) encBool :=
    ComputableInPolyTime.bool_and.comp (hlt.prod (computableInPolyTime_isBalancedBool.comp hfst))
  have hr : ComputableInPolyTime (fun p : Graph × ℕ => (p.1.validArcs.getD p.2 (0, 0)).1)
      (encPair encGraph encNat) encNat :=
    (ComputableInPolyTime.fst encNat encNat).comp
      (ComputableInPolyTime.listGetD_binary (encA := encPair encNat encNat) (0, 0) harcs hsnd)
  have harb : ComputableInPolyTime
      (fun p : Graph × ℕ => multiLaplacianCount p.1.activeVertices p.1.validArcs
        (p.1.validArcs.getD p.2 (0, 0)).1)
      (encPair encGraph encNat) encNat :=
    computableInPolyTime_multiLaplacianCount (computableInPolyTime_activeVertices.comp hfst)
      harcs hr
  have hprod : ComputableInPolyTime
      (fun p : Graph × ℕ =>
        (p.1.activeVertices.map fun v => ((p.1.outdeg v - 1).factorial : ℤ)).prod.toNat)
      (encPair encGraph encNat) encNat := by
    have hact : ComputableInPolyTime (fun p : Graph × ℕ => p.1.activeVertices)
        (encPair encGraph encNat) (encList encNat) :=
      computableInPolyTime_activeVertices.comp hfst
    have hout : ComputableInPolyTime
        (fun q : (Graph × ℕ) × ℕ => q.1.1.outdeg q.2)
        (encPair (encPair encGraph encNat) encNat) encUnary :=
      computableInPolyTime_outdeg
        (hfst.comp (ComputableInPolyTime.fst (encPair encGraph encNat) encNat))
        (ComputableInPolyTime.snd (encPair encGraph encNat) encNat)
    have hfac : ComputableInPolyTime
        (fun q : (Graph × ℕ) × ℕ => ((q.1.1.outdeg q.2 - 1).factorial : ℤ))
        (encPair (encPair encGraph encNat) encNat) encIntBin :=
      ComputableInPolyTime.intBin_natCast.comp
        (ComputableInPolyTime.binary_factorial.comp
          (ComputableInPolyTime.unary_sub' hout (ComputableInPolyTime.const 1)))
    have hlist : ComputableInPolyTime
        (fun p : Graph × ℕ => p.1.activeVertices.map fun v => ((p.1.outdeg v - 1).factorial : ℤ))
        (encPair encGraph encNat) (encList encIntBin) :=
      ComputableInPolyTime.mapWithInput hact hfac
    exact ComputableInPolyTime.intBin_toNat.comp
      (ComputableInPolyTime.intBin_prod.comp hlist)
  have hmul : ComputableInPolyTime
      (fun p : Graph × ℕ =>
        multiLaplacianCount p.1.activeVertices p.1.validArcs (p.1.validArcs.getD p.2 (0, 0)).1 *
          (p.1.activeVertices.map fun v => ((p.1.outdeg v - 1).factorial : ℤ)).prod.toNat)
      (encPair encGraph encNat) encNat :=
    ComputableInPolyTime.binary_mul' harb hprod
  exact ComputableInPolyTime.ite' hcond hmul (ComputableInPolyTime.const 0)

/-- The number of Eulerian circuits starting with arc `eIdx` in the multidigraph
`(G.arcSrc, G.arcTgt)` is computable in polynomial time on `encPair encGraph encNat`. -/
theorem computableInPolyTime_natCard_isEulerianCircuit :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if he : p.2 < p.1.validArcs.length then
          Nat.card {l : List (Fin p.1.validArcs.length) //
            Multidigraph.IsEulerianCircuit p.1.arcSrc p.1.arcTgt ⟨p.2, he⟩ l}
        else 0)
      (encPair encGraph encNat) encNat := by
  refine computableInPolyTime_eulerianCircuitCount.of_enc_eq fun p => ?_
  rw [eulerianCircuitCount_eq_natCard]

end Cslib.Complexity.Graph
