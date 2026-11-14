/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Substitution.BoundaryPartition
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.BoundaryRotation
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateColors
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ProbeRestriction
import Mathlib.Data.List.GetD

/-!
# Exact boundary-block corner-color paths

Cutting the actual probe-variable cycle after its unique canonical marker gives precisely
the executed free boundary block. Its corner colors run from the reverse marker to the marker.
An empty block explicitly forces the two marker colors to agree.
Auxiliary words retain their literal body successors outside the probe ports and give closed
paths in those same probe colors, including empty auxiliary words.
-/

public section

namespace Cslib.Complexity.CSP.GadgetRotation

open Cslib.Logic.PL Cslib.Logic.PL.CSP OrderedBoundary Graph

variable {Rel : Type} {arity : Rel → ℕ} {sem : Rel → List Bool → Bool}
  {n : ℕ} {R : Set (Fin n → Bool)}

/-- The computed free block is an exact entry/exit color path in the literal decoded probe
rotation. The theorem includes unused free ports, whose block is empty. -/
theorem isChain_freeBoundaryBlock_colors (g : PPGadget arity sem R) (w : GadgetWitness g)
    (i : Fin n) (P : Dart (incidenceGraph (probeBody g.body (List.ofFn Sum.inl))) → Bool)
    (hP : ∀ d, P (w.probeRotation.rotate d) = P d.reverse) :
    let marker := incidenceDart (gadgetProbeOccurrence g i) false
    List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((P marker.reverse, P marker.reverse) ::
        ((freeBoundaryBlocks g w).getD i.val []).map
          (fun j => (Dart.colorAtIndex P (2 * j), Dart.colorAtIndex P (2 * j + 1))) ++
        [(P marker, P marker)]) := by
  let marker := incidenceDart (gadgetProbeOccurrence g i) false
  have hc := ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).1
  have h := RotationCertificate.isChain_colors_tail_cycleWord hc marker P hP
  have hm : (((freeBoundaryBlocks g w).getD i.val []).map fun j =>
      (Dart.colorAtIndex P (2 * j), Dart.colorAtIndex P (2 * j + 1))) =
      (RotationCertificate.cycleWord w.certificate marker.index).tail.map
        (fun j => (Dart.colorAtIndex P j, Dart.colorAtIndex (fun d => P d.reverse) j)) := by
    rw [getD_freeBoundaryBlocks, List.map_map]
    apply List.map_congr_left
    intro j hj
    obtain ⟨p, hp, _⟩ := (mem_variable_cycleWord_iff hc (gadgetProbeOccurrence g i) j).mp
      (List.mem_of_mem_tail hj)
    rw [hp]
    dsimp only [Function.comp_def]
    have hdiv : 2 * incidenceEdgeIndex p / 2 = incidenceEdgeIndex p := by omega
    rw [hdiv]
    change (Dart.colorAtIndex P (incidenceDart p false).index,
        Dart.colorAtIndex P (incidenceDart p true).index) =
      (Dart.colorAtIndex P (incidenceDart p false).index,
        Dart.colorAtIndex (fun d => P d.reverse) (incidenceDart p false).index)
    simp only [Dart.colorAtIndex_index]
    rfl
  change List.IsChain _ ((P marker.reverse, P marker.reverse) :: _ ++ [(P marker, P marker)])
  rw [hm]
  exact h

/-- An unused free port has equal colors on its two marker ends. This follows from the
actual first-return word, rather than assuming that every boundary block is nonempty. -/
theorem marker_colors_eq_of_freeBoundaryBlock_nil
    (g : PPGadget arity sem R) (w : GadgetWitness g) (i : Fin n)
    (P : Dart (incidenceGraph (probeBody g.body (List.ofFn Sum.inl))) → Bool)
    (hP : ∀ d, P (w.probeRotation.rotate d) = P d.reverse)
    (he : (freeBoundaryBlocks g w).getD i.val [] = []) :
    P (incidenceDart (gadgetProbeOccurrence g i) false).reverse =
      P (incidenceDart (gadgetProbeOccurrence g i) false) := by
  have h := isChain_freeBoundaryBlock_colors g w i P hP
  simpa only [he, List.map_nil, List.cons_append, List.nil_append, List.isChain_pair] using h

/-- The exact free-block color path telescopes to its actual marker-edge bit. This also
computes zero for an empty block, without requiring an occurring free port. -/
theorem sum_freeBoundaryBlock_colors (g : PPGadget arity sem R) (w : GadgetWitness g)
    (i : Fin n) (P : Dart (incidenceGraph (probeBody g.body (List.ofFn Sum.inl))) → Bool)
    (hP : ∀ d, P (w.probeRotation.rotate d) = P d.reverse) :
    (((freeBoundaryBlocks g w).getD i.val []).map fun j =>
      Dart.colorAtIndex P (2 * j) ^^ Dart.colorAtIndex P (2 * j + 1)).sum =
      (P (incidenceDart (gadgetProbeOccurrence g i) false) ^^
        P (incidenceDart (gadgetProbeOccurrence g i) false).reverse) := by
  have h := List.sum_sub_eq_of_isChain_colorPairs (isChain_freeBoundaryBlock_colors g w i P hP)
  simpa only [List.map_map, Function.comp_def, BooleanRing.sub_eq_add, Bool.add_eq_xor,
    Bool.xor_comm] using h

/-- An actual marker-edge labeling obtained from clockwise colors is zero whenever that
port's computed body block is empty. This includes every unused canonical free port. -/
theorem marker_bit_eq_false_of_freeBoundaryBlock_nil
    (g : PPGadget arity sem R) (w : GadgetWitness g) (i : Fin n)
    (x : Fin (incidenceGraph (probeBody g.body (List.ofFn Sum.inl))).edges.length → Bool)
    (P : Dart (incidenceGraph (probeBody g.body (List.ofFn Sum.inl))) → Bool)
    (hP : ∀ d, P (w.probeRotation.rotate d) = P d.reverse)
    (hx : ∀ d, (P d ^^ P d.reverse) = x d.1)
    (he : (freeBoundaryBlocks g w).getD i.val [] = []) :
    x (incidenceDart (gadgetProbeOccurrence g i) false).1 = false := by
  have hc := marker_colors_eq_of_freeBoundaryBlock_nil g w i P hP he
  have hb := hx (incidenceDart (gadgetProbeOccurrence g i) false)
  rw [hc, Bool.xor_self] at hb
  exact hb.symm

/-- The actual auxiliary body cycle is a closed path of the probe's corner colors.
The prefix restriction leaves every successor unchanged outside the canonical free ports;
unused auxiliary ports give an empty closed path. -/
theorem isChain_auxiliaryBoundaryBlock_colors (g : PPGadget arity sem R)
    (w : GadgetWitness g) (a : Fin g.numAux)
    (P : Dart (incidenceGraph (probeBody g.body (List.ofFn Sum.inl))) → Bool)
    (hP : ∀ d, P (w.probeRotation.rotate d) = P d.reverse) :
    ∃ color : Bool, List.IsChain (fun p q : Bool × Bool => p.2 = q.1)
      ((color, color) :: ((auxiliaryBoundaryBlocks g w).getD a.val []).map
        (fun j => (Dart.colorAtIndex P (2 * j), Dart.colorAtIndex P (2 * j + 1))) ++
        [(color, color)]) := by
  by_cases hv : Sum.inr a ∈ g.body.vars
  · obtain ⟨o, hov, hword⟩ := auxiliaryBoundaryBlock_eq_cycleBlock g w a hv
    have hc := ((verifyRotationCertificate_eq_true_iff _ _).mp w.body_accepted).1
    have hp := ((verifyRotationCertificate_eq_true_iff _ _).mp w.probe_accepted).1
    let start := (incidenceDart o false).index
    let word := RotationCertificate.cycleWord (bodyCertificate g.body w.certificate) start
    have hindex (p : g.body.Occurrence) (side : Bool) :
        (incidenceDart (bodyOccurrence g.body (List.ofFn Sum.inl) p) side).index =
          (incidenceDart p side).index := by
      change 2 * incidenceEdgeIndex (bodyOccurrence _ _ p) + _ =
        2 * incidenceEdgeIndex p + _
      rw [incidenceEdgeIndex_bodyOccurrence]
      rfl
    have he (j : ℕ) (hj : j ∈ word) :
        Dart.colorAtIndex P (word.formPerm j) =
          Dart.colorAtIndex (fun d => P d.reverse) j := by
      obtain ⟨p, hjp, hpv⟩ := (mem_variable_cycleWord_iff hc o j).mp hj
      have hnot : p.var ∉ (List.ofFn (Sum.inl : Fin n → Fin n ⊕ Fin g.numAux)) := by
        rw [hpv, hov]
        simp
      rw [hjp]
      change Dart.colorAtIndex P (word.formPerm (incidenceDart p false).index) =
        Dart.colorAtIndex (fun d => P d.reverse) (incidenceDart p false).index
      rw [RotationCertificate.formPerm_cycleWord_apply hc (incidenceDart o false)
        (incidenceDart p false) ((vertex_incidenceDart_eq_iff p o false false).mpr
          ⟨rfl, hpv⟩), getD_bodyCertificate_of_variable_not_mem_ports w p hnot,
        ← hindex p false, ← RotationCertificate.index_decode_rotate hp,
        Dart.colorAtIndex_index, Dart.colorAtIndex_index]
      exact hP (incidenceDart (bodyOccurrence g.body (List.ofFn Sum.inl) p) false)
    have hcons : start :: word.tail = word := rfl
    have hn : (start :: word.tail).Nodup := by
      rw [hcons]
      exact RotationCertificate.nodup_cycleWord hc (incidenceDart o false)
    have he' (j : ℕ) (hj : j ∈ start :: word.tail) :
        Dart.colorAtIndex P ((start :: word.tail).formPerm j) =
          Dart.colorAtIndex (fun d => P d.reverse) j := by
      rw [hcons] at hj ⊢
      exact he j hj
    have h := List.isChain_colorPairs_cycle_formPerm start word.tail hn
      (Dart.colorAtIndex P) (Dart.colorAtIndex fun d => P d.reverse) he'
    have hm : (word.map (· / 2)).map
        (fun j => (Dart.colorAtIndex P (2 * j), Dart.colorAtIndex P (2 * j + 1))) =
        word.map (fun j => (Dart.colorAtIndex P j,
          Dart.colorAtIndex (fun d => P d.reverse) j)) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro j hj
      obtain ⟨p, rfl, _⟩ := (mem_variable_cycleWord_iff hc o j).mp hj
      have hd : 2 * incidenceEdgeIndex p / 2 = incidenceEdgeIndex p := by omega
      dsimp only [Function.comp_def]
      rw [hd]
      change (Dart.colorAtIndex P (incidenceDart p false).index,
        Dart.colorAtIndex P (incidenceDart p true).index) =
          (Dart.colorAtIndex P (incidenceDart p false).index,
            Dart.colorAtIndex (fun d => P d.reverse) (incidenceDart p false).index)
      rw [← hindex p true, ← hindex p false]
      simp only [Dart.colorAtIndex_index]
      rfl
    refine ⟨Dart.colorAtIndex P start, ?_⟩
    rw [hword, hm]
    simpa only [hcons] using h
  · have he : (auxiliaryBoundaryBlocks g w).getD a.val [] = [] := by
      rw [List.getD_eq_getElem _ _ (by
        simpa only [length_auxiliaryBoundaryBlocks] using a.isLt)]
      simp [auxiliaryBoundaryBlocks, hv]
    exact ⟨false, by rw [he]; simp⟩

end Cslib.Complexity.CSP.GadgetRotation
