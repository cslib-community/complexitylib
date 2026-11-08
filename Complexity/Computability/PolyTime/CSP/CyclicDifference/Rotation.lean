/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Computability.PolyTime.CSP.CyclicDifference.Program
public import Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Nullary
public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Lifting
import all Complexity.Computability.Complexity.Problems.CSP.RotationSystem.Certificate
import all Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Certificate

/-!
# Actual white-successor table and the polygon rotation

All semantic permutations here are derived from the decoded checked incidence rotation.
The executed compiler continues to use finite tables and bounded scans, not these proof-only
permutations. Nullaries remain indexed original constraint positions and add no darts.
-/

public section

namespace Cslib.Complexity.CSP.CyclicCompiler

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table
open Graph.RotationCertificate Graph.RotationSystem

variable {Rel : Type} {F : CSP Rel ℕ}

/-- Reading the argument table at an actual occurrence gives its actual cyclic successor. -/
theorem getD_argumentTable (o : F.Occurrence) :
    (argumentTable F).getD (incidenceEdgeIndex o) 0 =
      incidenceEdgeIndex (argumentPermutation F o) := by
  rw [List.getD_eq_getElem _ _ (by
    simpa only [argumentTable, List.length_map, incidenceGraph_edges] using
      incidenceEdgeIndex_lt o)]
  simp only [argumentTable, List.getElem_map, incidenceEdgeIndex]
  rw [List.getElem_idxOf (List.idxOf_lt_length_of_mem (CSP.mem_occurrences.mpr ⟨o, rfl⟩))]
  exact argumentNextIndex_occurrence o

/-- The argument successor table is a permutation of actual occurrence positions. -/
theorem argumentTable_nodup (F : CSP Rel ℕ) : (argumentTable F).Nodup := by
  apply F.occurrences_nodup.map_on
  intro a ha b hb hab
  obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp ha
  obtain ⟨p, rfl⟩ := CSP.mem_occurrences.mp hb
  change argumentNextIndex F o.1 o.2 = argumentNextIndex F p.1 p.2 at hab
  rw [argumentNextIndex_occurrence, argumentNextIndex_occurrence] at hab
  exact congrArg Occurrence.record ((argumentPermutation F).injective
    (incidenceEdgeIndex_injective hab))

/-- Bounded inverse scan computes the actual previous argument edge, including singleton scopes. -/
theorem idxOf_argumentTable (o : F.Occurrence) :
    (argumentTable F).idxOf (incidenceEdgeIndex o) =
      incidenceEdgeIndex ((argumentPermutation F).symm o) := by
  have hi : incidenceEdgeIndex ((argumentPermutation F).symm o) < (argumentTable F).length := by
    simpa only [argumentTable, List.length_map, incidenceGraph_edges] using
      incidenceEdgeIndex_lt ((argumentPermutation F).symm o)
  have he := getD_argumentTable ((argumentPermutation F).symm o)
  rw [Equiv.apply_symm_apply, List.getD_eq_getElem _ _ hi] at he
  rw [← he]
  exact (argumentTable_nodup F).idxOf_getElem _ _

/-- Inverting the supplied successor list at an actual variable end recovers precisely the
inverse variable permutation of the decoded rotation; no supplied inverse is trusted. -/
theorem idxOf_variable (cert : Graph.RotationCertificate)
    (h : verifyRotation (incidenceGraph F) cert = true) (o : F.Occurrence) :
    cert.successor.idxOf (2 * incidenceEdgeIndex o) =
      2 * incidenceEdgeIndex ((variablePermutation (decode _ cert h)).symm o) := by
  let r := decode (incidenceGraph F) cert h
  let p := (variablePermutation r).symm o
  have hi : 2 * incidenceEdgeIndex p < cert.successor.length := by
    rw [(verifyRotation_parts h).2.1]
    have := incidenceEdgeIndex_lt p
    omega
  have he : cert.successor.getD (2 * incidenceEdgeIndex p) 0 =
      2 * incidenceEdgeIndex o := by
    have he := index_decode_rotate h (incidenceDart p false)
    rw [rotate_incidenceDart_false, show variablePermutation r p = o from
      (variablePermutation r).apply_symm_apply o] at he
    simpa only [Graph.Dart.index, incidenceDart, Bool.toNat_false, Nat.add_zero] using he.symm
  rw [List.getD_eq_getElem _ _ hi] at he
  rw [← he]
  exact (verifyRotation_parts h).2.2.1.idxOf_getElem _ _

/-- The executed white table is exactly the polygon's backward-dart face successor. -/
theorem getD_whiteTable (cert : Graph.RotationCertificate)
    (h : verifyRotation (incidenceGraph F) cert = true) (o : F.Occurrence) :
    (whiteTable F cert).getD (incidenceEdgeIndex o) 0 =
      incidenceEdgeIndex ((argumentPermutation F).symm
        ((variablePermutation (decode _ cert h)).symm o)) := by
  have hi : incidenceEdgeIndex o < F.occurrences.length := by
    simpa only [incidenceGraph_edges, List.length_map] using incidenceEdgeIndex_lt o
  rw [List.getD_eq_getElem _ _ (by
    simpa only [whiteTable, List.length_map, List.length_range] using hi)]
  simp only [whiteTable, List.getElem_map, List.getElem_range, idxOf_variable cert h,
    Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  exact idxOf_argumentTable _

/-- The white permutation is derived from the actual variable and argument rotations. -/
@[expose] noncomputable def whitePermutation (r : Graph.RotationSystem (incidenceGraph F)) :
    Equiv.Perm F.Occurrence := (variablePermutation r).symm.trans (argumentPermutation F).symm

/-- Bounded white scans use precisely one clock unit per actual occurrence, including fixed
points of the permutation. -/
theorem orbitBool_white (cert : Graph.RotationCertificate)
    (h : verifyRotation (incidenceGraph F) cert = true) (o p : F.Occurrence) :
    orbitBool F.occurrences.length (whiteTable F cert) (incidenceEdgeIndex o)
      (incidenceEdgeIndex p) = true ↔
      (whitePermutation (decode _ cert h)).SameCycle o p := by
  let W := whitePermutation (decode (incidenceGraph F) cert h)
  have ht (q : F.Occurrence) : (whiteTable F cert).getD (incidenceEdgeIndex q) 0 =
      incidenceEdgeIndex (W q) := getD_whiteTable cert h q
  have hw (k : ℕ) (q : F.Occurrence) :
      walk (whiteTable F cert) k (incidenceEdgeIndex q) = incidenceEdgeIndex (W^[k] q) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [walk, Function.iterate_succ_apply', ← walk, ih, ht, Function.iterate_succ_apply']
  have hcard : Fintype.card F.Occurrence = F.occurrences.length := by
    simpa only [polygonGraph, List.length_map] using
      (length_edges_polygonGraph_eq_card F).symm
  simp only [orbitBool, List.any_eq_true, List.mem_range, decide_eq_true_eq, hw]
  rw [sameCycle_iff_bounded, hcard]
  constructor <;> rintro ⟨k, hk, he⟩ <;> refine ⟨k, hk, ?_⟩
  · exact incidenceEdgeIndex_injective he
  · exact congrArg incidenceEdgeIndex he

/-- The white orbit scan is the actual face orbit on backward polygon darts. -/
theorem sameCycle_white_iff (r : Graph.RotationSystem (incidenceGraph F))
    (o p : F.Occurrence) :
    (whitePermutation r).SameCycle o p ↔
      (polygonRotation r).faceNext.SameCycle (polygonDart o true) (polygonDart p true) := by
  have hm : Function.Semiconj (fun q : F.Occurrence => polygonDart q true)
      (whitePermutation r) (polygonRotation r).faceNext := by
    intro q
    exact (faceNext_polygonDart_true r q).symm
  constructor
  · exact fun h => h.map_of_semiconj hm
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    have hh : polygonDart (((whitePermutation r) ^ (k : ℤ)) o) true =
        polygonDart p true := by
      rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow]
      exact (hm.iterate_right k o).trans (by
        simpa only [Equiv.Perm.iterate_eq_pow] using hk)
    exact incidenceEdgeIndex_injective (congrArg (fun d => d.1.val) hh)

/-- The black orbit is the original indexed constraint position. -/
theorem sameCycle_black_iff (r : Graph.RotationSystem (incidenceGraph F))
    (o p : F.Occurrence) :
    (polygonRotation r).faceNext.SameCycle (polygonDart o false) (polygonDart p false) ↔
      o.1 = p.1 := by
  have hm : Function.Semiconj (fun q : F.Occurrence => polygonDart q false)
      (argumentPermutation F) (polygonRotation r).faceNext := by
    intro q
    exact (faceNext_polygonDart_false r q).symm
  rw [← sameCycle_argumentPermutation o p]
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
    refine ⟨(k : ℤ), ?_⟩
    have hh : polygonDart (((argumentPermutation F) ^ (k : ℤ)) o) false =
        polygonDart p false := by
      rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow]
      exact (hm.iterate_right k o).trans (by
        simpa only [Equiv.Perm.iterate_eq_pow] using hk)
    exact incidenceEdgeIndex_injective (congrArg (fun d => d.1.val) hh)
  · exact fun h => h.map_of_semiconj hm

/-- A polygon face cannot change its black/white endpoint side. -/
theorem sameCycle_polygon_side (r : Graph.RotationSystem (incidenceGraph F))
    (d e : Graph.Dart (polygonGraph F)) (h : (polygonRotation r).faceNext.SameCycle d e) :
    d.2 = e.2 := by
  have hstep (a : Graph.Dart (polygonGraph F)) : ((polygonRotation r).faceNext a).2 = a.2 := by
    obtain ⟨o, ho⟩ := exists_polygonDart a
    cases hb : a.2
    · rw [hb] at ho
      rw [← ho, faceNext_polygonDart_false]
      rfl
    · rw [hb] at ho
      rw [← ho, faceNext_polygonDart_true]
      rfl
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  have hi (n : ℕ) : ((polygonRotation r).faceNext^[n] d).2 = d.2 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', hstep, ih]
  have hh := hi k
  rw [Equiv.Perm.iterate_eq_pow, hk] at hh
  exact hh.symm

end Cslib.Complexity.CSP.CyclicCompiler
