/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ScopeJoin
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Probe
import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Relabel
import Mathlib.Data.List.OfFn
import CslibFrontier.Foundations.Data.List.OfFnPositions

/-!
# Appending disjoint ordered gadget boundaries

The two nonempty structural probes provide actual corners, even when their free labels
do not occur in the bodies. Joining the probe centers yields the concatenated boundary
word with its inherited orientation. The body is the literal left-then-right append.
All closed and nullary components survive. This joins disjoint variable supports only.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

open Cslib.Logic.PL Graph

variable {Rel V : Type} [DecidableEq V]

/-- Concatenate two distinct ordered boundary words on disjoint actual variable supports.
No body occurrence is required at a boundary label; the nonempty probes supply the corners. -/
theorem Witness.nonempty_appendOfFn {F H : CSP Rel V} {m n : ℕ}
    {p : Fin (m + 1) → V} {q : Fin (n + 1) → V}
    (w : Witness F (List.ofFn p)) (v : Witness H (List.ofFn q))
    (hd : List.Disjoint (F.vars ++ List.ofFn p) (H.vars ++ List.ofFn q))
    (hn : (List.ofFn p ++ List.ofFn q).Nodup) :
    Nonempty (Witness (F ++ H) (List.ofFn p ++ List.ofFn q)) := by
  let B : CSP (Option Rel) V := F.map (fun c => Constraint.mk (some c.rel) c.scope)
  let C : CSP (Option Rel) V := H.map (fun c => Constraint.mk (some c.rel) c.scope)
  let x : Fin (m + 1) → V := fun i => p i.rev
  let y : Fin (n + 1) → V := fun i => q i.rev
  have hF : B ++ [Constraint.mk none (List.ofFn x)] = probeBody F (List.ofFn p) := by
    simp only [probeBody, List.reverse_ofFn, B, x]
  have hH : C ++ [Constraint.mk none (List.ofFn y)] = probeBody H (List.ofFn q) := by
    simp only [probeBody, List.reverse_ofFn, C, y]
  have hw := w.probe_realization
  have hv := v.probe_realization
  rw [← hF] at hw
  rw [← hH] at hv
  obtain ⟨rho, hr, hor⟩ := hw
  obtain ⟨tau, hs, hos⟩ := hv
  have hd' : List.Disjoint (B ++ [Constraint.mk none (List.ofFn x)]).vars
      (C ++ [Constraint.mk none (List.ofFn y)]).vars := by
    rw [hF, hH]
    apply List.disjoint_left.mpr
    intro z hz hz'
    have hzF : z ∈ F.vars ++ List.ofFn p := by
      simpa only [vars_probeBody, List.mem_append, List.mem_reverse] using hz
    have hzH : z ∈ H.vars ++ List.ofFn q := by
      simpa only [vars_probeBody, List.mem_append, List.mem_reverse] using hz'
    exact List.disjoint_left.mp hd hzF hzH
  let certificate := RotationCertificate.ofRotation (scopeJoinRotation B C none x y hd' rho tau)
  have ht := verifyRotationCertificate_scopeJoinRotation B C none x y hd' rho tau hr hs hor hos
  change verifyRotationCertificate ((B ++ C) ++ [Constraint.mk none (List.ofFn (Fin.addCases y x))])
    certificate = true at ht
  have hscope : List.ofFn (Fin.addCases y x) = List.ofFn y ++ List.ofFn x := by
    rw [List.ofFn_add]
    change List.ofFn (fun i : Fin (n + 1) =>
      (Fin.addCases y x (Fin.castAdd (m + 1) i) : V)) ++
      List.ofFn (fun i : Fin (m + 1) =>
        (Fin.addCases y x (Fin.natAdd (n + 1) i) : V)) = _
    simp only [Fin.addCases_left, Fin.addCases_right]
  have htarget : ((B ++ C) ++ [Constraint.mk none (List.ofFn (Fin.addCases y x))]) =
      probeBody (F ++ H) (List.ofFn p ++ List.ofFn q) := by
    simp only [probeBody, List.map_append, List.reverse_append, List.reverse_ofFn, B, C,
      hscope, x, y]
  rw [htarget] at ht
  exact ⟨Witness.ofProbe hn certificate ht⟩

/-- Choose the checked literal body/boundary append supplied by the source witnesses. -/
noncomputable def Witness.appendOfFn {F H : CSP Rel V} {m n : ℕ}
    {p : Fin (m + 1) → V} {q : Fin (n + 1) → V}
    (w : Witness F (List.ofFn p)) (v : Witness H (List.ofFn q))
    (hd : List.Disjoint (F.vars ++ List.ofFn p) (H.vars ++ List.ofFn q))
    (hn : (List.ofFn p ++ List.ofFn q).Nodup) :
    Witness (F ++ H) (List.ofFn p ++ List.ofFn q) :=
  Classical.choice (w.nonempty_appendOfFn v hd hn)

/-- The same checked body append for ordinary nonempty boundary words. -/
noncomputable def Witness.append {F H : CSP Rel V} {x y : V} {ps qs : List V}
    (w : Witness F (x :: ps)) (v : Witness H (y :: qs))
    (hd : List.Disjoint (F.vars ++ (x :: ps)) (H.vars ++ (y :: qs)))
    (hn : ((x :: ps) ++ (y :: qs)).Nodup) :
    Witness (F ++ H) ((x :: ps) ++ (y :: qs)) := by
  let p : Fin (ps.length + 1) → V := Fin.cons x ps.get
  let q : Fin (qs.length + 1) → V := Fin.cons y qs.get
  have hp : List.ofFn p = x :: ps := by rw [List.ofFn_cons, List.ofFn_get]
  have hq : List.ofFn q = y :: qs := by rw [List.ofFn_cons, List.ofFn_get]
  let w' : Witness F (List.ofFn p) := ⟨w.certificate, by rw [hp]; exact w.accepted⟩
  let v' : Witness H (List.ofFn q) := ⟨v.certificate, by rw [hq]; exact v.accepted⟩
  let h := w'.appendOfFn v' (by rw [hp, hq]; exact hd) (by rw [hp, hq]; exact hn)
  exact ⟨h.certificate, by rw [← hp, ← hq]; exact h.accepted⟩

/-- Append two supplied nonempty boundary words, retaining exact body order. -/
noncomputable def Witness.appendWords {F H : CSP Rel V} {ps qs : List V}
    (w : Witness F ps) (v : Witness H qs) (hp : ps ≠ []) (hq : qs ≠ [])
    (hd : List.Disjoint (F.vars ++ ps) (H.vars ++ qs)) (hn : (ps ++ qs).Nodup) :
    Witness (F ++ H) (ps ++ qs) := by
  cases ps with
  | nil => exact (hp rfl).elim
  | cons x ps =>
    cases qs with
    | nil => exact (hq rfl).elim
    | cons y qs => exact w.append v hd hn

end Cslib.Complexity.CSP.OrderedBoundary
