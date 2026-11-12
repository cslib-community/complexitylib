/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.Disjoint
public import CslibFrontier.Logics.Propositional.CSP.Planar.Embedding.ConstraintJoin
import CslibFrontier.Foundations.Logic.Function.UpdateKernel
import CslibFrontier.Foundations.GroupTheory.Perm.Fin

/-!
# Joining the two structural probe centers

The source rows are left body, left probe, right body, right probe. Target rows are left
body, right body, one probe with right scope followed by left scope. Every old argument
occurrence is retained at its explicit target position. The two probe centers are the only
constraint fibers identified. These are positional constructions on the actual CSP lists.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL Cslib.Logic.PL.CSP Graph Graph.RotationSystem

variable {Rel V : Type} {m n : ℕ}

/-- Source coordinates for two bodies, each followed by its own probe scope. -/
@[expose] noncomputable def scopeJoinSourceEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) :
    (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n) ≃
      ((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])).Occurrence :=
  (Equiv.sumCongr (appendOfFnOccurrenceEquiv F r x) (appendOfFnOccurrenceEquiv H r y)).trans
    (appendOccurrenceEquiv _ _)

/-- Target coordinates retain both body blocks and put right probe arguments before left.
The concatenated scope has the same positive cyclic orientation after the center splice. -/
@[expose] noncomputable def scopeJoinTargetEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) :
    (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n) ≃
      ((F ++ H) ++ [(r, List.ofFn (Fin.addCases y x))]).Occurrence :=
  (Equiv.sumSumSumComm F.Occurrence (Fin m) H.Occurrence (Fin n)).trans
    ((Equiv.sumCongr (appendOccurrenceEquiv F H)
      ((Equiv.sumComm (Fin m) (Fin n)).trans finSumFinEquiv)).trans
        (appendOfFnOccurrenceEquiv (F ++ H) r (Fin.addCases y x)))

/-- Every source edge occurrence has its exact target occurrence in the joined-scope body. -/
@[expose] noncomputable def scopeJoinOccurrenceEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) :
    ((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])).Occurrence ≃
      ((F ++ H) ++ [(r, List.ofFn (Fin.addCases y x))]).Occurrence :=
  (scopeJoinSourceEquiv F H r x y).symm.trans (scopeJoinTargetEquiv F H r x y)

private theorem source_left (F H : CSP Rel V) (r : Rel) (x : Fin m → V) (y : Fin n → V)
    (a : F.Occurrence ⊕ Fin m) :
    scopeJoinSourceEquiv F H r x y (Sum.inl a) = appendOccurrenceEquiv _ _
      (Sum.inl (appendOfFnOccurrenceEquiv F r x a)) := rfl

private theorem source_right (F H : CSP Rel V) (r : Rel) (x : Fin m → V) (y : Fin n → V)
    (a : H.Occurrence ⊕ Fin n) :
    scopeJoinSourceEquiv F H r x y (Sum.inr a) = appendOccurrenceEquiv _ _
      (Sum.inr (appendOfFnOccurrenceEquiv H r y a)) := rfl

private theorem target_body_left (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) (o : F.Occurrence) :
    scopeJoinTargetEquiv F H r x y (Sum.inl (Sum.inl o)) =
      appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
        (Sum.inl (appendOccurrenceEquiv F H (Sum.inl o))) := rfl

private theorem target_body_right (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) (o : H.Occurrence) :
    scopeJoinTargetEquiv F H r x y (Sum.inr (Sum.inl o)) =
      appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
        (Sum.inl (appendOccurrenceEquiv F H (Sum.inr o))) := rfl

private theorem target_probe_left (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) (i : Fin m) :
    scopeJoinTargetEquiv F H r x y (Sum.inl (Sum.inr i)) =
      appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr (Fin.natAdd n i)) := rfl

private theorem target_probe_right (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) (i : Fin n) :
    scopeJoinTargetEquiv F H r x y (Sum.inr (Sum.inr i)) =
      appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr (Fin.castAdd m i)) := rfl

/-- Full source records in the four literal body/probe blocks. -/
theorem record_scopeJoinSourceEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V)
    (a : (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n)) :
    (scopeJoinSourceEquiv F H r x y a).record = match a with
      | Sum.inl (Sum.inl o) => o.record
      | Sum.inl (Sum.inr i) => (F.length, i.val, x i)
      | Sum.inr (Sum.inl o) => (F.length + 1 + o.1.val, o.2.val, o.var)
      | Sum.inr (Sum.inr i) => (F.length + 1 + H.length, i.val, y i) := by
  rcases a with (o | i) | (o | i)
  · change (appendOccurrenceEquiv _ _ (Sum.inl (appendOfFnOccurrenceEquiv F r x
      (Sum.inl o)))).record = _
    rw [record_appendOccurrenceEquiv_inl, record_appendOfFnOccurrenceEquiv_inl]
  · change (appendOccurrenceEquiv _ _ (Sum.inl (appendOfFnOccurrenceEquiv F r x
      (Sum.inr i)))).record = _
    rw [record_appendOccurrenceEquiv_inl, record_appendOfFnOccurrenceEquiv_inr]
  · change (appendOccurrenceEquiv _ _ (Sum.inr (appendOfFnOccurrenceEquiv H r y
      (Sum.inl o)))).record = _
    rw [record_appendOccurrenceEquiv_inr]
    have he := record_appendOfFnOccurrenceEquiv_inl H r y o
    have hc := congrArg Prod.fst he
    have hj := congrArg (fun record => record.2.1) he
    have hv := congrArg (fun record => record.2.2) he
    simp only [CSP.Occurrence.record] at hc hj hv
    simp only [List.length_append, List.length_singleton, hc, hj, hv]
  · change (appendOccurrenceEquiv _ _ (Sum.inr (appendOfFnOccurrenceEquiv H r y
      (Sum.inr i)))).record = _
    rw [record_appendOccurrenceEquiv_inr]
    have he := record_appendOfFnOccurrenceEquiv_inr H r y i
    have hc := congrArg Prod.fst he
    have hj := congrArg (fun record => record.2.1) he
    have hv := congrArg (fun record => record.2.2) he
    simp only [CSP.Occurrence.record] at hc hj hv
    simp only [List.length_append, List.length_singleton, hc, hj, hv]

/-- Full target records retain original body order and the specified right-then-left probe. -/
theorem record_scopeJoinTargetEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V)
    (a : (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n)) :
    (scopeJoinTargetEquiv F H r x y a).record = match a with
      | Sum.inl (Sum.inl o) => o.record
      | Sum.inl (Sum.inr i) => (F.length + H.length, n + i.val, x i)
      | Sum.inr (Sum.inl o) => (F.length + o.1.val, o.2.val, o.var)
      | Sum.inr (Sum.inr i) => (F.length + H.length, i.val, y i) := by
  rcases a with (o | i) | (o | i)
  · change (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inl (appendOccurrenceEquiv F H (Sum.inl o)))).record = _
    rw [record_appendOfFnOccurrenceEquiv_inl, record_appendOccurrenceEquiv_inl]
  · change (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inr (Fin.natAdd n i))).record = _
    rw [record_appendOfFnOccurrenceEquiv_inr]
    simp only [List.length_append, Fin.val_natAdd, Fin.addCases_right]
  · change (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inl (appendOccurrenceEquiv F H (Sum.inr o)))).record = _
    rw [record_appendOfFnOccurrenceEquiv_inl, record_appendOccurrenceEquiv_inr]
  · change (appendOfFnOccurrenceEquiv _ r (Fin.addCases y x)
      (Sum.inr (Fin.castAdd m i))).record = _
    rw [record_appendOfFnOccurrenceEquiv_inr]
    simp only [List.length_append, Fin.val_castAdd, Fin.addCases_left]

/-- The occurrence map leaves every actual variable label unchanged. -/
theorem var_scopeJoinOccurrenceEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V)
    (o : ((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])).Occurrence) :
    (scopeJoinOccurrenceEquiv F H r x y o).var = o.var := by
  obtain ⟨a, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective o
  have hs := congrArg (fun record => record.2.2) (record_scopeJoinSourceEquiv F H r x y a)
  have ht := congrArg (fun record => record.2.2) (record_scopeJoinTargetEquiv F H r x y a)
  change (scopeJoinTargetEquiv F H r x y
    ((scopeJoinSourceEquiv F H r x y).symm (scopeJoinSourceEquiv F H r x y a))).var = _
  rw [Equiv.symm_apply_apply]
  rcases a with (o | i) | (o | i) <;> exact ht.trans hs.symm

/-- The target constraint fibers are exactly the source fibers with the two probe centers
identified. This guard is about positions, including list-identical rows and nullaries. -/
theorem constraint_scopeJoinOccurrenceEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V)
    (o p : ((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])).Occurrence) :
    (scopeJoinOccurrenceEquiv F H r x y o).1 = (scopeJoinOccurrenceEquiv F H r x y p).1 ↔
      Function.update id (F.length + 1 + H.length) F.length o.1.val =
        Function.update id (F.length + 1 + H.length) F.length p.1.val := by
  obtain ⟨a, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective o
  obtain ⟨b, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective p
  have hsa := congrArg Prod.fst (record_scopeJoinSourceEquiv F H r x y a)
  have hsb := congrArg Prod.fst (record_scopeJoinSourceEquiv F H r x y b)
  have hta := congrArg Prod.fst (record_scopeJoinTargetEquiv F H r x y a)
  have htb := congrArg Prod.fst (record_scopeJoinTargetEquiv F H r x y b)
  change (scopeJoinTargetEquiv F H r x y
      ((scopeJoinSourceEquiv F H r x y).symm (scopeJoinSourceEquiv F H r x y a))).1 =
    (scopeJoinTargetEquiv F H r x y
      ((scopeJoinSourceEquiv F H r x y).symm (scopeJoinSourceEquiv F H r x y b))).1 ↔ _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Fin.ext_iff]
  rw [Function.update_id_apply_eq_iff]
  rcases a with (a | i) | (a | i) <;> rcases b with (b | j) | (b | j) <;>
    simp only [CSP.Occurrence.record] at hsa hsb hta htb <;>
    try { have := a.1.isLt; have := b.1.isLt; omega } <;>
    try { have := a.1.isLt; omega } <;> try { have := b.1.isLt; omega } <;> omega

private theorem argumentSuccessor_source (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V)
    (a : (F.Occurrence ⊕ Fin m) ⊕ (H.Occurrence ⊕ Fin n)) :
    argumentSuccessor (scopeJoinSourceEquiv F H r x y a) =
      scopeJoinSourceEquiv F H r x y (Sum.map
        (Sum.map argumentSuccessor (finRotate m))
        (Sum.map argumentSuccessor (finRotate n)) a) := by
  rcases a with (o | i) | (o | i)
  · rw [source_left, argumentSuccessor_appendOccurrenceEquiv]
    simp only [Sum.map_inl]
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inl]
    rfl
  · rw [source_left, argumentSuccessor_appendOccurrenceEquiv]
    simp only [Sum.map_inl]
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr]
    rfl
  · rw [source_right, argumentSuccessor_appendOccurrenceEquiv]
    simp only [Sum.map_inr]
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inl]
    rfl
  · rw [source_right, argumentSuccessor_appendOccurrenceEquiv]
    simp only [Sum.map_inr]
    rw [argumentSuccessor_appendOfFnOccurrenceEquiv_inr]
    rfl

private theorem argumentSuccessor_target_splice (F H : CSP Rel V) (r : Rel)
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (a : (F.Occurrence ⊕ Fin (m + 1)) ⊕ (H.Occurrence ⊕ Fin (n + 1))) :
    argumentSuccessor (scopeJoinTargetEquiv F H r x y a) =
      scopeJoinTargetEquiv F H r x y (Sum.map
        (Sum.map argumentSuccessor (finRotate (m + 1)))
        (Sum.map argumentSuccessor (finRotate (n + 1)))
        (Equiv.swap (Sum.inl (Sum.inr (Fin.last m)))
          (Sum.inr (Sum.inr (Fin.last n))) a)) := by
  classical
  rcases a with (o | i) | (o | i)
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
    rw [target_body_left, argumentSuccessor_appendOfFnOccurrenceEquiv_inl,
      argumentSuccessor_appendOccurrenceEquiv]
    rfl
  · by_cases hi : i = Fin.last m
    · subst i
      rw [Equiv.swap_apply_left]
      simp only [Sum.map_inr, finRotate_last]
      rw [target_probe_left, argumentSuccessor_appendOfFnOccurrenceEquiv_inr, target_probe_right]
      apply congrArg (fun j => appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr j))
      apply Fin.ext
      rw [val_finRotate]
      simp only [Fin.val_natAdd, Fin.val_last, Fin.val_castAdd, Fin.val_zero]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne (by simpa using hi) (by simp)]
      simp only [Sum.map_inl, Sum.map_inr]
      rw [target_probe_left, argumentSuccessor_appendOfFnOccurrenceEquiv_inr, target_probe_left]
      apply congrArg (fun j => appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr j))
      apply Fin.ext
      have hib := i.isLt
      have hin : i.val ≠ m := fun he => hi (Fin.ext he)
      rw [val_finRotate]
      simp only [Fin.val_natAdd, val_finRotate]
      split_ifs <;> omega
  · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]
    rw [target_body_right, argumentSuccessor_appendOfFnOccurrenceEquiv_inl,
      argumentSuccessor_appendOccurrenceEquiv]
    rfl
  · by_cases hi : i = Fin.last n
    · subst i
      rw [Equiv.swap_apply_right]
      simp only [Sum.map_inl, Sum.map_inr, finRotate_last]
      rw [target_probe_right, argumentSuccessor_appendOfFnOccurrenceEquiv_inr, target_probe_left]
      apply congrArg (fun j => appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr j))
      apply Fin.ext
      rw [val_finRotate]
      simp only [Fin.val_natAdd, Fin.val_last, Fin.val_castAdd, Fin.val_zero]
      split_ifs <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp) (by simpa using hi)]
      simp only [Sum.map_inr]
      rw [target_probe_right, argumentSuccessor_appendOfFnOccurrenceEquiv_inr, target_probe_right]
      apply congrArg (fun j => appendOfFnOccurrenceEquiv _ r (Fin.addCases y x) (Sum.inr j))
      apply Fin.ext
      have hib := i.isLt
      have hin : i.val ≠ n := fun he => hi (Fin.ext he)
      rw [val_finRotate]
      simp only [Fin.val_castAdd, val_finRotate]
      split_ifs <;> omega

/-- Joining the last outgoing corner at each probe center gives exactly the target positive
argument cycles, with no reflected scope or arbitrary all-port conjunction principle. -/
theorem argumentSuccessor_scopeJoinOccurrenceEquiv (F H : CSP Rel V) (r : Rel)
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (o : ((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])).Occurrence) :
    scopeJoinOccurrenceEquiv F H r x y (argumentSuccessor (Equiv.swap
      (scopeJoinSourceEquiv F H r x y (Sum.inl (Sum.inr (Fin.last m))))
      (scopeJoinSourceEquiv F H r x y (Sum.inr (Sum.inr (Fin.last n)))) o)) =
        argumentSuccessor (scopeJoinOccurrenceEquiv F H r x y o) := by
  classical
  obtain ⟨a, rfl⟩ := (scopeJoinSourceEquiv F H r x y).surjective o
  rw [← (scopeJoinSourceEquiv F H r x y).injective.map_swap]
  rw [argumentSuccessor_source]
  simp only [scopeJoinOccurrenceEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact (argumentSuccessor_target_splice F H r x y a).symm

variable [DecidableEq V]

private theorem source_probe_left_vertex (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) (i : Fin m) :
    (incidenceDart (scopeJoinSourceEquiv F H r x y (Sum.inl (Sum.inr i))) true).vertex =
      (((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])) : CSP Rel V).numVars +
        F.length := by
  rw [vertex_incidenceDart]
  simp only [ite_true]
  exact congrArg (fun record =>
    (((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])) : CSP Rel V).numVars + record.1)
      (record_scopeJoinSourceEquiv F H r x y (Sum.inl (Sum.inr i)))

private theorem source_probe_right_vertex (F H : CSP Rel V) (r : Rel)
    (x : Fin m → V) (y : Fin n → V) (i : Fin n) :
    (incidenceDart (scopeJoinSourceEquiv F H r x y (Sum.inr (Sum.inr i))) true).vertex =
      (((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])) : CSP Rel V).numVars +
        (F.length + 1 + H.length) := by
  rw [vertex_incidenceDart]
  simp only [ite_true]
  exact congrArg (fun record =>
    (((F ++ [(r, List.ofFn x)]) ++ (H ++ [(r, List.ofFn y)])) : CSP Rel V).numVars + record.1)
      (record_scopeJoinSourceEquiv F H r x y (Sum.inr (Sum.inr i)))

/-- Join the two actual probe centers at their last outgoing corners. Both probe scopes
are nonempty, so their actual constraint darts supply the corners even for empty bodies. -/
@[expose] noncomputable def scopeJoinRotation (F H : CSP Rel V) (r : Rel)
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (hd : List.Disjoint (F ++ [(r, List.ofFn x)]).vars (H ++ [(r, List.ofFn y)]).vars)
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn x)])))
    (tau : RotationSystem (incidenceGraph (H ++ [(r, List.ofFn y)]))) :
    RotationSystem (incidenceGraph ((F ++ H) ++ [(r, List.ofFn (Fin.addCases y x))])) :=
  constraintJoinRotation (scopeJoinOccurrenceEquiv F H r x y)
    F.length (F.length + 1 + H.length) (by omega)
    (incidenceDart (scopeJoinSourceEquiv F H r x y (Sum.inl (Sum.inr (Fin.last m)))) true)
    (incidenceDart (scopeJoinSourceEquiv F H r x y (Sum.inr (Sum.inr (Fin.last n)))) true)
    (by exact source_probe_left_vertex F H r x y (Fin.last m))
    (by exact source_probe_right_vertex F H r x y (Fin.last n))
    (by intro o p; rw [var_scopeJoinOccurrenceEquiv, var_scopeJoinOccurrenceEquiv])
    (constraint_scopeJoinOccurrenceEquiv F H r x y)
    (appendRotation _ _ hd rho tau)

/-- Different components are derived from the actual disjoint source supports. The target
genus is proved from the two source genera and the literal center splice. -/
theorem numericalGenusZero_scopeJoinRotation (F H : CSP Rel V) (r : Rel)
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (hd : List.Disjoint (F ++ [(r, List.ofFn x)]).vars (H ++ [(r, List.ofFn y)]).vars)
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn x)])))
    (tau : RotationSystem (incidenceGraph (H ++ [(r, List.ofFn y)])))
    (hr : rho.NumericalGenusZero) (hs : tau.NumericalGenusZero) :
    (scopeJoinRotation F H r x y hd rho tau).NumericalGenusZero := by
  unfold scopeJoinRotation
  apply numericalGenusZero_constraintJoinRotation
  · exact numericalGenusZero_appendRotation _ _ hd rho tau hr hs
  · rw [source_left, source_right, ← appendDartEquiv_inl, ← appendDartEquiv_inr]
    rw [sameComponent_transport_iff _ (appendDartEquiv_vertex_eq_iff _ _ hd)
      (reverse_appendDartEquiv _ _)
      (endpoints_declared_disjointUnion _ _ (incidenceVertices_declared _)
        (incidenceVertices_declared _)) (incidenceVertices_declared _),
      sameComponent_disjointUnion_iff (incidenceVertices_declared _)
        (incidenceVertices_declared _)]
    exact not_false

/-- Every original body constraint keeps its directed order, and the two probe cycles
become the precise positive cyclic concatenation specified by the target scope. -/
theorem respectsArgumentOrder_scopeJoinRotation (F H : CSP Rel V) (r : Rel)
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (hd : List.Disjoint (F ++ [(r, List.ofFn x)]).vars (H ++ [(r, List.ofFn y)]).vars)
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn x)])))
    (tau : RotationSystem (incidenceGraph (H ++ [(r, List.ofFn y)])))
    (hr : RespectsArgumentOrder rho) (hs : RespectsArgumentOrder tau) :
    RespectsArgumentOrder (scopeJoinRotation F H r x y hd rho tau) := by
  intro p
  obtain ⟨o, rfl⟩ := (scopeJoinOccurrenceEquiv F H r x y).surjective p
  rw [← occurrenceDartEquiv_apply]
  unfold scopeJoinRotation
  rw [rotate_constraintJoinRotation, ← (incidenceDart_injective true).map_swap]
  rw [(respectsArgumentOrder_appendRotation _ _ hd rho tau hr hs) _,
    occurrenceDartEquiv_apply, argumentSuccessor_scopeJoinOccurrenceEquiv]

/-- The full target checker accepts the actual joined-scope table from source ordered
numerical rotations, without a target certificate or genus premise. -/
theorem verifyRotationCertificate_scopeJoinRotation (F H : CSP Rel V) (r : Rel)
    (x : Fin (m + 1) → V) (y : Fin (n + 1) → V)
    (hd : List.Disjoint (F ++ [(r, List.ofFn x)]).vars (H ++ [(r, List.ofFn y)]).vars)
    (rho : RotationSystem (incidenceGraph (F ++ [(r, List.ofFn x)])))
    (tau : RotationSystem (incidenceGraph (H ++ [(r, List.ofFn y)])))
    (hr : rho.NumericalGenusZero) (hs : tau.NumericalGenusZero)
    (hor : RespectsArgumentOrder rho) (hos : RespectsArgumentOrder tau) :
    verifyRotationCertificate ((F ++ H) ++ [(r, List.ofFn (Fin.addCases y x))])
      (RotationCertificate.ofRotation (scopeJoinRotation F H r x y hd rho tau)) = true :=
  verifyRotationCertificate_ofRotation _
    (numericalGenusZero_scopeJoinRotation F H r x y hd rho tau hr hs)
    (respectsArgumentOrder_scopeJoinRotation F H r x y hd rho tau hor hos)

end Cslib.Complexity.CSP
