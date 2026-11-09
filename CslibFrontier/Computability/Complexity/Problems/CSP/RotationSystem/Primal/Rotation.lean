/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.CSP.RotationSystem.Primal.Graph
public import CslibFrontier.Foundations.GroupTheory.Perm.Doubled

/-!
# The polygon rotation from an ordered incidence rotation

The variable permutation is recovered from the supplied incidence rotation, rather than assumed.
The polygon rotation replaces each variable occurrence by two consecutive darts. Its cycles are
proved to be exactly the endpoint fibers of the actual listed polygon graph. This construction
has no planarity, runtime or oracle premise.

## Main definitions

* `Cslib.Complexity.CSP.variablePermutation`: recovered variable-side incidence rotation.
* `Cslib.Complexity.CSP.polygonRotation`: actual rotation of the listed polygon graph.

## Main results

* `Cslib.Complexity.CSP.sameCycle_variablePermutation`: exact variable fibers.
* `Cslib.Complexity.CSP.rotate_polygonDart_false`,
  `Cslib.Complexity.CSP.rotate_polygonDart_true`: exact indexed successor formulas.
* `Cslib.Complexity.CSP.faceNext_polygonDart_false`,
  `Cslib.Complexity.CSP.faceNext_polygonDart_true`: exact black/white face successors.
-/

public section

namespace Cslib.Complexity.CSP

open Cslib.Logic.PL

variable {Rel V : Type} [DecidableEq V] {F : CSP Rel V}

private theorem dense_lt (o : F.Occurrence) : F.distinctVars.idxOf o.var < F.numVars := by
  rw [← CSP.length_distinctVars]
  exact List.idxOf_lt_length_of_mem (CSP.mem_distinctVars.mpr o.var_mem)

private theorem rotation_side (r : Graph.RotationSystem (incidenceGraph F))
    (d : Graph.Dart (incidenceGraph F)) : (r.rotate d).2 = d.2 := by
  obtain ⟨o, ho⟩ := exists_incidenceDart d
  obtain ⟨p, hp⟩ := exists_incidenceDart (r.rotate d)
  have hv := r.vertex_rotate d
  have hvo := vertex_incidenceDart o d.2
  have hvp := vertex_incidenceDart p (r.rotate d).2
  rw [ho] at hvo
  rw [hp] at hvp
  rw [hvo, hvp] at hv
  have hdo := dense_lt o
  have hdp := dense_lt p
  cases hd : d.2 <;> cases he : (r.rotate d).2 <;> simp only [hd, he, Bool.false_eq_true,
    ↓reduceIte] at hv ⊢ <;> omega

/-- The occurrence reached by rotating at its variable endpoint. -/
private noncomputable def variableStep (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) : F.Occurrence :=
  ((incidenceDartEquiv F).symm (r.rotate (incidenceDart o false))).1

/-- Recovery of the actual variable-side successor, including its endpoint bit. -/
private theorem incidenceDart_variableStep (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    incidenceDart (variableStep r o) false = r.rotate (incidenceDart o false) := by
  have h := (incidenceDartEquiv F).apply_symm_apply (r.rotate (incidenceDart o false))
  rw [incidenceDartEquiv_apply] at h
  have hs := rotation_side r (incidenceDart o false)
  have hb : ((incidenceDartEquiv F).symm (r.rotate (incidenceDart o false))).2 = false := by
    exact (congrArg Prod.snd h).trans hs
  simpa only [variableStep, hb] using h

/-- The variable permutation is induced by the actual incidence rotation. Its inverse recovers
an occurrence after applying the inverse rotation, not an arbitrary cyclic ordering. -/
noncomputable def variablePermutation (r : Graph.RotationSystem (incidenceGraph F)) :
    Equiv.Perm F.Occurrence where
  toFun := variableStep r
  invFun := variableStep r.mirror
  left_inv o := by
    apply incidenceDart_injective false
    change incidenceDart (variableStep r.mirror (variableStep r o)) false = _
    rw [incidenceDart_variableStep, incidenceDart_variableStep]
    exact r.rotate.symm_apply_apply _
  right_inv o := by
    apply incidenceDart_injective false
    change incidenceDart (variableStep r (variableStep r.mirror o)) false = _
    rw [incidenceDart_variableStep, incidenceDart_variableStep]
    exact r.rotate.apply_symm_apply _

/-- The induced permutation reads exactly the supplied successor at variable ends. -/
@[simp] theorem rotate_incidenceDart_false (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    r.rotate (incidenceDart o false) = incidenceDart (variablePermutation r o) false :=
  (incidenceDart_variableStep r o).symm

/-- Variable rotation does not change the original variable name. -/
theorem variablePermutation_var (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) : (variablePermutation r o).var = o.var := by
  have h := r.vertex_rotate (incidenceDart o false)
  rw [rotate_incidenceDart_false, vertex_incidenceDart, vertex_incidenceDart] at h
  exact (List.idxOf_inj (CSP.mem_distinctVars.mpr (variablePermutation r o).var_mem)).mp h

/-- The induced cycles are precisely the original equal-variable fibers. -/
theorem sameCycle_variablePermutation (r : Graph.RotationSystem (incidenceGraph F))
    (o p : F.Occurrence) :
    (variablePermutation r).SameCycle o p ↔ o.var = p.var := by
  have hm : Function.Semiconj (fun o => incidenceDart o false) (variablePermutation r)
      r.rotate := fun o => (rotate_incidenceDart_false r o).symm
  constructor
  · intro h
    have hv := (r.sameCycle_iff _ _).mp (h.map_of_semiconj hm)
    simp only [vertex_incidenceDart, Bool.false_eq_true, ↓reduceIte] at hv
    exact (List.idxOf_inj (CSP.mem_distinctVars.mpr o.var_mem)).mp hv
  · intro h
    have hv : r.rotate.SameCycle (incidenceDart o false) (incidenceDart p false) := by
      apply (r.sameCycle_iff _ _).mpr
      simp [h]
    obtain ⟨n, hn⟩ := hv.exists_nat_pow_eq
    refine ⟨(n : ℤ), ?_⟩
    apply incidenceDart_injective false
    rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow, hm.iterate_right n,
      Equiv.Perm.iterate_eq_pow, hn]

/-- Coordinates pairing the two polygon darts at an occurrence's original variable.
The second dart is the reverse side of the preceding scope edge. -/
@[expose] noncomputable def polygonBlockEquiv (F : CSP Rel V) :
    F.Occurrence × Bool ≃ Graph.Dart (polygonGraph F) :=
    ({ toFun := fun x => (if x.2 then (argumentPermutation F).symm x.1 else x.1, x.2)
       invFun := fun x => (if x.2 then argumentPermutation F x.1 else x.1, x.2)
       left_inv := by rintro ⟨o, b⟩; cases b <;> simp
       right_inv := by rintro ⟨o, b⟩; cases b <;> simp } :
      F.Occurrence × Bool ≃ F.Occurrence × Bool).trans (polygonDartEquiv F)

/-- Both members of an occurrence block are at its original dense variable. -/
@[simp] theorem vertex_polygonBlockEquiv (o : F.Occurrence) (side : Bool) :
    (polygonBlockEquiv F (o, side)).vertex = F.distinctVars.idxOf o.var := by
  cases side
  · simp [polygonBlockEquiv]
  · change (polygonDart ((argumentPermutation F).symm o) true).vertex = _
    rw [vertex_polygonDart]
    exact congrArg (fun p : F.Occurrence => F.distinctVars.idxOf p.var)
      ((argumentPermutation F).apply_symm_apply o)

/-- The actual polygon rotation. At each variable, replace its recovered occurrence cycle
by the blocks `(p_o,q_(B⁻¹ o))`. The endpoint-fiber law is a theorem of this permutation. -/
noncomputable def polygonRotation (r : Graph.RotationSystem (incidenceGraph F)) :
    Graph.RotationSystem (polygonGraph F) where
  rotate := ((polygonBlockEquiv F).symm.trans
    (Equiv.Perm.doubled (variablePermutation r))).trans (polygonBlockEquiv F)
  sameCycle_iff d e := by
    obtain ⟨x, rfl⟩ := (polygonBlockEquiv F).surjective d
    obtain ⟨y, rfl⟩ := (polygonBlockEquiv F).surjective e
    rw [Equiv.Perm.sameCycle_equiv_iff (polygonBlockEquiv F)
      (Equiv.Perm.doubled (variablePermutation r)) _ (by intro z; simp),
      Equiv.Perm.sameCycle_doubled, sameCycle_variablePermutation,
      vertex_polygonBlockEquiv, vertex_polygonBlockEquiv]
    exact (List.idxOf_inj (CSP.mem_distinctVars.mpr x.1.var_mem)).symm

/-- A variable block starts at the forward dart of its occurrence edge. -/
@[simp] theorem polygonBlockEquiv_false (o : F.Occurrence) :
    polygonBlockEquiv F (o, false) = polygonDart o false := rfl

/-- The second member is the backward dart of the preceding scope edge. -/
@[simp] theorem polygonBlockEquiv_true (o : F.Occurrence) :
    polygonBlockEquiv F (o, true) =
      polygonDart ((argumentPermutation F).symm o) true := rfl

/-- In block coordinates, the constructed successor doubles the recovered variable cycle. -/
theorem rotate_polygonBlock (r : Graph.RotationSystem (incidenceGraph F))
    (x : F.Occurrence × Bool) :
    (polygonRotation r).rotate (polygonBlockEquiv F x) =
      polygonBlockEquiv F (Equiv.Perm.doubled (variablePermutation r) x) := by
  simp [polygonRotation]

/-- Exact successor at a forward polygon dart. -/
@[simp] theorem rotate_polygonDart_false (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    (polygonRotation r).rotate (polygonDart o false) =
      polygonDart ((argumentPermutation F).symm o) true :=
  rotate_polygonBlock r (o, false)

/-- Exact successor at a backward polygon dart. -/
@[simp] theorem rotate_polygonDart_true (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    (polygonRotation r).rotate (polygonDart o true) =
      polygonDart (variablePermutation r (argumentPermutation F o)) false := by
  have h := rotate_polygonBlock r (argumentPermutation F o, true)
  simpa only [polygonBlockEquiv_true, Equiv.symm_apply_apply, Equiv.Perm.doubled,
    Equiv.coe_fn_mk, ↓reduceIte, polygonBlockEquiv_false] using h

/-- Black faces traverse each actual scope in its original cyclic order. -/
@[simp] theorem faceNext_polygonDart_false (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    (polygonRotation r).faceNext (polygonDart o false) =
      polygonDart (argumentPermutation F o) false := by
  change (polygonRotation r).rotate.symm (polygonDart o true) = _
  rw [Equiv.symm_apply_eq]
  rw [rotate_polygonDart_false, Equiv.symm_apply_apply]

/-- White faces use exactly the permutation `B⁻¹ A⁻¹` on occurrences. -/
@[simp] theorem faceNext_polygonDart_true (r : Graph.RotationSystem (incidenceGraph F))
    (o : F.Occurrence) :
    (polygonRotation r).faceNext (polygonDart o true) =
      polygonDart ((argumentPermutation F).symm ((variablePermutation r).symm o)) true := by
  change (polygonRotation r).rotate.symm (polygonDart o false) = _
  rw [Equiv.symm_apply_eq]
  rw [rotate_polygonDart_true, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Cslib.Complexity.CSP
