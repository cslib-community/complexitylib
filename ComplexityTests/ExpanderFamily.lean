/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap
import Complexity.Foundations.Combinatorics.Expander.AffineFamily
import Complexity.Computability.PCP.Preprocess

/-!
# Indexed arithmetic expander families

Concrete rotations exercise the actual family, without enumerating its enormous label type.
The positive gap, size selection and semantic wrapper have nonvacuous instances. Reindexing
certificates retain arbitrary vertex encodings and charge both directions of the equivalence.
-/

namespace ComplexityTests.ExpanderFamily

open Cslib Turing.MultiTapeTM

-- The occupied branch moves to another vertex and returns the original dart in the reverse call.
example : (RotationMap.arithmeticExpander 3).rot (2, .inl (0, ((1, 2), (3, 4)))) =
    (0, .inl (74433099665838173, ((1, 2), (0, 0)))) := by decide

example : (RotationMap.arithmeticExpander 3).rot
    (0, .inl (74433099665838173, ((1, 2), (0, 0)))) =
      (2, .inl (0, ((1, 2), (3, 4)))) := by decide

-- Laziness and the unused-slot fallback are different self-loop branches.
example : (RotationMap.arithmeticExpander 3).rot (0, .inr (0, ((1, 2), (3, 4)))) =
    (0, .inr (0, ((1, 2), (3, 4)))) := by decide

private def unusedSlot : Fin (257 ^ 8) := ⟨257 ^ 8 - 1, by decide⟩

example : (RotationMap.arithmeticExpander 3).rot (2, .inl (unusedSlot, ((1, 2), (3, 4)))) =
    (2, .inl (unusedSlot, ((1, 2), (3, 4)))) := by decide

example : (RotationMap.arithmeticExpander 1).rot (0, .inl (0, ((1, 2), (3, 4)))) =
    (0, .inl (0, ((1, 2), (3, 4)))) := by decide

example : (RotationMap.arithmeticExpander 0).spectralExpansion = 0 :=
  RotationMap.spectralExpansion_eq_zero_of_subsingleton _

-- Pairing indices is executable in both directions, including levels above the base.
example : (IteratedProd.equivFin (Equiv.refl (Fin 3)) (Equiv.refl (Fin 2)) 2)
    (((2 : Fin 3), 0), 1) = 9 := by decide

example : (RotationMap.ZigzagTowerVertex.equivFin (Equiv.refl (Fin 2)) 2)
    (((1 : Fin 2), 0), 1) = 5 := by decide

example : (RotationMap.ZigzagTowerVertex.equivFin (Equiv.refl (Fin 2)) 2).symm 5 =
    (((1 : Fin 2), 0), 1) := by
  apply (RotationMap.ZigzagTowerVertex.equivFin (Equiv.refl (Fin 2)) 2).injective
  rw [Equiv.apply_symm_apply]
  decide

example : Nat.clog 2 9 - 1 = 3 := by decide
example : 9 ≤ 2 ^ (Nat.clog 2 9 - 1 + 1) ∧ 2 ^ (Nat.clog 2 9 - 1 + 1) ≤ 2 * 9 :=
  RotationMap.zigzagTower_size_bounds (by decide) (by decide)

-- This selects the second tower graph and executes the full round trip, without enumeration.
example : let p : Fin (257 ^ 8 + 1) × RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257 :=
      (257 ^ 8, .inl (0, ((1, 2), (3, 4))))
    (RotationMap.arithmeticExpander (257 ^ 8 + 1)).rot
      ((RotationMap.arithmeticExpander (257 ^ 8 + 1)).rot p) = p := by decide

example {V : Type*} [Fintype V] :
    (RotationMap.arithmeticExpanderFamily.graph V).spectralExpansion < 1 := by
  linarith [RotationMap.arithmeticExpanderFamily.spectralExpansion_graph_le V]

-- The mathematical PCP preprocessing accepts the arithmetic expander family and substitutes its
-- concrete degree `2 * 257 ^ 12`.
example {V E α : Type*} [Fintype E] [DecidableEq V] (G : PCP.ConstraintGraph V E α) :
    (G.preprocess RotationMap.arithmeticExpanderFamily).graph.spectralExpansion ≤
      1 - (1 - (1 - 9 / (400 * (257 : ℝ) ^ 16))) *
        ((2 * 257 ^ 12 : ℕ) : ℝ) / (2 * ((2 * 257 ^ 12 : ℕ) : ℝ) + 2) := by
  have hcard := RotationMap.card_affinePlaneFamilyLabel (ZMod.finEquiv 257).toEquiv.symm
  simpa only [hcard] using G.spectralExpansion_preprocess_le RotationMap.arithmeticExpanderFamily

example {V E α : Type*} [Fintype E] [DecidableEq V] [Nonempty α]
    (G : PCP.ConstraintGraph V E α) :
    (G.preprocess RotationMap.arithmeticExpanderFamily).toConstraintGraph.Satisfiable ↔
      G.Satisfiable :=
  G.satisfiable_preprocess_iff RotationMap.arithmeticExpanderFamily (by norm_num)

-- A reindexing certificate requires the rotation and both directions of the representation map.
example {V W D : Type} (G : RotationMap V D) (e : V ≃ W)
    (ev : V ↪ List Bool) (ew : W ↪ List Bool) (ed : D ↪ List Bool)
    (hf : ComputableInPolyTime e ev ew)
    (hb : ComputableInPolyTime e.symm ew ev)
    (hg : ComputableInPolyTime G.rot (encPair ev ed) (encPair ev ed)) :
    ComputableInPolyTime
      (fun p : (W × D) × Bool =>
        let next := (G.reindex e).rot p.1
        (next, !p.2))
      (encPair (encPair ew ed) encBool) (encPair (encPair ew ed) encBool) := by
  fail_if_success (clear hf; fun_prop)
  fail_if_success (clear hb; fun_prop)
  fail_if_success (clear hg; fun_prop)
  fun_prop

-- A concrete equivalence on an unbounded type uses structural encodings in either order.
example (G : RotationMap (Bool × List Bool) Bool)
    (hg : ComputableInPolyTime G.rot
      (encPair (encPair encBool encBits) encBool)
      (encPair (encPair encBool encBits) encBool)) :
    ComputableInPolyTime (G.reindex (Equiv.prodComm Bool (List Bool))).rot
      (encPair (encPair encBits encBool) encBool)
      (encPair (encPair encBits encBool) encBool) := by
  simp only [RotationMap.reindex, Equiv.prodComm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
  fun_prop [Prod.swap]

end ComplexityTests.ExpanderFamily
