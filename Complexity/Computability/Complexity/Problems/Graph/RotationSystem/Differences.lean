/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph.RotationSystem.Dual
public import Complexity.Foundations.Data.BitString.Parity
import Mathlib.Tactic.Abel

/-!
# Edge differences and parity on actual face orbits

Spins are functions on the original natural-number vertex names; edge differences retain
listed edge positions. Face parity sums over darts, so an edge traversed twice cancels,
while a singleton loop face counts its edge once. No bound on vertex names is used.

The permutation telescoping proof is an original reconstruction of the difference operation
in [DvorakKupec2015], Section 3, printed pp. 439–440. The numerical genus predicate is distinct
from geometric realization and from native compilation.

## Main definitions

* `Cslib.Complexity.Graph.edgeGradient`: Boolean endpoint differences.
* `Cslib.Complexity.Graph.RotationSystem.faceParity`: parity with dart multiplicities.
* `Cslib.Complexity.Graph.RotationSystem.FaceEven`: zero parity on every actual face orbit.
-/

public section

namespace Cslib.Complexity.Graph

/-- Boolean spin difference at each listed edge occurrence, including loops and parallels. -/
@[expose] def edgeGradient (G : Graph) (spin : ℕ → Bool) : Fin G.2.length → Bool :=
  fun i => spin (Dart.vertex (G := G) (i, false)) ^^
    spin (Dart.vertex (G := G) (i, true))

/-- Reading a difference from either dart gives the same endpoint exclusive or. -/
theorem edgeGradient_dart (G : Graph) (spin : ℕ → Bool) (d : Dart G) :
    G.edgeGradient spin d.1 = (spin d.vertex ^^ spin d.reverse.vertex) := by
  rcases d with ⟨i, b⟩
  cases b
  · rfl
  · exact Bool.xor_comm _ _

/-- Complementing all vertex spins leaves every edge difference unchanged. -/
theorem edgeGradient_not (G : Graph) (spin : ℕ → Bool) :
    G.edgeGradient (fun v => !(spin v)) = G.edgeGradient spin := by
  funext i
  simp [edgeGradient]

namespace RotationSystem

variable {G : Graph} (r : RotationSystem G)

open Classical in
/-- Parity of the edge labels on all darts of one actual face. The two ends of an edge are
separate summands, so repeated edge traversals have their proper multiplicity. -/
@[expose] noncomputable def faceParity (x : Fin G.2.length → Bool) (f : r.Face) : Bool :=
  parityOn (Finset.univ.filter fun d : Dart G => (Quotient.mk _ d : r.Face) = f)
    (fun d => x d.1)

/-- Every actual face orbit has even Boolean edge parity, including singleton orbits. -/
@[expose] def FaceEven (x : Fin G.2.length → Bool) : Prop :=
  ∀ f : r.Face, r.faceParity x f = false

/-- Reading face parity from a dart uses exactly its permutation orbit. -/
theorem faceParity_mk (x : Fin G.2.length → Bool) (d : Dart G) :
    r.faceParity x (Quotient.mk _ d) =
      parityOn (Finset.univ.filter fun e : Dart G => r.faceNext.SameCycle d e)
        (fun e => x e.1) := by
  classical
  unfold faceParity
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Quotient.eq,
    Equiv.Perm.SameCycle.setoid, Equiv.Perm.sameCycle_comm]

/-- Quantifying over dart representatives covers every actual face, including fixed points. -/
theorem faceEven_iff_dart (x : Fin G.2.length → Bool) :
    r.FaceEven x ↔ ∀ d : Dart G, r.faceParity x (Quotient.mk _ d) = false := by
  constructor
  · exact fun h d => h _
  · intro h f
    induction f using Quotient.inductionOn with | _ d => exact h d

/-- Canonical face IDs compute parity on the same actual orbit, with dart multiplicity. -/
theorem faceParity_eq_sum_faceId (x : Fin G.2.length → Bool) (d : Dart G) :
    r.faceParity x (Quotient.mk _ d) =
      ∑ e : Dart G, if r.faceId e = r.faceId d then x e.1 else 0 := by
  classical
  rw [faceParity_mk, parityOn_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  simp only [r.faceId_eq_iff, Equiv.Perm.sameCycle_comm]

/-- Face parity is additive in edge labels. -/
theorem faceParity_add (x y : Fin G.2.length → Bool) (f : r.Face) :
    r.faceParity (x + y) f = (r.faceParity x f ^^ r.faceParity y f) := by
  classical
  change r.faceParity (x + y) f = r.faceParity x f + r.faceParity y f
  simp only [faceParity, parityOn_eq_sum, Pi.add_apply, Finset.sum_add_distrib]

/-- Edge gradients telescope around any face, with no endpoint declaration or genus hypothesis. -/
theorem faceEven_edgeGradient (spin : ℕ → Bool) : r.FaceEven (G.edgeGradient spin) := by
  classical
  intro f
  have hv (d : Dart G) : (r.faceNext d).vertex = d.reverse.vertex := by
    change (r.rotate.symm d.reverse).vertex = d.reverse.vertex
    have h := r.vertex_rotate (r.rotate.symm d.reverse)
    simpa only [Equiv.apply_symm_apply] using h.symm
  have hs := Equiv.sum_comp r.faceNext (fun d : Dart G =>
    if (Quotient.mk _ d : r.Face) = f then spin d.vertex else (0 : Bool))
  simp only [r.face_eq_next, hv] at hs
  simp only [faceParity, parityOn_eq_sum, edgeGradient_dart,
    ← Bool.add_eq_xor, Finset.sum_add_distrib]
  simp only [Finset.sum_filter]
  rw [← hs]
  exact BooleanRing.add_self _

/-- Face-even assignments are closed under exclusive-or addition. -/
theorem FaceEven.add {x y : Fin G.2.length → Bool}
    (hx : r.FaceEven x) (hy : r.FaceEven y) : r.FaceEven (x + y) := by
  intro f
  rw [faceParity_add, hx f, hy f]
  rfl

end RotationSystem
end Cslib.Complexity.Graph
