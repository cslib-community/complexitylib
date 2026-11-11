/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver for the BEST theorem)

import CslibFrontier.Foundations.Combinatorics.Multidigraph.BEST

/-!
# Regression tests for the BEST theorem

On two vertices the reduced Laplacian at `0` is the `1 × 1` matrix `(A 1 0)`, so the BEST theorem
counts Eulerian circuits from the number of arcs `1 → 0`:

* the doubled `2`-cycle (two arcs each way) has `2` Eulerian circuits starting with a fixed arc,
  and both are exhibited;
* the `2`-cycle with a loop at `1` has `1`, since loops do not contribute;
* two disjoint loops form a balanced multidigraph without Eulerian circuits.

On the bidirected triangle the reduced Laplacian is a genuine `2 × 2` determinant, `3`: there are
`3` spanning in-arborescences and `3` Eulerian circuits starting with a fixed arc, all exhibited.

A single loop at `0` next to an isolated vertex `1` has one Eulerian circuit but no spanning
arborescence, so the hypothesis that every vertex has an outgoing arc is needed. A single arc
`0 → 1` is unbalanced and has no Eulerian circuit.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BEST

open Cslib.Multidigraph Matrix

/-- The reduced Laplacian at `0` of a matrix on `Fin 2` is `A 1 0`. -/
theorem det_laplacian_submatrix_zero {R : Type*} [CommRing R] (A : Matrix (Fin 2) (Fin 2) R) :
    (A.laplacian.submatrix (Subtype.val : {v : Fin 2 // v ≠ 0} → Fin 2) Subtype.val).det =
      A 1 0 := by
  refine (det_submatrix_equiv_self (finSuccAboveEquiv (0 : Fin 2))
    (A.laplacian.submatrix (Subtype.val : {v : Fin 2 // v ≠ 0} → Fin 2) Subtype.val)).symm.trans
    ?_
  rw [submatrix_submatrix, det_unique]
  simp [laplacian_apply, Fin.sum_univ_two, finSuccAboveEquiv]

/-! ### The doubled `2`-cycle -/

/-- The doubled `2`-cycle: arcs `0, 1 : 0 → 1` and `2, 3 : 1 → 0`. -/
def src₂ : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- The doubled `2`-cycle: arcs `0, 1 : 0 → 1` and `2, 3 : 1 → 0`. -/
def tgt₂ : Fin 4 → Fin 2 := ![1, 1, 0, 0]

-- Both Eulerian circuits starting with the arc `0`.
example : IsEulerianCircuit src₂ tgt₂ 0 [0, 2, 1, 3] :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

example : IsEulerianCircuit src₂ tgt₂ 0 [0, 3, 1, 2] :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

-- The arc `2 : 1 → 0` is a spanning in-arborescence rooted at `0`.
example : IsInArborescence src₂ tgt₂ 0 fun _ => 2 := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · obtain ⟨v, hv⟩ := v
    fin_cases v
    · exact absurd rfl hv
    · rfl
  · fin_cases v
    · exact .refl
    · exact .single ⟨by decide, rfl⟩

/-- The doubled `2`-cycle has `2` Eulerian circuits starting with a fixed arc. -/
example : Nat.card {l : List (Fin 4) // IsEulerianCircuit src₂ tgt₂ 0 l} = 2 := by
  have h := natCard_isEulerianCircuit_eq_det_mul src₂ tgt₂ ℤ (by decide)
    (fun v => by fin_cases v; exacts [⟨0, rfl⟩, ⟨2, rfl⟩]) 0
  have hsrc : src₂ 0 = 0 := rfl
  rw [hsrc, det_laplacian_submatrix_zero, arcMatrix_apply, Fin.prod_univ_two] at h
  have h1 : (Finset.univ.filter fun e => src₂ e = 1 ∧ tgt₂ e = 0).card = 2 := by decide
  have h2 : (Finset.univ.filter fun e => src₂ e = 0).card = 2 := by decide
  have h3 : (Finset.univ.filter fun e => src₂ e = 1).card = 2 := by decide
  rw [h1, h2, h3] at h
  norm_num at h
  exact_mod_cast h

/-! ### A loop does not contribute -/

/-- The `2`-cycle with a loop at `1`: arcs `0 : 0 → 1`, `1 : 1 → 0` and `2 : 1 → 1`. -/
def srcLoop : Fin 3 → Fin 2 := ![0, 1, 1]

/-- The `2`-cycle with a loop at `1`: arcs `0 : 0 → 1`, `1 : 1 → 0` and `2 : 1 → 1`. -/
def tgtLoop : Fin 3 → Fin 2 := ![1, 0, 1]

example : IsEulerianCircuit srcLoop tgtLoop 0 [0, 2, 1] :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

/-- The `2`-cycle with a loop has `1` Eulerian circuit starting with a fixed arc. -/
example : Nat.card {l : List (Fin 3) // IsEulerianCircuit srcLoop tgtLoop 0 l} = 1 := by
  have h := natCard_isEulerianCircuit_eq_det_mul srcLoop tgtLoop ℤ (by decide)
    (fun v => by fin_cases v; exacts [⟨0, rfl⟩, ⟨1, rfl⟩]) 0
  have hsrc : srcLoop 0 = 0 := rfl
  rw [hsrc, det_laplacian_submatrix_zero, arcMatrix_apply, Fin.prod_univ_two] at h
  have h1 : (Finset.univ.filter fun e => srcLoop e = 1 ∧ tgtLoop e = 0).card = 1 := by decide
  have h2 : (Finset.univ.filter fun e => srcLoop e = 0).card = 1 := by decide
  have h3 : (Finset.univ.filter fun e => srcLoop e = 1).card = 2 := by decide
  rw [h1, h2, h3] at h
  norm_num at h
  exact_mod_cast h

/-! ### Two disjoint loops -/

/-- Two disjoint loops, `0 : 0 → 0` and `1 : 1 → 1`. -/
def srcTwoLoops : Fin 2 → Fin 2 := id

/-- A balanced multidigraph that is not connected has no Eulerian circuit. -/
example : Nat.card {l : List (Fin 2) // IsEulerianCircuit srcTwoLoops srcTwoLoops 0 l} = 0 := by
  have h := natCard_isEulerianCircuit_eq_det_mul srcTwoLoops srcTwoLoops ℤ (fun _ => rfl)
    (fun v => ⟨v, rfl⟩) 0
  have hsrc : srcTwoLoops 0 = 0 := rfl
  rw [hsrc, det_laplacian_submatrix_zero, arcMatrix_apply] at h
  have h1 : (Finset.univ.filter fun e => srcTwoLoops e = 1 ∧ srcTwoLoops e = 0).card = 0 := by
    decide
  rw [h1] at h
  norm_num at h
  exact_mod_cast h

/-! ### The bidirected triangle -/

/-- The bidirected triangle: arcs `0 : 0 → 1`, `1 : 1 → 0`, `2 : 1 → 2`, `3 : 2 → 1`,
`4 : 2 → 0` and `5 : 0 → 2`. -/
def srcTri : Fin 6 → Fin 3 := ![0, 1, 1, 2, 2, 0]

/-- The bidirected triangle: arcs `0 : 0 → 1`, `1 : 1 → 0`, `2 : 1 → 2`, `3 : 2 → 1`,
`4 : 2 → 0` and `5 : 0 → 2`. -/
def tgtTri : Fin 6 → Fin 3 := ![1, 0, 2, 1, 0, 2]

-- The three Eulerian circuits starting with the arc `0 : 0 → 1`.
example : IsEulerianCircuit srcTri tgtTri 0 [0, 1, 5, 3, 2, 4] :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

example : IsEulerianCircuit srcTri tgtTri 0 [0, 2, 3, 1, 5, 4] :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

example : IsEulerianCircuit srcTri tgtTri 0 [0, 2, 4, 5, 3, 1] :=
  ⟨by decide, by decide, rfl, by decide, by decide⟩

/-- The reduced Laplacian at `0` of a matrix on `Fin 3`, as a `2 × 2` determinant. -/
theorem det_laplacian_submatrix_zero_three {R : Type*} [CommRing R]
    (A : Matrix (Fin 3) (Fin 3) R) :
    (A.laplacian.submatrix (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val).det =
      (A 1 0 + A 1 2) * (A 2 0 + A 2 1) - A 1 2 * A 2 1 := by
  refine (det_submatrix_equiv_self (finSuccAboveEquiv (0 : Fin 3))
    (A.laplacian.submatrix (Subtype.val : {v : Fin 3 // v ≠ 0} → Fin 3) Subtype.val)).symm.trans
    ?_
  rw [submatrix_submatrix, det_fin_two]
  simp only [Function.comp_apply, finSuccAboveEquiv_apply, Fin.succAbove_zero, laplacian_apply,
    submatrix_apply, Fin.sum_univ_three]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, ite_true, Fin.reduceEq, ite_false]
  ring

/-- The bidirected triangle has `3` spanning in-arborescences rooted at `0`, by the determinant,
and so `3` Eulerian circuits starting with a fixed arc. -/
example : Nat.card {l : List (Fin 6) // IsEulerianCircuit srcTri tgtTri 0 l} = 3 := by
  have h := natCard_isEulerianCircuit_eq_det_mul srcTri tgtTri ℤ (by decide)
    (fun v => by fin_cases v; exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩]) 0
  have hsrc : srcTri 0 = 0 := rfl
  rw [hsrc, det_laplacian_submatrix_zero_three, arcMatrix_apply, arcMatrix_apply,
    arcMatrix_apply, arcMatrix_apply, Fin.prod_univ_three] at h
  have h10 : (Finset.univ.filter fun e => srcTri e = 1 ∧ tgtTri e = 0).card = 1 := by decide
  have h12 : (Finset.univ.filter fun e => srcTri e = 1 ∧ tgtTri e = 2).card = 1 := by decide
  have h20 : (Finset.univ.filter fun e => srcTri e = 2 ∧ tgtTri e = 0).card = 1 := by decide
  have h21 : (Finset.univ.filter fun e => srcTri e = 2 ∧ tgtTri e = 1).card = 1 := by decide
  have d0 : (Finset.univ.filter fun e => srcTri e = 0).card = 2 := by decide
  have d1 : (Finset.univ.filter fun e => srcTri e = 1).card = 2 := by decide
  have d2 : (Finset.univ.filter fun e => srcTri e = 2).card = 2 := by decide
  rw [h10, h12, h20, h21, d0, d1, d2] at h
  norm_num at h
  exact_mod_cast h

/-! ### Edge cases -/

/-- A loop `0 : 0 → 0` next to the isolated vertex `1`. -/
def srcIsolated : Fin 1 → Fin 2 := fun _ => 0

-- The loop is the only Eulerian circuit.
example : Nat.card {l : List (Fin 1) // IsEulerianCircuit srcIsolated srcIsolated 0 l} = 1 := by
  refine Nat.card_eq_one_iff_exists.mpr ⟨⟨[0], ⟨by decide, by decide, rfl, by decide,
    by decide⟩⟩, fun ⟨l, hl⟩ => Subtype.ext ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t, l = 0 :: t := ⟨_, List.eq_cons_of_mem_head? hl.head⟩
  rcases t with _ | ⟨x, t⟩
  · rfl
  · have := hl.nodup
    rw [Subsingleton.elim x 0] at this
    simp at this

-- There is no spanning arborescence: the isolated vertex has no outgoing arc. So the BEST
-- theorem needs every vertex to have an outgoing arc, even for balanced multidigraphs.
example : Nat.card {f : {v : Fin 2 // v ≠ srcIsolated 0} → Fin 1 //
    IsInArborescence srcIsolated srcIsolated (srcIsolated 0) f} = 0 := by
  have : IsEmpty {f : {v : Fin 2 // v ≠ srcIsolated 0} → Fin 1 //
      IsInArborescence srcIsolated srcIsolated (srcIsolated 0) f} :=
    ⟨fun ⟨_, hf⟩ => by
      have h : (0 : Fin 2) = 1 := hf.src_eq ⟨1, by decide⟩
      exact absurd h (by decide)⟩
  exact Nat.card_of_isEmpty

/-- A single arc `0 → 1`. -/
def srcArc : Fin 1 → Fin 2 := fun _ => 0

/-- A single arc `0 → 1`. -/
def tgtArc : Fin 1 → Fin 2 := fun _ => 1

-- The single arc is unbalanced, so it is not an Eulerian circuit.
example (l : List (Fin 1)) : ¬ IsEulerianCircuit srcArc tgtArc 0 l := fun hl =>
  absurd (hl.card_filter_src_eq 0) (by decide)

section RootIndependence

/-- Doubled `2`-cycle: arcs `0, 1 : 0 → 1` and arcs `2, 3 : 1 → 0`. -/
private def rotSrc (e : Fin 4) : Fin 2 := if e.1 < 2 then 0 else 1

private def rotTgt (e : Fin 4) : Fin 2 := if e.1 < 2 then 1 else 0

-- Cyclic rotation `IsEulerianCircuit.equivRotate` sends `[0, 2, 1, 3]` to `[2, 1, 3, 0]`,
-- proving circuit-count and arborescence-count root independence.
example :
    (∀ h : Cslib.Multidigraph.IsEulerianCircuit rotSrc rotTgt 0 [0, 2, 1, 3],
      (Cslib.Multidigraph.IsEulerianCircuit.equivRotate (src := rotSrc) (tgt := rotTgt) 0 2
        ⟨[0, 2, 1, 3], h⟩).1 = [2, 1, 3, 0]) ∧
    Nat.card {l : List (Fin 4) // Cslib.Multidigraph.IsEulerianCircuit rotSrc rotTgt 0 l} =
      Nat.card {l : List (Fin 4) // Cslib.Multidigraph.IsEulerianCircuit rotSrc rotTgt 2 l} ∧
    Nat.card {f : {v : Fin 2 // v ≠ 0} → Fin 4 //
        Cslib.Multidigraph.IsInArborescence rotSrc rotTgt 0 f} =
      Nat.card {f : {v : Fin 2 // v ≠ 1} → Fin 4 //
        Cslib.Multidigraph.IsInArborescence rotSrc rotTgt 1 f} := by
  have hbal : ∀ v : Fin 2, (Finset.univ.filter fun e => rotSrc e = v).card =
      (Finset.univ.filter fun e => rotTgt e = v).card := by
    intro v; fin_cases v <;> decide
  refine ⟨fun h => ?_, Cslib.Multidigraph.natCard_isEulerianCircuit_eq rotSrc rotTgt 0 2,
    Cslib.Multidigraph.natCard_isInArborescence_eq rotSrc rotTgt hbal 0 1⟩
  rw [Cslib.Multidigraph.IsEulerianCircuit.coe_equivRotate]
  simp only
  decide

-- Root independence without positive out-degree: a loop at `0` plus an isolated vertex `1`.
private def isoSrc (_ : Fin 1) : Fin 2 := 0

example :
    Nat.card {f : {v : Fin 2 // v ≠ 0} → Fin 1 //
        Cslib.Multidigraph.IsInArborescence isoSrc isoSrc 0 f} =
      Nat.card {f : {v : Fin 2 // v ≠ 1} → Fin 1 //
        Cslib.Multidigraph.IsInArborescence isoSrc isoSrc 1 f} :=
  Cslib.Multidigraph.natCard_isInArborescence_eq isoSrc isoSrc (fun _ => rfl) 0 1

-- Counterexample showing balance is needed: `2` arcs `0 → 1` and `1` arc `1 → 0` give `1`
-- arborescence rooted at `0` and `2` rooted at `1`.
private def unbalSrc (e : Fin 3) : Fin 2 := if e.1 < 2 then 0 else 1

private def unbalTgt (e : Fin 3) : Fin 2 := if e.1 < 2 then 1 else 0

example :
    Nat.card {f : {v : Fin 2 // v ≠ 0} → Fin 3 //
        Cslib.Multidigraph.IsInArborescence unbalSrc unbalTgt 0 f} = 1 ∧
      Nat.card {f : {v : Fin 2 // v ≠ 1} → Fin 3 //
        Cslib.Multidigraph.IsInArborescence unbalSrc unbalTgt 1 f} = 2 := by
  have h0 := Cslib.Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence
    unbalSrc unbalTgt ℤ 0
  have : Subsingleton {v : Fin 2 // v ≠ 0} := ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => by
    fin_cases a <;> fin_cases b <;>
      first | exact absurd ha (by decide) | exact absurd hb (by decide) | rfl⟩
  have hdet0 : ((Cslib.Multidigraph.arcMatrix unbalSrc unbalTgt ℤ).laplacian.submatrix
      (Subtype.val : {v : Fin 2 // v ≠ 0} → Fin 2) Subtype.val).det = 1 := by
    rw [Matrix.det_eq_elem_of_subsingleton _ ⟨1, by decide⟩, Matrix.submatrix_apply,
      Matrix.laplacian_apply]
    simp only [Cslib.Multidigraph.arcMatrix_apply]
    decide
  rw [hdet0] at h0
  have h1 := Cslib.Multidigraph.det_laplacian_arcMatrix_submatrix_eq_natCard_isInArborescence
    unbalSrc unbalTgt ℤ 1
  have : Subsingleton {v : Fin 2 // v ≠ 1} := ⟨fun ⟨a, ha⟩ ⟨b, hb⟩ => by
    fin_cases a <;> fin_cases b <;>
      first | exact absurd ha (by decide) | exact absurd hb (by decide) | rfl⟩
  have hdet1 : ((Cslib.Multidigraph.arcMatrix unbalSrc unbalTgt ℤ).laplacian.submatrix
      (Subtype.val : {v : Fin 2 // v ≠ 1} → Fin 2) Subtype.val).det = 2 := by
    rw [Matrix.det_eq_elem_of_subsingleton _ ⟨0, by decide⟩, Matrix.submatrix_apply,
      Matrix.laplacian_apply]
    simp only [Cslib.Multidigraph.arcMatrix_apply]
    decide
  rw [hdet1] at h1
  exact ⟨by exact_mod_cast h0.symm, by exact_mod_cast h1.symm⟩

end RootIndependence

end CslibFrontierTests.BEST
