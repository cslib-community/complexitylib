/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Combinatorics.Multidigraph.BEST

/-!
# Regression tests for the BEST theorem

On two vertices the reduced Laplacian at `0` is the `1 × 1` matrix `(A 1 0)`, so the BEST theorem
counts Eulerian circuits from the number of arcs `1 → 0`:

* the doubled `2`-cycle (two arcs each way) has `2` Eulerian circuits starting with a fixed arc,
  and both are exhibited;
* the `2`-cycle with a loop at `1` has `1`, since loops do not contribute;
* two disjoint loops form a balanced multidigraph without Eulerian circuits.

A single loop at `0` next to an isolated vertex `1` has one Eulerian circuit but no spanning
arborescence, so the hypothesis that every vertex has an outgoing arc is needed. A single arc
`0 → 1` is unbalanced and has no Eulerian circuit.
-/

namespace ComplexityTests.BEST

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

end ComplexityTests.BEST
