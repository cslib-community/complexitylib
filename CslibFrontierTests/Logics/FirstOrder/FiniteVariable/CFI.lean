/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.FirstOrder.FiniteVariable.CFI
import CslibFrontierTests.FOPebbleGames

/-!
# Cai–Fürer–Immerman lower-bound graphs: checked instances and controls

* **Concrete structure of `cfiEven 0` (`K₄` base).** Evaluates gadget-to-edge adjacency, the
  uncoloring `C₃` triangle `{edge s(0, 1) _ 0, edge s(0, 1) _ 1, apex s(0, 1) _}`, and vertex
  supports of sizes `1` and `2`.
* **Parity-sum classification and small-`m` controls.** Verifies explicit double-twist and
  four-twist isomorphisms (`Pi.single 0 1 + Pi.single 2 1` and `fun _ => 1` are isomorphic to
  `cfiEven 0`), triple-twist non-isomorphism against `cfiEven 0`, non-isomorphism at the threshold
  `m = 3` (`K₃`), and the `m = 1` empty-type boundary (`IsEmpty (CFIVertex 1 (Pi.single 0 1))`)
  showing sharpness of `2 ≤ m` in `CFIVertex.nonempty_of_two_le`.
* **Non-regularity.** Every `cfiEven k` fails `IsRegularOfDegree d` for all `d : ℕ` (`apex` has
  degree `2` while `gadget 0 0 _` has at least `3` distinct neighbors), showing that CFI graphs
  separate `1`-WL and `k`-WL outside the class of regular graphs.
* **Concrete separations at `k = 0, 1, 2`.** Checks `0`-WL / `C¹` (`cfiEven 0` vs `cfiOdd 0`),
  `1`-WL / `colorHistogram` / `C²` (`cfiEven 1` vs `cfiOdd 1`), and `2`-WL / `C³` (`cfiEven 2` vs
  `cfiOdd 2`), including explicit satisfaction of the `3`-variable sentence `triangle.toCounting`
  that separated `C₆` from `C₃ ⊕ C₃` in `CslibFrontierTests.WeisfeilerLeman`.
-/

public section

namespace Cslib.Tests.CFI

open FirstOrder Language Structure SimpleGraph
open Cslib.Logic.FO
open Cslib.Tests.FOPebbleGames

/-! ### Concrete vertices, triangles, and supports in `cfiEven 0` -/

/-- Helper showing that `s(0, 1)` is non-diagonal whenever `(1 : Fin m) ≠ 0`. -/
theorem not_isDiag_01 {m : ℕ} [NeZero m] (h : (1 : Fin m) ≠ 0) :
    ¬ (s((0 : Fin m), 1) : Sym2 (Fin m)).IsDiag :=
  Sym2.mk_isDiag_iff.not.2 h.symm

/-- The all-zero gadget vertex over base vertex `0` in `cfiEven k`. -/
def zeroGadget (k : ℕ) : CFIVertex (2 * k + 4) 0 :=
  .gadget 0 0 (by simp only [Pi.zero_apply, Finset.sum_const_zero])

/-- In `cfiEven 0`, `zeroGadget 0` is adjacent to `edge s(0, 1) _ 0` and not to `edge s(0, 1) _ 1`.
-/
theorem zeroGadget_adj_edge_zero_and_not_one :
    let he := not_isDiag_01 (m := 4) (by decide)
    (cfiEven 0).Adj (zeroGadget 0) (.edge s(0, 1) he 0) ∧
      ¬ (cfiEven 0).Adj (zeroGadget 0) (.edge s(0, 1) he 1) := by
  intro he
  refine ⟨?_, ?_⟩
  · rw [zeroGadget, cfiGraph_adj_gadget_edge]
    exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rw [zeroGadget, cfiGraph_adj_gadget_edge]
    rintro ⟨w, -, hb⟩
    rw [Pi.zero_apply] at hb
    exact one_ne_zero hb

/-- The pair `edge s(0, 1) _ 0`, `edge s(0, 1) _ 1` and `apex s(0, 1) _` form a triangle in
`cfiEven 0`. -/
theorem edge_pair_apex_triangle :
    let he := not_isDiag_01 (m := 4) (by decide)
    (cfiEven 0).Adj (.edge s(0, 1) he 0) (.edge s(0, 1) he 1) ∧
      (cfiEven 0).Adj (.edge s(0, 1) he 1) (.apex s(0, 1) he) ∧
      (cfiEven 0).Adj (.apex s(0, 1) he) (.edge s(0, 1) he 0) := by
  intro he
  refine ⟨?_, ?_, ?_⟩
  · rw [cfiGraph_adj_edge_edge]
    exact ⟨rfl, by decide⟩
  · rw [cfiGraph_adj_edge_apex]
  · rw [cfiGraph_adj_apex_edge]

/-- Concrete support cardinalities on `cfiEven 0`: `1` on a gadget vertex and `2` on an edge or
apex vertex. -/
example :
    let he := not_isDiag_01 (m := 4) (by decide)
    (zeroGadget 0).support = {0} ∧
      (CFIVertex.edge s(0, 1) he 0 : CFIVertex 4 0).support.card = 2 ∧
      (CFIVertex.apex s(0, 1) he : CFIVertex 4 0).support.card = 2 := by
  intro he
  refine ⟨?_, ?_, ?_⟩
  · rw [zeroGadget, CFIVertex.support_gadget]
  · rw [CFIVertex.support_edge]
    decide
  · rw [CFIVertex.support_apex]
    decide

/-! ### Positive twist isomorphisms, negative parity controls, and small-`m` boundaries -/

/-- Twisting two distinct base vertices (`0` and `2`) on `K₄` produces a graph isomorphic to
`cfiEven 0`. -/
theorem nonempty_iso_double_twist_cfiEven_zero :
    Nonempty (cfiGraph 4 (Pi.single 0 1 + Pi.single 2 1) ≃g cfiEven 0) :=
  ⟨(cfiFlipIso (u := (0 : Fin 4)) (w := 2) (by decide) (by simp only [zero_add])).symm⟩

/-- Twisting all four base vertices of `K₄` (`∑ v, 1 = 0` in `ZMod 2`) also yields a graph
isomorphic to `cfiEven 0`. -/
theorem nonempty_iso_all_ones_cfiEven_zero :
    Nonempty (cfiGraph 4 (fun _ => 1) ≃g cfiEven 0) := by
  rw [nonempty_iso_cfiGraph_iff_sum_eq (by omega)]
  decide

/-- Twisting three base vertices of `K₄` gives a graph isomorphic to `cfiOdd 0` and non-isomorphic
to `cfiEven 0`. -/
theorem triple_twist_iso_cfiOdd_and_not_cfiEven :
    let f : Fin 4 → ZMod 2 := Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1
    Nonempty (cfiGraph 4 f ≃g cfiOdd 0) ∧ IsEmpty (cfiGraph 4 f ≃g cfiEven 0) := by
  intro f
  refine ⟨?_, ?_⟩
  · rw [nonempty_iso_cfiGraph_iff_sum_eq (by omega)]
    decide
  · exact isEmpty_iso_cfiGraph_of_sum_ne (by omega) (by decide)

/-- Non-isomorphism already holds at the minimum base size `m = 3` (`K₃`). -/
theorem isEmpty_iso_cfiGraph_three_zero_single :
    IsEmpty (cfiGraph 3 0 ≃g cfiGraph 3 (Pi.single 0 1)) :=
  isEmpty_iso_cfiGraph_of_sum_ne le_rfl (by decide)

/-- Sharpness of `2 ≤ m` in `CFIVertex.nonempty_of_two_le`: at `m = 1`, the vertex type
`CFIVertex 1 (Pi.single 0 1)` is empty because the empty sum on `{w : Fin 1 // w ≠ 0}` is `0 ≠ 1`
and `K₁` has no non-diagonal edges. -/
theorem isEmpty_cfiVertex_one_single : IsEmpty (CFIVertex 1 (Pi.single 0 1)) := by
  refine ⟨fun x => ?_⟩
  cases x with
  | gadget v α hα =>
    have hv0 : v = 0 := Subsingleton.elim v 0
    subst hv0
    have hemp : IsEmpty {w : Fin 1 // w ≠ 0} := ⟨fun w => w.property (Subsingleton.elim w.val 0)⟩
    rw [Fintype.sum_empty, Pi.single_eq_same] at hα
    exact zero_ne_one hα
  | edge e he _ =>
    induction e using Sym2.ind with
    | _ v w => exact he (Sym2.mk_isDiag_iff.2 (Subsingleton.elim v w))
  | apex e he =>
    induction e using Sym2.ind with
    | _ v w => exact he (Sym2.mk_isDiag_iff.2 (Subsingleton.elim v w))

/-! ### Non-regularity of `cfiEven k` -/

/-- `cfiEven k` is not `d`-regular for any `d : ℕ`: every apex vertex has degree `2`, whereas
`zeroGadget k` has at least `3` distinct neighbors (`edge s(0, 1) _ 0`, `edge s(0, 2) _ 0`,
`edge s(0, 3) _ 0`). -/
theorem not_isRegularOfDegree_cfiEven (k d : ℕ) : ¬ (cfiEven k).IsRegularOfDegree d := by
  intro hreg
  let u0 : Fin (2 * k + 4) := ⟨0, by omega⟩
  let u1 : Fin (2 * k + 4) := ⟨1, by omega⟩
  let u2 : Fin (2 * k + 4) := ⟨2, by omega⟩
  let u3 : Fin (2 * k + 4) := ⟨3, by omega⟩
  have h10 : u1 ≠ u0 := by simp only [u0, u1, ne_eq, Fin.mk.injEq, one_ne_zero, not_false_eq_true]
  have h20 : u2 ≠ u0 := by simp only [u0, u2, ne_eq, Fin.mk.injEq]; omega
  have h30 : u3 ≠ u0 := by simp only [u0, u3, ne_eq, Fin.mk.injEq]; omega
  have h12 : u1 ≠ u2 := by simp only [u1, u2, ne_eq, Fin.mk.injEq]; omega
  have h13 : u1 ≠ u3 := by simp only [u1, u3, ne_eq, Fin.mk.injEq]; omega
  have h23 : u2 ≠ u3 := by simp only [u2, u3, ne_eq, Fin.mk.injEq]; omega
  have he01 : ¬ (s(u0, u1) : Sym2 (Fin (2 * k + 4))).IsDiag := Sym2.mk_isDiag_iff.not.2 h10.symm
  have he02 : ¬ (s(u0, u2) : Sym2 (Fin (2 * k + 4))).IsDiag := Sym2.mk_isDiag_iff.not.2 h20.symm
  have he03 : ¬ (s(u0, u3) : Sym2 (Fin (2 * k + 4))).IsDiag := Sym2.mk_isDiag_iff.not.2 h30.symm
  let a : CFIVertex (2 * k + 4) 0 := .apex s(u0, u1) he01
  let e₀ : CFIVertex (2 * k + 4) 0 := .edge s(u0, u1) he01 0
  let e₁ : CFIVertex (2 * k + 4) 0 := .edge s(u0, u1) he01 1
  have hapex_sub : (cfiEven k).neighborFinset a ⊆ {e₀, e₁} := by
    intro y hy
    rw [mem_neighborFinset] at hy
    cases y with
    | gadget _ _ _ => exact absurd hy (not_cfiGraph_adj_apex_gadget _ _ _ _ _)
    | apex _ _ => exact absurd hy (not_cfiGraph_adj_apex_apex _ _ _ _)
    | edge e he b =>
      rw [cfiGraph_adj_apex_edge] at hy
      subst hy
      rw [Finset.mem_insert, Finset.mem_singleton]
      fin_cases b
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hapex_le : (cfiEven k).degree a ≤ 2 :=
    (Finset.card_le_card hapex_sub).trans Finset.card_le_two
  let n₁ : CFIVertex (2 * k + 4) 0 := .edge s(u0, u1) he01 0
  let n₂ : CFIVertex (2 * k + 4) 0 := .edge s(u0, u2) he02 0
  let n₃ : CFIVertex (2 * k + 4) 0 := .edge s(u0, u3) he03 0
  have hg_sub : ({n₁, n₂, n₃} : Finset (CFIVertex (2 * k + 4) 0)) ⊆
      (cfiEven k).neighborFinset (zeroGadget k) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rw [mem_neighborFinset, zeroGadget]
    rcases hy with rfl | rfl | rfl
    · exact (cfiGraph_adj_gadget_edge _ _ _ _ _ _).2 ⟨⟨u1, h10⟩, rfl, rfl⟩
    · exact (cfiGraph_adj_gadget_edge _ _ _ _ _ _).2 ⟨⟨u2, h20⟩, rfl, rfl⟩
    · exact (cfiGraph_adj_gadget_edge _ _ _ _ _ _).2 ⟨⟨u3, h30⟩, rfl, rfl⟩
  have hn12 : n₁ ≠ n₂ := fun h => h12 (Sym2.congr_right.1 (by injection h))
  have hn13 : n₁ ≠ n₃ := fun h => h13 (Sym2.congr_right.1 (by injection h))
  have hn23 : n₂ ≠ n₃ := fun h => h23 (Sym2.congr_right.1 (by injection h))
  have hcard3 : ({n₁, n₂, n₃} : Finset (CFIVertex (2 * k + 4) 0)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact hn23
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hn12, hn13⟩
  have hg_ge : 3 ≤ (cfiEven k).degree (zeroGadget k) := by
    rw [← hcard3]
    exact Finset.card_le_card hg_sub
  have hda : (cfiEven k).degree a = d := hreg a
  have hdg : (cfiEven k).degree (zeroGadget k) = d := hreg (zeroGadget k)
  omega

/-! ### Separations at `k = 0`, `k = 1`, and `k = 2` -/

/-- At `k = 0`, `cfiEven 0` and `cfiOdd 0` are non-isomorphic yet agree on `0`-WL and `C¹`. -/
theorem cfi_zero_separates_zero_wl :
    ¬ Nonempty (cfiEven 0 ≃g cfiOdd 0) ∧
      (∀ n, (cfiEven 0).wlHistogram 0 n = (cfiOdd 0).wlHistogram 0 n) ∧
      ∀ φ : FiniteVariable.CountingFormula Language.graph 1,
        φ.freeVars = ∅ →
          ∀ (a : Fin 1 → CFIVertex 4 0) (b : Fin 1 → CFIVertex 4 (Pi.single 0 1)),
            ((letI := (cfiEven 0).structure; φ.Realize a) ↔
              (letI := (cfiOdd 0).structure; φ.Realize b)) :=
  ⟨not_nonempty_iso_cfiEven_cfiOdd 0, wlHistogram_cfiEven_eq_cfiOdd 0,
    fun _ hφ a b => realize_countingFormula_cfiEven_iff_cfiOdd hφ a b⟩

/-- At `k = 1`, `cfiEven 1` and `cfiOdd 1` are non-isomorphic and non-regular, yet agree on both
`1`-WL (`wlHistogram 1`), vertex color refinement (`colorHistogram`), and `C²`. -/
theorem cfi_one_separates_one_wl_and_colorRefinement :
    ¬ Nonempty (cfiEven 1 ≃g cfiOdd 1) ∧
      (∀ d, ¬ (cfiEven 1).IsRegularOfDegree d) ∧
      (∀ n, (cfiEven 1).wlHistogram 1 n = (cfiOdd 1).wlHistogram 1 n) ∧
      (∀ n, (cfiEven 1).colorHistogram (fun _ => ()) n =
        (cfiOdd 1).colorHistogram (fun _ => ()) n) ∧
      ∀ φ : FiniteVariable.CountingFormula Language.graph 2,
        φ.freeVars = ∅ →
          ∀ (a : Fin 2 → CFIVertex 6 0) (b : Fin 2 → CFIVertex 6 (Pi.single 0 1)),
            ((letI := (cfiEven 1).structure; φ.Realize a) ↔
              (letI := (cfiOdd 1).structure; φ.Realize b)) :=
  ⟨not_nonempty_iso_cfiEven_cfiOdd 1, not_isRegularOfDegree_cfiEven 1,
    wlHistogram_cfiEven_eq_cfiOdd 1, colorHistogram_cfiEven_eq_cfiOdd le_rfl,
    fun _ hφ a b => realize_countingFormula_cfiEven_iff_cfiOdd hφ a b⟩

/-- At `k = 2`, `cfiEven 2` and `cfiOdd 2` are non-isomorphic yet agree on `2`-WL and all `C³`
sentences — and both explicitly satisfy the `3`-variable rank-`3` triangle sentence
`triangle.toCounting` (unlike `C₆` vs `C₃ ⊕ C₃`, which `2`-WL and `triangle.toCounting` separate).
-/
theorem cfi_two_separates_two_wl_and_realizes_triangle :
    let he := not_isDiag_01 (m := 8) (by decide)
    let b₀ : CFIVertex 8 (Pi.single 0 1) := .apex s(0, 1) he
    ¬ Nonempty (cfiEven 2 ≃g cfiOdd 2) ∧
      (∀ n, (cfiEven 2).wlHistogram 2 n = (cfiOdd 2).wlHistogram 2 n) ∧
      ∃ φ : FiniteVariable.Formula Language.graph 3,
        φ.freeVars = ∅ ∧ φ.quantifierRank = 3 ∧
          (letI := (cfiEven 2).structure;
            φ.toCounting.Realize fun _ => zeroGadget 2) ∧
          (letI := (cfiOdd 2).structure;
            φ.toCounting.Realize fun _ => b₀) := by
  intro he b₀
  have htri_even : (letI := (cfiEven 2).structure;
      triangle.toCounting.Realize fun _ => zeroGadget 2) := by
    let := (cfiEven 2).structure
    rw [FiniteVariable.Formula.realize_toCounting, realize_triangle_iff]
    exact ⟨.edge s(0, 1) he 0, .edge s(0, 1) he 1, .apex s(0, 1) he,
      (cfiGraph_adj_edge_edge _ _ _ _ _ _).2 ⟨rfl, by decide⟩,
      (cfiGraph_adj_edge_apex _ _ _ _ _).2 rfl,
      (cfiGraph_adj_edge_apex _ _ _ _ _).2 rfl⟩
  have htri_odd : (letI := (cfiOdd 2).structure;
      triangle.toCounting.Realize fun _ => b₀) :=
    (realize_countingFormula_cfiEven_iff_cfiOdd (k := 2) (φ := triangle.toCounting)
      (by rw [FiniteVariable.Formula.freeVars_toCounting, freeVars_triangle])
      (fun _ => zeroGadget 2) (fun _ => b₀)).1 htri_even
  exact ⟨not_nonempty_iso_cfiEven_cfiOdd 2, wlHistogram_cfiEven_eq_cfiOdd 2,
    triangle, freeVars_triangle, quantifierRank_triangle, htri_even, htri_odd⟩

end Cslib.Tests.CFI
