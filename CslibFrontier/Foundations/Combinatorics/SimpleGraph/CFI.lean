/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/CFI.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FinCases

/-!
# Cai–Fürer–Immerman graphs over complete base graphs

For a base vertex count `m` and a twist function `f : Fin m → ZMod 2`, the **Cai–Fürer–Immerman
graph** `SimpleGraph.cfiGraph m f` replaces each vertex `v : Fin m` of the complete graph `K_m` by
the parity gadget of assignments `α : {w : Fin m // w ≠ v} → ZMod 2` summing to `f v`, and replaces
each undirected edge `e = s(v, w)` (`v ≠ w`) by a pair of edge vertices `edge e he 0`, `edge e he 1`
joined to one another and to a dedicated `apex e he` vertex ([CaiFurerImmerman1992], Section 6).

* **Uncoloring via triangles.** Joining each edge pair `{edge e he 0, edge e he 1}` to `apex e he`
  places every edge and apex vertex in a triangle, whereas gadget vertices never have two adjacent
  neighbors and therefore lie in no triangles. For `3 ≤ m`, every `edge` vertex has at least one
  `gadget` neighbor while every neighbor of `apex` lies in a triangle, so any uncolored graph
  isomorphism `cfiGraph m f ≃g cfiGraph m g` preserves the three vertex sorts (`gadget`, `edge`,
  `apex`) and induces a base permutation `π : Fin m ≃ Fin m` (cf. [CaiFurerImmerman1992],
  Section 6).
* **Edge-twist classification.** Twisting `f` at both endpoints of an edge `u ≠ w` (`f + Pi.single u
  1 + Pi.single w 1`) yields an isomorphic graph (`SimpleGraph.cfiFlipIso`), and for `3 ≤ m` two CFI
  graphs `cfiGraph m f` and `cfiGraph m g` are isomorphic if and only if `∑ v, f v = ∑ v, g v`
  (`SimpleGraph.nonempty_iso_cfiGraph_iff_sum_eq`, [CaiFurerImmerman1992], Section 6).
* **Even and odd lower-bound family.** Setting `m = 2 * k + 4` gives the non-isomorphic pair
  `SimpleGraph.cfiEven k` (`f = 0`) and `SimpleGraph.cfiOdd k` (`f = Pi.single 0 1`), together with
  vertex supports of size at most `2` and the local bijection `SimpleGraph.cfiBaseEquiv` used in
  `CslibFrontier.Logics.FirstOrder.FiniteVariable.CFI` to win the infinite `(k + 1)`-pebble
  bijective game. Using `K_{2k + 4}` avoids degree-`3` expanders at the cost of `O(k · 2^{2k})`
  vertices rather than `O(k)`.

## Main definitions

* `SimpleGraph.CFIVertex`: vertices of the CFI graph over `K_m` with twist `f : Fin m → ZMod 2`.
* `SimpleGraph.cfiGraph`: the uncolored simple CFI graph on `CFIVertex m f`.
* `SimpleGraph.cfiEven`, `SimpleGraph.cfiOdd`: the even (`f = 0`) and odd (`f = Pi.single 0 1`) CFI
  graphs over `K_{2k + 4}`.
* `SimpleGraph.CFIVertex.support`: the base-vertex support (`{v}` or `e.toFinset`) of a CFI vertex.
* `SimpleGraph.CFIVertex.castAway`: retyping a CFI vertex across twists that agree off `u`.
* `SimpleGraph.cfiFlipIso`, `SimpleGraph.cfiFlipUpdateIso`, `SimpleGraph.cfiSingleFlipIso`,
  `SimpleGraph.cfiSingleIso`: graph isomorphisms shifting twists along edges of `K_m`.
* `SimpleGraph.cfiBaseEquiv`: the coordinate bijection `CFIVertex m 0 ≃ CFIVertex m (Pi.single u 1)`
  flipping coordinate `w ≠ u` inside the `u`-gadget.

## Main results

* `SimpleGraph.CFIVertex.card_support_le_two`: every CFI vertex has support of size at most `2`.
* `SimpleGraph.isEmpty_iso_cfiGraph_of_sum_ne`, `SimpleGraph.not_nonempty_iso_cfiGraph_of_sum_ne`,
  `SimpleGraph.nonempty_iso_cfiGraph_iff_sum_eq`: `cfiGraph m f` and `cfiGraph m g` (`3 ≤ m`) are
  isomorphic iff `∑ v, f v = ∑ v, g v`.
* `SimpleGraph.isEmpty_iso_cfiEven_cfiOdd`, `SimpleGraph.not_nonempty_iso_cfiEven_cfiOdd`:
  `cfiEven k` and `cfiOdd k` are non-isomorphic for every `k : ℕ`.
* `SimpleGraph.cfiBaseEquiv_eq_castAway`, `SimpleGraph.cfiSingleFlipIso_castAway_of_notMem`,
  `SimpleGraph.cfiSingleFlipIso_castAway_eq_cfiBaseEquiv`,
  `SimpleGraph.cfiSingleFlipIso_castAway_eq_cfiBaseEquiv_of_mem`: compatibility equations between
  `cfiBaseEquiv`, `castAway` and `cfiSingleFlipIso`.

## References

* [J.-Y. Cai, M. Fürer, N. Immerman, *An optimal lower bound on the number of variables for graph
  identification*][CaiFurerImmerman1992], Section 6.
-/

public section

namespace SimpleGraph

/-! ### Vertices and adjacency of CFI graphs -/

/-- Vertices of the uncolored Cai–Fürer–Immerman graph over `K_m` with twist `f : Fin m → ZMod 2`:
* `gadget v α hα`: an assignment `α` on directions `w ≠ v` whose `ZMod 2`-sum equals `f v`;
* `edge e he b`: one of the two vertices on the undirected edge `e` of `K_m`, labeled by `b`;
* `apex e he`: a triangle apex joined to both `edge e he 0` and `edge e he 1` so that uncolored
  graph isomorphisms preserve vertex roles. -/
inductive CFIVertex (m : ℕ) (f : Fin m → ZMod 2) : Type
  /-- A parity-`f v` gadget vertex over base vertex `v : Fin m`. -/
  | gadget (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v)
  /-- One of the two vertices associated with a non-diagonal undirected edge `e` of `K_m`. -/
  | edge (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2)
  /-- The uncoloring triangle apex associated with a non-diagonal undirected edge `e` of `K_m`. -/
  | apex (e : Sym2 (Fin m)) (he : ¬ e.IsDiag)
  deriving DecidableEq

section FintypeAndNonempty

instance {m : ℕ} {f : Fin m → ZMod 2} : Fintype (CFIVertex m f) :=
  Fintype.ofEquiv
    (((v : Fin m) × {α : {w : Fin m // w ≠ v} → ZMod 2 // ∑ w, α w = f v}) ⊕
      (({e : Sym2 (Fin m) // ¬ e.IsDiag} × ZMod 2) ⊕ {e : Sym2 (Fin m) // ¬ e.IsDiag}))
    { toFun
        | .inl ⟨v, ⟨α, hα⟩⟩ => .gadget v α hα
        | .inr (.inl ⟨⟨e, he⟩, b⟩) => .edge e he b
        | .inr (.inr ⟨e, he⟩) => .apex e he
      invFun
        | .gadget v α hα => .inl ⟨v, ⟨α, hα⟩⟩
        | .edge e he b => .inr (.inl ⟨⟨e, he⟩, b⟩)
        | .apex e he => .inr (.inr ⟨e, he⟩)
      left_inv y := by rcases y with ⟨_, ⟨_, _⟩⟩ | ⟨⟨_, _⟩, _⟩ | ⟨_, _⟩ <;> rfl
      right_inv x := by cases x <;> rfl }

instance {n : ℕ} {f : Fin (n + 2) → ZMod 2} : Inhabited (CFIVertex (n + 2) f) :=
  ⟨.apex s(0, 1) (Sym2.mk_isDiag_iff.not.2 Fin.zero_ne_one)⟩

/-- Whenever `2 ≤ m`, `CFIVertex m f` is nonempty. -/
theorem CFIVertex.nonempty_of_two_le {m : ℕ} (hm : 2 ≤ m) (f : Fin m → ZMod 2) :
    Nonempty (CFIVertex m f) :=
  ⟨.apex s(⟨0, by omega⟩, ⟨1, by omega⟩)
    (Sym2.mk_isDiag_iff.not.2 (by simp only [Fin.ext_iff, zero_ne_one, not_false_eq_true]))⟩

end FintypeAndNonempty

private def cfiAdj {m : ℕ} {f : Fin m → ZMod 2} : CFIVertex m f → CFIVertex m f → Prop
  | .gadget v α _, .edge e _ b => ∃ w : {w : Fin m // w ≠ v}, e = s(v, w.val) ∧ b = α w
  | .edge e _ b, .gadget v α _ => ∃ w : {w : Fin m // w ≠ v}, e = s(v, w.val) ∧ b = α w
  | .edge e₁ _ b₁, .edge e₂ _ b₂ => e₁ = e₂ ∧ b₁ ≠ b₂
  | .edge e₁ _ _, .apex e₂ _ => e₁ = e₂
  | .apex e₁ _, .edge e₂ _ _ => e₁ = e₂
  | _, _ => False

private theorem cfiAdj_symm {m : ℕ} {f : Fin m → ZMod 2} {x y : CFIVertex m f}
    (h : cfiAdj x y) : cfiAdj y x := by
  cases x <;> cases y
  all_goals simp only [cfiAdj] at h ⊢
  all_goals first | exact h | exact h.symm | exact ⟨h.1.symm, h.2.symm⟩

private theorem cfiAdj_irrefl {m : ℕ} {f : Fin m → ZMod 2} (x : CFIVertex m f) :
    ¬ cfiAdj x x := by
  cases x <;> simp only [cfiAdj, ne_eq, not_true_eq_false, and_false, not_false_eq_true]

/-- The uncolored Cai–Fürer–Immerman simple graph over `K_m` with twist `f : Fin m → ZMod 2`. -/
def cfiGraph (m : ℕ) (f : Fin m → ZMod 2) : SimpleGraph (CFIVertex m f) where
  Adj := cfiAdj
  symm := ⟨fun _ _ => cfiAdj_symm⟩
  loopless := ⟨cfiAdj_irrefl⟩

section AdjSimp

variable {m : ℕ} {f : Fin m → ZMod 2}

@[simp] theorem cfiGraph_adj_gadget_edge (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2)
    (hα : ∑ w, α w = f v) (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2) :
    (cfiGraph m f).Adj (.gadget v α hα) (.edge e he b) ↔
      ∃ w : {w : Fin m // w ≠ v}, e = s(v, w.val) ∧ b = α w := by
  rw [cfiGraph]
  rfl

@[simp] theorem cfiGraph_adj_edge_gadget (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2)
    (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v) :
    (cfiGraph m f).Adj (.edge e he b) (.gadget v α hα) ↔
      ∃ w : {w : Fin m // w ≠ v}, e = s(v, w.val) ∧ b = α w := by
  rw [cfiGraph]
  rfl

@[simp] theorem cfiGraph_adj_edge_edge (e₁ : Sym2 (Fin m)) (he₁ : ¬ e₁.IsDiag) (b₁ : ZMod 2)
    (e₂ : Sym2 (Fin m)) (he₂ : ¬ e₂.IsDiag) (b₂ : ZMod 2) :
    (cfiGraph m f).Adj (.edge e₁ he₁ b₁) (.edge e₂ he₂ b₂) ↔ e₁ = e₂ ∧ b₁ ≠ b₂ := by
  rw [cfiGraph]
  rfl

@[simp] theorem cfiGraph_adj_edge_apex (e₁ : Sym2 (Fin m)) (he₁ : ¬ e₁.IsDiag) (b : ZMod 2)
    (e₂ : Sym2 (Fin m)) (he₂ : ¬ e₂.IsDiag) :
    (cfiGraph m f).Adj (.edge e₁ he₁ b) (.apex e₂ he₂) ↔ e₁ = e₂ := by
  rw [cfiGraph]
  rfl

@[simp] theorem cfiGraph_adj_apex_edge (e₁ : Sym2 (Fin m)) (he₁ : ¬ e₁.IsDiag)
    (e₂ : Sym2 (Fin m)) (he₂ : ¬ e₂.IsDiag) (b : ZMod 2) :
    (cfiGraph m f).Adj (.apex e₁ he₁) (.edge e₂ he₂ b) ↔ e₁ = e₂ := by
  rw [cfiGraph]
  rfl

@[simp] theorem not_cfiGraph_adj_gadget_gadget (v₁ : Fin m) (α₁ : {w : Fin m // w ≠ v₁} → ZMod 2)
    (hα₁ : ∑ w, α₁ w = f v₁) (v₂ : Fin m) (α₂ : {w : Fin m // w ≠ v₂} → ZMod 2)
    (hα₂ : ∑ w, α₂ w = f v₂) :
    ¬ (cfiGraph m f).Adj (.gadget v₁ α₁ hα₁) (.gadget v₂ α₂ hα₂) := by
  rw [cfiGraph]
  exact id

@[simp] theorem not_cfiGraph_adj_gadget_apex (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2)
    (hα : ∑ w, α w = f v) (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
    ¬ (cfiGraph m f).Adj (.gadget v α hα) (.apex e he) := by
  rw [cfiGraph]
  exact id

@[simp] theorem not_cfiGraph_adj_apex_gadget (e : Sym2 (Fin m)) (he : ¬ e.IsDiag)
    (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v) :
    ¬ (cfiGraph m f).Adj (.apex e he) (.gadget v α hα) := by
  rw [cfiGraph]
  exact id

@[simp] theorem not_cfiGraph_adj_apex_apex (e₁ : Sym2 (Fin m)) (he₁ : ¬ e₁.IsDiag)
    (e₂ : Sym2 (Fin m)) (he₂ : ¬ e₂.IsDiag) :
    ¬ (cfiGraph m f).Adj (.apex e₁ he₁) (.apex e₂ he₂) := by
  rw [cfiGraph]
  exact id

end AdjSimp

instance {m : ℕ} {f : Fin m → ZMod 2} : DecidableRel (cfiGraph m f).Adj
  | .gadget v α hα, .edge e he b => decidable_of_iff' _ (cfiGraph_adj_gadget_edge v α hα e he b)
  | .edge e he b, .gadget v α hα => decidable_of_iff' _ (cfiGraph_adj_edge_gadget e he b v α hα)
  | .edge e₁ he₁ b₁, .edge e₂ he₂ b₂ =>
    decidable_of_iff' _ (cfiGraph_adj_edge_edge e₁ he₁ b₁ e₂ he₂ b₂)
  | .edge e₁ he₁ b, .apex e₂ he₂ => decidable_of_iff' _ (cfiGraph_adj_edge_apex e₁ he₁ b e₂ he₂)
  | .apex e₁ he₁, .edge e₂ he₂ b => decidable_of_iff' _ (cfiGraph_adj_apex_edge e₁ he₁ e₂ he₂ b)
  | .gadget v₁ α₁ hα₁, .gadget v₂ α₂ hα₂ =>
    isFalse (not_cfiGraph_adj_gadget_gadget v₁ α₁ hα₁ v₂ α₂ hα₂)
  | .gadget v α hα, .apex e he => isFalse (not_cfiGraph_adj_gadget_apex v α hα e he)
  | .apex e he, .gadget v α hα => isFalse (not_cfiGraph_adj_apex_gadget e he v α hα)
  | .apex e₁ he₁, .apex e₂ he₂ => isFalse (not_cfiGraph_adj_apex_apex e₁ he₁ e₂ he₂)

/-- The even Cai–Fürer–Immerman graph at dimension `k`: `cfiGraph (2 * k + 4) 0`. -/
abbrev cfiEven (k : ℕ) : SimpleGraph (CFIVertex (2 * k + 4) 0) :=
  cfiGraph (2 * k + 4) 0

/-- The odd Cai–Fürer–Immerman graph at dimension `k`: `cfiGraph (2 * k + 4) (Pi.single 0 1)`. -/
abbrev cfiOdd (k : ℕ) : SimpleGraph (CFIVertex (2 * k + 4) (Pi.single 0 1)) :=
  cfiGraph (2 * k + 4) (Pi.single 0 1)

/-! ### Base-vertex support and twist retyping away from a vertex -/

section SupportAndCast

variable {m : ℕ} {f g : Fin m → ZMod 2}

/-- The set of base vertices in `Fin m` on which a CFI vertex lives (`{v}` on `gadget v`, and the
two endpoints `e.toFinset` on `edge e` and `apex e`). -/
def CFIVertex.support : CFIVertex m f → Finset (Fin m)
  | .gadget v _ _ => {v}
  | .edge e _ _ => e.toFinset
  | .apex e _ => e.toFinset

@[simp] theorem CFIVertex.support_gadget (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2)
    (hα : ∑ w, α w = f v) : (CFIVertex.gadget v α hα).support = {v} := by
  rw [CFIVertex.support]

@[simp] theorem CFIVertex.support_edge (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2) :
    (CFIVertex.edge e he b : CFIVertex m f).support = e.toFinset := by
  rw [CFIVertex.support]

@[simp] theorem CFIVertex.support_apex (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
    (CFIVertex.apex e he : CFIVertex m f).support = e.toFinset := by
  rw [CFIVertex.support]

/-- Every CFI vertex has base-vertex support of size at most `2`. -/
theorem CFIVertex.card_support_le_two (x : CFIVertex m f) : x.support.card ≤ 2 := by
  cases x with
  | gadget v _ _ => simp only [support_gadget, Finset.card_singleton, Nat.one_le_ofNat]
  | edge e he _ =>
    rw [support_edge]
    exact (Sym2.card_toFinset_of_not_isDiag e he).le
  | apex e he =>
    rw [support_apex]
    exact (Sym2.card_toFinset_of_not_isDiag e he).le

/-- If two distinct base vertices `u ≠ w` both lie in `x.support`, then no third vertex `w'`
distinct from `u` and `w` lies in `x.support`. -/
theorem CFIVertex.notMem_support_of_mem_mem_ne {u w w' : Fin m} {x : CFIVertex m f}
    (hu : u ∈ x.support) (hw : w ∈ x.support) (huw : u ≠ w) (huw' : w' ≠ u) (hww' : w' ≠ w) :
    w' ∉ x.support := by
  intro hw'
  have hsub : ({u, w, w'} : Finset (Fin m)) ⊆ x.support := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have hcard := Finset.card_le_card hsub
  have h3 : ({u, w, w'} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      exact hww'.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨huw, huw'.symm⟩
  have hle := x.card_support_le_two
  omega

/-- Retype a CFI vertex from twist `f` to twist `g` when `f` and `g` agree outside `u` and
`u ∉ x.support`. -/
def CFIVertex.castAway (u : Fin m) (hfg : ∀ v ≠ u, f v = g v) :
    (x : CFIVertex m f) → u ∉ x.support → CFIVertex m g
  | .gadget v α hα, hu =>
    .gadget v α (hα.trans (hfg v fun hvu => hu (by simp only [support_gadget,
      Finset.mem_singleton, hvu.symm])))
  | .edge e he b, _ => .edge e he b
  | .apex e he, _ => .apex e he

/-- `CFIVertex.castAway` is injective on vertices avoiding `u`. -/
theorem CFIVertex.castAway_inj {u : Fin m} {hfg : ∀ v ≠ u, f v = g v}
    {x y : CFIVertex m f} (hx : u ∉ x.support) (hy : u ∉ y.support) :
    x.castAway u hfg hx = y.castAway u hfg hy ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by subst h; rfl⟩
  cases x <;> cases y <;> simp only [castAway, gadget.injEq, edge.injEq, apex.injEq, reduceCtorEq]
    at h ⊢
  all_goals exact h

/-- `CFIVertex.castAway` preserves and reflects adjacency in `cfiGraph`. -/
theorem cfiGraph_adj_castAway_iff {u : Fin m} {hfg : ∀ v ≠ u, f v = g v}
    {x y : CFIVertex m f} (hx : u ∉ x.support) (hy : u ∉ y.support) :
    (cfiGraph m g).Adj (x.castAway u hfg hx) (y.castAway u hfg hy) ↔ (cfiGraph m f).Adj x y := by
  cases x <;> cases y <;> rw [CFIVertex.castAway, CFIVertex.castAway, cfiGraph, cfiGraph] <;> rfl

end SupportAndCast

/-! ### Edge-twist isomorphisms and Duplicator's local bijection -/

section EdgeTwist

open scoped CharTwo

variable {m : ℕ}

private theorem sum_add_single_one {v : Fin m} (α : {z : Fin m // z ≠ v} → ZMod 2)
    (w : {z : Fin m // z ≠ v}) :
    (∑ z, (α + Pi.single w 1 : {z : Fin m // z ≠ v} → ZMod 2) z) = (∑ z, α z) + 1 := by
  simp only [Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single']

private theorem pi_add_cancel_right {ι : Type*} (α β : ι → ZMod 2) : α + β + β = α :=
  funext fun i => CharTwo.add_cancel_right (α i) (β i)

private theorem zmod_two_add_add_cancel (x a b : ZMod 2) : x + a + b + a + b = x := by
  revert x a b
  decide

private def cfiFlipMap {f g : Fin m → ZMod 2} {u w : Fin m} (huw : u ≠ w)
    (hfg : g = f + Pi.single u 1 + Pi.single w 1) : CFIVertex m f → CFIVertex m g
  | .gadget v α hα =>
    if hvu : v = u then
      .gadget v (α + Pi.single ⟨w, hvu ▸ huw.symm⟩ 1) (by
        rw [sum_add_single_one, hα, hfg, Pi.add_apply, Pi.add_apply, hvu,
          Pi.single_eq_same, Pi.single_eq_of_ne huw, add_zero])
    else if hvw : v = w then
      .gadget v (α + Pi.single ⟨u, hvw ▸ huw⟩ 1) (by
        rw [sum_add_single_one, hα, hfg, Pi.add_apply, Pi.add_apply, hvw,
          Pi.single_eq_of_ne huw.symm, Pi.single_eq_same, add_zero])
    else
      .gadget v α (by
        rw [hα, hfg, Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hvu,
          Pi.single_eq_of_ne hvw, add_zero, add_zero])
  | .edge e he b =>
    if e = s(u, w) then .edge e he (b + 1) else .edge e he b
  | .apex e he => .apex e he

private theorem cfiFlipMap_comp {f g : Fin m → ZMod 2} {u w : Fin m} (huw : u ≠ w)
    (hfg : g = f + Pi.single u 1 + Pi.single w 1)
    (hgf : f = g + Pi.single u 1 + Pi.single w 1) (x : CFIVertex m f) :
    cfiFlipMap huw hgf (cfiFlipMap huw hfg x) = x := by
  cases x with
  | gadget v α hα =>
    by_cases hvu : v = u
    · rw [cfiFlipMap, dite_eq_left hvu, cfiFlipMap, dite_eq_left hvu]
      simp only [pi_add_cancel_right]
    · by_cases hvw : v = w
      · rw [cfiFlipMap, dite_eq_right hvu, dite_eq_left hvw, cfiFlipMap, dite_eq_right hvu,
          dite_eq_left hvw]
        simp only [pi_add_cancel_right]
      · rw [cfiFlipMap, dite_eq_right hvu, dite_eq_right hvw, cfiFlipMap, dite_eq_right hvu,
          dite_eq_right hvw]
  | edge e he b =>
    by_cases heq : e = s(u, w)
    · rw [cfiFlipMap, ite_eq_left heq, cfiFlipMap, ite_eq_left heq]
      simp only [CharTwo.add_cancel_right]
    · rw [cfiFlipMap, ite_eq_right heq, cfiFlipMap, ite_eq_right heq]
  | apex e he => rfl

private theorem cfiFlipMap_adj_gadget_edge {f g : Fin m → ZMod 2} {u w : Fin m} (huw : u ≠ w)
    (hfg : g = f + Pi.single u 1 + Pi.single w 1) (v : Fin m)
    (α : {z : Fin m // z ≠ v} → ZMod 2) (hα : ∑ z, α z = f v)
    (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2)
    (hadj : (cfiGraph m f).Adj (.gadget v α hα) (.edge e he b)) :
    (cfiGraph m g).Adj (cfiFlipMap huw hfg (.gadget v α hα))
      (cfiFlipMap huw hfg (.edge e he b)) := by
  rw [cfiGraph_adj_gadget_edge] at hadj
  obtain ⟨z, rfl, rfl⟩ := hadj
  by_cases hvu : v = u
  · have hwv : w ≠ v := hvu ▸ huw.symm
    have hedge : (s(v, z.val) = s(u, w)) ↔ z = ⟨w, hwv⟩ := by
      rw [← hvu, Sym2.congr_right, Subtype.ext_iff]
    by_cases hz : z = ⟨w, hwv⟩
    · have heq : s(v, z.val) = s(u, w) := hedge.2 hz
      rw [cfiFlipMap, dite_eq_left hvu, cfiFlipMap, ite_eq_left heq, cfiGraph_adj_gadget_edge]
      exact ⟨z, rfl, by rw [Pi.add_apply, hz, Pi.single_eq_same]⟩
    · have hne : s(v, z.val) ≠ s(u, w) := mt hedge.1 hz
      rw [cfiFlipMap, dite_eq_left hvu, cfiFlipMap, ite_eq_right hne, cfiGraph_adj_gadget_edge]
      exact ⟨z, rfl, by rw [Pi.add_apply, Pi.single_eq_of_ne hz, add_zero]⟩
  · by_cases hvw : v = w
    · have huv : u ≠ v := hvw ▸ huw
      have hedge : (s(v, z.val) = s(u, w)) ↔ z = ⟨u, huv⟩ := by
        rw [Sym2.eq_swap (a := u), ← hvw, Sym2.congr_right, Subtype.ext_iff]
      by_cases hz : z = ⟨u, huv⟩
      · have heq : s(v, z.val) = s(u, w) := hedge.2 hz
        rw [cfiFlipMap, dite_eq_right hvu, dite_eq_left hvw, cfiFlipMap, ite_eq_left heq,
          cfiGraph_adj_gadget_edge]
        exact ⟨z, rfl, by rw [Pi.add_apply, hz, Pi.single_eq_same]⟩
      · have hne : s(v, z.val) ≠ s(u, w) := mt hedge.1 hz
        rw [cfiFlipMap, dite_eq_right hvu, dite_eq_left hvw, cfiFlipMap, ite_eq_right hne,
          cfiGraph_adj_gadget_edge]
        exact ⟨z, rfl, by rw [Pi.add_apply, Pi.single_eq_of_ne hz, add_zero]⟩
    · have hne : s(v, z.val) ≠ s(u, w) := by
        intro heq
        have hvmem : v ∈ s(u, w) := heq ▸ Sym2.mem_mk_left v z.val
        rw [Sym2.mem_iff] at hvmem
        exact hvmem.elim hvu hvw
      rw [cfiFlipMap, dite_eq_right hvu, dite_eq_right hvw, cfiFlipMap, ite_eq_right hne,
        cfiGraph_adj_gadget_edge]
      exact ⟨z, rfl, rfl⟩

private theorem cfiFlipMap_adj {f g : Fin m → ZMod 2} {u w : Fin m} (huw : u ≠ w)
    (hfg : g = f + Pi.single u 1 + Pi.single w 1) {x y : CFIVertex m f}
    (hadj : (cfiGraph m f).Adj x y) :
    (cfiGraph m g).Adj (cfiFlipMap huw hfg x) (cfiFlipMap huw hfg y) := by
  cases x with
  | gadget v α hα =>
    cases y with
    | gadget _ _ _ => exact absurd hadj (not_cfiGraph_adj_gadget_gadget _ _ _ _ _ _)
    | edge e he b => exact cfiFlipMap_adj_gadget_edge huw hfg v α hα e he b hadj
    | apex _ _ => exact absurd hadj (not_cfiGraph_adj_gadget_apex _ _ _ _ _)
  | edge e₁ he₁ b₁ =>
    cases y with
    | gadget v α hα =>
      exact (cfiFlipMap_adj_gadget_edge huw hfg v α hα e₁ he₁ b₁ hadj.symm).symm
    | edge e₂ he₂ b₂ =>
      rw [cfiGraph_adj_edge_edge] at hadj
      obtain ⟨rfl, hne⟩ := hadj
      by_cases heq : e₁ = s(u, w)
      · rw [cfiFlipMap, ite_eq_left heq, cfiFlipMap, ite_eq_left heq, cfiGraph_adj_edge_edge]
        exact ⟨rfl, fun h => hne (add_right_cancel h)⟩
      · rw [cfiFlipMap, ite_eq_right heq, cfiFlipMap, ite_eq_right heq, cfiGraph_adj_edge_edge]
        exact ⟨rfl, hne⟩
    | apex e₂ he₂ =>
      rw [cfiGraph_adj_edge_apex] at hadj
      obtain rfl : e₁ = e₂ := hadj
      by_cases heq : e₁ = s(u, w)
      · rw [cfiFlipMap, ite_eq_left heq, cfiFlipMap, cfiGraph_adj_edge_apex]
      · rw [cfiFlipMap, ite_eq_right heq, cfiFlipMap, cfiGraph_adj_edge_apex]
  | apex e₁ he₁ =>
    cases y with
    | gadget _ _ _ => exact absurd hadj (not_cfiGraph_adj_apex_gadget _ _ _ _ _)
    | edge e₂ he₂ b₂ =>
      rw [cfiGraph_adj_apex_edge] at hadj
      obtain rfl : e₁ = e₂ := hadj
      by_cases heq : e₁ = s(u, w)
      · rw [cfiFlipMap, cfiFlipMap, ite_eq_left heq, cfiGraph_adj_apex_edge]
      · rw [cfiFlipMap, cfiFlipMap, ite_eq_right heq, cfiGraph_adj_apex_edge]
    | apex _ _ => exact absurd hadj (not_cfiGraph_adj_apex_apex _ _ _ _)

/-- **Edge-twist isomorphism** ([CaiFurerImmerman1992], Section 6): twisting `f` by `1` at both
endpoints of an edge `u ≠ w` of `K_m` gives an isomorphic CFI graph. -/
def cfiFlipIso {f g : Fin m → ZMod 2} {u w : Fin m} (huw : u ≠ w)
    (hfg : g = f + Pi.single u 1 + Pi.single w 1) :
    cfiGraph m f ≃g cfiGraph m g :=
  have hgf : f = g + Pi.single u 1 + Pi.single w 1 := by
    ext v
    simp only [hfg, Pi.add_apply]
    exact (zmod_two_add_add_cancel _ _ _).symm
  { toFun := cfiFlipMap huw hfg
    invFun := cfiFlipMap huw hgf
    left_inv := cfiFlipMap_comp huw hfg hgf
    right_inv := cfiFlipMap_comp huw hgf hfg
    map_rel_iff' := fun {x y} => ⟨fun h => by
      change (cfiGraph m g).Adj (cfiFlipMap huw hfg x) (cfiFlipMap huw hfg y) at h
      have h' := cfiFlipMap_adj huw hgf h
      rwa [cfiFlipMap_comp huw hfg hgf, cfiFlipMap_comp huw hfg hgf] at h',
      cfiFlipMap_adj huw hfg⟩ }

/-- `Function.update` form of `SimpleGraph.cfiFlipIso`. -/
def cfiFlipUpdateIso {u w : Fin m} (huw : u ≠ w) (f : Fin m → ZMod 2) :
    cfiGraph m f ≃g cfiGraph m (Function.update (Function.update f u (f u + 1)) w (f w + 1)) :=
  cfiFlipIso huw (by
    ext v
    by_cases hvw : v = w
    · subst hvw
      simp only [Function.update_self, Pi.add_apply, Pi.single_eq_of_ne huw.symm,
        Pi.single_eq_same, add_zero]
    · by_cases hvu : v = u
      · subst hvu
        simp only [Function.update_of_ne hvw, Function.update_self, Pi.add_apply,
          Pi.single_eq_same, Pi.single_eq_of_ne huw, add_zero]
      · simp only [Function.update_of_ne hvw, Function.update_of_ne hvu, Pi.add_apply,
          Pi.single_eq_of_ne hvu, Pi.single_eq_of_ne hvw, add_zero])

/-- Shifting a single-vertex twist from `w` to a distinct vertex `u` (`u ≠ w`) via the edge-twist
isomorphism along `s(u, w)`. -/
def cfiSingleFlipIso {u w : Fin m} (huw : u ≠ w) :
    cfiGraph m (Pi.single w 1) ≃g cfiGraph m (Pi.single u 1) :=
  cfiFlipIso huw (by
    ext v
    simp only [Pi.add_apply]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add])

/-- Shifting a single-vertex twist between arbitrary vertices `u, w : Fin m`. -/
def cfiSingleIso (u w : Fin m) :
    cfiGraph m (Pi.single w 1) ≃g cfiGraph m (Pi.single u 1) :=
  if huw : u = w then huw ▸ Iso.refl else cfiSingleFlipIso huw

private def cfiBaseMap {f g : Fin m → ZMod 2} (u w : Fin m) (hwu : w ≠ u)
    (hu_eq : g u = f u + 1) (haway : ∀ v ≠ u, g v = f v) :
    CFIVertex m f → CFIVertex m g
  | .gadget v α hα =>
    if hvu : v = u then
      .gadget v (α + Pi.single ⟨w, hvu ▸ hwu⟩ 1) (by
        rw [sum_add_single_one, hα, hvu, hu_eq])
    else
      .gadget v α (hα.trans (haway v hvu).symm)
  | .edge e he b => .edge e he b
  | .apex e he => .apex e he

/-- Duplicator's local coordinate bijection `CFIVertex m 0 ≃ CFIVertex m (Pi.single u 1)`, which
flips coordinate `w` (`w ≠ u`) on `gadget u` and acts as the identity everywhere else. -/
def cfiBaseEquiv (u w : Fin m) (hwu : w ≠ u) :
    CFIVertex m 0 ≃ CFIVertex m (Pi.single u 1) :=
  have hu1 : (Pi.single u 1 : Fin m → ZMod 2) u = (0 : Fin m → ZMod 2) u + 1 := by
    simp only [Pi.single_eq_same, Pi.zero_apply, zero_add]
  have hu2 : (0 : Fin m → ZMod 2) u = (Pi.single u 1 : Fin m → ZMod 2) u + 1 := by
    simp only [Pi.zero_apply, Pi.single_eq_same, CharTwo.add_self_eq_zero]
  have haway1 : ∀ v ≠ u, (Pi.single u 1 : Fin m → ZMod 2) v = (0 : Fin m → ZMod 2) v :=
    fun v hv => by simp only [Pi.single_eq_of_ne hv, Pi.zero_apply]
  have haway2 : ∀ v ≠ u, (0 : Fin m → ZMod 2) v = (Pi.single u 1 : Fin m → ZMod 2) v :=
    fun v hv => (haway1 v hv).symm
  { toFun := cfiBaseMap u w hwu hu1 haway1
    invFun := cfiBaseMap u w hwu hu2 haway2
    left_inv := fun x => by
      cases x with
      | gadget v α hα =>
        by_cases hvu : v = u
        · rw [cfiBaseMap, dite_eq_left hvu, cfiBaseMap, dite_eq_left hvu]
          simp only [pi_add_cancel_right]
        · rw [cfiBaseMap, dite_eq_right hvu, cfiBaseMap, dite_eq_right hvu]
      | edge _ _ _ => rfl
      | apex _ _ => rfl
    right_inv := fun y => by
      cases y with
      | gadget v α hα =>
        by_cases hvu : v = u
        · rw [cfiBaseMap, dite_eq_left hvu, cfiBaseMap, dite_eq_left hvu]
          simp only [pi_add_cancel_right]
        · rw [cfiBaseMap, dite_eq_right hvu, cfiBaseMap, dite_eq_right hvu]
      | edge _ _ _ => rfl
      | apex _ _ => rfl }

/-- Away from `u`, `cfiBaseEquiv u w hwu` agrees with `CFIVertex.castAway u`. -/
theorem cfiBaseEquiv_eq_castAway {u w : Fin m} (hwu : w ≠ u)
    (hfg : ∀ v ≠ u, (0 : Fin m → ZMod 2) v = (Pi.single u 1 : Fin m → ZMod 2) v)
    (x : CFIVertex m 0) (hu : u ∉ x.support) :
    cfiBaseEquiv u w hwu x = x.castAway u hfg hu := by
  cases x with
  | gadget v α hα =>
    have hvu : v ≠ u := fun h => hu (by simp only [CFIVertex.support_gadget,
      Finset.mem_singleton, h.symm])
    unfold cfiBaseEquiv
    dsimp only [Equiv.coe_fn_mk]
    rw [cfiBaseMap, dite_eq_right hvu, CFIVertex.castAway]
  | edge _ _ _ => rfl
  | apex _ _ => rfl

/-- On vertices whose support avoids both `u` and `w`, `cfiSingleFlipIso huw` commutes with
`CFIVertex.castAway`. -/
theorem cfiSingleFlipIso_castAway_of_notMem {u w : Fin m} (huw : u ≠ w)
    (hfw : ∀ v ≠ w, (0 : Fin m → ZMod 2) v = (Pi.single w 1 : Fin m → ZMod 2) v)
    (hfu : ∀ v ≠ u, (0 : Fin m → ZMod 2) v = (Pi.single u 1 : Fin m → ZMod 2) v)
    (x : CFIVertex m 0) (hu : u ∉ x.support) (hw : w ∉ x.support) :
    cfiSingleFlipIso huw (x.castAway w hfw hw) = x.castAway u hfu hu := by
  cases x with
  | gadget v α hα =>
    have hvu : v ≠ u := fun h => hu (by simp only [CFIVertex.support_gadget,
      Finset.mem_singleton, h.symm])
    have hvw : v ≠ w := fun h => hw (by simp only [CFIVertex.support_gadget,
      Finset.mem_singleton, h.symm])
    unfold cfiSingleFlipIso cfiFlipIso
    dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    rw [CFIVertex.castAway, cfiFlipMap, dite_eq_right hvu, dite_eq_right hvw, CFIVertex.castAway]
  | edge e he b =>
    have hne : e ≠ s(u, w) := fun heq => hu (by
      rw [CFIVertex.support_edge, heq, Sym2.mem_toFinset]
      exact Sym2.mem_mk_left u w)
    unfold cfiSingleFlipIso cfiFlipIso
    dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    rw [CFIVertex.castAway, cfiFlipMap, ite_eq_right hne, CFIVertex.castAway]
  | apex _ _ => rfl

/-- On any vertex `x` with `w ∉ x.support`, `cfiSingleFlipIso huw` carries `x.castAway w` to
`cfiBaseEquiv u w huw.symm x`. -/
theorem cfiSingleFlipIso_castAway_eq_cfiBaseEquiv {u w : Fin m} (huw : u ≠ w)
    (hfw : ∀ v ≠ w, (0 : Fin m → ZMod 2) v = (Pi.single w 1 : Fin m → ZMod 2) v)
    (x : CFIVertex m 0) (hw : w ∉ x.support) :
    cfiSingleFlipIso huw (x.castAway w hfw hw) = cfiBaseEquiv u w huw.symm x := by
  cases x with
  | gadget v α hα =>
    unfold cfiSingleFlipIso cfiFlipIso cfiBaseEquiv
    dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    by_cases hvu : v = u
    · rw [CFIVertex.castAway, cfiFlipMap, dite_eq_left hvu, cfiBaseMap, dite_eq_left hvu]
    · have hvw : v ≠ w := fun h => hw (by simp only [CFIVertex.support_gadget,
        Finset.mem_singleton, h.symm])
      rw [CFIVertex.castAway, cfiFlipMap, dite_eq_right hvu, dite_eq_right hvw, cfiBaseMap,
        dite_eq_right hvu]
  | edge e he b =>
    have hne : e ≠ s(u, w) := fun heq => hw (by
      rw [CFIVertex.support_edge, heq, Sym2.mem_toFinset]
      exact Sym2.mem_mk_right u w)
    unfold cfiSingleFlipIso cfiFlipIso cfiBaseEquiv
    dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    rw [CFIVertex.castAway, cfiFlipMap, ite_eq_right hne, cfiBaseMap]
  | apex _ _ => rfl

/-- When both `u` and `w` (`u ≠ w`) lie in `x.support` and `w'` is distinct from `u` and `w`,
`cfiSingleFlipIso huw'` carries `x.castAway w'` to `cfiBaseEquiv u w huw.symm x`. -/
theorem cfiSingleFlipIso_castAway_eq_cfiBaseEquiv_of_mem {u w w' : Fin m} (huw : u ≠ w)
    (huw' : u ≠ w') (hww' : w ≠ w')
    (hfw' : ∀ v ≠ w', (0 : Fin m → ZMod 2) v = (Pi.single w' 1 : Fin m → ZMod 2) v)
    (x : CFIVertex m 0) (hu : u ∈ x.support) (hw : w ∈ x.support) (hw' : w' ∉ x.support) :
    cfiSingleFlipIso huw' (x.castAway w' hfw' hw') = cfiBaseEquiv u w huw.symm x := by
  cases x with
  | gadget v α hα =>
    rw [CFIVertex.support_gadget, Finset.mem_singleton] at hu hw
    exact absurd (hu.trans hw.symm) huw
  | edge e he b =>
    have hne : e ≠ s(u, w') := fun heq => by
      rw [CFIVertex.support_edge, heq, Sym2.mem_toFinset, Sym2.mem_iff] at hw
      exact hw.elim huw.symm hww'
    unfold cfiSingleFlipIso cfiFlipIso cfiBaseEquiv
    dsimp only [RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    rw [CFIVertex.castAway, cfiFlipMap, ite_eq_right hne, cfiBaseMap]
  | apex _ _ => rfl

end EdgeTwist

/-! ### Exact isomorphism classification by parity sum -/

section NonIsomorphism

open scoped CharTwo

variable {m : ℕ}

private def InTriangle {V : Type*} (G : SimpleGraph V) (x : V) : Prop :=
  ∃ y z, G.Adj x y ∧ G.Adj y z ∧ G.Adj x z

private def IsApexLike {V : Type*} (G : SimpleGraph V) (x : V) : Prop :=
  InTriangle G x ∧ ∀ y, G.Adj x y → InTriangle G y

private def NearApex {V : Type*} (G : SimpleGraph V) (x a : V) : Prop :=
  ∃ y, G.Adj x y ∧ G.Adj y a

private theorem Iso.inTriangle {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {x : V} : InTriangle G x → InTriangle H (φ x) := fun ⟨y, z, hxy, hyz, hxz⟩ =>
  ⟨φ y, φ z, φ.map_adj_iff.2 hxy, φ.map_adj_iff.2 hyz, φ.map_adj_iff.2 hxz⟩

private theorem Iso.inTriangle_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {x : V} : InTriangle H (φ x) ↔ InTriangle G x :=
  ⟨fun h => by simpa only [RelIso.symm_apply_apply] using φ.symm.inTriangle h, φ.inTriangle⟩

private theorem Iso.isApexLike {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {x : V} : IsApexLike G x → IsApexLike H (φ x) := fun ⟨ht, hall⟩ =>
  ⟨φ.inTriangle ht, fun y hy => by
    have hy' : G.Adj x (φ.symm y) := by
      simpa only [RelIso.symm_apply_apply] using φ.symm.map_adj_iff.2 hy
    simpa only [RelIso.apply_symm_apply] using φ.inTriangle (hall (φ.symm y) hy')⟩

private theorem Iso.isApexLike_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {x : V} : IsApexLike H (φ x) ↔ IsApexLike G x :=
  ⟨fun h => by simpa only [RelIso.symm_apply_apply] using φ.symm.isApexLike h, φ.isApexLike⟩

private theorem Iso.nearApex {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {x a : V} : NearApex G x a → NearApex H (φ x) (φ a) := fun ⟨y, hxy, hya⟩ =>
  ⟨φ y, φ.map_adj_iff.2 hxy, φ.map_adj_iff.2 hya⟩

private theorem Iso.nearApex_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (φ : G ≃g H) {x a : V} : NearApex H (φ x) (φ a) ↔ NearApex G x a :=
  ⟨fun h => by simpa only [RelIso.symm_apply_apply] using φ.symm.nearApex h, φ.nearApex⟩

private theorem not_inTriangle_gadget {f : Fin m → ZMod 2} (v : Fin m)
    (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v) :
    ¬ InTriangle (cfiGraph m f) (.gadget v α hα) := by
  rintro ⟨y, z, hxy, hyz, hxz⟩
  cases y with
  | gadget _ _ _ => exact not_cfiGraph_adj_gadget_gadget _ _ _ _ _ _ hxy
  | apex _ _ => exact not_cfiGraph_adj_gadget_apex _ _ _ _ _ hxy
  | edge e₁ he₁ b₁ =>
    cases z with
    | gadget _ _ _ => exact not_cfiGraph_adj_gadget_gadget _ _ _ _ _ _ hxz
    | apex _ _ => exact not_cfiGraph_adj_gadget_apex _ _ _ _ _ hxz
    | edge e₂ he₂ b₂ =>
      rw [cfiGraph_adj_gadget_edge] at hxy hxz
      rw [cfiGraph_adj_edge_edge] at hyz
      obtain ⟨w₁, rfl, rfl⟩ := hxy
      obtain ⟨w₂, rfl, rfl⟩ := hxz
      obtain ⟨heq, hne⟩ := hyz
      have hw : w₁ = w₂ := Subtype.ext (Sym2.congr_right.1 heq)
      exact hne (congrArg α hw)

private theorem zmod_two_add_one_ne_self (b : ZMod 2) : b + 1 ≠ b := by
  revert b
  decide

private theorem inTriangle_edge {f : Fin m → ZMod 2} (e : Sym2 (Fin m)) (he : ¬ e.IsDiag)
    (b : ZMod 2) : InTriangle (cfiGraph m f) (.edge e he b) :=
  ⟨.edge e he (b + 1), .apex e he,
    (cfiGraph_adj_edge_edge e he b e he (b + 1)).2 ⟨rfl, (zmod_two_add_one_ne_self b).symm⟩,
    (cfiGraph_adj_edge_apex e he (b + 1) e he).2 rfl,
    (cfiGraph_adj_edge_apex e he b e he).2 rfl⟩

private theorem inTriangle_apex {f : Fin m → ZMod 2} (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
    InTriangle (cfiGraph m f) (.apex e he) :=
  ⟨.edge e he 0, .edge e he 1,
    (cfiGraph_adj_apex_edge e he e he 0).2 rfl,
    (cfiGraph_adj_edge_edge e he 0 e he 1).2 ⟨rfl, by decide⟩,
    (cfiGraph_adj_apex_edge e he e he 1).2 rfl⟩

private theorem isApexLike_apex {f : Fin m → ZMod 2} (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
    IsApexLike (cfiGraph m f) (.apex e he) := by
  refine ⟨inTriangle_apex e he, fun y hy => ?_⟩
  cases y with
  | gadget _ _ _ => exact absurd hy (not_cfiGraph_adj_apex_gadget _ _ _ _ _)
  | edge e' he' b => exact inTriangle_edge e' he' b
  | apex _ _ => exact absurd hy (not_cfiGraph_adj_apex_apex _ _ _ _)

private theorem exists_ne_pair {m : ℕ} (hm : 3 ≤ m) (v w : Fin m) :
    ∃ u : Fin m, u ≠ v ∧ u ≠ w := by
  have hlt : ({v, w} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    have hcard : ({v, w} : Finset (Fin m)).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨u, -, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hu
  exact ⟨u, hu⟩

private theorem not_isApexLike_edge (hm : 3 ≤ m) {f : Fin m → ZMod 2}
    (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2) :
    ¬ IsApexLike (cfiGraph m f) (.edge e he b) := by
  induction e using Sym2.ind with
  | _ v w =>
    have hvw : v ≠ w := Sym2.mk_isDiag_iff.not.1 he
    obtain ⟨u, huv, huw⟩ := exists_ne_pair hm v w
    let w' : {z : Fin m // z ≠ v} := ⟨w, hvw.symm⟩
    let u' : {z : Fin m // z ≠ v} := ⟨u, huv⟩
    have hwu' : w' ≠ u' := fun h => huw.symm (congrArg Subtype.val h)
    let α : {z : Fin m // z ≠ v} → ZMod 2 := Pi.single w' b + Pi.single u' (f v + b)
    have hα : ∑ z, α z = f v := by
      simp only [α, Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single']
      rw [← add_assoc, add_comm b (f v), CharTwo.add_cancel_right]
    intro hapex
    refine not_inTriangle_gadget v α hα (hapex.2 (.gadget v α hα) ?_)
    rw [cfiGraph_adj_edge_gadget]
    refine ⟨w', rfl, ?_⟩
    simp only [α, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hwu', add_zero]

private theorem isApexLike_cfiGraph_iff (hm : 3 ≤ m) {f : Fin m → ZMod 2}
    {x : CFIVertex m f} :
    IsApexLike (cfiGraph m f) x ↔
      match x with
      | .gadget _ _ _ => False
      | .edge _ _ _ => False
      | .apex _ _ => True := by
  cases x with
  | gadget v α hα =>
    exact iff_of_false (fun h => not_inTriangle_gadget v α hα h.1) id
  | edge e he b =>
    exact iff_of_false (not_isApexLike_edge hm e he b) id
  | apex e he =>
    exact iff_of_true (isApexLike_apex e he) trivial

private theorem nearApex_gadget_apex {f : Fin m → ZMod 2} (v : Fin m)
    (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v)
    (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
    NearApex (cfiGraph m f) (.gadget v α hα) (.apex e he) ↔ v ∈ e := by
  constructor
  · rintro ⟨y, hxy, hya⟩
    cases y with
    | gadget _ _ _ => exact absurd hxy (not_cfiGraph_adj_gadget_gadget _ _ _ _ _ _)
    | apex _ _ => exact absurd hxy (not_cfiGraph_adj_gadget_apex _ _ _ _ _)
    | edge e' he' b =>
      rw [cfiGraph_adj_gadget_edge] at hxy
      rw [cfiGraph_adj_edge_apex] at hya
      obtain ⟨w, rfl, -⟩ := hxy
      obtain rfl : s(v, w.val) = e := hya
      exact Sym2.mem_mk_left v w.val
  · intro hv
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 hv
    have hwv : w ≠ v := Ne.symm (Sym2.mk_isDiag_iff.not.1 he)
    exact ⟨.edge s(v, w) he (α ⟨w, hwv⟩),
      (cfiGraph_adj_gadget_edge v α hα s(v, w) he _).2 ⟨⟨w, hwv⟩, rfl, rfl⟩,
      (cfiGraph_adj_edge_apex s(v, w) he _ s(v, w) he).2 rfl⟩

private theorem eq_of_forall_mem_sym2_iff (hm : 3 ≤ m) {v₁ v₂ : Fin m}
    (h : ∀ (e : Sym2 (Fin m)), ¬ e.IsDiag → (v₁ ∈ e ↔ v₂ ∈ e)) : v₁ = v₂ := by
  by_contra hne
  obtain ⟨u, huv₁, huv₂⟩ := exists_ne_pair hm v₁ v₂
  have he : ¬ (s(v₁, u) : Sym2 (Fin m)).IsDiag := Sym2.mk_isDiag_iff.not.2 huv₁.symm
  have hv₂ : v₂ ∈ (s(v₁, u) : Sym2 (Fin m)) := (h s(v₁, u) he).1 (Sym2.mem_mk_left v₁ u)
  rw [Sym2.mem_iff] at hv₂
  exact hv₂.elim (Ne.symm hne) huv₂.symm

private def defaultDir (hm : 3 ≤ m) (v : Fin m) : {w : Fin m // w ≠ v} :=
  if h : (⟨0, by omega⟩ : Fin m) ≠ v then
    ⟨⟨0, by omega⟩, h⟩
  else
    ⟨⟨1, by omega⟩, by
      push Not at h
      rw [← h]
      exact fun h01 => Nat.one_ne_zero (congrArg Fin.val h01)⟩

private def defaultGadget (hm : 3 ≤ m) (f : Fin m → ZMod 2) (v : Fin m) : CFIVertex m f :=
  .gadget v (Pi.single (defaultDir hm v) (f v)) (Fintype.sum_pi_single' (defaultDir hm v) (f v))

private theorem not_inTriangle_defaultGadget (hm : 3 ≤ m) (f : Fin m → ZMod 2) (v : Fin m) :
    ¬ InTriangle (cfiGraph m f) (defaultGadget hm f v) :=
  not_inTriangle_gadget _ _ _

private def gadgetBase (_hm : 3 ≤ m) {f : Fin m → ZMod 2} : CFIVertex m f → Fin m
  | .gadget v _ _ => v
  | _ => ⟨0, by omega⟩

private def edgeBit {f : Fin m → ZMod 2} : CFIVertex m f → ZMod 2
  | .edge _ _ b => b
  | _ => 0

private theorem not_isDiag_map {π : Fin m ≃ Fin m} {e : Sym2 (Fin m)} (he : ¬ e.IsDiag) :
    ¬ (e.map π).IsDiag :=
  mt (Sym2.isDiag_map π.injective).1 he

private theorem exists_gadget_eq_of_not_inTriangle {f : Fin m → ZMod 2} {x : CFIVertex m f}
    (hx : ¬ InTriangle (cfiGraph m f) x) :
    ∃ (v : Fin m) (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v),
      x = .gadget v α hα := by
  cases x with
  | gadget v α hα => exact ⟨v, α, hα, rfl⟩
  | edge e he b => exact absurd (inTriangle_edge e he b) hx
  | apex e he => exact absurd (inTriangle_apex e he) hx

private theorem exists_apex_eq_of_isApexLike (hm : 3 ≤ m) {f : Fin m → ZMod 2}
    {x : CFIVertex m f} (hx : IsApexLike (cfiGraph m f) x) :
    ∃ (e : Sym2 (Fin m)) (he : ¬ e.IsDiag), x = .apex e he := by
  rw [isApexLike_cfiGraph_iff hm] at hx
  cases x with
  | gadget _ _ _ => exact absurd hx id
  | edge _ _ _ => exact absurd hx id
  | apex e he => exact ⟨e, he, rfl⟩

private theorem exists_edge_eq_of_inTriangle_not_isApexLike {f : Fin m → ZMod 2}
    {x : CFIVertex m f} (ht : InTriangle (cfiGraph m f) x)
    (ha : ¬ IsApexLike (cfiGraph m f) x) :
    ∃ (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2), x = .edge e he b := by
  cases x with
  | gadget v α hα => exact absurd ht (not_inTriangle_gadget v α hα)
  | edge e he b => exact ⟨e, he, b, rfl⟩
  | apex e he => exact absurd (isApexLike_apex e he) ha

private theorem gadgetBase_eq_of_nearApex (hm : 3 ≤ m) {g : Fin m → ZMod 2}
    {x₁ x₂ : CFIVertex m g} (hx₁ : ¬ InTriangle (cfiGraph m g) x₁)
    (hx₂ : ¬ InTriangle (cfiGraph m g) x₂)
    (hnear : ∀ a, IsApexLike (cfiGraph m g) a →
      (NearApex (cfiGraph m g) x₁ a ↔ NearApex (cfiGraph m g) x₂ a)) :
    gadgetBase hm x₁ = gadgetBase hm x₂ := by
  obtain ⟨v₁, α₁, hα₁, rfl⟩ := exists_gadget_eq_of_not_inTriangle hx₁
  obtain ⟨v₂, α₂, h₂, rfl⟩ := exists_gadget_eq_of_not_inTriangle hx₂
  change v₁ = v₂
  refine eq_of_forall_mem_sym2_iff hm fun e he => ?_
  have h := hnear (.apex e he) (isApexLike_apex e he)
  rwa [nearApex_gadget_apex v₁ α₁ hα₁ e he, nearApex_gadget_apex v₂ α₂ h₂ e he] at h

private theorem iso_gadgetBase_eq (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (φ : cfiGraph m f ≃g cfiGraph m g) (v : Fin m)
    (α : {w : Fin m // w ≠ v} → ZMod 2) (hα : ∑ w, α w = f v) :
    gadgetBase hm (φ (.gadget v α hα)) = gadgetBase hm (φ (defaultGadget hm f v)) := by
  have hx₁ : ¬ InTriangle (cfiGraph m g) (φ (.gadget v α hα)) :=
    φ.inTriangle_iff.not.2 (not_inTriangle_gadget v α hα)
  have hx₂ : ¬ InTriangle (cfiGraph m g) (φ (defaultGadget hm f v)) :=
    φ.inTriangle_iff.not.2 (not_inTriangle_defaultGadget hm f v)
  refine gadgetBase_eq_of_nearApex hm hx₁ hx₂ fun a ha => ?_
  have ha' : IsApexLike (cfiGraph m f) (φ.symm a) := φ.symm.isApexLike ha
  obtain ⟨e, he, hea⟩ := exists_apex_eq_of_isApexLike hm ha'
  have ha_eq : a = φ (.apex e he) := by
    simpa only [RelIso.apply_symm_apply] using congrArg φ hea
  rw [ha_eq, φ.nearApex_iff, φ.nearApex_iff, defaultGadget, nearApex_gadget_apex,
    nearApex_gadget_apex]

private def isoBaseEquiv (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (φ : cfiGraph m f ≃g cfiGraph m g) : Fin m ≃ Fin m where
  toFun v := gadgetBase hm (φ (defaultGadget hm f v))
  invFun v' := gadgetBase hm (φ.symm (defaultGadget hm g v'))
  left_inv v := by
    dsimp only
    have hx : ¬ InTriangle (cfiGraph m g) (φ (defaultGadget hm f v)) :=
      φ.inTriangle_iff.not.2 (not_inTriangle_defaultGadget hm f v)
    obtain ⟨v', β, hβ, hv'⟩ := exists_gadget_eq_of_not_inTriangle hx
    have hv'_eq : gadgetBase hm (φ (defaultGadget hm f v)) = v' := by
      rw [hv', gadgetBase]
    rw [hv'_eq, ← iso_gadgetBase_eq hm φ.symm v' β hβ, ← hv', φ.symm_apply_apply,
      defaultGadget, gadgetBase]
  right_inv v' := by
    dsimp only
    have hy : ¬ InTriangle (cfiGraph m f) (φ.symm (defaultGadget hm g v')) :=
      φ.symm.inTriangle_iff.not.2 (not_inTriangle_defaultGadget hm g v')
    obtain ⟨v, α, hα, hv⟩ := exists_gadget_eq_of_not_inTriangle hy
    have hv_eq : gadgetBase hm (φ.symm (defaultGadget hm g v')) = v := by
      rw [hv, gadgetBase]
    rw [hv_eq, ← iso_gadgetBase_eq hm φ v α hα, ← hv, φ.apply_symm_apply,
      defaultGadget, gadgetBase]

private theorem iso_apply_apex (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (φ : cfiGraph m f ≃g cfiGraph m g) (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) :
    φ (.apex e he) = .apex (e.map (isoBaseEquiv hm φ)) (not_isDiag_map he) := by
  set π := isoBaseEquiv hm φ
  have hapex : IsApexLike (cfiGraph m g) (φ (.apex e he)) := φ.isApexLike (isApexLike_apex e he)
  obtain ⟨e', he', hφe⟩ := exists_apex_eq_of_isApexLike hm hapex
  have he_eq : e' = e.map π := by
    ext z
    obtain ⟨u, rfl⟩ := π.surjective z
    have hx : ¬ InTriangle (cfiGraph m g) (φ (defaultGadget hm f u)) :=
      φ.inTriangle_iff.not.2 (not_inTriangle_defaultGadget hm f u)
    obtain ⟨v', β, hβ, hv'⟩ := exists_gadget_eq_of_not_inTriangle hx
    have hπu : π u = v' := by
      change gadgetBase hm (φ (defaultGadget hm f u)) = v'
      rw [hv', gadgetBase]
    have hmem1 : π u ∈ e' ↔
        NearApex (cfiGraph m g) (φ (defaultGadget hm f u)) (φ (.apex e he)) := by
      rw [hπu, hv', hφe, nearApex_gadget_apex]
    have hmem2 : NearApex (cfiGraph m f) (defaultGadget hm f u) (.apex e he) ↔ u ∈ e := by
      rw [defaultGadget, nearApex_gadget_apex]
    rw [hmem1, φ.nearApex_iff, hmem2]
    exact ⟨fun hu => Sym2.mem_map.2 ⟨u, hu, rfl⟩, fun hmap => by
      obtain ⟨u', hu', hu'eq⟩ := Sym2.mem_map.1 hmap
      rwa [← π.injective hu'eq]⟩
  subst he_eq
  exact hφe

private theorem zmod_two_eq_add_of_ne {c₀ c₁ : ZMod 2} (hne : c₀ ≠ c₁) (b : ZMod 2) :
    (if b = 0 then c₀ else c₁) = b + c₀ := by
  revert c₀ c₁ b
  decide

private theorem iso_apply_edge (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (φ : cfiGraph m f ≃g cfiGraph m g) (e : Sym2 (Fin m)) (he : ¬ e.IsDiag) (b : ZMod 2) :
    φ (.edge e he b) =
      .edge (e.map (isoBaseEquiv hm φ)) (not_isDiag_map he) (b + edgeBit (φ (.edge e he 0))) := by
  set π := isoBaseEquiv hm φ
  have hbit : ∀ c : ZMod 2,
      φ (.edge e he c) = .edge (e.map π) (not_isDiag_map he) (edgeBit (φ (.edge e he c))) := by
    intro c
    have ht : InTriangle (cfiGraph m g) (φ (.edge e he c)) := φ.inTriangle (inTriangle_edge e he c)
    have ha : ¬ IsApexLike (cfiGraph m g) (φ (.edge e he c)) :=
      φ.isApexLike_iff.not.2 (not_isApexLike_edge hm e he c)
    obtain ⟨e', he', b', hφc⟩ := exists_edge_eq_of_inTriangle_not_isApexLike ht ha
    have hadj : (cfiGraph m g).Adj (φ (.edge e he c)) (φ (.apex e he)) :=
      φ.map_adj_iff.2 ((cfiGraph_adj_edge_apex e he c e he).2 rfl)
    rw [hφc, iso_apply_apex hm φ e he, cfiGraph_adj_edge_apex] at hadj
    subst hadj
    rw [hφc, edgeBit]
  have hadj01 : (cfiGraph m g).Adj (φ (.edge e he 0)) (φ (.edge e he 1)) :=
    φ.map_adj_iff.2 ((cfiGraph_adj_edge_edge e he 0 e he 1).2 ⟨rfl, by decide⟩)
  rw [hbit 0, hbit 1, cfiGraph_adj_edge_edge] at hadj01
  have hne : edgeBit (φ (.edge e he 0)) ≠ edgeBit (φ (.edge e he 1)) := hadj01.2
  rw [hbit b]
  congr 1
  have hb : edgeBit (φ (.edge e he b)) =
      if b = 0 then edgeBit (φ (.edge e he 0)) else edgeBit (φ (.edge e he 1)) := by
    fin_cases b <;> rfl
  rw [hb, zmod_two_eq_add_of_ne hne b]

private theorem sum_symm_zero_diag : ∀ {n : ℕ} (F : Fin n → Fin n → ZMod 2),
    (∀ i j, F i j = F j i) → (∀ i, F i i = 0) → ∑ i, ∑ j, F i j = 0
  | 0, _, _, _ => rfl
  | n + 1, F, hsymm, hdiag => by
    simp only [Fin.sum_univ_castSucc, Finset.sum_add_distrib, hdiag]
    have ih := sum_symm_zero_diag (fun i j => F i.castSucc j.castSucc)
      (fun i j => hsymm _ _) (fun i => hdiag _)
    have hlast : ∑ j : Fin n, F (Fin.last n) j.castSucc =
        ∑ j : Fin n, F j.castSucc (Fin.last n) :=
      Finset.sum_congr rfl fun j _ => hsymm _ _
    rw [ih, zero_add, add_zero, hlast, CharTwo.add_self_eq_zero]

private theorem sum_eq_of_iso (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (φ : cfiGraph m f ≃g cfiGraph m g) : ∑ v, f v = ∑ v, g v := by
  set π := isoBaseEquiv hm φ
  let σ : {e : Sym2 (Fin m) // ¬ e.IsDiag} → ZMod 2 :=
    fun e => edgeBit (φ (.edge e.val e.property 0))
  let F : Fin m → Fin m → ZMod 2 := fun v w =>
    if h : w ≠ v then σ ⟨s(v, w), Sym2.mk_isDiag_iff.not.2 h.symm⟩ else 0
  have hF_symm : ∀ v w, F v w = F w v := by
    intro v w
    by_cases h : w ≠ v
    · have h' : v ≠ w := h.symm
      dsimp only [F]
      rw [dite_eq_left h, dite_eq_left h']
      congr 1
      exact Subtype.ext (by dsimp only; exact Sym2.eq_swap)
    · push Not at h
      subst h
      rfl
  have hF_diag : ∀ v, F v v = 0 := fun v => by simp only [F, ne_eq, not_true_eq_false, ↓reduceDIte]
  have hv_eq : ∀ v : Fin m, g (π v) = f v + ∑ w : Fin m, F v w := by
    intro v
    let α₀ : {w : Fin m // w ≠ v} → ZMod 2 := Pi.single (defaultDir hm v) (f v)
    have hα₀ : ∑ w, α₀ w = f v := Fintype.sum_pi_single' (defaultDir hm v) (f v)
    have hx : ¬ InTriangle (cfiGraph m g) (φ (.gadget v α₀ hα₀)) :=
      φ.inTriangle_iff.not.2 (not_inTriangle_gadget v α₀ hα₀)
    obtain ⟨v', β, hβ, hv'⟩ := exists_gadget_eq_of_not_inTriangle hx
    have hπv : π v = v' := by
      change gadgetBase hm (φ (defaultGadget hm f v)) = v'
      rw [defaultGadget, hv', gadgetBase]
    subst hπv
    let eDir : {w : Fin m // w ≠ v} ≃ {z : Fin m // z ≠ π v} :=
      { toFun := fun w => ⟨π w.val, π.injective.ne w.property⟩
        invFun := fun z => ⟨π.symm z.val, fun h => by
          have h' := congrArg π h
          rw [π.apply_symm_apply] at h'
          exact z.property h'⟩
        left_inv := fun w => Subtype.ext (π.symm_apply_apply w.val)
        right_inv := fun z => Subtype.ext (π.apply_symm_apply z.val) }
    have hβ_apply : ∀ w : {w : Fin m // w ≠ v},
        β (eDir w) = α₀ w + σ ⟨s(v, w.val), Sym2.mk_isDiag_iff.not.2 w.property.symm⟩ := by
      intro w
      have he : ¬ (s(v, w.val) : Sym2 (Fin m)).IsDiag :=
        Sym2.mk_isDiag_iff.not.2 w.property.symm
      have hadj : (cfiGraph m g).Adj (φ (.gadget v α₀ hα₀)) (φ (.edge s(v, w.val) he (α₀ w))) :=
        φ.map_adj_iff.2 ((cfiGraph_adj_gadget_edge v α₀ hα₀ s(v, w.val) he (α₀ w)).2
          ⟨w, rfl, rfl⟩)
      rw [hv', iso_apply_edge hm φ s(v, w.val) he (α₀ w), cfiGraph_adj_gadget_edge] at hadj
      obtain ⟨z, hez, hbz⟩ := hadj
      have hmap : (s(v, w.val) : Sym2 (Fin m)).map π = s(π v, π w.val) := rfl
      rw [hmap] at hez
      have hz_eq : z = eDir w := Subtype.ext (Sym2.congr_right.1 hez.symm)
      rw [← hz_eq, ← hbz]
    have hsum_F : ∑ w : {w : Fin m // w ≠ v},
        σ ⟨s(v, w.val), Sym2.mk_isDiag_iff.not.2 w.property.symm⟩ = ∑ w : Fin m, F v w := by
      symm
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun w : Fin m => w ≠ v)]
      have hzero : ∑ x ∈ Finset.univ.filter (fun w : Fin m => ¬ w ≠ v), F v x = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hx
        rw [hx, hF_diag]
      rw [hzero, add_zero, Finset.sum_subtype (p := fun w : Fin m => w ≠ v)
        (Finset.univ.filter fun w : Fin m => w ≠ v)
        (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])]
      refine Finset.sum_congr rfl fun w _ => ?_
      dsimp only [F]
      rw [dite_eq_left w.property]
    rw [← hβ, ← eDir.sum_comp β]
    simp only [hβ_apply, Finset.sum_add_distrib, hα₀, hsum_F]
  have hsum_g : ∑ v', g v' = ∑ v, g (π v) := (π.sum_comp g).symm
  rw [hsum_g]
  simp only [hv_eq, Finset.sum_add_distrib, sum_symm_zero_diag F hF_symm hF_diag, add_zero]

/-- **Cai–Fürer–Immerman non-isomorphism** ([CaiFurerImmerman1992], Section 6): when `3 ≤ m` and
`∑ v, f v ≠ ∑ v, g v`, `cfiGraph m f` and `cfiGraph m g` have no graph isomorphism. -/
theorem isEmpty_iso_cfiGraph_of_sum_ne (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (hsum : ∑ v, f v ≠ ∑ v, g v) : IsEmpty (cfiGraph m f ≃g cfiGraph m g) :=
  ⟨fun φ => hsum (sum_eq_of_iso hm φ)⟩

/-- `¬ Nonempty` form of `SimpleGraph.isEmpty_iso_cfiGraph_of_sum_ne`. -/
theorem not_nonempty_iso_cfiGraph_of_sum_ne (hm : 3 ≤ m) {f g : Fin m → ZMod 2}
    (hsum : ∑ v, f v ≠ ∑ v, g v) : ¬ Nonempty (cfiGraph m f ≃g cfiGraph m g) :=
  fun ⟨φ⟩ => hsum (sum_eq_of_iso hm φ)

private theorem zmod_two_add_one_eq_of_ne {a b : ZMod 2} (h : a ≠ b) : a + 1 = b := by
  revert a b
  decide

private theorem nonempty_iso_cfiGraph_of_sum_eq :
    ∀ (d : ℕ) {f g : Fin m → ZMod 2},
      (Finset.univ.filter fun v => f v ≠ g v).card = d →
      ∑ v, f v = ∑ v, g v →
      Nonempty (cfiGraph m f ≃g cfiGraph m g)
  | 0, f, g, hd, _ => by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hd
    have hfg : f = g := funext fun v => not_ne_iff.1 (hd (Finset.mem_univ v))
    exact ⟨hfg ▸ Iso.refl⟩
  | 1, f, g, hd, hsum => by
    obtain ⟨u, hu⟩ := Finset.card_eq_one.1 hd
    have hmem_u : u ∈ Finset.univ.filter (fun v => f v ≠ g v) := by
      rw [hu]
      exact Finset.mem_singleton_self u
    have hfu : f u ≠ g u := (Finset.mem_filter.1 hmem_u).2
    have hother : ∀ v ≠ u, f v = g v := by
      intro v hvu
      by_contra hfv
      have hmem : v ∈ Finset.univ.filter (fun x => f x ≠ g x) :=
        Finset.mem_filter.2 ⟨Finset.mem_univ v, hfv⟩
      rw [hu, Finset.mem_singleton] at hmem
      exact hvu hmem
    have hgu : g u = f u + 1 := (zmod_two_add_one_eq_of_ne hfu).symm
    have hsum' : ∑ v, g v = ∑ v, f v + 1 := by
      rw [← Finset.add_sum_erase _ g (Finset.mem_univ u),
        ← Finset.add_sum_erase _ f (Finset.mem_univ u),
        Finset.sum_congr rfl fun v hv => (hother v (Finset.ne_of_mem_erase hv)).symm,
        hgu, add_right_comm]
    rw [hsum] at hsum'
    exact absurd (add_left_cancel (a := ∑ v, g v) (b := 0) (c := 1)
      (by rw [add_zero]; exact hsum')) zero_ne_one
  | d + 2, f, g, hd, hsum => by
    have hgt : 1 < (Finset.univ.filter fun v => f v ≠ g v).card := by omega
    obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.1 hgt
    have hfu : f u ≠ g u := (Finset.mem_filter.1 hu).2
    have hfw : f w ≠ g w := (Finset.mem_filter.1 hw).2
    let f' : Fin m → ZMod 2 := f + Pi.single u 1 + Pi.single w 1
    have hf'u : f' u = g u := by
      simp only [f', Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne huw, add_zero,
        zmod_two_add_one_eq_of_ne hfu]
    have hf'w : f' w = g w := by
      simp only [f', Pi.add_apply, Pi.single_eq_of_ne huw.symm, Pi.single_eq_same, add_zero,
        zmod_two_add_one_eq_of_ne hfw]
    have hfilt : (Finset.univ.filter fun v => f' v ≠ g v) =
        ((Finset.univ.filter fun v => f v ≠ g v).erase u).erase w := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      by_cases hvw : v = w
      · subst hvw
        simp only [hf'w, ne_eq, not_true_eq_false, false_and]
      · by_cases hvu : v = u
        · subst hvu
          simp only [hf'u, ne_eq, not_true_eq_false, false_and, and_false]
        · refine ⟨fun h => ⟨hvw, hvu, ?_⟩, fun ⟨_, _, h⟩ => ?_⟩
          · dsimp only [f'] at h
            rwa [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hvu, Pi.single_eq_of_ne hvw,
              add_zero, add_zero] at h
          · dsimp only [f']
            rwa [Pi.add_apply, Pi.add_apply, Pi.single_eq_of_ne hvu, Pi.single_eq_of_ne hvw,
              add_zero, add_zero]
    have hd' : (Finset.univ.filter fun v => f' v ≠ g v).card = d := by
      have hwu_mem : w ∈ (Finset.univ.filter fun v => f v ≠ g v).erase u :=
        Finset.mem_erase.2 ⟨huw.symm, hw⟩
      rw [hfilt, Finset.card_erase_of_mem hwu_mem, Finset.card_erase_of_mem hu]
      omega
    have hsum' : ∑ v, f' v = ∑ v, g v := by
      simp only [f', Pi.add_apply, Finset.sum_add_distrib, Fintype.sum_pi_single',
        CharTwo.add_cancel_right, hsum]
    obtain ⟨ψ⟩ := nonempty_iso_cfiGraph_of_sum_eq d hd' hsum'
    exact ⟨(cfiFlipIso huw rfl).trans ψ⟩

/-- **Cai–Fürer–Immerman isomorphism classification** ([CaiFurerImmerman1992], Section 6): for
`3 ≤ m`, `cfiGraph m f` and `cfiGraph m g` are isomorphic if and only if their twist functions have
the same `ZMod 2`-sum. -/
theorem nonempty_iso_cfiGraph_iff_sum_eq (hm : 3 ≤ m) {f g : Fin m → ZMod 2} :
    Nonempty (cfiGraph m f ≃g cfiGraph m g) ↔ ∑ v, f v = ∑ v, g v :=
  ⟨fun ⟨φ⟩ => sum_eq_of_iso hm φ, nonempty_iso_cfiGraph_of_sum_eq _ rfl⟩

/-- `cfiEven k` and `cfiOdd k` have no graph isomorphism for any `k : ℕ`. -/
theorem isEmpty_iso_cfiEven_cfiOdd (k : ℕ) : IsEmpty (cfiEven k ≃g cfiOdd k) := by
  refine isEmpty_iso_cfiGraph_of_sum_ne (by omega) ?_
  simp only [Pi.zero_apply, Finset.sum_const_zero, Fintype.sum_pi_single']
  decide

/-- `¬ Nonempty` form of `SimpleGraph.isEmpty_iso_cfiEven_cfiOdd`. -/
theorem not_nonempty_iso_cfiEven_cfiOdd (k : ℕ) : ¬ Nonempty (cfiEven k ≃g cfiOdd k) :=
  fun ⟨φ⟩ => (isEmpty_iso_cfiEven_cfiOdd k).false φ

end NonIsomorphism

end SimpleGraph
