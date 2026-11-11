/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.ExactlyOne
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
public import CslibFrontier.Logics.Propositional.CNF.ModelCount
public import CslibFrontier.Logics.Propositional.CNF.NotAllEqual
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import CslibFrontier.Foundations.Data.List.Counting
import Mathlib.Data.Finset.Card

/-!
# CNF counting encodings for independent sets, vertex colourings, and set splitting

Executable CNF encodings with explicit assignment bijections (`Equiv`), exact model counts, and
clause/variable parameter bounds for three combinatorial counting problems:

1. **Independent sets** (`indepSetCNF`, parameter `n = |V|`, width `2`): one variable per declared
   vertex, a width-2 tautology per vertex so every declared vertex occurs, and `¬x_u ∨ ¬x_v` per
   edge. Bijects satisfying assignments with independent vertex sets (`indepSetCNFEquiv`).
2. **Proper `q`-colourings** (`coloringCNF`, parameter `n = q * |V|`, width `≤ max q 2`): one-hot
   colour indicators `CNF.exactlyOne` per vertex and pairwise conflict clauses `¬x_{u,c} ∨ ¬x_{v,c}`
   per edge and colour `c < q`. Bijects satisfying assignments with `SimpleGraph.Coloring (Fin q)`
   (`coloringCNFEquiv`).
3. **Ordered `k`-set splitting** (`setSplittingCNF`, parameter `n = |U|`, width `≤ k`): positive
   and negative clauses per subset (`CNF.evalNAE`). Bijects satisfying assignments with ordered
   splitting bipartitions `(A, B)` (`setSplittingCNFEquiv`).

## Main definitions

* `Cslib.Logic.PL.CNF.indepSetCNF`, `Cslib.Logic.PL.CNF.indepSetCNFEquiv`.
* `Cslib.Logic.PL.CNF.coloringCNF`, `Cslib.Logic.PL.CNF.coloringCNFEquiv`.
* `Cslib.Logic.PL.CNF.setSplittingCNF`, `Cslib.Logic.PL.CNF.setSplittingCNFEquiv`.

## References

* [M. Cygan et al., *Parameterized Algorithms*][CyganEtAl2015]
* [L. Valiant, *The complexity of computing the permanent*][Valiant1979]
-/

public section

namespace Cslib.Logic.PL.CNF

variable {V : Type*}

/-! ### Graph adjacency helper from vertex and edge lists -/

/-- Edges between distinct declared vertices of `vs`. -/
@[expose] def edgePairs [DecidableEq V] (vs : List V) (es : List (V × V)) : List (V × V) :=
  es.filter fun e => decide (e.1 ∈ vs ∧ e.2 ∈ vs ∧ e.1 ≠ e.2)

private theorem mem_edgePairs [DecidableEq V] {vs : List V} {es : List (V × V)} {e : V × V} :
    e ∈ edgePairs vs es ↔ e ∈ es ∧ e.1 ∈ vs ∧ e.2 ∈ vs ∧ e.1 ≠ e.2 := by
  simp only [edgePairs, List.mem_filter, decide_eq_true_eq]

/-! ### 1. Independent sets (`n = |V|`, width `2`) -/

/-- **CNF encoding of independent sets**: one variable per vertex `v ∈ vs`, tautology
`[(v, true), (v, false)]` so all declared vertices occur, and `[(e.1, false), (e.2, false)]` for
every declared edge `e ∈ es`. Every clause has width `2`. -/
@[expose] def indepSetCNF [DecidableEq V] (vs : List V) (es : List (V × V)) : CNF V :=
  (vs.map fun v => [(v, true), (v, false)]) ++
    ((edgePairs vs es).map fun e => [(e.1, false), (e.2, false)])

/-- Every clause of `indepSetCNF vs es` has length `2`. -/
theorem length_clause_indepSetCNF [DecidableEq V] {vs : List V} {es : List (V × V)} {c : Clause V}
    (hc : c ∈ indepSetCNF vs es) : c.length = 2 := by
  simp only [indepSetCNF, List.mem_append, List.mem_map] at hc
  rcases hc with ⟨v, _, rfl⟩ | ⟨e, _, rfl⟩ <;> rfl

/-- The occurring variables of `indepSetCNF vs es` are precisely the vertices in `vs`. -/
@[simp]
theorem mem_vars_indepSetCNF [DecidableEq V] {vs : List V} {es : List (V × V)} {v : V} :
    v ∈ (indepSetCNF vs es).vars ↔ v ∈ vs := by
  simp only [indepSetCNF, CNF.vars, List.flatten_append, List.map_append, List.mem_append,
    List.mem_map, List.mem_flatten]
  constructor
  · rintro (⟨l, ⟨c, ⟨u, hu, rfl⟩, hl⟩, rfl⟩ | ⟨l, ⟨c, ⟨e, he, rfl⟩, hl⟩, rfl⟩)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl <;> exact hu
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      obtain ⟨-, h1, h2, -⟩ := mem_edgePairs.mp he
      rcases hl with rfl | rfl <;> assumption
  · intro hv
    exact Or.inl ⟨(v, true), ⟨[(v, true), (v, false)], ⟨v, hv, rfl⟩, List.mem_cons_self ..⟩, rfl⟩

/-- `indepSetCNF vs es` has at most `vs.toFinset.card` variables (equality holds always). -/
@[simp]
theorem numVars_indepSetCNF [DecidableEq V] (vs : List V) (es : List (V × V)) :
    (indepSetCNF vs es).numVars = vs.toFinset.card := by
  unfold CNF.numVars
  congr 1
  ext v
  simp only [List.mem_toFinset, mem_vars_indepSetCNF]

/-- Evaluation of `indepSetCNF vs es` under `σ`: no declared edge has both endpoints `true`. -/
theorem eval_indepSetCNF [DecidableEq V] (vs : List V) (es : List (V × V)) (σ : V → Bool) :
    (indepSetCNF vs es).eval σ = true ↔
      ∀ e ∈ es, e.1 ∈ vs → e.2 ∈ vs → e.1 ≠ e.2 → σ e.1 = true → σ e.2 = true → False := by
  simp only [indepSetCNF, CNF.eval_append, Bool.and_eq_true, CNF.eval_eq_true_iff,
    List.forall_mem_map, mem_edgePairs]
  have htaut : ∀ v ∈ vs, Clause.eval σ [(v, true), (v, false)] = true := fun v _ => by
    simp [Clause.eval, Literal.eval]
  rw [iff_true_intro htaut, true_and]
  simp only [Clause.eval_eq_true_iff, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, Bool.eq_false_iff, ne_eq]
  constructor
  · intro h e he h1 h2 hne hs1 hs2
    rcases h e ⟨he, h1, h2, hne⟩ with h' | h'
    · exact h' hs1
    · exact h' hs2
  · intro h e ⟨he, h1, h2, hne⟩
    by_cases hs1 : σ e.1 = true
    · exact Or.inr fun hs2 => h e he h1 h2 hne hs1 hs2
    · exact Or.inl hs1

/-- **Assignment bijection for `indepSetCNF`**: given a simple graph `G` on vertex subtype
`{v // v ∈ vs}` whose adjacency matches `es`, satisfying assignments on `vs.toFinset` biject with
independent sets of `G`. -/
def indepSetCNFEquiv [DecidableEq V] {vs : List V} {es : List (V × V)}
    {G : SimpleGraph {v : V // v ∈ vs}}
    (hG : ∀ (u w : {v : V // v ∈ vs}), G.Adj u w ↔
      u.1 ≠ w.1 ∧ ((u.1, w.1) ∈ es ∨ (w.1, u.1) ∈ es)) :
    {σ : vs.toFinset → Bool //
      (indepSetCNF vs es).eval (fun v => if hv : v ∈ vs.toFinset then σ ⟨v, hv⟩ else false) =
        true} ≃
      {S : Finset {v : V // v ∈ vs} // G.IsIndepSet (S : Set {v : V // v ∈ vs})} where
  toFun σ :=
    ⟨Finset.univ.filter fun u => σ.1 ⟨u.1, List.mem_toFinset.mpr u.2⟩ = true, by
      intro u hu w hw hne hadj
      rw [Finset.coe_filter, Set.mem_ofPred_eq] at hu hw
      obtain ⟨-, h1 | h2⟩ := (hG u w).mp hadj
      · exact ((eval_indepSetCNF vs es _).mp σ.2 (u.1, w.1) h1 u.2 w.2
          (fun h => hne (Subtype.ext h)))
          (by simpa [List.mem_toFinset.mpr u.2] using hu.2)
          (by simpa [List.mem_toFinset.mpr w.2] using hw.2)
      · exact ((eval_indepSetCNF vs es _).mp σ.2 (w.1, u.1) h2 w.2 u.2
          (fun h => hne (Subtype.ext h.symm)))
          (by simpa [List.mem_toFinset.mpr w.2] using hw.2)
          (by simpa [List.mem_toFinset.mpr u.2] using hu.2)⟩
  invFun S :=
    ⟨fun v => decide (⟨v.1, List.mem_toFinset.mp v.2⟩ ∈ S.1), by
      rw [eval_indepSetCNF]
      intro e he h1 h2 hne hs1 hs2
      have hm1 : e.1 ∈ vs.toFinset := List.mem_toFinset.mpr h1
      have hm2 : e.2 ∈ vs.toFinset := List.mem_toFinset.mpr h2
      simp only [hm1, ↓reduceDIte, decide_eq_true_eq] at hs1
      simp only [hm2, ↓reduceDIte, decide_eq_true_eq] at hs2
      have hadj : G.Adj ⟨e.1, h1⟩ ⟨e.2, h2⟩ := (hG _ _).mpr ⟨hne, Or.inl he⟩
      exact S.2 hs1 hs2 (fun h => hne (congrArg Subtype.val h)) hadj⟩
  left_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    ext v
    have hmv := List.mem_toFinset.mp v.2
    simp
  right_inv S := by
    obtain ⟨S, hS⟩ := S
    ext v
    simp

/-- **`indepSetCNF` preserves the exact count of independent sets.** -/
theorem modelCount_indepSetCNF [DecidableEq V] {vs : List V} {es : List (V × V)}
    {G : SimpleGraph {v : V // v ∈ vs}}
    (hG : ∀ (u w : {v : V // v ∈ vs}), G.Adj u w ↔
      u.1 ≠ w.1 ∧ ((u.1, w.1) ∈ es ∨ (w.1, u.1) ∈ es)) :
    (indepSetCNF vs es).modelCount =
      Nat.card {S : Finset {v : V // v ∈ vs} // G.IsIndepSet (S : Set {v : V // v ∈ vs})} := by
  classical
  have hvars : (indepSetCNF vs es).vars.toFinset = vs.toFinset := by
    ext v; simp
  rw [← modelCountOn_vars, hvars, modelCountOn, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((Equiv.subtypeEquivRight
    (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])).trans
    (indepSetCNFEquiv hG))

/-! ### 2. Proper `q`-colourings (`n = q * |V|`, width `≤ max q 2`) -/

/-- **CNF encoding of proper `q`-colourings**: one-hot variables `(v, c)` (`c < q`) per vertex
`v ∈ vs`, `CNF.exactlyOne` constraints for every vertex, and edge exclusions
`[((e.1, c), false), ((e.2, c), false)]` for every declared edge `e` and colour `c < q`. -/
@[expose] def coloringCNF [DecidableEq V] (q : ℕ) (vs : List V) (es : List (V × V)) : CNF (V × ℕ) :=
  (vs.flatMap fun v => CNF.exactlyOne ((List.range q).map fun c => (v, c))) ++
    ((edgePairs vs es).flatMap fun e =>
      (List.range q).map fun c => [((e.1, c), false), ((e.2, c), false)])

/-- Every clause of `coloringCNF q vs es` has width at most `max q 2`. -/
theorem length_clause_coloringCNF_le [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {c : Clause (V × ℕ)} (hc : c ∈ coloringCNF q vs es) : c.length ≤ max q 2 := by
  simp only [coloringCNF, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range] at hc
  rcases hc with ⟨v, _, hc⟩ | ⟨e, _, col, _, rfl⟩
  · rw [CNF.exactlyOne, List.mem_append] at hc
    rcases hc with hc | hc
    · rw [CNF.atLeastOne, List.mem_singleton] at hc
      subst hc
      simp
    · simp only [CNF.atMostOne, List.mem_flatMap, List.mem_map] at hc
      obtain ⟨_, _, _, _, rfl⟩ := hc
      exact le_max_right q 2
  · exact le_max_right q 2

/-- The occurring variables of `coloringCNF q vs es` are `{v ∈ vs} × {c < q}`. -/
@[simp]
theorem mem_vars_coloringCNF [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {p : V × ℕ} :
    p ∈ (coloringCNF q vs es).vars ↔ p.1 ∈ vs ∧ p.2 < q := by
  cases p with
  | mk v col =>
    simp only [coloringCNF, CNF.vars, List.flatten_append, List.map_append, List.mem_append,
      List.mem_map, List.mem_flatten, List.mem_flatMap]
    constructor
    · rintro (⟨⟨p', b⟩, ⟨c, ⟨w, hw, hc⟩, hl⟩, heq⟩ |
          ⟨⟨p', b⟩, ⟨c, ⟨e, he, col', hcol', rfl⟩, hl⟩, heq⟩)
      · have heqp' : p' = (v, col) := heq
        subst heqp'
        have hmem := CNF.fst_mem_of_mem_exactlyOne hc hl
        rw [List.mem_map] at hmem
        obtain ⟨k, hk, heqp⟩ := hmem
        rw [List.mem_range] at hk
        cases heqp
        exact ⟨hw, hk⟩
      · have heqp' : p' = (v, col) := heq
        subst heqp'
        obtain ⟨-, h1, h2, -⟩ := mem_edgePairs.mp he
        rw [List.mem_range] at hcol'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with hl1 | hl2
        · cases hl1; exact ⟨h1, hcol'⟩
        · cases hl2; exact ⟨h2, hcol'⟩
    · rintro ⟨hv, hcol⟩
      refine Or.inl ⟨((v, col), true),
        ⟨((List.range q).map fun c => (v, c)).map (·, true), ?_, ?_⟩, rfl⟩
      · refine ⟨v, hv, ?_⟩
        rw [CNF.exactlyOne, List.mem_append]
        exact Or.inl (by simp [CNF.atLeastOne])
      · exact List.mem_map.mpr ⟨(v, col), List.mem_map.mpr ⟨col, List.mem_range.mpr hcol, rfl⟩, rfl⟩

/-- `coloringCNF q vs es` has `q * |vs.toFinset|` occurring variables. -/
theorem numVars_coloringCNF [DecidableEq V] (q : ℕ) (vs : List V) (es : List (V × V)) :
    (coloringCNF q vs es).numVars = vs.toFinset.card * q := by
  have hvars : (coloringCNF q vs es).vars.toFinset = vs.toFinset ×ˢ Finset.range q := by
    ext ⟨v, c⟩
    simp only [List.mem_toFinset, mem_vars_coloringCNF, Finset.mem_product, Finset.mem_range]
  rw [CNF.numVars, hvars, Finset.card_product, Finset.card_range]

/-- Evaluation of `coloringCNF q vs es` under `σ`: every `v ∈ vs` has a unique true colour `< q`,
and adjacent vertices never share a colour. -/
theorem eval_coloringCNF [DecidableEq V] (q : ℕ) (vs : List V) (es : List (V × V))
    (σ : V × ℕ → Bool) :
    (coloringCNF q vs es).eval σ = true ↔
      (∀ v ∈ vs, (∃ c < q, σ (v, c) = true) ∧
        ∀ c₁ < q, ∀ c₂ < q, σ (v, c₁) = true → σ (v, c₂) = true → c₁ = c₂) ∧
      (∀ e ∈ es, e.1 ∈ vs → e.2 ∈ vs → e.1 ≠ e.2 →
        ∀ c < q, σ (e.1, c) = true → σ (e.2, c) = true → False) := by
  rw [coloringCNF, CNF.eval_append, Bool.and_eq_true, CNF.eval_flatMap_eq_true_iff,
    CNF.eval_flatMap_eq_true_iff]
  refine and_congr ?_ ?_
  · refine forall₂_congr fun v _ => ?_
    rw [CNF.eval_exactlyOne]
    simp only [List.mem_map, List.mem_range]
    constructor
    · rintro ⟨⟨_, ⟨c, hc, rfl⟩, hsc⟩, huniq⟩
      refine ⟨⟨c, hc, hsc⟩, fun c₁ hc₁ c₂ hc₂ h1 h2 => ?_⟩
      have heq := huniq (v, c₁) ⟨c₁, hc₁, rfl⟩ (v, c₂) ⟨c₂, hc₂, rfl⟩ h1 h2
      exact congrArg Prod.snd heq
    · rintro ⟨⟨c, hc, hsc⟩, huniq⟩
      refine ⟨⟨(v, c), ⟨c, hc, rfl⟩, hsc⟩, ?_⟩
      rintro ⟨v₁, c₁⟩ ⟨k₁, hk₁, heq₁⟩ ⟨v₂, c₂⟩ ⟨k₂, hk₂, heq₂⟩ h1 h2
      cases heq₁; cases heq₂
      exact congrArg (v, ·) (huniq c₁ hk₁ c₂ hk₂ h1 h2)
  · simp only [mem_edgePairs, CNF.eval_eq_true_iff, List.forall_mem_map, List.mem_range,
      Clause.eval_eq_true_iff, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
      exists_eq_left, Bool.eq_false_iff]
    constructor
    · intro h e he h1 h2 hne c hc hs1 hs2
      rcases h e ⟨he, h1, h2, hne⟩ c hc with h' | h'
      · exact h' hs1
      · exact h' hs2
    · intro h e ⟨he, h1, h2, hne⟩ c hc
      by_cases hs1 : σ (e.1, c) = true
      · exact Or.inr fun hs2 => h e he h1 h2 hne c hc hs1 hs2
      · exact Or.inl hs1

private noncomputable def coloringDecode [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {σ : (vs.toFinset ×ˢ Finset.range q : Finset (V × ℕ)) → Bool}
    (hσ : (coloringCNF q vs es).eval
      (fun p => if hp : p ∈ vs.toFinset ×ˢ Finset.range q then σ ⟨p, hp⟩ else false) = true)
    (u : {v : V // v ∈ vs}) : Fin q :=
  let h := ((eval_coloringCNF q vs es _).mp hσ).1 u.1 u.2
  ⟨h.1.choose, h.1.choose_spec.1⟩

private theorem coloringDecode_spec [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {σ : (vs.toFinset ×ˢ Finset.range q : Finset (V × ℕ)) → Bool}
    (hσ : (coloringCNF q vs es).eval
      (fun p => if hp : p ∈ vs.toFinset ×ˢ Finset.range q then σ ⟨p, hp⟩ else false) = true)
    (u : {v : V // v ∈ vs}) :
    (if hp : (u.1, (coloringDecode hσ u).1) ∈ vs.toFinset ×ˢ Finset.range q
      then σ ⟨(u.1, (coloringDecode hσ u).1), hp⟩ else false) = true :=
  (((eval_coloringCNF q vs es _).mp hσ).1 u.1 u.2).1.choose_spec.2

/-- **Assignment bijection for `coloringCNF`**: satisfying assignments on the one-hot variables
`vs.toFinset ×ˢ Finset.range q` biject with proper `Fin q`-colourings of `G`. -/

private def coloringEncode [DecidableEq V] {q : ℕ} {vs : List V}
    {G : SimpleGraph {v : V // v ∈ vs}}
    (C : G.Coloring (Fin q)) : (vs.toFinset ×ˢ Finset.range q : Finset (V × ℕ)) → Bool :=
  fun p => decide (p.1.2 = (C ⟨p.1.1, List.mem_toFinset.mp (Finset.mem_product.mp p.2).1⟩).1)

private theorem eval_coloringEncode [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {G : SimpleGraph {v : V // v ∈ vs}}
    (hG : ∀ (u w : {v : V // v ∈ vs}), G.Adj u w ↔
      u.1 ≠ w.1 ∧ ((u.1, w.1) ∈ es ∨ (w.1, u.1) ∈ es))
    (C : G.Coloring (Fin q)) :
    (coloringCNF q vs es).eval
      (fun p => if hp : p ∈ vs.toFinset ×ˢ Finset.range q then coloringEncode C ⟨p, hp⟩ else false) =
        true := by
  rw [eval_coloringCNF]
  refine ⟨fun v hv => ?_, fun e he h1 h2 hne c hc hs1 hs2 => ?_⟩
  · refine ⟨⟨(C ⟨v, hv⟩).1, (C ⟨v, hv⟩).2, ?_⟩, fun c₁ hc₁ c₂ hc₂ h1 h2 => ?_⟩
    · have hp : (v, (C ⟨v, hv⟩).1) ∈ vs.toFinset ×ˢ Finset.range q :=
        Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr (C ⟨v, hv⟩).2⟩
      simp [coloringEncode, hp]
    · have hp1 : (v, c₁) ∈ vs.toFinset ×ˢ Finset.range q :=
        Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hc₁⟩
      have hp2 : (v, c₂) ∈ vs.toFinset ×ˢ Finset.range q :=
        Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hc₂⟩
      simp only [coloringEncode, hp1, ↓reduceDIte, decide_eq_true_eq] at h1
      simp only [coloringEncode, hp2, ↓reduceDIte, decide_eq_true_eq] at h2
      exact h1.trans h2.symm
  · have hp1 : (e.1, c) ∈ vs.toFinset ×ˢ Finset.range q :=
      Finset.mem_product.mpr ⟨List.mem_toFinset.mpr h1, Finset.mem_range.mpr hc⟩
    have hp2 : (e.2, c) ∈ vs.toFinset ×ˢ Finset.range q :=
      Finset.mem_product.mpr ⟨List.mem_toFinset.mpr h2, Finset.mem_range.mpr hc⟩
    simp only [coloringEncode, hp1, ↓reduceDIte, decide_eq_true_eq] at hs1
    simp only [coloringEncode, hp2, ↓reduceDIte, decide_eq_true_eq] at hs2
    have hadj : G.Adj ⟨e.1, h1⟩ ⟨e.2, h2⟩ := (hG _ _).mpr ⟨hne, Or.inl he⟩
    exact C.valid hadj (Fin.ext (hs1.symm.trans hs2))

noncomputable def coloringCNFEquiv [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {G : SimpleGraph {v : V // v ∈ vs}}
    (hG : ∀ (u w : {v : V // v ∈ vs}), G.Adj u w ↔
      u.1 ≠ w.1 ∧ ((u.1, w.1) ∈ es ∨ (w.1, u.1) ∈ es)) :
    {σ : (vs.toFinset ×ˢ Finset.range q : Finset (V × ℕ)) → Bool //
      (coloringCNF q vs es).eval
        (fun p => if hp : p ∈ vs.toFinset ×ˢ Finset.range q then σ ⟨p, hp⟩ else false) =
          true} ≃
      G.Coloring (Fin q) where
  toFun σ :=
    SimpleGraph.Coloring.mk (coloringDecode σ.2) fun {u w} hadj hfin => by
      have heqcol : (coloringDecode σ.2 u).1 = (coloringDecode σ.2 w).1 := congrArg Fin.val hfin
      obtain ⟨hne, h1 | h2⟩ := (hG u w).mp hadj
      · exact ((eval_coloringCNF q vs es _).mp σ.2).2 (u.1, w.1) h1 u.2 w.2
          (fun h => hne h) (coloringDecode σ.2 u).1 (coloringDecode σ.2 u).2
          (coloringDecode_spec σ.2 u) (heqcol ▸ coloringDecode_spec σ.2 w)
      · exact ((eval_coloringCNF q vs es _).mp σ.2).2 (w.1, u.1) h2 w.2 u.2
          (fun h => hne h.symm) (coloringDecode σ.2 u).1 (coloringDecode σ.2 u).2
          (heqcol ▸ coloringDecode_spec σ.2 w) (coloringDecode_spec σ.2 u)
  invFun C :=
    ⟨coloringEncode C, eval_coloringEncode hG C⟩
  left_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    ext ⟨⟨v, c⟩, hp⟩
    have hv : v ∈ vs := List.mem_toFinset.mp (Finset.mem_product.mp hp).1
    have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hp).2
    have huniq := ((eval_coloringCNF q vs es _).mp hσ).1 v hv
    let col : ℕ := (coloringDecode hσ ⟨v, hv⟩).1
    have hcolLt : col < q := (coloringDecode hσ ⟨v, hv⟩).2
    have hpcol : (v, col) ∈ vs.toFinset ×ˢ Finset.range q :=
      Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hv, Finset.mem_range.mpr hcolLt⟩
    have hσcol : σ ⟨(v, col), hpcol⟩ = true := by
      have hspec := coloringDecode_spec hσ ⟨v, hv⟩
      change (if h : (v, col) ∈ vs.toFinset ×ˢ Finset.range q
        then σ ⟨(v, col), h⟩ else false) = true at hspec
      simpa only [hpcol, ↓reduceDIte] using hspec
    change decide (c = col) = σ ⟨(v, c), hp⟩
    by_cases hval : σ ⟨(v, c), hp⟩ = true
    · have hc_eq : c = col := huniq.2 c hc col hcolLt (by simpa [hp] using hval)
        (by simpa [hpcol] using hσcol)
      subst hc_eq
      simp [hval]
    · have hne : c ≠ col := by
        rintro rfl
        exact hval hσcol
      have hfalse : σ ⟨(v, c), hp⟩ = false := Bool.eq_false_iff.mpr hval
      simp [hfalse, hne]
  right_inv C := by
    ext ⟨u, hu⟩
    dsimp only
    let σ0 := coloringEncode C
    have hσ0 : (coloringCNF q vs es).eval
        (fun p => if hp : p ∈ vs.toFinset ×ˢ Finset.range q then σ0 ⟨p, hp⟩ else false) =
        true := eval_coloringEncode hG C
    change (coloringDecode hσ0 ⟨u, hu⟩).1 = (C ⟨u, hu⟩).1
    have hspec := coloringDecode_spec hσ0 ⟨u, hu⟩
    have hp : (u, (coloringDecode hσ0 ⟨u, hu⟩).1) ∈ vs.toFinset ×ˢ Finset.range q :=
      Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hu,
        Finset.mem_range.mpr (coloringDecode hσ0 ⟨u, hu⟩).2⟩
    simpa [σ0, hp] using hspec

/-- **`coloringCNF` preserves the exact count of proper `q`-colourings.** -/
theorem modelCount_coloringCNF [DecidableEq V] {q : ℕ} {vs : List V} {es : List (V × V)}
    {G : SimpleGraph {v : V // v ∈ vs}}
    (hG : ∀ (u w : {v : V // v ∈ vs}), G.Adj u w ↔
      u.1 ≠ w.1 ∧ ((u.1, w.1) ∈ es ∨ (w.1, u.1) ∈ es)) :
    (coloringCNF q vs es).modelCount = Nat.card (G.Coloring (Fin q)) := by
  classical
  have hvars : (coloringCNF q vs es).vars.toFinset = vs.toFinset ×ˢ Finset.range q := by
    ext ⟨v, c⟩; simp
  rw [← modelCountOn_vars, hvars, modelCountOn, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((Equiv.subtypeEquivRight
    (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])).trans
    (coloringCNFEquiv hG))

/-! ### 3. Ordered `k`-set splitting (`n = |U|`, width `≤ k`) -/

/-- **CNF encoding of ordered `k`-set splitting**: each subset `s ∈ sets` produces both its
positive clause `s.map (·, true)` and its negative clause `s.map (·, false)`. -/
@[expose] def setSplittingCNF (sets : List (List V)) : CNF V :=
  sets.flatMap fun s => [s.map (·, true), s.map (·, false)]

/-- Every clause of `setSplittingCNF sets` has length at most `k` when every set has size `≤ k`. -/
theorem length_clause_setSplittingCNF_le {k : ℕ} {sets : List (List V)}
    (hsets : ∀ s ∈ sets, s.length ≤ k) {c : Clause V} (hc : c ∈ setSplittingCNF sets) :
    c.length ≤ k := by
  simp only [setSplittingCNF, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hc
  obtain ⟨s, hs, rfl | rfl⟩ := hc <;> simpa using hsets s hs

/-- All variables of `setSplittingCNF sets` belong to `sets.flatten`. -/
theorem mem_vars_setSplittingCNF {sets : List (List V)} {v : V} :
    v ∈ (setSplittingCNF sets).vars ↔ v ∈ sets.flatten := by
  simp only [setSplittingCNF, CNF.vars, List.mem_map, List.mem_flatten, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro ⟨l, ⟨c, ⟨s, hs, rfl | rfl⟩, hc⟩, rfl⟩ <;>
      · obtain ⟨x, hx, heq⟩ := List.mem_map.mp hc
        cases heq
        exact ⟨s, hs, hx⟩
  · rintro ⟨s, hs, hv⟩
    exact ⟨(v, true), ⟨s.map (·, true), ⟨s, hs, Or.inl rfl⟩,
      List.mem_map.mpr ⟨v, hv, rfl⟩⟩, rfl⟩

/-- Evaluation of `setSplittingCNF sets` matches `CNF.evalNAE` on the positive clauses:
every set contains at least one `true` and one `false` element. -/
theorem eval_setSplittingCNF (sets : List (List V)) (σ : V → Bool) :
    (setSplittingCNF sets).eval σ = true ↔
      ∀ s ∈ sets, (∃ x ∈ s, σ x = true) ∧ (∃ y ∈ s, σ y = false) := by
  simp only [setSplittingCNF, CNF.eval_flatMap_eq_true_iff, CNF.eval_cons, CNF.eval_nil,
    Bool.and_true, Bool.and_eq_true, Clause.eval_eq_true_iff, List.mem_map,
    exists_exists_and_eq_and, Bool.eq_false_iff]

/-- Bridge to `CNF.evalNAE`: `setSplittingCNF` evaluates identically to `evalNAE` on the
positive hyperedge clauses. -/
theorem eval_setSplittingCNF_eq_evalNAE (sets : List (List V)) (σ : V → Bool) :
    (setSplittingCNF sets).eval σ = CNF.evalNAE σ (sets.map fun s => s.map (·, true)) := by
  rw [CNF.evalNAE, Bool.eq_iff_iff, eval_setSplittingCNF, Bool.and_eq_true]
  simp only [CNF.eval_map_eq_true_iff, Clause.eval_eq_true_iff, List.mem_map,
    exists_exists_and_eq_and, Bool.not_eq_true', imp_and, forall_and]

/-- **Assignment bijection for `setSplittingCNF`**: on any declared universe `U : Finset V`
covering `sets`, satisfying assignments on `U` biject with ordered bipartitions `(A, B)` of `U`
such that every `s ∈ sets` meets both `A` and `B`. -/
def setSplittingCNFEquiv [DecidableEq V] (U : Finset V) (sets : List (List V))
    (hsets : ∀ s ∈ sets, ∀ x ∈ s, x ∈ U) :
    {σ : U → Bool //
      (setSplittingCNF sets).eval (fun v => if hv : v ∈ U then σ ⟨v, hv⟩ else false) = true} ≃
      {P : Finset V × Finset V //
        P.1 ∪ P.2 = U ∧ Disjoint P.1 P.2 ∧
          ∀ s ∈ sets, (∃ x ∈ s, x ∈ P.1) ∧ (∃ y ∈ s, y ∈ P.2)} where
  toFun σ :=
    ⟨(U.filter fun v => if hv : v ∈ U then σ.1 ⟨v, hv⟩ = true else False,
      U.filter fun v => if hv : v ∈ U then σ.1 ⟨v, hv⟩ = false else False), by
      refine ⟨?_, ?_, ?_⟩
      · ext v
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv
        · intro hv
          cases h : σ.1 ⟨v, hv⟩
          · exact Or.inr ⟨hv, by simp [hv, h]⟩
          · exact Or.inl ⟨hv, by simp [hv, h]⟩
      · rw [Finset.disjoint_left]
        intro v h1 h2
        rw [Finset.mem_filter] at h1 h2
        rcases h1 with ⟨hv, h1⟩
        simp only [hv, ↓reduceDIte] at h1 h2
        exact Bool.noConfusion (h1.symm.trans h2.2)
      · intro s hs
        obtain ⟨⟨x, hx, hxt⟩, ⟨y, hy, hyf⟩⟩ := (eval_setSplittingCNF sets _).mp σ.2 s hs
        have hxU := hsets s hs x hx
        have hyU := hsets s hs y hy
        refine ⟨⟨x, hx, Finset.mem_filter.mpr ⟨hxU, ?_⟩⟩,
          ⟨y, hy, Finset.mem_filter.mpr ⟨hyU, ?_⟩⟩⟩
        · simpa [hxU] using hxt
        · simpa [hyU] using hyf⟩
  invFun P :=
    let ⟨⟨A, _⟩, _, hdisj, hsp⟩ := P
    ⟨fun v => decide (v.1 ∈ A), by
      rw [eval_setSplittingCNF]
      intro s hs
      obtain ⟨⟨x, hx, hx1⟩, ⟨y, hy, hy2⟩⟩ := hsp s hs
      have hxU := hsets s hs x hx
      have hyU := hsets s hs y hy
      have hy1 : y ∉ A := Finset.disjoint_right.mp hdisj hy2
      refine ⟨⟨x, hx, ?_⟩, ⟨y, hy, ?_⟩⟩
      · simp [hxU, hx1]
      · simp [hyU, hy1]⟩
  left_inv σ := by
    obtain ⟨σ, hσ⟩ := σ
    ext v
    simp [v.2]
  right_inv P := by
    obtain ⟨⟨A, B⟩, hAB, hdisj, hsp⟩ := P
    ext v
    · simp only [Finset.mem_filter, decide_eq_true_eq]
      exact ⟨fun ⟨hvU, h⟩ => by simpa [hvU] using h,
        fun hv => ⟨hAB ▸ Finset.mem_union_left B hv,
          by simp [hAB ▸ Finset.mem_union_left B hv, hv]⟩⟩
    · simp only [Finset.mem_filter, decide_eq_false_iff_not]
      constructor
      · intro ⟨hvU, hv⟩
        rw [← hAB, Finset.mem_union] at hvU
        refine hvU.resolve_left fun hA => ?_
        have hv_in : v ∈ U := hAB ▸ Finset.mem_union_left B hA
        have : decide (v ∈ A) = false := by simpa [hv_in] using hv
        simp [hA] at this
      · intro hvB
        have hvU : v ∈ U := hAB ▸ Finset.mem_union_right A hvB
        have hvnotA : v ∉ A := Finset.disjoint_right.mp hdisj hvB
        exact ⟨hvU, by simp [hvU, hvnotA]⟩

/-- **`setSplittingCNF` preserves the exact count of ordered splitting bipartitions.** -/
theorem modelCountOn_setSplittingCNF [DecidableEq V] (U : Finset V) (sets : List (List V))
    (hsets : ∀ s ∈ sets, ∀ x ∈ s, x ∈ U) :
    (setSplittingCNF sets).modelCountOn U =
      Nat.card {P : Finset V × Finset V //
        P.1 ∪ P.2 = U ∧ Disjoint P.1 P.2 ∧
          ∀ s ∈ sets, (∃ x ∈ s, x ∈ P.1) ∧ (∃ y ∈ s, y ∈ P.2)} := by
  classical
  rw [modelCountOn, ← Nat.card_eq_finsetCard]
  exact Nat.card_congr ((Equiv.subtypeEquivRight
    (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])).trans
    (setSplittingCNFEquiv U sets hsets))

end Cslib.Logic.PL.CNF
