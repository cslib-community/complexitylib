/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.FirstOrder.Locality.Sharp
public import CslibFrontierTests.FOLocality
import CslibFrontier.Tactic.FirstOrder.Simp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Exact Hanf and Gaifman locality ranks: checked instances

* **Upgrading `C_8` versus `C_4 ⊕ C_4` to rank `2`, and sharpness at rank `3`.** The 8-cycle and two
  disjoint 4-cycles are Hanf-equivalent at radius `1 = 2 ^ (2 - 1) - 1` (`nbhdIso_cycle8`), so sharp
  Hanf locality upgrades `CslibFrontierTests.FOLocality` from quantifier rank `1` to quantifier rank
  `2` (`realize_sentence_iff_of_nbhdIso_two_pow`). This cannot be improved to rank `3`
  (`2 ^ (3 - 1) - 1 = 3`): the rank-`3` sentence `hasTwinVertices` (`∃ x z, x ≠ z ∧ ∀ y, E x y →
  E z y`) holds in `C_4 ⊕ C_4` and fails in `C_8`.
* **Radius `0` suffices for quantifier rank `1` in Hanf locality.** `K_2` and its edgeless
  complement on `Fin 2` have isomorphic radius-`0` balls (`0 = 2 ^ (1 - 1) - 1`), so they agree on
  all sentences of quantifier rank at most `1`, while the rank-`2` sentence `∃ x y, E x y` separates
  them.
* **Sharp Gaifman locality on a path.** In `P_6`, vertices `1` and `3` lie in distinct automorphism
  orbits (`1` has a degree-`1` neighbor and `3` does not), yet have isomorphic radius-`1`
  neighborhoods (`1 = 2 ^ 1 - 1`); sharp Gaifman locality gives `1`-round EF equivalence and
  agreement on all formulas of quantifier rank at most `1`, while a rank-`2` formula separates them.
* **`loopReach` and matching lower bounds.** Concrete evaluation of `loopReach 0`, `loopReach 1`,
  and `loopReach 2` on a 3-vertex directed chain with a terminal self-loop; concrete witnesses from
  `exists_nbhdIso_realize_loopReach`, `exists_hanfEquiv_sentence_not_realize_iff`, and
  `exists_hanfEquiv_formula_not_realize_iff`; and nonvacuity/minimality checks showing that
  `fun n => 2 ^ n - 1` and `fun n => 2 ^ (n - 1) - 1` are the pointwise smallest Gaifman and Hanf
  locality functions.
* **Negative control (`[Nonempty M]` at `n = 1`).** Two empty structures disagreeing on a nullary
  relation are Hanf-equivalent at every radius yet Duplicator loses the `1`-round EF game. -/

public section

namespace Cslib.Tests.FOLocalitySharp

open FirstOrder Language Structure SimpleGraph
open Cslib.Logic.FO Cslib.Logic.FO.Locality
open Cslib.Tests.FOLocality (cycle8 twoCycle4 e8 nbhdIso_cycle8 nullaryLang nullaryRel)

/-! ### `C_8` versus `C_4 ⊕ C_4`: agreement up to rank `2`, separation at rank `3` -/

section Cycles

/-- `cycle8` as a `Language.graph`-structure. -/
local instance instStructureCycle8 : Language.graph.Structure (Fin 8) := cycle8.structure

/-- `twoCycle4` as a `Language.graph`-structure. -/
local instance instStructureTwoCycle4 : Language.graph.Structure (Bool × Fin 4) :=
  twoCycle4.structure

/-- **Sharp Hanf locality at `n = 2`**: because `2 ^ (2 - 1) - 1 = 1`, the 8-cycle and two disjoint
4-cycles agree on every sentence of quantifier rank at most `2` (upgrading the rank-`1` bound in
`CslibFrontierTests.FOLocality`, where `(3 ^ 2 - 1) / 2 = 4` was out of reach). -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 2) :
    Fin 8 ⊨ φ ↔ (Bool × Fin 4) ⊨ φ :=
  realize_sentence_iff_of_nbhdIso_two_pow (n := 2) e8 nbhdIso_cycle8 hφ

/-- Duplicator wins the `2`-round Ehrenfeucht–Fraïssé game between `C_8` and `C_4 ⊕ C_4`. -/
example : DuplicatorWins Language.graph 2
    (default : Fin 0 → Fin 8) (default : Fin 0 → Bool × Fin 4) :=
  HanfEquiv.duplicatorWins_of_two_pow (n := 2)
    (hanfEquiv_zero_iff.2 ⟨e8, nbhdIso_cycle8⟩)

/-- `∃ x z, x ≠ z ∧ ∀ y, adj x y → adj z y`, a sentence of quantifier rank `3`. -/
def hasTwinVertices : Language.graph.Sentence :=
  ((Term.bdEqual (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2)))).not ⊓
    (adj.boundedFormula₂ (Term.var (Sum.inr (0 : Fin 3))) (Term.var (Sum.inr (2 : Fin 3))) ⟹
      adj.boundedFormula₂ (Term.var (Sum.inr (1 : Fin 3)))
        (Term.var (Sum.inr (2 : Fin 3)))).all).ex.ex

theorem quantifierRank_hasTwinVertices : quantifierRank hasTwinVertices = 3 := by
  simp only [hasTwinVertices, Relations.boundedFormula₂, quantifierRank_ex, quantifierRank_inf,
    quantifierRank_not, quantifierRank_bdEqual, quantifierRank_all, quantifierRank_imp,
    quantifierRank_relations_boundedFormula]
  decide

theorem realize_hasTwinVertices {V : Type*} (G : SimpleGraph V) :
    (letI := G.structure; V ⊨ hasTwinVertices) ↔
      ∃ x z : V, x ≠ z ∧ ∀ y : V, G.Adj x y → G.Adj z y := by
  let := G.structure
  fo_simp [hasTwinVertices, Sentence.Realize, Formula.Realize]
  exact Iff.rfl

/-- `C_4 ⊕ C_4` satisfies `hasTwinVertices` (opposite corners of a 4-cycle share both neighbors). -/
example : (Bool × Fin 4) ⊨ hasTwinVertices :=
  (realize_hasTwinVertices twoCycle4).2 ⟨(false, 0), (false, 2), by decide, by decide⟩

/-- `C_8` refutes `hasTwinVertices`, so rank `2` cannot be improved to rank `3` at radius `1`. -/
example : ¬ (Fin 8 ⊨ hasTwinVertices) := by
  intro h
  have h8 : ¬ (∃ x z : Fin 8, x ≠ z ∧ ∀ y : Fin 8, cycle8.Adj x y → cycle8.Adj z y) := by decide
  exact h8 ((realize_hasTwinVertices cycle8).1 h)

/-- Consequently Duplicator loses the `3`-round EF game between `C_8` and `C_4 ⊕ C_4`. -/
example : ¬ DuplicatorWins Language.graph 3
    (default : Fin 0 → Fin 8) (default : Fin 0 → Bool × Fin 4) := by
  intro h
  have hiff : Fin 8 ⊨ hasTwinVertices ↔ (Bool × Fin 4) ⊨ hasTwinVertices :=
    h.realize_iff (φ := hasTwinVertices) quantifierRank_hasTwinVertices.le
  have htrue : (Bool × Fin 4) ⊨ hasTwinVertices :=
    (realize_hasTwinVertices twoCycle4).2 ⟨(false, 0), (false, 2), by decide, by decide⟩
  have h8 : ¬ (∃ x z : Fin 8, x ≠ z ∧ ∀ y : Fin 8, cycle8.Adj x y → cycle8.Adj z y) := by decide
  exact h8 ((realize_hasTwinVertices cycle8).1 (hiff.2 htrue))

end Cycles

/-! ### Hanf locality at `n = 1` uses radius `0` (`K_2` versus two isolated vertices) -/

section RankOneRadiusZero

/-- Any two simple graphs on the same vertex type have isomorphic radius-`0` singleton balls,
because simple graphs are irreflexive. -/
theorem nbhdIso_zero_of_simpleGraph {V : Type*} (G₁ G₂ : SimpleGraph V) (c : V) :
    @NbhdIso Language.graph V V G₁.structure G₂.structure 1 0 (fun _ => c) (fun _ => c) := by
  refine @IsNbhdIso.nbhdIso Language.graph V V G₁.structure G₂.structure 1 0
    (fun _ => c) (fun _ => c) id
    (@IsNbhdIso.mk Language.graph V V G₁.structure G₂.structure 1 0
      (fun _ => c) (fun _ => c) id ⟨fun u hu => ?_, fun _ _ _ _ h => h, fun v hv => ⟨v, ?_, rfl⟩⟩
      (fun _ => rfl) (fun {l} R t ht => ?_))
  · rw [@mem_ball_const Language.graph V G₁.structure, Nat.cast_zero, nonpos_iff_eq_zero,
      SimpleGraph.edist_eq_zero_iff] at hu
    subst hu
    rw [@mem_ball_const Language.graph V G₂.structure]
    dsimp only [id_eq]
    rw [SimpleGraph.edist_self, Nat.cast_zero]
  · rw [@mem_ball_const Language.graph V G₂.structure, Nat.cast_zero, nonpos_iff_eq_zero,
      SimpleGraph.edist_eq_zero_iff] at hv
    subst hv
    rw [@mem_ball_const Language.graph V G₁.structure, SimpleGraph.edist_self, Nat.cast_zero]
  · cases R
    have h0 := ht 0
    have h1 := ht 1
    rw [@mem_ball_const Language.graph V G₁.structure, Nat.cast_zero, nonpos_iff_eq_zero,
      SimpleGraph.edist_eq_zero_iff] at h0 h1
    change G₂.Adj (t 0) (t 1) ↔ G₁.Adj (t 0) (t 1)
    rw [← h0, ← h1]
    exact iff_of_false (G₂.loopless.irrefl _) (G₁.loopless.irrefl _)

/-- `K_2` and the edgeless graph on `Fin 2` satisfy the same sentences of quantifier rank `≤ 1`,
since `2 ^ (1 - 1) - 1 = 0`. -/
example {φ : Language.graph.Sentence} (hφ : quantifierRank φ ≤ 1) :
    (letI := (⊤ : SimpleGraph (Fin 2)).structure; Fin 2 ⊨ φ) ↔
      (letI := (⊥ : SimpleGraph (Fin 2)).structure; Fin 2 ⊨ φ) :=
  @realize_sentence_iff_of_nbhdIso_two_pow Language.graph (Fin 2) (Fin 2)
    (⊤ : SimpleGraph (Fin 2)).structure (⊥ : SimpleGraph (Fin 2)).structure _ _ _ 1
    (Equiv.refl (Fin 2)) (nbhdIso_zero_of_simpleGraph ⊤ ⊥) φ hφ

/-- At quantifier rank `2`, `∃ x y, adj x y` separates `K_2` from the edgeless graph on `Fin 2`. -/
def hasEdgeSentence : Language.graph.Sentence :=
  (adj.boundedFormula₂ (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2)))).ex.ex

example : quantifierRank hasEdgeSentence = 2 ∧
    (letI := (⊤ : SimpleGraph (Fin 2)).structure; Fin 2 ⊨ hasEdgeSentence) ∧
    ¬ (letI := (⊥ : SimpleGraph (Fin 2)).structure; Fin 2 ⊨ hasEdgeSentence) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hasEdgeSentence, Relations.boundedFormula₂, quantifierRank_ex,
      quantifierRank_relations_boundedFormula]
  · let := (⊤ : SimpleGraph (Fin 2)).structure
    fo_simp [hasEdgeSentence, Sentence.Realize, Formula.Realize]
    change ∃ x y : Fin 2, (⊤ : SimpleGraph (Fin 2)).Adj x y
    exact ⟨0, 1, by decide⟩
  · let := (⊥ : SimpleGraph (Fin 2)).structure
    fo_simp [hasEdgeSentence, Sentence.Realize, Formula.Realize]
    rintro ⟨x, y, hxy⟩
    exact hxy

end RankOneRadiusZero

/-! ### Sharp Gaifman locality on `P_6`: radius `1 = 2 ^ 1 - 1` suffices for quantifier rank `1` -/

section PathSix

/-- `pathGraph 6` as a `Language.graph`-structure. -/
local instance instStructurePath6 : Language.graph.Structure (Fin 6) := (pathGraph 6).structure

theorem mem_ball_one_path6 {c x : Fin 6} :
    x ∈ ball Language.graph (fun _ : Fin 1 => c) 1 ↔
      x.val ≤ c.val + 1 ∧ c.val ≤ x.val + 1 := by
  rw [mem_ball_const, gaifmanGraph_structure, edist_pathGraph, Nat.cast_le]
  omega

/-- Shift by `+2` maps the radius-`1` ball `{0, 1, 2}` around `1` isomorphically onto the
radius-`1` ball `{2, 3, 4}` around `3` in `P_6`. -/
theorem nbhdIso_path6_one_three :
    NbhdIso Language.graph 1 (fun _ : Fin 1 => (1 : Fin 6)) (fun _ : Fin 1 => (3 : Fin 6)) := by
  refine IsNbhdIso.nbhdIso (h := fun x : Fin 6 => ⟨min (x.val + 2) 5, by omega⟩)
    ⟨⟨?_, ?_, ?_⟩, fun _ => rfl, ?_⟩
  · intro x hx
    rw [mem_ball_one_path6] at hx ⊢
    dsimp only; omega
  · intro x hx y hy hxy
    rw [mem_ball_one_path6] at hx hy
    have hv := congrArg Fin.val hxy
    dsimp only at hv
    exact Fin.ext (by omega)
  · intro y hy
    rw [mem_ball_one_path6] at hy
    refine ⟨⟨y.val - 2, by omega⟩, ?_, Fin.ext ?_⟩
    · rw [mem_ball_one_path6]; dsimp only; omega
    · dsimp only; omega
  · intro l R t ht
    cases R
    have h0 := mem_ball_one_path6.1 (ht 0)
    have h1 := mem_ball_one_path6.1 (ht 1)
    change (pathGraph 6).Adj ⟨min ((t 0).val + 2) 5, _⟩ ⟨min ((t 1).val + 2) 5, _⟩ ↔
      (pathGraph 6).Adj (t 0) (t 1)
    simp only [pathGraph_adj]
    omega

/-- **Sharp Gaifman locality at `n = 1`**: vertices `1` and `3` of `P_6` satisfy the same formulas
of quantifier rank at most `1` (using radius `2 ^ 1 - 1 = 1` instead of `(3 ^ 2 - 1) / 2 = 4`). -/
example {φ : Language.graph.Formula (Fin 1)} (hφ : quantifierRank φ ≤ 1) :
    φ.Realize ![(1 : Fin 6)] ↔ φ.Realize ![(3 : Fin 6)] := by
  have h1 : (![(1 : Fin 6)] : Fin 1 → Fin 6) = fun _ => 1 := funext fun i => by fin_cases i; rfl
  have h3 : (![(3 : Fin 6)] : Fin 1 → Fin 6) = fun _ => 3 := funext fun i => by fin_cases i; rfl
  rw [h1, h3]
  exact nbhdIso_path6_one_three.formula_realize_iff_of_two_pow (n := 1) hφ

/-- No graph automorphism of `P_6` maps `1` to `3`, and the rank-`2` formula `hasLeafNeighbor`
(`∃ y, adj x y ∧ ∀ z, adj y z → z = x`) separates `1` from `3`. -/
def hasLeafNeighbor : Language.graph.Formula (Fin 1) :=
  (adj.boundedFormula₂ (Term.var (Sum.inl 0)) (Term.var (Sum.inr (0 : Fin 1))) ⊓
    (adj.boundedFormula₂ (Term.var (Sum.inr (0 : Fin 2))) (Term.var (Sum.inr (1 : Fin 2))) ⟹
      Term.bdEqual (Term.var (Sum.inr (1 : Fin 2))) (Term.var (Sum.inl 0))).all).ex

example : quantifierRank hasLeafNeighbor = 2 ∧
    hasLeafNeighbor.Realize ![(1 : Fin 6)] ∧
    ¬ hasLeafNeighbor.Realize ![(3 : Fin 6)] := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [hasLeafNeighbor, Relations.boundedFormula₂, quantifierRank_ex, quantifierRank_inf,
      quantifierRank_all, quantifierRank_imp, quantifierRank_relations_boundedFormula,
      quantifierRank_bdEqual]
    decide
  · fo_simp [hasLeafNeighbor, Formula.Realize]
    change ∃ y : Fin 6, (pathGraph 6).Adj 1 y ∧ ∀ z : Fin 6, (pathGraph 6).Adj y z → z = 1
    exact ⟨0, by decide, by decide⟩
  · fo_simp [hasLeafNeighbor, Formula.Realize]
    change ¬ ∃ y : Fin 6, (pathGraph 6).Adj 3 y ∧ ∀ z : Fin 6, (pathGraph 6).Adj y z → z = 3
    decide

end PathSix

/-! ### `loopReach` on a concrete 3-vertex directed chain with a terminal self-loop -/

/-- Directed chain `0 → 1 → 2` on `Fin 3` with a single self-loop at `2`. -/
def dirChain3Rel (x y : Fin 3) : Prop :=
  (x.val + 1 = y.val) ∨ (x = 2 ∧ y = 2)

section LoopReachChain

/-- `dirChain3Rel` as a `Language.graph`-structure on `Fin 3`. -/
local instance instStructureDirChain3 : Language.graph.Structure (Fin 3) :=
  relStructure dirChain3Rel

/-- `loopReach 0` holds at `2` (which has a self-loop) and fails at `1`. -/
example : (loopReach 0).Realize ![(2 : Fin 3)] ∧ ¬ (loopReach 0).Realize ![(1 : Fin 3)] := by
  simp only [realize_loopReach_zero, relMap_relStructure, dirChain3Rel]
  decide

/-- `loopReach 1` holds at `1` (distance `1 ≤ 2 ^ 1 - 1` to `2`) and fails at `0` (distance `2`). -/
example : (loopReach 1).Realize ![(1 : Fin 3)] ∧ ¬ (loopReach 1).Realize ![(0 : Fin 3)] := by
  simp only [realize_loopReach_succ, realize_distLE_zero, realize_loopReach_zero,
    relMap_relStructure, dirChain3Rel]
  decide

/-- `loopReach 2` holds at `0` (distance `2 ≤ 2 ^ 2 - 1 = 3` to `2`). -/
example : (loopReach 2).Realize ![(0 : Fin 3)] := by
  simp only [realize_loopReach_succ, realize_distLE_succ, realize_distLE_zero,
    realize_loopReach_zero, relMap_relStructure, dirChain3Rel]
  exact ⟨1, ⟨1, .inr (.inl rfl), .inl rfl⟩, 2, .inr (.inl rfl), .inr ⟨rfl, rfl⟩⟩

end LoopReachChain

/-! ### Concrete lower-bound witnesses and nonvacuity/minimality of the exact ranks -/

/-- At `n = 2` and `r = 2 < 2 ^ 2 - 1 = 3`, two vertices of a finite `Language.graph`-structure
have isomorphic radius-`2` neighborhoods yet `loopReach 2` separates them. -/
example : ∃ (M : Type) (_ : Finite M) (_ : Language.graph.Structure M) (a b : Fin 1 → M),
    NbhdIso Language.graph 2 a b ∧ (loopReach 2).Realize a ∧ ¬ (loopReach 2).Realize b :=
  exists_nbhdIso_realize_loopReach (n := 2) (r := 2) (by decide) (by decide)

/-- At `n = 3` and `d = 2 < 2 ^ (3 - 1) - 1 = 3`, two finite nonempty `Language.graph`-structures
are Hanf-equivalent at radius `2` yet disagree on a sentence of quantifier rank `3`. -/
example : ∃ (M N : Type) (_ : Finite M) (_ : Nonempty M)
    (_ : Language.graph.Structure M) (_ : Language.graph.Structure N)
    (σ : Language.graph.Sentence),
    quantifierRank σ = 3 ∧
    HanfEquiv Language.graph 2 (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) ∧
    M ⊨ σ ∧ ¬ (N ⊨ σ) :=
  exists_hanfEquiv_sentence_not_realize_iff (n := 3) (d := 2) (by decide) (by decide)

/-- Likewise for `1`-tuples at `n = 3` and `d = 2`. -/
example : ∃ (M N : Type) (_ : Finite M) (_ : Nonempty M)
    (_ : Language.graph.Structure M) (_ : Language.graph.Structure N)
    (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
    quantifierRank φ = 3 ∧ HanfEquiv Language.graph 2 a b ∧ φ.Realize a ∧ ¬ φ.Realize b :=
  exists_hanfEquiv_formula_not_realize_iff (n := 3) (d := 2) (by decide) (by decide)

/-- **Exactness of `2 ^ n - 1` for Gaifman locality**: `fun n => 2 ^ n - 1` satisfies the Gaifman
locality hypothesis of `two_pow_sub_one_le_of_gaifman_radius` (confirming nonvacuity) and is
pointwise minimal among all functions with that property. -/
theorem isExactGaifmanRank :
    (∀ (n : ℕ) (M : Type) [Finite M] [Language.graph.Structure M]
      (a b : Fin 1 → M) (φ : Language.graph.Formula (Fin 1)),
      quantifierRank φ ≤ n → NbhdIso Language.graph (2 ^ n - 1) a b →
      (φ.Realize a ↔ φ.Realize b)) ∧
    ∀ ρ : ℕ → ℕ,
      (∀ (n : ℕ) (M : Type) [Finite M] [Language.graph.Structure M]
        (a b : Fin 1 → M) (φ : Language.graph.Formula (Fin 1)),
        quantifierRank φ ≤ n → NbhdIso Language.graph (ρ n) a b →
        (φ.Realize a ↔ φ.Realize b)) →
      ∀ n, 2 ^ n - 1 ≤ ρ n :=
  ⟨fun _ _ _ _ _ _ _ hφ hab => hab.formula_realize_iff_of_two_pow hφ,
    fun _ hρ => two_pow_sub_one_le_of_gaifman_radius hρ⟩

/-- **Exactness of `2 ^ (n - 1) - 1` for Hanf sentence locality**: `fun n => 2 ^ (n - 1) - 1`
satisfies the sentence Hanf-locality hypothesis of `two_pow_pred_sub_one_le_of_hanf_sentence_radius`
and is pointwise minimal among all functions with that property. -/
theorem isExactHanfSentenceRank :
    (∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
      [Language.graph.Structure M] [Language.graph.Structure N]
      (σ : Language.graph.Sentence), quantifierRank σ ≤ n →
      HanfEquiv Language.graph (2 ^ (n - 1) - 1) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) →
      (M ⊨ σ ↔ N ⊨ σ)) ∧
    ∀ ρ : ℕ → ℕ,
      (∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
        [Language.graph.Structure M] [Language.graph.Structure N]
        (σ : Language.graph.Sentence), quantifierRank σ ≤ n →
        HanfEquiv Language.graph (ρ n) (Fin.elim0 : Fin 0 → M) (Fin.elim0 : Fin 0 → N) →
        (M ⊨ σ ↔ N ⊨ σ)) →
      ∀ n, 2 ^ (n - 1) - 1 ≤ ρ n :=
  ⟨fun _ _ _ _ _ _ _ σ hσ hMN => by
      obtain ⟨f, hf⟩ := hanfEquiv_zero_iff.1 hMN
      exact realize_sentence_iff_of_nbhdIso_two_pow f hf hσ,
    fun _ hρ => two_pow_pred_sub_one_le_of_hanf_sentence_radius hρ⟩

/-- **Exactness of `2 ^ (n - 1) - 1` for Hanf `1`-tuple locality**: `fun n => 2 ^ (n - 1) - 1`
satisfies the `1`-tuple Hanf-locality hypothesis of `two_pow_pred_sub_one_le_of_hanf_radius` and is
pointwise minimal among all functions with that property. -/
theorem isExactHanfTupleRank :
    (∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
      [Language.graph.Structure M] [Language.graph.Structure N]
      (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
      quantifierRank φ ≤ n → HanfEquiv Language.graph (2 ^ (n - 1) - 1) a b →
      (φ.Realize a ↔ φ.Realize b)) ∧
    ∀ ρ : ℕ → ℕ,
      (∀ (n : ℕ) (M N : Type) [Finite M] [Nonempty M]
        [Language.graph.Structure M] [Language.graph.Structure N]
        (a : Fin 1 → M) (b : Fin 1 → N) (φ : Language.graph.Formula (Fin 1)),
        quantifierRank φ ≤ n → HanfEquiv Language.graph (ρ n) a b →
        (φ.Realize a ↔ φ.Realize b)) →
      ∀ n, 2 ^ (n - 1) - 1 ≤ ρ n :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ hφ hab => hab.formula_realize_iff_of_two_pow hφ,
    fun _ hρ => two_pow_pred_sub_one_le_of_hanf_radius hρ⟩

/-! ### Negative control: `[Nonempty M]` cannot be dropped even at `n = 1` -/

section EmptyControl

/-- On `Empty` the nullary relation holds. -/
local instance instStructureEmpty : nullaryLang.Structure Empty where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun _ _ => True

/-- On `PEmpty` the nullary relation fails. -/
local instance instStructurePEmpty : nullaryLang.Structure PEmpty.{1} where
  funMap := fun {_} f => Empty.elim f
  RelMap := fun _ _ => False

/-- Two empty structures disagreeing on a nullary relation satisfy `HanfEquiv` at radius
`2 ^ (1 - 1) - 1 = 0`, yet Duplicator loses the `1`-round EF game (`DuplicatorWins.mono` down to
round `0`), showing `[Nonempty M]` is required in `HanfEquiv.duplicatorWins_of_two_pow` for `n ≥ 1`
as well as `n = 0`. -/
example : HanfEquiv nullaryLang (2 ^ (1 - 1) - 1) (default : Fin 0 → Empty)
      (default : Fin 0 → PEmpty) ∧
    ¬ DuplicatorWins nullaryLang 1 (default : Fin 0 → Empty) (default : Fin 0 → PEmpty) := by
  refine ⟨hanfEquiv_iff.2 ⟨Equiv.equivPEmpty Empty, fun c => c.elim⟩, fun h => ?_⟩
  have h0 : DuplicatorWins nullaryLang 0 (default : Fin 0 → Empty) (default : Fin 0 → PEmpty) :=
    h.mono (Nat.zero_le 1)
  exact ((duplicatorWins_zero.1 h0).relMap_iff nullaryRel Fin.elim0).1 trivial

end EmptyControl

end Cslib.Tests.FOLocalitySharp
