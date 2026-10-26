/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Amplification
public import Complexity.Computability.PCP.Amplifier
public import Complexity.Computability.PCP.ThreeSAT

/-!
# Dinur's gap theorem

The combinatorial heart of Dinur's proof of the PCP theorem [Dinur, Corollary 4.2][Dinur2005]:
every formula `φ` in 3-CNF with `m` clauses yields a constraint graph `gapGraph φ` over the fixed
alphabet `Σ₀ = Bool × (Fin 6 → Bool)` with polynomially many vertices and edges in
`m` (`exists_card_gapGraph_le`), which is satisfiable exactly when `φ` is
(`satisfiable_gapGraph_iff`), and whose value is at least the universal constant
`Cslib.PCP.Dinur.gap` when `φ` is unsatisfiable (`gap_le_unsatVal_gapGraph`). As the
construction can be carried out in polynomial time [Dinur, Theorem 4.1][Dinur2005], telling the
two cases apart is as hard as 3-SAT: this is the PCP theorem in its gap form. This module proves
its combinatorial half; the polynomial-time half is `Cslib.PCP.Encoded.isPolyTime_gapGraph`.

The construction:

1. the constraint graph `ofCNF φ` of the formula, with `3 m` edges, over the alphabet
   `Fin 3 → Bool`, satisfiable exactly when `φ` is;
2. preprocessed and composed (`cnfGraph φ`): its vertices become the half-edges, so the variables
   of `φ` disappear, and its alphabet becomes `Σ₀`; it has a number of edges linear in `m`;
3. then `⌈log₂ |E|⌉` rounds of Dinur's amplifier (`Cslib.PCP.Dinur.amplifier`), which double the
   value up to the threshold: since an unsatisfiable graph with `|E|` edges has value at least
   `1 / |E|`, the value reaches the threshold, while the size grows by a factor polynomial in `|E|`.

Everything here is a noncomputable definition: the expanders of preprocessing are chosen
non-constructively (`Cslib.RotationMap.expanderFamily`). The polynomial-time realization, which
needs explicit expanders [Dinur, Lemma 2.2][Dinur2005], is the separate pipeline
`Cslib.PCP.Encoded.gapGraph` in `Complexity.Computability.PCP.Encoded.GapTheorem`, built on the
explicit arithmetic expander family; it is the construction the PCP theorem uses.
As the function `gapGraph` is fixed, the theorems below are not mere existence statements, which
would be trivial: a function deciding satisfiability could output one fixed graph of each kind.

## Main definitions

* `Cslib.PCP.Dinur.round`: Dinur's round on bundled constraint graphs.
* `Cslib.PCP.Dinur.amplifier`: Dinur's round as a gap amplifier.
* `Cslib.PCP.Dinur.cnfGraph`: the constraint graph of a formula over `Σ₀`.
* `Cslib.PCP.Dinur.gapGraph`: the gap graph of a formula.

## Main results

* `Cslib.PCP.Dinur.satisfiable_gapGraph_iff`: completeness and soundness, qualitatively.
* `Cslib.PCP.Dinur.gap_le_unsatVal_gapGraph`: the gap.
* `Cslib.PCP.Dinur.unsatVal_gapGraph_eq_zero_or_gap_le`: the dichotomy.
* `Cslib.PCP.Dinur.exists_card_gapGraph_le`: the size is polynomial in the number of clauses.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

universe u

namespace Cslib.PCP.Dinur

open ConstraintGraph HadamardTester Logic.PL RotationMap

/-- **Dinur's round** on a finite constraint graph over the fixed alphabet `Σ₀`:
`amplify walkLength killRate`, with the vertices and edges it builds from the edges of its input. -/
noncomputable def round (G : FinConstraintGraph.{u} SelectedAlphabet) :
    FinConstraintGraph.{u} SelectedAlphabet :=
  letI := Classical.decEq G.V
  ⟨AmplifyVertex G.E SelectedAlphabet walkLength killRate,
    AmplifyEdge G.E SelectedAlphabet walkLength killRate,
    G.graph.amplify walkLength killRate⟩

/-- Dinur's round preserves satisfiability. -/
theorem satisfiable_round_iff (G : FinConstraintGraph.{u} SelectedAlphabet) :
    (round G).graph.Satisfiable ↔ G.graph.Satisfiable :=
  letI := Classical.decEq G.V
  satisfiable_amplify_iff G.graph

/-- **Dinur's main theorem** [Dinur, Theorem 4.1][Dinur2005]: Dinur's round doubles the value up
to the threshold `gap`. -/
theorem min_le_unsatVal_round (G : FinConstraintGraph.{u} SelectedAlphabet) :
    min (2 * G.graph.unsatVal) gap ≤ (round G).graph.unsatVal :=
  letI := Classical.decEq G.V
  min_le_unsatVal_amplify G.graph

/-- Dinur's round has `vertexFactor` vertices per edge of its input. -/
theorem card_vertices_round (G : FinConstraintGraph.{u} SelectedAlphabet) :
    Fintype.card (round G).V = vertexFactor * Fintype.card G.E :=
  card_vertices_amplify

/-- Dinur's round has `edgeFactor` edges per edge of its input. -/
theorem card_edges_round (G : FinConstraintGraph.{u} SelectedAlphabet) :
    Fintype.card (round G).E = edgeFactor * Fintype.card G.E :=
  card_edges_amplify

/-- **Dinur's amplifier** [Dinur, Theorem 4.1][Dinur2005]: Dinur's round on finite constraint
graphs over the fixed alphabet `Σ₀`, which doubles the value up to the threshold `gap` and
multiplies the numbers of vertices and edges by at most `vertexFactor + edgeFactor`. -/
noncomputable def amplifier : Amplifier.{u} SelectedAlphabet where
  toFun := round
  factor := vertexFactor + edgeFactor
  gap := gap
  gap_pos := gap_pos
  gap_le_one := gap_le_one
  card_vertices_le G :=
    (card_vertices_round G).trans_le (Nat.mul_le_mul_right _ (Nat.le_add_right _ _))
  card_edges_le G :=
    (card_edges_round G).trans_le (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))
  satisfiable_iff := satisfiable_round_iff
  min_le_unsatVal := min_le_unsatVal_round

/-- The threshold of Dinur's amplifier is `gap`. -/
@[simp]
theorem gap_amplifier : amplifier.{u}.gap = gap :=
  rfl

/-- The size factor of Dinur's amplifier is `vertexFactor + edgeFactor`. -/
@[simp]
theorem factor_amplifier : amplifier.{u}.factor = vertexFactor + edgeFactor :=
  rfl

/-! ### The gap graph of a formula -/

variable {V : Type u} [DecidableEq V] (φ : CNF V)

/-- The constraint graph of a formula `φ` over the fixed alphabet `Σ₀`: its constraint graph
`ofCNF φ`, preprocessed, then composed. Preprocessing replaces the vertices by the half-edges, so
that the variables of `φ` disappear, and composition brings the alphabet to `Σ₀`. -/
noncomputable def cnfGraph : FinConstraintGraph.{0} SelectedAlphabet :=
  ⟨_, _, ((ofCNF φ).preprocess expanderFamily).toConstraintGraph.composeSelected⟩

/-- The vertices of the constraint graph of a formula over `Σ₀`: those of the composed graph of
the preprocessed `ofCNF φ`, built from its edges `Fin φ.length × Fin 3`. -/
private theorem cnfGraph_V : (cnfGraph φ).V =
    (ComposePos ((Fin φ.length × Fin 3) × Bool)
        (((Fin φ.length × Fin 3) × Bool) × PreprocessLabel (Fin 120)) (Fin 3 → Bool) ⊕
      (((Fin φ.length × Fin 3) × Bool) × PreprocessLabel (Fin 120)) ×
        (Fin 5 × Rand (Fin 3 → Bool))) :=
  rfl

/-- The edges of the constraint graph of a formula over `Σ₀`: those of the composed graph of the
preprocessed `ofCNF φ`. -/
private theorem cnfGraph_E : (cnfGraph φ).E =
    (((((Fin φ.length × Fin 3) × Bool) × PreprocessLabel (Fin 120)) ×
      (Fin 5 × Rand (Fin 3 → Bool))) × Fin 6) :=
  rfl

/-- If the clauses of `φ` have at most three literals, its constraint graph over `Σ₀` is
satisfiable exactly when `φ` is. -/
theorem satisfiable_cnfGraph_iff (h3 : ∀ κ ∈ φ, κ.length ≤ 3) :
    (cnfGraph φ).graph.Satisfiable ↔ φ.Satisfiable :=
  (satisfiable_composeSelected_iff _).trans
    (((ofCNF φ).satisfiable_preprocess_iff _ (by norm_num)).trans (satisfiable_ofCNF_iff φ h3))

/-- The alphabet `Fin 3 → Bool` of the constraint graph of a formula has eight symbols. -/
private theorem card_cnfAlphabet : Fintype.card (Fin 3 → Bool) = 8 := by
  simp

/-- The constraint graph over `Σ₀` of a formula with `m` clauses has `43560 · 2 ^ 1403 · m`
edges. -/
theorem card_edges_cnfGraph : Fintype.card (cnfGraph φ).E = 43560 * 2 ^ 1403 * φ.length := by
  rw [Fintype.card_congr' (cnfGraph_E φ), card_edges_composeSelected, card_cnfAlphabet,
    show 20 * 8 ^ 2 + 15 * 8 + 3 = 1403 from rfl]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, card_label_preprocess]
  generalize 2 ^ 1403 = c
  ring

/-- The constraint graph over `Σ₀` of a formula with `m` clauses has
`(1536 + 1452 (2 ^ 16 + 2 ^ 256 + 5 * 2 ^ 1403)) m` vertices. -/
theorem card_vertices_cnfGraph :
    Fintype.card (cnfGraph φ).V = (1536 + 1452 * (2 ^ 16 + 2 ^ 256 + 5 * 2 ^ 1403)) * φ.length := by
  rw [Fintype.card_congr' (cnfGraph_V φ), card_vertices_composeSelected, card_cnfAlphabet,
    show 20 * 8 ^ 2 + 15 * 8 + 3 = 1403 from rfl, show 4 * 8 ^ 2 = 256 from rfl,
    show 2 * 8 = 16 from rfl]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, card_label_preprocess]
  generalize 2 ^ 1403 = c
  generalize 2 ^ 256 = d
  ring

/-- **The gap graph** of a formula `φ` [Dinur, Corollary 4.2][Dinur2005]: `⌈log₂ |E|⌉` rounds of
Dinur's amplifier on the constraint graph of `φ` over `Σ₀`, which has `|E|` edges. -/
noncomputable def gapGraph : FinConstraintGraph.{0} SelectedAlphabet :=
  amplifier.iter (Nat.clog 2 (Fintype.card (cnfGraph φ).E)) (cnfGraph φ)

/-- **Completeness and soundness of the gap graph**: if the clauses of `φ` have at most three
literals, its gap graph is satisfiable exactly when `φ` is. -/
theorem satisfiable_gapGraph_iff (h3 : ∀ κ ∈ φ, κ.length ≤ 3) :
    (gapGraph φ).graph.Satisfiable ↔ φ.Satisfiable :=
  (amplifier.satisfiable_iter_iff _ _).trans (satisfiable_cnfGraph_iff φ h3)

/-- **Dinur's gap theorem** [Dinur, Corollary 4.2][Dinur2005]: if the clauses of `φ` have at most
three literals and `φ` is unsatisfiable, the value of its gap graph is at least the universal
constant `gap`. -/
theorem gap_le_unsatVal_gapGraph (h3 : ∀ κ ∈ φ, κ.length ≤ 3) (h : ¬ φ.Satisfiable) :
    gap ≤ (gapGraph φ).graph.unsatVal :=
  amplifier.gap_le_unsatVal_iter (fun hs ↦ h ((satisfiable_cnfGraph_iff φ h3).1 hs))
    (Nat.le_pow_clog one_lt_two _)

/-- **The dichotomy** [Dinur, Corollary 4.2][Dinur2005]: the value of the gap graph of a formula
is either zero or at least the universal constant `gap`. -/
theorem unsatVal_gapGraph_eq_zero_or_gap_le :
    (gapGraph φ).graph.unsatVal = 0 ∨ gap ≤ (gapGraph φ).graph.unsatVal :=
  amplifier.unsatVal_iter_eq_zero_or_gap_le _ (Nat.le_pow_clog one_lt_two _)

/-- **The gap graph is polynomial** [Dinur, Corollary 4.2][Dinur2005]: its numbers of vertices and
edges are at most `C m ^ c` for a formula with `m` clauses, for universal constants `C` and `c`. -/
theorem exists_card_gapGraph_le :
    ∃ C c : ℕ, ∀ {V : Type u} [DecidableEq V] (φ : CNF V),
      Fintype.card (gapGraph φ).V ≤ C * φ.length ^ c ∧
        Fintype.card (gapGraph φ).E ≤ C * φ.length ^ c := by
  -- the constants are kept opaque, so that nothing tries to evaluate them
  generalize hf : Nat.clog 2 amplifier.{0}.factor = f
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℕ, ∀ {V : Type u} [DecidableEq V] (φ : CNF V),
      Fintype.card (cnfGraph φ).E = c₀ * φ.length :=
    ⟨_, fun φ ↦ card_edges_cnfGraph φ⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℕ, ∀ {V : Type u} [DecidableEq V] (φ : CNF V),
      Fintype.card (cnfGraph φ).V = c₁ * φ.length :=
    ⟨_, fun φ ↦ card_vertices_cnfGraph φ⟩
  refine ⟨c₁ + 2 ^ f * c₀ ^ (f + 1), f + 1, fun φ ↦ ?_⟩
  have hE : Fintype.card (gapGraph φ).E ≤ 2 ^ f * Fintype.card (cnfGraph φ).E ^ (f + 1) := by
    rw [← hf]
    exact amplifier.card_edges_iter_clog_le (cnfGraph φ)
  have hV : Fintype.card (gapGraph φ).V ≤
      max (Fintype.card (cnfGraph φ).V) (2 ^ f * Fintype.card (cnfGraph φ).E ^ (f + 1)) := by
    rw [← hf]
    exact amplifier.card_vertices_iter_clog_le (cnfGraph φ)
  rw [hc₀] at hE hV
  rw [hc₁] at hV
  have key : 2 ^ f * (c₀ * φ.length) ^ (f + 1) ≤
      (c₁ + 2 ^ f * c₀ ^ (f + 1)) * φ.length ^ (f + 1) := by
    rw [mul_pow, ← mul_assoc, add_mul]
    exact Nat.le_add_left _ _
  refine ⟨hV.trans (max_le ?_ key), hE.trans key⟩
  rw [add_mul]
  exact Nat.le_add_right_of_le (Nat.mul_le_mul_left _ (Nat.le_self_pow (Nat.succ_ne_zero _) _))

end Cslib.PCP.Dinur
