/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Amplification.Family
import Mathlib.Tactic.IrreducibleDef

/-!
# An amplification round

The main theorem of Dinur's proof of the PCP theorem [Dinur, Theorem 4.1][Dinur2005] is a single
transformation of constraint graphs that keeps satisfiable graphs satisfiable, at least doubles the
value of unsatisfiable ones until it reaches a universal constant, multiplies the size by at most a
universal constant, and leaves the alphabet fixed. It is the composite of the three operations of
the proof:

1. **preprocessing** (`Cslib.PCP.ConstraintGraph.preprocess`) with the family of `120`-regular
   expanders `Cslib.RotationMap.expanderFamily`: a `242`-regular expander on the half-edges, losing
   a factor `1452000` of the value, whatever the alphabet;
2. **powering** (`Cslib.PCP.RegularConstraintGraph.power`) along killed walks truncated at `T`
   steps, killed with probability `1 / q`, which multiplies the value by a factor linear in `q`, at
   the cost of an alphabet of size `|α| ^ (∑ ℓ ≤ T, 242 ^ ℓ)`;
3. **composition** (`Cslib.PCP.ConstraintGraph.composeSelected`), back to the fixed alphabet
   `Bool × (Fin 6 → Bool)` of `128` symbols, losing a factor `840` of the value
   whatever the alphabet it starts from.

The round `G.amplify T q` is defined over any finite alphabet `α`. For `T = 4 |α| (q - 1)`, its
value is at least `(q - 1) / (840 (4 |α| ^ 2 + 16 |α| ^ 4 + 92928000 |α| ^ 5))` times
`min (UNSAT(G) / 1452000) (1 / T ^ 2)` (`le_unsatVal_amplify`), and its numbers of vertices
and edges are those of `G` times factors depending on `|α|`, `T` and `q` only
(`card_vertices_amplify`, `card_edges_amplify`): the vertices of a preprocessed graph are the
half-edges, so the result does not depend on the vertices of `G` at all.

Over the fixed alphabet `Σ₀ = Bool × (Fin 6 → Bool)` (`Cslib.PCP.SelectedAlphabet`),
with the killing rate `q = 2 ^ 94 + 1` and the walk length `T = 2 ^ 103` chosen once and for all,
the round maps `Σ₀` to itself and **doubles the value up to the threshold** `γ = 2 ^ (-61)`:
`min (2 UNSAT(G)) γ ≤ UNSAT(G.amplify T q)` (`Cslib.PCP.Dinur.min_le_unsatVal_amplify`). This is
Dinur's main theorem, in a non-explicit form: the expanders of preprocessing are chosen
non-constructively (`Cslib.RotationMap.expanderFamily`), and the round is a noncomputable
definition. Its polynomial-time realization, with explicit expanders and a larger killing rate, is
`Cslib.PCP.Encoded.Graph.arithmeticAmplify`, in
`Complexity.Computability.PCP.Encoded.Amplification.Arithmetic`. The construction remains
asymptotic: despite the smaller answer alphabet, the size factors are triply exponential in `T`.

## Main definitions

* `Cslib.PCP.ConstraintGraph.amplify`: the amplification round, preprocessing, then powering, then
  composition.
* `Cslib.PCP.ConstraintGraph.amplifyVertexFactor`, `Cslib.PCP.ConstraintGraph.amplifyEdgeFactor`:
  the numbers of vertices and edges of the round per edge of the original graph.
* `Cslib.PCP.Dinur.killRate`, `Cslib.PCP.Dinur.walkLength`, `Cslib.PCP.Dinur.gap`:
  the parameters of the round and its threshold.

## Main results

* `Cslib.PCP.ConstraintGraph.satisfiable_amplify_iff`: the round preserves satisfiability.
* `Cslib.PCP.ConstraintGraph.le_unsatVal_amplify`: the value of the round, for any alphabet.
* `Cslib.PCP.ConstraintGraph.card_vertices_amplify`, `Cslib.PCP.ConstraintGraph.card_edges_amplify`:
  its size.
* `Cslib.PCP.Dinur.min_le_unsatVal_amplify`: over the fixed alphabet, the round doubles the value
  up to the threshold `Cslib.PCP.Dinur.gap`.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [I. Dinur, *The PCP theorem by gap amplification*, ECCC TR05-046, revision 1][Dinur2005]
-/

@[expose] public section

namespace Cslib.PCP

open Finset HadamardTester RotationMap

namespace ConstraintGraph

/-- The darts of the powered constraint graph in an amplification round on a constraint graph with
edges `E`: a half-edge of the original graph, the labels of a walk of `T` steps from it in the
preprocessed graph, and its kill signals. They are the edges of the constraint graph that
composition is applied to. -/
abbrev AmplifyDart (E : Type*) (T q : ℕ) : Type _ :=
  Amplification.Dart (Fin 120) E T q

/-- The vertices of the amplification round: those of the composed constraint graph of the powered
one, whose alphabet is `WalkLabels (PreprocessLabel (Fin 120)) T → α`. -/
abbrev AmplifyVertex (E α : Type*) (T q : ℕ) : Type _ :=
  Amplification.Vertex (Fin 120) E α T q

/-- The edges of the amplification round: those of the composed constraint graph of the powered
one. -/
abbrev AmplifyEdge (E α : Type*) (T q : ℕ) : Type _ :=
  Amplification.Edge (Fin 120) E α T q

/- The instances on the vertices and edges of the round are assembled once for any alphabet, so
that those of the round over a concrete alphabet stay below the size limit of instance
synthesis. -/

instance {E α : Type*} [Fintype E] [Fintype α] [DecidableEq α] {T q : ℕ} :
    Fintype (AmplifyVertex E α T q) :=
  inferInstanceAs (Fintype (_ ⊕ _))

instance {E α : Type*} [Fintype E] [Fintype α] [DecidableEq α] {T q : ℕ} :
    Fintype (AmplifyEdge E α T q) :=
  inferInstanceAs (Fintype (_ × _))

section Round

variable {V E α : Type*} [Fintype E] [DecidableEq V] (G : ConstraintGraph V E α)

/-- **The amplification round** [Dinur, Theorem 4.1][Dinur2005]: preprocessing with the
non-explicit family of expanders `RotationMap.expanderFamily`, then powering along killed walks
truncated at `T` steps and killed at rate `q`, then composition back to the alphabet
`SelectedAlphabet`. -/
noncomputable def amplify (T q : ℕ) [NeZero q] [Fintype α] [DecidableEq α] :
    ConstraintGraph (AmplifyVertex E α T q) (AmplifyEdge E α T q) SelectedAlphabet :=
  G.amplifyWith (.ofFamily G expanderFamily) T q

variable [Fintype α] [DecidableEq α] [Nonempty α] {T q : ℕ} [NeZero q]

/-- **The amplification round preserves satisfiability**, for walks of at least one step and a
killing rate `q ≥ 2`. -/
theorem satisfiable_amplify_iff (hT : 1 ≤ T) (hq : 2 ≤ q) :
    (G.amplify T q).Satisfiable ↔ G.Satisfiable :=
  G.satisfiable_amplifyWith_iff (.ofFamily G expanderFamily) (by norm_num) hT hq

/-- **The value of the amplification round** [Dinur, Theorem 4.1][Dinur2005]: for a killing rate
`q ≥ 2` and walks truncated at `T = 4 |α| (q - 1)` steps, it is at least
`(q - 1) / (840 (4 |α| ^ 2 + 16 |α| ^ 4 + 92928000 |α| ^ 5))` times
`min (UNSAT(G) / 1452000) (1 / T ^ 2)`. The factors `1452000` and `840` are lost by
preprocessing and composition; the factor linear in `q` is gained by powering, on the expander that
preprocessing provides. -/
theorem le_unsatVal_amplify (hq : 2 ≤ q) (hT : T = 4 * Fintype.card α * (q - 1)) :
    ((q : ℝ) - 1) / (840 * (4 * Fintype.card α ^ 2 + 16 * Fintype.card α ^ 4 +
        92928000 * Fintype.card α ^ 5)) *
      min (G.unsatVal / 1452000) (1 / T ^ 2) ≤ (G.amplify T q).unsatVal := by
  have h := G.le_unsatVal_amplifyWith (.ofFamily G expanderFamily) (by norm_num) hq hT
  norm_num [Amplification.denominator, Amplification.retention] at h
  convert h using 1 <;> first | rfl | (congr 2 <;> ring)

end Round

/-! ### Size -/

section Size

/-- The size `K ^ (∑ ℓ ≤ T, 242 ^ ℓ)` of the alphabet of the powered constraint graph in an
amplification round with walks of length `T`, over an alphabet of size `K`. -/
def amplifyAlphabetCard (K T : ℕ) : ℕ :=
  Amplification.alphabetCard 120 K T

/-- The number of vertices of an amplification round per edge of the original graph, for an
alphabet of size `K`, walks of length `T`, and killing rate `q`. With powered alphabet size `k`,
this is `2 ^ (k + 1) + 2 (2 ^ (2 k) + 2 ^ (4 k ^ 2) + 5 * 2 ^ (20 k ^ 2 + 15 k + 3)) (242 q) ^ T`.
-/
def amplifyVertexFactor (K T q : ℕ) : ℕ :=
  Amplification.vertexFactor 120 K T q

/-- The number `60 · 2 ^ (20 k ^ 2 + 15 k + 3) (242 q) ^ T` of edges of an amplification round per
edge of the original graph, where `k` is the size of the alphabet of the powered graph: an alphabet
of size `K`, walks of length `T`, killing rate `q`. -/
def amplifyEdgeFactor (K T q : ℕ) : ℕ :=
  Amplification.edgeFactor 120 K T q

variable {E α : Type*} [Fintype E] [Fintype α] (T q : ℕ)

/-- The alphabet of the powered constraint graph in an amplification round has
`|α| ^ (∑ ℓ ≤ T, 242 ^ ℓ)` symbols. -/
theorem card_walkLabels_preprocessLabel :
    Fintype.card (WalkLabels (PreprocessLabel (Fin 120)) T → α) =
      amplifyAlphabetCard (Fintype.card α) T :=
  Amplification.card_walkLabels (D := Fin 120) (α := α) T

/-- The powered constraint graph in an amplification round has `2 |E| (242 q) ^ T` darts. -/
theorem card_amplifyDart :
    Fintype.card (AmplifyDart E T q) = 2 * (242 * q) ^ T * Fintype.card E := by
  simpa only [Fintype.card_fin] using Amplification.card_dart (D := Fin 120) (E := E) T q

/-- **The size of the amplification round**: every edge of the original graph gives
`amplifyVertexFactor |α| T q` vertices. Its vertices play no role. -/
theorem card_vertices_amplify [DecidableEq α] :
    Fintype.card (AmplifyVertex E α T q) =
      amplifyVertexFactor (Fintype.card α) T q * Fintype.card E :=
  Amplification.card_vertices (D := Fin 120) (E := E) (α := α) T q

/-- **The size of the amplification round**: every edge of the original graph gives
`amplifyEdgeFactor |α| T q` edges. -/
theorem card_edges_amplify [DecidableEq α] :
    Fintype.card (AmplifyEdge E α T q) =
      amplifyEdgeFactor (Fintype.card α) T q * Fintype.card E :=
  Amplification.card_edges (D := Fin 120) (E := E) (α := α) T q

end Size

end ConstraintGraph

/-! ### Dinur's round -/

namespace Dinur

open ConstraintGraph

/-- The killing rate `q = 2 ^ 94 + 1` gives enough gain for the chosen spectral bound and
selected composition loss. It is irreducible to avoid evaluating the resulting finite types. -/
irreducible_def killRate : ℕ :=
  2 ^ 94 + 1

/-- The length `T = 2 ^ 103 = 4 |Σ₀| (q - 1)` at which the walks of Dinur's round are
truncated. It is irreducible: the sizes of Dinur's round are triply exponential in `T`, and
neither the elaborator nor the kernel should ever try to evaluate them. -/
irreducible_def walkLength : ℕ :=
  2 ^ 103

instance : NeZero killRate :=
  ⟨by rw [killRate_def]; exact Nat.succ_ne_zero _⟩

/-- The killing rate is at least `2`. -/
theorem two_le_killRate : 2 ≤ killRate := by
  rw [killRate_def]
  exact Nat.succ_le_succ Nat.one_le_two_pow

/-- The walks of Dinur's round have at least one step. -/
theorem one_le_walkLength : 1 ≤ walkLength :=
  walkLength_def ▸ Nat.one_le_two_pow

/-- The walk length is the one that the powering bound asks for. -/
theorem walkLength_eq : walkLength = 4 * Fintype.card SelectedAlphabet * (killRate - 1) := by
  rw [card_alphabet_composeSelected, walkLength_def, killRate_def, Nat.add_sub_cancel]
  norm_num

/-- The threshold `γ = 2 ^ (-61)` up to which Dinur's round doubles the value. -/
noncomputable def gap : ℝ :=
  1 / 2 ^ 61

/-- The threshold is positive. -/
theorem gap_pos : 0 < gap := by norm_num [gap]

/-- The threshold is at most one. -/
theorem gap_le_one : gap ≤ 1 := by norm_num [gap]

variable {V E : Type*} [Fintype E] [DecidableEq V] (G : ConstraintGraph V E SelectedAlphabet)

/-- **Dinur's round preserves satisfiability.** -/
theorem satisfiable_amplify_iff :
    (G.amplify walkLength killRate).Satisfiable ↔ G.Satisfiable :=
  G.satisfiable_amplify_iff one_le_walkLength two_le_killRate

/-- **Dinur's main theorem** [Dinur, Theorem 4.1][Dinur2005]: Dinur's round, over the fixed
alphabet `Σ₀`, at least doubles the value of a constraint graph, up to the threshold `gap`. -/
theorem min_le_unsatVal_amplify :
    min (2 * G.unsatVal) gap ≤ (G.amplify walkLength killRate).unsatVal := by
  apply G.min_le_unsatVal_amplifyWith (.ofFamily G expanderFamily)
    (by norm_num) two_le_killRate walkLength_eq gap_pos.le
  rw [card_alphabet_composeSelected, killRate_def, walkLength_def]
  norm_num [Amplification.gain, Amplification.retention, gap]

/-- The number of vertices of Dinur's round per edge of the original graph. -/
def vertexFactor : ℕ :=
  amplifyVertexFactor 128 walkLength killRate

/-- The number of edges of Dinur's round per edge of the original graph. -/
def edgeFactor : ℕ :=
  amplifyEdgeFactor 128 walkLength killRate

/-- **The size of Dinur's round**: every edge of the original graph gives `vertexFactor`
vertices. -/
theorem card_vertices_amplify :
    Fintype.card (AmplifyVertex E SelectedAlphabet walkLength killRate) =
      vertexFactor * Fintype.card E := by
  rw [ConstraintGraph.card_vertices_amplify, card_alphabet_composeSelected, vertexFactor]

/-- **The size of Dinur's round**: every edge of the original graph gives `edgeFactor` edges. -/
theorem card_edges_amplify :
    Fintype.card (AmplifyEdge E SelectedAlphabet walkLength killRate) =
      edgeFactor * Fintype.card E := by
  rw [ConstraintGraph.card_edges_amplify, card_alphabet_composeSelected, edgeFactor]

end Dinur

end Cslib.PCP
