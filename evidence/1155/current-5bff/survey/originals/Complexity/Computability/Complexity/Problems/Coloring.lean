/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.Graph
public import Complexity.Computability.Complexity.Problems.ThreeSAT
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Complexity.Computability.Complexity.CookLevin.Completeness
import Complexity.Computability.Complexity.Problems.SAT.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Foundations.Data.List.Counting
import Mathlib.Data.List.GetD

/-!
# Graph coloring

`KColoring k` is the set of graphs, given by a list of vertices and a list of edges, whose
declared vertices can be colored with `k` colors so that adjacent vertices get different colors
[Karp1972]; `ThreeColoring` is `KColoring 3`. Graphs are read through
`Cslib.Complexity.Graph.toSimpleGraph` restricted to the declared vertices (`SimpleGraph.induce`),
and colorings through `SimpleGraph.Colorable`. Edges with an undeclared endpoint and self-loops
are therefore ignored. A graph without declared vertices belongs to every `KColoring k`, and for
`k = 0` these are the only members.

A certificate for `KColoring k` gives each declared vertex `k` bits, at the position of its first
occurrence; the color is the number of set bits, which must be below `k`.

The reduction `SAT.toThreeColoring` is the palette, variable and clause gadget construction for
3-colorability, a standard exercise [Sipser, Chapter 7][Sipser2013]. Three palette vertices `T`, `F`
and `B` form a triangle; the two literals of each variable form a triangle with `B`, so they take
the colors of `T` and `F` in some order. The gadget of a clause is a chain of OR gadgets: its stage
`0` is adjacent to `T` and `B`, hence colored like `F`; stage `j + 1` is a triangle attached to the
output of stage `j` and to the `j`-th literal, whose output can take the color of `T` exactly when
one of them does; and the output of the last stage is adjacent to `F` and `B`, hence colored like
`T`. Chaining handles clauses of every width, including the empty clause, so the reduction is from
`SAT`; it also reduces `ThreeSAT` after rejecting clauses with more than three literals.

For `k = m + 3` colors, `SAT.toKColoring m` adds `m` universal vertices adjacent to every vertex
and to each other. They take `m` colors of their own, and the gadget vertices are colored with the
remaining three, so `KColoring k` is `NP`-complete for every `k ≥ 3`.

## Main definitions

* `Cslib.Complexity.KColoring`, `Cslib.Complexity.ThreeColoring`.
* `Cslib.Complexity.KColoring.colorOf`, `Cslib.Complexity.KColoring.verifier`.
* `Cslib.Complexity.SAT.toThreeColoring`, `Cslib.Complexity.SAT.toKColoring`.

## Main results

* `Cslib.Complexity.mem_KColoring_iff`: membership as a bounded natural-number coloring.
* `Cslib.Complexity.KColoring.isVerifier`, `Cslib.Complexity.KColoring.mem_NP`:
  `KColoring k ∈ NP encGraph` for every `k`.
* `Cslib.Complexity.SAT.toThreeColoring_mem_iff`: `toThreeColoring φ ∈ ThreeColoring ↔ φ ∈ SAT`.
* `Cslib.Complexity.SAT.computableInPolyTime_toThreeColoring`: the reduction is
  polynomial-time.
* `Cslib.Complexity.polyTimeReducible_SAT_ThreeColoring`,
  `Cslib.Complexity.polyTimeReducible_ThreeSAT_ThreeColoring`,
  `Cslib.Complexity.ThreeColoring_npHard`, `Cslib.Complexity.ThreeColoring_npComplete`:
  `ThreeColoring` is `NP`-complete.
* `Cslib.Complexity.SAT.length_toThreeColoring_le`: the graph of the 3-coloring reduction has
  linearly many vertices and edges for clauses of bounded width.
* `Cslib.Complexity.SAT.toKColoring_mem_iff`: `toKColoring m φ ∈ KColoring (m + 3) ↔ φ ∈ SAT`.
* `Cslib.Complexity.polyTimeReducible_SAT_KColoring`, `Cslib.Complexity.KColoring_npHard`,
  `Cslib.Complexity.KColoring_npComplete`: `KColoring k` is `NP`-complete for `k ≥ 3`.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM ComputableTidilyInPolyTime

/-- The graphs whose declared vertices can be colored with `k` colors, adjacent vertices getting
different colors [Karp1972]. -/
def KColoring (k : ℕ) : Set Graph := {G | (G.toSimpleGraph.induce {v | v ∈ G.1}).Colorable k}

/-- The graphs whose declared vertices can be colored with three colors, adjacent vertices getting
different colors [Sipser, Chapter 7][Sipser2013]. -/
abbrev ThreeColoring : Set Graph := KColoring 3

/-- Membership in `KColoring k` as a coloring by natural numbers below `k`. -/
theorem mem_KColoring_iff {k : ℕ} {G : Graph} :
    G ∈ KColoring k ↔ ∃ c : ℕ → ℕ, (∀ v ∈ G.1, c v < k) ∧
      ∀ u ∈ G.1, ∀ v ∈ G.1, G.toSimpleGraph.Adj u v → c u ≠ c v := by
  classical
  rw [KColoring, Set.mem_ofPred_eq, SimpleGraph.colorable_iff_exists_bdd_nat_coloring]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨fun v => if h : v ∈ G.1 then C ⟨v, h⟩ else 0, fun v hv => ?_,
      fun u hu v hv huv => ?_⟩
    · simpa only [hv, dite_true] using hC ⟨v, hv⟩
    · simpa only [hu, hv, dite_true] using C.valid (v := ⟨u, hu⟩) (w := ⟨v, hv⟩) huv
  · rintro ⟨c, hc, hadj⟩
    exact ⟨SimpleGraph.Coloring.mk (fun v => c v) fun {u v} huv => hadj u u.2 v v.2 huv,
      fun v => hc v v.2⟩

namespace KColoring

/-! ### The verifier -/

/-- The color of `v` described by the certificate `w`: the number of set bits among the `k` bits
of `w` from position `k * i` on, where `i` is the first occurrence of `v` in `V`. -/
def colorOf (k : ℕ) (V : List ℕ) (w : List Bool) (v : ℕ) : ℕ :=
  (List.range k).countP fun c => w.getD (k * V.idxOf v + c) false

/-- The verifier for `KColoring k`: every declared vertex gets a color below `k` from the
certificate, and no two adjacent declared vertices get the same color. -/
def verifier (k : ℕ) (x : Graph × List Bool) : Bool :=
  x.1.1.all fun u => decide (colorOf k x.1.1 x.2 u < k) &&
    x.1.1.all fun v => !(x.1.adjBool u v && decide (colorOf k x.1.1 x.2 u = colorOf k x.1.1 x.2 v))

/-- `KColoring.verifier k` verifies `KColoring k` with certificates of `k` bits per symbol of the
encoded graph. -/
theorem isVerifier (k : ℕ) :
    IsVerifier encGraph (Polynomial.C k * Polynomial.X) (verifier k) (KColoring k) := by
  intro G
  simp only [mem_KColoring_iff, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    verifier, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, Graph.adjBool_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨c, hc, hadj⟩
    have hcol : ∀ v ∈ G.1,
        colorOf k G.1 (unaryBlocks k (k * (encGraph G).length) fun i => c (G.1.getD i 0)) v =
          c v := by
      intro v hv
      have hlt : G.1.idxOf v < G.1.length := List.idxOf_lt_length_iff.2 hv
      have hget : G.1.getD (G.1.idxOf v) 0 = v := by
        rw [List.getD_eq_getElem _ _ hlt, List.getElem_idxOf hlt]
      have hlen := G.length_vertices_le_encGraph
      rw [colorOf, countP_unaryBlocks (by rw [hget]; exact (hc v hv).le)
        (Nat.mul_le_mul_left k (by omega)), hget]
    refine ⟨_, length_unaryBlocks .., fun u hu => ⟨by rw [hcol u hu]; exact hc u hu,
      fun v hv => ?_⟩⟩
    rw [hcol u hu, hcol v hv]
    by_cases huv : G.toSimpleGraph.Adj u v
    · exact Or.inr (hadj u hu v hv huv)
    · exact Or.inl huv
  · rintro ⟨w, -, hw⟩
    refine ⟨colorOf k G.1 w, fun v hv => (hw v hv).1, fun u hu v hv huv => ?_⟩
    rcases (hw u hu).2 v hv with h | h
    · exact (h huv).elim
    · exact h

/-- Reading a color from a certificate is polynomial-time, with the color in unary. -/
@[fun_prop]
theorem computableInPolyTime_colorOf (k : ℕ) :
    ComputableInPolyTime (fun p : (List ℕ × List Bool) × ℕ => colorOf k p.1.1 p.1.2 p.2)
      (encPair (encPair (encList encNat) encBits) encNat) encUnary := by
  refine .of_tidy ?_
  have hrange : ComputableTidilyInPolyTime (fun _ : (List ℕ × List Bool) × ℕ => List.range k)
      (encPair (encPair (encList encNat) encBits) encNat) (encList encUnary) := const _
  have hk : ComputableTidilyInPolyTime (fun _ : ((List ℕ × List Bool) × ℕ) × ℕ => k)
      (encPair (encPair (encPair (encList encNat) encBits) encNat) encUnary) encUnary := const _
  exact countPWithInput hrange (by fun_prop)

/-- The `KColoring k` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier (k : ℕ) :
    ComputableInPolyTime (verifier k) (encPair encGraph encBits) encBool := by
  refine .of_tidy ?_
  have hV : ComputableTidilyInPolyTime (fun x : Graph × List Bool => x.1.1)
      (encPair encGraph encBits) (encList encNat) := by
    unfold encGraph
    fun_prop
  have hcol : ComputableTidilyInPolyTime
      (fun p : (Graph × List Bool) × ℕ => colorOf k p.1.1.1 p.1.2 p.2)
      (encPair (encPair encGraph encBits) encNat) encUnary :=
    (computableInPolyTime_colorOf k).tidy.comp
      (g := fun p : (Graph × List Bool) × ℕ => ((p.1.1.1, p.1.2), p.2))
      (by unfold encGraph; fun_prop)
  have hproj : ComputableTidilyInPolyTime
      (fun p : ((Graph × List Bool) × ℕ) × ℕ => ((p.1.1.1, p.1.2), p.2))
      (encPair (encPair (encPair encGraph encBits) encNat) encNat)
      (encPair (encPair encGraph encNat) encNat) := by fun_prop
  have hproj' : ComputableTidilyInPolyTime
      (fun p : ((Graph × List Bool) × ℕ) × ℕ => (p.1.1, p.2))
      (encPair (encPair (encPair encGraph encBits) encNat) encNat)
      (encPair (encPair encGraph encBits) encNat) := by fun_prop
  exact allWithInput hV (bool_and' (unary_lt' hcol (const k))
    (allWithInput (hV.comp (fst _ _)) (bool_not.comp
      (bool_and' (Graph.computableInPolyTime_adjBool.tidy.comp hproj)
        ((hcol.comp (fst _ _)).decide_eq' (hcol.comp hproj'))))))

/-- `KColoring k` belongs to `NP`. -/
theorem mem_NP (k : ℕ) : KColoring k ∈ NP encGraph :=
  ⟨_, verifier k, (computableInPolyTime_verifier k), isVerifier k⟩

end KColoring

namespace SAT

/-! ### The gadget graph -/

/-- The palette vertex of color `c`: color `0` reads true, `1` reads false and `2` is the base
color. -/
def paletteVertex (c : ℕ) : ℕ := Nat.pair 0 c

/-- The vertex of a literal of `φ`, numbered by the first occurrence of its variable in `φ`. -/
def literalVertex (φ : CNF ℕ) (l : Literal ℕ) : ℕ :=
  Nat.pair 1 (Nat.pair (φ.vars.idxOf l.1) l.2.toNat)

/-- Vertex `r` of stage `j` of the gadget of clause `i`; vertex `2` is the output of the stage. -/
def gadgetVertex (i j r : ℕ) : ℕ := Nat.pair 2 (Nat.pair i (Nat.pair j r))

/-- The edges between the two literals of the variable `x` and the base palette vertex. -/
def variableEdges (φ : CNF ℕ) (x : ℕ) : List (ℕ × ℕ) :=
  [(literalVertex φ (x, true), literalVertex φ (x, false)),
    (literalVertex φ (x, true), paletteVertex 2), (literalVertex φ (x, false), paletteVertex 2)]

/-- Stage `j + 1` of the gadget of clause `i`: a triangle attached to the output of stage `j` and
to the literal `l`. -/
def stageEdges (φ : CNF ℕ) (i j : ℕ) (l : Literal ℕ) : List (ℕ × ℕ) :=
  [(gadgetVertex i (j + 1) 0, gadgetVertex i (j + 1) 1),
    (gadgetVertex i (j + 1) 1, gadgetVertex i (j + 1) 2),
    (gadgetVertex i (j + 1) 2, gadgetVertex i (j + 1) 0),
    (gadgetVertex i (j + 1) 0, gadgetVertex i j 2),
    (gadgetVertex i (j + 1) 1, literalVertex φ l)]

/-- The gadget of the clause `c` with index `i`: the output of stage `0` is adjacent to the true
and base palette vertices, one stage follows for each literal, and the output of the last stage is
adjacent to the false and base palette vertices. -/
def clauseEdges (φ : CNF ℕ) (i : ℕ) (c : Clause ℕ) : List (ℕ × ℕ) :=
  [(gadgetVertex i 0 2, paletteVertex 0), (gadgetVertex i 0 2, paletteVertex 2),
    (gadgetVertex i c.length 2, paletteVertex 1), (gadgetVertex i c.length 2, paletteVertex 2)] ++
    c.zipIdx.flatMap fun l => stageEdges φ i l.2 l.1

/-- The edges of the gadget graph of `φ`: the palette triangle, the variable triangles and the
clause gadgets. -/
def coloringEdges (φ : CNF ℕ) : List (ℕ × ℕ) :=
  [(paletteVertex 0, paletteVertex 1), (paletteVertex 1, paletteVertex 2),
    (paletteVertex 2, paletteVertex 0)] ++
    φ.vars.flatMap (variableEdges φ) ++ φ.zipIdx.flatMap fun c => clauseEdges φ c.2 c.1

/-- The reduction from `SAT` to `ThreeColoring`: the gadget graph of `φ`, whose declared vertices
are the endpoints of its edges. -/
def toThreeColoring (φ : CNF ℕ) : Graph :=
  ((coloringEdges φ).flatMap fun e => [e.1, e.2], coloringEdges φ)

/-! ### Correctness of the reduction -/

/-- No edge of the gadget graph is a self-loop. -/
private theorem ne_of_mem_coloringEdges {φ : CNF ℕ} {e : ℕ × ℕ} (he : e ∈ coloringEdges φ) :
    e.1 ≠ e.2 := by
  simp only [coloringEdges, clauseEdges, stageEdges, variableEdges, List.mem_append,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (he | ⟨x, -, he⟩) | ⟨⟨cl, i⟩, -, he | ⟨⟨l, j⟩, -, he⟩⟩
  · rcases he with rfl | rfl | rfl <;> simp [paletteVertex]
  · rcases he with rfl | rfl | rfl <;> simp [paletteVertex, literalVertex, Nat.pair_eq_pair]
  · rcases he with rfl | rfl | rfl | rfl <;> simp [paletteVertex, gadgetVertex, Nat.pair_eq_pair]
  · rcases he with rfl | rfl | rfl | rfl | rfl <;>
      simp [gadgetVertex, literalVertex, Nat.pair_eq_pair]

private theorem mem_endpoints {E : List (ℕ × ℕ)} {e : ℕ × ℕ} (he : e ∈ E) :
    e.1 ∈ E.flatMap (fun e => [e.1, e.2]) ∧ e.2 ∈ E.flatMap (fun e => [e.1, e.2]) :=
  ⟨List.mem_flatMap.2 ⟨e, he, by simp⟩, List.mem_flatMap.2 ⟨e, he, by simp⟩⟩

private theorem variableEdges_subset {φ : CNF ℕ} {x : ℕ} (hx : x ∈ φ.vars) :
    variableEdges φ x ⊆ coloringEdges φ := fun e he => by
  simp only [coloringEdges, List.mem_append, List.mem_flatMap]
  exact Or.inl (Or.inr ⟨x, hx, he⟩)

private theorem clauseEdges_subset {φ : CNF ℕ} {i : ℕ} (hi : i < φ.length) :
    clauseEdges φ i φ[i] ⊆ coloringEdges φ := fun e he => by
  simp only [coloringEdges, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(φ[i], i), List.mem_zipIdx_iff_getElem?.2 (by simp [hi]), he⟩

private theorem stageEdges_subset {φ : CNF ℕ} {i j : ℕ} (hi : i < φ.length)
    (hj : j < φ[i].length) : stageEdges φ i j φ[i][j] ⊆ coloringEdges φ := fun e he => by
  refine clauseEdges_subset hi ?_
  simp only [clauseEdges, List.mem_append, List.mem_flatMap]
  exact Or.inr ⟨(φ[i][j], j), List.mem_zipIdx_iff_getElem?.2 (by simp [hj]), he⟩

/-- In a proper coloring of the gadget graph, a clause none of whose first `j` literals is
colored like the true palette vertex has the output of stage `j` colored like the false one. -/
private theorem output_eq_of_coloring {φ : CNF ℕ} {c : ℕ → ℕ}
    (hE : ∀ e ∈ coloringEdges φ, c e.1 ≠ c e.2 ∧ c e.1 < 3 ∧ c e.2 < 3) {i : ℕ}
    (hi : i < φ.length) :
    ∀ j ≤ φ[i].length, (∀ l ∈ φ[i].take j, c (literalVertex φ l) = c (paletteVertex 1)) →
      c (gadgetVertex i j 2) = c (paletteVertex 1) := by
  have hTF := hE (paletteVertex 0, paletteVertex 1) (by simp [coloringEdges])
  have hFB := hE (paletteVertex 1, paletteVertex 2) (by simp [coloringEdges])
  have hBT := hE (paletteVertex 2, paletteVertex 0) (by simp [coloringEdges])
  intro j
  induction j with
  | zero =>
    intro _ _
    have h₁ := hE _ (clauseEdges_subset hi (by simp [clauseEdges] :
      (gadgetVertex i 0 2, paletteVertex 0) ∈ clauseEdges φ i φ[i]))
    have h₂ := hE _ (clauseEdges_subset hi (by simp [clauseEdges] :
      (gadgetVertex i 0 2, paletteVertex 2) ∈ clauseEdges φ i φ[i]))
    simp only at hTF hFB hBT h₁ h₂
    omega
  | succ j ih =>
    intro hj hlit
    have hj' : j < φ[i].length := hj
    have hpre : ∀ l ∈ φ[i].take j, c (literalVertex φ l) = c (paletteVertex 1) :=
      fun l hl => hlit l (List.take_subset_take_left _ (Nat.le_succ j) hl)
    have hout := ih hj'.le hpre
    have hl := hlit φ[i][j] (by
      rw [List.take_add_one, List.getElem?_eq_getElem hj']
      exact List.mem_append_right _ (by simp))
    have hst := stageEdges_subset hi hj'
    have h₁ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 0, gadgetVertex i (j + 1) 1) ∈ _))
    have h₂ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 1, gadgetVertex i (j + 1) 2) ∈ _))
    have h₃ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 2, gadgetVertex i (j + 1) 0) ∈ _))
    have h₄ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 0, gadgetVertex i j 2) ∈ _))
    have h₅ := hE _ (hst (by simp [stageEdges] :
      (gadgetVertex i (j + 1) 1, literalVertex φ φ[i][j]) ∈ _))
    simp only at hTF hFB hBT h₁ h₂ h₃ h₄ h₅
    omega

/-- A proper 3-coloring of the gadget graph yields a satisfying assignment. -/
private theorem satisfiable_of_coloring {φ : CNF ℕ} {c : ℕ → ℕ}
    (hE : ∀ e ∈ coloringEdges φ, c e.1 ≠ c e.2 ∧ c e.1 < 3 ∧ c e.2 < 3) : φ ∈ SAT := by
  have hTF := hE (paletteVertex 0, paletteVertex 1) (by simp [coloringEdges])
  have hFB := hE (paletteVertex 1, paletteVertex 2) (by simp [coloringEdges])
  have hBT := hE (paletteVertex 2, paletteVertex 0) (by simp [coloringEdges])
  simp only at hTF hFB hBT
  let σ : ℕ → Bool := fun x => decide (c (literalVertex φ (x, true)) = c (paletteVertex 0))
  -- A literal that `σ` falsifies is colored like the false palette vertex.
  have hfalse : ∀ l : Literal ℕ, l.1 ∈ φ.vars → σ l.1 ≠ l.2 →
      c (literalVertex φ l) = c (paletteVertex 1) := by
    rintro ⟨x, b⟩ hx hσ
    have h₁ := hE _ (variableEdges_subset hx (by simp [variableEdges] :
      (literalVertex φ (x, true), literalVertex φ (x, false)) ∈ _))
    have h₂ := hE _ (variableEdges_subset hx (by simp [variableEdges] :
      (literalVertex φ (x, true), paletteVertex 2) ∈ _))
    have h₃ := hE _ (variableEdges_subset hx (by simp [variableEdges] :
      (literalVertex φ (x, false), paletteVertex 2) ∈ _))
    simp only at h₁ h₂ h₃ hσ
    cases b
    · have : c (literalVertex φ (x, true)) = c (paletteVertex 0) := by
        simpa [σ] using hσ
      omega
    · have : c (literalVertex φ (x, true)) ≠ c (paletteVertex 0) := by
        simpa [σ] using hσ
      omega
  refine ⟨σ, (CNF.eval_eq_true_iff _ _).2 fun cl hcl => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcl
  rw [Clause.eval_eq_true_iff]
  by_contra hsat
  push Not at hsat
  have hout := output_eq_of_coloring hE hi φ[i].length le_rfl fun l hl => by
    rw [List.take_length] at hl
    exact hfalse l (CNF.mem_vars.2 ⟨_, hcl, l.2, hl⟩) (hsat l hl)
  have h := hE _ (clauseEdges_subset hi (by simp [clauseEdges] :
    (gadgetVertex i φ[i].length 2, paletteVertex 1) ∈ clauseEdges φ i φ[i]))
  exact h.1 hout

/-- The color of a literal under `σ`: `0` when it holds and `1` otherwise. -/
private def literalColor (σ : ℕ → Bool) (l : Literal ℕ) : ℕ := if σ l.1 = l.2 then 0 else 1

/-- The color of the output of stage `j` of the gadget of the clause `c` under `σ`: `0` when one
of the first `j` literals of `c` holds and `1` otherwise. -/
private def outputColor (σ : ℕ → Bool) (c : Clause ℕ) (j : ℕ) : ℕ :=
  if (c.take j).any (Literal.eval σ) then 0 else 1

/-- The 3-coloring of the gadget graph read off an assignment `σ`, decoding vertex labels. -/
private def gadgetColoring (φ : CNF ℕ) (σ : ℕ → Bool) (n : ℕ) : ℕ :=
  match n.unpair.1 with
  | 0 => n.unpair.2 % 3
  | 1 => literalColor σ (φ.vars.getD n.unpair.2.unpair.1 0, decide (n.unpair.2.unpair.2 = 1))
  | _ =>
    let c := φ.getD n.unpair.2.unpair.1 []
    let j := n.unpair.2.unpair.2.unpair.1
    let a := outputColor σ c (j - 1)
    let b := literalColor σ (c.getD (j - 1) (0, false))
    match n.unpair.2.unpair.2.unpair.2 with
    | 0 => if a = 0 then 1 else if b = 0 then 2 else 0
    | 1 => if a ≠ 0 ∧ b = 0 then 1 else 2
    | _ => outputColor σ c j

private theorem gadgetColoring_palette (φ : CNF ℕ) (σ : ℕ → Bool) (c : ℕ) :
    gadgetColoring φ σ (paletteVertex c) = c % 3 := by
  simp [gadgetColoring, paletteVertex]

private theorem gadgetColoring_literal {φ : CNF ℕ} (σ : ℕ → Bool) {l : Literal ℕ}
    (hl : l.1 ∈ φ.vars) : gadgetColoring φ σ (literalVertex φ l) = literalColor σ l := by
  obtain ⟨x, b⟩ := l
  have hlt : φ.vars.idxOf x < φ.vars.length := List.idxOf_lt_length_iff.2 hl
  simp only [gadgetColoring, literalVertex, Nat.unpair_pair]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    List.getElem_idxOf hlt]
  cases b <;> rfl

private theorem gadgetColoring_output (φ : CNF ℕ) (σ : ℕ → Bool) (i j : ℕ) :
    gadgetColoring φ σ (gadgetVertex i j 2) = outputColor σ (φ.getD i []) j := by
  simp [gadgetColoring, gadgetVertex]

private theorem gadgetColoring_stage₀ (φ : CNF ℕ) (σ : ℕ → Bool) (i j : ℕ) :
    gadgetColoring φ σ (gadgetVertex i (j + 1) 0) =
      if outputColor σ (φ.getD i []) j = 0 then 1
      else if literalColor σ ((φ.getD i []).getD j (0, false)) = 0 then 2 else 0 := by
  simp [gadgetColoring, gadgetVertex]

private theorem gadgetColoring_stage₁ (φ : CNF ℕ) (σ : ℕ → Bool) (i j : ℕ) :
    gadgetColoring φ σ (gadgetVertex i (j + 1) 1) =
      if outputColor σ (φ.getD i []) j ≠ 0 ∧
        literalColor σ ((φ.getD i []).getD j (0, false)) = 0 then 1 else 2 := by
  simp [gadgetColoring, gadgetVertex]

private theorem outputColor_succ {σ : ℕ → Bool} {c : Clause ℕ} {j : ℕ} (hj : j < c.length) :
    outputColor σ c (j + 1) =
      if outputColor σ c j = 0 ∨ literalColor σ c[j] = 0 then 0 else 1 := by
  have h : (c.take (j + 1)).any (Literal.eval σ) =
      ((c.take j).any (Literal.eval σ) || decide (σ c[j].1 = c[j].2)) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj, List.any_append]
    simp [Literal.eval, beq_eq_decide]
  unfold outputColor literalColor
  rw [h]
  by_cases h₁ : (c.take j).any (Literal.eval σ) = true <;>
    by_cases h₂ : σ c[j].1 = c[j].2 <;> simp [h₁, h₂]

/-- The coloring read off a satisfying assignment is proper on every edge of the gadget graph. -/
private theorem gadgetColoring_ne {φ : CNF ℕ} {σ : ℕ → Bool} (hσ : φ.eval σ = true) :
    ∀ e ∈ coloringEdges φ, gadgetColoring φ σ e.1 ≠ gadgetColoring φ σ e.2 := by
  intro e he
  simp only [coloringEdges, List.mem_append, List.mem_flatMap] at he
  rcases he with (he | ⟨x, hx, he⟩) | ⟨⟨cl, i⟩, hi, he⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp [gadgetColoring_palette]
  · simp only [variableEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [gadgetColoring_literal σ (l := (x, true)) hx,
        gadgetColoring_literal σ (l := (x, false)) hx, gadgetColoring_palette, literalColor] <;>
      cases σ x <;> simp
  · have hi' := List.mem_zipIdx_iff_getElem?.1 hi
    simp only at hi'
    obtain ⟨hilt, hcl⟩ := List.getElem?_eq_some_iff.1 hi'
    have hφi : φ.getD i [] = cl := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt, Option.getD_some, hcl]
    have hmem : cl ∈ φ := hcl ▸ List.getElem_mem hilt
    have hsat : (cl.take cl.length).any (Literal.eval σ) = true := by
      rw [List.take_length]
      exact (CNF.eval_eq_true_iff _ _).1 hσ cl hmem
    simp only [clauseEdges, List.mem_append, List.mem_flatMap] at he
    rcases he with he | ⟨⟨l, j⟩, hj, he⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl <;>
        simp only [gadgetColoring_palette, gadgetColoring_output, hφi, outputColor, hsat] <;>
        simp
    · have hj' := List.mem_zipIdx_iff_getElem?.1 hj
      simp only at hj'
      obtain ⟨hjlt, hl⟩ := List.getElem?_eq_some_iff.1 hj'
      have hlv : l.1 ∈ φ.vars := CNF.mem_vars.2 ⟨_, hmem, l.2, hl ▸ List.getElem_mem hjlt⟩
      have hsucc := outputColor_succ (σ := σ) hjlt
      rw [hl] at hsucc
      have hgetD : cl.getD j (0, false) = l := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlt, Option.getD_some, hl]
      have ha : outputColor σ cl j = 0 ∨ outputColor σ cl j = 1 := by
        unfold outputColor; split_ifs <;> simp
      have hb : literalColor σ l = 0 ∨ literalColor σ l = 1 := by
        unfold literalColor; split_ifs <;> simp
      simp only [stageEdges, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;>
        simp only [gadgetColoring_stage₀, gadgetColoring_stage₁, gadgetColoring_output,
          gadgetColoring_literal σ hlv, hφi, hgetD, hsucc] <;>
        split_ifs <;> omega

private theorem gadgetColoring_lt {φ : CNF ℕ} {σ : ℕ → Bool} (n : ℕ) :
    gadgetColoring φ σ n < 3 := by
  unfold gadgetColoring
  split
  · exact Nat.mod_lt _ (by norm_num)
  · unfold literalColor; split_ifs <;> simp
  · dsimp only
    split
    · split_ifs <;> simp
    · split_ifs <;> simp
    · unfold outputColor; split_ifs <;> simp

/-- **Correctness of the 3-coloring reduction.** A formula is satisfiable exactly when its gadget
graph is 3-colorable. -/
theorem toThreeColoring_mem_iff (φ : CNF ℕ) : toThreeColoring φ ∈ ThreeColoring ↔ φ ∈ SAT := by
  rw [mem_KColoring_iff]
  constructor
  · rintro ⟨c, hlt, hadj⟩
    refine satisfiable_of_coloring (c := c) fun e he => ?_
    obtain ⟨h₁, h₂⟩ := mem_endpoints he
    refine ⟨hadj _ h₁ _ h₂ ?_, hlt _ h₁, hlt _ h₂⟩
    simp only [toThreeColoring, Graph.toSimpleGraph_adj]
    exact ⟨ne_of_mem_coloringEdges he, Or.inl he⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨gadgetColoring φ σ, fun v _ => gadgetColoring_lt v, fun u _ v _ huv => ?_⟩
    · simp only [toThreeColoring, Graph.toSimpleGraph_adj] at huv
      rcases huv.2 with h | h
      · exact gadgetColoring_ne hσ _ h
      · exact (gadgetColoring_ne hσ _ h).symm

/-! ### Polynomial-time reduction -/

attribute [local fun_prop] ComputableInPolyTime.tidy in
/-- The reduction `toThreeColoring` is computable in polynomial time: vertex labels are computed in
unary from clause, position and first-occurrence indices, then converted to binary. -/
@[fun_prop]
theorem computableInPolyTime_toThreeColoring :
    ComputableInPolyTime toThreeColoring encCNF encGraph := by
  refine .of_tidy ?_
  have hlit : ComputableTidilyInPolyTime (fun p : CNF ℕ × Literal ℕ => literalVertex p.1 p.2)
      (encPair encCNF (encPair encNat encBool)) encNat := by
    unfold literalVertex
    exact unary_to_binary.comp (by fun_prop)
  have hgad : ComputableTidilyInPolyTime (fun p : ℕ × ℕ × ℕ => gadgetVertex p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encUnary encUnary)) encNat := by
    unfold gadgetVertex
    exact unary_to_binary.comp (by fun_prop)
  unfold toThreeColoring coloringEdges clauseEdges stageEdges variableEdges encGraph
  fun_prop

/-! ### Size -/

/-- **The 3-coloring reduction has linear size.** On formulas with `m` clauses of at most `k`
literals, the graph of `SAT.toThreeColoring` has at most `(24 k + 12) m + 9` vertices and edges in
total, counted as listed. -/
theorem length_toThreeColoring_le {k : ℕ} {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ k) :
    (toThreeColoring φ).1.length + (toThreeColoring φ).2.length ≤ (24 * k + 12) * φ.length + 9 := by
  have hzip : ∀ c ∈ φ.zipIdx, c.1.length ≤ k := fun c hc => by
    obtain ⟨hi, hcl⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hc)
    exact hcl ▸ hφ _ (List.getElem_mem hi)
  have hvars := CNF.length_vars_le_mul_length hφ
  have h₁ : (φ.vars.flatMap (variableEdges φ)).length ≤ φ.vars.length * 3 :=
    List.length_flatMap_le fun _ _ => by simp [variableEdges]
  have h₂ : (φ.zipIdx.flatMap fun c => clauseEdges φ c.2 c.1).length ≤
      φ.length * (5 * k + 4) := by
    simpa using List.length_flatMap_le (l := φ.zipIdx) fun c hc => by
      have hst := List.length_flatMap_le (l := c.1.zipIdx) (k := 5)
        (f := fun l => stageEdges φ c.2 l.2 l.1) fun _ _ => by simp [stageEdges]
      simp only [List.length_zipIdx] at hst
      simp only [clauseEdges, List.length_append, List.length_cons, List.length_nil]
      have := hzip c hc
      nlinarith
  have hE : (coloringEdges φ).length ≤ (8 * k + 4) * φ.length + 3 := by
    simp only [coloringEdges, List.length_append, List.length_cons, List.length_nil]
    nlinarith
  have hV : (toThreeColoring φ).1.length = 2 * (coloringEdges φ).length := by
    simp only [toThreeColoring, List.length_flatMap, List.length_cons, List.length_nil,
      List.map_const', List.sum_replicate, smul_eq_mul]
    ring
  rw [hV]
  simp only [toThreeColoring]
  nlinarith

/-! ### More colors -/

/-- The `r`-th universal vertex of the reduction to `KColoring (m + 3)`. -/
def universalVertex (r : ℕ) : ℕ := Nat.pair 3 r

/-- The edges of the gadget graph of `φ` together with `m` universal vertices, each adjacent to
every vertex of the gadget graph and to the other universal vertices. -/
def kColoringEdges (m : ℕ) (φ : CNF ℕ) : List (ℕ × ℕ) :=
  coloringEdges φ ++ (List.range m).flatMap fun r =>
    ((coloringEdges φ).flatMap fun e => [e.1, e.2]).map (fun v => (universalVertex r, v)) ++
      (List.range r).map fun r' => (universalVertex r, universalVertex r')

/-- The reduction from `SAT` to `KColoring (m + 3)`: the gadget graph of `φ` with `m` universal
vertices, which take `m` colors of their own. -/
def toKColoring (m : ℕ) (φ : CNF ℕ) : Graph :=
  ((kColoringEdges m φ).flatMap fun e => [e.1, e.2], kColoringEdges m φ)

/-- Gadget vertices are labelled with tags `0`, `1` and `2`. -/
private theorem unpair_fst_lt_of_mem_coloringEdges {φ : CNF ℕ} {e : ℕ × ℕ}
    (he : e ∈ coloringEdges φ) : e.1.unpair.1 < 3 ∧ e.2.unpair.1 < 3 := by
  simp only [coloringEdges, clauseEdges, stageEdges, variableEdges, List.mem_append,
    List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with (he | ⟨x, -, he⟩) | ⟨⟨cl, i⟩, -, he | ⟨⟨l, j⟩, -, he⟩⟩
  · rcases he with rfl | rfl | rfl <;> simp [paletteVertex]
  · rcases he with rfl | rfl | rfl <;> simp [paletteVertex, literalVertex]
  · rcases he with rfl | rfl | rfl | rfl <;> simp [paletteVertex, gadgetVertex]
  · rcases he with rfl | rfl | rfl | rfl | rfl <;> simp [gadgetVertex, literalVertex]

private theorem mem_kColoringEdges {m : ℕ} {φ : CNF ℕ} {e : ℕ × ℕ} :
    e ∈ kColoringEdges m φ ↔ e ∈ coloringEdges φ ∨
      (∃ r < m, ∃ v ∈ (coloringEdges φ).flatMap (fun e => [e.1, e.2]),
        e = (universalVertex r, v)) ∨
      (∃ r < m, ∃ r' < r, e = (universalVertex r, universalVertex r')) := by
  simp only [kColoringEdges, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro (h | ⟨r, hr, ⟨v, hv, rfl⟩ | ⟨r', hr', rfl⟩⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨r, hr, v, hv, rfl⟩)
    · exact Or.inr (Or.inr ⟨r, hr, r', hr', rfl⟩)
  · rintro (h | ⟨r, hr, v, hv, rfl⟩ | ⟨r, hr, r', hr', rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, Or.inl ⟨v, hv, rfl⟩⟩
    · exact Or.inr ⟨r, hr, Or.inr ⟨r', hr', rfl⟩⟩

/-- The rank of `x` among the natural numbers outside `S`. -/
private theorem card_filter_notMem_lt {S : Finset ℕ} {n x : ℕ}
    (hS : S ⊆ Finset.range (n + 3)) (hcard : S.card = n) (hx : x ∉ S) (hxlt : x < n + 3) :
    ((Finset.range x).filter (· ∉ S)).card < 3 := by
  have htot := Finset.card_filter_add_card_filter_not (s := Finset.range (n + 3)) (· ∈ S)
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS, hcard, Finset.card_range] at htot
  have hsub : insert x ((Finset.range x).filter (· ∉ S)) ⊆
      (Finset.range (n + 3)).filter (· ∉ S) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range] at hy ⊢
    rcases hy with rfl | ⟨hy, hyS⟩
    · exact ⟨hxlt, hx⟩
    · exact ⟨by omega, hyS⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp)] at this
  omega

private theorem card_filter_notMem_strictMono {S : Finset ℕ} {x y : ℕ} (hx : x ∉ S)
    (hxy : x < y) :
    ((Finset.range x).filter (· ∉ S)).card < ((Finset.range y).filter (· ∉ S)).card := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset
    (Finset.filter_subset_filter _ (Finset.range_subset_range.2 hxy.le))).2 ⟨x, ?_, ?_⟩)
  · simp [hxy, hx]
  · simp

/-- **Correctness of the `(m + 3)`-coloring reduction.** A formula is satisfiable exactly when its
gadget graph with `m` universal vertices is `(m + 3)`-colorable. -/
theorem toKColoring_mem_iff (m : ℕ) (φ : CNF ℕ) :
    toKColoring m φ ∈ KColoring (m + 3) ↔ φ ∈ SAT := by
  rw [mem_KColoring_iff]
  have hadj_of : ∀ {e : ℕ × ℕ}, e ∈ kColoringEdges m φ → e.1 ≠ e.2 →
      (toKColoring m φ).toSimpleGraph.Adj e.1 e.2 := fun he hne => by
    simp only [toKColoring, Graph.toSimpleGraph_adj]
    exact ⟨hne, Or.inl he⟩
  have hU : ∀ {r v : ℕ}, v ∈ (coloringEdges φ).flatMap (fun e => [e.1, e.2]) →
      universalVertex r ≠ v := fun hv h => by
    obtain ⟨e, he, hv⟩ := List.mem_flatMap.1 hv
    have := unpair_fst_lt_of_mem_coloringEdges he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> simp [← h, universalVertex] at this
  constructor
  · rintro ⟨c, hlt, hadj⟩
    have hE : ∀ e ∈ kColoringEdges m φ, e.1 ≠ e.2 →
        c e.1 ≠ c e.2 ∧ c e.1 < m + 3 ∧ c e.2 < m + 3 := fun e he hne => by
      obtain ⟨h₁, h₂⟩ := mem_endpoints he
      exact ⟨hadj _ h₁ _ h₂ (hadj_of he hne), hlt _ h₁, hlt _ h₂⟩
    have hT : (paletteVertex 0, paletteVertex 1) ∈ coloringEdges φ := by simp [coloringEdges]
    have hTv : paletteVertex 0 ∈ (coloringEdges φ).flatMap (fun e => [e.1, e.2]) :=
      (mem_endpoints hT).1
    -- The universal vertices take `m` distinct colors.
    set S := (Finset.range m).image fun r => c (universalVertex r) with hSdef
    have hUU : ∀ r < m, ∀ r' < r, c (universalVertex r) ≠ c (universalVertex r') :=
      fun r hr r' hr' => (hE _ (mem_kColoringEdges.2 (Or.inr (Or.inr ⟨r, hr, r', hr', rfl⟩)))
        (by simp [universalVertex]; omega)).1
    have hUlt : ∀ r < m, c (universalVertex r) < m + 3 := fun r hr =>
      (hE _ (mem_kColoringEdges.2 (Or.inr (Or.inl ⟨r, hr, _, hTv, rfl⟩))) (hU hTv)).2.1
    have hcard : S.card = m := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro r hr r' hr' h
      simp only [Finset.coe_range, Set.mem_Iio] at hr hr'
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h' | h'
      · exact hUU r' hr' r h' h.symm
      · exact hUU r hr r' h' h
    have hSsub : S ⊆ Finset.range (m + 3) := by
      intro x hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hx
      exact Finset.mem_range.2 (hUlt r (Finset.mem_range.1 hr))
    -- Gadget vertices avoid the colors of the universal vertices.
    have hnot : ∀ {v}, v ∈ (coloringEdges φ).flatMap (fun e => [e.1, e.2]) → c v ∉ S :=
      fun hv hS => by
        obtain ⟨r, hr, hrv⟩ := Finset.mem_image.1 hS
        exact (hE _ (mem_kColoringEdges.2 (Or.inr (Or.inl ⟨r, Finset.mem_range.1 hr, _, hv,
          rfl⟩))) (hU hv)).1 hrv
    refine satisfiable_of_coloring (c := fun v => ((Finset.range (c v)).filter (· ∉ S)).card)
      fun e he => ?_
    obtain ⟨h₁, h₂⟩ := mem_endpoints he
    obtain ⟨hne, hlt₁, hlt₂⟩ := hE e (mem_kColoringEdges.2 (Or.inl he))
      (ne_of_mem_coloringEdges he)
    refine ⟨fun h => ?_, card_filter_notMem_lt hSsub hcard (hnot h₁) hlt₁,
      card_filter_notMem_lt hSsub hcard (hnot h₂) hlt₂⟩
    rcases Nat.lt_or_gt_of_ne hne with h' | h'
    · exact (card_filter_notMem_strictMono (hnot h₁) h').ne h
    · exact (card_filter_notMem_strictMono (hnot h₂) h').ne h.symm
  · rintro ⟨σ, hσ⟩
    let c : ℕ → ℕ := fun v => if v.unpair.1 = 3 then 3 + v.unpair.2 else gadgetColoring φ σ v
    have hcU : ∀ r, c (universalVertex r) = 3 + r := fun r => by simp [c, universalVertex]
    have hcG : ∀ {v}, v ∈ (coloringEdges φ).flatMap (fun e => [e.1, e.2]) →
        c v = gadgetColoring φ σ v := fun hv => by
      obtain ⟨e, he, hv⟩ := List.mem_flatMap.1 hv
      have := unpair_fst_lt_of_mem_coloringEdges he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · simp [c, Nat.ne_of_lt this.1]
      · simp [c, Nat.ne_of_lt this.2]
    have hEc : ∀ e ∈ kColoringEdges m φ, c e.1 ≠ c e.2 ∧ c e.1 < m + 3 ∧ c e.2 < m + 3 := by
      intro e he
      rcases mem_kColoringEdges.1 he with he | ⟨r, hr, v, hv, rfl⟩ | ⟨r, hr, r', hr', rfl⟩
      · obtain ⟨h₁, h₂⟩ := mem_endpoints he
        rw [hcG h₁, hcG h₂]
        have := gadgetColoring_lt (φ := φ) (σ := σ) e.1
        have := gadgetColoring_lt (φ := φ) (σ := σ) e.2
        exact ⟨gadgetColoring_ne hσ e he, by omega, by omega⟩
      · simp only [hcU, hcG hv]
        have := gadgetColoring_lt (φ := φ) (σ := σ) v
        omega
      · simp only [hcU]
        omega
    refine ⟨c, fun v hv => ?_, fun u _ v _ huv => ?_⟩
    · obtain ⟨e, he, hv⟩ := List.mem_flatMap.1 hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (hEc e he).2.1
      · exact (hEc e he).2.2
    · simp only [toKColoring, Graph.toSimpleGraph_adj] at huv
      rcases huv.2 with h | h
      · exact (hEc _ h).1
      · exact (hEc _ h).1.symm

/-- The reduction `toKColoring m` is computable in polynomial time for every fixed `m`. -/
@[fun_prop]
theorem computableInPolyTime_toKColoring (m : ℕ) :
    ComputableInPolyTime (toKColoring m) encCNF encGraph := by
  refine .of_tidy ?_
  have hG := computableInPolyTime_toThreeColoring.tidy
  have hU : ComputableTidilyInPolyTime (fun r => universalVertex r) encUnary encNat :=
    unary_to_binary.comp (show ComputableTidilyInPolyTime (fun r => Nat.pair 3 r) _ _ by
      fun_prop)
  have hrange : ComputableTidilyInPolyTime (fun _ : CNF ℕ => List.range m) encCNF
      (encList encUnary) := const _
  have hE : ComputableTidilyInPolyTime coloringEdges encCNF (encList (encPair encNat encNat)) :=
    (snd (encList encNat) (encList (encPair encNat encNat))).comp hG
  unfold toKColoring kColoringEdges
  fun_prop

end SAT

/-- `SAT` reduces to `ThreeColoring` in polynomial time via `SAT.toThreeColoring`. -/
theorem polyTimeReducible_SAT_ThreeColoring :
    PolyTimeReducible encCNF encGraph SAT ThreeColoring :=
  ⟨SAT.toThreeColoring, SAT.computableInPolyTime_toThreeColoring,
    fun φ => (SAT.toThreeColoring_mem_iff φ).symm⟩

/-- `ThreeSAT` reduces to `ThreeColoring` in polynomial time: a formula with a clause of more than
three literals is mapped to the gadget graph of the empty clause, which is not 3-colorable. -/
theorem polyTimeReducible_ThreeSAT_ThreeColoring :
    PolyTimeReducible encCNF encGraph ThreeSAT ThreeColoring := by
  refine ⟨fun φ => if φ.all (fun c => decide (c.length ≤ 3)) then SAT.toThreeColoring φ
    else SAT.toThreeColoring [[]], by fun_prop, fun φ => ?_⟩
  simp only [ThreeSAT, Set.mem_ofPred_eq]
  split_ifs with h
  · rw [SAT.toThreeColoring_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨fun h' => h'.2, fun h' => ⟨h, h'⟩⟩
  · rw [SAT.toThreeColoring_mem_iff, mem_SAT]
    simp only [List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨fun h' => (h h'.1).elim, fun ⟨σ, hσ⟩ => ?_⟩
    simp at hσ

/-- `ThreeColoring` is `NP`-hard. -/
theorem ThreeColoring_npHard : NPHard encGraph ThreeColoring :=
  CookLevin.SAT_npHard.trans polyTimeReducible_SAT_ThreeColoring

/-- **`ThreeColoring` is NP-complete** [Garey and Johnson][GareyJohnson1979]. -/
theorem ThreeColoring_npComplete : NPComplete encGraph ThreeColoring :=
  ⟨KColoring.mem_NP 3, ThreeColoring_npHard⟩

/-- For `k ≥ 3`, `SAT` reduces to `KColoring k` in polynomial time via `SAT.toKColoring (k - 3)`.
-/
theorem polyTimeReducible_SAT_KColoring {k : ℕ} (hk : 3 ≤ k) :
    PolyTimeReducible encCNF encGraph SAT (KColoring k) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  exact ⟨SAT.toKColoring m, (SAT.computableInPolyTime_toKColoring m),
    fun φ => (SAT.toKColoring_mem_iff m φ).symm⟩

/-- For `k ≥ 3`, `KColoring k` is `NP`-hard. -/
theorem KColoring_npHard {k : ℕ} (hk : 3 ≤ k) : NPHard encGraph (KColoring k) :=
  CookLevin.SAT_npHard.trans (polyTimeReducible_SAT_KColoring hk)

/-- **For `k ≥ 3`, `KColoring k` is NP-complete** [Garey and Johnson][GareyJohnson1979]. -/
theorem KColoring_npComplete {k : ℕ} (hk : 3 ≤ k) : NPComplete encGraph (KColoring k) :=
  ⟨KColoring.mem_NP k, KColoring_npHard hk⟩

end Cslib.Complexity
