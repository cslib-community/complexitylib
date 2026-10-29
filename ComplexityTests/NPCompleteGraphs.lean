/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.Coloring
import Complexity.Computability.Complexity.Problems.Hamiltonian.Directed
import Complexity.Computability.Complexity.Problems.Hamiltonian.Undirected
import Complexity.Computability.Complexity.Problems.TSP
import Complexity.Computability.Complexity.Problems.VertexCover
import Complexity.Tactic.PolyTime

/-!
# NP-complete graph problem tests

Concrete, boundary, and `fun_prop` checks for `VertexCover`, `KColoring`,
`ThreeColoring`, and the directed Hamiltonian path and cycle reductions, with the headline
`NP`-completeness results of all the graph problems. The Hamiltonian verifiers, the vertex-splitting
reductions and `TSP` are tested in `ComplexityTests/NPCompleteGraphs/`.
-/

namespace ComplexityTests.NPCompleteGraphs

open Cslib.Complexity Cslib.Logic.PL Turing.MultiTapeTM

/-! ### Headline complexity class results -/

example :
    (VertexCover ∈ NP (encPair encGraph encNat) ∧
        PolyTimeReducible encCNF (encPair encGraph encNat) SAT VertexCover) ∧
      (KColoring 2 ∈ NP encGraph ∧ KColoring 5 ∈ NP encGraph) ∧
      (ThreeColoring ∈ NP encGraph ∧
        PolyTimeReducible encCNF encGraph SAT ThreeColoring) ∧
      (KColoring 4 ∈ NP encGraph ∧
        PolyTimeReducible encCNF encGraph SAT (KColoring 4)) ∧
      (DirHamPath ∈ NP (encPair encGraph (encPair encNat encNat)) ∧
        PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) SAT DirHamPath) ∧
      (DirHamCycle ∈ NP encGraph ∧
        PolyTimeReducible encCNF encGraph SAT DirHamCycle) ∧
      (HamPath ∈ NP (encPair encGraph (encPair encNat encNat)) ∧
        PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) SAT HamPath) ∧
      (HamCycle ∈ NP encGraph ∧
        PolyTimeReducible encCNF encGraph SAT HamCycle) :=
  ⟨⟨VertexCover_npComplete.1, VertexCover_npComplete.2 encCNF SAT SAT.mem_NP⟩,
    ⟨KColoring.mem_NP 2, KColoring.mem_NP 5⟩,
    ⟨ThreeColoring_npComplete.1, ThreeColoring_npComplete.2 encCNF SAT SAT.mem_NP⟩,
    ⟨(KColoring_npComplete (by norm_num)).1,
      (KColoring_npComplete (by norm_num)).2 encCNF SAT SAT.mem_NP⟩,
    ⟨DirHamPath_npComplete.1, DirHamPath_npComplete.2 encCNF SAT SAT.mem_NP⟩,
    ⟨DirHamCycle_npComplete.1, DirHamCycle_npComplete.2 encCNF SAT SAT.mem_NP⟩,
    ⟨HamPath_npComplete.1, HamPath_npComplete.2 encCNF SAT SAT.mem_NP⟩,
    ⟨HamCycle_npComplete.1, HamCycle_npComplete.2 encCNF SAT SAT.mem_NP⟩⟩

example :
    PolyTimeReducible encCNF encGraph SAT ThreeColoring ∧
      PolyTimeReducible encCNF (encPair encGraph encNat) SAT VertexCover ∧
      PolyTimeReducible encCNF (encPair encGraph (encPair encNat encNat)) SAT DirHamPath :=
  ⟨ThreeSAT_npComplete.2 encCNF SAT SAT.mem_NP |>.trans polyTimeReducible_ThreeSAT_ThreeColoring,
    polyTimeReducible_SAT_IndependentSet.trans polyTimeReducible_IndependentSet_VertexCover,
    ThreeSAT_npComplete.2 encCNF SAT SAT.mem_NP |>.trans polyTimeReducible_ThreeSAT_DirHamPath⟩

/-! ### Compositional `fun_prop` synthesis -/

example :
    ComputableInPolyTime IndependentSet.toVertexCover (encPair encGraph encNat)
        (encPair encGraph encNat) ∧
      ComputableInPolyTime VertexCover.verifier
        (encPair (encPair encGraph encNat) encBits) encBool ∧
      ComputableInPolyTime (KColoring.verifier 3) (encPair encGraph encBits) encBool ∧
      ComputableInPolyTime SAT.toThreeColoring encCNF encGraph ∧
      ComputableInPolyTime (SAT.toKColoring 2) encCNF encGraph ∧
      ComputableInPolyTime SAT.toDirHamPath encCNF
        (encPair encGraph (encPair encNat encNat)) ∧
      ComputableInPolyTime SAT.toDirHamCycle encCNF encGraph ∧
      ComputableInPolyTime
        (fun φ => IndependentSet.toVertexCover (SAT.toIndependentSet φ))
        encCNF (encPair encGraph encNat) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> fun_prop

/-! ### `VertexCover` concrete and boundary tests -/

private def triangle : Graph := ([0, 1, 2], [(0, 1), (1, 2), (2, 0)])

-- A triangle has vertex covers with two vertices but none with one.
example :
    VertexCover.verifier ((triangle, 2), [true, true, false]) = true ∧
      VertexCover.verifier ((triangle, 2), [false, true, true]) = true ∧
      VertexCover.verifier ((triangle, 1), [true, false, false]) = false ∧
      VertexCover.verifier ((triangle, 2), [true, false, false]) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

example : (triangle, 2) ∈ VertexCover := by
  rw [mem_VertexCover_iff]
  refine ⟨{0, 1}, by decide, fun u hu v hv huv => ?_, rfl⟩
  simp only [triangle, List.mem_cons, List.not_mem_nil, or_false] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first | exact (huv.ne rfl).elim | simp

example : (triangle, 1) ∉ VertexCover := by
  rw [mem_VertexCover_iff]
  rintro ⟨S, -, hS, hcard⟩
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.1 hcard
  have h₀₁ := hS 0 (by simp [triangle]) 1 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hS 1 (by simp [triangle]) 2 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₀ := hS 2 (by simp [triangle]) 0 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  simp only [Finset.mem_singleton] at h₀₁ h₁₂ h₂₀
  omega

-- Covers have exactly `k` vertices: the triangle has one of all three vertices, but none of four.
example : (triangle, 3) ∈ VertexCover ∧ (triangle, 4) ∉ VertexCover := by
  refine ⟨?_, fun h => absurd (mem_VertexCover_iff_exists_card_le.1 h).1 (by decide)⟩
  rw [mem_VertexCover_iff]
  refine ⟨{0, 1, 2}, by decide, fun u hu _ _ _ => Or.inl ?_, rfl⟩
  simpa [triangle] using hu

-- Empty graph: `k = 0` is accepted and `k = 1` is rejected.
example :
    VertexCover.verifier ((([], []), 0), []) = true ∧
      VertexCover.verifier ((([], []), 1), [true]) = false ∧
      ((([], []) : Graph), 0) ∈ VertexCover ∧
      ((([], []) : Graph), 1) ∉ VertexCover :=
  ⟨rfl, rfl, mem_VertexCover_iff.2 ⟨∅, by simp, by simp, rfl⟩, fun h =>
    absurd (mem_VertexCover_iff_exists_card_le.1 h).1 (by decide)⟩

-- Duplicate vertices count once; edges with an undeclared endpoint and self-loops are ignored;
-- oversized binary targets are rejected without unary expansion; and `toVertexCover` complements
-- the target within distinct declared vertices.
example :
    VertexCover.verifier ((([0, 0, 1], [(0, 1)]), 2), [true, true, false]) = false ∧
      VertexCover.verifier ((([0, 0, 1], [(0, 1)]), 1), [true, false, false]) = true ∧
      VertexCover.verifier
        ((([10, 20], [(10, 99), (99, 20), (10, 10)]), 0), [false, false]) = true ∧
      VertexCover.verifier ((([0, 1], [(0, 1)]), 2 ^ 100), [true, true]) = false ∧
      IndependentSet.toVertexCover (triangle, 1) = (triangle, 2) ∧
      IndependentSet.toVertexCover (([0, 0, 1], []), 2) = (([0, 0, 1], []), 0) ∧
      IndependentSet.toVertexCover (triangle, 4) = (triangle, 4) ∧
      IndependentSet.toVertexCover (([], []), 0) = (([], []), 0) :=
  ⟨rfl, rfl, rfl, by decide, by decide, by decide, by decide, by decide⟩

/-! ### `KColoring` and `ThreeColoring` concrete and boundary tests -/

-- A certificate from a coloring `c`: block `i` of `k` bits has `c` of vertex `i` set bits.
private def certificate (k : ℕ) (G : Graph) (c : ℕ → ℕ) : List Bool :=
  (List.range (k * G.1.length)).map fun j => decide (j % k < c (G.1.getD (j / k) 0))

-- Colors are counts of set bits in each vertex's block of `k` bits, and the triangle is
-- 3-colorable but not 2-colorable.
example :
    KColoring.colorOf 3 [5, 7] [true, false, false, true, true, false] 7 = 2 ∧
      KColoring.colorOf 3 [5, 7] [true, false, false, true, true, false] 5 = 1 ∧
      KColoring.verifier 3 (triangle, certificate 3 triangle id) = true ∧
      KColoring.verifier 2 (triangle, [false, false, true, false, true, true]) = false :=
  ⟨rfl, rfl, rfl, rfl⟩

example : triangle ∈ ThreeColoring := by
  rw [mem_KColoring_iff]
  refine ⟨id, by decide, fun u _ v _ huv => huv.ne⟩

example : triangle ∉ KColoring 2 := by
  rw [mem_KColoring_iff]
  rintro ⟨c, hc, hadj⟩
  have h₀ := hc 0 (by simp [triangle])
  have h₁ := hc 1 (by simp [triangle])
  have h₂ := hc 2 (by simp [triangle])
  have h₀₁ := hadj 0 (by simp [triangle]) 1 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hadj 1 (by simp [triangle]) 2 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₀ := hadj 2 (by simp [triangle]) 0 (by simp [triangle])
    ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  omega

-- The complete graph on four vertices is not 3-colorable.
private def k4 : Graph := ([0, 1, 2, 3], [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)])

example : k4 ∉ ThreeColoring := by
  rw [mem_KColoring_iff]
  rintro ⟨c, hc, hadj⟩
  have h₀ := hc 0 (by simp [k4])
  have h₁ := hc 1 (by simp [k4])
  have h₂ := hc 2 (by simp [k4])
  have h₃ := hc 3 (by simp [k4])
  have h₀₁ := hadj 0 (by simp [k4]) 1 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₀₂ := hadj 0 (by simp [k4]) 2 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₀₃ := hadj 0 (by simp [k4]) 3 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₂ := hadj 1 (by simp [k4]) 2 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₁₃ := hadj 1 (by simp [k4]) 3 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  have h₂₃ := hadj 2 (by simp [k4]) 3 (by simp [k4]) ((Graph.adjBool_eq_true_iff _ _ _).1 rfl)
  omega

example : KColoring.verifier 4 (k4, certificate 4 k4 id) = true := rfl

-- A block with all bits set encodes the out-of-range color `k`.
example : KColoring.verifier 3 (([0], []), [true, true, true]) = false := rfl

-- With `k = 0`, exactly the graphs without declared vertices are colorable.
example : KColoring.verifier 0 (([], [(0, 1)]), []) = true := rfl
example : KColoring.verifier 0 (([0], []), []) = false := rfl
example : (([], [(0, 1)]) : Graph) ∈ KColoring 0 :=
  mem_KColoring_iff.2 ⟨fun _ => 0, by simp, by simp⟩
example : (([0], []) : Graph) ∉ KColoring 0 := by
  rw [mem_KColoring_iff]
  rintro ⟨c, hc, -⟩
  exact Nat.not_lt_zero _ (hc 0 (by simp))

-- Duplicate vertices share the block of their first occurrence; undeclared edges are ignored.
example : KColoring.verifier 2
    (([0, 1, 0], [(0, 1), (1, 7), (7, 0)]), [false, false, true, false]) = true := rfl

/-! ### The 3-coloring gadget -/

-- The gadget graph of the empty formula is the palette triangle.
example : (SAT.toThreeColoring []).2 = [(0, 1), (1, 4), (4, 0)] := by decide
example : SAT.toThreeColoring [] ∈ ThreeColoring :=
  (SAT.toThreeColoring_mem_iff _).2 ⟨fun _ => true, rfl⟩

-- The stage `0` output of an empty clause is adjacent to all three palette vertices.
example : (SAT.toThreeColoring [[]]).2 =
    [(0, 1), (1, 4), (4, 0), (258, 0), (258, 4), (258, 1), (258, 4)] := by decide
example : SAT.toThreeColoring [[]] ∉ ThreeColoring := by
  rw [SAT.toThreeColoring_mem_iff]
  rintro ⟨σ, hσ⟩
  simp at hσ

-- A satisfiable formula: a coloring certificate read off a satisfying assignment.
private def unitFormula : CNF ℕ := [[(0, true)]]

private def unitColoring (v : ℕ) : ℕ :=
  if v = SAT.paletteVertex 1 ∨ v = SAT.literalVertex unitFormula (0, false) ∨
      v = SAT.gadgetVertex 0 0 2 ∨ v = SAT.gadgetVertex 0 1 1 then 1
  else if v = SAT.paletteVertex 2 ∨ v = SAT.gadgetVertex 0 1 0 then 2
  else 0

example : KColoring.verifier 3 (SAT.toThreeColoring unitFormula,
    certificate 3 (SAT.toThreeColoring unitFormula) unitColoring) = true := by decide

-- Complementary unit clauses: the gadget graph is not 3-colorable.
example : SAT.toThreeColoring [[(0, true)], [(0, false)]] ∉ ThreeColoring := by
  rw [SAT.toThreeColoring_mem_iff]
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [h] at hσ

-- A clause of width four is handled by the chain of OR gadgets.
example : SAT.toThreeColoring [[(0, false), (1, false), (2, false), (3, true)]] ∈ ThreeColoring :=
  (SAT.toThreeColoring_mem_iff _).2 ⟨fun _ => true, rfl⟩

-- Universal vertices for more colors: four colors for the gadget graph with one universal vertex.
example : (SAT.toKColoring 1 []).2 =
    [(0, 1), (1, 4), (4, 0), (12, 0), (12, 1), (12, 1), (12, 4), (12, 4), (12, 0)] := by
  decide
example : SAT.toKColoring 1 [[(0, true)]] ∈ KColoring 4 :=
  (SAT.toKColoring_mem_iff 1 _).2 ⟨fun _ => true, rfl⟩
example : SAT.toKColoring 2 [[(0, true)], [(0, false)]] ∉ KColoring 5 := by
  rw [SAT.toKColoring_mem_iff]
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [h] at hσ

/-! ### Directed Hamiltonian paths and cycles -/

-- A directed path through all vertices, and the boundary conventions for cycles: a single
-- vertex needs a self-loop.
example : (([0, 1, 2], [(0, 1), (1, 2)]), 0, 2) ∈ DirHamPath :=
  ⟨[0, 1, 2], by decide, fun _ => Iff.rfl, rfl, rfl, by decide⟩

example : ([0], [(0, 0)]) ∈ DirHamCycle :=
  ⟨[0], by decide, fun _ => Iff.rfl, by decide, (Cycle.chain_singleton _ _).2 (by decide)⟩

example : ([0], []) ∉ DirHamCycle := by
  rintro ⟨p, hnd, hcov, hne, hch⟩
  obtain ⟨a, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  have ha : a = 0 := by simpa using (hcov a).1 List.mem_cons_self
  obtain rfl : rest = [] := List.eq_nil_iff_forall_not_mem.2 fun b hb => by
    have hb0 : b = 0 := by simpa using (hcov b).1 (List.mem_cons_of_mem _ hb)
    exact (List.nodup_cons.1 hnd).1 (by rw [ha, ← hb0]; exact hb)
  simp at hch

-- Closing a path into a cycle needs an arc back to a start vertex that no arc enters.
example : ([0, 1, 2], [(2, 0), (0, 1), (1, 2)]) ∈ DirHamCycle :=
  (Graph.mem_DirHamCycle_cons_iff (G := ([0, 1, 2], [(0, 1), (1, 2)])) (by decide)
    (fun u => by simp)).2 ⟨[0, 1, 2], by decide, fun _ => Iff.rfl, rfl, rfl, by decide⟩

-- The diamond graph of the empty formula is the single top node, and that of a unit clause has
-- one diamond with a row of six nodes and one clause node.
example : SAT.toDirHamPath [] = (([0], []), 0, 0) := by decide
example : SAT.toDirHamPath [] ∈ DirHamPath := (SAT.toDirHamPath_mem_iff _).2 ⟨fun _ => true, rfl⟩

example : SAT.toDirHamPath [[(0, true)]] =
    (([0, 1, 2, 3, 17, 82, 257, 626, 6],
      [(0, 2), (0, 626), (2, 1), (626, 1), (2, 3), (3, 2), (3, 17), (17, 3), (17, 82), (82, 17),
        (82, 257), (257, 82), (257, 626), (626, 257), (17, 6), (6, 82)]), 0, 1) := by
  decide

-- The rightward traversal with the detour through the clause node.
example : (SAT.toDirHamPath [[(0, true)]]).1.IsDirHamPath 0 1
    [0, 2, 3, 17, 6, 82, 257, 626, 1] :=
  ⟨by decide, fun _ => (show [0, 2, 3, 17, 6, 82, 257, 626, 1].Perm
    [0, 1, 2, 3, 17, 82, 257, 626, 6] by decide).mem_iff, rfl, rfl, by decide⟩

-- The empty clause has no detour into its node, and complementary unit clauses are unsatisfiable.
example : SAT.toDirHamPath [[]] ∉ DirHamPath := by
  rw [SAT.toDirHamPath_mem_iff]
  rintro ⟨σ, hσ⟩
  simp at hσ

example : SAT.toDirHamCycle [[(0, true)]] ∈ DirHamCycle :=
  (SAT.toDirHamCycle_mem_iff _).2 ⟨fun _ => true, rfl⟩

example : SAT.toDirHamCycle [[(0, true)], [(0, false)]] ∉ DirHamCycle := by
  rw [SAT.toDirHamCycle_mem_iff]
  rintro ⟨σ, hσ⟩
  cases h : σ 0 <;> simp [h] at hσ

-- Clauses wider than three literals and repeated variables are handled.
example : SAT.toDirHamPath [[(0, false), (1, false), (0, true), (2, false)], [(1, true)]] ∈
    DirHamPath :=
  (SAT.toDirHamPath_mem_iff _).2 ⟨fun _ => true, rfl⟩

end ComplexityTests.NPCompleteGraphs
