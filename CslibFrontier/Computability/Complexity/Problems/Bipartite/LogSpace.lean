/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Bipartite
public import CslibFrontier.Computability.Complexity.Classes.LogSpace.USTCON
public import CslibFrontier.Computability.Complexity.Problems.STCON.Header
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Boolean

/-!
# Bipartiteness is in logarithmic space

The copies of the double cover (`Cslib.Complexity.Bipartite.oddCycleInstance`) are written in
logarithmic space by a counter program with output (`Cslib.Complexity.Bipartite.writer`). It
counts the unary header `1^n 0` of the encoded graph, writes the header of the instance of
undirected connectivity, and writes its matrix entry by entry. An entry within a copy reads the
one entry of the input matrix that it depends on; every other entry is arithmetic in `n` and the
two vertex numbers (`Cslib.Complexity.Bipartite.computableInLogSpace_oddCycleInstance`). The
registers hold `n` and two vertex numbers, at most `2 n² + 2`.

This is a logarithmic-space many-one reduction from non-bipartiteness to undirected connectivity
(`Cslib.Complexity.Bipartite.compl_logSpaceReducible_USTCON`). With Reingold's theorem
`Cslib.Complexity.USTCON_mem_L` and the closure of `L` under complement, bipartiteness is in `L`
(`Cslib.Complexity.Bipartite.mem_L`) [Goldreich, Exercise 5.16][Goldreich2008]. As for every
problem in `L`, the decider is only required to be correct on encodings of instances. The space
measure is that of `L`: the work-tape cells visited.

Conversely, undirected connectivity reduces to non-bipartiteness
(`Cslib.Complexity.Bipartite.USTCON_logSpaceReducible_compl`). Under logarithmic-space many-one
reductions this is immediate from `USTCON_mem_L`: the reduction decides its input and outputs a
triangle or the graph without vertices, as `Cslib.Complexity.USTCON_logSpaceHard_L` does. The
reduction of Goldreich's guideline, which adds edges to the double cover, is not formalized.
Together, bipartiteness and the complement of undirected connectivity reduce to each other
(`Cslib.Complexity.Bipartite.logSpaceReducible_compl_USTCON`,
`Cslib.Complexity.Bipartite.compl_USTCON_logSpaceReducible`).

## Main definitions

* `Cslib.Complexity.Bipartite.writer`: the counter program writing the copies of the double
  cover.

## Main results

* `Cslib.Complexity.Bipartite.computableInLogSpace_oddCycleInstance`: the copies of the double
  cover are computed in logarithmic space.
* `Cslib.Complexity.Bipartite.compl_logSpaceReducible_USTCON`,
  `Cslib.Complexity.Bipartite.USTCON_logSpaceReducible_compl`: non-bipartiteness and undirected
  connectivity reduce to each other.
* `Cslib.Complexity.Bipartite.logSpaceReducible_compl_USTCON`,
  `Cslib.Complexity.Bipartite.compl_USTCON_logSpaceReducible`: the same for bipartiteness and
  undirected non-connectivity.
* `Cslib.Complexity.Bipartite.mem_L`: bipartiteness is in `L`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*][Goldreich2008]
-/

public section

namespace Cslib.Complexity

namespace Bipartite

/-! ### The writer -/

section Writer

open _root_.Turing _root_.Turing.CounterProgram _root_.Turing.CounterProgram.Instr
  _root_.Turing.CounterProgram.Expr _root_.Turing.MultiTapeTM

/-- The number of vertices, from `n` in register `0`. -/
def numVerticesExpr : Expr := add (mul (const 2) (mul (reg 0) (reg 0))) (const 2)

/-- The copy of the vertex in a register. -/
def copyExpr (i : ℕ) : Expr := div (sub (reg i) (const 2)) (mul (const 2) (reg 0))

/-- The vertex of the graph that the vertex in a register stands for. -/
def vertExpr (i : ℕ) : Expr := div (mod (sub (reg i) (const 2)) (mul (const 2) (reg 0))) (const 2)

/-- The side of the vertex in a register. -/
def sideExpr (i : ℕ) : Expr := mod (sub (reg i) (const 2)) (const 2)

/-- The row `1` and the column `2` lie in one copy, on different sides. -/
def withinExpr : Expr :=
  andB (ltB (const 1) (reg 1)) (andB (ltB (const 1) (reg 2))
    (andB (eqB (copyExpr 1) (copyExpr 2)) (notB (eqB (sideExpr 1) (sideExpr 2)))))

/-- The position of the input entry that an entry within a copy reads. -/
def positionExpr : Expr := add (add (reg 0) (const 1)) (add (mul (vertExpr 1) (reg 0)) (vertExpr 2))

/-- The entries at the source and the target. -/
def endpointExpr : Expr :=
  orB (andB (ltB (reg 1) (const 2)) (andB (ltB (const 1) (reg 2))
      (andB (eqB (vertExpr 2) (copyExpr 2)) (eqB (sideExpr 2) (reg 1)))))
    (andB (ltB (const 1) (reg 1)) (andB (ltB (reg 2) (const 2))
      (andB (eqB (vertExpr 1) (copyExpr 1)) (eqB (sideExpr 1) (reg 2)))))

/-- **The writer** of the copies of the double cover, on the encoded graph. Register `0` receives
`n`, register `1` counts the unary header and then runs over the rows, register `2` over the
columns. Labels `0` and `1` count the header of the input; the loop at label `2` and labels `6`
to `9` write the header `1^N 0 0 1 0` of the instance, with source `0` and target `1`; the nested
loops at labels `10` and `13` write the matrix, the entry at labels `16` to `20`; label `21`
halts. -/
def writer : CounterProgram where
  code := List.flatten [
    [read (reg 0) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0],
    forCode 2 1 numVerticesExpr 5 6,
    [emit true 4, emit false 7, emit false 8, emit true 9, emit false 10],
    forCode 10 1 numVerticesExpr 13 21, forCode 13 2 numVerticesExpr 16 12,
    [lt (const 0) withinExpr 17 18,
     read positionExpr 19 20 20,
     lt (const 0) endpointExpr 19 20,
     emit true 15,
     emit false 15,
     halt []]]
  registers := 3

variable (G : UGraphInstance) {B : ℕ}

private theorem bounded3 {a₀ a₁ a₂ : ℕ} (h₀ : a₀ ≤ B) (h₁ : a₁ ≤ B) (h₂ : a₂ ≤ B) :
    ∀ x ∈ [a₀, a₁, a₂], x ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

private theorem eval_numVerticesExpr (r c : ℕ) :
    numVerticesExpr.eval [G.n, r, c] = numVertices G.n := by
  simp [numVerticesExpr, numVertices, Nat.mul_assoc]

private theorem eval_copyExpr_one (r c : ℕ) : (copyExpr 1).eval [G.n, r, c] = copy G.n r := by
  simp [copyExpr, copy]

private theorem eval_copyExpr_two (r c : ℕ) : (copyExpr 2).eval [G.n, r, c] = copy G.n c := by
  simp [copyExpr, copy]

private theorem eval_vertExpr_one (r c : ℕ) : (vertExpr 1).eval [G.n, r, c] = vert G.n r := by
  simp [vertExpr, vert]

private theorem eval_vertExpr_two (r c : ℕ) : (vertExpr 2).eval [G.n, r, c] = vert G.n c := by
  simp [vertExpr, vert]

private theorem eval_sideExpr_one (r c : ℕ) : (sideExpr 1).eval [G.n, r, c] = side r := by
  simp [sideExpr, side]

private theorem eval_sideExpr_two (r c : ℕ) : (sideExpr 2).eval [G.n, r, c] = side c := by
  simp [sideExpr, side]

private theorem eval_withinExpr (r c : ℕ) :
    withinExpr.eval [G.n, r, c] =
      (decide (2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c ∧ side r ≠ side c)).toNat := by
  rw [withinExpr, eval_andB eval_ltB (eval_andB eval_ltB (eval_andB eval_eqB
    (eval_notB eval_eqB)))]
  simp only [eval_const, eval_reg, List.getD_cons_zero, List.getD_cons_succ, eval_copyExpr_one,
    eval_copyExpr_two, eval_sideExpr_one, eval_sideExpr_two]
  congr 1

private theorem eval_endpointExpr (r c : ℕ) :
    endpointExpr.eval [G.n, r, c] =
      (decide (r < 2 ∧ 2 ≤ c ∧ vert G.n c = copy G.n c ∧ side c = r) ||
        decide (2 ≤ r ∧ c < 2 ∧ vert G.n r = copy G.n r ∧ side r = c)).toNat := by
  rw [endpointExpr, eval_orB (eval_andB eval_ltB (eval_andB eval_ltB (eval_andB eval_eqB
    eval_eqB))) (eval_andB eval_ltB (eval_andB eval_ltB (eval_andB eval_eqB eval_eqB)))]
  simp only [eval_const, eval_reg, List.getD_cons_zero, List.getD_cons_succ, eval_copyExpr_one,
    eval_copyExpr_two, eval_vertExpr_one, eval_vertExpr_two, eval_sideExpr_one,
    eval_sideExpr_two]
  congr 1

/-- Writing the entry `(r, c)` of the matrix. -/
private theorem reachesOut_entry (hB : numVertices G.n ≤ B) {r c : ℕ}
    (hr : r < numVertices G.n) (hc : c < numVertices G.n) :
    writer.ReachesOut G.encode (writer.Active B) (16, [G.n, r, c]) (15, [G.n, r, c])
      [entry G r c] := by
  have hb : ∀ z ∈ [G.n, r, c], z ≤ B :=
    bounded3 ((le_numVertices G.n).trans hB) (by omega) (by omega)
  have hemit : ∀ (b : Bool) (l : ℕ),
      writer.instr l = (if b then emit true 15 else emit false 15) →
      writer.ReachesOut G.encode (writer.Active B) (l, [G.n, r, c]) (15, [G.n, r, c]) [b] := by
    rintro (_ | _) l hl
    · exact ReachesOut.emit hl hb (ReachesOut.refl _)
    · exact ReachesOut.emit hl hb (ReachesOut.refl _)
  refine ReachesOut.lt (show writer.instr 16 = _ from rfl) hb ?_
  rw [eval_const, eval_withinExpr]
  by_cases hw : 2 ≤ r ∧ 2 ≤ c ∧ copy G.n r = copy G.n c ∧ side r ≠ side c
  · -- an entry within a copy reads the input
    obtain ⟨-, hvr, -, -⟩ := eq_copyVertex hw.1 hr
    obtain ⟨-, hvc, -, -⟩ := eq_copyVertex hw.2.1 hc
    simp only [hw, ne_eq, not_false_eq_true, and_self, decide_true, Bool.toNat_true,
      ↓reduceIte, zero_lt_one]
    refine ReachesOut.read (show writer.instr 17 = _ from rfl) hb ?_
    have hpos : positionExpr.eval [G.n, r, c] = G.n + 1 + (vert G.n r * G.n + vert G.n c) := by
      simp only [positionExpr, eval_add, eval_mul, eval_reg, eval_const, List.getD_cons_zero,
        eval_vertExpr_one, eval_vertExpr_two]
    have hentry : entry G r c = G.adj ⟨vert G.n r, hvr⟩ ⟨vert G.n c, hvc⟩ := by
      rw [entry, ite_eq_left hw, UGraphInstance.adjN, dite_eq_left ⟨hvr, hvc⟩]
    have hm : G.toDigraph.encode[G.n + 1 + (vert G.n r * G.n + vert G.n c)]? =
        some (G.adj ⟨vert G.n r, hvr⟩ ⟨vert G.n c, hvc⟩) :=
      G.toDigraph.getElem?_encode_matrix hvr hvc
    rw [hpos, UGraphInstance.encode, hm, hentry]
    cases G.adj ⟨vert G.n r, hvr⟩ ⟨vert G.n c, hvc⟩
    · exact hemit false 20 rfl
    · exact hemit true 19 rfl
  · -- every other entry is arithmetic
    simp only [hw, decide_false, Bool.toNat_false, lt_irrefl, ↓reduceIte]
    refine ReachesOut.lt (show writer.instr 18 = _ from rfl) hb ?_
    rw [eval_const, eval_endpointExpr]
    have hentry : entry G r c =
        (decide (r < 2 ∧ 2 ≤ c ∧ vert G.n c = copy G.n c ∧ side c = r) ||
          decide (2 ≤ r ∧ c < 2 ∧ vert G.n r = copy G.n r ∧ side r = c)) := by
      rw [entry, ite_eq_right hw]
    rw [hentry]
    cases (decide (r < 2 ∧ 2 ≤ c ∧ vert G.n c = copy G.n c ∧ side c = r) ||
      decide (2 ≤ r ∧ c < 2 ∧ vert G.n r = copy G.n r ∧ side r = c))
    · exact hemit false 20 rfl
    · exact hemit true 19 rfl

/-- **The matrix row by row**, by the nested loops at labels `10` and `13`. -/
private theorem reachesOut_rows (hB : numVertices G.n ≤ B) {i₀ : ℕ} (hi₀ : i₀ ≤ B) :
    ∃ regs, writer.ReachesOut G.encode (writer.Active B) (10, [G.n, i₀, 0]) (21, regs)
      ((List.range (numVertices G.n)).flatMap fun r =>
        (List.range (numVertices G.n)).map (entry G r)) ∧ ∀ x ∈ regs, x ≤ B := by
  have hn : G.n ≤ B := (le_numVertices G.n).trans hB
  have hreg : ∀ {r c : ℕ}, r ≤ numVertices G.n → c ≤ numVertices G.n →
      ∀ z ∈ [G.n, r, c], z ≤ B := fun hr hc => bounded3 hn (hr.trans hB) (hc.trans hB)
  have hcode₁ : writer.CodeAt 10 (forCode 10 1 numVerticesExpr 13 21) :=
    codeAt_of_prefix ⟨_, rfl⟩
  have hcode₂ : writer.CodeAt 13 (forCode 13 2 numVerticesExpr 16 12) :=
    codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨regs, hreach, x, rfl, -, hx⟩ := reachesOut_forCode (w := G.encode)
    (N := numVertices G.n) (o := fun r => (List.range (numVertices G.n)).map (entry G r)) hcode₁
    (fun r regs => ∃ x, regs = [G.n, r, x] ∧ r ≤ numVertices G.n ∧ x ≤ numVertices G.n) hB
    (by
      rintro r regs ⟨x, rfl, hr, hx⟩
      exact ⟨rfl, eval_numVerticesExpr G r x, by simp, hreg hr hx⟩)
    (by
      rintro r hr regs ⟨x, rfl, -, hx⟩
      obtain ⟨regs', hreach, rfl, -⟩ := reachesOut_forCode (w := G.encode)
        (N := numVertices G.n) (o := fun c => [entry G r c]) hcode₂
        (fun c regs => regs = [G.n, r, c] ∧ c ≤ numVertices G.n) hB
        (by
          rintro c regs ⟨rfl, hc⟩
          exact ⟨rfl, eval_numVerticesExpr G r c, by simp, hreg hr.le hc⟩)
        (by
          rintro c hc regs ⟨rfl, -⟩
          exact ⟨_, reachesOut_entry G hB hr hc, rfl, hreg hr.le hc.le, by simp, by omega⟩)
        [G.n, r, x] (hreg hr.le hx) ⟨by simp, by omega⟩
      refine ⟨_, ?_, rfl, hreg hr.le le_rfl, numVertices G.n, by simp, by omega, le_rfl⟩
      rwa [← List.map_eq_flatMap] at hreach)
    [G.n, i₀, 0] (bounded3 hn hi₀ (Nat.zero_le _)) ⟨0, by simp, by omega, by omega⟩
  exact ⟨_, hreach, hreg le_rfl hx⟩

/-- **The copies of the double cover are computed in logarithmic space** from the encoded
graph. -/
theorem computableInLogSpace_oddCycleInstance :
    ComputableInLogSpace oddCycleInstance encUGraph encUSTCON := by
  refine writer.computableInLogSpace_of_reachesOut 2 fun G => ?_
  simp only [encUGraph_apply]
  have hlen : G.encode.length = G.n + 1 + G.n * G.n := G.toDigraph.length_encode
  set B := (G.encode.length + 1) ^ 2
  have hB : numVertices G.n ≤ B := by
    simp only [B, numVertices, hlen]
    nlinarith
  have hn : G.n ≤ B := (le_numVertices G.n).trans hB
  have hreg : ∀ {u : ℕ}, u ≤ numVertices G.n → ∀ z ∈ [G.n, u, 0], z ≤ B :=
    fun hu => bounded3 hn (hu.trans hB) (Nat.zero_le _)
  -- the header of the input
  have hcount := reachesOut_count (P := writer) (w := G.encode) (n := G.n) (fun j => [j, 0, 0])
    (u := 0)
    (show writer.instr 0 = _ from rfl) (show writer.instr 1 = _ from rfl) (fun _ _ => by simp)
    (fun j hj => bounded3 (hj.trans hn) (Nat.zero_le _) (Nat.zero_le _))
    (fun j hj => by
      rw [eval_reg, List.getD_cons_zero, UGraphInstance.encode,
        G.toDigraph.getElem?_encode_n hj.le]
      simp [UGraphInstance.toDigraph, hj])
    (by
      have h := G.toDigraph.getElem?_encode_n (i := G.toDigraph.n) le_rfl
      rw [eval_reg, List.getD_cons_zero, UGraphInstance.encode]
      simp only [UGraphInstance.toDigraph] at h ⊢
      simp [h]) 0 (Nat.zero_le _)
  -- the unary header `1^N` of the output
  have hcode : writer.CodeAt 2 (forCode 2 1 numVerticesExpr 5 6) := codeAt_of_prefix ⟨_, rfl⟩
  obtain ⟨regs₁, hones, rfl, -⟩ := reachesOut_forCode (w := G.encode) (N := numVertices G.n)
    (o := fun _ => [true]) hcode
    (fun u regs => regs = [G.n, u, 0] ∧ u ≤ numVertices G.n) hB
    (by
      rintro u regs ⟨rfl, hu⟩
      exact ⟨rfl, eval_numVerticesExpr G u 0, by simp, hreg hu⟩)
    (by
      rintro u hu regs ⟨rfl, -⟩
      exact ⟨_, ReachesOut.emit (show writer.instr 5 = _ from rfl) (hreg hu.le)
        (ReachesOut.refl _), rfl, hreg hu.le, by simp, by omega⟩)
    [G.n, 0, 0] (hreg (Nat.zero_le _)) ⟨by simp, by omega⟩
  rw [List.flatMap_def, List.map_const', List.length_range,
    List.flatten_replicate_singleton] at hones
  obtain ⟨regs, hrows, hregs⟩ := reachesOut_rows G hB (i₀ := numVertices G.n) hB
  have hr := hreg le_rfl
  have hchain := hcount.trans (hones.trans
    (ReachesOut.emit (show writer.instr 6 = _ from rfl) hr
      (ReachesOut.emit (show writer.instr 7 = _ from rfl) hr
        (ReachesOut.emit (show writer.instr 8 = _ from rfl) hr
          (ReachesOut.emit (show writer.instr 9 = _ from rfl) hr hrows)))))
  refine ⟨(21, regs), _, [], hchain, rfl, ?_, hregs⟩
  rw [encUSTCON, Function.Embedding.coeFn_mk, USTCONInstance.encode,
    USTCONInstance.toSTCONInstance, STCONInstance.encode,
    STCONInstance.matrix_eq_flatMap _ (entry G) (fun _ _ => rfl)]
  simp [oddCycleInstance]

end Writer

/-! ### Reductions -/

/-- **Non-bipartiteness reduces to undirected connectivity in logarithmic space**, by the copies
of the double cover. -/
theorem compl_logSpaceReducible_USTCON :
    LogSpaceReducible encUGraph encUSTCON Bipartiteᶜ USTCON :=
  ⟨oddCycleInstance, computableInLogSpace_oddCycleInstance,
    fun G => (oddCycleInstance_mem_iff G).symm⟩

/-- **Bipartiteness reduces to undirected non-connectivity in logarithmic space.** -/
theorem logSpaceReducible_compl_USTCON :
    LogSpaceReducible encUGraph encUSTCON Bipartite USTCONᶜ := by
  simpa only [compl_compl] using compl_logSpaceReducible_USTCON.compl

/-- **Bipartiteness is in `L`** [Goldreich, Exercise 5.16][Goldreich2008]: it reduces to the
complement of undirected connectivity, which is in `L` by Reingold's theorem. -/
theorem mem_L : Bipartite ∈ L encUGraph :=
  logSpaceReducible_compl_USTCON.mem_L (compl_mem_L USTCON_mem_L)

/-- The triangle, which is not bipartite. -/
@[expose] def triangle : UGraphInstance where
  n := 3
  adj a b := decide (a ≠ b)
  symm a b := by simp [ne_comm]
  loopless a := by simp

/-- The graph without vertices, which is bipartite. -/
@[expose] def empty : UGraphInstance where
  n := 0
  adj _ _ := false
  symm _ _ := rfl
  loopless _ := rfl

theorem triangle_notMem : triangle ∉ Bipartite := by
  rw [mem_Bipartite, SimpleGraph.IsBipartite, SimpleGraph.two_colorable_iff_forall_loop_even]
  intro h
  have hadj : ∀ a b : Fin 3, a ≠ b → triangle.graph.Adj a b := fun a b hab => by
    simpa [triangle] using hab
  have := h (show Fin triangle.n from (0 : Fin 3)) (.cons (hadj 0 1 (by decide))
    (.cons (hadj 1 2 (by decide)) (.cons (hadj 2 0 (by decide)) .nil)))
  exact Nat.not_even_iff_odd.2 ⟨1, rfl⟩ this

theorem empty_mem : empty ∈ Bipartite :=
  ⟨SimpleGraph.Coloring.mk (fun _ => 0) fun {a} => a.elim0⟩

/-- **Undirected connectivity reduces to non-bipartiteness in logarithmic space.** Under
logarithmic-space many-one reductions this is immediate from Reingold's theorem: the reduction
decides its input and outputs the triangle or the graph without vertices. -/
theorem USTCON_logSpaceReducible_compl :
    LogSpaceReducible encUSTCON encUGraph USTCON Bipartiteᶜ := by
  obtain ⟨f, hf, hA⟩ := USTCON_mem_L
  refine ⟨fun I => if f I then triangle else empty,
    (Turing.MultiTapeTM.ComputableInLogSpace.of_finite (encIn := Turing.MultiTapeTM.encBool)
      (fun b : Bool => if b then triangle else empty)).comp hf, fun I => ?_⟩
  rw [hA I]
  cases h : f I <;> simp [h, empty_mem, triangle_notMem]

/-- **Undirected non-connectivity reduces to bipartiteness in logarithmic space.** -/
theorem compl_USTCON_logSpaceReducible :
    LogSpaceReducible encUSTCON encUGraph USTCONᶜ Bipartite := by
  simpa only [compl_compl] using USTCON_logSpaceReducible_compl.compl

end Bipartite

end Cslib.Complexity
