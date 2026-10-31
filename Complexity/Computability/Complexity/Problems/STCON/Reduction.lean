/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Problems.STCON
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Expr
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.ReadSymbol
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.CounterBounds

/-!
# The configuration graph as an instance of directed connectivity

A nondeterministic machine `ntm` within space `c * (Nat.log2 n + 1)` accepts an input `w` exactly
when an accepting halted vertex is reachable from the start vertex in its compact configuration
graph (`Turing.MultiTapeNTM.ConfigurationGraph.accepts_iff_reachable_bad_of_runsInSpace`). Adding
one sink vertex, with an arc from every accepting halted vertex, turns this into a question of
directed `s`–`t` connectivity (`Cslib.Complexity.STCON.configurationInstance`): the vertices are
the `vertexBound` identifiers of the compact graph and the sink, the source is the start vertex
and the target is the sink [Sipser, Theorem 8.25][Sipser2013].

The instance is computed in logarithmic space from the framed input
(`Cslib.Complexity.STCON.computableInLogSpace_configurationInstance`) by a counter program with
output (`Cslib.Complexity.STCON.writer`). It counts the input length `n`, writes the unary header,
and writes the adjacency matrix entry by entry, keeping only `n`, the two vertex identifiers and
the code of one input symbol: each entry reads at most the one input bit that the arc of the
configuration graph depends on, and evaluates the arithmetic edge test
(`Turing.MultiTapeNTM.ConfigurationGraph.edgeExpr`). The identifiers are below a fixed polynomial
in `n`, so the registers stay polynomially bounded. The framing of the input keeps them bounded by
a polynomial in the length of the input even when the instance is encoded by the empty word.

## Main definitions

* `Cslib.Complexity.STCON.sinkAdj`: the arcs of the configuration graph with a sink.
* `Cslib.Complexity.STCON.configurationInstance`: the instance of directed connectivity.
* `Cslib.Complexity.STCON.writer`: the counter program writing the encoded instance.

## Main results

* `Cslib.Complexity.STCON.configurationInstance_mem_iff`: the instance is in `STCON` exactly when
  the machine accepts.
* `Cslib.Complexity.STCON.computableInLogSpace_configurationInstance`: the instance is computed in
  logarithmic space.

## References

* [M. Sipser, *Introduction to the Theory of Computation*, Theorem 8.25][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

namespace STCON

open _root_.Turing _root_.Turing.MultiTapeNTM _root_.Turing.MultiTapeNTM.ConfigurationGraph

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

/-- The start vertex is a vertex of the ambient graph. -/
theorem startID_lt_vertexBound (n : ℕ) :
    startID ntm (radix (radixExponent State c) n) <
      vertexBound (k := k) (radix (radixExponent State c) n) := by
  have hcard : Fintype.card (Option State) < radix (radixExponent State c) n :=
    calc Fintype.card (Option State) < 2 ^ Fintype.card (Option State) := Nat.lt_two_pow_self
      _ ≤ (n + 2) ^ Fintype.card (Option State) := Nat.pow_le_pow_left (by omega) _
      _ ≤ radix (radixExponent State c) n :=
        Nat.pow_le_pow_right (by omega) (by simp only [radixExponent]; omega)
  apply Cslib.Radix.pack_lt (radix_pos _ _)
  intro i
  cases i with
  | inputPos =>
    change 1 < _
    have := Fintype.card_pos (α := Option State)
    omega
  | control =>
    change stateCode (some ntm.q₀) < _
    exact (Fintype.equivFin (Option State) _).isLt.trans hcard
  | _ => exact radix_pos _ _

/-- The arcs of the configuration graph on `w`, with a sink at `vertexBound`: an arc of the
compact configuration graph between identifiers below `vertexBound`, and an arc from each
accepting halted vertex to the sink. -/
noncomputable def sinkAdj (D : ℕ) (w : List Bool) (u v : ℕ) : Bool :=
  if v < vertexBound (k := k) (radix D w.length) then
    edgeWithSymbol ntm (radix D w.length) w.length u v w[queryIndex (k := k) (radix D w.length) u]?
  else bad (k := k) (State := State) (radix D w.length) w.length u

/-- **The configuration graph of `ntm` on `w` as an instance of directed connectivity**: the
`vertexBound` identifiers of the compact configuration graph and a sink, with source the start
vertex and target the sink. -/
noncomputable def configurationInstance (w : List Bool) : STCONInstance where
  n := vertexBound (k := k) (radix (radixExponent State c) w.length) + 1
  adj u v := sinkAdj ntm (radixExponent State c) w u v
  s := ⟨startID ntm (radix (radixExponent State c) w.length),
    (startID_lt_vertexBound ntm c w.length).trans (Nat.lt_succ_self _)⟩
  t := ⟨vertexBound (k := k) (radix (radixExponent State c) w.length), Nat.lt_succ_self _⟩

/-- Every path from the source to the sink in `configurationInstance` passes through an accepting
halted vertex just before the sink. -/
private theorem exists_bad_of_mem_configurationInstance {w : List Bool}
    (h : configurationInstance ntm c w ∈ STCON) :
    ∃ u, Relation.ReflTransGen (Edge ntm (radix (radixExponent State c) w.length) w)
      (startID ntm (radix (radixExponent State c) w.length)) u ∧
      bad (k := k) (State := State) (radix (radixExponent State c) w.length) w.length u = true := by
  -- a path to the sink passes through an accepting vertex just before it
  set D := radixExponent State c
  set I := configurationInstance ntm c w
  have hstart := startID_lt_vertexBound ntm c w.length
  have key : ∀ x : Fin I.n, Relation.ReflTransGen I.Adj I.s x →
      ((x : ℕ) < vertexBound (k := k) (radix D w.length) →
        Relation.ReflTransGen (Edge ntm (radix D w.length) w)
          (startID ntm (radix D w.length)) x) ∧
      ((x : ℕ) = vertexBound (k := k) (radix D w.length) → ∃ u,
        Relation.ReflTransGen (Edge ntm (radix D w.length) w) (startID ntm (radix D w.length)) u ∧
          bad (k := k) (State := State) (radix D w.length) w.length u = true) := by
    intro x hx
    induction hx with
    | refl => exact ⟨fun _ => .refl, fun h => absurd h (Nat.ne_of_lt hstart)⟩
    | @tail y z _ hyz ih =>
      change sinkAdj ntm D w y z = true at hyz
      unfold sinkAdj at hyz
      split_ifs at hyz with hz
      · have hy := (lt_vertexBound_of_edgeWithSymbol (ntm := ntm) hyz).1
        exact ⟨fun _ => (ih.1 hy).tail hyz, fun h => absurd h (Nat.ne_of_lt hz)⟩
      · have hy := lt_vertexBound_of_valid (k := k) (State := State) (by
          simp only [bad, Bool.and_eq_true] at hyz
          exact hyz.1.1)
        exact ⟨fun h => absurd h hz, fun _ => ⟨y, ih.1 hy, hyz⟩⟩
  exact (key I.t h).2 rfl

/-- **The instance is in `STCON` exactly when the machine accepts**, for a machine within space
`c * (Nat.log2 n + 1)` on the input. -/
theorem configurationInstance_mem_iff {w : List Bool}
    (hs : ntm.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    configurationInstance ntm c w ∈ STCON ↔ ntm.Accepts w := by
  set D := radixExponent State c
  set I := configurationInstance ntm c w
  rw [accepts_iff_reachable_bad_of_runsInSpace c hs]
  refine ⟨exists_bad_of_mem_configurationInstance ntm c, ?_⟩
  -- a path to an accepting vertex continues to the sink
  rintro ⟨u, hu, hbad⟩
  rw [mem_STCON]
  have hlift : ∀ x, Relation.ReflTransGen (Edge ntm (radix D w.length) w)
      (startID ntm (radix D w.length)) x →
      ∃ hx : x < I.n, Relation.ReflTransGen I.Adj I.s ⟨x, hx⟩ := by
    intro x hx
    induction hx with
    | refl => exact ⟨I.s.isLt, .refl⟩
    | @tail y z _ hyz ih =>
      obtain ⟨hy, hpath⟩ := ih
      have hz := (lt_vertexBound_of_edgeWithSymbol (ntm := ntm) hyz).2
      refine ⟨hz.trans (Nat.lt_succ_self _), hpath.tail ?_⟩
      change sinkAdj ntm D w y z = true
      rw [sinkAdj, ite_eq_left hz]
      exact hyz
  obtain ⟨hu', hpath⟩ := hlift u hu
  refine hpath.tail ?_
  change sinkAdj ntm D w u (vertexBound (k := k) (radix D w.length)) = true
  rw [sinkAdj, ite_eq_right (lt_irrefl _)]
  exact hbad

/-! ### The writer -/

section Writer

open CounterProgram Instr Expr _root_.Turing.MultiTapeTM

variable (D : ℕ)

/-- The number of vertices, from the input length in register `0`. -/
noncomputable abbrev numVerticesExpr : Expr :=
  add (vertexBoundExpr k (radixExpr D (reg 0))) (const 1)

/-- **The writer** of the encoded instance, on the framed input. Register `0` holds the input
length, register `1` a counter or the row, register `2` the column and register `3` the code of
the input symbol of the row's arc. Labels `0` and `1` count the input; the three counting loops
at labels `2`, `7` and `12` write the unary header; the nested loops at labels `17` and `20`
write the matrix, the entry at labels `23` to `32`; label `33` halts. -/
noncomputable def writer : CounterProgram where
  code :=
    [read (mul (const 2) (reg 0)) 1 2 2,
     assign 0 (add (reg 0) (const 1)) 0] ++
    forCode 2 1 (numVerticesExpr (k := k) D) 5 6 ++ [emit true 4, emit false 7] ++
    forCode 7 1 (startIDExpr ntm (radixExpr D (reg 0))) 10 11 ++ [emit true 9, emit false 12] ++
    forCode 12 1 (vertexBoundExpr k (radixExpr D (reg 0))) 15 16 ++ [emit true 14, emit false 17] ++
    forCode 17 1 (numVerticesExpr (k := k) D) 20 33 ++
    forCode 20 2 (numVerticesExpr (k := k) D) 23 19 ++
    [lt (reg 2) (vertexBoundExpr k (radixExpr D (reg 0))) 24 30] ++
    readSymbolCode 24 3 29 (reg 0) (queryIndexExpr k (radixExpr D (reg 0)) (reg 1)) ++
    [lt (const 0) (edgeExpr ntm (radixExpr D (reg 0)) (reg 0) (reg 1) (reg 2) (reg 3)) 31 32,
     lt (const 0) (badExpr k State (radixExpr D (reg 0)) (reg 0) (reg 1)) 31 32,
     emit true 22,
     emit false 22,
     halt []]
  registers := 4

variable {ntm D} (w : List Bool) {B : ℕ}

private theorem flatMap_range_true (M : ℕ) :
    (List.range M).flatMap (fun _ => [true]) = List.replicate M true := by
  induction M with
  | zero => rfl
  | succ M ih => simp [List.range_succ, List.replicate_succ', ih]

/-- Bounded registers. -/
private theorem bounded_regs {L u v y : ℕ} (hL : L ≤ B) (hu : u ≤ B) (hv : v ≤ B) (hy : y ≤ B) :
    ∀ r ∈ [L, u, v, y], r ≤ B := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- The input length is counted by reading the markers of the framed input. -/
private theorem reachesOut_count (hL : w.length ≤ B) : ∀ j ≤ w.length,
    (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B) (0, [j, 0, 0, 0])
      (2, [w.length, 0, 0, 0]) [] := by
  intro j hj
  induction h : w.length - j generalizing j with
  | zero =>
    have : j = w.length := by omega
    subst this
    refine ReachesOut.read (show (writer ntm D).instr 0 = _ from rfl)
      (bounded_regs hL (by omega) (by omega) (by omega)) ?_
    simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero,
      getElem?_frame_two_mul_length, readLabel]
    exact ReachesOut.refl _
  | succ m ih =>
    refine ReachesOut.read (show (writer ntm D).instr 0 = _ from rfl)
      (bounded_regs (by omega) (by omega) (by omega) (by omega)) ?_
    simp only [eval_mul, eval_const, eval_reg, List.getD_cons_zero,
      getElem?_frame_two_mul (show j < w.length by omega), readLabel]
    refine ReachesOut.assign (show (writer ntm D).instr 1 = _ from rfl)
      (bounded_regs (by omega) (by omega) (by omega) (by omega)) ?_
    simpa using ih (j + 1) (by omega) (by omega)

/-- A counting loop writing `M` set bits. -/
private theorem reachesOut_ones {b body exit M : ℕ} {bound : Expr}
    (hcode : (writer ntm D).CodeAt b (forCode b 1 bound body exit))
    (hbody : (writer ntm D).instr body = emit true (b + 2))
    (hbound : ∀ i, bound.eval [w.length, i, 0, 0] = M) (hM : M ≤ B) (hL : w.length ≤ B)
    {i₀ : ℕ} (hi₀ : i₀ ≤ B) :
    (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B) (b, [w.length, i₀, 0, 0])
      (exit, [w.length, M, 0, 0]) (List.replicate M true) := by
  obtain ⟨regs', hreach, hinv⟩ := reachesOut_forCode (w := frame w) (o := fun _ => [true])
    (N := M) hcode
    (fun k regs => regs = [w.length, k, 0, 0] ∧ k ≤ M) hM
    (by
      rintro k regs ⟨rfl, hk⟩
      exact ⟨rfl, hbound k, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro k hk regs ⟨rfl, -⟩
      have hB : ∀ r ∈ [w.length, k, 0, 0], r ≤ B :=
        bounded_regs hL (by omega) (by omega) (by omega)
      exact ⟨[w.length, k, 0, 0], ReachesOut.emit hbody hB (ReachesOut.refl _), rfl, hB,
        by simp, by omega⟩)
    [w.length, i₀, 0, 0] (bounded_regs hL hi₀ (by omega) (by omega))
    (by simp)
  obtain ⟨rfl, -⟩ := hinv
  rw [flatMap_range_true] at hreach
  exact hreach

/-- The entry at labels `29` and `30`: compare the Boolean value of an expression with `0`. -/
private theorem reachesOut_bit {l : ℕ} {e : Expr} {regs : List ℕ} {b : Bool}
    (hl : (writer ntm D).instr l = lt (const 0) e 31 32) (he : e.eval regs = b.toNat)
    (hB : ∀ r ∈ regs, r ≤ B) :
    (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B) (l, regs) (22, regs) [b] := by
  refine ReachesOut.lt hl hB ?_
  rw [eval_const, he]
  cases b
  · exact ReachesOut.emit (show (writer ntm D).instr 32 = _ from rfl) hB (ReachesOut.refl _)
  · exact ReachesOut.emit (show (writer ntm D).instr 31 = _ from rfl) hB (ReachesOut.refl _)

private theorem flatMap_singleton_eq_map {β : Type} (l : List ℕ) (f : ℕ → β) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- Reading the symbol at `queryIndex` from the framed input into register `3`. -/
private theorem reachesOut_entry_symbol (hL : w.length ≤ B)
    (hN : vertexBound (k := k) (radix D w.length) + 1 ≤ B) (h2 : 2 ≤ B) {u v y : ℕ}
    (hu : u ≤ vertexBound (k := k) (radix D w.length) + 1)
    (hv : v < vertexBound (k := k) (radix D w.length) + 1) (hy : y ≤ 2) :
    ∃ y' ≤ 2, y' = symbolCode w[queryIndex (k := k) (radix D w.length) u]? ∧
      (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B)
        (24, [w.length, u, v, y]) (29, [w.length, u, v, y']) [] := by
  have hB : ∀ r ∈ [w.length, u, v, y], r ≤ B := bounded_regs hL (by omega) (by omega) (by omega)
  have hcode : (writer ntm D).CodeAt 24
      (readSymbolCode 24 3 29 (reg 0) (queryIndexExpr k (radixExpr D (reg 0)) (reg 1))) := by
    simp only [readSymbolCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨_, Nat.le_of_lt_succ (symbolCode_lt _), rfl, ?_⟩
  simpa using reachesOut_readSymbolCode (w := w) hcode (by simp) hB

/-- **An entry of the matrix**: the code of the requested input symbol is stored in register `3`,
and the entry is written. -/
private theorem reachesOut_entry (hL : w.length ≤ B)
    (hN : vertexBound (k := k) (radix D w.length) + 1 ≤ B) (h2 : 2 ≤ B) {u v y : ℕ}
    (hu : u ≤ vertexBound (k := k) (radix D w.length) + 1)
    (hv : v < vertexBound (k := k) (radix D w.length) + 1)
    (hy : y ≤ 2) :
    ∃ y' ≤ 2, (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B)
      (23, [w.length, u, v, y]) (22, [w.length, u, v, y']) [sinkAdj ntm D w u v] := by
  have hB : ∀ {y'}, y' ≤ 2 → ∀ r ∈ [w.length, u, v, y'], r ≤ B := fun hy' =>
    bounded_regs hL (by omega) (by omega) (by omega)
  by_cases hvb : v < vertexBound (k := k) (radix D w.length)
  · obtain ⟨y', hy', hsym, hreach⟩ :=
      reachesOut_entry_symbol (ntm := ntm) (D := D) w hL hN h2 hu hv hy
    refine ⟨y', hy', ?_⟩
    refine ReachesOut.lt (show (writer ntm D).instr 23 = _ from rfl) (hB hy) ?_
    simp only [eval_reg, eval_vertexBoundExpr, eval_radixExpr, List.getD_cons_zero,
      List.getD_cons_succ, hvb, ↓reduceIte]
    refine (hreach.trans (reachesOut_bit w (show (writer ntm D).instr 29 = _ from rfl)
      (eval_edgeExpr ntm (symbol := w[queryIndex (k := k) (radix D w.length) u]?) (by simp [hsym]))
      (hB hy'))).of_eq ?_
    simp [sinkAdj, hvb]
  · refine ⟨y, hy, ?_⟩
    refine ReachesOut.lt (show (writer ntm D).instr 23 = _ from rfl) (hB hy) ?_
    simp only [eval_reg, eval_vertexBoundExpr, eval_radixExpr, List.getD_cons_zero,
      List.getD_cons_succ, hvb, ↓reduceIte]
    refine (reachesOut_bit w (show (writer ntm D).instr 30 = _ from rfl) eval_badExpr
      (hB hy)).of_eq ?_
    simp [sinkAdj, hvb]

/-- **A row of the matrix**, by the inner counting loop at label `20`. -/
private theorem reachesOut_row (hL : w.length ≤ B)
    (hN : vertexBound (k := k) (radix D w.length) + 1 ≤ B) (h2 : 2 ≤ B) {u x y : ℕ}
    (hu : u < vertexBound (k := k) (radix D w.length) + 1)
    (hx : x ≤ vertexBound (k := k) (radix D w.length) + 1)
    (hy : y ≤ 2) :
    ∃ y' ≤ 2, (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B)
      (20, [w.length, u, x, y]) (19, [w.length, u, vertexBound (k := k) (radix D w.length) + 1, y'])
      ((List.range (vertexBound (k := k) (radix D w.length) + 1)).map (sinkAdj ntm D w u)) := by
  have hcode : (writer ntm D).CodeAt 20 (forCode 20 2 (numVerticesExpr (k := k) D) 23 19) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs', hreach, y', rfl, -, hy'⟩ := reachesOut_forCode (w := frame w)
    (o := fun v => [sinkAdj ntm D w u v]) (N := vertexBound (k := k) (radix D w.length) + 1) hcode
    (fun v regs => ∃ y, regs = [w.length, u, v, y] ∧
      v ≤ vertexBound (k := k) (radix D w.length) + 1 ∧
      y ≤ 2) hN
    (by
      rintro v regs ⟨y, rfl, hv, hy⟩
      exact ⟨rfl, by simp, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro v hv regs ⟨y, rfl, -, hy⟩
      obtain ⟨y', hy', hreach⟩ := reachesOut_entry (ntm := ntm) (D := D) w hL hN h2 hu.le hv hy
      exact ⟨_, hreach, rfl, bounded_regs hL (by omega) (by omega) (by omega),
        y', by simp, by omega, hy'⟩)
    [w.length, u, x, y] (bounded_regs hL (by omega) (by omega) (by omega))
    ⟨y, by simp, by omega, hy⟩
  rw [flatMap_singleton_eq_map] at hreach
  exact ⟨y', hy', hreach⟩

/-- **The matrix**, by the outer counting loop at label `17`. -/
private theorem reachesOut_matrix (hL : w.length ≤ B)
    (hN : vertexBound (k := k) (radix D w.length) + 1 ≤ B) (h2 : 2 ≤ B) {i₀ : ℕ} (hi₀ : i₀ ≤ B) :
    ∃ regs, (writer ntm D).ReachesOut (frame w) ((writer ntm D).Active B)
      (17, [w.length, i₀, 0, 0]) (33, regs)
      ((List.range (vertexBound (k := k) (radix D w.length) + 1)).flatMap fun u =>
        (List.range (vertexBound (k := k) (radix D w.length) + 1)).map (sinkAdj ntm D w u)) ∧
      ∀ r ∈ regs, r ≤ B := by
  have hcode : (writer ntm D).CodeAt 17 (forCode 17 1 (numVerticesExpr (k := k) D) 20 33) := by
    simp only [forCode, codeAt_cons, codeAt_nil, and_true]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨regs', hreach, x, y, rfl, -, hx, hy⟩ := reachesOut_forCode (w := frame w)
    (o := fun u =>
      (List.range (vertexBound (k := k) (radix D w.length) + 1)).map (sinkAdj ntm D w u))
    (N := vertexBound (k := k) (radix D w.length) + 1) hcode
    (fun u regs => ∃ x y, regs = [w.length, u, x, y] ∧
      u ≤ vertexBound (k := k) (radix D w.length) + 1 ∧
        x ≤ vertexBound (k := k) (radix D w.length) + 1 ∧
      y ≤ 2) hN
    (by
      rintro u regs ⟨x, y, rfl, hu, hx, hy⟩
      exact ⟨rfl, by simp, by simp, bounded_regs hL (by omega) (by omega) (by omega)⟩)
    (by
      rintro u hu regs ⟨x, y, rfl, -, hx, hy⟩
      obtain ⟨y', hy', hreach⟩ := reachesOut_row (ntm := ntm) (D := D) w hL hN h2 hu hx hy
      exact ⟨_, hreach, rfl, bounded_regs hL (by omega) (by omega) (by omega),
        _, y', by simp, by omega, le_rfl, hy'⟩)
    [w.length, i₀, 0, 0] (bounded_regs hL hi₀ (by omega) (by omega))
    ⟨0, 0, by simp, by omega, by omega, by omega⟩
  exact ⟨_, hreach, bounded_regs hL (by omega) (by omega) (by omega)⟩


/-- A `forCode` block in `writer` is at `b` when instructions `b`, `b + 1`, `b + 2` match. -/
private theorem codeAt_forCode {b u body exit : ℕ} {bound : Expr}
    (h₀ : (writer ntm D).instr b = .assign u (const 0) (b + 1))
    (h₁ : (writer ntm D).instr (b + 1) = .lt (reg u) bound body exit)
    (h₂ : (writer ntm D).instr (b + 2) = .assign u (add (reg u) (const 1)) (b + 1)) :
    (writer ntm D).CodeAt b (forCode b u bound body exit) := by
  simp only [forCode, codeAt_cons, codeAt_nil, and_true]
  exact ⟨h₀, h₁, h₂⟩

variable (ntm) in
/-- **The instance is computed in logarithmic space** from the framed input. -/
theorem computableInLogSpace_configurationInstance :
    ComputableInLogSpace (configurationInstance ntm c) (encFramed encBits) encSTCON := by
  set D := radixExponent State c
  refine (writer ntm D).computableInLogSpace_of_reachesOut
    (D * Fintype.card (Register k) + 1) fun w => ?_
  simp only [encFramed_apply, encBits_apply]
  set VB := vertexBound (k := k) (radix D w.length)
  set S := startID ntm (radix D w.length)
  set B := ((frame w).length + 1) ^ (D * Fintype.card (Register k) + 1)
  have hS : S < VB := startID_lt_vertexBound ntm c w.length
  obtain ⟨hN, hL, h2⟩ := configurationCounter_bounds (k := k) D w
  have hreg (i : ℕ) (hi : i ≤ B) : ∀ r ∈ [w.length, i, 0, 0], r ≤ B :=
    bounded_regs hL hi (by omega) (by omega)
  have hones₁ := reachesOut_ones (ntm := ntm) (D := D) w
    (codeAt_forCode rfl rfl rfl)
    (show (writer ntm D).instr 5 = _ from rfl) (M := VB + 1) (fun _ => by simp [VB]) hN hL
    (i₀ := 0) (by omega)
  have hones₂ := reachesOut_ones (ntm := ntm) (D := D) w
    (codeAt_forCode rfl rfl rfl)
    (show (writer ntm D).instr 10 = _ from rfl) (M := S) (fun _ => by simp [S]) (by omega) hL
    (i₀ := VB + 1) hN
  have hones₃ := reachesOut_ones (ntm := ntm) (D := D) w
    (codeAt_forCode rfl rfl rfl)
    (show (writer ntm D).instr 15 = _ from rfl) (M := VB) (fun _ => by simp [VB]) (by omega) hL
    (i₀ := S) (by omega)
  obtain ⟨regs, hmat, hregs⟩ := reachesOut_matrix (ntm := ntm) (D := D) w hL hN h2
    (i₀ := VB) (by omega)
  have hchain := (reachesOut_count (ntm := ntm) (D := D) w hL 0 (Nat.zero_le _)).trans
    (hones₁.trans (ReachesOut.emit (show (writer ntm D).instr 6 = _ from rfl)
      (hreg _ (by omega)) (hones₂.trans (ReachesOut.emit
        (show (writer ntm D).instr 11 = _ from rfl) (hreg _ (by omega))
        (hones₃.trans (ReachesOut.emit (show (writer ntm D).instr 16 = _ from rfl)
          (hreg _ (by omega)) hmat))))))
  refine ⟨(33, regs), _, [], hchain, rfl, ?_, hregs⟩
  rw [encSTCON_apply, STCONInstance.encode,
    STCONInstance.matrix_eq_flatMap _ (sinkAdj ntm D w) fun _ _ => rfl]
  simp [configurationInstance, VB, S, D]


end Writer


end STCON

end Cslib.Complexity
