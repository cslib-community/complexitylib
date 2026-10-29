/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Dijkstra.ListEncode
public import Complexity.Algorithms.WordRAM.PriorityQueue.Basic
public import Complexity.Computability.WordRAM.Compile

/-!
# Black-Box Dijkstra's Algorithm Parameterized by Any Word-RAM Priority Queue

This file implements the outer graph-traversal layer of Dijkstra's single-source shortest-path
algorithm once (`Cslib.Algorithms.WordRAM.Dijkstra.dijkstraCode`) on `15 + r_pq` registers over
`Basis.exact`, parameterized only by a `Cslib.Algorithms.WordRAM.PriorityQueue.PQCode` subroutine,
and proves its black-box correctness and amortized instruction-count specification
(`Cslib.Algorithms.WordRAM.Dijkstra.dijkstra_of_pq_spec`) for any
`Cslib.Algorithms.WordRAM.PriorityQueue.PQPackage` (supporting arbitrary concrete potentials
`potential : Data r_pq → ℕ`).

Instantiating `dijkstra_of_pq_spec` with:
* `PriorityQueue.BinaryHeap.pkg` (`potential = 0`) yields `LogLinearSpec` and `LogLinearStatement`
  (`O((m + 1) (⌊log₂ n⌋ + 1))`);
* any amortized `PQPackage` with `O(1)` `insert`/`decreaseKey` and `O(log n + 1)` `extractMin`
  (such as a Fibonacci heap) directly yields `O(m + min(n, m + 1) (⌊log₂ n⌋ + 1))` and
  `O(m + n (⌊log₂ n⌋ + 1))` with zero duplication of Dijkstra's graph logic.

## Main definitions

* `Cslib.Algorithms.WordRAM.Dijkstra.pqMap`: register relocation `Fin.natAdd 15` placing the
  priority-queue registers at `15 .. 15 + r_pq - 1`.
* `Cslib.Algorithms.WordRAM.Dijkstra.dijkstraCode`: structured word-RAM code for Dijkstra's
  algorithm calling a black-box `PQCode .exact r_pq`.

## Main results

* `Cslib.Algorithms.WordRAM.Dijkstra.dijkstraCode_exec`: structured `ExecWithin` correctness and
  amortized running-time bound for `dijkstraCode pkg.code`.
* `Cslib.Algorithms.WordRAM.Dijkstra.dijkstra_of_pq_spec`: flat-program `Runs` + `halt` theorem for
  `(dijkstraCode pkg.code).program OuterReg.zero`.

## References

* [E. W. Dijkstra, *A note on two problems in connexion with graphs*][Dijkstra1959]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Dijkstra

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.WordRAM.PriorityQueue

/-- Relocation map embedding the `r_pq` priority-queue registers above the `15` outer registers. -/
def pqMap {r_pq : ℕ} : Fin r_pq → Fin (15 + r_pq) := Fin.natAdd 15

/-- Register relocation `pqMap` is injective. -/
theorem pqMap_injective {r_pq : ℕ} : (pqMap (r_pq := r_pq)).Injective :=
  Fin.natAdd_injective r_pq 15

/-! ### Outer caller registers (`0 .. 14`) of `dijkstraCode` -/
namespace OuterReg

variable {r_pq : ℕ}

/-- Constant `0`. -/
abbrev zero : Fin (15 + r_pq) := ⟨0, by omega⟩
/-- Constant `1`. -/
abbrev one : Fin (15 + r_pq) := ⟨1, by omega⟩
/-- Constant `3`. -/
abbrev three : Fin (15 + r_pq) := ⟨2, by omega⟩
/-- Number of vertices `n`. -/
abbrev nReg : Fin (15 + r_pq) := ⟨3, by omega⟩
/-- Base address `n + 4` of the edge array. -/
abbrev eb : Fin (15 + r_pq) := ⟨4, by omega⟩
/-- Base address `G.dbase = n + 2 * m + 4` of the `n` output distance words. -/
abbrev db : Fin (15 + r_pq) := ⟨5, by omega⟩
/-- Current vertex `u` extracted from the priority queue. -/
abbrev u : Fin (15 + r_pq) := ⟨6, by omega⟩
/-- Distance word `best = d[u]` of `u`. -/
abbrev best : Fin (15 + r_pq) := ⟨7, by omega⟩
/-- Current edge index `j`. -/
abbrev j : Fin (15 + r_pq) := ⟨8, by omega⟩
/-- End edge index `jend` of `adj u`. -/
abbrev jend : Fin (15 + r_pq) := ⟨9, by omega⟩
/-- Target vertex `tv` of edge `j`. -/
abbrev tv : Fin (15 + r_pq) := ⟨10, by omega⟩
/-- Weight `tc` of edge `j`. -/
abbrev tc : Fin (15 + r_pq) := ⟨11, by omega⟩
/-- Candidate distance word `best + tc`. -/
abbrev cand : Fin (15 + r_pq) := ⟨12, by omega⟩
/-- Current distance word `d[tv]` (inside `relaxEdges`) and emptiness flag (in outer loop). -/
abbrev dv : Fin (15 + r_pq) := ⟨13, by omega⟩
/-- Scratch address register. -/
abbrev t : Fin (15 + r_pq) := ⟨14, by omega⟩

end OuterReg

open OuterReg

-- These comparisons reduce on fixed register indices even though `r_pq` is a variable.
local macro "fin15" : tactic => `(tactic| exact of_decide_eq_true rfl)

private theorem outer_notMem_pqMap {r_pq : ℕ} {i : Fin (15 + r_pq)} (hi : i.val < 15) :
    i ∉ Set.range (pqMap (r_pq := r_pq)) := by
  rintro ⟨k, rfl⟩
  simp only [pqMap, Fin.val_natAdd] at hi
  omega

/-! ## Structured Word-RAM Code of Black-Box Dijkstra -/

/-- Straight-line outer header: loads `n`, `source`, `db = G.dbase`, `eb = n + 4`, sets
`mem[db + source] := 1`, and places `pqBase = db + n` in `t`. -/
def outerHeader {r_pq : ℕ} : Code .exact (15 + r_pq) := ram_exact[
  zero ← #0; one ← #1; three ← #3;
  t ← #1; nReg ← *t;
  t ← #2; u ← *t;
  t ← nReg + three; t ← *t;
  db ← t + t; db ← db + nReg; db ← db + three; db ← db + one;
  eb ← nReg + three; eb ← eb + one;
  t ← db + u; *t ← one;
  t ← db + nReg ]

/-- Full setup of `dijkstraCode`: runs `outerHeader`, initializes the relocated priority queue at
`pqBase = G.dbase + G.n` via `initFresh`, inserts `(source, 1)`, and sets `dv := 0` (non-empty). -/
def dijkstraSetup {r_pq : ℕ} (P : PQCode .exact r_pq) : Code .exact (15 + r_pq) :=
  .seq outerHeader <|
  .seq (.op (.copy (pqMap P.frontierReg) t)) <|
  .seq (.op (.copy (pqMap P.nReg) nReg)) <|
  .seq (P.toSubroutineCode.initFresh.rename pqMap) <|
  .seq (P.callInsert pqMap zero one u one)
       (.op (.copy dv zero))

/-- Straight-line start of one edge relaxation: loads `(tv, tc)` for edge `j`, advances `j`, forms
`cand := best + tc`, and loads `dv := mem[db + tv]`. -/
def edgePrefix {r_pq : ℕ} : Code .exact (15 + r_pq) := ram_exact[
  t ← j + j; t ← t + eb; tv ← *t; t ← t + one; tc ← *t; j ← j + one;
  cand ← best + tc;
  t ← db + tv; dv ← *t ]

/-- Body of `relaxEdges` for a single outgoing edge. -/
def edgeBody {r_pq : ℕ} (P : PQCode .exact r_pq) : Code .exact (15 + r_pq) :=
  .seq edgePrefix
    (.branch (.eq dv zero)
      (.seq (.op (.store t cand)) (P.callInsert pqMap zero one tv cand))
      (.branch (.lt cand dv)
        (.seq (.op (.store t cand)) (P.callDecreaseKey pqMap zero one tv cand))
        (.op (.copy t t))))

/-- Inner loop scanning all outgoing edges `[j, jend)` of vertex `u`. -/
def relaxEdges {r_pq : ℕ} (P : PQCode .exact r_pq) : Code .exact (15 + r_pq) :=
  .loop (.lt j jend) (edgeBody P)

/-- Offset-loading block for `u`: sets `j := offset u` and `jend := offset (u + 1)`. -/
def loadOffsets {r_pq : ℕ} : Code .exact (15 + r_pq) := ram_exact[
  t ← u + three; j ← *t; t ← t + one; jend ← *t ]

/-- One outer round of `dijkstraCode`: extracts minimum `(u, best)`, loads `u`'s edge range, scans
its outgoing edges via `relaxEdges`, and refreshes the emptiness flag `dv` via `callIsEmpty`. -/
def dijkstraRound {r_pq : ℕ} (P : PQCode .exact r_pq) : Code .exact (15 + r_pq) :=
  .seq (P.callExtractMin pqMap one) <|
  .seq (.op (.copy u (pqMap P.outV))) <|
  .seq (.op (.copy best (pqMap P.outK))) <|
  .seq loadOffsets <|
  .seq (relaxEdges P) <|
  .seq (P.callIsEmpty pqMap zero)
       (.op (.copy dv (pqMap P.outFlag)))

/-- Complete structured word-RAM code for Dijkstra's algorithm calling `P : PQCode .exact r_pq`. -/
def dijkstraCode {r_pq : ℕ} (P : PQCode .exact r_pq) : Code .exact (15 + r_pq) :=
  .seq (dijkstraSetup P) (.loop (.eq dv zero) (dijkstraRound P))

/-! ## Input Boundedness and Framing Helpers -/

section Helpers

variable {r_pq w : ℕ}

/-- Maximum priority-queue key ever inserted or decreased on instance `G`. -/
abbrev pqKeyMax (G : ListInstance) : ℕ := G.n * G.maxWeight + G.maxWeight + 1

/-- Base address `G.dbase + G.n` of the priority-queue memory block. -/
abbrev pqBase (G : ListInstance) : ℕ := G.dbase + G.n

private theorem fits_pqKeyMax {G : ListInstance}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    Fits w (pqKeyMax G) :=
  hw_in.of_le (by unfold pqKeyMax; nlinarith)

private theorem inputFits_encode (G : ListInstance)
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))) :
    InputFits w G.encode := by
  refine ⟨?_, ?_⟩
  · rw [G.encode_length]
    exact hw_in.of_le (by nlinarith)
  · intro x hx
    simp only [ListInstance.encode, List.mem_cons, List.mem_append, List.mem_map, List.mem_range,
      List.mem_flatMap, List.mem_finRange, true_and] at hx
    rcases hx with rfl | rfl | ⟨⟨i, hi, rfl⟩ | ⟨u, ⟨v, c⟩, he, hx⟩⟩
    · exact hw_in.of_le (by nlinarith)
    · have := G.source.isLt
      exact hw_in.of_le (by nlinarith)
    · have hle : G.offset i ≤ G.m := G.offset_n ▸ G.offset_mono (by omega)
      exact hw_in.of_le (by nlinarith)
    · simp only [List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · have := v.isLt
        exact hw_in.of_le (by nlinarith)
      · have hc := G.le_maxWeight he
        exact hw_in.of_le (by nlinarith)

private theorem frame_outer_regs {P : PQCode .exact r_pq} {n K_max base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    {s : IndexedMinPQ.State n} {x x' : Data (15 + r_pq)}
    (hr : C.rep s (x.comap pqMap)) (hx' : x'.Bounded w)
    (hreg : ∀ k, (x'.regs (pqMap k)) = (x.regs (pqMap k)))
    (hm : x'.mem = x.mem) :
    C.rep s (x'.comap pqMap) ∧ C.potential (x'.comap pqMap) = C.potential (x.comap pqMap) := by
  refine C.frame_caller (F := ∅) hr (hx'.comap pqMap) (fun i _ => hreg i)
    (Finset.disjoint_empty_right _) ?_
  rw [hm]
  exact Modifies.refl _ _

private theorem frame_outer_write {P : PQCode .exact r_pq} {n K_max base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    {s : IndexedMinPQ.State n} {x : Data (15 + r_pq)} (hr : C.rep s (x.comap pqMap))
    (a : ℕ) {val : ℕ} (ha : a < base) (hfit : Fits w val) :
    C.rep s ((x.write a val).comap pqMap) ∧
      C.potential ((x.write a val).comap pqMap) = C.potential (x.comap pqMap) := by
  have hb : (x.comap pqMap).Bounded w := C.bounded hr
  have hb' : ((x.write a val).comap pqMap).Bounded w := by
    refine ⟨hb.1, fun b => ?_⟩
    simp only [Data.comap, Data.write_mem, Function.update_apply]
    split_ifs
    · exact hfit
    · exact hb.2 b
  have hdisj : Disjoint (Block.mk base C.space).footprint {a} := by
    rw [Finset.disjoint_singleton_right, Block.mem_footprint]
    dsimp only [Block.Owns]
    omega
  have hmod : Modifies {a} x.mem (x.write a val).mem := by
    intro b hb_ne
    rw [Finset.mem_singleton] at hb_ne
    exact Function.update_of_ne hb_ne _ _
  exact C.frame_caller hr hb' (fun _ _ => rfl) hdisj hmod

private theorem stateOf_unique {P : PQCode .exact r_pq} {n K_max base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n)) :
    ∀ {s : IndexedMinPQ.State n} {y : Data (15 + r_pq)}, C.rep s (y.comap pqMap) →
      (by classical exact if h : ∃ s', C.rep s' (y.comap pqMap) then Classical.choose h
        else IndexedMinPQ.empty n) = s := by
  classical
  intro s y hr
  have hex : ∃ s', C.rep s' (y.comap pqMap) := ⟨s, hr⟩
  simp only [hex, ↓reduceDIte]
  exact C.rep_unique (Classical.choose_spec hex) hr

/-- Canonical abstract PQ state extracted from `y` via `C.rep_unique` (for proof potentials). -/
private noncomputable def stateOf {P : PQCode .exact r_pq} {n K_max base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    (y : Data (15 + r_pq)) : IndexedMinPQ.State n := by
  classical
  exact if h : ∃ s', C.rep s' (y.comap pqMap) then Classical.choose h else IndexedMinPQ.empty n

private theorem stateOf_eq {P : PQCode .exact r_pq} {n K_max base : ℕ}
    (C : SubroutineDS P.toSubroutineCode (IndexedMinPQ.spec n K_max) w base ![n]
      (IndexedMinPQ.empty n))
    {s : IndexedMinPQ.State n} {y : Data (15 + r_pq)} (hr : C.rep s (y.comap pqMap)) :
    stateOf C y = s :=
  stateOf_unique C hr

private theorem edgesWord_take_succ {N b d i : ℕ} {es : List (Fin N × ℕ)} (v : Fin N)
    (hi : i < es.length) :
    edgesWord b (es.take (i + 1)) v d = if es[i].1 = v then
      edgeWord b es[i].2 (edgesWord b (es.take i) v d) else edgesWord b (es.take i) v d := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [edgesWord, List.foldl_append, Option.toList_some, List.foldl_cons, List.foldl_nil]

end Helpers

/-! ## Inner Edge-Scan Specification (`relaxEdges_spec`) -/

section InnerScan

variable {r_pq w : ℕ}

/-- Discovered vertices (`mem[dbase + v] ≠ 0`) that are no longer in `dom s`. -/
def visitedSet (G : ListInstance) (s : IndexedMinPQ.State G.n) (y : Data (15 + r_pq)) :
    Finset (Fin G.n) :=
  Finset.univ.filter fun v => y.mem (G.dbase + v) ≠ 0 ∧ v ∉ IndexedMinPQ.dom s

/-- Total outgoing edges of vertices outside `S`. -/
def remEdges (G : ListInstance) (S : Finset (Fin G.n)) : ℕ :=
  ∑ v ∈ Finset.univ.filter (· ∉ S), (G.adj v).length

/-- Tentative distances decoded from `y.mem (G.dbase + ·)`. -/
noncomputable def distWords (G : ListInstance) (y : Data (15 + r_pq)) (v : Fin G.n) : ℕ∞ :=
  decodeDist (y.mem (G.dbase + v))

/-- Synchronization between abstract PQ state `s` and distance array `y.mem (G.dbase + ·)`: every
handle in `dom s` has a nonzero distance word equal to its PQ key. -/
def PQSync (G : ListInstance) (s : IndexedMinPQ.State G.n) (y : Data (15 + r_pq)) : Prop :=
  ∀ v : Fin G.n, v ∈ IndexedMinPQ.dom s →
    y.mem (G.dbase + v) ≠ 0 ∧ s v = some (y.mem (G.dbase + v))

private theorem disjoint_visited_dom (G : ListInstance) (s : IndexedMinPQ.State G.n)
    (y : Data (15 + r_pq)) : Disjoint (visitedSet G s y) (IndexedMinPQ.dom s) :=
  Finset.disjoint_left.mpr fun _ hv hd => (Finset.mem_filter.mp hv).2.2 hd

private theorem card_visited_add_dom_le (G : ListInstance) (s : IndexedMinPQ.State G.n)
    (y : Data (15 + r_pq)) :
    (visitedSet G s y).card + (IndexedMinPQ.dom s).card ≤ G.n := by
  calc
    (visitedSet G s y).card + (IndexedMinPQ.dom s).card
      = (visitedSet G s y ∪ IndexedMinPQ.dom s).card :=
        (Finset.card_union_of_disjoint (disjoint_visited_dom G s y)).symm
    _ ≤ (Finset.univ : Finset (Fin G.n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = G.n := Finset.card_fin G.n

private theorem card_visited_add_dom_lt_of_notMem (G : ListInstance) (s : IndexedMinPQ.State G.n)
    (y : Data (15 + r_pq)) {v : Fin G.n}
    (hv_vis : v ∉ visitedSet G s y) (hv_dom : v ∉ IndexedMinPQ.dom s) :
    (visitedSet G s y).card + (IndexedMinPQ.dom s).card + 1 ≤ G.n := by
  have hnot : v ∉ visitedSet G s y ∪ IndexedMinPQ.dom s := by
    rw [Finset.mem_union]
    exact not_or.mpr ⟨hv_vis, hv_dom⟩
  calc
    (visitedSet G s y).card + (IndexedMinPQ.dom s).card + 1
      = (visitedSet G s y ∪ IndexedMinPQ.dom s).card + 1 := by
        rw [Finset.card_union_of_disjoint (disjoint_visited_dom G s y)]
    _ = (insert v (visitedSet G s y ∪ IndexedMinPQ.dom s)).card :=
        (Finset.card_insert_of_notMem hnot).symm
    _ ≤ (Finset.univ : Finset (Fin G.n)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = G.n := Finset.card_fin G.n

private theorem edgeBody_spec (pkg : PQPackage .exact r_pq) {G : ListInstance}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n))
    {B J C_wt : ℕ} {V : Fin G.n} {S_vis : Finset (Fin G.n)} {R_after : ℕ}
    {s : IndexedMinPQ.State G.n} {y : Data (15 + r_pq)}
    (hy_bnd : y.Bounded w)
    (hzero : y.regs zero = 0) (hone : y.regs one = 1)
    (heb : y.regs eb = G.n + 4) (hdb : y.regs db = G.dbase)
    (hbest : y.regs best = B) (hB : B ≠ 0)
    (hj : y.regs j = J) (hJ : J < G.m) (hj_lt : J < y.regs jend)
    (hT : y.mem (J + J + (G.n + 4)) = V.val)
    (hW : y.mem (J + J + (G.n + 4) + 1) = C_wt)
    (hBC : B + C_wt ≤ pqKeyMax G)
    (hr : (pkg.cert hw_sp (fits_pqKeyMax hw_in)).rep s (y.comap pqMap))
    (hsync : PQSync G s y)
    (hvis_eq : visitedSet G s y = S_vis)
    (hvis_le : V ∈ S_vis → y.mem (G.dbase + V) ≤ B + C_wt) :
    let hK := fits_pqKeyMax hw_in
    let C := pkg.cert hw_sp hK
    let cIns := pkg.insertTime G.n + 20
    let cDec := pkg.decreaseTime G.n + 20
    let Φ := fun d : Data (15 + r_pq) =>
      C.potential (d.comap pqMap) +
        cIns * min (G.n - S_vis.card - (IndexedMinPQ.dom (stateOf C d)).card)
          (R_after + (d.regs jend - d.regs j)) +
        cDec * (d.regs jend - d.regs j)
    ∃ (z : Data (15 + r_pq)) (s' : IndexedMinPQ.State G.n) (t_step : ℕ),
      ExecWithin w (edgeBody pkg.code) y z t_step ∧
      z.Bounded w ∧
      z.regs j = J + 1 ∧
      (∀ i : Fin (15 + r_pq), i.val < 15 → i ∉ [j, tv, tc, cand, dv, t] → z.regs i = y.regs i) ∧
      C.rep s' (z.comap pqMap) ∧
      PQSync G s' z ∧
      visitedSet G s' z = S_vis ∧
      (IndexedMinPQ.dom s').card ≤ (IndexedMinPQ.dom s).card + 1 ∧
      (∀ v : Fin G.n, z.mem (G.dbase + v) =
        if V = v then edgeWord B C_wt (y.mem (G.dbase + v)) else y.mem (G.dbase + v)) ∧
      (∀ a < G.dbase, z.mem a = y.mem a) ∧
      t_step + 2 + Φ z ≤ Φ y := by
  intro hK C cIns cDec Φ
  have hDb : G.dbase = G.n + 2 * G.m + 4 := rfl
  have hV := V.isLt
  have hsp_eq : C.space = pkg.space G.n := pkg.cert_space hw_sp hK
  have hsp_lo : G.n + 1 ≤ C.space := hsp_eq ▸ pkg.space_lower G.n
  have hS_cert : Fits w (pqBase G + C.space) := hsp_eq ▸ hw_sp
  have harg_eq : C.argMatch = pkg.code.argMatch := pkg.cert_argMatch hw_sp hK
  have f1 : Fits w (J + J) := hw_sp.of_le (by unfold pqBase; omega)
  have f2 : Fits w (J + J + (G.n + 4)) := hw_sp.of_le (by unfold pqBase; omega)
  have f3 : Fits w (J + J + (G.n + 4) + 1) := hw_sp.of_le (by unfold pqBase; omega)
  have f4 : Fits w (J + 1) := hw_sp.of_le (by unfold pqBase; omega)
  have f5 : Fits w (G.dbase + V) := hw_sp.of_le (by unfold pqBase; omega)
  have fC : Fits w (B + C_wt) := hK.of_le hBC
  let y₁ := ((((((((y.set t (J + J)).set t (J + J + (G.n + 4))).set tv V.val).set t
    (J + J + (G.n + 4) + 1)).set tc C_wt).set j (J + 1)).set cand (B + C_wt)).set t
    (G.dbase + V)).set dv (y.mem (G.dbase + V))
  have e₁ : ExecWithin w edgePrefix y y₁ 9 := by
    ram_exact_eval [edgePrefix, y₁, hone, heb, hdb, hbest, hj, hT, hW, fC, f1, f2, f3, f4, f5,
      Fin.ext_iff]
  have hy₁_bnd : y₁.Bounded w := e₁.bounded hy_bnd
  have hy₁_pq : ∀ k, y₁.regs (pqMap k) = y.regs (pqMap k) := by
    intro k
    have hk : ∀ i : Fin (15 + r_pq), i.val < 15 → pqMap k ≠ i := by
      intro i hi h; exact outer_notMem_pqMap hi ⟨k, h⟩
    simp only [y₁, Data.set_regs, Function.update_of_ne (hk dv (by fin15)),
      Function.update_of_ne (hk t (by fin15)), Function.update_of_ne (hk cand (by fin15)),
      Function.update_of_ne (hk j (by fin15)), Function.update_of_ne (hk tc (by fin15)),
      Function.update_of_ne (hk tv (by fin15))]
  have hy₁_out : ∀ i : Fin (15 + r_pq), i ∉ [j, tv, tc, cand, dv, t] → y₁.regs i = y.regs i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    simp only [y₁, Data.set_regs, Function.update_of_ne hi.2.2.2.2.1,
      Function.update_of_ne hi.2.2.2.2.2, Function.update_of_ne hi.2.2.2.1,
      Function.update_of_ne hi.1, Function.update_of_ne hi.2.2.1, Function.update_of_ne hi.2.1]
  obtain ⟨hr₁, hpot₁⟩ := frame_outer_regs C hr hy₁_bnd hy₁_pq rfl
  have hz_out := outer_notMem_pqMap (r_pq := r_pq) (i := zero) (by fin15)
  have ho_out := outer_notMem_pqMap (r_pq := r_pq) (i := one) (by fin15)
  have htv_out := outer_notMem_pqMap (r_pq := r_pq) (i := tv) (by fin15)
  have hcand_out := outer_notMem_pqMap (r_pq := r_pq) (i := cand) (by fin15)
  have hy_st : stateOf C y = s := stateOf_eq C hr
  by_cases hD0 : y.mem (G.dbase + V) = 0
  · have hc_eq : (Cond.eq dv zero).Holds y₁ := by
      have hdv_y₁ : y₁.regs dv = 0 := by
        have h : y₁.regs dv = y.mem (G.dbase + V) := rfl
        exact h.trans hD0
      have hz_y₁ : y₁.regs zero = 0 := (hy₁_out zero (by fin15)).trans hzero
      rw [Cond.holds_eq, hdv_y₁, hz_y₁]
    have hV_not_dom : V ∉ IndexedMinPQ.dom s := fun hd => (hsync V hd).1 hD0
    have hV_none : s V = none := IndexedMinPQ.notMem_dom_iff.mp hV_not_dom
    have hV_not_vis : V ∉ visitedSet G s y := by
      simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hD0, ne_eq,
        not_true_eq_false, false_and, not_false_eq_true]
    have hcard_lt : S_vis.card + (IndexedMinPQ.dom s).card + 1 ≤ G.n :=
      hvis_eq ▸ card_visited_add_dom_lt_of_notMem G s y hV_not_vis hV_not_dom
    let y₂ := y₁.write (G.dbase + V) (B + C_wt)
    have e_st : ExecWithin (B := .exact) w (.op (.store t cand)) y₁ y₂ 1 := by
      have ht_eq : y₁.regs t = G.dbase + V := rfl
      have hc_eq' : y₁.regs cand = B + C_wt := rfl
      dsimp only [y₂]
      rw [← ht_eq, ← hc_eq']
      exact ExecWithin.store
    obtain ⟨hr₂, hpot₂⟩ := frame_outer_write C hr₁ (G.dbase + V) (by unfold pqBase; omega) fC
    have hy₂_z : y₂.regs zero = 0 := (hy₁_out zero (by fin15)).trans hzero
    have hy₂_o : y₂.regs one = 1 := (hy₁_out one (by fin15)).trans hone
    have hy₂_tv : y₂.regs tv = V.val := rfl
    have hy₂_cand : y₂.regs cand = B + C_wt := rfl
    obtain ⟨z, t_ins, e_ins, hr_z, hmod_z, hregs_z, hpot_ins⟩ :=
      pkg.code.callInsert_exec C hsp_lo hS_cert hK harg_eq pqMap_injective
        hz_out ho_out htv_out hcand_out hr₂ ⟨hV_none, hBC⟩ hy₂_z hy₂_o hy₂_tv hy₂_cand
    have hmod_low : ∀ a < pqBase G, z.mem a = y₂.mem a := fun a ha =>
      hmod_z a (by rw [Block.mem_footprint]; dsimp only [Block.Owns]; omega)
    let s' : IndexedMinPQ.State G.n := Function.update s V (some (B + C_wt))
    have hdom' : IndexedMinPQ.dom s' = insert V (IndexedMinPQ.dom s) :=
      IndexedMinPQ.dom_insert s V (B + C_wt)
    have hcard_dom' : (IndexedMinPQ.dom s').card = (IndexedMinPQ.dom s).card + 1 := by
      rw [hdom', Finset.card_insert_of_notMem hV_not_dom]
    have hz_bnd : z.Bounded w := by
      refine (e_ins.bounded (e_st.bounded hy₁_bnd))
    have hzj : z.regs j = J + 1 := by
      rw [hregs_z j (outer_notMem_pqMap (by fin15))]
      rfl
    have hzjend : z.regs jend = y.regs jend := by
      rw [hregs_z jend (outer_notMem_pqMap (by fin15))]
      exact hy₁_out jend (by fin15)
    have hz_out : ∀ i : Fin (15 + r_pq), i.val < 15 → i ∉ [j, tv, tc, cand, dv, t] →
        z.regs i = y.regs i := fun i hi hnot =>
      (hregs_z i (outer_notMem_pqMap hi)).trans (hy₁_out i hnot)
    have hz_word : ∀ v : Fin G.n, z.mem (G.dbase + v) =
        if V = v then edgeWord B C_wt (y.mem (G.dbase + v)) else y.mem (G.dbase + v) := by
      intro v
      rw [hmod_low (G.dbase + v) (by unfold pqBase; have := v.isLt; omega)]
      simp only [y₂, Data.write_mem, y₁, Data.set_mem, Function.update_apply]
      by_cases hv : V = v
      · subst hv
        simp only [↓reduceIte, edgeWord, hD0]
      · have hne : (G.dbase + (v : ℕ)) ≠ G.dbase + V := by
          intro he; exact hv (Fin.ext (by omega))
        simp only [hv, hne, ↓reduceIte]
    have hsync' : PQSync G s' z := by
      intro v hv_dom
      rw [hdom', Finset.mem_insert] at hv_dom
      rcases hv_dom with hv_eq | hv_dom
      · rw [hv_eq, hz_word V]
        simp only [↓reduceIte, edgeWord, hD0]
        exact ⟨by omega, Function.update_self V (some (B + C_wt)) s⟩
      · have hne : v ≠ V := fun he => hV_not_dom (he ▸ hv_dom)
        have hne' : V ≠ v := hne.symm
        rw [hz_word v]
        simp only [hne', ↓reduceIte, s', Function.update_of_ne hne]
        exact hsync v hv_dom
    have hvis' : visitedSet G s' z = S_vis := by
      rw [← hvis_eq]
      ext v
      simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hdom', Finset.mem_insert]
      by_cases hv : V = v
      · subst hv
        simp only [true_or, not_true_eq_false, and_false, false_and, hD0, ne_eq]
      · rw [hz_word v]
        have hne : v ≠ V := Ne.symm hv
        simp only [hv, ↓reduceIte, hne, false_or]
    have hchg : C.charge s (.insert V (B + C_wt)) ≤ pkg.insertTime G.n :=
      pkg.charge_insert hw_sp hK s V (B + C_wt)
    have hz_st : stateOf C z = s' := stateOf_eq C hr_z
    refine ⟨z, s', 9 + (1 + t_ins + 1), e₁.seq (.branch_pos hc_eq (e_st.seq e_ins)),
      hz_bnd, hzj, hz_out, hr_z, hsync', hvis', hcard_dom'.le, hz_word, ?_, ?_⟩
    · intro a ha
      rw [hmod_low a (by unfold pqBase; omega)]
      dsimp only [y₂, Data.write_mem, y₁, Data.set_mem]
      exact Function.update_of_ne (by omega) _ _
    · dsimp only [Φ]
      rw [hz_st, hy_st, hcard_dom', hzj, hzjend, hj]
      rw [hpot₂, hpot₁] at hpot_ins
      have hmin_le : min (G.n - S_vis.card - ((IndexedMinPQ.dom s).card + 1))
          (R_after + (y.regs jend - (J + 1))) + 1 ≤
          min (G.n - S_vis.card - (IndexedMinPQ.dom s).card) (R_after + (y.regs jend - J)) := by
        omega
      have hmul1 : cIns * (min (G.n - S_vis.card - ((IndexedMinPQ.dom s).card + 1))
          (R_after + (y.regs jend - (J + 1))) + 1) ≤
          cIns * min (G.n - S_vis.card - (IndexedMinPQ.dom s).card)
            (R_after + (y.regs jend - J)) := Nat.mul_le_mul_left cIns hmin_le
      have hmul2 : cDec * (y.regs jend - (J + 1)) + cDec = cDec * (y.regs jend - J) := by
        have hsub : y.regs jend - J = (y.regs jend - (J + 1)) + 1 := by omega
        rw [hsub, Nat.mul_add, Nat.mul_one]
      dsimp only [cIns, cDec] at hmul1 hmul2 ⊢
      linarith only [hpot_ins, hchg, hmul1, hmul2]
  · have hc_eq : ¬(Cond.eq dv zero).Holds y₁ := by
      have hdv_y₁ : y₁.regs dv = y.mem (G.dbase + V) := rfl
      have hz_y₁ : y₁.regs zero = 0 := (hy₁_out zero (by fin15)).trans hzero
      rw [Cond.holds_eq, hdv_y₁, hz_y₁]
      exact hD0
    by_cases hlt : B + C_wt < y.mem (G.dbase + V)
    · have hc_lt : (Cond.lt cand dv).Holds y₁ := by
        have hcand_y₁ : y₁.regs cand = B + C_wt := rfl
        have hdv_y₁ : y₁.regs dv = y.mem (G.dbase + V) := rfl
        rw [Cond.holds_lt, hcand_y₁, hdv_y₁]
        exact hlt
      have hV_not_vis : V ∉ S_vis := fun hv => Nat.not_lt.mpr (hvis_le hv) hlt
      have hV_dom : V ∈ IndexedMinPQ.dom s := by
        by_contra hnd
        apply hV_not_vis
        rw [← hvis_eq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ V, hD0, hnd⟩
      have hsV : s V = some (y.mem (G.dbase + V)) := (hsync V hV_dom).2
      let y₂ := y₁.write (G.dbase + V) (B + C_wt)
      have e_st : ExecWithin (B := .exact) w (.op (.store t cand)) y₁ y₂ 1 := by
        have ht_eq : y₁.regs t = G.dbase + V := rfl
        have hc_eq' : y₁.regs cand = B + C_wt := rfl
        dsimp only [y₂]
        rw [← ht_eq, ← hc_eq']
        exact ExecWithin.store
      obtain ⟨hr₂, hpot₂⟩ := frame_outer_write C hr₁ (G.dbase + V) (by unfold pqBase; omega) fC
      have hy₂_z : y₂.regs zero = 0 := (hy₁_out zero (by fin15)).trans hzero
      have hy₂_o : y₂.regs one = 1 := (hy₁_out one (by fin15)).trans hone
      have hy₂_tv : y₂.regs tv = V.val := rfl
      have hy₂_cand : y₂.regs cand = B + C_wt := rfl
      obtain ⟨z, t_dec, e_dec, hr_z, hmod_z, hregs_z, hpot_dec⟩ :=
        pkg.code.callDecreaseKey_exec C hsp_lo hS_cert hK harg_eq pqMap_injective
          ho_out htv_out hcand_out hr₂ ⟨⟨y.mem (G.dbase + V), hsV, hlt.le⟩, hBC⟩
          hy₂_z hy₂_o hy₂_tv hy₂_cand
      have hmod_low : ∀ a < pqBase G, z.mem a = y₂.mem a := fun a ha =>
        hmod_z a (by rw [Block.mem_footprint]; dsimp only [Block.Owns]; omega)
      let s' : IndexedMinPQ.State G.n := Function.update s V (some (B + C_wt))
      have hdom' : IndexedMinPQ.dom s' = IndexedMinPQ.dom s :=
        IndexedMinPQ.dom_decreaseKey hV_dom (B + C_wt)
      have hz_bnd : z.Bounded w := e_dec.bounded (e_st.bounded hy₁_bnd)
      have hzj : z.regs j = J + 1 := by
        rw [hregs_z j (outer_notMem_pqMap (by fin15))]
        rfl
      have hzjend : z.regs jend = y.regs jend := by
        rw [hregs_z jend (outer_notMem_pqMap (by fin15))]
        exact hy₁_out jend (by fin15)
      have hz_out : ∀ i : Fin (15 + r_pq), i.val < 15 → i ∉ [j, tv, tc, cand, dv, t] →
          z.regs i = y.regs i := fun i hi hnot =>
        (hregs_z i (outer_notMem_pqMap hi)).trans (hy₁_out i hnot)
      have hz_word : ∀ v : Fin G.n, z.mem (G.dbase + v) =
          if V = v then edgeWord B C_wt (y.mem (G.dbase + v)) else y.mem (G.dbase + v) := by
        intro v
        rw [hmod_low (G.dbase + v) (by unfold pqBase; have := v.isLt; omega)]
        simp only [y₂, Data.write_mem, y₁, Data.set_mem, Function.update_apply]
        by_cases hv : V = v
        · subst hv
          simp only [↓reduceIte, edgeWord, hD0, hlt]
        · have hne : (G.dbase + (v : ℕ)) ≠ G.dbase + V := by
            intro he; exact hv (Fin.ext (by omega))
          simp only [hv, hne, ↓reduceIte]
      have hsync' : PQSync G s' z := by
        intro v hv_dom
        rw [hdom'] at hv_dom
        by_cases hv : v = V
        · subst hv
          rw [hz_word v]
          simp only [↓reduceIte, edgeWord, hD0, hlt]
          exact ⟨by omega, Function.update_self v (some (B + C_wt)) s⟩
        · have hne' : V ≠ v := Ne.symm hv
          rw [hz_word v]
          simp only [hne', ↓reduceIte, s', Function.update_of_ne hv]
          exact hsync v hv_dom
      have hvis' : visitedSet G s' z = S_vis := by
        rw [← hvis_eq]
        ext v
        simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hdom']
        by_cases hv : V = v
        · subst hv
          exact ⟨fun h => absurd hV_dom h.2, fun h => absurd hV_dom h.2⟩
        · rw [hz_word v]
          simp only [hv, ↓reduceIte]
      have hchg : C.charge s (.decreaseKey V (B + C_wt)) ≤ pkg.decreaseTime G.n :=
        pkg.charge_decreaseKey hw_sp hK s V (B + C_wt)
      have hz_st : stateOf C z = s' := stateOf_eq C hr_z
      refine ⟨z, s', 9 + (1 + t_dec + 1 + 2),
        e₁.seq (.branch_neg hc_eq (.branch_pos hc_lt (e_st.seq e_dec))),
        hz_bnd, hzj, hz_out, hr_z, hsync', hvis', by rw [hdom']; omega, hz_word, ?_, ?_⟩
      · intro a ha
        rw [hmod_low a (by unfold pqBase; omega)]
        dsimp only [y₂, Data.write_mem, y₁, Data.set_mem]
        exact Function.update_of_ne (by omega) _ _
      · dsimp only [Φ]
        rw [hz_st, hy_st, hdom', hzj, hzjend, hj]
        rw [hpot₂, hpot₁] at hpot_dec
        have hmin_le : min (G.n - S_vis.card - (IndexedMinPQ.dom s).card)
            (R_after + (y.regs jend - (J + 1))) ≤
            min (G.n - S_vis.card - (IndexedMinPQ.dom s).card) (R_after + (y.regs jend - J)) := by
          omega
        have hmul1 := Nat.mul_le_mul_left cIns hmin_le
        have hmul2 : cDec * (y.regs jend - (J + 1)) + cDec = cDec * (y.regs jend - J) := by
          have hsub : y.regs jend - J = (y.regs jend - (J + 1)) + 1 := by omega
          rw [hsub, Nat.mul_add, Nat.mul_one]
        dsimp only [cIns, cDec] at hmul1 hmul2 ⊢
        linarith only [hpot_dec, hchg, hmul1, hmul2]
    · have hc_lt : ¬(Cond.lt cand dv).Holds y₁ := by
        have hcand_y₁ : y₁.regs cand = B + C_wt := rfl
        have hdv_y₁ : y₁.regs dv = y.mem (G.dbase + V) := rfl
        rw [Cond.holds_lt, hcand_y₁, hdv_y₁]
        exact hlt
      let z := y₁.set t (y₁.regs t)
      have e_nop : ExecWithin (B := .exact) w (.op (.copy t t)) y₁ z 1 := ExecWithin.copy
      have hz_eq : z = y₁ := by
        ext i
        · simp only [z, Data.set_regs, Function.update_eq_self]
        · rfl
      rw [hz_eq] at e_nop
      have hzj : y₁.regs j = J + 1 := rfl
      have hzjend : y₁.regs jend = y.regs jend := hy₁_out jend (by fin15)
      have hz_word : ∀ v : Fin G.n, y₁.mem (G.dbase + v) =
          if V = v then edgeWord B C_wt (y.mem (G.dbase + v)) else y.mem (G.dbase + v) := by
        intro v
        by_cases hv : V = v
        · subst hv
          simp only [y₁, Data.set_mem, ↓reduceIte, edgeWord, hD0, hlt]
        · simp only [y₁, Data.set_mem, hv, ↓reduceIte]
      have hy₁_st : stateOf C y₁ = s := stateOf_eq C hr₁
      refine ⟨y₁, s, 9 + (1 + 2 + 2),
        e₁.seq (.branch_neg hc_eq (.branch_neg hc_lt e_nop)),
        hy₁_bnd, hzj, fun i _ hnot => hy₁_out i hnot, hr₁, hsync, hvis_eq, Nat.le_succ _,
        hz_word, fun _ _ => rfl, ?_⟩
      dsimp only [Φ]
      rw [hy₁_st, hy_st, hzj, hzjend, hj, hpot₁]
      have hmin_le : min (G.n - S_vis.card - (IndexedMinPQ.dom s).card)
          (R_after + (y.regs jend - (J + 1))) ≤
          min (G.n - S_vis.card - (IndexedMinPQ.dom s).card) (R_after + (y.regs jend - J)) := by
        omega
      have hmul1 := Nat.mul_le_mul_left cIns hmin_le
      have hmul2 : cDec * (y.regs jend - (J + 1)) + cDec = cDec * (y.regs jend - J) := by
        have hsub : y.regs jend - J = (y.regs jend - (J + 1)) + 1 := by omega
        rw [hsub, Nat.mul_add, Nat.mul_one]
      dsimp only [cIns, cDec] at hmul1 hmul2 ⊢
      linarith only [hmul1, hmul2]

end InnerScan

section RelaxLoop

variable {r_pq w : ℕ}

private theorem edgesWord_of_le {N b d : ℕ} {es : List (Fin N × ℕ)} {v : Fin N} (hd : d ≠ 0)
    (hle : ∀ c, (v, c) ∈ es → d ≤ b + c) : edgesWord b es v d = d := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have h' : (if e.1 = v then edgeWord b e.2 d else d) = d := by
      split_ifs with he
      · have := hle e.2 (by rw [← he]; simp)
        simp [edgeWord, hd, Nat.not_lt.2 this]
      · rfl
    simp only [edgesWord, List.foldl_cons] at ih ⊢
    rw [h']
    exact ih fun c hc => hle c (List.mem_cons_of_mem _ hc)

private structure ScanInv (pkg : PQPackage .exact r_pq) (G : ListInstance)
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n))
    (U : Fin G.n) (B D₀ : ℕ) (S_vis : Finset (Fin G.n)) (x y : Data (15 + r_pq)) : Prop where
  bounded : y.Bounded w
  frame : ∀ i : Fin (15 + r_pq), i.val < 15 → i ∉ [j, tv, tc, cand, dv, t] → y.regs i = x.regs i
  j_ge : G.offset U ≤ y.regs j
  j_le : y.regs j ≤ G.offset ((U : ℕ) + 1)
  word : ∀ v : Fin G.n, y.mem (G.dbase + v) =
    edgesWord B ((G.adj U).take (y.regs j - G.offset U)) v (x.mem (G.dbase + v))
  input : ∀ a < G.dbase, y.mem a = x.mem a
  pq : ∃ s : IndexedMinPQ.State G.n, (pkg.cert hw_sp (fits_pqKeyMax hw_in)).rep s (y.comap pqMap) ∧
    PQSync G s y ∧
    visitedSet G s y = S_vis ∧
    (IndexedMinPQ.dom s).card ≤ D₀ + (y.regs j - G.offset U)

private theorem relaxEdges_spec (pkg : PQPackage .exact r_pq) {G : ListInstance}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n))
    (U : Fin G.n) {B : ℕ} {S_vis : Finset (Fin G.n)} {R_after : ℕ}
    {s₀ : IndexedMinPQ.State G.n} {x : Data (15 + r_pq)}
    (hx_bnd : x.Bounded w)
    (hzero : x.regs zero = 0) (hone : x.regs one = 1)
    (heb : x.regs eb = G.n + 4) (hdb : x.regs db = G.dbase)
    (hbest : x.regs best = B) (hB : B ≠ 0)
    (hj : x.regs j = G.offset U) (hjend : x.regs jend = G.offset ((U : ℕ) + 1))
    (hBC_all : ∀ e ∈ G.adj U, B + e.2 ≤ pqKeyMax G)
    (hinput : ∀ a < G.dbase, x.mem a = (Data.init G.encode : Data (15 + r_pq)).mem a)
    (hr₀ : (pkg.cert hw_sp (fits_pqKeyMax hw_in)).rep s₀ (x.comap pqMap))
    (hsync₀ : PQSync G s₀ x)
    (hvis₀ : visitedSet G s₀ x = S_vis)
    (hvis_le : ∀ v ∈ S_vis, x.mem (G.dbase + v) ≠ 0 ∧
      ∀ c, (v, c) ∈ G.adj U → x.mem (G.dbase + v) ≤ B + c) :
    let hK := fits_pqKeyMax hw_in
    let C := pkg.cert hw_sp hK
    let cIns := pkg.insertTime G.n + 20
    let cDec := pkg.decreaseTime G.n + 20
    ∃ (z : Data (15 + r_pq)) (s' : IndexedMinPQ.State G.n) (t_scan : ℕ),
      ExecWithin w (relaxEdges pkg.code) x z t_scan ∧
      z.Bounded w ∧
      (∀ i : Fin (15 + r_pq), i.val < 15 → i ∉ [j, tv, tc, cand, dv, t] → z.regs i = x.regs i) ∧
      C.rep s' (z.comap pqMap) ∧
      PQSync G s' z ∧
      visitedSet G s' z = S_vis ∧
      (IndexedMinPQ.dom s').card ≤ (IndexedMinPQ.dom s₀).card + (G.adj U).length ∧
      (∀ v : Fin G.n, z.mem (G.dbase + v) = edgesWord B (G.adj U) v (x.mem (G.dbase + v))) ∧
      (∀ a < G.dbase, z.mem a = x.mem a) ∧
      t_scan + C.potential (z.comap pqMap) +
          cIns * min (G.n - S_vis.card - (IndexedMinPQ.dom s').card) R_after ≤
        C.potential (x.comap pqMap) +
          cIns * min (G.n - S_vis.card - (IndexedMinPQ.dom s₀).card)
            (R_after + (G.adj U).length) +
          cDec * (G.adj U).length + 2 := by
  intro hK C cIns cDec
  have hsucc : G.offset ((U : ℕ) + 1) = G.offset U + (G.adj U).length := G.offset_succ U.isLt
  have hle_m : G.offset ((U : ℕ) + 1) ≤ G.m := G.offset_n ▸ G.offset_mono U.isLt
  let D₀ := (IndexedMinPQ.dom s₀).card
  let Φ : Data (15 + r_pq) → ℕ := fun d =>
    C.potential (d.comap pqMap) +
      cIns * min (G.n - S_vis.card - (IndexedMinPQ.dom (stateOf C d)).card)
        (R_after + (d.regs jend - d.regs j)) +
      cDec * (d.regs jend - d.regs j)
  have hx_inv : ScanInv pkg G hw_in hw_sp U B D₀ S_vis x x :=
    ⟨hx_bnd, fun _ _ _ => rfl, hj.ge, hj ▸ G.offset_mono (Nat.le_succ _),
      fun v => by simp [hj, edgesWord], fun _ _ => rfl,
      ⟨s₀, hr₀, hsync₀, hvis₀, by simp [D₀, hj]⟩⟩
  obtain ⟨z, t_scan, he_scan, hz_inv, hnot_lt, hΦ_end⟩ :=
    ExecWithin.loop_potential_retain (cond := .lt j jend)
      (ScanInv pkg G hw_in hw_sp U B D₀ S_vis x) Φ
      (fun y hy hc => by
        obtain ⟨s, hr, hsync, hvis_y, hdom_y⟩ := hy.pq
        have hy_jend : y.regs jend = G.offset ((U : ℕ) + 1) :=
          (hy.frame jend (by fin15) (by fin15)).trans hjend
        rw [Cond.holds_lt, hy_jend] at hc
        have hj_ge := hy.j_ge
        let i := y.regs j - G.offset U
        have hi : i < (G.adj U).length := by dsimp only [i]; omega
        have hJi : y.regs j = G.offset U + i := by dsimp only [i]; omega
        have hJm : y.regs j < G.m := lt_of_lt_of_le hc hle_m
        have hDb : G.dbase = G.n + 2 * G.m + 4 := rfl
        have hT : y.mem (y.regs j + y.regs j + (G.n + 4)) = ((G.adj U)[i].1 : ℕ) := by
          rw [hy.input _ (by omega), hinput _ (by omega), hJi,
            show G.offset U + i + (G.offset U + i) + (G.n + 4) =
              2 * (G.offset U + i) + G.n + 4 by ring]
          exact G.init_target U hi
        have hW : y.mem (y.regs j + y.regs j + (G.n + 4) + 1) = (G.adj U)[i].2 := by
          rw [hy.input _ (by omega), hinput _ (by omega), hJi,
            show G.offset U + i + (G.offset U + i) + (G.n + 4) + 1 =
              2 * (G.offset U + i) + G.n + 5 by ring]
          exact G.init_weight U hi
        have hmem_e : (G.adj U)[i] ∈ G.adj U := List.getElem_mem hi
        have hBC : B + (G.adj U)[i].2 ≤ pqKeyMax G := hBC_all _ hmem_e
        have hv_le : (G.adj U)[i].1 ∈ S_vis →
            y.mem (G.dbase + (G.adj U)[i].1) ≤ B + (G.adj U)[i].2 := by
          intro hvS
          obtain ⟨hnz, hall⟩ := hvis_le _ hvS
          rw [hy.word, edgesWord_of_le hnz (fun c hc' => hall c (List.mem_of_mem_take hc'))]
          exact hall _ hmem_e
        obtain ⟨y', s', t_step, he_step, hy'_bnd, hy'_j, hy'_fr, hr', hsync', hvis',
            hdom', hy'_word, hy'_in, hpot_step⟩ :=
          edgeBody_spec pkg hw_in hw_sp (R_after := R_after) hy.bounded
            ((hy.frame zero (by fin15) (by fin15)).trans hzero)
            ((hy.frame one (by fin15) (by fin15)).trans hone)
            ((hy.frame eb (by fin15) (by fin15)).trans heb)
            ((hy.frame db (by fin15) (by fin15)).trans hdb)
            ((hy.frame best (by fin15) (by fin15)).trans hbest)
            hB rfl hJm (hy_jend.symm ▸ hc) hT hW hBC hr hsync hvis_y hv_le
        refine ⟨y', t_step, he_step, ⟨hy'_bnd, ?_, by omega, by omega, ?_, ?_,
          ⟨s', hr', hsync', hvis', by omega⟩⟩, hpot_step⟩
        · intro k hk hnot
          exact (hy'_fr k hk hnot).trans (hy.frame k hk hnot)
        · intro v
          have hsub : y'.regs j - G.offset U = i + 1 := by omega
          rw [hsub, edgesWord_take_succ v hi, hy'_word v, hy.word v]
        · intro a ha
          exact (hy'_in a ha).trans (hy.input a ha))
      hx_inv
  obtain ⟨s', hr', hsync', hvis', hdom'⟩ := hz_inv.pq
  have hz_jend : z.regs jend = G.offset ((U : ℕ) + 1) :=
    (hz_inv.frame jend (by fin15) (by fin15)).trans hjend
  rw [Cond.holds_lt, hz_jend] at hnot_lt
  have hzj_eq : z.regs j = G.offset ((U : ℕ) + 1) := le_antisymm hz_inv.j_le (Nat.not_lt.mp hnot_lt)
  have hlen : z.regs j - G.offset U = (G.adj U).length := by omega
  have hsub_z : z.regs jend - z.regs j = 0 := by omega
  have hsub_x : x.regs jend - x.regs j = (G.adj U).length := by omega
  refine ⟨z, s', t_scan, he_scan, hz_inv.bounded, hz_inv.frame, hr', hsync', hvis',
    hlen ▸ hdom', ?_, hz_inv.input, ?_⟩
  · intro v
    rw [hz_inv.word v, hlen, List.take_length]
  · dsimp only [Φ] at hΦ_end
    rw [stateOf_eq C hr', stateOf_eq C hr₀, hsub_z, hsub_x, Nat.add_zero, Nat.mul_zero,
      Nat.add_zero] at hΦ_end
    simpa only [Nat.add_assoc] using hΦ_end

end RelaxLoop

/-! ## Outer Round Invariant, Setup, Round Step, and Main Black-Box Theorems -/

section OuterAlgorithm

variable {r_pq w : ℕ}

private structure OuterInv (pkg : PQPackage .exact r_pq) (G : ListInstance)
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n))
    (y : Data (15 + r_pq)) : Prop where
  bounded : y.Bounded w
  zero_eq : y.regs zero = 0
  one_eq : y.regs one = 1
  three_eq : y.regs three = 3
  n_eq : y.regs nReg = G.n
  eb_eq : y.regs eb = G.n + 4
  db_eq : y.regs db = G.dbase
  input : ∀ a < G.dbase, y.mem a = (Data.init G.encode : Data (15 + r_pq)).mem a
  pq : ∃ s : IndexedMinPQ.State G.n, (pkg.cert hw_sp (fits_pqKeyMax hw_in)).rep s (y.comap pqMap) ∧
    PQSync G s y ∧
    (y.regs dv = 0 ↔ IndexedMinPQ.dom s ≠ ∅) ∧
    G.toInstance.Inv (visitedSet G s y) (distWords G y)

private noncomputable def outerPot (pkg : PQPackage .exact r_pq) (G : ListInstance)
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n))
    (y : Data (15 + r_pq)) : ℕ :=
  let C := pkg.cert hw_sp (fits_pqKeyMax hw_in)
  let s := stateOf C y
  let S := visitedSet G s y
  let R := remEdges G S
  let D := (IndexedMinPQ.dom s).card
  C.potential (y.comap pqMap) +
    (pkg.extractTime G.n + pkg.emptyTime G.n + 20) * min (G.n - S.card) (R + D) +
    (pkg.insertTime G.n + 20) * min (G.n - S.card - D) R +
    (pkg.decreaseTime G.n + 20) * R

private theorem dijkstraSetup_spec (pkg : PQPackage .exact r_pq) {G : ListInstance}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n)) :
    let hK := fits_pqKeyMax hw_in
    let C := pkg.cert hw_sp hK
    ∃ y t_setup, ExecWithin w (dijkstraSetup pkg.code) (.init G.encode) y t_setup ∧
      OuterInv pkg G hw_in hw_sp y ∧
      t_setup + C.potential (y.comap pqMap) ≤
        pkg.initTime G.n + pkg.insertTime G.n + 26 ∧
      outerPot pkg G hw_in hw_sp y ≤
        C.potential (y.comap pqMap) +
          min G.n (G.m + 1) * (pkg.extractTime G.n + pkg.emptyTime G.n + 20) +
          min G.n G.m * (pkg.insertTime G.n + 20) +
          G.m * (pkg.decreaseTime G.n + 20) := by
  classical
  intro hK C
  have hsp_eq : C.space = pkg.space G.n := pkg.cert_space hw_sp hK
  have hsp_lo : G.n + 1 ≤ C.space := hsp_eq ▸ pkg.space_lower G.n
  have hS_cert : Fits w (pqBase G + C.space) := hsp_eq ▸ hw_sp
  have harg_eq : C.argMatch = pkg.code.argMatch := pkg.cert_argMatch hw_sp hK
  have hsrc_lt := G.source.isLt
  have hDb' : G.m + G.m + G.n + 3 + 1 = G.dbase := by unfold ListInstance.dbase; omega
  have hoff : (Data.init G.encode : Data (15 + r_pq)).mem (G.n + 3) = G.m := by
    rw [G.init_offset le_rfl, G.offset_n]
  have f0 : Fits w 0 := fits_zero w
  have f1 : Fits w 1 := hw_sp.of_le (by have := pkg.space_lower G.n; omega)
  have f2 : Fits w 2 := hw_in.of_le (by nlinarith)
  have f3 : Fits w 3 := hw_in.of_le (by nlinarith)
  have fn : Fits w G.n := hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have fn3 : Fits w (G.n + 3) := hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have fn4 : Fits w (G.n + 3 + 1) := hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have fm2 : Fits w (G.m + G.m) := hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have fm2n : Fits w (G.m + G.m + G.n) := hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have fm2n3 : Fits w (G.m + G.m + G.n + 3) :=
    hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have fDb : Fits w G.dbase := hw_sp.of_le (by unfold pqBase; omega)
  have fds : Fits w (G.dbase + G.source) := hw_sp.of_le (by unfold pqBase; omega)
  have fpq : Fits w (pqBase G) := hw_sp.of_le (by omega)
  let x₀ : Data (15 + r_pq) := .init G.encode
  have hx₀_bnd : x₀.Bounded w := Data.Bounded.init (inputFits_encode G hw_in)
  obtain ⟨x₁, he_hdr, hx₁_m, hx₁_z, hx₁_o, hx₁_3, hx₁_n, hx₁_u, hx₁_db, hx₁_eb, hx₁_t⟩ :
      ∃ x₁, ExecWithin w outerHeader x₀ x₁ 18 ∧
        x₁.mem = Function.update x₀.mem (G.dbase + G.source) 1 ∧
        x₁.regs zero = 0 ∧ x₁.regs one = 1 ∧ x₁.regs three = 3 ∧
        x₁.regs nReg = G.n ∧ x₁.regs u = G.source.val ∧
        x₁.regs db = G.dbase ∧ x₁.regs eb = G.n + 4 ∧ x₁.regs t = pqBase G := by
    refine ⟨?z_hdr, ?e_hdr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case e_hdr =>
      ram_exact_eval [outerHeader, x₀, Data.init_regs, G.init_n, G.init_source, hoff,
        f0, f1, f2, f3, fn, fn3, fn4, fm2, fm2n, fm2n3, hDb', fDb, fds, fpq, Fin.ext_iff]
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  let x₁' := x₁.set (pqMap pkg.code.frontierReg) (pqBase G)
  let x₂ := x₁'.set (pqMap pkg.code.nReg) G.n
  have he_cp1 : ExecWithin (B := .exact) w (.op (.copy (pqMap pkg.code.frontierReg) t))
      x₁ x₁' 1 := by
    dsimp only [x₁']
    rw [← hx₁_t]
    exact ExecWithin.copy
  have he_cp2 : ExecWithin (B := .exact) w (.op (.copy (pqMap pkg.code.nReg) nReg))
      x₁' x₂ 1 := by
    have hn_eq : x₁'.regs nReg = G.n := by
      rw [Data.set_regs,
        Function.update_of_ne (fun h => outer_notMem_pqMap (by fin15) ⟨_, h.symm⟩)]
      exact hx₁_n
    dsimp only [x₂]
    rw [← hn_eq]
    exact ExecWithin.copy
  have hx₂_bnd : x₂.Bounded w := he_cp2.bounded (he_cp1.bounded (he_hdr.bounded hx₀_bnd))
  have hx₂_out : ∀ i : Fin (15 + r_pq), i.val < 15 → x₂.regs i = x₁.regs i := by
    intro i hi
    have h1 : i ≠ pqMap pkg.code.nReg := fun h => outer_notMem_pqMap hi ⟨_, h.symm⟩
    have h2 : i ≠ pqMap pkg.code.frontierReg := fun h => outer_notMem_pqMap hi ⟨_, h.symm⟩
    simp only [x₂, x₁', Data.set_regs, Function.update_of_ne h1, Function.update_of_ne h2]
  have hx₂_fr : x₂.regs (pqMap pkg.code.frontierReg) = pqBase G := by
    have hne : pqMap pkg.code.frontierReg ≠ pqMap pkg.code.nReg :=
      fun h => pkg.code.nReg_ne_frontier.symm (pqMap_injective h)
    simp only [x₂, x₁', Data.set_regs, Function.update_of_ne hne, Function.update_self]
  have hx₂_par : ∀ j_p,
      x₂.regs (pqMap (pkg.code.toSubroutineCode.initParams j_p)) = ![G.n] j_p := by
    intro j_p
    fin_cases j_p
    change x₂.regs (pqMap (pkg.code.initParams 0)) = G.n
    rw [pkg.code.initParams_eq]
    simp only [Matrix.cons_val_zero, x₂, x₁', Data.set_regs, Function.update_self]
  have hx₂_zero_mem : ∀ a ∈ (Block.mk (pqBase G) C.space).footprint, x₂.mem a = 0 := by
    intro a ha
    rw [Block.mem_footprint] at ha
    dsimp only [Block.Owns, pqBase] at ha
    change x₁.mem a = 0
    rw [hx₁_m, Function.update_of_ne (by omega)]
    exact G.init_past (by omega)
  obtain ⟨x₃, he_init, _, hr₃, hpot₃, hmod₃, hregs₃⟩ :=
    C.initFresh_rename pqMap_injective (hx₂_bnd.comap pqMap) hx₂_fr hx₂_par hx₂_zero_mem
  have hx₃_out : ∀ i : Fin (15 + r_pq), i.val < 15 → x₃.regs i = x₁.regs i := fun i hi =>
    (hregs₃ i (outer_notMem_pqMap hi)).trans (hx₂_out i hi)
  have h1_le_K : 1 ≤ pqKeyMax G := by unfold pqKeyMax; omega
  obtain ⟨x₄, t_ins, he_ins, hr₄, hmod₄, hregs₄, hpot₄⟩ :=
    pkg.code.callInsert_exec C hsp_lo hS_cert hK harg_eq pqMap_injective
      (outer_notMem_pqMap (by fin15)) (outer_notMem_pqMap (by fin15))
      (outer_notMem_pqMap (by fin15)) (outer_notMem_pqMap (by fin15))
      hr₃ ⟨rfl, h1_le_K⟩
      ((hx₃_out zero (by fin15)).trans hx₁_z)
      ((hx₃_out one (by fin15)).trans hx₁_o)
      ((hx₃_out u (by fin15)).trans hx₁_u)
      ((hx₃_out one (by fin15)).trans hx₁_o)
  have hx₄_out : ∀ i : Fin (15 + r_pq), i.val < 15 → x₄.regs i = x₁.regs i := fun i hi =>
    (hregs₄ i (outer_notMem_pqMap hi)).trans (hx₃_out i hi)
  let y := x₄.set dv 0
  have he_dv : ExecWithin (B := .exact) w (.op (.copy dv zero)) x₄ y 1 := by
    have hz4 : x₄.regs zero = 0 := (hx₄_out zero (by fin15)).trans hx₁_z
    dsimp only [y]
    rw [← hz4]
    exact ExecWithin.copy
  have hy_bnd : y.Bounded w := he_dv.bounded
    (he_ins.bounded (he_init.bounded hx₂_bnd))
  have hy_pq : ∀ k, y.regs (pqMap k) = x₄.regs (pqMap k) := fun k =>
    Function.update_of_ne (fun h => outer_notMem_pqMap (by fin15) ⟨k, h⟩) _ _
  let s₀ : IndexedMinPQ.State G.n := Function.update (IndexedMinPQ.empty G.n) G.source (some 1)
  obtain ⟨hr_y, hpot_y⟩ := frame_outer_regs C hr₄ hy_bnd hy_pq rfl
  have hlow_mem : ∀ a < pqBase G, y.mem a = x₁.mem a := by
    intro a ha
    have h4 : x₄.mem a = x₃.mem a :=
      hmod₄ a (by rw [Block.mem_footprint]; dsimp only [Block.Owns]; omega)
    have h3 : x₃.mem a = x₂.mem a :=
      hmod₃ a (by rw [Block.mem_footprint]; dsimp only [Block.Owns]; omega)
    exact h4.trans h3
  have hD_init : ∀ v : Fin G.n, y.mem (G.dbase + v) = if v = G.source then 1 else 0 := by
    intro v
    rw [hlow_mem (G.dbase + v) (by unfold pqBase; have := v.isLt; omega), hx₁_m,
      Function.update_apply]
    by_cases hv : v = G.source
    · subst hv; simp
    · have hne : G.dbase + (v : ℕ) ≠ G.dbase + G.source := fun he => hv (Fin.ext (by omega))
      simp only [hv, hne, ↓reduceIte]
      exact G.init_past (by omega)
  have hdom_s₀ : IndexedMinPQ.dom s₀ = {G.source} := by
    simp [s₀]
  have hsync_y : PQSync G s₀ y := by
    intro v hv_dom
    rw [hdom_s₀, Finset.mem_singleton] at hv_dom
    subst hv_dom
    simp [hD_init, s₀]
  have hvis_y : visitedSet G s₀ y = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v
    simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hD_init v, hdom_s₀,
      Finset.mem_singleton]
    by_cases hv : v = G.source
    · subst hv; simp
    · simp [hv]
  have hdist_y : distWords G y = Function.update (fun _ => ⊤) G.source 0 := by
    funext v
    simp only [distWords, hD_init v]
    by_cases hv : v = G.source
    · subst hv; simp [decodeDist]
    · simp [hv, decodeDist]
  have hrem_emp : remEdges G ∅ = G.m := by
    simp [remEdges, ListInstance.m]
  have hcard_s₀ : (IndexedMinPQ.dom s₀).card = 1 := by
    rw [hdom_s₀, Finset.card_singleton]
  have hdom_ne : IndexedMinPQ.dom s₀ ≠ ∅ := by
    rw [hdom_s₀]
    exact Finset.singleton_ne_empty G.source
  have hy_out : ∀ i : Fin (15 + r_pq), i.val < 15 → i ≠ dv → y.regs i = x₁.regs i := by
    intro i hi hne
    exact (Function.update_of_ne hne _ _).trans (hx₄_out i hi)
  have hinit_le : C.initTime ≤ pkg.initTime G.n := pkg.cert_initTime hw_sp hK
  have hpot0_eq : C.initPotential = 0 := pkg.cert_initPotential hw_sp hK
  have hchg_ins : C.charge (IndexedMinPQ.empty G.n) (.insert G.source 1) ≤ pkg.insertTime G.n :=
    pkg.charge_insert hw_sp hK (IndexedMinPQ.empty G.n) G.source 1
  refine ⟨y, 18 + (1 + (1 + (C.initTime + (t_ins + 1)))),
    he_hdr.seq (he_cp1.seq (he_cp2.seq (he_init.seq (he_ins.seq he_dv)))),
    ⟨hy_bnd,
      (hy_out zero (by fin15) (by fin15)).trans hx₁_z,
      (hy_out one (by fin15) (by fin15)).trans hx₁_o,
      (hy_out three (by fin15) (by fin15)).trans hx₁_3,
      (hy_out nReg (by fin15) (by fin15)).trans hx₁_n,
      (hy_out eb (by fin15) (by fin15)).trans hx₁_eb,
      (hy_out db (by fin15) (by fin15)).trans hx₁_db,
      fun a ha => by
        rw [hlow_mem a (by unfold pqBase; omega), hx₁_m, Function.update_of_ne (by omega)],
      ⟨s₀, hr_y, hsync_y, ?_, ?_⟩⟩,
    ?_, ?_⟩
  · have hdv_y : y.regs dv = 0 := rfl
    simp only [hdv_y, true_iff]
    exact hdom_ne
  · rw [hvis_y, hdist_y]
    exact Instance.Inv.init G.toInstance
  · rw [hpot_y]
    rw [hpot0_eq] at hpot₃
    omega
  · change C.potential (y.comap pqMap) +
        (pkg.extractTime G.n + pkg.emptyTime G.n + 20) *
          min (G.n - (visitedSet G (stateOf C y) y).card)
            (remEdges G (visitedSet G (stateOf C y) y) +
              (IndexedMinPQ.dom (stateOf C y)).card) +
        (pkg.insertTime G.n + 20) *
          min (G.n - (visitedSet G (stateOf C y) y).card -
            (IndexedMinPQ.dom (stateOf C y)).card)
            (remEdges G (visitedSet G (stateOf C y) y)) +
        (pkg.decreaseTime G.n + 20) * remEdges G (visitedSet G (stateOf C y) y) ≤ _
    rw [stateOf_eq C hr_y, hvis_y, hrem_emp, hcard_s₀, Finset.card_empty, Nat.sub_zero]
    have hmin1 : min (G.n - 1) G.m ≤ min G.n G.m := by omega
    have hmul_ins := Nat.mul_le_mul_left (pkg.insertTime G.n + 20) hmin1
    have hcomm1 : (pkg.extractTime G.n + pkg.emptyTime G.n + 20) * min G.n (G.m + 1) =
        min G.n (G.m + 1) * (pkg.extractTime G.n + pkg.emptyTime G.n + 20) := Nat.mul_comm _ _
    have hcomm2 : (pkg.insertTime G.n + 20) * min G.n G.m =
        min G.n G.m * (pkg.insertTime G.n + 20) := Nat.mul_comm _ _
    have hcomm3 : (pkg.decreaseTime G.n + 20) * G.m = G.m * (pkg.decreaseTime G.n + 20) :=
      Nat.mul_comm _ _
    linarith only [hmul_ins, hcomm1, hcomm2, hcomm3]

private theorem dijkstraRound_spec (pkg : PQPackage .exact r_pq) {G : ListInstance}
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (pqBase G + pkg.space G.n))
    {y : Data (15 + r_pq)} (hy : OuterInv pkg G hw_in hw_sp y)
    (hc : (Cond.eq dv zero).Holds y) :
    ∃ z T, ExecWithin w (dijkstraRound pkg.code) y z T ∧
      OuterInv pkg G hw_in hw_sp z ∧
      T + 2 + outerPot pkg G hw_in hw_sp z ≤ outerPot pkg G hw_in hw_sp y := by
  classical
  let hK := fits_pqKeyMax hw_in
  let C := pkg.cert hw_sp hK
  have hsp_eq : C.space = pkg.space G.n := pkg.cert_space hw_sp hK
  have hsp_lo : G.n + 1 ≤ C.space := hsp_eq ▸ pkg.space_lower G.n
  have hsp_pos : 1 ≤ C.space := by omega
  have hS_cert : Fits w (pqBase G + C.space) := hsp_eq ▸ hw_sp
  have harg_eq : C.argMatch = pkg.code.argMatch := pkg.cert_argMatch hw_sp hK
  have hdec_eq : C.decode = pkg.code.decode := pkg.cert_decode hw_sp hK
  obtain ⟨s, hr, hsync, hdv_iff, hinv⟩ := hy.pq
  have hdv0 : y.regs dv = 0 := by
    simp only [Cond.holds_eq, hy.zero_eq] at hc
    exact hc
  have hdom_ne : IndexedMinPQ.dom s ≠ ∅ := hdv_iff.mp hdv0
  have hfm_ne : IndexedMinPQ.findMin s ≠ none :=
    mt IndexedMinPQ.findMin_eq_none_iff.mp hdom_ne
  obtain ⟨⟨U, B⟩, hfm⟩ : ∃ uk, IndexedMinPQ.findMin s = some uk :=
    Option.ne_none_iff_exists'.mp hfm_ne
  have hsU : s U = some B := IndexedMinPQ.findMin_eq_some_state hfm
  have hU_dom : U ∈ IndexedMinPQ.dom s := IndexedMinPQ.findMin_mem_dom hfm
  obtain ⟨hdU_ne, hsU_mem⟩ := hsync U hU_dom
  have hB_mem : y.mem (G.dbase + U) = B := Option.some.inj (hsU_mem.symm.trans hsU)
  have hB_ne : B ≠ 0 := hB_mem ▸ hdU_ne
  obtain ⟨x₁, t_ext, he_ext, hdec_ext, hr₁_raw, hmod_ext, hregs_ext, hpot_ext⟩ :=
    pkg.code.callExtractMin_exec C hsp_pos hS_cert harg_eq hdec_eq pqMap_injective hr hy.one_eq
  simp only [IndexedMinPQ.spec, hfm] at hdec_ext hr₁_raw
  let s₁ : IndexedMinPQ.State G.n := Function.update s U none
  have hr₁ : C.rep s₁ (x₁.comap pqMap) := hr₁_raw
  have hx₁_outV_K : x₁.regs (pqMap pkg.code.outV) = U.val ∧
      x₁.regs (pqMap pkg.code.outK) = B := by
    dsimp only [PQCode.decode, Data.comap, Function.comp_apply] at hdec_ext
    by_cases hfl : x₁.regs (pqMap pkg.code.outFlag) = 0
    · simp only [hfl, ↓reduceIte] at hdec_ext
      nomatch hdec_ext
    · simp only [hfl, ↓reduceIte] at hdec_ext
      by_cases hlt : x₁.regs (pqMap pkg.code.outV) < G.n
      · simp only [hlt, ↓reduceDIte] at hdec_ext
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj (Option.some.inj hdec_ext))
        exact ⟨congrArg Fin.val h1, h2⟩
      · simp only [hlt, ↓reduceDIte] at hdec_ext
        nomatch hdec_ext
  have hx₁_low : ∀ a < pqBase G, x₁.mem a = y.mem a := fun a ha =>
    hmod_ext a (by rw [Block.mem_footprint]; dsimp only [Block.Owns]; omega)
  have hx₁_out : ∀ i : Fin (15 + r_pq), i.val < 15 → x₁.regs i = y.regs i := fun i hi =>
    hregs_ext i (outer_notMem_pqMap hi)
  let x₁' := x₁.set u U.val
  let x₂ := x₁'.set best B
  have he_u : ExecWithin (B := .exact) w (.op (.copy u (pqMap pkg.code.outV))) x₁ x₁' 1 := by
    dsimp only [x₁']
    rw [← hx₁_outV_K.1]
    exact ExecWithin.copy
  have he_b : ExecWithin (B := .exact) w (.op (.copy best (pqMap pkg.code.outK))) x₁' x₂ 1 := by
    have hk_eq : x₁'.regs (pqMap pkg.code.outK) = B := by
      rw [Data.set_regs, Function.update_of_ne (fun h => outer_notMem_pqMap (by fin15) ⟨_, h⟩)]
      exact hx₁_outV_K.2
    dsimp only [x₂]
    rw [← hk_eq]
    exact ExecWithin.copy
  have hU_lt := U.isLt
  have hf_off0 : Fits w ((U : ℕ) + 3) :=
    hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have hf_off1 : Fits w ((U : ℕ) + 3 + 1) :=
    hw_sp.of_le (by unfold pqBase ListInstance.dbase; omega)
  have hx₂_in : ∀ a < G.dbase, x₂.mem a = (Data.init G.encode : Data (15 + r_pq)).mem a :=
    fun a ha => (hx₁_low a (by unfold pqBase; omega)).trans (hy.input a ha)
  have hoff₀ : x₂.mem ((U : ℕ) + 3) = G.offset U := by
    rw [hx₂_in _ (by unfold ListInstance.dbase; omega), G.init_offset (by omega)]
  have hoff₁ : x₂.mem ((U : ℕ) + 3 + 1) = G.offset ((U : ℕ) + 1) := by
    rw [hx₂_in _ (by unfold ListInstance.dbase; omega),
      show (U : ℕ) + 3 + 1 = (U : ℕ) + 1 + 3 by omega, G.init_offset (by omega)]
  have hx₂_3 : x₂.regs three = 3 := by
    have h : x₂.regs three = x₁.regs three := rfl
    exact h.trans ((hx₁_out three (by fin15)).trans hy.three_eq)
  have hx₂_1 : x₂.regs one = 1 := by
    have h : x₂.regs one = x₁.regs one := rfl
    exact h.trans ((hx₁_out one (by fin15)).trans hy.one_eq)
  have hx₂_u : x₂.regs u = U.val := rfl
  obtain ⟨x₃, he_off, hx₃_m, hx₃_j, hx₃_jend, hx₃_fr⟩ :
      ∃ x₃, ExecWithin w loadOffsets x₂ x₃ 4 ∧ x₃.mem = x₂.mem ∧
        x₃.regs j = G.offset U ∧ x₃.regs jend = G.offset ((U : ℕ) + 1) ∧
        ∀ i ∉ [t, j, jend], x₃.regs i = x₂.regs i := by
    refine ⟨?z_off, ?e_off, ?_, ?_, ?_, ?_⟩
    case e_off =>
      ram_exact_eval [loadOffsets, hx₂_u, hx₂_3, hx₂_1, hoff₀, hoff₁, hf_off0, hf_off1, Fin.ext_iff]
    · rfl
    · rfl
    · rfl
    · intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      simp only [Data.set_regs, Function.update_of_ne hi.2.2, Function.update_of_ne hi.2.1,
        Function.update_of_ne hi.1]
  have hx₃_bnd : x₃.Bounded w :=
    he_off.bounded (he_b.bounded (he_u.bounded (he_ext.bounded hy.bounded)))
  have hx₃_pq : ∀ k, x₃.regs (pqMap k) = x₁.regs (pqMap k) := by
    intro k
    have hk : ∀ i : Fin (15 + r_pq), i.val < 15 → pqMap k ≠ i :=
      fun i hi h => outer_notMem_pqMap hi ⟨k, h⟩
    rw [hx₃_fr (pqMap k) (by simp [hk t (by fin15), hk j (by fin15), hk jend (by fin15)])]
    simp only [x₂, x₁', Data.set_regs, Function.update_of_ne (hk best (by fin15)),
      Function.update_of_ne (hk u (by fin15))]
  obtain ⟨hr₃, hpot₃⟩ := frame_outer_regs C hr₁ hx₃_bnd hx₃_pq hx₃_m
  have hx₃_D : ∀ v : Fin G.n, x₃.mem (G.dbase + v) = y.mem (G.dbase + v) := fun v => by
    rw [hx₃_m]
    exact hx₁_low (G.dbase + v) (by unfold pqBase; have := v.isLt; omega)
  have hdom_s₁ : IndexedMinPQ.dom s₁ = (IndexedMinPQ.dom s).erase U :=
    IndexedMinPQ.dom_erase_update s U
  have hsync₃ : PQSync G s₁ x₃ := by
    intro v hv_dom
    rw [hdom_s₁, Finset.mem_erase] at hv_dom
    rw [hx₃_D v]
    dsimp only [s₁]
    rw [Function.update_of_ne hv_dom.1]
    exact hsync v hv_dom.2
  let S_old := visitedSet G s y
  let S_vis := insert U S_old
  have hU_not_S : U ∉ S_old := by
    simp only [S_old, visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro _; exact not_not.mpr hU_dom
  have hvis₃ : visitedSet G s₁ x₃ = S_vis := by
    ext v
    simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hx₃_D v, hdom_s₁,
      Finset.mem_erase, S_vis, S_old, Finset.mem_insert]
    by_cases hv : v = U
    · subst hv
      simp [hB_mem, hB_ne]
    · simp [hv]
  -- Dijkstra invariant step on `U`
  have hdU : distWords G y U = decodeDist B := by simp [distWords, hB_mem]
  have hfinU : distWords G y U ≠ ⊤ := hdU ▸ decodeDist_ne_top hB_ne
  have hminU : ∀ v ∉ S_old, distWords G y U ≤ distWords G y v := by
    intro v hv
    simp only [S_old, visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, not_and,
      not_not] at hv
    rw [hdU]
    by_cases hd0 : y.mem (G.dbase + v) = 0
    · simp [distWords, hd0, decodeDist]
    · have hv_dom : v ∈ IndexedMinPQ.dom s := hv hd0
      have hsv := (hsync v hv_dom).2
      exact decodeDist_le hB_ne hd0 (IndexedMinPQ.findMin_key_le hfm hsv)
  have hstep_inv := Instance.Inv.step G.toInstance hinv hU_not_S hminU hfinU
  have hBC_all : ∀ e ∈ G.adj U, B + e.2 ≤ pqKeyMax G := by
    intro e he
    have hb := hinv.bound U hfinU
    rw [hdU] at hb
    simp only [decodeDist, hB_ne, ↓reduceIte] at hb
    have hb' : B - 1 ≤ S_old.card * G.toInstance.maxWeight := by exact_mod_cast hb
    have hc_le : S_old.card ≤ G.n := by simpa using Finset.card_le_univ S_old
    have hW := G.toInstance_maxWeight_le
    have he2 := G.le_maxWeight he
    have hmul := Nat.mul_le_mul hc_le hW
    unfold pqKeyMax
    omega
  have hvis_le : ∀ v ∈ S_vis, x₃.mem (G.dbase + v) ≠ 0 ∧
      ∀ c, (v, c) ∈ G.adj U → x₃.mem (G.dbase + v) ≤ B + c := by
    intro v hvS
    rw [hx₃_D v]
    rcases Finset.mem_insert.mp hvS with rfl | hv_old
    · exact ⟨hB_mem ▸ hB_ne, fun c _ => by rw [hB_mem]; omega⟩
    · have hdv_ne : y.mem (G.dbase + v) ≠ 0 := (Finset.mem_filter.mp hv_old).2.1
      refine ⟨hdv_ne, fun c hc_e => ?_⟩
      have h₁ := hstep_inv.eq_of_mem v (Finset.mem_insert_of_mem hv_old)
      have h₂ := hinv.eq_of_mem v hv_old
      obtain ⟨c', hc'⟩ : ∃ c', G.lightest U v = some c' := by
        cases h : G.lightest U v with
        | none => exact absurd hc_e ((G.lightest_eq_none_iff.mp h) c)
        | some c' => exact ⟨c', rfl⟩
      have hle_c := (G.lightest_eq_some_iff.mp hc').2 c hc_e
      have hrel : G.toInstance.relax (distWords G y) U v =
          min (distWords G y v) (distWords G y U + c') := by
        simp only [Instance.relax, show G.toInstance.weight U v = some c' from hc']
      have hmin' : distWords G y v ≤ distWords G y U + c' := by
        rw [← min_eq_left_iff, ← hrel, h₁, h₂]
      rw [hdU] at hmin'
      simp only [distWords, decodeDist, hdv_ne, hB_ne, ↓reduceIte] at hmin'
      have : y.mem (G.dbase + v) - 1 ≤ B - 1 + c' := by exact_mod_cast hmin'
      omega
  have hx₃_out_keep : ∀ i : Fin (15 + r_pq), i.val < 15 → i ∉ [u, best, t, j, jend] →
      x₃.regs i = y.regs i := by
    intro i hi hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    rw [hx₃_fr i (by simp [hnot.2.2.1, hnot.2.2.2.1, hnot.2.2.2.2])]
    simp only [x₂, x₁', Data.set_regs, Function.update_of_ne hnot.2.1, Function.update_of_ne hnot.1]
    exact hx₁_out i hi
  let R_after := remEdges G S_vis
  obtain ⟨x₄, s', t_scan, he_scan, hx₄_bnd, hx₄_fr, hr₄, hsync₄, hvis₄, hdom₄, hx₄_word,
      hx₄_in, hpot_scan⟩ :=
    relaxEdges_spec pkg hw_in hw_sp U (R_after := R_after) hx₃_bnd
      ((hx₃_out_keep zero (by fin15) (by fin15)).trans hy.zero_eq)
      ((hx₃_out_keep one (by fin15) (by fin15)).trans hy.one_eq)
      ((hx₃_out_keep eb (by fin15) (by fin15)).trans hy.eb_eq)
      ((hx₃_out_keep db (by fin15) (by fin15)).trans hy.db_eq)
      (by rw [hx₃_fr best (by fin15)]; rfl)
      hB_ne hx₃_j hx₃_jend hBC_all (fun a ha => (hx₃_m ▸ hx₂_in a ha))
      hr₃ hsync₃ hvis₃ hvis_le
  have hx₄_z : x₄.regs zero = 0 :=
    (hx₄_fr zero (by fin15) (by fin15)).trans
      ((hx₃_out_keep zero (by fin15) (by fin15)).trans hy.zero_eq)
  obtain ⟨x₅, t_emp, he_emp, hflag₅, hr₅, hmod₅, hregs₅, hpot_emp⟩ :=
    pkg.code.callIsEmpty_exec C harg_eq hdec_eq pqMap_injective
      (outer_notMem_pqMap (by fin15)) hr₄ hx₄_z
  let z := x₅.set dv (x₅.regs (pqMap pkg.code.outFlag))
  have he_dv : ExecWithin (B := .exact) w (.op (.copy dv (pqMap pkg.code.outFlag))) x₅ z 1 :=
    ExecWithin.copy
  have hz_bnd : z.Bounded w := he_dv.bounded (he_emp.bounded hx₄_bnd)
  have hz_pq : ∀ k, z.regs (pqMap k) = x₅.regs (pqMap k) := fun k =>
    Function.update_of_ne (fun h => outer_notMem_pqMap (by fin15) ⟨k, h⟩) _ _
  obtain ⟨hr_z, hpot_z⟩ := frame_outer_regs C hr₅ hz_bnd hz_pq rfl
  have hx₅_low : ∀ a < pqBase G, x₅.mem a = x₄.mem a := fun a ha =>
    hmod₅ a (by rw [Block.mem_footprint]; dsimp only [Block.Owns]; omega)
  have hz_D : ∀ v : Fin G.n, z.mem (G.dbase + v) = x₄.mem (G.dbase + v) := fun v =>
    hx₅_low (G.dbase + v) (by unfold pqBase; have := v.isLt; omega)
  have hsync_z : PQSync G s' z := by
    intro v hv_dom
    rw [hz_D v]
    exact hsync₄ v hv_dom
  have hvis_z : visitedSet G s' z = S_vis := by
    rw [← hvis₄]
    ext v
    simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hz_D v]
  have hdist_z : distWords G z = G.toInstance.relax (distWords G y) U := by
    funext v
    change decodeDist (z.mem (G.dbase + v)) = _
    rw [hz_D v, hx₄_word v]
    exact decode_edgesWord G hB_ne hdU (by rw [hx₃_D v]; rfl)
  have hz_keep : ∀ i : Fin (15 + r_pq), i.val < 15 →
      i ∉ [u, best, j, jend, tv, tc, cand, dv, t] → z.regs i = y.regs i := by
    intro i hi hnot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnot
    have h1 : z.regs i = x₅.regs i := Function.update_of_ne hnot.2.2.2.2.2.2.2.1 _ _
    have h2 : x₅.regs i = x₄.regs i := hregs₅ i (outer_notMem_pqMap hi)
    have h3 : x₄.regs i = x₃.regs i := hx₄_fr i hi
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or];
          exact ⟨hnot.2.2.1, hnot.2.2.2.2.1, hnot.2.2.2.2.2.1, hnot.2.2.2.2.2.2.1,
            hnot.2.2.2.2.2.2.2.1, hnot.2.2.2.2.2.2.2.2⟩)
    have h4 : x₃.regs i = y.regs i := hx₃_out_keep i hi
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or];
          exact ⟨hnot.1, hnot.2.1, hnot.2.2.2.2.2.2.2.2, hnot.2.2.1, hnot.2.2.2.1⟩)
    exact h1.trans (h2.trans (h3.trans h4))
  have hz_inv : OuterInv pkg G hw_in hw_sp z := by
    refine ⟨hz_bnd,
      (hz_keep zero (by fin15) (by fin15)).trans hy.zero_eq,
      (hz_keep one (by fin15) (by fin15)).trans hy.one_eq,
      (hz_keep three (by fin15) (by fin15)).trans hy.three_eq,
      (hz_keep nReg (by fin15) (by fin15)).trans hy.n_eq,
      (hz_keep eb (by fin15) (by fin15)).trans hy.eb_eq,
      (hz_keep db (by fin15) (by fin15)).trans hy.db_eq,
      fun a ha => by
        change x₅.mem a = _
        rw [hx₅_low a (by unfold pqBase; omega), hx₄_in a ha, hx₃_m]
        exact hx₂_in a ha,
      ⟨s', hr_z, hsync_z, ?_, ?_⟩⟩
    · have hdv_z : z.regs dv = x₅.regs (pqMap pkg.code.outFlag) := rfl
      rw [hdv_z]
      exact hflag₅
    · rw [hvis_z, hdist_z]
      exact hstep_inv
  -- Amortized round accounting
  have hrem_split : remEdges G S_old = R_after + (G.adj U).length := by
    have hflt : Finset.univ.filter (· ∉ S_old) =
        insert U (Finset.univ.filter (· ∉ S_vis)) := by
      ext v
      by_cases hv : v = U
      · subst hv; simp [S_vis, hU_not_S]
      · simp [S_vis, hv]
    dsimp only [R_after, remEdges]
    rw [hflt, Finset.sum_insert (by simp [S_vis]), add_comm]
  have hS_card : S_vis.card = S_old.card + 1 := Finset.card_insert_of_notMem hU_not_S
  have hS_lt_n : S_old.card < G.n := by
    have hle : S_vis.card ≤ G.n := by simpa using Finset.card_le_univ S_vis
    omega
  have hdom_card : (IndexedMinPQ.dom s).card = (IndexedMinPQ.dom s₁).card + 1 := by
    rw [hdom_s₁]
    exact (Finset.card_erase_add_one hU_dom).symm
  have hsum_eq : G.n - S_vis.card - (IndexedMinPQ.dom s₁).card =
      G.n - S_old.card - (IndexedMinPQ.dom s).card := by omega
  have hrnd_drop : min (G.n - S_vis.card) (R_after + (IndexedMinPQ.dom s').card) + 1 ≤
      min (G.n - S_old.card) (remEdges G S_old + (IndexedMinPQ.dom s).card) := by
    rw [hrem_split, hS_card, hdom_card]
    omega
  have hchg_ext : C.charge s .extractMin ≤ pkg.extractTime G.n := pkg.charge_extractMin hw_sp hK s
  have hchg_emp : C.charge s' .isEmpty ≤ pkg.emptyTime G.n := pkg.charge_isEmpty hw_sp hK s'
  refine ⟨z, t_ext + (1 + (1 + (4 + (t_scan + (t_emp + 1))))),
    he_ext.seq (he_u.seq (he_b.seq (he_off.seq (he_scan.seq (he_emp.seq he_dv))))),
    hz_inv, ?_⟩
  change t_ext + (1 + (1 + (4 + (t_scan + (t_emp + 1))))) + 2 +
      (C.potential (z.comap pqMap) +
        (pkg.extractTime G.n + pkg.emptyTime G.n + 20) *
          min (G.n - (visitedSet G (stateOf C z) z).card)
            (remEdges G (visitedSet G (stateOf C z) z) +
              (IndexedMinPQ.dom (stateOf C z)).card) +
        (pkg.insertTime G.n + 20) *
          min (G.n - (visitedSet G (stateOf C z) z).card -
            (IndexedMinPQ.dom (stateOf C z)).card)
            (remEdges G (visitedSet G (stateOf C z) z)) +
        (pkg.decreaseTime G.n + 20) * remEdges G (visitedSet G (stateOf C z) z)) ≤
      C.potential (y.comap pqMap) +
        (pkg.extractTime G.n + pkg.emptyTime G.n + 20) *
          min (G.n - (visitedSet G (stateOf C y) y).card)
            (remEdges G (visitedSet G (stateOf C y) y) +
              (IndexedMinPQ.dom (stateOf C y)).card) +
        (pkg.insertTime G.n + 20) *
          min (G.n - (visitedSet G (stateOf C y) y).card -
            (IndexedMinPQ.dom (stateOf C y)).card)
            (remEdges G (visitedSet G (stateOf C y) y)) +
        (pkg.decreaseTime G.n + 20) * remEdges G (visitedSet G (stateOf C y) y)
  rw [stateOf_eq C hr_z, stateOf_eq C hr, hvis_z]
  change t_ext + (1 + (1 + (4 + (t_scan + (t_emp + 1))))) + 2 +
      (C.potential (z.comap pqMap) +
        (pkg.extractTime G.n + pkg.emptyTime G.n + 20) *
          min (G.n - S_vis.card) (R_after + (IndexedMinPQ.dom s').card) +
        (pkg.insertTime G.n + 20) *
          min (G.n - S_vis.card - (IndexedMinPQ.dom s').card) R_after +
        (pkg.decreaseTime G.n + 20) * R_after) ≤
      C.potential (y.comap pqMap) +
        (pkg.extractTime G.n + pkg.emptyTime G.n + 20) *
          min (G.n - S_old.card) (remEdges G S_old + (IndexedMinPQ.dom s).card) +
        (pkg.insertTime G.n + 20) *
          min (G.n - S_old.card - (IndexedMinPQ.dom s).card) (remEdges G S_old) +
        (pkg.decreaseTime G.n + 20) * remEdges G S_old
  rw [hpot_z]
  rw [hpot₃, hsum_eq, ← hrem_split] at hpot_scan
  have hmul_rnd := Nat.mul_le_mul_left (pkg.extractTime G.n + pkg.emptyTime G.n + 20) hrnd_drop
  have hmul_dec : (pkg.decreaseTime G.n + 20) * remEdges G S_old =
      (pkg.decreaseTime G.n + 20) * R_after + (pkg.decreaseTime G.n + 20) * (G.adj U).length := by
    rw [hrem_split, Nat.mul_add]
  linarith only [hpot_ext, hpot_emp, hpot_scan, hchg_ext, hchg_emp, hmul_rnd, hmul_dec]

private theorem dijkstraExit_spec (pkg : PQPackage .exact r_pq) {G : ListInstance}
    {hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2))}
    {hw_sp : Fits w (pqBase G + pkg.space G.n)}
    {y : Data (15 + r_pq)} (hy : OuterInv pkg G hw_in hw_sp y)
    (hc : ¬(Cond.eq dv zero).Holds y) (v : Fin G.n) :
    y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨s, _, _, hdv_iff, hinv⟩ := hy.pq
  have hdv_ne : y.regs dv ≠ 0 := by
    simp only [Cond.holds_eq, hy.zero_eq] at hc
    exact hc
  have hdom_emp : IndexedMinPQ.dom s = ∅ := Decidable.byContradiction fun hne =>
    hdv_ne (hdv_iff.mpr hne)
  have hdone : ∀ u_v ∉ visitedSet G s y, distWords G y u_v = ⊤ := by
    intro u_v huv
    simp only [visitedSet, Finset.mem_filter, Finset.mem_univ, true_and, hdom_emp,
      Finset.notMem_empty, not_false_eq_true, and_true, not_not] at huv
    simp [distWords, huv, decodeDist]
  have heq := Instance.Inv.eq_dist G.toInstance hinv hdone v
  change y.mem (G.dbase + v) = encodeDist (G.toInstance.dist G.toInstance.source v)
  rw [← heq]
  exact (encodeDist_decodeDist _).symm

/-- **Black-box structured Dijkstra theorem.** For any exact-basis `PQPackage`, `dijkstraCode`
computes all encoded shortest-path distances within
`initTime + insertTime + 28 + min(n, m + 1) * (extractTime + emptyTime + 20) +`
`min(n, m) * (insertTime + 20) + m * (decreaseTime + 20)` instructions. -/
theorem dijkstraCode_exec (pkg : PQPackage .exact r_pq) (G : ListInstance) (w : ℕ)
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (G.dbase + G.n + pkg.space G.n)) :
    ∃ y, ExecWithin w (dijkstraCode pkg.code) (.init G.encode) y
        (pkg.initTime G.n + pkg.insertTime G.n + 28 +
          min G.n (G.m + 1) * (pkg.extractTime G.n + pkg.emptyTime G.n + 20) +
          min G.n G.m * (pkg.insertTime G.n + 20) +
          G.m * (pkg.decreaseTime G.n + 20)) ∧
      ∀ v : Fin G.n, y.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  obtain ⟨x, t_set, he_set, hx_inv, hset_le, hpot_le⟩ := dijkstraSetup_spec pkg hw_in hw_sp
  obtain ⟨y, he_loop, hy_inv, hc_exit⟩ :=
    ExecWithin.loop_potential (OuterInv pkg G hw_in hw_sp) (outerPot pkg G hw_in hw_sp)
      (fun _ h hc => dijkstraRound_spec pkg hw_in hw_sp h hc) hx_inv
  refine ⟨y, (he_set.seq he_loop).mono ?_, fun v => dijkstraExit_spec pkg hy_inv hc_exit v⟩
  linarith only [hset_le, hpot_le]

/-- **Black-box flat-program Dijkstra theorem.** Compiling `dijkstraCode pkg.code` produces a flat
word-RAM program over `Basis.exact` that computes all single-source shortest-path distances and
halts within the parameterized priority-queue instruction bound. -/
theorem dijkstra_of_pq_spec (pkg : PQPackage .exact r_pq) (G : ListInstance) (w : ℕ)
    (hw_in : Fits w (8 * (G.n + G.m + 2) * (G.maxWeight + 2)))
    (hw_sp : Fits w (G.dbase + G.n + pkg.space G.n)) :
    let p := (dijkstraCode pkg.code).program OuterReg.zero
    ∃ t steps, Runs w p (.init G.encode) t steps ∧
      (∃ v, step w p t = .halt v) ∧
      steps ≤ pkg.initTime G.n + pkg.insertTime G.n + 28 +
        min G.n (G.m + 1) * (pkg.extractTime G.n + pkg.emptyTime G.n + 20) +
        min G.n G.m * (pkg.insertTime G.n + 20) +
        G.m * (pkg.decreaseTime G.n + 20) ∧
      ∀ v : Fin G.n, t.data.mem (G.outAddr v) = encodeDist (G.dist G.source v) := by
  intro p
  obtain ⟨y, ⟨steps, hsteps, he⟩, hd⟩ := dijkstraCode_exec pkg G w hw_in hw_sp
  have hr := he.runs (pc := 0) (p := p) (Program.Contains.self _).append_left
  rw [Nat.zero_add] at hr
  refine ⟨⟨(dijkstraCode pkg.code).size, y⟩, steps, hr, ⟨y.regs OuterReg.zero, ?_⟩, hsteps, hd⟩
  exact step_halt (by simp [p, Code.program])

end OuterAlgorithm

end Cslib.Algorithms.WordRAM.Dijkstra
