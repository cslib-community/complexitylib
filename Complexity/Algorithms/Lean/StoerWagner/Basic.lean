/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.Karger.Graph
public import Complexity.Foundations.Combinatorics.WeightedCut.MAOrdering
public import Cslib.Algorithms.Lean.TimeM
import Mathlib.Tactic.Linarith

/-!
# The Stoer–Wagner minimum cut algorithm

The Stoer–Wagner algorithm [StoerWagner1997] computes a global minimum cut of a weighted
multigraph `W : Fin n → Fin n → ℕ` (`Cslib.WeightedCut.IsMultigraph`) deterministically. Each
*phase* computes a maximum adjacency ordering of the current supervertices by maximum adjacency
search (`Cslib.WeightedCut.maSearch`), records the *cut of the phase*, the cut `{t}` of its last
vertex `t`, and merges `t` into the second to last vertex `s`. After `n - 1` phases one supervertex
is left, and the lightest cut of the phase is a global minimum cut.

Correctness has two parts. By the MA-ordering lemma
(`Cslib.WeightedCut.cutWeight_singleton_le_of_isMAOrdering`), the cut of the phase weighs at most
every cut separating `s` and `t`. A cut not separating `s` and `t` survives merging them with the
same weight (`cutWeight_contractCut`), so the minimum cut weight is the smaller of the weight of the
cut of the phase and the minimum cut weight after the merge (`minCut_eq_min_contractMatrix`, the
phase recursion of [StoerWagner1997]). Contraction is `Karger.Graph`'s (`contractMatrix`,
`contractPart`), which keeps the supervertices as `Fin m` and moves the last one into the freed
slot.

## Main definitions

* `Cslib.Algorithms.Lean.StoerWagner.maOrder`: a maximum adjacency ordering of `Fin k`.
* `Cslib.Algorithms.Lean.StoerWagner.run`: the phases on the supervertices of a contraction.
* `Cslib.Algorithms.Lean.StoerWagner.stoerWagner`: the algorithm, answering one side of a minimum
  cut and its weight.
* `Cslib.Algorithms.Lean.StoerWagner.stoerWagnerM`: the algorithm in `TimeM`, with a cost model.

## Main results

* `Cslib.Algorithms.Lean.StoerWagner.minCut_eq_min_contractMatrix`: the phase recursion.
* `Cslib.Algorithms.Lean.StoerWagner.minCut_eq_min_of_isMAOrdering`: one phase.
* `Cslib.Algorithms.Lean.StoerWagner.stoerWagner_spec`: the algorithm answers a non-trivial cut of
  minimum weight, and its weight.
* `Cslib.Algorithms.Lean.StoerWagner.time_stoerWagnerM_le`: at most `n ^ 3 + 2 n ^ 2` steps.

## Cost model

`stoerWagnerM` charges unit cost per scanned entry of an array implementation with machine-word
arithmetic on weights, as the `TimeM` annotations of the other algorithms here do; the charges are
`TimeM.tick` annotations in the program, not derived from the Lean evaluation, which uses
closures. A search step on `r` remaining candidates costs `2 r - 1`: a scan for the largest key and
an update of the other `r - 1` keys, so a phase on `m` supervertices of a graph on `n` vertices
costs `m ^ 2` for the search. Recording the cut of the phase costs `m + n` (its degree, and the
vertex set of the original graph mapped to `t`), and the merge costs `2 m + n + 1` (merging a row
and a column, relabelling the original vertices, comparing two weights). This is the `O(n³)`
array version of the algorithm; the `O(n m + n² log n)` bound of [StoerWagner1997] uses Fibonacci
heaps and is not formalized here.

## Limitations

Weights are natural numbers, as in `Cslib.WeightedCut`; rational weights can be scaled to natural
numbers, real weights are not covered. The algorithm answers one minimum cut, not all of them.

## References

* [M. Stoer and F. Wagner, *A Simple Min-Cut Algorithm*][StoerWagner1997]
* [H. Nagamochi and T. Ibaraki, *Computing Edge-Connectivity in Multigraphs and Capacitated
  Graphs*][NagamochiIbaraki1992]
-/

public section

namespace Cslib.Algorithms.Lean.StoerWagner

open Cslib.WeightedCut Cslib.Algorithms.WordRAM.Karger

/-! ### The algorithm -/

/-- A maximum adjacency ordering of `Fin k`, by maximum adjacency search starting from vertex `0`
(ties broken towards smaller vertices). -/
def maOrder {k : ℕ} (W : Fin k → Fin k → ℕ) : List (Fin k) :=
  maSearch W k (fun _ => 0) (List.finRange k)

private theorem maOrder_spec {k : ℕ} (W : Fin k → Fin k → ℕ) :
    (maOrder W).Perm (List.finRange k) ∧ IsMAOrderingFrom W ∅ (maOrder W) :=
  maSearch_spec W k (fun _ => 0) ∅ (List.finRange k)
    (List.nodup_finRange k) (by simp) (fun y => by simp) (by simp)

/-- `maOrder W` lists every vertex once. -/
theorem perm_maOrder {k : ℕ} (W : Fin k → Fin k → ℕ) : (maOrder W).Perm (List.finRange k) :=
  (maOrder_spec W).1

/-- `maOrder W` is a maximum adjacency ordering. -/
theorem isMAOrdering_maOrder {k : ℕ} (W : Fin k → Fin k → ℕ) : IsMAOrdering W (maOrder W) :=
  ⟨(perm_maOrder W).nodup_iff.mpr (List.nodup_finRange k),
    fun v => (perm_maOrder W).mem_iff.mpr (List.mem_finRange v), (maOrder_spec W).2⟩

/-- The last two entries `(s, t)` of a list, and `(d, d)` for shorter lists. -/
def lastTwo {α : Type*} (d : α) (l : List α) : α × α :=
  match l.reverse with
  | t :: s :: _ => (s, t)
  | _ => (d, d)

/-- A list of length at least two ends with the two entries of `lastTwo`. -/
theorem exists_eq_append_lastTwo {α : Type*} (d : α) {l : List α} (hl : 2 ≤ l.length) :
    ∃ p, l = p ++ [(lastTwo d l).1, (lastTwo d l).2] := by
  unfold lastTwo
  rcases h : l.reverse with _ | ⟨t, _ | ⟨s, r⟩⟩
  · rw [List.reverse_eq_nil_iff] at h
    subst h
    simp at hl
  · have := congrArg List.length h
    simp only [List.length_reverse, List.length_singleton] at this
    omega
  · refine ⟨r.reverse, ?_⟩
    rw [← List.reverse_reverse l, h]
    simp

/-- The answer of the algorithm: one side of a cut, and the weight of the cut. -/
structure CutResult (n : ℕ) where
  /-- One side of the cut. -/
  side : Finset (Fin n)
  /-- The weight of the cut. -/
  weight : ℕ
  deriving DecidableEq

/-- The phases of the algorithm on the supervertices `Fin (k + 2)` of the contraction
`part : Fin n → Fin (k + 2)` of the input. A phase computes a maximum adjacency ordering, ending
with `s, t`, and merges `t` into `s`; the answer is the cut of the phase, the original vertices
mapped to `t`, unless the phases after the merge find a cut at most as heavy. With two
supervertices left the cut of the single phase is that of supervertex `1`. -/
def run {n : ℕ} : (k : ℕ) → (Fin (k + 2) → Fin (k + 2) → ℕ) → (Fin n → Fin (k + 2)) →
    CutResult n
  | 0, W, part => ⟨pullbackCut part {1}, rowDeg W 1⟩
  | k + 1, W, part =>
    let st := lastTwo 0 (maOrder W)
    let phase : CutResult n := ⟨pullbackCut part {st.2}, rowDeg W st.2⟩
    if hst : st.1 = st.2 then phase else
      let rest := run k (contractMatrix W st.1 st.2) (contractPart part st.1 st.2 hst)
      if rest.weight ≤ phase.weight then rest else phase

/-- **The Stoer–Wagner algorithm** [StoerWagner1997]: one side of a minimum cut of the multigraph
`W` on `Fin n`, and its weight. With fewer than two vertices there is no non-trivial cut, and the
answer is `(∅, 0)`. -/
def stoerWagner : {n : ℕ} → (Fin n → Fin n → ℕ) → CutResult n
  | 0, _ => ⟨∅, 0⟩
  | 1, _ => ⟨∅, 0⟩
  | n + 2, W => run n W id

/-! ### Correctness -/

private theorem pullbackCut_id {n : ℕ} (C : Finset (Fin n)) : pullbackCut id C = C := by
  ext x
  simp [pullbackCut]

/-- Merging `t` into `s` preserves the weight of the cuts that do not separate `s` and `t`. -/
theorem cutWeight_contractCut {k : ℕ} {W : Fin (k + 1) → Fin (k + 1) → ℕ} (hW : IsMultigraph W)
    {s t : Fin (k + 1)} (hst : s ≠ t) {C : Finset (Fin (k + 1))} (hC : s ∈ C ↔ t ∈ C) :
    cutWeight (contractMatrix W s t) (contractCut t C) = cutWeight W C := by
  have hc := isContractionOf_contract (isContractionOf_id hW) hst
  rw [← cutWeight_pullbackCut hc, pullbackCut_contractCut id hst hC, pullbackCut_id]

/-- **The phase recursion** of [StoerWagner1997]: if `X` is a minimum cut separating `s` and `t`,
the global minimum cut weight is the smaller of the weight of `X` and the global minimum cut weight
after merging `t` into `s`. -/
theorem minCut_eq_min_contractMatrix {k : ℕ} {W : Fin (k + 3) → Fin (k + 3) → ℕ}
    (hW : IsMultigraph W) {s t : Fin (k + 3)} (hst : s ≠ t) {X : Finset (Fin (k + 3))}
    (hX : s ∈ X ↔ t ∉ X) (hmin : ∀ Y, (s ∈ Y ↔ t ∉ Y) → cutWeight W X ≤ cutWeight W Y) :
    minCut W = min (cutWeight W X) (minCut (contractMatrix W s t)) := by
  have hc := isContractionOf_contract (isContractionOf_id hW) hst
  have hXnt : IsNonTrivialCut X := by
    by_cases hs : s ∈ X
    · exact ⟨⟨s, hs⟩, fun h => hX.mp hs (h ▸ Finset.mem_univ t)⟩
    · have ht : t ∈ X := by tauto
      exact ⟨⟨t, ht⟩, fun h => hs (h ▸ Finset.mem_univ s)⟩
  refine le_antisymm (le_min (minCut_le_cutWeight W hXnt)
    (minCut_le_of_isContractionOf (by simp) hc)) ?_
  obtain ⟨C, hCnt, hCw⟩ := exists_minCut_achiever (by simp) W
  rw [← hCw]
  by_cases hsep : s ∈ C ↔ t ∉ C
  · exact (min_le_left _ _).trans (hmin C hsep)
  · have hsame : s ∈ C ↔ t ∈ C := by tauto
    have hpull : pullbackCut (contractPart id s t hst) (contractCut t C) = C := by
      rw [pullbackCut_contractCut id hst hsame, pullbackCut_id]
    have hBnt : IsNonTrivialCut (contractCut t C) :=
      isNonTrivialCut_of_pullbackCut _ (hpull ▸ hCnt)
    refine (min_le_right _ _).trans ((minCut_le_cutWeight _ hBnt).trans (le_of_eq ?_))
    exact cutWeight_contractCut hW hst hsame

/-- **One phase**: for the last two vertices `s, t` of a maximum adjacency ordering, the global
minimum cut weight is the smaller of the weight of the cut of the phase `{t}` and the global
minimum cut weight after merging `t` into `s`. -/
theorem minCut_eq_min_of_isMAOrdering {k : ℕ} {W : Fin (k + 3) → Fin (k + 3) → ℕ}
    (hW : IsMultigraph W) {p : List (Fin (k + 3))} {s t : Fin (k + 3)}
    (hl : IsMAOrdering W (p ++ [s, t])) :
    minCut W = min (cutWeight W {t}) (minCut (contractMatrix W s t)) := by
  have hst : s ≠ t := by simpa using (List.nodup_append.mp hl.nodup).2.1
  exact minCut_eq_min_contractMatrix hW hst (by simp [hst])
    fun Y hY => cutWeight_singleton_le_of_isMAOrdering hW hl hY

/-- The phases on a contraction of `W₀` answer a non-trivial cut of `W₀` with its weight, and that
weight is the global minimum cut weight of the contraction. -/
theorem run_spec {n : ℕ} {W₀ : Fin n → Fin n → ℕ} :
    ∀ (k : ℕ) {W : Fin (k + 2) → Fin (k + 2) → ℕ} {part : Fin n → Fin (k + 2)},
      IsContractionOf W₀ part W →
      IsNonTrivialCut (run k W part).side ∧ cutWeight W₀ (run k W part).side =
        (run k W part).weight ∧ (run k W part).weight = minCut W
  | 0, W, part, hC => by
    have hW := hC.multigraph
    refine ⟨isNonTrivialCut_pullbackCut hC.surj (isNonTrivialCut_singleton (by simp) 1), ?_, ?_⟩
    · simp only [run]
      rw [cutWeight_pullbackCut hC, cutWeight_singleton hW]
    · simp only [run]
      refine le_antisymm ?_ (minCut_le_rowDeg (by simp) hW 1)
      rw [le_minCut_iff (by simp)]
      intro B hB
      rw [cutWeight_fin_two hW hB, ← cutWeight_singleton hW,
        ← cutWeight_fin_two hW (isNonTrivialCut_singleton (by simp) 1)]
  | k + 1, W, part, hC => by
    have hW := hC.multigraph
    have hl := isMAOrdering_maOrder W
    have hlen : 2 ≤ (maOrder W).length := by
      rw [(perm_maOrder W).length_eq]
      simp
    obtain ⟨p, hp⟩ := exists_eq_append_lastTwo 0 hlen
    rw [hp] at hl
    have hst : (lastTwo 0 (maOrder W)).1 ≠ (lastTwo 0 (maOrder W)).2 := by
      simpa using (List.nodup_append.mp hl.nodup).2.1
    have hphase := minCut_eq_min_of_isMAOrdering hW hl
    rw [cutWeight_singleton hW] at hphase
    obtain ⟨ih1, ih2, ih3⟩ := run_spec k (isContractionOf_contract hC hst)
    have hpt : cutWeight W₀ (pullbackCut part {(lastTwo 0 (maOrder W)).2}) =
        rowDeg W (lastTwo 0 (maOrder W)).2 := by
      rw [cutWeight_pullbackCut hC, cutWeight_singleton hW]
    have hpnt : IsNonTrivialCut (pullbackCut part {(lastTwo 0 (maOrder W)).2}) :=
      isNonTrivialCut_pullbackCut hC.surj (isNonTrivialCut_singleton (by simp) _)
    simp only [run, dite_eq_right hst]
    split_ifs with hle
    · refine ⟨ih1, ih2, ?_⟩
      rw [hphase, ← ih3, min_eq_right hle]
    · refine ⟨hpnt, hpt, ?_⟩
      dsimp only at hle ⊢
      rw [hphase, min_eq_left (by omega)]

/-- **Correctness of the Stoer–Wagner algorithm** [StoerWagner1997]: on a multigraph with at least
two vertices it answers a non-trivial cut of minimum weight, and the weight of that cut. -/
theorem stoerWagner_spec {n : ℕ} (hn : 2 ≤ n) {W : Fin n → Fin n → ℕ} (hW : IsMultigraph W) :
    IsNonTrivialCut (stoerWagner W).side ∧ cutWeight W (stoerWagner W).side = minCut W ∧
      (stoerWagner W).weight = minCut W := by
  obtain _ | _ | n := n
  · omega
  · omega
  obtain ⟨h1, h2, h3⟩ := run_spec n (isContractionOf_id hW)
  exact ⟨h1, h2.trans h3, h3⟩

/-! ### Cost -/

open Cslib.Algorithms.Lean (TimeM)

variable {V : Type*} [DecidableEq V]

/-- Maximum adjacency search (`Cslib.WeightedCut.maSearch`) in `TimeM`: a step on `r` remaining
candidates costs `2 r - 1`, a scan for the largest key and an update of the other keys. -/
def maSearchM (W : V → V → ℕ) : ℕ → (V → ℕ) → List V → TimeM ℕ (List V)
  | 0, _, _ => pure []
  | fuel + 1, key, R =>
    match R.argmax key with
    | none => pure []
    | some v => do
      TimeM.tick (2 * R.length - 1)
      let rest ← maSearchM W fuel (fun y => key y + W v y) (R.erase v)
      pure (v :: rest)

/-- `maSearchM` computes `maSearch`. -/
theorem ret_maSearchM (W : V → V → ℕ) :
    ∀ fuel key R, (maSearchM W fuel key R).ret = maSearch W fuel key R
  | 0, _, _ => rfl
  | fuel + 1, key, R => by
    rw [maSearchM, maSearch]
    rcases R.argmax key with _ | v
    · rfl
    · simp only [TimeM.ret_bind, TimeM.ret_pure, ret_maSearchM W fuel]

/-- Maximum adjacency search over `r` candidates costs at most `r ^ 2`. -/
theorem time_maSearchM_le (W : V → V → ℕ) :
    ∀ fuel key R, (maSearchM W fuel key R).time ≤ R.length ^ 2
  | 0, _, _ => by simp [maSearchM]
  | fuel + 1, key, R => by
    rw [maSearchM]
    rcases harg : R.argmax key with _ | v
    · simp
    · have hvR : v ∈ R := List.argmax_mem harg
      have ih := time_maSearchM_le W fuel (fun y => key y + W v y) (R.erase v)
      rw [List.length_erase_of_mem hvR] at ih
      obtain ⟨m, hm⟩ : ∃ m, R.length = m + 1 := ⟨R.length - 1, by
        have := List.length_pos_of_mem hvR
        omega⟩
      have hstep : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
      rw [hm, Nat.add_sub_cancel] at ih
      simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure, hm, hstep]
      nlinarith

/-- `maOrder` in `TimeM`. -/
def maOrderM {k : ℕ} (W : Fin k → Fin k → ℕ) : TimeM ℕ (List (Fin k)) :=
  maSearchM W k (fun _ => 0) (List.finRange k)

/-- `maOrderM` computes `maOrder`. -/
theorem ret_maOrderM {k : ℕ} (W : Fin k → Fin k → ℕ) : (maOrderM W).ret = maOrder W :=
  ret_maSearchM W k _ _

/-- A maximum adjacency ordering of `k` supervertices costs at most `k ^ 2`. -/
theorem time_maOrderM_le {k : ℕ} (W : Fin k → Fin k → ℕ) : (maOrderM W).time ≤ k ^ 2 := by
  have := time_maSearchM_le W k (fun _ => 0) (List.finRange k)
  rwa [List.length_finRange] at this

/-- `run` in `TimeM`, with the charges of the cost model. -/
def runM {n : ℕ} : (k : ℕ) → (Fin (k + 2) → Fin (k + 2) → ℕ) → (Fin n → Fin (k + 2)) →
    TimeM ℕ (CutResult n)
  | 0, W, part => do
    TimeM.tick (2 + n)
    pure ⟨pullbackCut part {1}, rowDeg W 1⟩
  | k + 1, W, part => do
    let order ← maOrderM W
    let st := lastTwo 0 order
    TimeM.tick (k + 3 + n)
    let phase : CutResult n := ⟨pullbackCut part {st.2}, rowDeg W st.2⟩
    if hst : st.1 = st.2 then pure phase else do
      TimeM.tick (2 * (k + 3) + n + 1)
      let rest ← runM k (contractMatrix W st.1 st.2) (contractPart part st.1 st.2 hst)
      pure (if rest.weight ≤ phase.weight then rest else phase)

/-- `runM` computes `run`. -/
theorem ret_runM {n : ℕ} :
    ∀ (k : ℕ) (W : Fin (k + 2) → Fin (k + 2) → ℕ) (part : Fin n → Fin (k + 2)),
      (runM k W part).ret = run k W part
  | 0, W, part => rfl
  | k + 1, W, part => by
    rw [runM, run, TimeM.ret_bind]
    generalize hord : (maOrderM W).ret = ord
    rw [ret_maOrderM] at hord
    subst hord
    dsimp only
    split
    · rfl
    · simp only [TimeM.ret_bind, TimeM.ret_pure, ret_runM k]

/-- The phases on `k + 2` supervertices of a contraction of a graph on `n` vertices cost at most
`(k + 2) ^ 3 + 2 n (k + 2)`. -/
theorem time_runM_le {n : ℕ} : ∀ (k : ℕ) (W : Fin (k + 2) → Fin (k + 2) → ℕ)
    (part : Fin n → Fin (k + 2)), (runM k W part).time ≤ (k + 2) ^ 3 + 2 * n * (k + 2)
  | 0, W, part => by
    simp only [runM, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    nlinarith
  | k + 1, W, part => by
    have hs := time_maOrderM_le W
    simp only [runM, TimeM.time_bind, TimeM.time_tick]
    split_ifs with hst
    · simp only [TimeM.time_pure]
      nlinarith
    · have ih := time_runM_le k (contractMatrix W (lastTwo 0 (maOrderM W).ret).1
        (lastTwo 0 (maOrderM W).ret).2) (contractPart part _ _ hst)
      simp only [TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
      nlinarith

/-- `stoerWagner` in `TimeM`, with the charges of the cost model. -/
def stoerWagnerM : {n : ℕ} → (Fin n → Fin n → ℕ) → TimeM ℕ (CutResult n)
  | 0, _ => pure ⟨∅, 0⟩
  | 1, _ => pure ⟨∅, 0⟩
  | n + 2, W => runM n W id

/-- `stoerWagnerM` computes `stoerWagner`. -/
theorem ret_stoerWagnerM {n : ℕ} (W : Fin n → Fin n → ℕ) :
    (stoerWagnerM W).ret = stoerWagner W := by
  obtain _ | _ | n := n
  · rfl
  · rfl
  · exact ret_runM n W id

/-- **The cost of the Stoer–Wagner algorithm**: at most `n ^ 3 + 2 n ^ 2` steps on `n` vertices in
the cost model of the module docstring. -/
theorem time_stoerWagnerM_le {n : ℕ} (W : Fin n → Fin n → ℕ) :
    (stoerWagnerM W).time ≤ n ^ 3 + 2 * n ^ 2 := by
  obtain _ | _ | n := n
  · simp [stoerWagnerM]
  · simp [stoerWagnerM]
  · have := time_runM_le n W id
    simp only [stoerWagnerM]
    nlinarith

end Cslib.Algorithms.Lean.StoerWagner
