/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.ClockedTable
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PairedPorts
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.FairCoin.PairedPorts.LogSpace
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.CounterBounds

/-!
# Paired-port time-layered reduction for randomized logarithmic space

Connects the abstract `Matrix.PairedPorts` algebraic structure to the concrete natural-number port
routines (`clockedOutPort`, `clockedInPort`, `clockedOutCount`) and their deterministic
logarithmic-space computability certificates, completing the Lemma 2.1 reduction of
[OpenAI2026LogSpace] for both `BPL` and `RL`.

On every input word `w`, the ambient compact transition matrix `compactCoinMatrix` admits a
canonical `Matrix.PairedPorts` structure of outgoing port degree `2` and constant incoming port
degree `inPortBound machine`. Lifting along `Matrix.PairedPorts.finTimeLayer` produces the paired
ports of the strict-upper-triangular clocked matrix `finTimeLayer T (compactCoinMatrix ...)` whose
port lookups, multiplicities, start vertex, and terminal rewards agree identically with the
logarithmic-space computable functions on natural-number identifiers.

The resulting family of finite paired-port substochastic linear systems is packaged in
`Cslib.Complexity.PairedTimeLayerFamily`, decoupling downstream derandomization arguments from
Turing-machine register encodings.

## Main definitions

* `Turing.MultiTapePTM.ConfigurationGraph.compactPairedPorts`: paired-port structure on
  `compactCoinMatrix`.
* `Turing.MultiTapePTM.ConfigurationGraph.clockedCompactPairedPorts`: paired-port structure on
  `finTimeLayer T (compactCoinMatrix ...)`.
* `Cslib.Complexity.PairedTimeLayerFamily`: Turing-machine-independent family of polynomial-size
  strict-upper-triangular substochastic matrices with paired ports and logarithmic-space local
  evaluators.

## Main results

* `Turing.MultiTapePTM.ConfigurationGraph.clockedCompactPairedPorts_outPort_val`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedCompactPairedPorts_inPort_val`,
  `Turing.MultiTapePTM.ConfigurationGraph.clockedCompactPairedPorts_outWeight`: exact value
  agreement with `clockedOutPort`, `clockedInPort`, and `clockedOutCount`.
* `Cslib.Complexity.exists_compactTimeLayer_of_mem_RL`: one-sided error clocked matrix reduction
  for `RL`.
* `Cslib.Complexity.exists_pairedTimeLayerFamily_of_mem_BPL`,
  `Cslib.Complexity.exists_pairedTimeLayerFamily_of_mem_RL`: complete Lemma 2.1 paired-port
  time-layered reductions for `BPL` and `RL`.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Section 2, Lemma 2.1 (`model.tex`, 23 September 2026, revision `7ef5c0cc`, not peer reviewed).
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph Matrix

variable {k : ℕ} {State : Type} [Fintype State]

section ListFinHelpers

private def liftFinList {N : ℕ} : ∀ (l : List ℕ), (∀ x ∈ l, x < N) → List (Fin N)
  | [], _ => []
  | x :: xs, h =>
    ⟨x, h x List.mem_cons_self⟩ ::
      liftFinList xs fun y hy => h y (List.mem_cons_of_mem x hy)

private theorem map_val_liftFinList {N : ℕ} :
    ∀ (l : List ℕ) (h : ∀ x ∈ l, x < N), (liftFinList l h).map Fin.val = l
  | [], _ => rfl
  | x :: xs, h =>
    congrArg (x :: ·) (map_val_liftFinList xs fun y hy => h y (List.mem_cons_of_mem x hy))

private theorem mem_of_map_val_iff {N : ℕ} {l : List (Fin N)} {lNat : List ℕ}
    (hmap : l.map Fin.val = lNat) (x : Fin N) :
    x ∈ l ↔ x.val ∈ lNat := by
  rw [← hmap, List.mem_map]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    exact Fin.ext hyx ▸ hy

private theorem idxOf_eq_idxOf_map_val {N : ℕ} :
    ∀ (l : List (Fin N)) (x : Fin N), (l.map Fin.val).idxOf x.val = l.idxOf x
  | [], _ => rfl
  | y :: ys, x => by
    have hbeq : (y.val == x.val) = (y == x) := by simp [Fin.ext_iff]
    simp only [List.map_cons, List.idxOf_cons, hbeq]
    split_ifs
    · rfl
    · exact congrArg Nat.succ (idxOf_eq_idxOf_map_val ys x)

end ListFinHelpers

/-! ### Base paired ports on the compact configuration box -/

/-- Outgoing neighbor list of `u` in `Fin (vertexBound B)` for `compactCoinMatrix`. -/
noncomputable def compactOutTargets (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) : List (Fin (vertexBound (k := k) B)) :=
  liftFinList (coinOutTargetsWithSymbol machine B w.length u.val w[queryIndex (k := k) B u.val]?)
    fun _ hv => (lt_vertexBound_of_mem_coinOutTargetsWithSymbol machine hv).2

/-- Incoming neighbor list of `v` in `Fin (vertexBound B)` for `compactCoinMatrix`. -/
noncomputable def compactInSources (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (v : Fin (vertexBound (k := k) B)) : List (Fin (vertexBound (k := k) B)) :=
  liftFinList (coinInSources machine B w v.val) fun u hu =>
    (lt_vertexBound_of_mem_coinOutTargetsWithSymbol machine
      ((mem_coinOutTargetsWithSymbol_iff_mem_coinInSources machine B w u v.val).mpr hu)).1

theorem map_val_compactOutTargets (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) :
    (compactOutTargets machine B w u).map Fin.val =
      coinOutTargetsWithSymbol machine B w.length u.val w[queryIndex (k := k) B u.val]? :=
  map_val_liftFinList _ _

theorem map_val_compactInSources (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (v : Fin (vertexBound (k := k) B)) :
    (compactInSources machine B w v).map Fin.val = coinInSources machine B w v.val :=
  map_val_liftFinList _ _

theorem nodup_compactOutTargets (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) :
    (compactOutTargets machine B w u).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [map_val_compactOutTargets]
  exact nodup_coinOutTargetsWithSymbol machine B w.length u.val _

theorem nodup_compactInSources (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (v : Fin (vertexBound (k := k) B)) :
    (compactInSources machine B w v).Nodup := by
  apply List.Nodup.of_map Fin.val
  rw [map_val_compactInSources]
  exact nodup_coinInSources machine B w v.val

theorem length_compactOutTargets_le (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) :
    (compactOutTargets machine B w u).length ≤ 2 := by
  rw [← List.length_map Fin.val, map_val_compactOutTargets]
  exact length_coinOutTargetsWithSymbol_le machine B w.length u.val _

theorem length_compactInSources_le (machine : MultiTapePTM k Bool State) (B : ℕ) (w : List Bool)
    (v : Fin (vertexBound (k := k) B)) :
    (compactInSources machine B w v).length ≤ inPortBound machine := by
  rw [← List.length_map Fin.val, map_val_compactInSources]
  exact length_coinInSources_le machine B w v.val

theorem mem_compactOutTargets_iff_mem_compactInSources (machine : MultiTapePTM k Bool State)
    (B : ℕ) (w : List Bool) (u v : Fin (vertexBound (k := k) B)) :
    v ∈ compactOutTargets machine B w u ↔ u ∈ compactInSources machine B w v := by
  rw [mem_of_map_val_iff (map_val_compactOutTargets machine B w u),
    mem_of_map_val_iff (map_val_compactInSources machine B w v)]
  exact mem_coinOutTargetsWithSymbol_iff_mem_coinInSources machine B w u.val v.val

theorem mem_compactOutTargets_of_compactCoinMatrix_ne_zero (machine : MultiTapePTM k Bool State)
    {R : Type*} [Field R] {B : ℕ} {w : List Bool} {u v : Fin (vertexBound (k := k) B)}
    (hne : compactCoinMatrix machine R B w u v ≠ 0) :
    v ∈ compactOutTargets machine B w u := by
  rw [mem_of_map_val_iff (map_val_compactOutTargets machine B w u),
    mem_coinOutTargetsWithSymbol_iff]
  by_contra h0
  have hzero : coinCountWithSymbol machine B w.length u.val v.val
      w[queryIndex (k := k) B u.val]? = 0 := by omega
  apply hne
  simp [compactCoinMatrix, hzero]

/-- Canonical paired-port structure on `compactCoinMatrix` with `2` outgoing ports and
`inPortBound machine` incoming ports per vertex. -/
noncomputable def compactPairedPorts (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (B : ℕ) (w : List Bool) :
    (compactCoinMatrix machine R B w).PairedPorts 2 (inPortBound machine) :=
  Matrix.PairedPorts.ofLists (compactCoinMatrix machine R B w) 2 (inPortBound machine)
    (compactOutTargets machine B w) (compactInSources machine B w)
    (nodup_compactOutTargets machine B w) (nodup_compactInSources machine B w)
    (length_compactOutTargets_le machine B w) (length_compactInSources_le machine B w)
    (mem_compactOutTargets_iff_mem_compactInSources machine B w)
    fun hne => mem_compactOutTargets_of_compactCoinMatrix_ne_zero machine hne

/-- Natural-number value of `(compactPairedPorts machine R B w).outPort u p`. -/
theorem compactPairedPorts_outPort_val (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) (p : Fin 2) :
    ((compactPairedPorts machine R B w).outPort u p).map (fun (v, q) => (v.val, q.val)) =
      match (coinOutTargetsWithSymbol machine B w.length u.val
          w[queryIndex (k := k) B u.val]?)[p.val]? with
      | none => none
      | some v => some (v, (coinInSources machine B w v).idxOf u.val) := by
  have hget : ((compactOutTargets machine B w u)[p.val]?).map Fin.val =
      (coinOutTargetsWithSymbol machine B w.length u.val
        w[queryIndex (k := k) B u.val]?)[p.val]? := by
    rw [← List.getElem?_map, map_val_compactOutTargets]
  cases hg : (compactOutTargets machine B w u)[p.val]? with
  | none =>
    rw [hg, Option.map_none] at hget
    rw [← hget]
    dsimp only
    rw [Option.map_eq_none_iff, compactPairedPorts, Matrix.PairedPorts.ofLists_outPort_eq_none_iff]
    exact hg
  | some v =>
    rw [hg, Option.map_some] at hget
    rw [← hget]
    dsimp only
    have hv_mem : v ∈ compactOutTargets machine B w u := List.mem_of_getElem? hg
    have hu_mem : u ∈ compactInSources machine B w v :=
      (mem_compactOutTargets_iff_mem_compactInSources machine B w u v).mp hv_mem
    have hq_lt : (compactInSources machine B w v).idxOf u < inPortBound machine :=
      (List.idxOf_lt_length_of_mem hu_mem).trans_le (length_compactInSources_le machine B w v)
    let q : Fin (inPortBound machine) := ⟨(compactInSources machine B w v).idxOf u, hq_lt⟩
    have hsome : (compactPairedPorts machine R B w).outPort u p = some (v, q) := by
      rw [compactPairedPorts, Matrix.PairedPorts.ofLists_outPort_eq_some_iff]
      exact ⟨hg, rfl⟩
    rw [hsome, Option.map_some]
    dsimp only [q]
    rw [← idxOf_eq_idxOf_map_val, map_val_compactInSources]

/-- Natural-number value of `(compactPairedPorts machine R B w).inPort v q`. -/
theorem compactPairedPorts_inPort_val (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (B : ℕ) (w : List Bool)
    (v : Fin (vertexBound (k := k) B)) (q : Fin (inPortBound machine)) :
    ((compactPairedPorts machine R B w).inPort v q).map (fun (u, p) => (u.val, p.val)) =
      match (coinInSources machine B w v.val)[q.val]? with
      | none => none
      | some u =>
        some (u,
          (coinOutTargetsWithSymbol machine B w.length u
            w[queryIndex (k := k) B u]?).idxOf v.val) := by
  have hget : ((compactInSources machine B w v)[q.val]?).map Fin.val =
      (coinInSources machine B w v.val)[q.val]? := by
    rw [← List.getElem?_map, map_val_compactInSources]
  cases hg : (compactInSources machine B w v)[q.val]? with
  | none =>
    rw [hg, Option.map_none] at hget
    rw [← hget]
    dsimp only
    rw [Option.map_eq_none_iff, compactPairedPorts, Matrix.PairedPorts.ofLists_inPort_eq_none_iff]
    exact hg
  | some u =>
    rw [hg, Option.map_some] at hget
    rw [← hget]
    dsimp only
    have hu_mem : u ∈ compactInSources machine B w v := List.mem_of_getElem? hg
    have hv_mem : v ∈ compactOutTargets machine B w u :=
      (mem_compactOutTargets_iff_mem_compactInSources machine B w u v).mpr hu_mem
    have hp_lt : (compactOutTargets machine B w u).idxOf v < 2 :=
      (List.idxOf_lt_length_of_mem hv_mem).trans_le (length_compactOutTargets_le machine B w u)
    let p : Fin 2 := ⟨(compactOutTargets machine B w u).idxOf v, hp_lt⟩
    have hsome : (compactPairedPorts machine R B w).inPort v q = some (u, p) := by
      rw [compactPairedPorts, Matrix.PairedPorts.ofLists_inPort_eq_some_iff]
      exact ⟨hg, rfl⟩
    rw [hsome, Option.map_some]
    dsimp only [p]
    rw [← idxOf_eq_idxOf_map_val, map_val_compactOutTargets]

/-- Outgoing port weight of `compactPairedPorts` in terms of `coinCountWithSymbol`. -/
theorem compactPairedPorts_outWeight (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (B : ℕ) (w : List Bool)
    (u : Fin (vertexBound (k := k) B)) (p : Fin 2) :
    (compactPairedPorts machine R B w).outWeight u p =
      match (coinOutTargetsWithSymbol machine B w.length u.val
          w[queryIndex (k := k) B u.val]?)[p.val]? with
      | none => 0
      | some v =>
        (coinCountWithSymbol machine B w.length u.val v
          w[queryIndex (k := k) B u.val]? : R) / 2 := by
  have hget : ((compactOutTargets machine B w u)[p.val]?).map Fin.val =
      (coinOutTargetsWithSymbol machine B w.length u.val
        w[queryIndex (k := k) B u.val]?)[p.val]? := by
    rw [← List.getElem?_map, map_val_compactOutTargets]
  rw [compactPairedPorts, Matrix.PairedPorts.ofLists_outWeight_apply]
  cases hg : (compactOutTargets machine B w u)[p.val]? with
  | none =>
    rw [hg, Option.map_none] at hget
    rw [← hget]
  | some v =>
    rw [hg, Option.map_some] at hget
    rw [← hget]
    rfl

/-! ### Clocked paired ports on consecutive identifiers -/

/-- Paired-port structure on the finite clocked transition matrix
`finTimeLayer (2 * (2 * (w.length + 1)) ^ d) (compactCoinMatrix machine R (radix D w.length) w)`
indexed by `Fin (clockedVertexBound D d w.length)`. -/
noncomputable def clockedCompactPairedPorts (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (D d : ℕ) (w : List Bool) :
    (finTimeLayer (2 * (2 * (w.length + 1)) ^ d)
      (compactCoinMatrix machine R (radix D w.length) w)).PairedPorts 2 (inPortBound machine) :=
  (compactPairedPorts machine R (radix D w.length) w).finTimeLayer
    (2 * (2 * (w.length + 1)) ^ d)

/-- Exact agreement between `(clockedCompactPairedPorts ...).outPort` and `clockedOutPort`. -/
theorem clockedCompactPairedPorts_outPort_val (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (D d : ℕ) (w : List Bool)
    (a : Fin (clockedVertexBound (k := k) D d w.length)) (p : Fin 2) :
    ((clockedCompactPairedPorts machine R D d w).outPort a p).map
        (fun (b, q) => (b.val, q.val)) =
      clockedOutPort machine D d w a.val p.val := by
  have ha_lt : a.val < clockedVertexBound (k := k) D d w.length := a.isLt
  unfold clockedVertexBound at a
  let n := w.length
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := 2 * (2 * (n + 1)) ^ d
  have hmap : ((clockedCompactPairedPorts machine R D d w).outPort a p).map
      (fun (b, q) => (b.val, q.val)) =
      ((((compactPairedPorts machine R B w).finTimeLayer T).outPort a p).map
        (fun (b, q) => (b.val, q))).map (fun (bVal, q) => (bVal, q.val)) := by
    rw [clockedCompactPairedPorts, Option.map_map]
    rfl
  rw [hmap, Matrix.PairedPorts.finTimeLayer_outPort_val]
  dsimp only [clockedOutPort]
  by_cases hdiv : a.val / N < T
  · have hcond : a.val < clockedVertexBound (k := k) D d n ∧ p.val < 2 ∧ a.val / N < T :=
      ⟨ha_lt, p.isLt, hdiv⟩
    rw [ite_eq_left hdiv, ite_eq_left hcond]
    have hbase := compactPairedPorts_outPort_val machine R B w a.modNat p
    change (((compactPairedPorts machine R B w).outPort a.modNat p).map
        fun (v, q) => (v.val, q.val)) =
      match (coinOutTargetsWithSymbol machine B n (a.val % N)
          w[queryIndex (k := k) B (a.val % N)]?)[p.val]? with
      | none => none
      | some v => some (v, (coinInSources machine B w v).idxOf (a.val % N)) at hbase
    cases ho : (compactPairedPorts machine R B w).outPort a.modNat p with
    | none =>
      rw [ho, Option.map_none] at hbase
      cases hg : (coinOutTargetsWithSymbol machine B n (a.val % N)
          w[queryIndex (k := k) B (a.val % N)]?)[p.val]? with
      | none => rfl
      | some v => rw [hg] at hbase; cases hbase
    | some vq =>
      obtain ⟨v, q⟩ := vq
      rw [ho, Option.map_some] at hbase
      cases hg : (coinOutTargetsWithSymbol machine B n (a.val % N)
          w[queryIndex (k := k) B (a.val % N)]?)[p.val]? with
      | none => rw [hg] at hbase; cases hbase
      | some vNat =>
        rw [hg, Option.some.injEq, Prod.mk.injEq] at hbase
        obtain ⟨hv_eq, hq_eq⟩ := hbase
        simp [hv_eq, hq_eq, n, B, N]
  · have hcond : ¬ (a.val < clockedVertexBound (k := k) D d n ∧ p.val < 2 ∧ a.val / N < T) :=
      fun h => hdiv h.2.2
    rw [ite_eq_right hdiv, ite_eq_right hcond, Option.map_none]

/-- Exact agreement between `(clockedCompactPairedPorts ...).inPort` and `clockedInPort`. -/
theorem clockedCompactPairedPorts_inPort_val (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (D d : ℕ) (w : List Bool)
    (b : Fin (clockedVertexBound (k := k) D d w.length)) (q : Fin (inPortBound machine)) :
    ((clockedCompactPairedPorts machine R D d w).inPort b q).map
        (fun (a, p) => (a.val, p.val)) =
      clockedInPort machine D d w b.val q.val := by
  have hb_lt : b.val < clockedVertexBound (k := k) D d w.length := b.isLt
  unfold clockedVertexBound at b
  let n := w.length
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := 2 * (2 * (n + 1)) ^ d
  have hmap : ((clockedCompactPairedPorts machine R D d w).inPort b q).map
      (fun (a, p) => (a.val, p.val)) =
      ((((compactPairedPorts machine R B w).finTimeLayer T).inPort b q).map
        (fun (a, p) => (a.val, p))).map (fun (aVal, p) => (aVal, p.val)) := by
    rw [clockedCompactPairedPorts, Option.map_map]
    rfl
  rw [hmap, Matrix.PairedPorts.finTimeLayer_inPort_val]
  dsimp only [clockedInPort]
  by_cases hdiv : 0 < b.val / N
  · have hcond : b.val < clockedVertexBound (k := k) D d n ∧ q.val < inPortBound machine ∧
        0 < b.val / N := ⟨hb_lt, q.isLt, hdiv⟩
    rw [ite_eq_left hdiv, ite_eq_left hcond]
    have hbase := compactPairedPorts_inPort_val machine R B w b.modNat q
    change (((compactPairedPorts machine R B w).inPort b.modNat q).map
        fun (u, p) => (u.val, p.val)) =
      match (coinInSources machine B w (b.val % N))[q.val]? with
      | none => none
      | some u =>
        some (u, (coinOutTargetsWithSymbol machine B n u
          w[queryIndex (k := k) B u]?).idxOf (b.val % N)) at hbase
    cases hi : (compactPairedPorts machine R B w).inPort b.modNat q with
    | none =>
      rw [hi, Option.map_none] at hbase
      cases hg : (coinInSources machine B w (b.val % N))[q.val]? with
      | none => rfl
      | some u => rw [hg] at hbase; cases hbase
    | some up =>
      obtain ⟨u, p⟩ := up
      rw [hi, Option.map_some] at hbase
      cases hg : (coinInSources machine B w (b.val % N))[q.val]? with
      | none => rw [hg] at hbase; cases hbase
      | some uNat =>
        rw [hg, Option.some.injEq, Prod.mk.injEq] at hbase
        obtain ⟨hu_eq, hp_eq⟩ := hbase
        simp [hu_eq, hp_eq, n, B, N]
  · have hcond : ¬ (b.val < clockedVertexBound (k := k) D d n ∧ q.val < inPortBound machine ∧
        0 < b.val / N) := fun h => hdiv h.2.2
    rw [ite_eq_right hdiv, ite_eq_right hcond, Option.map_none]

/-- Exact agreement between `(clockedCompactPairedPorts ...).outWeight` and half of
`clockedOutCount`. -/
theorem clockedCompactPairedPorts_outWeight (machine : MultiTapePTM k Bool State)
    (R : Type*) [Field R] (D d : ℕ) (w : List Bool)
    (a : Fin (clockedVertexBound (k := k) D d w.length)) (p : Fin 2) :
    (clockedCompactPairedPorts machine R D d w).outWeight a p =
      (clockedOutCount machine D d w a.val p.val : R) / 2 := by
  have ha_lt : a.val < clockedVertexBound (k := k) D d w.length := a.isLt
  unfold clockedVertexBound at a
  let n := w.length
  let B := radix D n
  let N := vertexBound (k := k) B
  let T := 2 * (2 * (n + 1)) ^ d
  rw [clockedCompactPairedPorts, Matrix.PairedPorts.finTimeLayer_outWeight_apply]
  dsimp only [clockedOutCount, clockedOutCountWithSymbol]
  by_cases hdiv : a.val / N < T
  · have hcond : a.val < clockedVertexBound (k := k) D d n ∧ p.val < 2 ∧ a.val / N < T :=
      ⟨ha_lt, p.isLt, hdiv⟩
    have hmod_val : (a.modNat).val = a.val % vertexBound (k := k) (radix D w.length) := rfl
    rw [ite_eq_left hdiv, ite_eq_left hcond, compactPairedPorts_outWeight, hmod_val]
    cases (coinOutTargetsWithSymbol machine (radix D w.length) w.length
        (a.val % vertexBound (k := k) (radix D w.length))
        w[queryIndex (k := k) (radix D w.length)
          (a.val % vertexBound (k := k) (radix D w.length))]?)[p.val]? with
    | none => simp
    | some v => rfl
  · have hcond : ¬ (a.val < clockedVertexBound (k := k) D d n ∧ p.val < 2 ∧ a.val / N < T) :=
      fun h => hdiv h.2.2
    rw [ite_eq_right hdiv, ite_eq_right hcond]
    simp

/-- Numeric value of the clock-zero initial vertex in `Fin ((T + 1) * vertexBound B)`. -/
theorem val_clockedStart (machine : MultiTapePTM k Bool State) (c T : ℕ) {w : List Bool}
    (hs : machine.toNTM.RunsInSpace w (c * (Nat.log2 w.length + 1))) :
    ((timeLayerEquiv T (vertexBound (k := k) (radix (radixExponent State c) w.length))).symm
      (toLex (0, compactStart machine c hs))).val =
      startID machine.toNTM (radix (radixExponent State c) w.length) := by
  rw [timeLayerEquiv_val T]
  simp [compactStart]

end Turing.MultiTapePTM.ConfigurationGraph

namespace Cslib.Complexity

open _root_.Turing _root_.Turing.MultiTapeTM
  MultiTapeNTM.ConfigurationGraph MultiTapePTM.ConfigurationGraph Matrix

variable {α : Type} {enc : α ↪ List Bool} {A : Set α}

/-- **The enumerated clocked RL matrix.** One-sided error counterpart of
`Cslib.Complexity.exists_compactTimeLayer_of_mem_BPL`: members achieve potential at least `1 / 2`
at `x₀`, while non-members have potential `0` at `x₀`. -/
theorem exists_compactTimeLayer_of_mem_RL (h : A ∈ RL enc) :
    ∃ (k : ℕ) (State : Type) (_ : Fintype State) (M : MultiTapePTM k Bool State) (c d : ℕ),
      ∀ a, ∃ hs : M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)),
        let w := enc a
        let D := radixExponent State c
        let B := radix D w.length
        let N := vertexBound (k := k) B
        let T := 2 * (2 * (w.length + 1)) ^ d
        let P := compactCoinMatrix M ℝ B w
        let e₀ := compactAcceptVec (k := k) (State := State) ℝ B w.length
        let S := finTimeLayer T P
        let e := finTimeLayerReward T e₀
        let p := finTimeLayerPotential T P e₀
        let x₀ := (timeLayerEquiv T N).symm (toLex (0, compactStart M c hs))
        M.toNTM.RunsInTime w T ∧
        Fintype.card (Fin ((T + 1) * N)) ≤
          (2 * (w.length + 1)) ^ (D * Fintype.card (Register k) + d + 2) ∧
        S.IsStrictUpperTriangular ∧ (∀ x y, 0 ≤ S x y) ∧ S *ᵥ 1 ≤ 1 ∧
        (∀ x, e x = 0 ∨ e x = 1) ∧ (1 - S) *ᵥ p = e ∧ (1 - S)⁻¹ *ᵥ e = p ∧
        p ∈ Set.Icc 0 1 ∧
        (a ∈ A → 1 / 2 ≤ p x₀) ∧ (a ∉ A → p x₀ = 0) := by
  classical
  obtain ⟨k, State, _, M, c, hM⟩ := h
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨d, hd⟩ := M.toNTM.exists_runsInTime_polynomial_of_runsInSpace_log c
  refine ⟨k, State, inferInstance, M, c, d, fun a => ?_⟩
  obtain ⟨hs, t, ht, hmem, hnot⟩ := hM a
  refine ⟨hs, ?_⟩
  dsimp only
  have hT := hd hs ht
  have hP0 := compactCoinMatrix_nonneg (machine := M) (R := ℝ)
    (radix (radixExponent State c) (enc a).length) (enc a)
  have hP1 := compactCoinMatrix_mulVec_one_le (machine := M) (R := ℝ)
    (radix (radixExponent State c) (enc a).length) (enc a)
  refine ⟨hT, ?_, finTimeLayer_isStrictUpperTriangular _ _, finTimeLayer_nonneg hP0 _,
    finTimeLayer_mulVec_one_le hP1 _, ?_, one_sub_finTimeLayer_mulVec _ _ _,
    inv_one_sub_finTimeLayer_mulVec _ _ _,
    finTimeLayerPotential_mem_Icc hP0 hP1 (compactAcceptVec_mem_Icc _ _) _, ?_, ?_⟩
  · rw [Fintype.card_fin]
    exact (Nat.le_succ _).trans (clockedVertexBound_add_one_le_pow
      (k := k) (radixExponent State c) d (enc a).length)
  · intro x
    unfold finTimeLayerReward timeLayerReward compactAcceptVec
    dsimp only [Function.comp_apply]
    split_ifs <;> simp
  · intro ha
    rw [finTimeLayer_compactCoinMatrix_acceptance]
    have hn := (M.two_pow_mul_le_iff ht hT 1 2).mp (by simpa only [one_mul] using hmem ha)
    simp only [one_mul] at hn
    have hc : (2 : ℝ) ^ (2 * (2 * ((enc a).length + 1)) ^ d) ≤
        2 * (M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) : ℝ) := by
      exact_mod_cast hn
    rw [le_div_iff₀ (by positivity)]
    linarith
  · intro ha
    rw [finTimeLayer_compactCoinMatrix_acceptance]
    have heq := M.acceptCoins_mul_two_pow ht hT
    rw [hnot ha, zero_mul] at heq
    have h0 : M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) = 0 :=
      (Nat.mul_eq_zero.mp heq).resolve_right (Nat.two_pow_pos t).ne'
    simp [h0]

/-- A Turing-machine-independent family of polynomial-size strict-upper-triangular substochastic
matrices over `ℝ` indexed by `a : α` (under encoding `enc`), equipped with bounded-degree paired
ports (`2` outgoing ports and `dIn` incoming ports per vertex) and deterministic logarithmic-space
evaluators for dimension, start vertex, terminal reward, port multiplicities, and port lookups.

This packages the output of Lemma 2.1 of [OpenAI2026LogSpace] for consumption by deterministic
logarithmic-space potential estimators. -/
structure PairedTimeLayerFamily {α : Type} (enc : α ↪ List Bool) where
  /-- Constant incoming port degree bound across all instances. -/
  dIn : ℕ
  /-- Positivity of the incoming port degree bound. -/
  dIn_pos : 0 < dIn
  /-- Polynomial degree exponent bounding the matrix dimension `dim a`. -/
  dimExp : ℕ
  /-- Matrix dimension on instance `a`. -/
  dim : α → ℕ
  /-- Every instance has positive matrix dimension. -/
  dim_pos : ∀ a, 0 < dim a
  /-- Explicit polynomial upper bound on `dim a` in terms of `(enc a).length`. -/
  dim_le_pow : ∀ a, dim a ≤ (2 * ((enc a).length + 1)) ^ dimExp
  /-- Strict-upper-triangular substochastic transition matrix on `Fin (dim a)`. -/
  matrix : ∀ a, Matrix (Fin (dim a)) (Fin (dim a)) ℝ
  /-- Strict upper triangularity of `matrix a` in the numeric `Fin (dim a)` order. -/
  isStrictUpperTriangular : ∀ a, (matrix a).IsStrictUpperTriangular
  /-- Entrywise nonnegativity of `matrix a`. -/
  matrix_nonneg : ∀ a x y, 0 ≤ matrix a x y
  /-- Substochastic row-sum bound `matrix a *ᵥ 1 ≤ 1`. -/
  matrix_mulVec_one_le : ∀ a, matrix a *ᵥ 1 ≤ 1
  /-- Terminal `{0, 1}` reward vector on `Fin (dim a)`. -/
  reward : ∀ a, Fin (dim a) → ℝ
  /-- Binary values of `reward a`. -/
  reward_eq_zero_or_one : ∀ a x, reward a x = 0 ∨ reward a x = 1
  /-- Remaining-time acceptance potential vector `(1 - matrix a)⁻¹ *ᵥ reward a`. -/
  potential : ∀ a, Fin (dim a) → ℝ
  /-- Linear system `(1 - matrix a) *ᵥ potential a = reward a`. -/
  one_sub_mulVec_potential : ∀ a, (1 - matrix a) *ᵥ potential a = reward a
  /-- Inverse representation `(1 - matrix a)⁻¹ *ᵥ reward a = potential a`. -/
  inv_one_sub_mulVec_reward : ∀ a, (1 - matrix a)⁻¹ *ᵥ reward a = potential a
  /-- Pointwise `[0, 1]` bounds on `potential a`. -/
  potential_mem_Icc : ∀ a, potential a ∈ Set.Icc 0 1
  /-- Distinguished start vertex on `Fin (dim a)`. -/
  start : ∀ a, Fin (dim a)
  /-- Paired-port representation of `matrix a` with `2` outgoing and `dIn` incoming ports. -/
  ports : ∀ a, (matrix a).PairedPorts 2 dIn
  /-- Natural-number evaluator for `(start a).val`. -/
  startNat : α → ℕ
  /-- Boolean evaluator for `reward a` on natural-number vertex IDs. -/
  acceptBool : α → ℕ → Bool
  /-- Half-integer numerator (`0`, `1`, or `2`) of outgoing port weights on natural-number IDs. -/
  outCount : α → ℕ → ℕ → ℕ
  /-- Outgoing port lookup `(targetVertex, incomingPort)` on natural-number IDs. -/
  outPortNat : α → ℕ → ℕ → Option (ℕ × ℕ)
  /-- Incoming port lookup `(sourceVertex, outgoingPort)` on natural-number IDs. -/
  inPortNat : α → ℕ → ℕ → Option (ℕ × ℕ)
  /-- Agreement of `startNat` with `start`. -/
  val_start : ∀ a, (start a).val = startNat a
  /-- Agreement of `acceptBool` with `reward`. -/
  reward_eq_acceptBool : ∀ a (u : Fin (dim a)), reward a u = ((acceptBool a u.val).toNat : ℝ)
  /-- Out-of-range behavior of `acceptBool`. -/
  acceptBool_eq_false_of_ge : ∀ a {u}, dim a ≤ u → acceptBool a u = false
  /-- Upper bound `outCount a u p ≤ 2` (so port weights lie in `{0, 1/2, 1}`). -/
  outCount_le_two : ∀ a u p, outCount a u p ≤ 2
  /-- Agreement of `outCount` with `(ports a).outWeight`. -/
  outWeight_eq_outCount : ∀ a (u : Fin (dim a)) (p : Fin 2),
    (ports a).outWeight u p = (outCount a u.val p.val : ℝ) / 2
  /-- Inactive outgoing ports have multiplicity `0`. -/
  outCount_eq_zero_of_outPortNat_eq_none : ∀ a u p,
    outPortNat a u p = none → outCount a u p = 0
  /-- Active outgoing ports have positive multiplicity (`1` or `2`). -/
  outCount_pos_of_outPortNat_eq_some : ∀ a {u p v q},
    outPortNat a u p = some (v, q) → 0 < outCount a u p
  /-- Agreement of `outPortNat` with `(ports a).outPort`. -/
  outPort_map_val : ∀ a (u : Fin (dim a)) (p : Fin 2),
    ((ports a).outPort u p).map (fun (v, q) => (v.val, q.val)) = outPortNat a u.val p.val
  /-- Agreement of `inPortNat` with `(ports a).inPort`. -/
  inPort_map_val : ∀ a (v : Fin (dim a)) (q : Fin dIn),
    ((ports a).inPort v q).map (fun (u, p) => (u.val, p.val)) = inPortNat a v.val q.val
  /-- Mutual inversion of `outPortNat` and `inPortNat` on all natural-number arguments. -/
  outPortNat_eq_some_iff : ∀ a u p v q,
    outPortNat a u p = some (v, q) ↔ inPortNat a v q = some (u, p)
  /-- Out-of-range vertex behavior of `outPortNat`. -/
  outPortNat_eq_none_of_ge_dim : ∀ a {u} (p), dim a ≤ u → outPortNat a u p = none
  /-- Out-of-range port behavior of `outPortNat`. -/
  outPortNat_eq_none_of_port_ge : ∀ a (u) {p}, 2 ≤ p → outPortNat a u p = none
  /-- Out-of-range vertex behavior of `inPortNat`. -/
  inPortNat_eq_none_of_ge_dim : ∀ a {v} (q), dim a ≤ v → inPortNat a v q = none
  /-- Out-of-range port behavior of `inPortNat`. -/
  inPortNat_eq_none_of_port_ge : ∀ a (v) {q}, dIn ≤ q → inPortNat a v q = none
  /-- Deterministic logarithmic-space computability of `dim`. -/
  computableInLogSpace_dim : ComputableInLogSpace dim enc encNat
  /-- Deterministic logarithmic-space computability of `startNat`. -/
  computableInLogSpace_startNat : ComputableInLogSpace startNat enc encNat
  /-- Deterministic logarithmic-space computability of `acceptBool`. -/
  computableInLogSpace_acceptBool :
    ComputableInLogSpace (fun (a, u) => acceptBool a u) (encPair enc encNat) encBool
  /-- Deterministic logarithmic-space computability of `outCount`. -/
  computableInLogSpace_outCount :
    ComputableInLogSpace (fun (a, u, p) => outCount a u p)
      (encPair enc (encPair encNat encNat)) encNat
  /-- Deterministic logarithmic-space computability of `outPortNat`. -/
  computableInLogSpace_outPortNat :
    ComputableInLogSpace (fun (a, u, p) => outPortNat a u p)
      (encPair enc (encPair encNat encNat)) (encOption (encPair encNat encNat))
  /-- Deterministic logarithmic-space computability of `inPortNat`. -/
  computableInLogSpace_inPortNat :
    ComputableInLogSpace (fun (a, v, q) => inPortNat a v q)
      (encPair enc (encPair encNat encNat)) (encOption (encPair encNat encNat))

namespace PairedTimeLayerFamily

/-- An outgoing port has multiplicity `0` iff it is inactive (`outPortNat a u p = none`). -/
theorem outCount_eq_zero_iff (F : PairedTimeLayerFamily enc) (a : α) (u p : ℕ) :
    F.outCount a u p = 0 ↔ F.outPortNat a u p = none := by
  cases h : F.outPortNat a u p with
  | none => exact ⟨fun _ => rfl, fun _ => F.outCount_eq_zero_of_outPortNat_eq_none a u p h⟩
  | some vq =>
    have hpos := F.outCount_pos_of_outPortNat_eq_some a h
    exact ⟨fun hz => absurd hz (Nat.ne_of_gt hpos), fun hnone => by cases hnone⟩

/-- Every active outgoing port `F.outPortNat a u p = some (v, q)` has in-range vertex and port
indices. -/
theorem bounds_of_outPortNat_eq_some (F : PairedTimeLayerFamily enc) (a : α) {u p v q : ℕ}
    (h : F.outPortNat a u p = some (v, q)) :
    u < F.dim a ∧ p < 2 ∧ v < F.dim a ∧ q < F.dIn := by
  have hu : u < F.dim a := by
    by_contra hge
    rw [F.outPortNat_eq_none_of_ge_dim a p (Nat.le_of_not_lt hge)] at h
    cases h
  have hp : p < 2 := by
    by_contra hge
    rw [F.outPortNat_eq_none_of_port_ge a u (Nat.le_of_not_lt hge)] at h
    cases h
  have hin : F.inPortNat a v q = some (u, p) := (F.outPortNat_eq_some_iff a u p v q).mp h
  have hv : v < F.dim a := by
    by_contra hge
    rw [F.inPortNat_eq_none_of_ge_dim a q (Nat.le_of_not_lt hge)] at hin
    cases hin
  have hq : q < F.dIn := by
    by_contra hge
    rw [F.inPortNat_eq_none_of_port_ge a v (Nat.le_of_not_lt hge)] at hin
    cases hin
  exact ⟨hu, hp, hv, hq⟩

/-- Every active outgoing port `F.outPortNat a u p = some (v, q)` strictly advances in numeric
topological order (`u < v`). -/
theorem lt_of_outPortNat_eq_some (F : PairedTimeLayerFamily enc) (a : α) {u p v q : ℕ}
    (h : F.outPortNat a u p = some (v, q)) : u < v := by
  obtain ⟨hu, hp, -, -⟩ := F.bounds_of_outPortNat_eq_some a h
  let u' : Fin (F.dim a) := ⟨u, hu⟩
  let p' : Fin 2 := ⟨p, hp⟩
  have hmap := F.outPort_map_val a u' p'
  change ((F.ports a).outPort u' p').map (fun (v', q') => (v'.val, q'.val)) =
      F.outPortNat a u p at hmap
  rw [h] at hmap
  cases hg : (F.ports a).outPort u' p' with
  | none =>
    rw [hg] at hmap
    cases hmap
  | some vq' =>
    obtain ⟨v', q'⟩ := vq'
    rw [hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmap
    obtain ⟨hv_eq, -⟩ := hmap
    have hcnt : 0 < F.outCount a u p := F.outCount_pos_of_outPortNat_eq_some a h
    have hw : (F.ports a).outWeight u' p' = (F.outCount a u p : ℝ) / 2 :=
      F.outWeight_eq_outCount a u' p'
    have hentry : (F.ports a).outWeight u' p' = F.matrix a u' v' :=
      (F.ports a).outWeight_eq_entry hg
    have hmat_pos : 0 < F.matrix a u' v' := by
      rw [← hentry, hw]
      positivity
    have hlt : u' < v' := by
      by_contra hnot
      have hz : F.matrix a u' v' = 0 := F.isStrictUpperTriangular a hnot
      linarith
    change u < v'.val at hlt
    simpa only [hv_eq] using hlt

end PairedTimeLayerFamily

/-- Build a `PairedTimeLayerFamily` from a logarithmic-space fair-coin machine `M` at space
constant `c` and polynomial clock exponent `d`. -/
noncomputable def PairedTimeLayerFamily.ofMachine {k : ℕ} {State : Type} [Fintype State]
    (enc : α ↪ List Bool) (M : MultiTapePTM k Bool State) (c d : ℕ)
    (hs : ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1))) :
    PairedTimeLayerFamily enc :=
  let D := radixExponent State c
  let x₀ (a : α) : Fin (clockedVertexBound (k := k) D d (enc a).length) :=
    (timeLayerEquiv (2 * (2 * ((enc a).length + 1)) ^ d)
      (vertexBound (k := k) (radix D (enc a).length))).symm
      (toLex (0, compactStart M c (hs a)))
  have henc : ComputableInLogSpace (fun a : α => enc a) enc encBits :=
    ComputableInLogSpace.id.congr fun _ => rfl
  have hmap2 : ComputableInLogSpace (fun (a, u) => (enc a, u))
      (encPair enc encNat) (encPair encBits encNat) :=
    (ComputableInLogSpace.pair
      (henc.comp (ComputableInLogSpace.fst enc encNat))
      (ComputableInLogSpace.snd enc encNat)).congr_fun fun ⟨_, _⟩ => rfl
  have hmap3 : ComputableInLogSpace (fun (a, u, p) => (enc a, u, p))
      (encPair enc (encPair encNat encNat)) (encPair encBits (encPair encNat encNat)) :=
    (ComputableInLogSpace.pair
      (henc.comp (ComputableInLogSpace.fst enc (encPair encNat encNat)))
      (ComputableInLogSpace.snd enc (encPair encNat encNat))).congr_fun fun ⟨_, _, _⟩ => rfl
  { dIn := inPortBound M
    dIn_pos := inPortBound_pos M
    dimExp := D * Fintype.card (Register k) + d + 2
    dim a := clockedVertexBound (k := k) D d (enc a).length
    dim_pos a := (x₀ a).pos
    dim_le_pow a := (Nat.le_succ _).trans
      (clockedVertexBound_add_one_le_pow (k := k) D d (enc a).length)
    matrix a := finTimeLayer (2 * (2 * ((enc a).length + 1)) ^ d)
      (compactCoinMatrix M ℝ (radix D (enc a).length) (enc a))
    isStrictUpperTriangular _ := finTimeLayer_isStrictUpperTriangular _ _
    matrix_nonneg a := finTimeLayer_nonneg
      (compactCoinMatrix_nonneg (machine := M) (R := ℝ) (radix D (enc a).length) (enc a)) _
    matrix_mulVec_one_le a := finTimeLayer_mulVec_one_le
      (compactCoinMatrix_mulVec_one_le (machine := M) (R := ℝ) (radix D (enc a).length) (enc a)) _
    reward a := finTimeLayerReward (2 * (2 * ((enc a).length + 1)) ^ d)
      (compactAcceptVec (k := k) (State := State) ℝ (radix D (enc a).length) (enc a).length)
    reward_eq_zero_or_one a x := by
      unfold clockedVertexBound at x
      rw [finTimeLayerReward_eq_clockedAccept]
      cases clockedAccept (k := k) (State := State)
        (radix D (enc a).length) (enc a).length (2 * (2 * ((enc a).length + 1)) ^ d) x <;> simp
    potential a := finTimeLayerPotential (2 * (2 * ((enc a).length + 1)) ^ d)
      (compactCoinMatrix M ℝ (radix D (enc a).length) (enc a))
      (compactAcceptVec (k := k) (State := State) ℝ (radix D (enc a).length) (enc a).length)
    one_sub_mulVec_potential _ := one_sub_finTimeLayer_mulVec _ _ _
    inv_one_sub_mulVec_reward _ := inv_one_sub_finTimeLayer_mulVec _ _ _
    potential_mem_Icc a := finTimeLayerPotential_mem_Icc
      (compactCoinMatrix_nonneg (machine := M) (R := ℝ) (radix D (enc a).length) (enc a))
      (compactCoinMatrix_mulVec_one_le (machine := M) (R := ℝ) (radix D (enc a).length) (enc a))
      (compactAcceptVec_mem_Icc _ _) _
    start := x₀
    ports a := clockedCompactPairedPorts M ℝ D d (enc a)
    startNat a := startID M.toNTM (radix D (enc a).length)
    acceptBool a u := clockedAccept (k := k) (State := State)
      (radix D (enc a).length) (enc a).length (2 * (2 * ((enc a).length + 1)) ^ d) u
    outCount a u p := clockedOutCount M D d (enc a) u p
    outPortNat a u p := clockedOutPort M D d (enc a) u p
    inPortNat a v q := clockedInPort M D d (enc a) v q
    val_start a := val_clockedStart M c _ (hs a)
    reward_eq_acceptBool a u := finTimeLayerReward_eq_clockedAccept
      (k := k) (State := State) (R := ℝ) (radix D (enc a).length) (enc a).length
      (2 * (2 * ((enc a).length + 1)) ^ d) u
    acceptBool_eq_false_of_ge := fun _ {_} hu => clockedAccept_eq_false_of_ge_bound hu
    outCount_le_two a u p := clockedOutCount_le_two M D d (enc a) u p
    outWeight_eq_outCount a u p := clockedCompactPairedPorts_outWeight M ℝ D d (enc a) u p
    outCount_eq_zero_of_outPortNat_eq_none _ _ _ h :=
      clockedOutCount_eq_zero_of_outPort_eq_none M h
    outCount_pos_of_outPortNat_eq_some := fun _ {_ _ _ _} h =>
      clockedOutCount_pos_of_outPort_eq_some M h
    outPort_map_val a u p := clockedCompactPairedPorts_outPort_val M ℝ D d (enc a) u p
    inPort_map_val a v q := clockedCompactPairedPorts_inPort_val M ℝ D d (enc a) v q
    outPortNat_eq_some_iff a u p v q := clockedOutPort_eq_some_iff M D d (enc a) u p v q
    outPortNat_eq_none_of_ge_dim := fun _ {_} p hu => clockedOutPort_eq_none_of_ge_bound M hu p
    outPortNat_eq_none_of_port_ge := fun _ u {_} hp => clockedOutPort_eq_none_of_port_ge M u hp
    inPortNat_eq_none_of_ge_dim := fun _ {_} q hv => clockedInPort_eq_none_of_ge_bound M hv q
    inPortNat_eq_none_of_port_ge := fun _ v {_} hq => clockedInPort_eq_none_of_port_ge M v hq
    computableInLogSpace_dim :=
      ((computableInLogSpace_clockedVertexBound (k := k) D d).comp henc).congr_fun fun _ => rfl
    computableInLogSpace_startNat :=
      ((computableInLogSpace_startID M.toNTM D).comp henc).congr_fun fun _ => rfl
    computableInLogSpace_acceptBool :=
      ((computableInLogSpace_clockedAccept (k := k) (State := State) D d).comp hmap2).congr_fun
        fun ⟨_, _⟩ => rfl
    computableInLogSpace_outCount :=
      ((computableInLogSpace_clockedOutCount M D d).comp hmap3).congr_fun fun ⟨_, _, _⟩ => rfl
    computableInLogSpace_outPortNat :=
      ((computableInLogSpace_clockedOutPort M D d).comp hmap3).congr_fun fun ⟨_, _, _⟩ => rfl
    computableInLogSpace_inPortNat :=
      ((computableInLogSpace_clockedInPort M D d).comp hmap3).congr_fun fun ⟨_, _, _⟩ => rfl }

/-- Exact acceptance-probability identity at the start vertex of
`PairedTimeLayerFamily.ofMachine`. -/
theorem PairedTimeLayerFamily.ofMachine_potential_start {k : ℕ} {State : Type} [Fintype State]
    (enc : α ↪ List Bool) (M : MultiTapePTM k Bool State) (c d : ℕ)
    (hs : ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1))) (a : α) :
    (ofMachine enc M c d hs).potential a ((ofMachine enc M c d hs).start a) =
      (M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) : ℝ) /
        2 ^ (2 * (2 * ((enc a).length + 1)) ^ d) := by
  dsimp only [ofMachine]
  rw [finTimeLayer_compactCoinMatrix_acceptance]

/-- **Paired-port time-layered reduction for `BPL` (Lemma 2.1 of [OpenAI2026LogSpace]).**
Every language `A ∈ BPL enc` reduces to estimating the start entry of `(1 - S_a)⁻¹ e_a` for a
`PairedTimeLayerFamily` with acceptance gap `2 / 3` versus `1 / 3`. -/
theorem exists_pairedTimeLayerFamily_of_mem_BPL (h : A ∈ BPL enc) :
    ∃ F : PairedTimeLayerFamily enc,
      ∀ a, (a ∈ A → 2 / 3 ≤ F.potential a (F.start a)) ∧
        (a ∉ A → F.potential a (F.start a) ≤ 1 / 3) := by
  classical
  obtain ⟨k, State, _, M, c, hM⟩ := h
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨d, hd⟩ := M.toNTM.exists_runsInTime_polynomial_of_runsInSpace_log c
  let hs : ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) :=
    fun a => (hM a).1
  refine ⟨PairedTimeLayerFamily.ofMachine enc M c d hs, fun a => ?_⟩
  obtain ⟨_, t, ht, hmem, hnot⟩ := hM a
  have hT := hd (hs a) ht
  rw [PairedTimeLayerFamily.ofMachine_potential_start]
  constructor
  · intro ha
    have hn := (M.two_pow_mul_le_iff ht hT 2 3).mp (hmem ha)
    have hc : (2 : ℝ) * 2 ^ (2 * (2 * ((enc a).length + 1)) ^ d) ≤
        3 * (M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) : ℝ) := by
      exact_mod_cast hn
    rw [le_div_iff₀ (by positivity)]
    linarith
  · intro ha
    have hn := (M.mul_le_two_pow_iff ht hT 1 3).mp (by simpa only [one_mul] using hnot ha)
    simp only [one_mul] at hn
    have hc : (3 : ℝ) * (M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) : ℝ) ≤
        2 ^ (2 * (2 * ((enc a).length + 1)) ^ d) := by
      exact_mod_cast hn
    rw [div_le_iff₀ (by positivity)]
    linarith

/-- **Paired-port time-layered reduction for `RL` (Lemma 2.1 of [OpenAI2026LogSpace]).**
Every language `A ∈ RL enc` reduces to estimating the start entry of `(1 - S_a)⁻¹ e_a` for a
`PairedTimeLayerFamily` with one-sided acceptance gap `1 / 2` versus `0`. -/
theorem exists_pairedTimeLayerFamily_of_mem_RL (h : A ∈ RL enc) :
    ∃ F : PairedTimeLayerFamily enc,
      ∀ a, (a ∈ A → 1 / 2 ≤ F.potential a (F.start a)) ∧
        (a ∉ A → F.potential a (F.start a) = 0) := by
  classical
  obtain ⟨k, State, _, M, c, hM⟩ := h
  let : Fintype State := Fintype.ofFinite State
  obtain ⟨d, hd⟩ := M.toNTM.exists_runsInTime_polynomial_of_runsInSpace_log c
  let hs : ∀ a, M.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)) :=
    fun a => (hM a).1
  refine ⟨PairedTimeLayerFamily.ofMachine enc M c d hs, fun a => ?_⟩
  obtain ⟨_, t, ht, hmem, hnot⟩ := hM a
  have hT := hd (hs a) ht
  rw [PairedTimeLayerFamily.ofMachine_potential_start]
  constructor
  · intro ha
    have hn := (M.two_pow_mul_le_iff ht hT 1 2).mp (by simpa only [one_mul] using hmem ha)
    simp only [one_mul] at hn
    have hc : (2 : ℝ) ^ (2 * (2 * ((enc a).length + 1)) ^ d) ≤
        2 * (M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) : ℝ) := by
      exact_mod_cast hn
    rw [le_div_iff₀ (by positivity)]
    linarith
  · intro ha
    have heq := M.acceptCoins_mul_two_pow ht hT
    rw [hnot ha, zero_mul] at heq
    have h0 : M.acceptCoins (enc a) (2 * (2 * ((enc a).length + 1)) ^ d) = 0 :=
      (Nat.mul_eq_zero.mp heq).resolve_right (Nat.two_pow_pos t).ne'
    simp [h0]

end Cslib.Complexity
