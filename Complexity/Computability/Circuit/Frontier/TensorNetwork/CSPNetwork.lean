/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.ClauseNetwork
public import Complexity.Foundations.Data.BitString.List.Binary
public import Complexity.Logics.Propositional.CSP.PartitionFunction
import Complexity.Foundations.Data.BitString.Binary
import Complexity.Logics.Propositional.CSP.Vars
import Mathlib.Data.List.GetD

/-!
# The constraint network of a weighted Boolean CSP

The network of the occurrence list of a CSP instance `F : CSP Rel ℕ`
(`Cslib.Circuits.Frontier.ClauseNetwork.network`) with weighted row tables: the row of constraint
`(R, vs)` lists `wt R w` at the words `w` of length `|vs|`, and the variables are joined by the
equality chains of the clause network. Its contraction is the partition function
`F.partitionFunction wt` (`ClauseNetwork.contraction_cspNetwork`). This is the network of
Appendix D.2 of [OpenAI2026ETH] with the clause tables replaced by arbitrary weight tables, as in
a Holant or weighted `#CSP` instance; like the clause network, it is bipartite with its rows first
and its degree is at most `max k 4` for constraints of arity at most `k`.

The occurrences are those of the positive formula `F.varCNF` with the same scopes, so the ports
of row `i` carry the scope of constraint `i` in order
(`ClauseNetwork.map_clausePorts_occurrences`).

## Main definitions

* `Cslib.Circuits.Frontier.ClauseNetwork.cspEntry`, `Cslib.Circuits.Frontier.ClauseNetwork.cspRow`:
  the weight tables of the constraints.
* `Cslib.Circuits.Frontier.ClauseNetwork.cspNetwork`: the constraint network.

## Main results

* `Cslib.Circuits.Frontier.ClauseNetwork.contraction_cspNetwork`: the contraction is the partition
  function.
* `Cslib.Circuits.Frontier.ClauseNetwork.isRowsFirstBipartite_cspNetwork`,
  `Cslib.Circuits.Frontier.ClauseNetwork.maxDegree_cspNetwork_le`,
  `Cslib.Circuits.Frontier.ClauseNetwork.length_table_cspNetwork`,
  `Cslib.Circuits.Frontier.ClauseNetwork.numEdges_cspNetwork`,
  `Cslib.Circuits.Frontier.ClauseNetwork.length_vertices_cspNetwork`: its shape.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.2 (p. 54).
-/

public section

namespace Cslib.Circuits.Frontier.ClauseNetwork

open Cslib.Logic.PL

variable {Rel : Type*}

/-- The table entry of a constraint `c`, of arity at most `k`, at the word of value `idx`:
`wt c.1 w` for the word `w` of length `|c.2|` with value `idx`. -/
@[expose] def cspEntry (k : ℕ) (wt : Rel → List Bool → ℕ) (c : Constraint Rel ℕ) (idx : ℕ) : ℕ :=
  ((List.range (k + 1)).map fun r => wt c.1 (BitString.lowBits r idx)).getD c.2.length 0

/-- The row tables of a CSP instance: row `i` is the table of constraint `i`. -/
@[expose] def cspRow (k : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) (i idx : ℕ) : ℕ :=
  (F.map fun c => cspEntry k wt c idx).getD i 0

/-- **The constraint network** of a weighted Boolean CSP instance with constraints of arity at
most `k`, with its number of rows. -/
@[expose] def cspNetwork (k : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) :
    ℕ × ExplicitTensorNetwork ℕ :=
  network (occurrences F.varCNF) (max k 4) F.length (cspRow k wt F)

variable {k : ℕ} {wt : Rel → List Bool → ℕ} {F : CSP Rel ℕ}

private theorem count_le (hk : ∀ c ∈ F, c.2.length ≤ k) (i : ℕ) :
    ((occurrences F.varCNF).map Prod.fst).count i ≤ k := by
  rw [count_map_fst_occurrences]
  by_cases hi : i < F.length
  · rw [CSP.varCNF, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.length_map]
    exact hk _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by rw [CSP.length_varCNF]; omega)]
    exact Nat.zero_le _

/-- The table of constraint `i` at the word an assignment puts on its ports is the weight of the
constraint at the values of its scope. -/
private theorem cspRow_eq (hk : ∀ c ∈ F, c.2.length ≤ k) (σ : ℕ → Bool) {i : ℕ}
    (hi : i < F.length) :
    cspRow k wt F i (BitString.lsbValue ((clausePorts (occurrences F.varCNF) i).map
      fun j => σ (var (occurrences F.varCNF) (j / 3)))) = wt F[i].1 (F[i].2.map σ) := by
  have hports : ((clausePorts (occurrences F.varCNF) i).map
      fun j => σ (var (occurrences F.varCNF) (j / 3))) = F[i].2.map σ := by
    have h := congrArg (List.map fun l : Literal ℕ => σ l.1)
      (map_clausePorts_occurrences F.varCNF i)
    rw [List.map_map, CSP.varCNF, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map,
      List.map_map] at h
    exact h
  have hlen : F[i].2.length < k + 1 := Nat.lt_succ_of_le (hk _ (List.getElem_mem hi))
  rw [hports, cspRow, List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, cspEntry,
    List.getD_eq_getElem _ _ (by simpa using hlen), List.getElem_map, List.getElem_range,
    show F[i].2.length = (F[i].2.map σ).length by simp, BitString.lowBits_lsbValue]

/-- **The contraction of the constraint network is the partition function**, for instances whose
constraints have arity at most `k`. -/
theorem contraction_cspNetwork (hk : ∀ c ∈ F, c.2.length ≤ k) :
    (cspNetwork k wt F).2.contraction = F.partitionFunction wt := by
  rw [cspNetwork, contraction_network _ k _ _ (count_le hk)
    (congrArg List.toFinset ((map_occurrences F.varCNF).trans (CSP.vars_varCNF F))),
    CSP.partitionFunction]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [CSP.weight]
  congr 1
  refine List.ext_getElem (by simp) fun i h₁ h₂ => ?_
  rw [List.getElem_map, List.getElem_map, List.getElem_range]
  exact cspRow_eq hk (fun v => if h : v ∈ F.vars.toFinset then τ ⟨v, h⟩ else false)
    (by simpa using h₁)

/-- **The constraint network is rows-first bipartite.** -/
theorem isRowsFirstBipartite_cspNetwork (k : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) :
    (cspNetwork k wt F).2.IsRowsFirstBipartite (cspNetwork k wt F).1 :=
  isRowsFirstBipartite_network _ _ _ _ fun _ ho => by
    simpa [CSP.length_varCNF] using (mem_occurrences.mp ho).1

/-- **The degree bound**: for constraints of arity at most `k`, every vertex has at most
`max k 4` ports. -/
theorem maxDegree_cspNetwork_le (hk : ∀ c ∈ F, c.2.length ≤ k) :
    (cspNetwork k wt F).2.maxDegree ≤ max k 4 :=
  maxDegree_network_le _ _ k _ (count_le hk)

/-- **Full tables**, for constraints of arity at most `k`. -/
theorem length_table_cspNetwork (hk : ∀ c ∈ F, c.2.length ≤ k) :
    ∀ v ∈ (cspNetwork k wt F).2.vertices, v.2.length = 2 ^ v.1.length :=
  length_table_network _ _ k _ (count_le hk)

/-- The constraint network has three edges per variable occurrence. -/
theorem numEdges_cspNetwork (k : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) :
    (cspNetwork k wt F).2.numEdges = 3 * F.vars.length := by
  rw [← CSP.vars_varCNF, ← length_occurrences]
  rfl

/-- The constraint network has one vertex per constraint and two per variable occurrence. -/
theorem length_vertices_cspNetwork (k : ℕ) (wt : Rel → List Bool → ℕ) (F : CSP Rel ℕ) :
    (cspNetwork k wt F).2.vertices.length = F.length + 2 * F.vars.length := by
  rw [← CSP.vars_varCNF, ← length_occurrences, cspNetwork, length_vertices_network]

end Cslib.Circuits.Frontier.ClauseNetwork
