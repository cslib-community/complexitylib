/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Parameterized
public import CslibFrontier.Computability.Complexity.Problems.Clique

/-!
# Clique and Independent Set under fpt-reductions

Complementing the graph on its declared vertices maps cliques to independent sets and back
(`Cslib.Complexity.Graph.compl_mem_Clique_iff`,
`Cslib.Complexity.Graph.compl_mem_IndependentSet_iff`) and keeps the target `k`. It is a
polynomial-time map, so it is an fpt-reduction in both directions for the parameter `k`
[CyganEtAl2015, Section 13.1]. Hence `Clique` is fixed-parameter tractable exactly when
`IndependentSet` is (`Cslib.Complexity.Clique_mem_FPT_iff`); both are W[1]-complete
[CyganEtAl2015, Chapter 13], which is not formalized here.

## Main results

* `Cslib.Complexity.fptReducible_IndependentSet_Clique`,
  `Cslib.Complexity.fptReducible_Clique_IndependentSet`: fpt-reductions in both directions.
* `Cslib.Complexity.Clique_mem_FPT_iff`, `Cslib.Complexity.Clique_mem_XP_iff`: `Clique` and
  `IndependentSet` are together in `FPT`, and together in `XP`.

## References

* [M. Cygan, F. V. Fomin, Ł. Kowalik, D. Lokshtanov, D. Marx, M. Pilipczuk, M. Pilipczuk,
  S. Saurabh, *Parameterized Algorithms*][CyganEtAl2015]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- **`IndependentSet` fpt-reduces to `Clique`** [CyganEtAl2015, Section 13.1] by complementing the
graph, keeping the parameter `k`. -/
theorem fptReducible_IndependentSet_Clique :
    FPTReducible (encPair encGraph encNat) (encPair encGraph encNat) Prod.snd Prod.snd
      IndependentSet Clique :=
  FPTReducible.of_computableInPolyTime (f := fun x : Graph × ℕ => (x.1.compl, x.2)) (h := id)
    (by fun_prop) (fun _ => le_rfl) fun ⟨G, m⟩ => (Graph.compl_mem_Clique_iff G m).symm

/-- **`Clique` fpt-reduces to `IndependentSet`** [CyganEtAl2015, Section 13.1] by complementing the
graph, keeping the parameter `k`. -/
theorem fptReducible_Clique_IndependentSet :
    FPTReducible (encPair encGraph encNat) (encPair encGraph encNat) Prod.snd Prod.snd
      Clique IndependentSet :=
  FPTReducible.of_computableInPolyTime (f := fun x : Graph × ℕ => (x.1.compl, x.2)) (h := id)
    (by fun_prop) (fun _ => le_rfl) fun ⟨G, m⟩ => (Graph.compl_mem_IndependentSet_iff G m).symm

/-- `Clique` is fixed-parameter tractable in `k` exactly when `IndependentSet` is. -/
theorem Clique_mem_FPT_iff :
    Clique ∈ FPT (encPair encGraph encNat) Prod.snd ↔
      IndependentSet ∈ FPT (encPair encGraph encNat) Prod.snd :=
  ⟨fptReducible_IndependentSet_Clique.mem_FPT, fptReducible_Clique_IndependentSet.mem_FPT⟩

/-- `Clique` is in `XP` for the parameter `k` exactly when `IndependentSet` is. -/
theorem Clique_mem_XP_iff :
    Clique ∈ XP (encPair encGraph encNat) Prod.snd ↔
      IndependentSet ∈ XP (encPair encGraph encNat) Prod.snd :=
  ⟨fptReducible_IndependentSet_Clique.mem_XP, fptReducible_Clique_IndependentSet.mem_XP⟩

end Cslib.Complexity
